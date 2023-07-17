mod dialect;

use crate::dialect::sl_sh::SlSh;
use crate::dialect::slosh::Slosh;
use crate::dialect::Dialect;
use quote::quote;
use quote::ToTokens;
use quote::__private::TokenStream;
use std::fmt::{Display, Formatter};
use syn::__private::{Span, TokenStream2};
use syn::spanned::Spanned;
use syn::{
    parse, parse_macro_input, AttributeArgs, Error, FnArg, GenericArgument, Ident, Item, ItemFn,
    Lit, Meta, NestedMeta, PathArguments, Type, TypeBareFn, TypePath, TypeReference, TypeTuple,
};

extern crate static_assertions;

type ParamParsingFn = fn(Box<dyn Dialect>, &Ident, TokenStream, Param, usize, usize) -> TokenStream;

#[derive(Copy, Clone, Debug, PartialEq)]
enum TypeHandle {
    Direct,
    Optional,
    VarArgs,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) enum PassingStyle {
    Value,
    Reference,
    MutReference,
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub(crate) struct Param {
    handle: TypeHandle,
    passing_style: PassingStyle,
}

type MacroResult<T> = Result<T, Error>;

const POSSIBLE_RETURN_TYPES: [&str; 2] = ["LispResult", "Option"];
const SPECIAL_ARG_TYPES: [&str; 2] = ["Option", "VarArgs"];
const POSSIBLE_ARG_TYPES: [&str; 3] = ["Option", "VarArgs", "Vec"];

#[derive(Copy, Clone)]
pub(crate) enum SupportedGenericReturnTypes {
    LispResult,
    Option,
}

enum RustType {
    BareFn(TypeBareFn, Span),
    Path(TypePath, Span),
    Tuple(TypeTuple, Span),
    Reference(TypeReference, Span),
    Unsupported(Span),
}

impl RustType {
    pub fn span(&self) -> Span {
        match self {
            RustType::BareFn(_, x) => *x,
            RustType::Path(_, x) => *x,
            RustType::Tuple(_, x) => *x,
            RustType::Reference(_, x) => *x,
            RustType::Unsupported(x) => *x,
        }
    }
}

impl From<Type> for RustType {
    fn from(ty: Type) -> Self {
        match ty {
            Type::BareFn(x) => {
                let span = x.span();
                RustType::BareFn(x, span)
            }
            Type::Path(x) => {
                let span = x.span();
                RustType::Path(x, span)
            }
            Type::Reference(x) => {
                let span = x.span();
                RustType::Reference(x, span)
            }
            Type::Tuple(x) => {
                let span = x.span();
                RustType::Tuple(x, span)
            }
            x => {
                let span = x.span();
                RustType::Unsupported(span)
            }
        }
    }
}

impl Display for SupportedGenericReturnTypes {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SupportedGenericReturnTypes::LispResult => {
                write!(f, "LispResult")
            }
            SupportedGenericReturnTypes::Option => {
                write!(f, "Option")
            }
        }
    }
}

fn opt_is_valid_generic_type<'a>(
    type_path: &TypePath,
    possible_types: &'a [&str],
) -> Option<&'a str> {
    if type_path.path.segments.len() == 1 && type_path.path.segments.first().is_some() {
        let path_segment = &type_path.path.segments.first().unwrap();
        let ident = &path_segment.ident;
        for type_name in possible_types {
            if ident == type_name {
                return Some(type_name);
            }
        }
    }
    None
}

fn is_valid_generic_type(
    type_path: &TypePath,
    possible_types: &[&str],
) -> MacroResult<SupportedGenericReturnTypes> {
    if type_path.path.segments.len() == 1 && type_path.path.segments.first().is_some() {
        let path_segment = &type_path.path.segments.first().unwrap();
        let ident = &path_segment.ident;
        for type_name in possible_types {
            if ident == type_name {
                if type_name == &SupportedGenericReturnTypes::LispResult.to_string().as_str() {
                    return Ok(SupportedGenericReturnTypes::LispResult);
                } else if type_name == &SupportedGenericReturnTypes::Option.to_string().as_str() {
                    return Ok(SupportedGenericReturnTypes::Option);
                }
            }
        }
    }
    Err(Error::new(
        type_path.span(),
        format!(
            "Functions can only return GenericArguments of type {possible_types:?}, try wrapping this value in Option or LispResult."
        ),
    ))
}

fn get_generic_argument_from_type_path(
    type_path: &TypePath,
) -> Option<(&GenericArgument, &TypePath)> {
    if type_path.path.segments.len() == 1 {
        for path_segment in &type_path.path.segments.iter().rev().next() {
            if let PathArguments::AngleBracketed(args) = &path_segment.arguments {
                if let Some(ty) = args.args.iter().rev().next() {
                    return Some((ty, type_path));
                }
            }
        }
    }
    None
}

fn get_generic_argument_from_type(ty: &Type) -> Option<(&GenericArgument, &TypePath)> {
    if let Type::Path(ref type_path) = ty {
        get_generic_argument_from_type_path(type_path)
    } else {
        None
    }
}

fn generate_assertions_code_for_return_type_conversions(return_type: &Type) -> TokenStream2 {
    quote! {
      static_assertions::assert_impl_all!(#return_type: std::convert::Into<crate::types::Expression>);
    }
}

fn get_attribute_value_with_key(
    original_item_fn: &ItemFn,
    key: &str,
    values: &[(String, String)],
) -> MacroResult<Option<String>> {
    if values.is_empty() {
        Err(Error::new(
            original_item_fn.span(),
            "macro requires at least one name-value pair, 'fn_name = \"<name-of-fun>\"'.",
        ))
    } else {
        for name_value in values {
            if name_value.0 == key {
                return Ok(Some(name_value.1.to_string()));
            }
        }
        Ok(None)
    }
}

fn get_bool_attribute_value_with_key(
    original_item_fn: &ItemFn,
    key: &str,
    values: &[(String, String)],
) -> MacroResult<bool> {
    if values.is_empty() {
        Err(Error::new(
            original_item_fn.span(),
            "macro requires at least one name-value pair, 'fn_name = \"<name-of-fun>\"'.",
        ))
    } else {
        for name_value in values {
            if name_value.0 == key {
                return Ok(name_value.1 == "true");
            }
        }
        Ok(false)
    }
}

fn get_attribute_name_value(nested_meta: &NestedMeta) -> MacroResult<(String, String)> {
    match nested_meta {
        NestedMeta::Meta(meta) => match meta {
            Meta::NameValue(pair) => {
                let path = &pair.path;
                let lit = &pair.lit;
                match (path.get_ident(), lit) {
                    (Some(ident), Lit::Str(partial_name)) => {
                        Ok((ident.to_string(), partial_name.value()))
                    }
                    (Some(ident), Lit::Bool(b)) => {
                        Ok((ident.to_string(), b.value.to_string()))
                    }
                    (_, _) => Err(Error::new(
                        meta.span(),
                        "macro requires one name-value pair, 'fn_name'. Supports optional name-value pair 'eval_values = true')",
                    )),
                }
            }
            other => Err(Error::new(
                other.span(),
                "macro only supports one name-value pair attribute argument, 'fn_name'.",
            )),
        },
        other => Err(Error::new(
            other.span(),
            "macro only supports one name-value pair attribute argument, 'fn_name'.",
        )),
    }
}

fn get_type_handle(type_path: &TypePath) -> TypeHandle {
    if let Some((_generic, type_path)) = get_generic_argument_from_type_path(type_path) {
        let wrapper = opt_is_valid_generic_type(type_path, SPECIAL_ARG_TYPES.as_slice());
        match wrapper {
            Some(wrapper) if wrapper == "Option" => {
                return TypeHandle::Optional;
            }
            Some(wrapper) if wrapper == "VarArgs" => {
                return TypeHandle::VarArgs;
            }
            _ => {}
        }
    }
    TypeHandle::Direct
}

fn get_parser_for_type_handle(noop_outer_parse: bool) -> ParamParsingFn {
    match noop_outer_parse {
        true => no_parse_param,
        false => parse_param,
    }
}

fn no_parse_param(
    _dialect: Box<dyn Dialect>,
    _arg_name: &Ident,
    inner: TokenStream,
    _param: Param,
    _required_args: usize,
    _idx: usize,
) -> TokenStream {
    inner
}

fn parse_param(
    _dialect: Box<dyn Dialect>,
    arg_name: &Ident,
    inner: TokenStream,
    param: Param,
    required_args: usize,
    idx: usize,
) -> TokenStream {
    match param.handle {
        TypeHandle::Direct => {
            quote! {
                let param = arg_types[#idx];
                match param.handle {
                    crate::macro_types::TypeHandle::Direct => match args.get(#idx) {
                        None => {
                            return Err(crate::types::LispError::new(format!(
                                "{} not given enough arguments, expected at least {} arguments, got {}.",
                                fn_name,
                                #required_args,
                                args.len()
                            )));
                        }
                        Some(#arg_name) => {
                            #inner
                        },
                    },
                    _ => {
                        return Err(crate::types::LispError::new(format!(
                            "{} failed to parse its arguments, internal error.",
                            fn_name,
                        )));
                    },
                }
            }
        }
        TypeHandle::Optional => {
            quote! {
                let param = arg_types[#idx];
                let arg = args.get(#idx);
                match param.handle {
                    crate::macro_types::TypeHandle::Optional => {
                        let #arg_name = arg.map(|x| x.to_owned());
                        #inner
                    },
                    _ => {
                        return Err(crate::types::LispError::new(format!(
                            "{} failed to parse its arguments, internal error.",
                            fn_name,
                        )));
                    },
                }
            }
        }
        TypeHandle::VarArgs => {
            quote! {
                let param = arg_types[#idx];
                let arg = args.get(#idx);
                match param.handle {
                    crate::macro_types::TypeHandle::VarArgs => {
                        let #arg_name = args[#idx..].iter().map(|x| x.clone()).collect::<Vec<crate::types::Expression>>();
                        #inner
                    },
                    _ => {
                        return Err(crate::types::LispError::new(format!(
                            "{} failed to parse its arguments, internal error.",
                            fn_name,
                        )));
                    }
                }
            }
        }
    }
}

/// create a vec literal of the expected Param types so code can check its arguments at runtime for
/// API arity/type correctness.
fn embed_params_vec(params: &[Param]) -> TokenStream {
    let mut tokens = vec![];
    for param in params {
        tokens.push(match (param.handle, param.passing_style) {
            (TypeHandle::Direct, PassingStyle::MutReference) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::Direct,
                    passing_style: crate::macro_types::PassingStyle::MutReference
                }}
            }
            (TypeHandle::Optional, PassingStyle::MutReference) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::Optional,
                    passing_style: crate::macro_types::PassingStyle::MutReference
                }}
            }
            (TypeHandle::VarArgs, PassingStyle::MutReference) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::VarArgs,
                    passing_style: crate::macro_types::PassingStyle::MutReference
                }}
            }
            (TypeHandle::Direct, PassingStyle::Reference) => {
                quote! {crate::Param {
                    handle: crate::macro_types::TypeHandle::Direct,
                    passing_style: crate::macro_types::PassingStyle::Reference
                }}
            }
            (TypeHandle::Optional, PassingStyle::Reference) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::Optional,
                    passing_style: crate::macro_types::PassingStyle::Reference
                }}
            }
            (TypeHandle::VarArgs, PassingStyle::Reference) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::VarArgs,
                    passing_style: crate::macro_types::PassingStyle::Reference
                }}
            }
            (TypeHandle::Direct, PassingStyle::Value) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::Direct,
                    passing_style: crate::macro_types::PassingStyle::Value
                }}
            }
            (TypeHandle::Optional, PassingStyle::Value) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::Optional,
                    passing_style: crate::macro_types::PassingStyle::Value
                }}
            }
            (TypeHandle::VarArgs, PassingStyle::Value) => {
                quote! { crate::Param {
                    handle: crate::macro_types::TypeHandle::VarArgs,
                    passing_style: crate::macro_types::PassingStyle::Value
                }}
            }
        });
    }
    let const_params_len = get_const_params_len_ident();
    quote! {
        let arg_types: [crate::Param; #const_params_len] = [ #(#tokens),* ];
    }
}

/// create two lists that can be joined by macro syntax to create the inner part of a function
/// signature, e.g. (arg_0: a_type, arg_1: b_type, ...) in some existing rust function:
/// fn myfn(arg_0: a_type, arg_1: b_type, ...) { ... }
fn generate_inner_fn_signature_to_orig_fn_call(
    original_item_fn: &ItemFn,
    takes_env: bool,
) -> MacroResult<Vec<Ident>> {
    let len = if takes_env {
        original_item_fn.sig.inputs.len() - 1
    } else {
        original_item_fn.sig.inputs.len()
    };
    let mut arg_names = vec![];
    for i in 0..len {
        let parse_name = "arg_".to_string() + &i.to_string();
        let parse_name = Ident::new(&parse_name, Span::call_site());
        arg_names.push(parse_name);
    }
    Ok(arg_names)
}

/// return a code for how to refer to the inner exp enum referent type in
/// an function call.
fn tokens_for_matching_references(passing_style: PassingStyle, ty: &TypePath) -> TokenStream {
    match passing_style {
        PassingStyle::Value => quote! {#ty},
        PassingStyle::Reference => quote! {&#ty},
        PassingStyle::MutReference => quote! {& mut #ty},
    }
}

fn get_arg_pos(ident: &Ident) -> MacroResult<String> {
    let arg_string = ident.to_string();
    arg_string.split('_').nth(1).map(|x| x.to_string()).ok_or_else(|| Error::new(
        ident.span(),
        "Arg name should be in form arg_2 which means it should always have two and only two items. Internal error.",
    ))
}

/// None if not Rust type vec
fn is_vec(ty: &TypePath) -> Option<Type> {
    if let Some((ty, type_path)) = get_generic_argument_from_type_path(ty) {
        let wrapper = opt_is_valid_generic_type(type_path, &["Vec"]);
        if let (GenericArgument::Type(ty), Some(_)) = (ty, wrapper) {
            match <Type as Into<RustType>>::into(ty.clone()) {
                RustType::Path(_, _) | RustType::Tuple(_, _) => return Some(ty.clone()),
                _ => {}
            }
        }
    }
    None
}

/// at this point the macro is only operating on types it expects
/// which are any rust types, any rust types wrapped in Option,
/// and any rust types wrapped in Vec. If in the future this is
/// confusing wrapper types can be made, i.e. SlshVarArgs,
/// so normal rust Vec could be used without being turned into
/// a SlshVarArgs
fn get_type_or_wrapped_type<'a>(ty: &'a TypePath, possible_types: &'a [&str]) -> RustType {
    if let Some((ty, type_path)) = get_generic_argument_from_type_path(ty) {
        let wrapper = opt_is_valid_generic_type(type_path, possible_types);
        if let (GenericArgument::Type(ty), Some(_)) = (ty, wrapper) {
            return <Type as Into<RustType>>::into(ty.clone());
        }
    }
    RustType::Path(ty.clone(), ty.span())
}

fn num_required_args(params: &[Param]) -> usize {
    params.iter().fold(0, |accum, nxt| {
        if nxt.handle == TypeHandle::Direct {
            accum + 1
        } else {
            accum
        }
    })
}

/// Optional and VarArgs types are supported to create the idea of items that might be provided or
/// for providing a list of zero or more items that can be passed in.
///
/// The nature of varargs and optional parameters are context dependent because variable numbers of
/// arguments (VarArgs) are singletons that have to be at the end of the function signature, and
/// optional arguments (Optional) must appear after non-optional ones.
///
/// Formally this method verifies that parameters marked as Optional are last, and one VarArgs parameter
/// is supported but only in the last position, which can be after zero or more Optional arguments.
/// This means non Optional/VarArgs types must come before all Optional and VarArgs types and all
/// Optional types must come before one VarArgs type.
fn are_args_valid(original_item_fn: &ItemFn, params: &[Param], takes_env: bool) -> MacroResult<()> {
    if params.is_empty() || (!takes_env && params.len() == 1 || takes_env && params.len() == 2) {
        Ok(())
    } else {
        let mut found_opt = false;
        let mut found_value = false;
        for (i, param) in params.iter().rev().enumerate() {
            match (i, param.handle, found_opt, found_value) {
                (i, TypeHandle::VarArgs, _, _) if i > 0 => {
                    return Err(Error::new(
                        original_item_fn.span(),
                        "Only one Vec argument is supported and it must be the last argument.",
                    ));
                }
                (_, TypeHandle::Optional, _, true) => {
                    return Err(Error::new(
                        original_item_fn.span(),
                        "Optional argument(s) must be placed last.",
                    ));
                }
                (_, TypeHandle::Optional, _, _) => {
                    found_opt = true;
                }
                (_, TypeHandle::Direct, _, _) => {
                    found_value = true;
                }
                (_, _, _, _) => {}
            }
        }
        Ok(())
    }
}

fn get_param_from_type(ty: Type, span: Span, pos: usize) -> MacroResult<Param> {
    let ty_clone = ty.clone();
    let param = match <Type as Into<RustType>>::into(ty) {
        RustType::Path(ty, _span) => {
            let val = get_type_handle(&ty);
            Param {
                handle: val,
                passing_style: PassingStyle::Value,
            }
        }
        RustType::Tuple(_type_tuple, _span) => Param {
            handle: TypeHandle::Direct,
            passing_style: PassingStyle::Value,
        },
        RustType::Reference(ty_ref, _span) => {
            let passing_style = if ty_ref.mutability.is_some() {
                PassingStyle::MutReference
            } else {
                PassingStyle::Reference
            };
            match <Type as Into<RustType>>::into(*ty_ref.elem) {
                RustType::Path(ty, _span) => {
                    let val = get_type_handle(&ty);
                    Param {
                        handle: val,
                        passing_style,
                    }
                }
                RustType::Tuple(_type_tuple, _span) => Param {
                    handle: TypeHandle::Direct,
                    passing_style,
                },
                _ => {
                    return Err(Error::new(
                        span,
                        format!(
                            "Error with argument at position {}, macro only supports passing Type::Path and Type::Tuple by value or ref/ref mut, no either syn::Type's are supported: {:?}.",
                            pos,
                            ty_clone.to_token_stream(),
                        ),
                    ));
                }
            }
        }
        _ => {
            return Err(Error::new(
                span,
                format!(
                    "Error with argument at position {}, macro only supports passing Type::Path and Type::Tuple by value or ref/ref mut, no either syn::Type's are supported: {:?}.",
                    pos,
                    ty_clone.to_token_stream(),
                ),
            ));
        }
    };
    Ok(param)
}

/// Create a Vec<Arg> from the original fn's signature. Information is needed at compile and
/// run time to translate the list of sl_sh expressions to rust native types. This Arg types
/// stores the information about the rust native type (Value/Option/Var) as well as whether it's moved, passed
/// by reference, or passed by mutable reference.
fn parse_src_function_arguments(
    original_item_fn: &ItemFn,
    takes_env: bool,
) -> MacroResult<Vec<Param>> {
    let mut parsed_args = vec![];
    let len = if takes_env {
        original_item_fn.sig.inputs.len() - 1
    } else {
        original_item_fn.sig.inputs.len()
    };
    let mut arg_names = vec![];
    for i in 0..len {
        let parse_name = "arg_".to_string() + &i.to_string();
        let parse_name = Ident::new(&parse_name, Span::call_site());
        arg_names.push(parse_name);
    }

    let skip = usize::from(takes_env);

    for (i, fn_arg) in original_item_fn.sig.inputs.iter().enumerate().skip(skip) {
        match fn_arg {
            FnArg::Receiver(_) => {
                return Err(Error::new(
                    original_item_fn.span(),
                    "Associated functions that take the self argument are not supported.",
                ))
            }
            FnArg::Typed(ty) => {
                parsed_args.push(get_param_from_type(
                    *ty.ty.clone(),
                    original_item_fn.span(),
                    i,
                )?);
            }
        }
    }
    Ok(parsed_args)
}

/// return the function names the macro will create. Given a base name, <base>
/// return intern_<base> Ident to be used as function name
fn get_intern_fn_name(original_fn_name: &str) -> Ident {
    let builtin_name = "intern_".to_string() + original_fn_name;
    Ident::new(&builtin_name, Span::call_site())
}

/// return the function names the macro will create. Given a base name, <base>
/// return parse_<base> Ident to be used as function name
fn get_parse_fn_name(original_fn_name: &str) -> Ident {
    let builtin_name = "parse_".to_string() + original_fn_name;
    Ident::new(&builtin_name, Span::call_site())
}

/// Pull out every #doc attribute on the target fn for the proc macro attribute.
/// Ignore any other attributes and only Err if there are no #doc attributes.
fn get_documentation_for_fn(original_item_fn: &ItemFn) -> MacroResult<String> {
    let mut docs = "".to_string();
    for attr in &original_item_fn.attrs {
        for path_segment in attr.path.segments.iter() {
            if &path_segment.ident.to_string() == "doc" {
                if let Ok(Meta::NameValue(pair)) = attr.parse_meta() {
                    if let Lit::Str(partial_name) = &pair.lit {
                        docs += &*partial_name.value();
                        docs += "\n";
                    }
                }
            }
        }
    }
    if docs.is_empty() {
        Err(Error::new(
            original_item_fn.span(),
            "Functions with this attribute included must have documentation.",
        ))
    } else {
        Ok(docs)
    }
}

fn get_const_params_len_ident() -> Ident {
    Ident::new("PARAMS_LEN", Span::call_site())
}

fn parse_attributes(
    original_item_fn: &ItemFn,
    attr_args: AttributeArgs,
) -> MacroResult<(String, Ident, bool, bool, bool)> {
    let vals = attr_args
        .iter()
        .map(get_attribute_name_value)
        .collect::<MacroResult<Vec<(String, String)>>>()?;
    let fn_name_ident = "fn_name".to_string();
    let fn_name = get_attribute_value_with_key(original_item_fn, &fn_name_ident, vals.as_slice())?
        .ok_or_else(|| {
            Error::new(
                original_item_fn.span(),
                "macro requires name-value pair, 'fn_name'",
            )
        })?;
    let fn_name_ident = Ident::new(&fn_name_ident, Span::call_site());

    let eval_values =
        get_bool_attribute_value_with_key(original_item_fn, "eval_values", vals.as_slice())?;
    let takes_env =
        get_bool_attribute_value_with_key(original_item_fn, "takes_env", vals.as_slice())?;

    // all functions default to inlining unless explicitly overriden.
    let inline =
        !get_bool_attribute_value_with_key(original_item_fn, "do_not_inline", vals.as_slice())?;

    Ok((fn_name, fn_name_ident, eval_values, takes_env, inline))
}

/// this function outputs all of the generated code, it is composed into two different functions:
/// intern_<original_fn_name>
/// parse_<original_fn_name>
/// - intern_ is the simplest function, it is generated to be called within sl-sh to avoid writing
/// boilerplate code to submit a function symbol and the associated code to the runtime.
/// - parse_ has the same function signature as all rust native functions, it takes the environment
/// and a list of args. It evals those arguments at runtime and converts them to rust types
/// they can be consumed by the target rust function.
fn generate_sl_sh_fn<T: Dialect>(
    dialect: T,
    original_item_fn: &ItemFn,
    attr_args: AttributeArgs,
) -> MacroResult<TokenStream> {
    let (fn_name, fn_name_ident, eval_values, takes_env, inline) =
        parse_attributes(original_item_fn, attr_args)?;
    let original_fn_name_str = original_item_fn.sig.ident.to_string();
    let original_fn_name_str = original_fn_name_str.as_str();

    let params = parse_src_function_arguments(original_item_fn, takes_env)?;
    are_args_valid(original_item_fn, params.as_slice(), takes_env)?;
    let builtin_fn = dialect.generate_builtin_fn(
        original_item_fn,
        original_fn_name_str,
        fn_name.as_str(),
        params.as_slice(),
        &fn_name_ident,
        takes_env,
        inline,
    )?;

    let args_len = if takes_env {
        original_item_fn.sig.inputs.len() - 1
    } else {
        original_item_fn.sig.inputs.len()
    };
    let parse_fn = dialect.generate_parse_fn(
        original_fn_name_str,
        eval_values,
        &fn_name_ident,
        fn_name.as_str(),
        args_len,
        params.as_slice(),
        builtin_fn,
    );
    let doc_comments = get_documentation_for_fn(original_item_fn)?;
    let intern_fn = dialect.generate_intern_fn(
        original_fn_name_str,
        &fn_name_ident,
        fn_name.as_str(),
        doc_comments,
    );
    let tokens = quote! {
        #parse_fn

        #intern_fn
    };
    Ok(tokens)
}

fn generate_macro_code<T: Dialect>(
    dialect: T,
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr_args = parse_macro_input!(attr as AttributeArgs);

    let tokens = match parse::<Item>(input) {
        Ok(item) => match &item {
            Item::Fn(original_item_fn) => {
                let generated_code = match generate_sl_sh_fn(dialect, original_item_fn, attr_args) {
                    Ok(generated_code) => generated_code,
                    Err(e) => e.to_compile_error(),
                };
                let original_fn_code = item.into_token_stream();
                quote! {
                    #generated_code

                    #[allow(dead_code)]
                    #original_fn_code
                }
            }
            _ => Error::new(item.span(), "This attribute only supports functions.")
                .to_compile_error(),
        },
        Err(e) => Error::new(e.span(), "Failed to parse proc_macro_attribute.").to_compile_error(),
    };

    proc_macro::TokenStream::from(tokens)
}

/// Macro that creates a bridge between rust native code and sl-sh code. Specify the lisp
/// function name to be interned with the "fn_name" attribute. This macro outputs all of the
/// generated bridge code as well as the original function's code so it can be used
/// by the generated bridge code.
#[proc_macro_attribute]
pub fn sl_sh_fn(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    generate_macro_code(SlSh {}, attr, input)
}

/// Macro that creates a bridge between rust native code and slosh code. Specify the lisp
/// function name to be interned with the "fn_name" attribute. This macro outputs all of the
/// generated bridge code as well as the original function's code so it can be used
/// by the generated bridge code.
#[proc_macro_attribute]
pub fn sl_vm_fn(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    generate_macro_code(Slosh {}, attr, input)
}

//TODO
//  - functions that return Values, tuple return types?
//  - fcns that accept iters?
//  - then... compare against inline the function being called... randomize variable names...
//      and fn names too? could pick some random string and prefix all generated idents.

#[cfg(test)]
mod test {
    use super::*;
    use std::convert::TryInto;

    // serves as a model for what it's like at runtime to iterate over the parameters of a function,
    // T serves as a generic so these tests can run with some data, but in practice T is some
    // type from the consuming library.
    fn loop_over_to_inline<T, const N: usize>(
        fn_name: &str,
        params: &[Param; N],
        args: &[T],
    ) -> Result<(), String> {
        let required_args = num_required_args(params);
        for idx in 0..N {
            to_inline(fn_name, idx, required_args, params, args)?;
        }
        if N > 0 {
            too_many_args_detection(fn_name, params, N, args)?;
        }

        Ok(())
    }

    // run last to see if the number of received arguments has exceeded the number expected based
    // on the arity of the rust function, and whether or not it ends in a varargs/array.
    fn too_many_args_detection<T>(
        fn_name: &str,
        arg_types: &[Param],
        len: usize,
        args: &[T],
    ) -> Result<(), String> {
        match args.get(len) {
            Some(_) if arg_types[len - 1].handle != TypeHandle::VarArgs => {
                return Err(format!(
                    "{} given too many arguments, expected {}, got {}.",
                    fn_name,
                    arg_types.len(),
                    args.len()
                ));
            }
            _ => {
                //macro
                println!("macro")
            }
        }
        Ok(())
    }

    // loop over each input and check based on current idx and presence of Arg or not
    // whether the args received is lower than needed based on the arity of the rust function.
    fn to_inline<T>(
        fn_name: &str,
        idx: usize,
        required_args: usize,
        params: &[Param],
        args: &[T],
    ) -> Result<(), String> {
        let param = params[idx];
        match args.get(idx) {
            None if param.handle == TypeHandle::Direct => {
                return Err(format!(
                    "{} not given enough arguments, expected at least {} arguments, got {}.",
                    fn_name,
                    required_args,
                    args.len()
                ));
            }
            _arg => {
                // insert
                println!("macro");
            }
        }
        Ok(())
    }
    struct Foo {}

    #[test]
    fn test_params_values_only() {
        let two_moved_values = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
        ];

        // if there are not enough arguments we throw an error.
        let args = vec![Foo {}];
        let args = loop_over_to_inline::<Foo, 2>(
            "foo",
            two_moved_values.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("not given enough arguments"));

        // if there are too many arguments we throw an error.
        let args = vec![Foo {}, Foo {}, Foo {}];
        let args = loop_over_to_inline::<Foo, 2>(
            "foo",
            two_moved_values.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("given too many"));

        let args = vec![Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 2>(
            "foo",
            two_moved_values.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
    }

    #[test]
    fn test_params_optionals() {
        let one_val_one_opt = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
        ];
        let args = vec![Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 2>(
            "foo",
            one_val_one_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![Foo {}];
        loop_over_to_inline::<Foo, 2>(
            "foo",
            one_val_one_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![];
        let args = loop_over_to_inline::<Foo, 2>(
            "foo",
            one_val_one_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("not given enough arguments"));

        let args = vec![Foo {}, Foo {}, Foo {}];
        let args = loop_over_to_inline::<Foo, 2>(
            "foo",
            one_val_one_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("given too many"));

        let val_and_opt = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
        ];
        let args = vec![Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 2>(
            "foo",
            val_and_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![Foo {}];
        loop_over_to_inline::<Foo, 2>(
            "foo",
            val_and_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![];
        let args = loop_over_to_inline::<Foo, 2>(
            "foo",
            val_and_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("not given enough arguments"));

        let args = vec![Foo {}, Foo {}, Foo {}];
        let args = loop_over_to_inline::<Foo, 2>(
            "foo",
            val_and_opt.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("given too many"));
    }

    #[test]
    fn test_params_vec() {
        let one_vec = vec![Param {
            handle: TypeHandle::VarArgs,
            passing_style: PassingStyle::MutReference,
        }];

        let args = vec![];
        loop_over_to_inline::<Foo, 1>(
            "foo",
            one_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![Foo {}];
        loop_over_to_inline::<Foo, 1>(
            "foo",
            one_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 1>(
            "foo",
            one_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let args = vec![Foo {}, Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 1>(
            "foo",
            one_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
    }

    #[test]
    fn test_params_vec_with_options() {
        let val_opt_and_vec = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::MutReference,
            },
            Param {
                handle: TypeHandle::VarArgs,
                passing_style: PassingStyle::Value,
            },
        ];

        let args = vec![];
        let args = loop_over_to_inline::<Foo, 3>(
            "foo",
            val_opt_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        );
        assert!(args.unwrap_err().contains("not given enough arguments"));
        let args = vec![Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            val_opt_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            val_opt_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}, Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            val_opt_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}, Foo {}, Foo {}, Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            val_opt_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");

        let opts_and_vec = vec![
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::MutReference,
            },
            Param {
                handle: TypeHandle::VarArgs,
                passing_style: PassingStyle::Value,
            },
        ];

        let args = vec![];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            opts_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            opts_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            opts_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}, Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            opts_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
        let args = vec![Foo {}, Foo {}, Foo {}, Foo {}, Foo {}];
        loop_over_to_inline::<Foo, 3>(
            "foo",
            opts_and_vec.as_slice().try_into().unwrap(),
            args.as_slice(),
        )
        .expect("Parsing should succeed.");
    }
}
