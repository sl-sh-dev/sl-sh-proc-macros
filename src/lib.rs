use quote::quote;
use quote::ToTokens;
use quote::__private::TokenStream;
use std::fmt::{Display, Formatter};
use syn::__private::{Span, TokenStream2};
use syn::spanned::Spanned;
use syn::{
    parse, parse_macro_input, AttributeArgs, Error, FnArg, GenericArgument, Ident, Item, ItemFn,
    Lit, Meta, NestedMeta, PathArguments, ReturnType, Type, TypeBareFn, TypePath, TypeReference,
    TypeTuple,
};
extern crate static_assertions;

type MacroResult<T> = Result<T, Error>;

const POSSIBLE_RETURN_TYPES: [&str; 2] = ["LispResult", "Option"];
const SPECIAL_ARG_TYPES: [&str; 2] = ["Option", "VarArgs"];
const POSSIBLE_ARG_TYPES: [&str; 3] = ["Option", "VarArgs", "Vec"];

#[derive(Copy, Clone)]
enum SupportedGenericReturnTypes {
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
            // Type::Array(_) => {} // TODO
            // Type::Slice(_) => {} // TODO
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

/// returns the option of inner type and the wrapped generic type (None if it's
/// not generic. If there is no return type None, None is returned. Throws
/// an error if the generic return type is not in the list of predefined
/// constants POSSIBLE_RESULT_TYPES.
fn get_return_type(
    original_item_fn: &ItemFn,
) -> MacroResult<(Option<Type>, Option<SupportedGenericReturnTypes>)> {
    let return_type = match &original_item_fn.sig.output {
        ReturnType::Default => return Ok((None, None)),
        ReturnType::Type(_ra_arrow, ty) => *ty.clone(),
    };

    if let Some((inner_type, type_path)) = get_generic_argument_from_type(&return_type) {
        let wrapper = is_valid_generic_type(type_path, POSSIBLE_RETURN_TYPES.as_slice())?;
        match inner_type {
            GenericArgument::Type(ty) => Ok((Some(ty.clone()), Some(wrapper))),
            _ => Err(Error::new(
                original_item_fn.span(),
                format!(
                    "sl_sh_fn macros can only return generic arguments of types {:?}.",
                    &POSSIBLE_RETURN_TYPES
                ),
            )),
        }
    } else {
        Ok((Some(return_type), None))
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

fn is_valid_generic_type<'a>(
    type_path: &TypePath,
    possible_types: &'a [&str],
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
                "Functions of with generic arguments of type {:?} must contain Types, see GenericArgument.",
                possible_types
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
            "sl_sh_fn requires at least one name-value pair, 'fn_name = \"<name-of-sl-sh-fun>\"'.",
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
                        "sl_sh_fn requires one name-value pair, 'fn_name'. Supports optional name-value pair 'eval_values = true')",
                    )),
                }
            }
            other => Err(Error::new(
                other.span(),
                "sl_sh_fn only supports one name-value pair attribute argument, 'fn_name'.",
            )),
        },
        other => Err(Error::new(
            other.span(),
            "sl_sh_fn only supports one name-value pair attribute argument, 'fn_name'.",
        )),
    }
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum TypeHandle {
    Direct,
    Optional,
    VarArgs,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum PassingStyle {
    Value,
    Reference,
    MutReference,
}

#[derive(Copy, Clone, Debug, PartialEq)]
struct Param {
    handle: TypeHandle,
    passing_style: PassingStyle,
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

fn no_parse_param(_arg_name: &Ident, inner: TokenStream, _param: Param) -> TokenStream {
    inner
}

fn parse_param(arg_name: &Ident, inner: TokenStream, param: Param) -> TokenStream {
    match (param.handle, param.passing_style) {
        (TypeHandle::Direct, PassingStyle::Value) => {
            //quote! {
            //        #arg_name;
            //        crate::ArgType::Exp(#arg_name);
            //        #inner;
            //}
        }
        (TypeHandle::Direct, PassingStyle::Reference) => {}
        (TypeHandle::Direct, PassingStyle::MutReference) => {}
        (TypeHandle::Optional, PassingStyle::Value) => {}
        (TypeHandle::Optional, PassingStyle::Reference) => {}
        (TypeHandle::Optional, PassingStyle::MutReference) => {}
        (TypeHandle::VarArgs, PassingStyle::Value) => {}
        (TypeHandle::VarArgs, PassingStyle::Reference) => {}
        (TypeHandle::VarArgs, PassingStyle::MutReference) => {}
    }
    quote! {}
}

fn no_parse(_arg_name: &Ident, inner: TokenStream) -> TokenStream {
    inner
}

fn parse_value(arg_name: &Ident, inner: TokenStream) -> TokenStream {
    quote! {
        crate::ret_err_exp_enum!(
                #arg_name,
                crate::ArgType::Exp(#arg_name),
                #inner,
                "sl_sh_fn macro is broken. ArgType::Exp can't be parsed as ArgType::Exp"
            )
    }
}

fn parse_optional(arg_name: &Ident, inner: TokenStream) -> TokenStream {
    quote! {
        crate::ret_err_exp_enum!(
                #arg_name,
                crate::ArgType::Opt(#arg_name),
                #inner,
                "sl_sh_fn macro is broken. Alleged ArgType::Opt can't be parsed as ArgType::Opt"
            )
    }
}

fn parse_varargs(arg_name: &Ident, inner: TokenStream) -> TokenStream {
    quote! {
        crate::ret_err_exp_enum!(
                #arg_name,
                crate::ArgType::VarArgs(#arg_name),
                #inner,
                "sl_sh_fn macro is broken. Alleged ArgType::Vargs can't be parsed as ArgType::Vargs"
            )
    }
}

//TODO PR #3 must completely remove ArgType in both repos once new sl_sh_fn2 is ready
fn get_parser_for_type_handle(
    val: TypeHandle,
    noop_outer_parse: bool,
) -> fn(&Ident, TokenStream) -> TokenStream {
    match (val, noop_outer_parse) {
        (_, true) => no_parse,
        (TypeHandle::Direct, false) => parse_value,
        (TypeHandle::Optional, false) => parse_optional,
        (TypeHandle::VarArgs, false) => parse_varargs,
    }
}

//TODO PR #3 must completely remove ArgType in both repos once new sl_sh_fn2 is ready
fn get_parser_for_type_handle2(
    param: Param,
    noop_outer_parse: bool,
) -> fn(&Ident, TokenStream, Param) -> TokenStream {
    match (param.handle, param.passing_style, noop_outer_parse) {
        (_, _, true) => no_parse_param,
        (_, _, false) => parse_param,
    }
}

fn make_orig_fn_call(
    takes_env: bool,
    original_item_fn: &ItemFn,
    original_fn_name: &Ident,
    arg_names: Vec<Ident>,
) -> MacroResult<TokenStream> {
    // the original function call must return an Expression object
    // this means all returned rust native types must implement TryIntoExpression
    // this is nested inside the builtin expression which must always
    // return a LispResult.
    let takes_env = if takes_env {
        quote! {env, } // env is the name that is passed in to this function
    } else {
        quote! {}
    };
    let (return_type, lisp_return) = get_return_type(original_item_fn)?;
    let returns_none = "()" == return_type.to_token_stream().to_string();
    let original_fn_call = match (return_type, lisp_return, returns_none) {
        (Some(_), Some(SupportedGenericReturnTypes::LispResult), true) => quote! {
            #original_fn_name(#takes_env #(#arg_names),*)?;
            Ok(crate::types::Expression::make_nil())
        },
        (Some(_), Some(SupportedGenericReturnTypes::Option), true) => quote! {
            #original_fn_name(#takes_env #(#arg_names),*);
            Ok(crate::types::Expression::make_nil())
        },
        (Some(_), Some(SupportedGenericReturnTypes::LispResult), false) => quote! {
            #original_fn_name(#takes_env #(#arg_names),*).map(Into::into)
        },
        (Some(_), Some(SupportedGenericReturnTypes::Option), false) => quote! {
            if let Some(val) = #original_fn_name(#takes_env #(#arg_names),*) {
                Ok(val.into())
            } else {
                Ok(crate::types::Expression::make_nil())
            }
        },
        // coerce to Expression
        (Some(_), None, _) => quote! {
            Ok(#original_fn_name(#takes_env #(#arg_names),*).into())
        },
        (None, Some(_), _) => {
            unreachable!("If this functions returns a LispResult it must also return a value.");
        }
        // no return
        (None, None, _) => quote! {
            #original_fn_name(#takes_env #(#arg_names),*);
            Ok(crate::types::Expression::make_nil())
        },
    };
    Ok(quote! {
        #original_fn_call
    })
}

/// create two lists that can be joined by macro syntax to create the inner part of a function
/// signature, e.g. (arg_0: a_type, arg_1: b_type, ...) in some existing rust function:
/// fn myfn(arg_0: a_type, arg_1: b_type, ...) { ... }
fn generate_inner_fn_signature_to_orig_fn_call2(
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

/// create two lists that can be joined by macro syntax to create the inner part of a function
/// signature, e.g. (arg_0: a_type, arg_1: b_type, ...) in some existing rust function:
/// fn myfn(arg_0: a_type, arg_1: b_type, ...) { ... }
fn generate_inner_fn_signature_to_orig_fn_call(
    original_item_fn: &ItemFn,
    takes_env: bool,
) -> MacroResult<(Vec<Ident>, Vec<TokenStream>)> {
    let len = if takes_env {
        original_item_fn.sig.inputs.len() - 1
    } else {
        original_item_fn.sig.inputs.len()
    };
    let mut arg_names = vec![];
    let mut arg_types = vec![];
    for i in 0..len {
        let parse_name = "arg_".to_string() + &i.to_string();
        let parse_name = Ident::new(&parse_name, Span::call_site());
        arg_names.push(parse_name);
        arg_types.push(quote! { crate::ArgType })
    }
    Ok((arg_names, arg_types))
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

/// if expecting a Vec then the actual expression itself should be iterable
/// (Pair/Vector/Nil), set arg_name_itself_is_iter = true. Otherwise it's
/// varargs which means the original args vector is passed in and
/// iterated over. the implication of passing in Vec is that if the Exp
/// doesn't match one of a few underlying sl-sh types passing it to
/// this function is an error.
fn parse_variadic_args_type(
    arg_name_itself_is_iter: bool,
    ty: &TypePath,
    fn_name: &str,
    arg_name: &Ident,
    inner: TokenStream,
    collect_type: TokenStream,
) -> MacroResult<TokenStream> {
    let rust_type = get_type_or_wrapped_type(ty, POSSIBLE_ARG_TYPES.as_slice());
    let arg_pos = get_arg_pos(arg_name)?;
    match rust_type {
        RustType::Path(wrapped_ty, _span) => {
            let arg_check = if arg_name_itself_is_iter {
                quote! {
                    if !crate::is_sequence!(#arg_name)
                    {
                        let err_str = format!("{}: Expected a vector or list for argument at position {}.", #fn_name, #arg_pos);
                        return Err(LispError::new(err_str));
                    }
                }
            } else {
                quote! {}
            };
            Ok(quote! {{
                #arg_check
                use crate::builtins_util::TryIntoExpression;

                static_assertions::assert_impl_all!(crate::types::Expression: crate::builtins_util::TryIntoExpression<#wrapped_ty>);
                let #arg_name = #arg_name
                    .iter()
                    .map(|#arg_name| {
                        #arg_name.clone().try_into_for(#fn_name)
                    })
                    .collect::<crate::LispResult<#ty>>()?;
                #inner
            }})
        }
        RustType::Tuple(type_tuple, _span) => {
            if !type_tuple.elems.is_empty() {
                let arg_pos = get_arg_pos(arg_name)?;
                let arg_check = if arg_name_itself_is_iter {
                    quote! {
                        if !crate::is_sequence!(#arg_name)
                        {
                            let err_str = format!("{}: Expected a vector or list for argument at position {}.", #fn_name, #arg_pos);
                            return Err(LispError::new(err_str));
                        }
                    }
                } else {
                    quote! {}
                };
                let tuple_len = type_tuple.elems.len();
                let arg_name_base = arg_name.to_string() + "_";
                let arg_names = (0..type_tuple.elems.len())
                    .into_iter()
                    .map(|x| {
                        Ident::new(
                            &(arg_name_base.to_string() + &x.to_string()),
                            Span::call_site(),
                        )
                    })
                    .collect::<Vec<Ident>>();
                let mut types = vec![];
                let mut type_assertions = vec![];
                let mut args = vec![];
                for (elem, arg_name) in type_tuple.elems.iter().zip(arg_names.iter()) {
                    types.push(elem.clone());
                    type_assertions.push(quote! {
                        static_assertions::assert_impl_all!(crate::types::Expression: crate::builtins_util::TryIntoExpression<#elem>);
                    });
                    args.push(quote! {
                        let #arg_name: #elem = #arg_name.clone().try_into_for(#fn_name)?;
                    })
                }
                Ok(quote! {{
                    use crate::builtins_util::TryIntoExpression;
                    use std::convert::TryInto;
                    #(#type_assertions)*
                    #arg_check
                    let #arg_name = #arg_name
                        .iter()
                        .map(|#arg_name| {
                            let #arg_name = #arg_name.iter().collect::<Vec<crate::types::Expression>>();
                            match #arg_name.try_into() {
                                Ok(#arg_name) => {
                                    let #arg_name: [crate::Expression; #tuple_len] = #arg_name;
                                    let [#(#arg_names),*] = #arg_name;
                                    #(#args)*
                                    Ok((#(#arg_names),*))
                                }
                                Err(_) => {
                                    let err_str = format!("{}: Expected a sl_sh vector or list of tuples of length {} corresponding to the argument at position {}.", #fn_name, #tuple_len, #arg_pos);
                                    Err(LispError::new(err_str))
                                }
                            }
                        })
                        .collect::<crate::LispResult<#collect_type<(#(#types),*)>>>()?;
                    #inner
                }})
            } else {
                let arg_pos = get_arg_pos(arg_name)?;
                let err_str = format!(
                    "Error with argument at position {}, sl_sh_fn only supports tuple pairs.",
                    arg_pos
                );
                Err(Error::new(type_tuple.span(), err_str))
            }
        }
        ty => {
            let err_str = "Vec<T> and VarArgs<T> only support T of type Type::Path or Type::Tuple.";
            Err(Error::new(ty.span(), err_str))
        }
    }
}

/// for Option<Expression> values the ref_exp must first be parsed as an
/// Option, and only in the case that the option is Some will it be
/// necessary to match against every ExpEnum variant.
fn parse_optional_type(
    ty: &TypePath,
    fn_name: &str,
    fn_name_attr: &Ident,
    arg_name: &Ident,
    passing_style: PassingStyle,
    inner: TokenStream,
) -> MacroResult<TokenStream> {
    let some_inner = quote! {
        let #arg_name = Some(#arg_name);
        #inner
    };
    // in the case that the value is some, which means the Expression is no longer
    // wrapped in Option, the parse_typehandle_value_type can be repurposed but
    // with the caveat that after the value of inner it is handed first wraps
    // the matched ExpEnum in Some bound to the #arg_name like the
    // rust native function expects.
    let some_arg_value_type_parsing_code = parse_direct_type(
        ty,
        fn_name,
        fn_name_attr,
        arg_name,
        passing_style,
        some_inner,
    )?;
    Ok(quote! {
        match #arg_name {
            None => {
                let #arg_name = None;
                #inner
            }
            Some(#arg_name) => {
               #some_arg_value_type_parsing_code
            }
        }
    })
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

/// for regular Expression values (no Optional/VarArgs) ref_exp
/// just needs to be matched based on it's ExpEnum variant.
fn parse_direct_type(
    ty: &TypePath,
    fn_name: &str,
    fn_name_attr: &Ident,
    arg_name: &Ident,
    passing_style: PassingStyle,
    inner: TokenStream,
) -> MacroResult<TokenStream> {
    if is_vec(ty).is_some() {
        parse_variadic_args_type(true, ty, fn_name, arg_name, inner, quote! { Vec })
    } else {
        let ty = get_type_or_wrapped_type(ty, SPECIAL_ARG_TYPES.as_slice());
        match ty {
            RustType::Path(ty, _span) => {
                let str = ty.to_token_stream().to_string();
                // handle &str differently, want impl RustProcedure<F> for TypedWrapper<&str>
                // w/o this special case it generate RustProcedureRefMut on a TypedWrapper<str> which is unsized.
                let (fn_ref, passing_style, ty) =
                    if str == "str" && passing_style == PassingStyle::Reference {
                        let passing_style = PassingStyle::Value;
                        (quote! { &#ty }, passing_style, quote! { &#ty })
                    } else {
                        (
                            tokens_for_matching_references(passing_style, &ty),
                            passing_style,
                            quote! { #ty },
                        )
                    };
                let callback_declaration = quote! {
                    let callback = |#arg_name: #fn_ref| -> crate::LispResult<crate::types::Expression> {
                        #inner
                    };
                };

                match passing_style {
                    PassingStyle::Value => Ok(quote! {{
                        use crate::types::RustProcedure;
                        let typed_data: crate::types::TypedWrapper<#ty, crate::types::Expression> =
                            crate::types::TypedWrapper::new(#arg_name);
                        #callback_declaration
                        typed_data.apply(#fn_name_attr, callback)
                    }}),
                    PassingStyle::Reference => Ok(quote! {{
                        use crate::types::RustProcedureRef;
                        let typed_data: crate::types::TypedWrapper<#ty, crate::types::Expression> =
                            crate::types::TypedWrapper::new(#arg_name);
                        #callback_declaration
                        typed_data.apply_ref(#fn_name_attr, callback)
                    }}),
                    PassingStyle::MutReference => Ok(quote! {{
                        use crate::types::RustProcedureRefMut;
                        let mut typed_data: crate::types::TypedWrapper<#ty, crate::types::Expression> =
                            crate::types::TypedWrapper::new(#arg_name);
                        #callback_declaration
                        typed_data.apply_ref_mut(#fn_name_attr, callback)
                    }}),
                }
            }
            RustType::Tuple(type_tuple, _span) => parse_type_tuple(
                &type_tuple,
                fn_name,
                fn_name_attr,
                inner,
                arg_name,
                no_parse,
            ),
            RustType::BareFn(_, _) | RustType::Reference(_, _) | RustType::Unsupported(_) => {
                let arg_pos = get_arg_pos(arg_name)?;
                let err_str = format!(
                    "Error with argument at position {}, sl_sh_fn only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                    arg_pos
                );
                Err(Error::new(ty.span(), err_str))
            }
        }
    }
}

/// create the nested match statements to parse rust types into sl_sh types.
/// the rust types will determine what sl_sh functions will be used for
/// transformation. If this function throws errors it means that the
/// inputs, val/passing style are wrong and aren't matching to the ArgType(s)
/// properly, or the rust type lookup function is busted.
fn parse_type(
    ty: &TypePath,
    fn_name: (&str, &Ident),
    inner: TokenStream,
    val: TypeHandle,
    arg_name: &Ident,
    passing_style: PassingStyle,
    outer_parse: fn(&Ident, TokenStream) -> TokenStream,
) -> MacroResult<TokenStream> {
    let tokens = match val {
        TypeHandle::Direct => {
            parse_direct_type(ty, fn_name.0, fn_name.1, arg_name, passing_style, inner)?
        }
        TypeHandle::Optional => {
            parse_optional_type(ty, fn_name.0, fn_name.1, arg_name, passing_style, inner)?
        }
        TypeHandle::VarArgs => parse_variadic_args_type(
            false,
            ty,
            fn_name.0,
            arg_name,
            inner,
            quote! { crate::VarArgs },
        )?,
    };
    Ok(outer_parse(arg_name, tokens))
}

/// create the nested match statements to parse rust types into sl_sh types.
/// the rust types will determine what sl_sh functions will be used for
/// transformation. If this function throws errors it means that the
/// inputs, val/passing style are wrong and aren't matching to the ArgType(s)
/// properly, or the rust type lookup function is busted.
fn parse_type2(
    ty: &TypePath,
    fn_name: (&str, &Ident),
    inner: TokenStream,
    param: Param,
    arg_name: &Ident,
    passing_style: PassingStyle,
    outer_parse: fn(&Ident, TokenStream, Param) -> TokenStream,
) -> MacroResult<TokenStream> {
    let tokens = match param.handle {
        TypeHandle::Direct => {
            parse_direct_type(ty, fn_name.0, fn_name.1, arg_name, passing_style, inner)?
        }
        TypeHandle::Optional => {
            parse_optional_type(ty, fn_name.0, fn_name.1, arg_name, passing_style, inner)?
        }
        TypeHandle::VarArgs => parse_variadic_args_type(
            false,
            ty,
            fn_name.0,
            arg_name,
            inner,
            quote! { crate::VarArgs },
        )?,
    };
    Ok(outer_parse(arg_name, tokens, param))
}

/// create a vec literal of the expected Param types so code can check its arguments at runtime for
/// API arity/type correctness.
/// TODO have this return a generated const array.
fn embed_params_vec(params: &[Param]) -> TokenStream {
    let mut tokens = vec![];
    for param in params {
        tokens.push(match (param.handle, param.passing_style) {
            (TypeHandle::Direct, PassingStyle::MutReference) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::Direct,
                    passing_style: crate::builtins_util::PassingStyle::MutReference
                }}
            }
            (TypeHandle::Optional, PassingStyle::MutReference) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::Optional,
                    passing_style: crate::builtins_util::PassingStyle::MutReference
                }}
            }
            (TypeHandle::VarArgs, PassingStyle::MutReference) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::VarArgs,
                    passing_style: crate::builtins_util::PassingStyle::MutReference
                }}
            }
            (TypeHandle::Direct, PassingStyle::Reference) => {
                quote! {crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::Direct,
                    passing_style: crate::builtins_util::PassingStyle::Reference
                }}
            }
            (TypeHandle::Optional, PassingStyle::Reference) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::Optional,
                    passing_style: crate::builtins_util::PassingStyle::Reference
                }}
            }
            (TypeHandle::VarArgs, PassingStyle::Reference) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::VarArgs,
                    passing_style: crate::builtins_util::PassingStyle::Reference
                }}
            }
            (TypeHandle::Direct, PassingStyle::Value) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::Direct,
                    passing_style: crate::builtins_util::PassingStyle::Value
                }}
            }
            (TypeHandle::Optional, PassingStyle::Value) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::Optional,
                    passing_style: crate::builtins_util::PassingStyle::Value
                }}
            }
            (TypeHandle::VarArgs, PassingStyle::Value) => {
                quote! { crate::builtins_util::Param {
                    handle: crate::builtins_util::TypeHandle::VarArgs,
                    passing_style: crate::builtins_util::PassingStyle::Value
                }}
            }
        });
    }
    //TODO rename this variable to param_types or params.
    quote! {
        let arg_types = vec![ #(#tokens),* ];
    }
}

/// write the intern_ function code. This code is generated to be called within sl-sh to avoid writing
/// boilerplate code to submit a function symbol and the associated code to the runtime. Every builtin
/// function must be inserted into a hashmap where the key is the name of the function and the value
/// is a function expression that stores the name of the rust function to call and its documentation.
/// It looks like the following in all cases:
// ```
// fn intern_one_int_to_float<S: std::hash::BuildHasher>(
//    interner: &mut sl_sh::Interner,
//    data: &mut std::collections::HashMap<&'static str, (sl_sh::types::Expression, String), S>,
//) {
//    let fn_name = "oneintofloat";
//    data.insert(
//        interner.intern(fn_name),
//        sl_sh::types::Expression::make_function(parse_one_int_to_float, " my docs\n"),
//    );
//}
// ```
fn generate_intern_fn(
    original_fn_name_str: &str,
    fn_name_attr: &Ident,
    fn_name: &str,
    doc_comments: String,
) -> TokenStream {
    let parse_name = get_parse_fn_name(original_fn_name_str);
    let intern_name = get_intern_fn_name(original_fn_name_str);
    quote! {
        fn #intern_name<S: std::hash::BuildHasher>(
            interner: &mut crate::Interner,
            data: &mut std::collections::HashMap<&'static str, (crate::types::Expression, String), S>,
        ) {
            let #fn_name_attr = #fn_name;
            data.insert(
                interner.intern(#fn_name_attr),
                crate::types::Expression::make_function(#parse_name, #doc_comments),
            );
        }
    }
}

/// write the parse_ version of the provided function. The function it generates takes an environment
/// and a list of Expressions, evaluates those expressions and then maps the provided list of expressions
/// to a list of ArgType values. To accomplish this information from compile time, arg_types,
/// is manually inserted into this function. This way the evaluated list of args and the expected
/// list of args can be compared and the appropriate vector of arguments can be created and
/// passed to the builtin function. To map a vector of ArgType structs to an actual function
/// call the ExpandVecToArgs trait is used. A sample parse_ function for a function that takes
/// one argument is shown below.
// ```
// fn parse_one_int_to_float(
//     environment: &mut sl_sh::environment::Environment,
//     args: &mut dyn Iterator<Item = sl_sh::types::Expression>,
// ) -> sl_sh::LispResult<sl_sh::types::Expression> {
//     use sl_sh::builtins_util::ExpandVecToArgs;
//     use std::convert::TryInto;
//     let fn_name = "one-in-to-float";
//     const ARGS_LEN: usize = 1usize;
//     // this arg_types variable is generated by the macro for use at runtime.
//     let arg_types = vec![sl_sh::builtins_util::Arg {
//         val: sl_sh::builtins_util::TypeHandle::Direct,
//         passing_style: sl_sh::builtins_util::PassingStyle::Value,
//     }];
//
//     let args = crate::builtins_util::make_args_eval_no_values(environment, args)?;
//     let args = sl_sh::get_arg_types(fn_name, arg_types, args)?;
//     if args.len() == ARGS_LEN {
//         match args.try_into() {
//             Ok(params) => {
//                 // use const generics and blanket implementation of ExpandVecToArgs over
//                 // function calls to map vector to function call.
//                 let params: [sl_sh::ArgType; ARGS_LEN] = params;
//                 builtin_one_int_to_float.call_expand_args(params)
//             }
//             Err(e) => Err(sl_sh::types::LispError::new(format!(
//                 "{} is broken and can't parse its arguments.",
//                 fn_name
//             ))),
//         }
//     } else if args.len() > ARGS_LEN {
//         Err(sl_sh::types::LispError::new(format!(
//             "{}  given too many arguments, expected {}, got, {}.",
//             fn_name,
//             ARGS_LEN,
//             args.len()
//         )))
//     } else {
//         Err(sl_sh::types::LispError::new(format!(
//             "{}  not given enough arguments, expected {}, got, {}.",
//             fn_name,
//             ARGS_LEN,
//             args.len()
//         )))
//     }
// }
// ```
fn generate_parse_fn(
    original_fn_name_str: &str,
    eval_values: bool,
    fn_name_attr: &Ident,
    fn_name: &str,
    args_len: usize,
    args: &[Param],
) -> TokenStream {
    let parse_name = get_parse_fn_name(original_fn_name_str);
    let builtin_name = get_builtin_fn_name(original_fn_name_str);
    let arg_types = embed_params_vec(args);

    let make_args = if eval_values {
        quote! {
            let args = crate::builtins_util::make_args(environment, args)?;
        }
    } else {
        quote! {
            let args = crate::builtins_util::make_args_eval_no_values(environment, args)?;
        }
    };

    quote! {
        fn #parse_name(
            environment: &mut crate::environment::Environment,
            args: &mut dyn Iterator<Item = crate::types::Expression>,
        ) -> crate::LispResult<crate::types::Expression> {
            use std::convert::TryInto;
            use crate::builtins_util::ExpandVecToArgs;
            #make_args
            let #fn_name_attr = #fn_name;
            const ARGS_LEN: usize = #args_len;
            #arg_types
            let args = crate::get_arg_types(fn_name, arg_types, args)?;
            if args.len() == ARGS_LEN {
                match args.try_into() {
                    Ok(params) => {
                        let params: [crate::ArgType; ARGS_LEN] = params;
                        #builtin_name.call_expand_args(environment, params)
                    },
                    Err(e) => {
                        Err(crate::types::LispError::new(format!("{} is broken and can't parse its arguments.", #fn_name)))
                    }
                }
            } else if args.len() > ARGS_LEN {
                Err(crate::types::LispError::new(format!("{} given too many arguments, expected {}, got {}.", #fn_name, ARGS_LEN, args.len())))
            } else {
                Err(crate::types::LispError::new(format!("{} not given enough arguments, expected {}, got {}.", #fn_name, ARGS_LEN, args.len())))
            }
        }
    }
}

fn generate_parse_fn2(
    original_fn_name_str: &str,
    eval_values: bool,
    fn_name_attr: &Ident,
    fn_name: &str,
    args_len: usize,
    params: &[Param],
    inner: TokenStream,
) -> TokenStream {
    let parse_name = get_parse_fn_name(original_fn_name_str);
    let arg_vec_literal = embed_params_vec(params);

    // in slosh this will change because the args are already evaluated and the macro will
    // be dealing with a slice so... keep this allocation at runtime for now because it
    // simplified the implementation and is more realistic long-term even though it's
    // suboptimal in this case.
    let make_args = if eval_values {
        quote! {
            let args = crate::builtins_util::make_args(environment, args)?;
        }
    } else {
        quote! {
            let args = crate::builtins_util::make_args_eval_no_values(environment, args)?;
        }
    };

    quote! {
        fn #parse_name(
            environment: &mut crate::environment::Environment,
            args: &mut dyn Iterator<Item = crate::types::Expression>,
        ) -> crate::LispResult<crate::types::Expression> {
            use std::convert::TryInto;
            use crate::builtins_util::ExpandVecToArgs;
            #make_args
            let #fn_name_attr = #fn_name;
            const ARGS_LEN: usize = #args_len;
            #arg_vec_literal

            // TODO remove in slosh implementation as args will be a slice
            let args = args.into_iter().collect::<Vec<Expression>>();
            let args = args.as_slice();
            // TODO can this call go away by validating args while walking the args slice in the
            // retro-fitted parsing?
            crate::validate_args(fn_name, arg_types, args)?;

            #inner
        }
    }
}
/// write the builtin_ version of the provided function. This function is the function taht makes
/// a direct call to the original rust native function to which the macro was applied. To accomplish
/// this the builtin_ function generates takes some number of ArgType structs (the wrapper enum that
/// enables passing optional and varargs). the body of the function handles unwrapping the ArgType
/// variables and then unwrapping the Expressions those contain into the proper rust native
/// function. The process is done in a for loop but it recursively builds the body of builtin_
/// by passing around a token stream.
///
/// The token stream is initialized with code to call to the original rust native function with
/// pre-generated names for each of the arguments, e.g. `my_rust_native_function(arg_0, arg_1);`.
/// Each subsequent iteration of the loop takes the previous token stream returned by the loop and
/// uses that as it's innermost scope. Thus the original function call is at the core of a series
/// of scopes that create all the necessary arguments with the proper types that were specified on
/// initialization. For a function of one argument that means the code would look something like:
// ```
// use sl_sh_proc_macros::sl_sh_fn;
// fn builtin_one_int_to_float(arg_0: crate::ArgType) -> crate::LispResult<crate::types::Expression> {
//    const _: fn() = || {
//        fn assert_impl_all<T: ?Sized + std::convert::Into<crate::Expression>>() {}
//        assert_impl_all::<f64>();
//    };
//    let fn_name = "one-int-to-float";
//    match arg_0 {
//        crate::ArgType::Exp(arg_0) => {
//            use crate::types::RustProcedure;
//            let mut typed_data: crate::types::TypedWrapper<i64, crate::types::Expression> =
//                crate::types::TypedWrapper::new(arg_0);
//            let callback = |arg_0: i64| -> crate::LispResult<crate::types::Expression> {
//                one_int_to_float(arg_0).map(Into::into)
//            };
//            typed_data.apply(fn_name, callback)
//        }
//        _ => {
//            return Err(LispError::new(
//                "sl_sh_fn macro is broken. ArgType::Exp can't be parsed as ArgType::Exp",
//            ));
//        }
//    }
//}
// #[sl_sh_fn(fn_name = "one-int-to-float")]
// fn one_int_to_float(int: i64) -> LispResult<f64> {
//    Ok(int as f64)
// }
// ```
fn generate_builtin_fn(
    original_item_fn: &ItemFn,
    original_fn_name_str: &str,
    fn_name: &str,
    fn_name_attr: &Ident,
    takes_env: bool,
) -> MacroResult<TokenStream> {
    let original_fn_name = Ident::new(original_fn_name_str, Span::call_site());
    let builtin_name = get_builtin_fn_name(original_fn_name_str);
    let (arg_names, arg_types) =
        generate_inner_fn_signature_to_orig_fn_call(original_item_fn, takes_env)?;

    let orig_fn_call = make_orig_fn_call(
        takes_env,
        original_item_fn,
        &original_fn_name,
        arg_names.clone(),
    )?;
    // initialize the innermost token stream to the code of the original_fn_call
    let mut prev_token_stream = orig_fn_call;
    let skip = usize::from(takes_env);
    let fn_args = original_item_fn
        .sig
        .inputs
        .iter()
        .skip(skip)
        .zip(arg_names.iter());
    for (fn_arg, arg_name) in fn_args {
        if let FnArg::Typed(ty) = fn_arg {
            prev_token_stream = parse_fn_arg_type(
                &ty.ty,
                fn_name,
                fn_name_attr,
                prev_token_stream,
                arg_name,
                false,
            )?;
        }
    }
    let (return_type, _) = get_return_type(original_item_fn)?;
    let mut conversions_assertions_code = vec![];
    if let Some(return_type) = return_type {
        conversions_assertions_code.push(generate_assertions_code_for_return_type_conversions(
            &return_type,
        ));
    }
    let tokens = quote! {
        fn #builtin_name(env: &mut crate::environment::Environment, #(#arg_names: #arg_types),*) -> crate::LispResult<crate::types::Expression> {
            #(#conversions_assertions_code)*
            let #fn_name_attr = #fn_name;
            #prev_token_stream
        }
    };
    Ok(tokens)
}

fn stuff(arg: Arg) {
    match (arg.val, arg.passing_style) {
        (ArgVal::Value, ArgPassingStyle::Move) => {
            let mut i = 0;
            if let Some(arg_0) = args.next() {
                let arg_0 = crate::eval(environment, arg_0)?;
                if let Some(param_0) = params.get(i) {
                    match (param_0.val, param_0.passing_style) {
                        (ArgVal::Value, ArgPassingStyle::Move) => {
                            use crate::types::RustProcedure;
                            let mut typed_data: crate::types::TypedWrapper<f64, crate::types::Expression> =
                                crate::types::TypedWrapper::new(arg_0);
                            let callback = |arg_0: f64| -> crate::LispResult<crate::types::Expression> {
                                Ok()//TODO
                            };
                            typed_data.apply(fn_name, callback)
                        }
                        (_, _) => {
                            Err(LispError::new(format!(
                                "{} macro is unable to parse its arguments, expected specific args at idx {} but arg_types vec had types that violated the generated codes expectations.",
                                fn_name,
                                i,
                            )))
                        }
                    }
                } else {
                    Err(LispError::new(format!(
                        "{} macro is unable to parse its arguments, expected {} args but arg_types vec did not have the item.",
                        fn_name,
                        i + 1,
                    )))
                }
            } else {
                Err(LispError::new(format!(
                    "{}  not given enough arguments, expected {}, got, {}.",
                    fn_name, ARGS_LEN, i,
                )))
            }
        }
        (ArgVal::Optional, ArgPassingStyle::Move) => {}
        (ArgVal::VarArgs, ArgPassingStyle::Move) => {}
        (ArgVal::Value, ArgPassingStyle::Reference) => {}
        (ArgVal::Optional, ArgPassingStyle::Reference) => {}
        (ArgVal::VarArgs, ArgPassingStyle::Reference) => {}
        (ArgVal::Value, ArgPassingStyle::MutReference) => {}
        (ArgVal::Optional, ArgPassingStyle::MutReference) => {}
        (ArgVal::VarArgs, ArgPassingStyle::MutReference) => {}
    }
}

fn generate_builtin_fn2(
    original_item_fn: &ItemFn,
    original_fn_name_str: &str,
    fn_name: &str,
    params: &[Param],
    fn_name_attr: &Ident,
    takes_env: bool,
) -> MacroResult<TokenStream> {
    let original_fn_name = Ident::new(original_fn_name_str, Span::call_site());
    let arg_names = generate_inner_fn_signature_to_orig_fn_call2(original_item_fn, takes_env)?;

    let orig_fn_call = make_orig_fn_call(
        takes_env,
        original_item_fn,
        &original_fn_name,
        arg_names.clone(),
    )?;
    // initialize the innermost token stream to the code of the original_fn_call
    let mut prev_token_stream = orig_fn_call;
    let skip = usize::from(takes_env);
    let inputs_less_env_len = original_item_fn.sig.inputs.len() - skip;
    if inputs_less_env_len != params.len() {
        let err_str = format!(
            "sl_sh_fn macro is broken, signature of target function has an arity of {}, but this macro computed its arity as: {} (arity is - 1 if takes_env is true).",
            inputs_less_env_len,
            params.len(),
        );
        return Err(Error::new(original_item_fn.span(), err_str));
    }
    let fn_args = original_item_fn
        .sig
        .inputs
        .iter()
        .skip(skip)
        .zip(arg_names.iter())
        .zip(params.iter());
    for (idx, ((fn_arg, arg_name), param)) in fn_args.enumerate() {
        if let FnArg::Typed(ty) = fn_arg {
            // this needs to use the args.iter() pattern now.
            prev_token_stream = parse_fn_arg_type2(
                &ty.ty,
                fn_name,
                fn_name_attr,
                prev_token_stream,
                arg_name,
                false,
                idx,
                *param,
            )?;
        }
    }
    let (return_type, _) = get_return_type(original_item_fn)?;
    let mut conversions_assertions_code = vec![];
    if let Some(return_type) = return_type {
        conversions_assertions_code.push(generate_assertions_code_for_return_type_conversions(
            &return_type,
        ));
    }
    let tokens = quote! {
        #(#conversions_assertions_code)*
        // let #fn_name_attr = #fn_name; already included in parse function
        // as well as `args`, a vec of expression,
        // `fn_name_attr` the ident of the fn_name
        // `ARGS_LEN` constant representing arity of original fn
        // and `arg_types` the embedded vec of Arg's available at runtime.
        #prev_token_stream
    };
    Ok(tokens)
}

// TODO document this new version
#[allow(clippy::too_many_arguments)]
fn parse_fn_arg_type2(
    ty: &Type, //TODO Cow?
    fn_name: &str,
    fn_name_attr: &Ident,
    prev_token_stream: TokenStream,
    arg_name: &Ident,
    noop_outer_parse: bool,
    idx: usize,
    param: Param,
) -> MacroResult<TokenStream> {
    match <Type as Into<RustType>>::into(ty.clone()) {
        RustType::Path(ty, _span) => {
            let parse_layer_1 = get_parser_for_type_handle2(param, noop_outer_parse);
            let passing_style = PassingStyle::Value;
            parse_type2(
                &ty,
                (fn_name, fn_name_attr),
                prev_token_stream,
                param,
                arg_name,
                passing_style,
                parse_layer_1,
            )
        }
        RustType::Tuple(type_tuple, _span) => {
            let parse_layer_1 = get_parser_for_type_handle2(param, noop_outer_parse);
            parse_type_tuple2(
                &type_tuple,
                fn_name,
                fn_name_attr,
                prev_token_stream,
                arg_name,
                param,
                parse_layer_1,
            )
        }
        RustType::Reference(ty_ref, _span) => match <Type as Into<RustType>>::into(*ty_ref.elem) {
            RustType::Path(ty, _span) => {
                let parse_layer_1 = get_parser_for_type_handle2(param, noop_outer_parse);
                let passing_style = if ty_ref.mutability.is_some() {
                    PassingStyle::MutReference
                } else {
                    PassingStyle::Reference
                };
                parse_type2(
                    &ty,
                    (fn_name, fn_name_attr),
                    prev_token_stream,
                    param,
                    arg_name,
                    passing_style,
                    parse_layer_1,
                )
            }
            RustType::Tuple(type_tuple, _span) => {
                let parse_layer_1 = get_parser_for_type_handle2(param, noop_outer_parse);
                parse_type_tuple2(
                    &type_tuple,
                    fn_name,
                    fn_name_attr,
                    prev_token_stream,
                    arg_name,
                    param,
                    parse_layer_1,
                )
            }
            RustType::BareFn(_, _) | RustType::Unsupported(_) | RustType::Reference(_, _) => {
                let arg_pos = get_arg_pos(arg_name)?;
                let err_str = format!(
                    "Error with argument at position {}, sl_sh_fn only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                    arg_pos
                );
                Err(Error::new(ty.span(), err_str))
            }
        },
        RustType::BareFn(_, _) | RustType::Unsupported(_) => {
            let arg_pos = get_arg_pos(arg_name)?;
            let err_str = format!(
                "Error with argument at position {}, sl_sh_fn only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                arg_pos
            );
            Err(Error::new(ty.span(), err_str))
        }
    }
}

fn parse_fn_arg_type(
    ty: &Type, //TODO Cow?
    fn_name: &str,
    fn_name_attr: &Ident,
    prev_token_stream: TokenStream,
    arg_name: &Ident,
    noop_outer_parse: bool,
) -> MacroResult<TokenStream> {
    match <Type as Into<RustType>>::into(ty.clone()) {
        RustType::Path(ty, _span) => {
            let val = get_type_handle(&ty);
            let parse_layer_1 = get_parser_for_type_handle(val, noop_outer_parse);
            let passing_style = PassingStyle::Value;
            parse_type(
                &ty,
                (fn_name, fn_name_attr),
                prev_token_stream,
                val,
                arg_name,
                passing_style,
                parse_layer_1,
            )
        }
        RustType::Tuple(type_tuple, _span) => {
            let val = TypeHandle::Direct;
            let parse_layer_1 = get_parser_for_type_handle(val, noop_outer_parse);
            parse_type_tuple(
                &type_tuple,
                fn_name,
                fn_name_attr,
                prev_token_stream,
                arg_name,
                parse_layer_1,
            )
        }
        RustType::Reference(ty_ref, _span) => match <Type as Into<RustType>>::into(*ty_ref.elem) {
            RustType::Path(ty, _span) => {
                let val = get_type_handle(&ty);
                let parse_layer_1 = get_parser_for_type_handle(val, noop_outer_parse);
                let passing_style = if ty_ref.mutability.is_some() {
                    PassingStyle::MutReference
                } else {
                    PassingStyle::Reference
                };
                parse_type(
                    &ty,
                    (fn_name, fn_name_attr),
                    prev_token_stream,
                    val,
                    arg_name,
                    passing_style,
                    parse_layer_1,
                )
            }
            RustType::Tuple(type_tuple, _span) => {
                let val = TypeHandle::Direct;
                let parse_layer_1 = get_parser_for_type_handle(val, noop_outer_parse);
                parse_type_tuple(
                    &type_tuple,
                    fn_name,
                    fn_name_attr,
                    prev_token_stream,
                    arg_name,
                    parse_layer_1,
                )
            }
            RustType::BareFn(_, _) | RustType::Unsupported(_) | RustType::Reference(_, _) => {
                let arg_pos = get_arg_pos(arg_name)?;
                let err_str = format!(
                    "Error with argument at position {}, sl_sh_fn only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                    arg_pos
                );
                Err(Error::new(ty.span(), err_str))
            }
        },
        RustType::BareFn(_, _) | RustType::Unsupported(_) => {
            let arg_pos = get_arg_pos(arg_name)?;
            let err_str = format!(
                "Error with argument at position {}, sl_sh_fn only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                arg_pos
            );
            Err(Error::new(ty.span(), err_str))
        }
    }
}

fn parse_type_tuple(
    type_tuple: &TypeTuple,
    fn_name: &str,
    fn_name_attr: &Ident,
    inner: TokenStream,
    arg_name: &Ident,
    outer_parse: fn(&Ident, TokenStream) -> TokenStream,
) -> MacroResult<TokenStream> {
    // at the end of all the tuple parsing the inner token stream expects
    // arg_name to be:
    // let arg_name_N: (T, U) = (arg_name_N_0, arg_name_N_1);
    // this means that first we must take the arg_names of what will be the
    // tuple pair and put them back into the ident that this recursive process
    // expects.
    let arg_name_base = arg_name.to_string() + "_";
    let arg_names = (0..type_tuple.elems.len())
        .into_iter()
        .map(|x| {
            Ident::new(
                &(arg_name_base.to_string() + &x.to_string()),
                Span::call_site(),
            )
        })
        .collect::<Vec<Ident>>();
    let mut inner = quote! {
        let #arg_name = (#(#arg_names),*);
        #inner
    };
    let mut expressions = vec![];
    let tuple_len = type_tuple.elems.len();
    let tokens = if !type_tuple.elems.is_empty() {
        for (i, ty) in type_tuple.elems.iter().enumerate() {
            expressions.push(quote! { crate::types::Expression });
            let arg_name_pair = Ident::new(
                &(arg_name_base.to_string() + &i.to_string()),
                Span::call_site(),
            );
            inner = parse_fn_arg_type(ty, fn_name, fn_name_attr, inner, &arg_name_pair, true)?;
        }
        inner
    } else {
        inner
    };
    let arg_pos = get_arg_pos(arg_name)?;
    let tokens = quote! {{
        use std::convert::TryInto;
        if !crate::is_sequence!(#arg_name)
        {
            let err_str = format!("{}: Expected a vector or list for argument at position {}.", #fn_name, #arg_pos);
            return Err(LispError::new(err_str));
        }
        let #arg_name = #arg_name.iter().collect::<Vec<crate::types::Expression>>();
        match #arg_name.try_into() {
            Ok(#arg_name) => {
                let #arg_name: [crate::Expression; #tuple_len] = #arg_name;
                let [#(#arg_names),*] = #arg_name;
                #tokens
            }
            Err(_) => {
                let err_str = format!("{}: Expected a sl_sh vector or list with {} elements corresponding to the tuple at argument position {}.", #fn_name, #tuple_len, #arg_pos);
                return Err(LispError::new(err_str));
            }
        }
    }};
    Ok(outer_parse(arg_name, tokens))
}

fn parse_type_tuple2(
    type_tuple: &TypeTuple,
    fn_name: &str,
    fn_name_attr: &Ident,
    inner: TokenStream,
    arg_name: &Ident,
    param: Param,
    outer_parse: fn(&Ident, TokenStream, Param) -> TokenStream,
) -> MacroResult<TokenStream> {
    // at the end of all the tuple parsing the inner token stream expects
    // arg_name to be:
    // let arg_name_N: (T, U) = (arg_name_N_0, arg_name_N_1);
    // this means that first we must take the arg_names of what will be the
    // tuple pair and put them back into the ident that this recursive process
    // expects.
    let arg_name_base = arg_name.to_string() + "_";
    let arg_names = (0..type_tuple.elems.len())
        .into_iter()
        .map(|x| {
            Ident::new(
                &(arg_name_base.to_string() + &x.to_string()),
                Span::call_site(),
            )
        })
        .collect::<Vec<Ident>>();
    let mut inner = quote! {
        let #arg_name = (#(#arg_names),*);
        #inner
    };
    let mut expressions = vec![];
    let tuple_len = type_tuple.elems.len();
    let tokens = if !type_tuple.elems.is_empty() {
        for (i, ty) in type_tuple.elems.iter().enumerate() {
            expressions.push(quote! { crate::types::Expression });
            let arg_name_pair = Ident::new(
                &(arg_name_base.to_string() + &i.to_string()),
                Span::call_site(),
            );
            let param = get_param_from_type(ty.clone(), ty.span(), i)?;
            inner = parse_fn_arg_type2(
                ty,
                fn_name,
                fn_name_attr,
                inner,
                &arg_name_pair,
                true,
                i,
                param,
            )?;
        }
        inner
    } else {
        inner
    };
    let arg_pos = get_arg_pos(arg_name)?;
    let tokens = quote! {{
        use std::convert::TryInto;
        if !crate::is_sequence!(#arg_name)
        {
            let err_str = format!("{}: Expected a vector or list for argument at position {}.", #fn_name, #arg_pos);
            return Err(LispError::new(err_str));
        }
        let #arg_name = #arg_name.iter().collect::<Vec<crate::types::Expression>>();
        match #arg_name.try_into() {
            Ok(#arg_name) => {
                let #arg_name: [crate::Expression; #tuple_len] = #arg_name;
                let [#(#arg_names),*] = #arg_name;
                #tokens
            }
            Err(_) => {
                let err_str = format!("{}: Expected a sl_sh vector or list with {} elements corresponding to the tuple at argument position {}.", #fn_name, #tuple_len, #arg_pos);
                return Err(LispError::new(err_str));
            }
        }
    }};
    Ok(outer_parse(arg_name, tokens, param))
}

/// Optional and VarArgs types are supported to create the idea of items that might be provided or
/// for providing a list of zero or more items that can be passed in.
/// The nature of optional and varargs are context dependent because variable numbers of
/// arguments have to be at the end of the function signature. This method verifies that items
/// marked as Optional are last, and VarArgs is supported but only in the last position, which can
/// be after any number of Optional arguments. This means non Optional/VarArgs types must
/// come before all Optional and VarArgs types.
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
                        &format!(
                            "Error with argument at position {}, sl_sh_fn only supports passing Type::Path and Type::Tuple by value or ref/ref mut, no either syn::Type's are supported: {:?}.",
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
                &format!(
                    "Error with argument at position {}, sl_sh_fn only supports passing Type::Path and Type::Tuple by value or ref/ref mut, no either syn::Type's are supported: {:?}.",
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

/// return the function names the macro will create. Given a base name, <base>
/// return builtin_<base> Ident to be used as function name
fn get_builtin_fn_name(original_fn_name: &str) -> Ident {
    let builtin_name = "builtin_".to_string() + original_fn_name;
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

fn parse_attributes(
    original_item_fn: &ItemFn,
    attr_args: AttributeArgs,
) -> MacroResult<(String, Ident, bool, bool)> {
    let vals = attr_args
        .iter()
        .map(get_attribute_name_value)
        .collect::<MacroResult<Vec<(String, String)>>>()?;
    let fn_name_attr = "fn_name".to_string();
    let fn_name = get_attribute_value_with_key(original_item_fn, &fn_name_attr, vals.as_slice())?
        .ok_or_else(|| {
        Error::new(
            original_item_fn.span(),
            "sl_sh_fn requires name-value pair, 'fn_name'",
        )
    })?;
    let fn_name_attr = Ident::new(&fn_name_attr, Span::call_site());

    let eval_values = if let Some(value) =
        get_attribute_value_with_key(original_item_fn, "eval_values", vals.as_slice())?
    {
        value == "true"
    } else {
        false
    };
    let takes_env = if let Some(value) =
        get_attribute_value_with_key(original_item_fn, "takes_env", vals.as_slice())?
    {
        value == "true"
    } else {
        false
    };
    Ok((fn_name, fn_name_attr, eval_values, takes_env))
}

/// this function outputs all of the generated code, it is composed into three different functions:
/// intern_<original_fn_name>
/// parse_<original_fn_name>
/// builtin_<original_fn_name>
/// - intern_ is the simplest function, it is generated to be called within sl-sh to avoid writing
/// boilerplate code to submit a function symbol and the associated code to the runtime.
/// - parse_ has the same function signature as all rust native functions, it takes the environment
/// and a list of evalable args. It evals those arguments at runtime so the resultant expressions
/// can be consumed by the builtin code.
/// - builtin_ is the core of the macro, it takes some number of wrapped expression types prepared by
/// parse and translates those to the appropriate rust types and calls the rust native function.
fn generate_sl_sh_fn(
    original_item_fn: &ItemFn,
    attr_args: AttributeArgs,
) -> MacroResult<TokenStream> {
    let (fn_name, fn_name_attr, eval_values, takes_env) =
        parse_attributes(original_item_fn, attr_args)?;
    let original_fn_name_str = original_item_fn.sig.ident.to_string();
    let original_fn_name_str = original_fn_name_str.as_str();

    let args = parse_src_function_arguments(original_item_fn, takes_env)?;
    are_args_valid(original_item_fn, args.as_slice(), takes_env)?;
    let builtin_fn = generate_builtin_fn(
        original_item_fn,
        original_fn_name_str,
        fn_name.as_str(),
        &fn_name_attr,
        takes_env,
    )?;

    let args_len = if takes_env {
        original_item_fn.sig.inputs.len() - 1
    } else {
        original_item_fn.sig.inputs.len()
    };
    let parse_fn = generate_parse_fn(
        original_fn_name_str,
        eval_values,
        &fn_name_attr,
        fn_name.as_str(),
        args_len,
        args.as_slice(),
    );
    let doc_comments = get_documentation_for_fn(original_item_fn)?;
    let intern_fn = generate_intern_fn(
        original_fn_name_str,
        &fn_name_attr,
        fn_name.as_str(),
        doc_comments,
    );
    let tokens = quote! {
        #builtin_fn

        #parse_fn

        #intern_fn
    };
    Ok(tokens)
}

/// let's get iterator-y
fn generate_sl_sh_fn2(
    original_item_fn: &ItemFn,
    attr_args: AttributeArgs,
) -> MacroResult<TokenStream> {
    let (fn_name, fn_name_attr, eval_values, takes_env) =
        parse_attributes(original_item_fn, attr_args)?;
    let original_fn_name_str = original_item_fn.sig.ident.to_string();
    let original_fn_name_str = original_fn_name_str.as_str();

    let params = parse_src_function_arguments(original_item_fn, takes_env)?;
    are_args_valid(original_item_fn, params.as_slice(), takes_env)?;
    let builtin_fn = generate_builtin_fn2(
        original_item_fn,
        original_fn_name_str,
        fn_name.as_str(),
        params.as_slice(),
        &fn_name_attr,
        takes_env,
    )?;

    let args_len = if takes_env {
        original_item_fn.sig.inputs.len() - 1
    } else {
        original_item_fn.sig.inputs.len()
    };
    let parse_fn = generate_parse_fn2(
        original_fn_name_str,
        eval_values,
        &fn_name_attr,
        fn_name.as_str(),
        args_len,
        params.as_slice(),
        builtin_fn,
    );
    let doc_comments = get_documentation_for_fn(original_item_fn)?;
    let intern_fn = generate_intern_fn(
        original_fn_name_str,
        &fn_name_attr,
        fn_name.as_str(),
        doc_comments,
    );
    let tokens = quote! {
        #parse_fn

        #intern_fn
    };
    Ok(tokens)
}

/// macro that creates a bridge between rust native code and sl-sh code, specify the lisp
/// function name to be interned with the "fn_name" attribute. This macro outputs all of the
/// generated bridge code as well as the original function's code so it can be used
/// by the generated bridge code.
#[proc_macro_attribute]
pub fn sl_sh_fn(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr_args = parse_macro_input!(attr as AttributeArgs);

    let tokens = match parse::<Item>(input) {
        Ok(item) => match &item {
            Item::Fn(original_item_fn) => {
                let generated_code = match generate_sl_sh_fn(original_item_fn, attr_args) {
                    Ok(generated_code) => generated_code,
                    Err(e) => e.to_compile_error(),
                };
                let original_fn_code = item.into_token_stream();
                quote! {
                    #generated_code

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

/// macro that creates a bridge between rust native code and sl-sh code, specify the lisp
/// function name to be interned with the "fn_name" attribute. This macro outputs all of the
/// generated bridge code as well as the original function's code so it can be used
/// by the generated bridge code.
#[proc_macro_attribute]
pub fn sl_sh_fn2(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    let attr_args = parse_macro_input!(attr as AttributeArgs);

    let tokens = match parse::<Item>(input) {
        Ok(item) => match &item {
            Item::Fn(original_item_fn) => {
                let generated_code = match generate_sl_sh_fn2(original_item_fn, attr_args) {
                    Ok(generated_code) => generated_code,
                    Err(e) => e.to_compile_error(),
                };
                let original_fn_code = item.into_token_stream();
                quote! {
                    #generated_code

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

#[cfg(test)]
mod test {
    use super::*;

    fn are_args_valid(params: &[Param]) -> bool {
        if params.is_empty() || params.len() == 1 {
            true
        } else {
            let mut found_opt = false;
            let mut found_value = false;
            for (i, param) in params.iter().rev().enumerate() {
                match (i, param.handle, found_opt, found_value) {
                    (i, TypeHandle::VarArgs, _, _) if i > 0 => {
                        // vec can only be last argument
                        return false;
                    }
                    (_, TypeHandle::Optional, _, true) => {
                        // optionals all must be last
                        return false;
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
            true
        }
    }

    #[test]
    fn test_args() {
        let args = vec![];
        assert!(are_args_valid(args.as_slice()));
        // values are always valid
        let args = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::MutReference,
            },
        ];
        assert!(are_args_valid(args.as_slice()));

        // vec must be last argument
        let args = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::VarArgs,
                passing_style: PassingStyle::Value,
            },
        ];
        assert!(are_args_valid(args.as_slice()));

        // vec must be last argument
        let args = vec![
            Param {
                handle: TypeHandle::VarArgs,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
        ];
        assert!(!are_args_valid(args.as_slice()));

        // opt must be last argument
        let args = vec![
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
        ];
        assert!(!are_args_valid(args.as_slice()));

        // opt must be last argument(s)
        let args = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
        ];
        assert!(are_args_valid(args.as_slice()));

        // opt must be last argument(s), unless it's one vec in the last slot
        let args = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::VarArgs,
                passing_style: PassingStyle::Value,
            },
        ];
        assert!(are_args_valid(args.as_slice()));

        // vec must always be last
        let args = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::VarArgs,
                passing_style: PassingStyle::Reference,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
        ];
        assert!(!are_args_valid(args.as_slice()));

        // opt must always be last argument(s)
        let args = vec![
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Reference,
            },
        ];
        assert!(!are_args_valid(args.as_slice()));

        // opt must always be last argument(s)
        let args = vec![
            Param {
                handle: TypeHandle::Optional,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Value,
            },
            Param {
                handle: TypeHandle::Direct,
                passing_style: PassingStyle::Reference,
            },
        ];
        assert!(!are_args_valid(args.as_slice()));
    }
}

//TODO
//  - functions that return Values.
//  - tuple return types?
//  - avoid allocations by using iter instead of vec.
//  - fcns that accept iter.
//  - then... compare against inline the function being called... randomize variable names.
