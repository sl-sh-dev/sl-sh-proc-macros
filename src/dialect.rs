use crate::{
    generate_assertions_code_for_return_type_conversions,
    generate_inner_fn_signature_to_orig_fn_call, get_arg_pos, get_generic_argument_from_type,
    get_param_from_type, get_parser_for_type_handle, get_type_or_wrapped_type,
    is_valid_generic_type, is_vec, no_parse_param, num_required_args,
    tokens_for_matching_references, MacroResult, Param, ParamParsingFn, PassingStyle, RustType,
    SupportedGenericReturnTypes, TypeHandle, POSSIBLE_ARG_TYPES, POSSIBLE_RETURN_TYPES,
    SPECIAL_ARG_TYPES,
};
use quote::quote;
use quote::ToTokens;
use quote::__private::TokenStream;
use syn::__private::Span;
use syn::spanned::Spanned;
use syn::{Error, FnArg, GenericArgument, Ident, ItemFn, ReturnType, Type, TypePath, TypeTuple};

pub mod sl_sh;
pub mod slosh;

//TODO make functions static that do not rely on self parameter!
pub(crate) trait Dialect {
    /// Return the backing dialect of the trait.
    fn dialect(&self) -> Box<dyn Dialect>;

    /// write the builtin_ version of the provided function. This function is the function that makes
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
    #[allow(clippy::too_many_arguments)]
    fn generate_builtin_fn(
        &self,
        original_item_fn: &ItemFn,
        original_fn_name_str: &str,
        fn_name: &str,
        params: &[Param],
        fn_name_ident: &Ident,
        takes_env: bool,
        inline: bool,
    ) -> MacroResult<TokenStream> {
        let original_fn_name = Ident::new(original_fn_name_str, Span::call_site());
        let arg_names = generate_inner_fn_signature_to_orig_fn_call(original_item_fn, takes_env)?;
        let required_args = num_required_args(params);

        let orig_fn_call = self.make_orig_fn_call(
            inline,
            takes_env,
            original_item_fn,
            &original_fn_name,
            required_args,
            arg_names.clone(),
        )?;
        // initialize the innermost token stream to the code of the original_fn_call
        let mut prev_token_stream = orig_fn_call;
        let skip = usize::from(takes_env);
        let inputs_less_env_len = original_item_fn.sig.inputs.len() - skip;
        if inputs_less_env_len != params.len() {
            let err_str = format!(
                "macro is broken, signature of target function has an arity of {}, but this macro computed its arity as: {} (arity is - 1 if takes_env is true).",
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
                prev_token_stream = self.parse_fn_arg_type(
                    &ty.ty,
                    fn_name,
                    fn_name_ident,
                    prev_token_stream,
                    arg_name,
                    false,
                    idx,
                    *param,
                    required_args,
                )?;
            }
        }
        let (return_type, _) = self.get_return_type(original_item_fn)?;
        let mut conversions_assertions_code = vec![];
        if let Some(return_type) = return_type {
            conversions_assertions_code.push(generate_assertions_code_for_return_type_conversions(
                &return_type,
            ));
        }
        let tokens = quote! {
            #(#conversions_assertions_code)*
            // let #fn_name_ident = #fn_name; already included in parse function
            // as well as `args`, a vec of expression,
            // `fn_name_ident` the ident of the fn_name
            // `ARGS_LEN` constant representing arity of original fn
            // and `arg_types` the embedded vec of Arg's available at runtime.
            #prev_token_stream
        };
        Ok(tokens)
    }

    /// recursively wrap the received sl_sh args at the given idx in callback functions that parse the Expressions
    /// into the a variable with a predefined  name with the same type as the corresponding parameter
    /// in the rust native function.
    #[allow(clippy::too_many_arguments)]
    fn parse_fn_arg_type(
        &self,
        ty: &Type,
        fn_name: &str,
        fn_name_ident: &Ident,
        prev_token_stream: TokenStream,
        arg_name: &Ident,
        noop_outer_parse: bool,
        idx: usize,
        param: Param,
        required_args: usize,
    ) -> MacroResult<TokenStream> {
        match <Type as Into<RustType>>::into(ty.clone()) {
            RustType::Path(ty, _span) => {
                let parse_layer_1 = get_parser_for_type_handle(noop_outer_parse);
                let passing_style = PassingStyle::Value;
                self.parse_type(
                    &ty,
                    (fn_name, fn_name_ident),
                    prev_token_stream,
                    param,
                    arg_name,
                    passing_style,
                    idx,
                    required_args,
                    parse_layer_1,
                )
            }
            RustType::Tuple(type_tuple, _span) => {
                let parse_layer_1 = get_parser_for_type_handle(noop_outer_parse);
                self.parse_type_tuple(
                    &type_tuple,
                    fn_name,
                    fn_name_ident,
                    prev_token_stream,
                    arg_name,
                    idx,
                    required_args,
                    param,
                    parse_layer_1,
                )
            }
            RustType::Reference(ty_ref, _span) => {
                match <Type as Into<RustType>>::into(*ty_ref.elem) {
                    RustType::Path(ty, _span) => {
                        let parse_layer_1 = get_parser_for_type_handle(noop_outer_parse);
                        let passing_style = if ty_ref.mutability.is_some() {
                            PassingStyle::MutReference
                        } else {
                            PassingStyle::Reference
                        };
                        self.parse_type(
                            &ty,
                            (fn_name, fn_name_ident),
                            prev_token_stream,
                            param,
                            arg_name,
                            passing_style,
                            idx,
                            required_args,
                            parse_layer_1,
                        )
                    }
                    RustType::Tuple(type_tuple, _span) => {
                        let parse_layer_1 = get_parser_for_type_handle(noop_outer_parse);
                        self.parse_type_tuple(
                            &type_tuple,
                            fn_name,
                            fn_name_ident,
                            prev_token_stream,
                            arg_name,
                            idx,
                            required_args,
                            param,
                            parse_layer_1,
                        )
                    }
                    RustType::BareFn(_, _)
                    | RustType::Unsupported(_)
                    | RustType::Reference(_, _) => {
                        let arg_pos = get_arg_pos(arg_name)?;
                        let err_str = format!(
                        "Error with argument at position {}, macro only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                        arg_pos
                    );
                        Err(Error::new(ty.span(), err_str))
                    }
                }
            }
            RustType::BareFn(_, _) | RustType::Unsupported(_) => {
                let arg_pos = get_arg_pos(arg_name)?;
                let err_str = format!(
                    "Error with argument at position {}, macro only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                    arg_pos
                );
                Err(Error::new(ty.span(), err_str))
            }
        }
    }

    /// for regular Expression values (no Optional/VarArgs) ref_exp
    /// just needs to be matched based on it's ExpEnum variant.
    #[allow(clippy::too_many_arguments)]
    fn parse_direct_type(
        &self,
        ty: &TypePath,
        fn_name: &str,
        fn_name_ident: &Ident,
        arg_name: &Ident,
        passing_style: PassingStyle,
        inner: TokenStream,
        idx: usize,
        required_args: usize,
        param: Param,
    ) -> MacroResult<TokenStream> {
        if is_vec(ty).is_some() {
            self.parse_variadic_args_type(true, ty, fn_name, arg_name, inner, quote! { Vec })
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
                        PassingStyle::Value | PassingStyle::Reference => Ok(quote! {{
                            use crate::macro_types::RustProcedure;
                            let typed_data: crate::types::TypedWrapper<#ty, crate::types::Expression> =
                                crate::types::TypedWrapper::new(&#arg_name);
                            #callback_declaration
                            typed_data.apply(#fn_name_ident, callback)
                        }}),
                        PassingStyle::MutReference => Ok(quote! {{
                            use crate::macro_types::RustProcedureRefMut;
                            let mut typed_data: crate::types::TypedWrapper<#ty, crate::types::Expression> =
                                crate::types::TypedWrapper::new(&#arg_name);
                            #callback_declaration
                            typed_data.apply_ref_mut(#fn_name_ident, callback)
                        }}),
                    }
                }
                RustType::Tuple(type_tuple, _span) => self.parse_type_tuple(
                    &type_tuple,
                    fn_name,
                    fn_name_ident,
                    inner,
                    arg_name,
                    idx,
                    required_args,
                    param,
                    no_parse_param,
                ),
                RustType::BareFn(_, _) | RustType::Reference(_, _) | RustType::Unsupported(_) => {
                    let arg_pos = get_arg_pos(arg_name)?;
                    let err_str = format!(
                        "Error with argument at position {}, macro only supports Vec<T>, Option<T>, and T where T is a Type::Path or Type::Tuple and can be moved, passed by reference, or passed by mutable reference (|&|&mut )(Type Path | (Type Path,*))",
                        arg_pos
                    );
                    Err(Error::new(ty.span(), err_str))
                }
            }
        }
    }

    /// for Option<Expression> values the ref_exp must first be parsed as an
    /// Option, and only in the case that the option is Some will it be
    /// necessary to match against every ExpEnum variant.
    #[allow(clippy::too_many_arguments)]
    fn parse_optional_type(
        &self,
        ty: &TypePath,
        fn_name: &str,
        fn_name_ident: &Ident,
        arg_name: &Ident,
        passing_style: PassingStyle,
        inner: TokenStream,
        idx: usize,
        required_args: usize,
        param: Param,
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
        let some_arg_value_type_parsing_code = self.parse_direct_type(
            ty,
            fn_name,
            fn_name_ident,
            arg_name,
            passing_style,
            some_inner,
            idx,
            required_args,
            param,
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

    /// if expecting a Vec then the actual expression itself should be iterable
    /// (Pair/Vector/Nil), set arg_name_itself_is_iter = true. Otherwise it's
    /// varargs which means the original args vector is passed in and
    /// iterated over. the implication of passing in Vec is that if the Exp
    /// doesn't match one of a few underlying sl-sh types passing it to
    /// this function is an error.
    fn parse_variadic_args_type(
        &self,
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
                        let #arg_name = if !crate::is_sequence!(#arg_name)
                        {
                            let err_str = format!("{}: Expected a vector or list for argument at position {}.", #fn_name, #arg_pos);
                            return Err(LispError::new(err_str));
                        } else {
                            #arg_name
                        };
                    }
                } else {
                    // HACK: this should not be needed but sometimes in current sl-sh 0.9.69 implementation
                    // VarArgs (which are being passed in when arg_name_itself_is_iter  is false) can be
                    // passed an array that contains nil, which is different than nil itself, either way
                    // this can be dealt with easily at the macro level. Removing this code causes
                    // the try_into_for in the final quote! block to fail because it can't convert
                    // nil into its desired type. This happens because it is iterating over a list
                    // that is nil. In reality, it shouldn't but the Expression object is a vector of
                    // nil, this is defensive code that should go away in slosh.
                    quote! {
                        let #arg_name = if #arg_name.len() == 1 && #arg_name.get(0).unwrap().is_nil() {
                            vec![]
                        } else {
                            #arg_name
                        };
                    }
                };
                Ok(quote! {{
                    #arg_check
                    use crate::macro_types::TryIntoExpression;

                    static_assertions::assert_impl_all!(crate::types::Expression: crate::macro_types::TryIntoExpression<#wrapped_ty>);
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
                        static_assertions::assert_impl_all!(crate::types::Expression: crate::macro_types::TryIntoExpression<#elem>);
                    });
                        args.push(quote! {
                            let #arg_name: #elem = #arg_name.clone().try_into_for(#fn_name)?;
                        })
                    }
                    Ok(quote! {{
                        use crate::macro_types::TryIntoExpression;
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
                        "Error with argument at position {}, macro only supports tuple pairs.",
                        arg_pos
                    );
                    Err(Error::new(type_tuple.span(), err_str))
                }
            }
            ty => {
                let err_str =
                    "Vec<T> and VarArgs<T> only support T of type Type::Path or Type::Tuple.";
                Err(Error::new(ty.span(), err_str))
            }
        }
    }

    /// create the nested match statements to parse rust types into sl_sh types.
    /// the rust types will determine what sl_sh functions will be used for
    /// transformation. If this function throws errors it means that the
    /// inputs, val/passing style are wrong and aren't matching to the ArgType(s)
    /// properly, or the rust type lookup function is busted.
    #[allow(clippy::too_many_arguments)]
    fn parse_type(
        &self,
        ty: &TypePath,
        fn_name: (&str, &Ident),
        inner: TokenStream,
        param: Param,
        arg_name: &Ident,
        passing_style: PassingStyle,
        idx: usize,
        required_args: usize,
        outer_parse: ParamParsingFn,
    ) -> MacroResult<TokenStream> {
        let tokens = match param.handle {
            TypeHandle::Direct => self.parse_direct_type(
                ty,
                fn_name.0,
                fn_name.1,
                arg_name,
                passing_style,
                inner,
                idx,
                required_args,
                param,
            )?,
            TypeHandle::Optional => self.parse_optional_type(
                ty,
                fn_name.0,
                fn_name.1,
                arg_name,
                passing_style,
                inner,
                idx,
                required_args,
                param,
            )?,
            TypeHandle::VarArgs => self.parse_variadic_args_type(
                false,
                ty,
                fn_name.0,
                arg_name,
                inner,
                quote! { crate::VarArgs },
            )?,
        };
        Ok(outer_parse(
            self.dialect(),
            arg_name,
            tokens,
            param,
            required_args,
            idx,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn parse_type_tuple(
        &self,
        type_tuple: &TypeTuple,
        fn_name: &str,
        fn_name_ident: &Ident,
        inner: TokenStream,
        arg_name: &Ident,
        idx: usize,
        required_args: usize,
        param: Param,
        outer_parse: ParamParsingFn,
    ) -> MacroResult<TokenStream> {
        // at the end of all the tuple parsing the inner token stream expects
        // arg_name to be:
        // let arg_name_N: (T, U) = (arg_name_N_0, arg_name_N_1);
        // this means that first we must take the arg_names of what will be the
        // tuple pair and put them back into the ident that this recursive process
        // expects.
        let arg_name_base = arg_name.to_string() + "_";
        let arg_names = (0..type_tuple.elems.len())
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
                inner = self.parse_fn_arg_type(
                    ty,
                    fn_name,
                    fn_name_ident,
                    inner,
                    &arg_name_pair,
                    true,
                    i,
                    param,
                    required_args,
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
                return Err(crate::types::LispError::new(err_str));
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
                    return Err(crate::types::LispError::new(err_str));
                }
            }
        }};
        Ok(outer_parse(
            self.dialect(),
            arg_name,
            tokens,
            param,
            required_args,
            idx,
        ))
    }

    /// generate an (optionally inlined) call to the original fn with the names of all of the variables,
    /// arg_names, filled in,, e.g. `fn myfn(arg_0, arg_1, arg_2, ...) { ... }`.
    /// This function also inserts a dynamic check to throw an error if too many
    /// arguments were provided based on the signature of the target function.
    fn make_orig_fn_call(
        &self,
        inline: bool,
        takes_env: bool,
        original_item_fn: &ItemFn,
        original_fn_name: &Ident,
        required_args: usize,
        arg_names: Vec<Ident>,
    ) -> MacroResult<TokenStream> {
        // the original function call must return an Expression object
        // this means all returned rust native types must implement TryIntoExpression
        // this is nested inside the builtin expression which must always
        // return a LispResult.
        let skip = usize::from(takes_env);
        let takes_env = if takes_env {
            quote! {environment, } // environment is the name that is passed in to this function
        } else {
            quote! {}
        };

        let (return_type, lisp_return) = self.get_return_type(original_item_fn)?;
        let returns_none = "()" == return_type.to_token_stream().to_string();
        let fn_body = if inline {
            let mut inline_toks = vec![];
            for (fn_arg, arg_name) in original_item_fn
                .sig
                .inputs
                .iter()
                .skip(skip)
                .zip(arg_names.iter())
            {
                match fn_arg {
                    FnArg::Receiver(_) => {}
                    FnArg::Typed(typed) => {
                        let pat = typed.pat.clone();
                        let ty = typed.ty.clone();
                        let binding = quote! {
                            let #pat: #ty = #arg_name;
                        };
                        inline_toks.push(binding);
                    }
                }
            }

            let block = original_item_fn.block.clone();
            match &original_item_fn.sig.output {
                ReturnType::Default => {
                    quote! {{
                        #(#inline_toks)*
                        let res = {
                            #block
                        };
                        res
                    }}
                }
                ReturnType::Type(_ra_arrow, ty) => {
                    quote! {{
                        #(#inline_toks)*
                        let res: #ty = {
                            #block
                        };
                        res
                    }}
                }
            }
        } else {
            quote! {
                #original_fn_name(#takes_env #(#arg_names),*)
            }
        };

        let original_fn_call = match (return_type, lisp_return, returns_none) {
            (Some(_), Some(SupportedGenericReturnTypes::LispResult), true) => quote! {
                #fn_body?;
                return Ok(crate::types::Expression::make_nil());
            },
            (Some(_), Some(SupportedGenericReturnTypes::Option), true) => quote! {
                #fn_body;
                return Ok(crate::types::Expression::make_nil());
            },
            (Some(_), Some(SupportedGenericReturnTypes::LispResult), false) => quote! {
                return #fn_body.map(Into::into);
            },
            (Some(_), Some(SupportedGenericReturnTypes::Option), false) => quote! {
                if let Some(val) = #fn_body {
                    return Ok(val.into());
                } else {
                    return Ok(crate::types::Expression::make_nil());
                }
            },
            // coerce to Expression
            (Some(_), None, _) => quote! {
                return Ok(#fn_body.into());
            },
            (None, Some(_), _) => {
                unreachable!("If this functions returns a LispResult it must also return a value.");
            }
            // no return
            (None, None, _) => quote! {
                #fn_body;
                return Ok(crate::types::Expression::make_nil());
            },
        };
        let const_params_len = self.get_const_params_len_ident();
        Ok(quote! {
            match args.get(#const_params_len) {
                Some(_) if #const_params_len == 0 || arg_types[#const_params_len - 1].handle != crate::macro_types::TypeHandle::VarArgs => {
                    return Err(crate::types::LispError::new(format!(
                        "{} given too many arguments, expected at least {} arguments, got {}.",
                        fn_name,
                        #required_args,
                        args.len()
                    )));
                }
                _ => {
                    #original_fn_call
                }
            }
        })
    }

    fn get_const_params_len_ident(&self) -> Ident {
        Ident::new("PARAMS_LEN", Span::call_site())
    }

    /// returns the option of inner type and the wrapped generic type (None if it's
    /// not generic. If there is no return type None, None is returned. Throws
    /// an error if the generic return type is not in the list of predefined
    /// constants POSSIBLE_RESULT_TYPES.
    fn get_return_type(
        &self,
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
                        "macro macros can only return generic arguments of types {:?}.",
                        &POSSIBLE_RETURN_TYPES
                    ),
                )),
            }
        } else {
            Ok((Some(return_type), None))
        }
    }
}
