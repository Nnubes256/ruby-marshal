//! Derive macros for `ruby-marshal`.

#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]
#![allow(clippy::wildcard_imports)]
#![allow(clippy::missing_errors_doc)]
#![allow(clippy::too_many_lines)]
#![allow(clippy::items_after_statements)]
#![allow(clippy::option_if_let_else)]
#![allow(
    clippy::module_name_repetitions,
    clippy::must_use_candidate,
    clippy::missing_const_for_fn,
    clippy::inefficient_to_string,
    clippy::multiple_crate_versions,
    clippy::redundant_pub_crate,
    clippy::use_self
)]

use crate::utils::symbols::*;
use proc_macro2::{Ident, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
    parse_macro_input, spanned::Spanned, Attribute, Data, DeriveInput, Field, GenericArgument,
    Generics, Meta, NestedMeta, Type,
};

mod utils;

#[proc_macro_derive(FromRubyMarshal, attributes(marshal))]
pub fn derive(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let res: proc_macro::TokenStream = derive_inner(input).into();
    res
}

enum TyType<'a> {
    Required(&'a Type),
    Optional(&'a Type),
}

fn retrieve_field_type(ty: &Type) -> TyType {
    let Type::Path(ref path) = ty else {
        return TyType::Required(ty);
    };

    let Some(possible_option) = path.path.segments.first() else {
        return TyType::Required(ty);
    };

    match &possible_option.arguments {
        syn::PathArguments::AngleBracketed(abga) if possible_option.ident == "Option" => {
            match abga.args.first() {
                Some(GenericArgument::Type(a)) => TyType::Optional(a),
                _ => TyType::Required(ty),
            }
        }
        _ => TyType::Required(ty),
    }
}

#[derive(Default)]
struct TopOptions {
    crate_internal: bool,
}

fn derive_inner(input: DeriveInput) -> proc_macro2::TokenStream {
    let top_options = match extract_top_options(&input.attrs) {
        Ok(opts) => opts,
        Err(err) => return err.to_compile_error(),
    };
    let name = input.ident;
    let deserialize_fields_code = match parse_fields(&name, &input.generics, &input.data) {
        Ok(ts) => ts,
        Err(err) => return err.to_compile_error(),
    };
    let imports = if top_options.crate_internal {
        quote! {
            use crate::de::{Result as DeResult, Deserializer, FromRubyMarshal, RubyType, RawRubyType, ParsingError};
        }
    } else {
        quote! {
            extern crate ruby_marshal as _ruby_marshal;
            use _ruby_marshal::de::{Result as DeResult, Deserializer, FromRubyMarshal, RubyType, RawRubyType, ParsingError};
        }
    };

    quote! {
        #[doc(hidden)]
        #[allow(non_upper_case_globals, non_snake_case, unused_attributes, unused_qualifications, no_effect_underscore_binding)]
        const _: () = {
            #imports
            #deserialize_fields_code
        };
    }
}

fn extract_top_options(attrs: &[Attribute]) -> syn::Result<TopOptions> {
    let mut top_options = TopOptions::default();
    for meta_item in attrs
        .iter()
        .flat_map(utils::get_marshal_meta_items)
        .flatten()
    {
        match &meta_item {
            // Parse `#[marshal(__crate_internal)]`
            NestedMeta::Meta(Meta::Path(word)) if word == CRATE_INTERNAL => {
                top_options.crate_internal = true;
            }
            NestedMeta::Meta(x) => {
                let path = x.path().to_token_stream().to_string().replace(' ', "");
                return Err(syn::Error::new(
                    x.path().span(),
                    format!("unknown marshal container attribute `{path}`"),
                ));
            }
            NestedMeta::Lit(x) => {
                return Err(syn::Error::new(
                    x.span(),
                    "unexpected literal in marshal field attribute",
                ))
            }
        }
    }
    Ok(top_options)
}

#[derive(Default)]
struct FieldOptions {
    rename: Option<String>,
    ivar_data: bool,
}

fn extract_field_options(attrs: &[Attribute]) -> syn::Result<FieldOptions> {
    let mut field_options = FieldOptions::default();
    for meta_item in attrs
        .iter()
        .flat_map(utils::get_marshal_meta_items)
        .flatten()
    {
        match &meta_item {
            // Parse `#[marshal(rename)]`
            NestedMeta::Meta(Meta::NameValue(word)) if word.path == RENAME => {
                if let syn::Lit::Str(s) = word.lit.clone() {
                    field_options.rename = Some(s.value());
                } else {
                    return Err(syn::Error::new(
                        word.lit.span(),
                        "expected marshal rename attribute to be a string: `rename = \"...\"`",
                    ));
                }
            }
            NestedMeta::Meta(Meta::Path(word)) if word == IVAR_DATA => {
                field_options.ivar_data = true;
            }
            NestedMeta::Meta(x) => {
                let path = x.path().to_token_stream().to_string().replace(' ', "");
                return Err(syn::Error::new(
                    x.path().span(),
                    format!("unknown marshal container attribute `{path}`"),
                ));
            }
            NestedMeta::Lit(x) => {
                return Err(syn::Error::new(
                    x.span(),
                    "unexpected literal in marshal field attribute",
                ))
            }
        }
    }
    Ok(field_options)
}

struct FieldInfo<'a> {
    field: &'a Field,
    field_type: TyType<'a>,
    var_name: Ident,
}

fn parse_fields(struct_name: &Ident, generics: &Generics, data: &Data) -> syn::Result<TokenStream> {
    let de_lifetime = generics
        .lifetimes()
        .map(|v| &v.lifetime)
        .find(|v| v.ident == LIFETIME_DE);
    match data {
        syn::Data::Struct(dtst) => match &dtst.fields {
            syn::Fields::Named(fields) => {
                let mut deserialize_fields_def = Vec::with_capacity(fields.named.len());
                let mut deserialize_fields_code = Vec::with_capacity(fields.named.len());
                let mut final_build_method_none_checks = Vec::with_capacity(fields.named.len());
                let mut final_build_method_struct_construct_fields =
                    Vec::with_capacity(fields.named.len());
                let mut ivar_data_field = None;
                for field in &fields.named {
                    let name = field
                        .ident
                        .as_ref()
                        .ok_or_else(|| syn::Error::new(field.span(), "Field has no name?!"))?;
                    let field_type = retrieve_field_type(&field.ty);
                    let attrs = extract_field_options(&field.attrs)?;

                    let var_name = Ident::new(&format!("__{struct_name}__{name}"), field.span());
                    deserialize_fields_def.push(quote_spanned!(field.span()=>
                        let mut #var_name = None;
                    ));
                    if attrs.ivar_data {
                        if ivar_data_field.is_some() {
                            return Err(syn::Error::new(
                                field.span(),
                                "duplicate #[marshal(ivar_data)] attribute",
                            ));
                        }

                        ivar_data_field = Some(FieldInfo {
                            field,
                            field_type,
                            var_name: var_name.clone(),
                        });
                    } else {
                        let name_string = if let Some(rename) = attrs.rename {
                            rename
                        } else {
                            name.to_string()
                        };
                        deserialize_fields_code.push(match field_type {
                            TyType::Required(_) => quote_spanned!(field.span()=>
                                RawRubyType::Symbol(#name_string) => {
                                    #var_name = it.next_element_of_type()?;
                                }
                            ),
                            TyType::Optional(_) => quote_spanned!(field.span()=>
                                RawRubyType::Symbol(#name_string) => {
                                    #var_name = it.next_element_of_type()?.flatten();
                                }
                            ),
                        });
                    }
                    let no_field_error_message = format!(
                        "Expected field {}, but was not found while deserializing {}",
                        name, struct_name
                    );
                    final_build_method_none_checks.push(match retrieve_field_type(&field.ty) {
                        TyType::Required(_) => quote_spanned! {field.span() =>
                            let #var_name = if let ::core::option::Option::Some(x) = #var_name.take() { x } else {
                                return ::core::result::Result::Err(ParsingError::Message(#no_field_error_message.to_string()));
                            };
                        },
                        TyType::Optional(_) => quote_spanned! {field.span() =>
                            let #var_name = #var_name.take();
                        },
                    });

                    final_build_method_struct_construct_fields.push(
                        quote_spanned! {field.span() =>
                            #name: #var_name
                        },
                    );
                }
                let impl_struct_name = if let Some(de) = de_lifetime {
                    quote_spanned!(struct_name.span() => #struct_name<#de>)
                } else {
                    struct_name.to_token_stream()
                };
                let deser_match_body = if let Some(ivar_meta) = ivar_data_field {
                    let var_name = ivar_meta.var_name;
                    let ivar_data_read = match ivar_meta.field_type {
                        TyType::Required(_) => quote_spanned!(ivar_meta.field.span()=>
                            let (ivar_data, mut it) = iv.read_data_of_type()?;
                            #var_name = Some(ivar_data);
                        ),
                        TyType::Optional(_) => quote_spanned!(ivar_meta.field.span()=>
                            let (ivar_data, mut it) = iv.read_data_of_type()?;
                            #var_name = ivar_data;
                        ),
                    };
                    quote! {
                        RubyType::InstanceVariable(mut iv) => {
                            #ivar_data_read
                            while let Some(mut key) = it.next_raw_element()? {
                                match key {
                                    #(#deserialize_fields_code),*
                                    _ => {
                                        let _ = it.skip_element()?;
                                    }
                                }
                            }
                        }
                        _ => return Err(ParsingError::Message("Expected ivar".to_string())),
                    }
                } else {
                    quote! {
                        RubyType::Hash(mut it) => {
                            while let Some(mut key) = it.next_raw_element()? {
                                match key {
                                    #(#deserialize_fields_code),*
                                    _ => {
                                        let _ = it.skip_element()?;
                                    }
                                }
                            }
                        }
                        _ => return Err(ParsingError::Message("Expected map".to_string())),
                    }
                };
                Ok(quote! {
                    #[automatically_derived]
                    impl<'de> FromRubyMarshal<'de> for #impl_struct_name {
                        fn deserialize(deserializer: &mut Deserializer<'de>) -> DeResult<Self> {
                            #(#deserialize_fields_def)*

                            match deserializer.next_element()?.get() {
                                #deser_match_body
                            }

                            #(#final_build_method_none_checks)*
                            ::core::result::Result::Ok(#struct_name {
                                #(#final_build_method_struct_construct_fields),*
                            })
                        }
                    }
                })
            }
            syn::Fields::Unnamed(_) => todo!(),
            syn::Fields::Unit => todo!(),
        },
        syn::Data::Enum(_) => todo!(),
        syn::Data::Union(_) => todo!(),
    }
}
