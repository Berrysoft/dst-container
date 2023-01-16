use proc_macro::TokenStream;
use proc_macro2::Ident;
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::{
    parse::{Parse, Parser},
    parse_macro_input, parse_str, Data, DeriveInput, Field, Fields, GenericParam, Type,
};

#[proc_macro_derive(MaybeUninitProject)]
pub fn derive_maybe_uninit_project(input: TokenStream) -> TokenStream {
    let struct_input = parse_macro_input!(input as DeriveInput);
    let struct_name = struct_input.ident;
    let vis = struct_input.vis;
    let generics = struct_input.generics;
    let generic_inputs = generics
        .params
        .iter()
        .map(|p| match p {
            GenericParam::Type(p) => {
                let ident = &p.ident;
                quote!(#ident)
            }
            GenericParam::Lifetime(p) => {
                let life = &p.lifetime;
                quote!(#life)
            }
            GenericParam::Const(p) => {
                let ident = &p.ident;
                quote!(#ident)
            }
        })
        .collect::<Vec<_>>();
    let generic_inputs = if generic_inputs.is_empty() {
        quote!()
    } else {
        quote!(<#(#generic_inputs,)*>)
    };
    let project_struct_name = parse_str::<Ident>(&format!("__MaybeUninit{struct_name}")).unwrap();

    let repr = struct_input
        .attrs
        .iter()
        .find(|attr| attr.path.get_ident().map_or(false, |ident| ident == "repr"))
        .expect("Need #[repr(...)].");
    let repr_content = repr.tokens.to_string();
    if !matches!(repr_content.as_str(), "(C)" | "(packed)" | "(transparent)") {
        panic!("Expected #[repr(C)], #[repr(packed)], #[repr(transparent)] only.");
    }

    let project_data_declare = match struct_input.data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => {
                let fields = fields.named.into_iter().collect::<Vec<_>>();
                let fields = map_maybe_uninit_fields(fields);
                quote!({#(#fields,)*})
            }
            Fields::Unnamed(fields) => {
                let fields = fields.unnamed.into_iter().collect::<Vec<_>>();
                let fields = map_maybe_uninit_fields(fields);
                quote!((#(#fields,)*);)
            }
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
    };

    let dst_crate_name = match crate_name("dst-container").unwrap() {
        FoundCrate::Itself => quote!(crate),
        FoundCrate::Name(name) => {
            let name = parse_str::<Ident>(&name).unwrap();
            quote!(::#name)
        }
    };

    let output = quote! {
        #[doc(hidden)]
        #repr
        #vis struct #project_struct_name #generics #project_data_declare

        impl #generics #dst_crate_name :: MaybeUninitProject for #struct_name #generic_inputs {
            type Target = #project_struct_name #generic_inputs;
        }
    };
    TokenStream::from(output)
}

fn map_maybe_uninit_fields(fields: impl IntoIterator<Item = Field>) -> Vec<Field> {
    fields
        .into_iter()
        .map(|mut field| {
            field.ty = match field.ty {
                Type::Slice(slice) => {
                    let ty = slice.elem;
                    Type::parse.parse2(quote!([::core::mem::MaybeUninit<#ty>]))
                }
                ty => Type::parse.parse2(quote!(::core::mem::MaybeUninit<#ty>)),
            }
            .unwrap();
            field
        })
        .collect()
}
