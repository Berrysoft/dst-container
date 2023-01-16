use proc_macro::TokenStream;
use proc_macro2::Ident;
use quote::quote;
use syn::{
    parse::{Parse, Parser},
    parse_macro_input, parse_str, Data, DeriveInput, Fields, GenericParam, Type,
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
    let generic_inputs = quote!(<#(#generic_inputs,)*>);
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
            Fields::Named(named_fields) => {
                let fields = named_fields.named.into_iter().collect::<Vec<_>>();
                let fields = fields
                    .iter()
                    .map(|field| {
                        let mut field = field.clone();
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
                    .collect::<Vec<_>>();
                quote!({#(#fields,)*})
            }
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
    };

    let output = quote! {
        #[doc(hidden)]
        #repr
        #vis struct #project_struct_name #generics #project_data_declare

        impl #generics MaybeUninitProject for #struct_name #generic_inputs {
            type Target = #project_struct_name #generic_inputs;
        }
    };
    TokenStream::from(output)
}
