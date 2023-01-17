use proc_macro::TokenStream;
use proc_macro2::Ident;
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::{
    parse::{Parse, Parser},
    parse_str, Attribute, Data, DeriveInput, Field, Fields, GenericParam, Generics, Type,
    Visibility,
};

struct PreDerive {
    attrs: Vec<Attribute>,
    vis: Visibility,
    struct_name: Ident,
    generics: Generics,
    data: Data,
    generic_inputs: proc_macro2::TokenStream,
    dst_crate_name: proc_macro2::TokenStream,
}

fn pre_derive(input: TokenStream) -> PreDerive {
    let struct_input: DeriveInput = syn::parse(input).unwrap();
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

    let dst_crate_name = match crate_name("dst-container").unwrap() {
        FoundCrate::Itself => quote!(crate),
        FoundCrate::Name(name) => {
            let name = parse_str::<Ident>(&name).unwrap();
            quote!(::#name)
        }
    };

    PreDerive {
        attrs: struct_input.attrs,
        vis: struct_input.vis,
        struct_name: struct_input.ident,
        generics,
        data: struct_input.data,
        generic_inputs,
        dst_crate_name,
    }
}

#[proc_macro_derive(MaybeUninitProject)]
pub fn derive_maybe_uninit_project(input: TokenStream) -> TokenStream {
    let PreDerive {
        attrs,
        vis,
        struct_name,
        generics,
        data,
        generic_inputs,
        dst_crate_name,
    } = pre_derive(input);

    let project_struct_name = parse_str::<Ident>(&format!("__MaybeUninit{struct_name}")).unwrap();

    let repr = attrs
        .iter()
        .find(|attr| attr.path.get_ident().map_or(false, |ident| ident == "repr"))
        .expect("Need #[repr(...)].");
    let repr_content = repr.tokens.to_string();
    if !matches!(repr_content.as_str(), "(C)" | "(packed)" | "(transparent)") {
        panic!("Expected #[repr(C)], #[repr(packed)], #[repr(transparent)] only.");
    }

    let project_data_declare = match data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => {
                let fields = fields.named.into_iter().collect::<Vec<_>>();
                let fields = map_maybe_uninit_fields(fields, &dst_crate_name);
                quote!({#(#fields,)*})
            }
            Fields::Unnamed(fields) => {
                let fields = fields.unnamed.into_iter().collect::<Vec<_>>();
                let fields = map_maybe_uninit_fields(fields, &dst_crate_name);
                quote!((#(#fields,)*);)
            }
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
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

fn map_maybe_uninit_fields(
    fields: impl IntoIterator<Item = Field>,
    dst_crate_name: &proc_macro2::TokenStream,
) -> Vec<Field> {
    fields
        .into_iter()
        .map(|mut field| {
            let ty = field.ty;
            field.ty = Type::parse
                .parse2(quote!(<#ty as #dst_crate_name :: MaybeUninitProject>::Target))
                .unwrap();
            field
        })
        .collect()
}

#[proc_macro_derive(UnsizedClone)]
pub fn derive_unsized_clone(input: TokenStream) -> TokenStream {
    let PreDerive {
        attrs: _,
        vis: _,
        struct_name,
        generics,
        data,
        generic_inputs,
        dst_crate_name,
    } = pre_derive(input);

    let (types, idents) = match data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => {
                let fields = fields.named.into_iter().collect::<Vec<_>>();
                let types = fields
                    .iter()
                    .map(|field| &field.ty)
                    .cloned()
                    .collect::<Vec<_>>();
                let idents = fields
                    .iter()
                    .map(|field| field.ident.as_ref().unwrap())
                    .cloned()
                    .collect::<Vec<_>>();
                (types, idents)
            }
            Fields::Unnamed(fields) => {
                let fields = fields.unnamed.into_iter().collect::<Vec<_>>();
                let types = fields
                    .iter()
                    .map(|field| &field.ty)
                    .cloned()
                    .collect::<Vec<_>>();
                let idents = (0..fields.len())
                    .map(|i| Ident::parse.parse_str(&i.to_string()).unwrap())
                    .collect::<Vec<_>>();
                (types, idents)
            }
            _ => unimplemented!(),
        },
        _ => unimplemented!(),
    };

    let where_clause = quote!(where #(#types: UnsizedClone,)*);
    let clone_to_statement = idents
        .into_iter()
        .map(|ident| quote!(self.#ident.clone_to(&mut dest.#ident);))
        .collect::<Vec<_>>();

    let output = quote! {
        impl #generics #dst_crate_name :: UnsizedClone for #struct_name #generic_inputs #where_clause {
            fn clone_to(&self, dest: &mut Self::Target) {
                #(#clone_to_statement)*
            }
        }
    };
    TokenStream::from(output)
}
