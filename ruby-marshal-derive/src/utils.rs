use std::fmt::{self, Display};
use syn::{Ident, Meta, Path};

// Adapted from https://raw.githubusercontent.com/serde-rs/serde/6b948111ca56bb5cfd447f8516dea5fe1338e552/serde_derive/src/internals/symbol.rs
#[derive(Copy, Clone)]
pub struct Symbol(&'static str);

pub mod symbols {
    use super::Symbol;

    pub const MARSHAL: Symbol = Symbol("marshal");

    pub const CRATE_INTERNAL: Symbol = Symbol("__crate_internal");

    pub const RENAME: Symbol = Symbol("rename");
    pub const IVAR_DATA: Symbol = Symbol("ivar_data");

    pub const LIFETIME_DE: Symbol = Symbol("de");
}
use symbols::*;

impl PartialEq<Symbol> for Ident {
    fn eq(&self, word: &Symbol) -> bool {
        self == word.0
    }
}

impl<'a> PartialEq<Symbol> for &'a Ident {
    fn eq(&self, word: &Symbol) -> bool {
        *self == word.0
    }
}

impl PartialEq<Symbol> for Path {
    fn eq(&self, word: &Symbol) -> bool {
        self.is_ident(word.0)
    }
}

impl<'a> PartialEq<Symbol> for &'a Path {
    fn eq(&self, word: &Symbol) -> bool {
        self.is_ident(word.0)
    }
}

impl Display for Symbol {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str(self.0)
    }
}

// https://github.com/serde-rs/serde/blob/6b948111ca56bb5cfd447f8516dea5fe1338e552/serde_derive/src/internals/attr.rs#L1567-L1583
pub fn get_marshal_meta_items(
    //cx: &Ctxt,
    attr: &syn::Attribute,
) -> Result<Vec<syn::NestedMeta>, ()> {
    if attr.path != MARSHAL {
        return Ok(Vec::new());
    }

    match attr.parse_meta() {
        Ok(Meta::List(meta)) => Ok(meta.nested.into_iter().collect()),
        Ok(_other) => {
            //cx.error_spanned_by(other, "expected #[marshal(...)]");
            Err(())
        }
        Err(_err) => {
            //cx.syn_error(err);
            Err(())
        }
    }
}
