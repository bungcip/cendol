//! semantic analysis phase
use crate::{
    ast::{NameId, TypeRef},
    source_manager::SourceSpan,
};
use hashbrown::HashMap;
use serde::Serialize;
use std::num::NonZeroU32;

pub mod ast_to_mir;
pub mod name_resolver;
pub mod symbol_resolver;
pub mod symbol_table;
pub mod tests_lowering;
pub mod tests_mir;
pub mod type_resolver;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
    pub const GLOBAL: Self = ScopeId(unsafe { NonZeroU32::new_unchecked(1) });

    pub fn get(&self) -> u32 {
        self.0.get() - 1
    }

    pub fn from_index(index: usize) -> Self {
        ScopeId(NonZeroU32::new((index + 1) as u32).unwrap())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize)]
pub struct SymbolRef(NonZeroU32);

impl SymbolRef {
    pub fn get(&self) -> u32 {
        self.0.get() - 1
    }

    pub fn from_index(index: usize) -> Self {
        SymbolRef(NonZeroU32::new((index + 1) as u32).unwrap())
    }
}

/// Represents a symbol in the symbol table
#[derive(Debug, Clone, Serialize)]
pub struct SymbolEntry {
    pub name: NameId,
    pub type_info: TypeRef,
    pub kind: SymbolKind,
    pub def_span: SourceSpan,
    pub is_completed: bool, // for structs/unions, if they have been defined
    pub scope_id: ScopeId,
}

/// Different kinds of symbols that can be in the symbol table
#[derive(Debug, Clone, Serialize)]
pub enum SymbolKind {
    Variable {
        is_static: bool,
        is_extern: bool,
    },
    Function {
        is_static: bool,
        is_inline: bool,
    },
    Parameter,
    Typedef,
    EnumConstant {
        value: i64,
    },
    RecordTag, // struct/union tag
    Label,
    Member, // struct/union member
}

/// Represents a scope in the symbol table
#[derive(Debug, Clone)]
pub struct Scope {
    pub kind: ScopeKind,
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<NameId, SymbolRef>,
    pub tags: HashMap<NameId, SymbolRef>, // for struct/union/enum tags
    pub labels: HashMap<NameId, SymbolRef>,
}

/// Different kinds of scopes
#[derive(Debug, Clone)]
pub enum ScopeKind {
    File,
    Function(SymbolRef),
    Block,
    Record(SymbolRef), // for struct/union members
    Enum(SymbolRef),   // for enum constants
    Prototype,         // for function prototype parameters
}
