//! Symbol table management and scope handling.
//!
//! This module provides the core data structures and operations for managing
//! symbols and scopes during semantic analysis. It maintains a hierarchical
//! scope structure and provides efficient symbol lookup and storage.

use hashbrown::HashMap;
use std::num::NonZeroU32;
use std::sync::Arc;
use thiserror::Error;

use crate::{
    ast::*,
    semantic::{QualType, RecordMember, TypeRef},
};

/// Defines the kind of builtin function for efficient identification in later phases.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize)]
pub enum BuiltinFunctionKind {
    // Atomic operations
    AtomicLoadN,
    AtomicStoreN,
    AtomicExchangeN,
    AtomicCompareExchangeN,
    AtomicFetchAdd,
    AtomicFetchSub,
    AtomicFetchAnd,
    AtomicFetchOr,
    AtomicFetchXor,
    AtomicAddFetch,
    AtomicSubFetch,
    AtomicAndFetch,
    AtomicOrFetch,
    AtomicXorFetch,

    // Bitwise builtins
    Popcount,
    PopcountL,
    PopcountLL,
    Clz,
    ClzL,
    ClzLL,
    Ctz,
    CtzL,
    CtzLL,
    Ffs,
    FfsL,
    FfsLL,

    // Math builtins
    Fabs,
    FabsF,
    FabsL,

    // Memory builtins
    Memcpy,
    Memmove,
    Memset,
    Memcmp,

    // Varargs builtins
    VaStart,
    VaEnd,
    VaCopy,

    // Other builtins
    Expect,
    ConstantP,
    Unreachable,
    Trap,
    Prefetch,
    Alloca,
    Complex,

    // Float constant builtins
    Inff,
    HugeValf,
    Inf,
    HugeVal,
    Nanf,
    Nan,

    // Bswap builtins
    Bswap16,
    Bswap32,
    Bswap64,

    Signbit,
    SignbitF,
    SignbitL,
    FrameAddress,
    Pause,
}

impl BuiltinFunctionKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::AtomicLoadN => "__atomic_load_n",
            Self::AtomicStoreN => "__atomic_store_n",
            Self::AtomicExchangeN => "__atomic_exchange_n",
            Self::AtomicCompareExchangeN => "__atomic_compare_exchange_n",
            Self::AtomicFetchAdd => "__atomic_fetch_add",
            Self::AtomicFetchSub => "__atomic_fetch_sub",
            Self::AtomicFetchAnd => "__atomic_fetch_and",
            Self::AtomicFetchOr => "__atomic_fetch_or",
            Self::AtomicFetchXor => "__atomic_fetch_xor",
            Self::AtomicAddFetch => "__atomic_add_fetch",
            Self::AtomicSubFetch => "__atomic_sub_fetch",
            Self::AtomicAndFetch => "__atomic_and_fetch",
            Self::AtomicOrFetch => "__atomic_or_fetch",
            Self::AtomicXorFetch => "__atomic_xor_fetch",
            Self::Popcount => "__builtin_popcount",
            Self::PopcountL => "__builtin_popcountl",
            Self::PopcountLL => "__builtin_popcountll",
            Self::Clz => "__builtin_clz",
            Self::ClzL => "__builtin_clzl",
            Self::ClzLL => "__builtin_clzll",
            Self::Ctz => "__builtin_ctz",
            Self::CtzL => "__builtin_ctzl",
            Self::CtzLL => "__builtin_ctzll",
            Self::Ffs => "__builtin_ffs",
            Self::FfsL => "__builtin_ffsl",
            Self::FfsLL => "__builtin_ffsll",
            Self::Fabs => "__builtin_fabs",
            Self::FabsF => "__builtin_fabsf",
            Self::FabsL => "__builtin_fabsl",
            Self::Memcpy => "__builtin_memcpy",
            Self::Memmove => "__builtin_memmove",
            Self::Memset => "__builtin_memset",
            Self::Memcmp => "__builtin_memcmp",
            Self::VaStart => "__builtin_va_start",
            Self::VaEnd => "__builtin_va_end",
            Self::VaCopy => "__builtin_va_copy",
            Self::Expect => "__builtin_expect",
            Self::ConstantP => "__builtin_constant_p",
            Self::Unreachable => "__builtin_unreachable",
            Self::Trap => "__builtin_trap",
            Self::Prefetch => "__builtin_prefetch",
            Self::Alloca => "__builtin_alloca",
            Self::Complex => "__builtin_complex",
            Self::Inff => "__builtin_inff",
            Self::HugeValf => "__builtin_huge_valf",
            Self::Inf => "__builtin_inf",
            Self::HugeVal => "__builtin_huge_val",
            Self::Nanf => "__builtin_nanf",
            Self::Nan => "__builtin_nan",
            Self::Bswap16 => "__builtin_bswap16",
            Self::Bswap32 => "__builtin_bswap32",
            Self::Bswap64 => "__builtin_bswap64",
            Self::Signbit => "__builtin_signbit",
            Self::SignbitF => "__builtin_signbitf",
            Self::SignbitL => "__builtin_signbitl",
            Self::FrameAddress => "__builtin_frame_address",
            Self::Pause => "__builtin_ia32_pause",
        }
    }

    pub const ALL_VARIANTS: &[Self] = &[
        Self::AtomicLoadN,
        Self::AtomicStoreN,
        Self::AtomicExchangeN,
        Self::AtomicCompareExchangeN,
        Self::AtomicFetchAdd,
        Self::AtomicFetchSub,
        Self::AtomicFetchAnd,
        Self::AtomicFetchOr,
        Self::AtomicFetchXor,
        Self::AtomicAddFetch,
        Self::AtomicSubFetch,
        Self::AtomicAndFetch,
        Self::AtomicOrFetch,
        Self::AtomicXorFetch,
        Self::Popcount,
        Self::PopcountL,
        Self::PopcountLL,
        Self::Clz,
        Self::ClzL,
        Self::ClzLL,
        Self::Ctz,
        Self::CtzL,
        Self::CtzLL,
        Self::Ffs,
        Self::FfsL,
        Self::FfsLL,
        Self::Fabs,
        Self::FabsF,
        Self::FabsL,
        Self::Memcpy,
        Self::Memmove,
        Self::Memset,
        Self::Memcmp,
        Self::VaStart,
        Self::VaEnd,
        Self::VaCopy,
        Self::Expect,
        Self::ConstantP,
        Self::Unreachable,
        Self::Trap,
        Self::Prefetch,
        Self::Alloca,
        Self::Complex,
        Self::Inff,
        Self::HugeValf,
        Self::Inf,
        Self::HugeVal,
        Self::Nanf,
        Self::Nan,
        Self::Bswap16,
        Self::Bswap32,
        Self::Bswap64,
        Self::Signbit,
        Self::SignbitF,
        Self::SignbitL,
        Self::FrameAddress,
        Self::Pause,
    ];

    pub fn is_bitwise(self) -> bool {
        matches!(
            self,
            Self::Popcount
                | Self::PopcountL
                | Self::PopcountLL
                | Self::Clz
                | Self::ClzL
                | Self::ClzLL
                | Self::Ctz
                | Self::CtzL
                | Self::CtzLL
                | Self::Ffs
                | Self::FfsL
                | Self::FfsLL
        )
    }

    pub fn is_fabs(self) -> bool {
        matches!(self, Self::Fabs | Self::FabsF | Self::FabsL)
    }

    pub fn to_atomic_op(self) -> Option<AtomicOp> {
        match self {
            Self::AtomicLoadN => Some(AtomicOp::LoadN),
            Self::AtomicStoreN => Some(AtomicOp::StoreN),
            Self::AtomicExchangeN => Some(AtomicOp::ExchangeN),
            Self::AtomicCompareExchangeN => Some(AtomicOp::CompareExchangeN),
            Self::AtomicFetchAdd => Some(AtomicOp::FetchAdd),
            Self::AtomicFetchSub => Some(AtomicOp::FetchSub),
            Self::AtomicFetchAnd => Some(AtomicOp::FetchAnd),
            Self::AtomicFetchOr => Some(AtomicOp::FetchOr),
            Self::AtomicFetchXor => Some(AtomicOp::FetchXor),
            Self::AtomicAddFetch => Some(AtomicOp::AddFetch),
            Self::AtomicSubFetch => Some(AtomicOp::SubFetch),
            Self::AtomicAndFetch => Some(AtomicOp::AndFetch),
            Self::AtomicOrFetch => Some(AtomicOp::OrFetch),
            Self::AtomicXorFetch => Some(AtomicOp::XorFetch),
            _ => None,
        }
    }
}

pub type SymbolRef = NonZeroU32;

/// Represents the definition state of a symbol entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionState {
    Tentative,    // int x;
    Defined,      // int x = ...;
    DeclaredOnly, // extern int x;
}

/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
/// Symbol are stored in a separate Vec<Symbol> with SymbolRef references.
/// invariant:
/// - Variable / Typedef / Function: type_info is meaningful
/// - EnumConstant: type_info = int (unqualified)
/// - Label / RecordTag / EnumTag: type_info = TypeKind::Error
#[derive(Debug, Clone)]
pub struct Symbol {
    pub name: NameId,
    pub kind: SymbolKind, // e.g., Variable, Function, Typedef
    pub type_info: QualType,
    pub scope_id: ScopeId, // Reference to the scope where it's defined
    pub def_span: SourceSpan,
    pub def_state: DefinitionState,
    pub is_completed: bool,
    pub visibility: crate::lang_options::Visibility,
    pub has_explicit_visibility: bool,
}

impl Symbol {
    pub(crate) fn is_const(&self) -> bool {
        self.type_info.is_const()
    }

    pub(crate) fn has_linkage(&self) -> bool {
        match &self.kind {
            SymbolKind::Function(_) => true,
            SymbolKind::Variable(v) => v.is_global || v.storage == Some(StorageClass::Extern) || v.is_thread_local,
            _ => false,
        }
    }

    pub(crate) fn has_static_duration(&self) -> bool {
        match &self.kind {
            SymbolKind::Variable(v) => {
                v.is_global || v.storage == Some(StorageClass::Static) || v.storage == Some(StorageClass::Extern)
            }
            SymbolKind::Function(_) => true,
            _ => false,
        }
    }

    pub(crate) fn get_function_storage(&self) -> Option<StorageClass> {
        match &self.kind {
            SymbolKind::Function(f) => f.storage,
            _ => None,
        }
    }

    pub(crate) fn is_function(&self) -> bool {
        matches!(self.kind, SymbolKind::Function(_))
    }
}

/// Defines the kind of symbol.
#[derive(Debug, Clone)]
pub enum SymbolKind {
    Variable(Variable),
    Function(Function),
    Typedef {
        aliased_type: QualType,
    },
    EnumConstant {
        value: i64, // Resolved constant value
    },
    Label,
    Record {
        is_complete: bool,
        members: Arc<[RecordMember]>,
    },
    EnumTag {
        is_complete: bool,
    },
    // Add other symbol kinds as needed (e.g., Macro, BlockScope)
}

/// Symbol table error types
#[derive(Debug, Error)]
pub enum SymbolTableError {
    #[error("Invalid redefinition: symbol '{name}' cannot be redefined")]
    InvalidRedefinition { name: NameId, existing: SymbolRef },
}

use serde::Serialize;

/// Scope ID for efficient scope references
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
    pub const GLOBAL: Self = Self(NonZeroU32::new(1).unwrap());

    pub(crate) fn new(id: u32) -> Option<Self> {
        NonZeroU32::new(id).map(Self)
    }

    pub(crate) fn get(self) -> u32 {
        self.0.get()
    }
}

/// Symbol namespaces in C
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Namespace {
    Ordinary, // Variables, functions, typedefs, enum constants
    Tag,      // Struct, union, and enum tags
    Label,    // Goto labels
}

/// Scope information
#[derive(Debug, Default, Clone)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<NameId, SymbolRef>, // Ordinary identifiers
    pub tags: HashMap<NameId, SymbolRef>,    // Struct/union/enum tags
    pub labels: HashMap<NameId, SymbolRef>,  // Goto labels
    pub level: u32,
}

/// Represents a variable in the symbol table.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Variable {
    pub is_global: bool,
    pub is_thread_local: bool,
    pub storage: Option<StorageClass>,
    pub initializer: Option<NodeRef>,
    pub alignment: Option<u16>,
    pub cleanup_func: Option<SymbolRef>,
}

/// Represents a function in the symbol table.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Function {
    pub storage: Option<StorageClass>,
    pub is_noreturn: bool,
    pub param_len: u16,
    pub builtin_kind: Option<BuiltinFunctionKind>,
}

#[derive(Debug)]
enum UndoOp {
    MapInsertion {
        scope_id: ScopeId,
        namespace: Namespace,
        name: NameId,
        prev_symbol: Option<SymbolRef>,
    },
    SymbolModified {
        index: SymbolRef,
        old_symbol: Box<Symbol>,
    },
}

/// Symbol table using flattened storage
#[derive(Debug)]
pub struct SymbolTable {
    pub entries: Vec<Symbol>,
    pub scopes: Vec<Scope>,
    current_scope_id: ScopeId,
    next_scope_id: u32,
    undo_log: Vec<UndoOp>,
}

impl SymbolTable {
    pub(crate) fn new() -> Self {
        // ⚡ Bolt: Pre-allocate space for symbols and scopes to avoid multiple reallocations.
        // A medium-sized C translation unit can easily have hundreds of symbols and multiple scopes.
        let mut table = SymbolTable {
            entries: Vec::with_capacity(512),
            scopes: Vec::with_capacity(32),
            current_scope_id: ScopeId::GLOBAL,
            next_scope_id: 2, // Start after GLOBAL
            undo_log: Vec::with_capacity(512),
        };

        // Initialize global scope
        table.scopes.push(Scope::default());

        table.entries.push(Symbol {
            name: NameId::new(""),
            kind: SymbolKind::Label,
            type_info: QualType::unqualified(TypeRef::dummy()),
            scope_id: ScopeId::GLOBAL,
            def_span: SourceSpan::empty(),
            def_state: DefinitionState::DeclaredOnly,
            is_completed: false,
            visibility: crate::lang_options::Visibility::Default,
            has_explicit_visibility: false,
        });
        table
    }

    pub(crate) fn push_scope(&mut self) -> ScopeId {
        let new_scope_id = ScopeId::new(self.next_scope_id).unwrap();
        self.next_scope_id += 1;

        let new_scope = Scope {
            parent: Some(self.current_scope_id),
            level: self.scopes[self.current_scope_id.get() as usize - 1].level + 1,
            ..Default::default()
        };

        self.scopes.push(new_scope);
        self.current_scope_id = new_scope_id;
        new_scope_id
    }

    pub(crate) fn pop_scope(&mut self) -> Option<ScopeId> {
        let current_scope_id_before_pop = self.current_scope_id;
        let current_scope = &self.scopes[current_scope_id_before_pop.get() as usize - 1];
        if let Some(parent) = current_scope.parent {
            self.current_scope_id = parent;
            Some(parent)
        } else {
            None
        }
    }

    pub(crate) fn current_scope(&self) -> ScopeId {
        self.current_scope_id
    }

    pub(crate) fn set_current_scope(&mut self, scope_id: ScopeId) {
        self.current_scope_id = scope_id;
    }

    pub(crate) fn get_scope(&self, scope_id: ScopeId) -> &Scope {
        &self.scopes[scope_id.get() as usize - 1]
    }

    pub(crate) fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut Scope {
        &mut self.scopes[scope_id.get() as usize - 1]
    }

    fn record_map_insertion(&mut self, scope_id: ScopeId, ns: Namespace, name: NameId, prev: Option<SymbolRef>) {
        self.undo_log.push(UndoOp::MapInsertion {
            scope_id,
            namespace: ns,
            name,
            prev_symbol: prev,
        });
    }

    fn add_symbol_in_scope(&mut self, name: NameId, entry: Symbol, scope_id: ScopeId) -> SymbolRef {
        let sym = self.push_symbol(entry);
        let scope = self.get_scope_mut(scope_id);
        let prev = scope.symbols.insert(name, sym);
        self.record_map_insertion(scope_id, Namespace::Ordinary, name, prev);
        sym
    }

    fn add_symbol(&mut self, name: NameId, entry: Symbol) -> SymbolRef {
        self.add_symbol_in_scope(name, entry, self.current_scope_id)
    }

    fn add_symbol_in_namespace(&mut self, name: NameId, entry: Symbol, ns: Namespace) -> SymbolRef {
        let sym = self.push_symbol(entry);
        let scope_id = self.current_scope_id;
        let current_scope = self.get_scope_mut(scope_id);
        let prev = match ns {
            Namespace::Ordinary => current_scope.symbols.insert(name, sym),
            Namespace::Tag => current_scope.tags.insert(name, sym),
            Namespace::Label => current_scope.labels.insert(name, sym),
        };
        self.record_map_insertion(scope_id, ns, name, prev);
        sym
    }

    pub(crate) fn lookup_symbol_and_scope(&self, name: NameId) -> Option<(SymbolRef, ScopeId)> {
        self.lookup(name, self.current_scope_id, Namespace::Ordinary)
    }

    pub(crate) fn lookup_symbol(&self, name: NameId) -> Option<SymbolRef> {
        self.lookup(name, self.current_scope_id, Namespace::Ordinary)
            .map(|(s, _)| s)
    }

    pub(super) fn lookup_tag(&self, name: NameId) -> Option<(SymbolRef, ScopeId)> {
        self.lookup(name, self.current_scope_id, Namespace::Tag)
    }

    pub(crate) fn lookup(&self, name: NameId, start_scope: ScopeId, ns: Namespace) -> Option<(SymbolRef, ScopeId)> {
        let mut scope_id = start_scope;
        loop {
            let scope = self.get_scope(scope_id);
            let result = match ns {
                Namespace::Ordinary => scope.symbols.get(&name),
                Namespace::Tag => scope.tags.get(&name),
                Namespace::Label => scope.labels.get(&name),
            };
            if let Some(&sym) = result {
                return Some((sym, scope_id));
            }
            if let Some(parent) = scope.parent {
                scope_id = parent;
            } else {
                break;
            }
        }
        None
    }

    /// find a symbol in exact scope without looking to parent scope if not exist
    pub(crate) fn fetch(&self, name: NameId, scope_id: ScopeId, ns: Namespace) -> Option<SymbolRef> {
        let scope = self.get_scope(scope_id);
        match ns {
            Namespace::Ordinary => scope.symbols.get(&name).copied(),
            Namespace::Tag => scope.tags.get(&name).copied(),
            Namespace::Label => scope.labels.get(&name).copied(),
        }
    }

    /// fetch a symbol in exact current scope without looking to parent scope if not exist
    pub(crate) fn fetch_current(&self, name: NameId, ns: Namespace) -> Option<SymbolRef> {
        self.fetch(name, self.current_scope_id, ns)
    }

    fn push_symbol(&mut self, entry: Symbol) -> SymbolRef {
        let index = self.entries.len() as u32 + 1;
        self.entries.push(entry);
        SymbolRef::new(index).expect("SymbolEntryRef overflow")
    }

    pub(crate) fn get_symbol(&self, index: SymbolRef) -> &Symbol {
        &self.entries[(index.get() - 1) as usize]
    }

    pub(crate) fn get_symbol_mut(&mut self, index: SymbolRef) -> &mut Symbol {
        &mut self.entries[(index.get() - 1) as usize]
    }

    /// define builtin function in Global scope
    pub(crate) fn define_builtin_function(
        &mut self,
        name: NameId,
        func_ty: TypeRef,
        func: Function,
    ) -> Result<SymbolRef, SymbolTableError> {
        let mut symbol = self.create_symbol(
            name,
            SymbolKind::Function(func),
            QualType::unqualified(func_ty),
            SourceSpan::empty(),
        );

        // Builtin declarations are always "DeclaredOnly"
        symbol.def_state = DefinitionState::DeclaredOnly;

        // Builtin declarations are always in global scope
        self.merge_global_symbol(name, symbol)
    }

    /// helper method to create symbol
    fn create_symbol(&mut self, name: NameId, kind: SymbolKind, ty: QualType, span: SourceSpan) -> Symbol {
        Symbol {
            name,
            kind,
            type_info: ty,
            scope_id: self.current_scope_id,
            def_span: span,
            def_state: DefinitionState::Defined,
            is_completed: true,
            visibility: crate::lang_options::Visibility::Default,
            has_explicit_visibility: false,
        }
    }

    /// Define a typedef in the parser (used for type disambiguation).
    pub(crate) fn define_parser_typedef(&mut self, name: NameId, span: SourceSpan) {
        let ty = QualType::unqualified(TypeRef::dummy());
        let symbol = self.create_symbol(name, SymbolKind::Typedef { aliased_type: ty }, ty, span);
        let sym_ref = self.push_symbol(symbol);
        let scope_id = self.current_scope_id;
        let prev = self.get_scope_mut(scope_id).symbols.insert(name, sym_ref);
        self.record_map_insertion(scope_id, Namespace::Ordinary, name, prev);
    }

    /// Define a non-typedef in the parser (used for type disambiguation).
    pub(crate) fn define_parser_non_typedef(&mut self, name: NameId, span: SourceSpan) {
        let ty = QualType::unqualified(TypeRef::dummy());
        let var = Variable {
            is_global: self.current_scope_id == ScopeId::GLOBAL,
            is_thread_local: false,
            storage: None,
            initializer: None,
            alignment: None,
            cleanup_func: None,
        };
        let symbol = self.create_symbol(name, SymbolKind::Variable(var), ty, span);
        let sym_ref = self.push_symbol(symbol);
        let scope_id = self.current_scope_id;
        let prev = self.get_scope_mut(scope_id).symbols.insert(name, sym_ref);
        self.record_map_insertion(scope_id, Namespace::Ordinary, name, prev);
    }

    /// Define a new variable in the current scope.
    /// Handles global variable merging and local variable insertion.
    pub(crate) fn define_variable(
        &mut self,
        name: NameId,
        ty: QualType,
        span: SourceSpan,
        var: Variable,
    ) -> Result<SymbolRef, SymbolTableError> {
        let mut symbol = self.create_symbol(name, SymbolKind::Variable(var), ty, span);

        symbol.def_state = match var {
            v if v.initializer.is_some() => DefinitionState::Defined,
            v if v.storage == Some(StorageClass::Extern) => DefinitionState::DeclaredOnly,
            _ => DefinitionState::Tentative,
        };

        if !symbol.has_linkage() {
            return Ok(self.add_symbol(name, symbol));
        }

        if self.current_scope_id == ScopeId::GLOBAL {
            return self.merge_global_symbol(name, symbol);
        }

        // Local declaration with linkage (e.g. extern int x;)
        // C11 6.2.2 linkage merging: search for a visible prior declaration with linkage.
        let target = self
            .lookup_symbol(name)
            .filter(|&s| self.get_symbol(s).has_linkage())
            .or_else(|| {
                // If not visible, it has external linkage and refers to the global symbol if it exists.
                self.fetch(name, ScopeId::GLOBAL, Namespace::Ordinary)
                    .filter(|&s| self.get_symbol(s).has_linkage())
            });

        let target = match target {
            Some(existing) => existing,
            None => {
                // No existing linkage symbol found, create/merge a new one in global scope.
                symbol.scope_id = ScopeId::GLOBAL;
                self.merge_global_symbol(name, symbol)?
            }
        };

        // Link the local name to the target symbol
        let scope_id = self.current_scope_id;
        let prev = self.get_scope_mut(scope_id).symbols.insert(name, target);
        self.record_map_insertion(scope_id, Namespace::Ordinary, name, prev);
        Ok(target)
    }

    /// Define a new function in the current scope.
    /// Handles global function merging (declarations/definitions).
    pub(crate) fn define_function(
        &mut self,
        name: NameId,
        ty: TypeRef,
        span: SourceSpan,
        func: Function,
        is_definition: bool,
    ) -> Result<SymbolRef, SymbolTableError> {
        let mut symbol = self.create_symbol(name, SymbolKind::Function(func), QualType::unqualified(ty), span);

        // Function declarations are "DeclaredOnly" by default, or "Defined" if it's a function definition
        symbol.def_state = if is_definition {
            DefinitionState::Defined
        } else {
            DefinitionState::DeclaredOnly
        };

        if self.current_scope_id == ScopeId::GLOBAL {
            self.merge_global_symbol(name, symbol)
        } else {
            // Function declarations in local scope always have linkage
            if let Some(existing) = self.lookup_symbol(name) {
                let existing_sym = self.get_symbol(existing);
                if existing_sym.has_linkage() {
                    self.get_scope_mut(self.current_scope_id).symbols.insert(name, existing);
                    return Ok(existing);
                }
            }

            if let Some(global) = self.fetch(name, ScopeId::GLOBAL, Namespace::Ordinary) {
                let global_sym = self.get_symbol(global);
                if global_sym.has_linkage() {
                    self.get_scope_mut(self.current_scope_id).symbols.insert(name, global);
                    return Ok(global);
                }
            }

            // Create global entry for the function
            symbol.scope_id = ScopeId::GLOBAL;
            let global = self.merge_global_symbol(name, symbol)?;
            let scope_id = self.current_scope_id;
            let prev = self.get_scope_mut(scope_id).symbols.insert(name, global);
            self.record_map_insertion(scope_id, Namespace::Ordinary, name, prev);
            Ok(global)
        }
    }

    /// Define a typedef in the current scope.
    pub(crate) fn define_typedef(
        &mut self,
        name: NameId,
        ty: QualType,
        span: SourceSpan,
    ) -> Result<SymbolRef, SymbolTableError> {
        let symbol = self.create_symbol(name, SymbolKind::Typedef { aliased_type: ty }, ty, span);

        // Check for redefinition in the SAME scope
        if let Some(existing) = self.fetch_current(name, Namespace::Ordinary) {
            return Err(SymbolTableError::InvalidRedefinition { name, existing });
        }

        Ok(self.add_symbol(name, symbol))
    }

    /// Define an enum constant in the current scope.
    pub(crate) fn define_enum_constant(
        &mut self,
        name: NameId,
        value: i64,
        ty: TypeRef,
        span: SourceSpan,
    ) -> Result<SymbolRef, SymbolTableError> {
        let symbol = self.create_symbol(
            name,
            SymbolKind::EnumConstant { value },
            QualType::unqualified(ty),
            span,
        );
        if let Some(existing) = self.fetch_current(name, Namespace::Ordinary) {
            return Err(SymbolTableError::InvalidRedefinition { name, existing });
        }

        Ok(self.add_symbol(name, symbol))
    }

    /// Define a record (struct/union) tag in the current scope.
    pub(crate) fn define_record(
        &mut self,
        name: NameId,
        ty: TypeRef,
        is_complete: bool,
        span: SourceSpan,
    ) -> SymbolRef {
        let mut symbol = self.create_symbol(
            name,
            SymbolKind::Record {
                is_complete,
                members: Arc::new([]),
            },
            QualType::unqualified(ty),
            span,
        );
        symbol.is_completed = false;
        self.add_symbol_in_namespace(name, symbol, Namespace::Tag)
    }

    /// Define an enum tag in the current scope.
    pub(crate) fn define_enum(&mut self, name: NameId, ty: TypeRef, span: SourceSpan) -> SymbolRef {
        let mut symbol = self.create_symbol(
            name,
            SymbolKind::EnumTag { is_complete: false },
            QualType::unqualified(ty),
            span,
        );
        symbol.is_completed = false;
        self.add_symbol_in_namespace(name, symbol, Namespace::Tag)
    }

    /// Define a label in the current scope.
    pub(crate) fn define_label(
        &mut self,
        name: NameId,
        ty: TypeRef,
        span: SourceSpan,
    ) -> Result<SymbolRef, SymbolTableError> {
        if let Some(existing) = self.fetch_current(name, Namespace::Label) {
            return Err(SymbolTableError::InvalidRedefinition { name, existing });
        }
        let symbol = self.create_symbol(name, SymbolKind::Label, QualType::unqualified(ty), span);
        Ok(self.add_symbol_in_namespace(name, symbol, Namespace::Label))
    }

    /// Lookup a label in the current scope.
    pub(crate) fn lookup_label(&self, name: NameId) -> Option<(SymbolRef, ScopeId)> {
        self.lookup(name, self.current_scope_id, Namespace::Label)
    }

    /// Merge a new symbol entry with an existing one in the global scope.
    /// This implements C11 6.9.2 for handling tentative definitions, extern declarations, and actual definitions.
    fn merge_global_symbol(&mut self, name: NameId, new_entry: Symbol) -> Result<SymbolRef, SymbolTableError> {
        let Some(sym) = self.fetch(name, ScopeId::GLOBAL, Namespace::Ordinary) else {
            return Ok(self.add_symbol_in_scope(name, new_entry, ScopeId::GLOBAL));
        };

        let old_symbol = Box::new(self.get_symbol(sym).clone());
        self.undo_log.push(UndoOp::SymbolModified { index: sym, old_symbol });

        let existing = self.get_symbol_mut(sym);

        // 1. Verify kinds match and check variable-specific constraints
        match (&mut existing.kind, &new_entry.kind) {
            (SymbolKind::Variable(existing_var), SymbolKind::Variable(new_var)) => {
                if existing_var.is_thread_local != new_var.is_thread_local {
                    return Err(SymbolTableError::InvalidRedefinition { name, existing: sym });
                }
                // Alignment compatibility
                match (existing_var.alignment, new_var.alignment) {
                    (Some(a), Some(b)) if a != b => {
                        return Err(SymbolTableError::InvalidRedefinition { name, existing: sym });
                    }
                    (None, Some(b)) => existing_var.alignment = Some(b),
                    _ => {}
                }
            }
            (SymbolKind::Function(_), SymbolKind::Function(_)) => {}
            _ => return Err(SymbolTableError::InvalidRedefinition { name, existing: sym }),
        }

        // 2. Apply C11 merging rules for definition states
        match (existing.def_state, new_entry.def_state) {
            (DefinitionState::Defined, DefinitionState::Defined) => {
                return Err(SymbolTableError::InvalidRedefinition { name, existing: sym });
            }
            (_, DefinitionState::Defined) => {
                existing.def_state = DefinitionState::Defined;
                if let (SymbolKind::Variable(existing_var), SymbolKind::Variable(new_var)) =
                    (&mut existing.kind, &new_entry.kind)
                {
                    existing_var.initializer = new_var.initializer;
                }
            }
            (DefinitionState::DeclaredOnly, DefinitionState::Tentative) => {
                existing.def_state = DefinitionState::Tentative;
            }
            _ => {}
        }

        Ok(sym)
    }

    pub(crate) fn save_state(&self) -> SymbolTableState {
        SymbolTableState {
            entries_len: self.entries.len(),
            scopes_len: self.scopes.len(),
            undo_log_len: self.undo_log.len(),
            current_scope_id: self.current_scope_id,
            next_scope_id: self.next_scope_id,
        }
    }

    pub(crate) fn restore_state(&mut self, state: SymbolTableState) {
        while self.undo_log.len() > state.undo_log_len {
            let op = self.undo_log.pop().unwrap();
            match op {
                UndoOp::MapInsertion {
                    scope_id,
                    namespace,
                    name,
                    prev_symbol,
                } => {
                    let scope = self.get_scope_mut(scope_id);
                    let map = match namespace {
                        Namespace::Ordinary => &mut scope.symbols,
                        Namespace::Tag => &mut scope.tags,
                        Namespace::Label => &mut scope.labels,
                    };
                    if let Some(prev) = prev_symbol {
                        map.insert(name, prev);
                    } else {
                        map.remove(&name);
                    }
                }
                UndoOp::SymbolModified { index, old_symbol } => {
                    self.entries[(index.get() - 1) as usize] = *old_symbol;
                }
            }
        }

        self.entries.truncate(state.entries_len);
        self.scopes.truncate(state.scopes_len);
        self.current_scope_id = state.current_scope_id;
        self.next_scope_id = state.next_scope_id;
    }

    pub(crate) fn clear_parser_symbols(&mut self) {
        self.entries.truncate(1);
        for scope in self.scopes.iter_mut() {
            scope.symbols.clear();
            scope.tags.clear();
            scope.labels.clear();
        }
        self.undo_log.clear();
        self.current_scope_id = ScopeId::GLOBAL;
    }
}

#[derive(Clone)]
pub struct SymbolTableState {
    entries_len: usize,
    scopes_len: usize,
    undo_log_len: usize,
    current_scope_id: ScopeId,
    next_scope_id: u32,
}
