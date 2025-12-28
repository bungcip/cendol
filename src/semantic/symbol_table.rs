//! Symbol table management and scope handling.
//!
//! This module provides the core data structures and operations for managing
//! symbols and scopes during semantic analysis. It maintains a hierarchical
//! scope structure and provides efficient symbol lookup and storage.

use hashbrown::HashMap;
use std::num::NonZeroU32;

use log::debug;
use thiserror::Error;

use crate::ast::*;

pub type SymbolEntryRef = NonZeroU32;

/// Represents the definition state of a symbol entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionState {
    Tentative,    // int x;
    Defined,      // int x = ...;
    DeclaredOnly, // extern int x;
}

/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
/// Symbol entries are stored in a separate Vec<SymbolEntry> with SymbolEntryRef references.
#[derive(Debug, Clone)]
pub struct SymbolEntry {
    pub name: NameId,
    pub kind: SymbolKind, // e.g., Variable, Function, Typedef
    pub type_info: TypeRef,
    #[allow(unused)]
    pub storage_class: Option<StorageClass>,
    #[allow(unused)]
    pub scope_id: ScopeId, // Reference to the scope where it's defined
    pub def_span: SourceSpan,
    pub def_state: DefinitionState,
    #[allow(unused)]
    pub is_referenced: bool,
    pub is_completed: bool,
}

/// Defines the kind of symbol.
#[derive(Debug, Clone)]
pub enum SymbolKind {
    Variable {
        is_global: bool,
        // Initializer might be an AST node or a constant value
        initializer: Option<NodeRef>,
    },
    Function {
        #[allow(unused)]
        is_inline: bool,
        #[allow(unused)]
        is_variadic: bool,
        #[allow(unused)]
        parameters: Vec<FunctionParameter>,
    },
    Typedef {
        aliased_type: TypeRef,
    },
    EnumConstant {
        value: i64, // Resolved constant value
    },
    #[allow(unused)]
    Label {
        is_defined: bool,
        is_used: bool,
    },
    Record {
        is_complete: bool,
        members: Vec<StructMember>,
        #[allow(unused)]
        size: Option<usize>,
        #[allow(unused)]
        alignment: Option<usize>,
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
    InvalidRedefinition { name: NameId },
}

/// Scope ID for efficient scope references
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(NonZeroU32);

impl ScopeId {
    pub const GLOBAL: Self = Self(NonZeroU32::new(1).unwrap());

    pub fn new(id: u32) -> Option<Self> {
        NonZeroU32::new(id).map(Self)
    }

    pub fn get(self) -> u32 {
        self.0.get()
    }
}

/// Symbol namespaces in C
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Namespace {
    Ordinary, // Variables, functions, typedefs, enum constants
    Tag,      // Struct, union, and enum tags

    // TODO: currently, no code write Namespace::Label, need to fix
    #[allow(unused)]
    Label, // Goto labels
}

/// Scope information
#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<NameId, SymbolEntryRef>, // Ordinary identifiers
    pub tags: HashMap<NameId, SymbolEntryRef>,    // Struct/union/enum tags
    pub labels: HashMap<NameId, SymbolEntryRef>,  // Goto labels
    pub level: u32,
}

/// Symbol table using flattened storage
#[derive(Debug)]
pub struct SymbolTable {
    pub entries: Vec<SymbolEntry>,
    pub scopes: Vec<Scope>,
    current_scope_id: ScopeId,
    next_scope_id: u32,
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolTable {
    pub fn new() -> Self {
        let mut table = SymbolTable {
            entries: Vec::new(),
            scopes: Vec::new(),
            current_scope_id: ScopeId::GLOBAL,
            next_scope_id: 2, // Start after GLOBAL
        };

        // Initialize global scope
        table.scopes.push(Scope {
            parent: None,
            symbols: HashMap::new(),
            tags: HashMap::new(),
            labels: HashMap::new(),
            // kind: ScopeKind::Global,
            level: 0,
        });

        table
    }

    pub fn push_scope(&mut self) -> ScopeId {
        let new_scope_id = ScopeId::new(self.next_scope_id).unwrap();
        self.next_scope_id += 1;

        if (new_scope_id.get() as usize) <= self.scopes.len() {
            // Re-use existing scope during second pass (e.g. analysis after lowering)
            self.current_scope_id = new_scope_id;
            debug!(
                "SymbolTable: Re-entering existing scope {}. Current scope is now {}",
                new_scope_id.get(),
                self.current_scope_id.get()
            );
            return new_scope_id;
        }

        let new_scope = Scope {
            parent: Some(self.current_scope_id),
            symbols: HashMap::new(),
            tags: HashMap::new(),
            labels: HashMap::new(),
            // kind,
            level: self.scopes[self.current_scope_id.get() as usize - 1].level + 1,
        };

        self.scopes.push(new_scope);
        self.current_scope_id = new_scope_id;
        debug!(
            "SymbolTable: Pushed new scope. New current_scope_id: {}",
            self.current_scope_id.get()
        );
        new_scope_id
    }

    /// Reset the traversal state to the global scope.
    /// Used between different passes (e.g. between lowering and analysis) to re-enter
    /// the same hierarchy of scopes in the same order.
    pub fn reset_traversal(&mut self) {
        self.current_scope_id = ScopeId::GLOBAL;
        self.next_scope_id = 2;
        debug!("SymbolTable: Traversal reset to GLOBAL");
    }

    pub fn pop_scope(&mut self) -> Option<ScopeId> {
        let current_scope_id_before_pop = self.current_scope_id;
        let current_scope = &self.scopes[current_scope_id_before_pop.get() as usize - 1];
        if let Some(parent) = current_scope.parent {
            self.current_scope_id = parent;
            debug!(
                "SymbolTable: Popped scope. Old current_scope_id: {}, New current_scope_id: {}",
                current_scope_id_before_pop.get(),
                self.current_scope_id.get()
            );
            Some(parent)
        } else {
            debug!("SymbolTable: Attempted to pop global scope. No change.");
            None
        }
    }

    pub fn current_scope(&self) -> ScopeId {
        self.current_scope_id
    }

    pub fn set_current_scope(&mut self, scope_id: ScopeId) {
        self.current_scope_id = scope_id;
        debug!("SymbolTable: Set current_scope_id to {}", self.current_scope_id.get());
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &Scope {
        &self.scopes[scope_id.get() as usize - 1]
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut Scope {
        &mut self.scopes[scope_id.get() as usize - 1]
    }

    pub fn add_symbol(&mut self, name: NameId, entry: SymbolEntry) -> SymbolEntryRef {
        let entry_ref = self.push_symbol_entry(entry);
        let current_scope = self.get_scope_mut(self.current_scope_id);
        current_scope.symbols.insert(name, entry_ref);
        entry_ref
    }

    pub fn add_symbol_in_namespace(&mut self, name: NameId, entry: SymbolEntry, ns: Namespace) -> SymbolEntryRef {
        let entry_ref = self.push_symbol_entry(entry);
        let current_scope = self.get_scope_mut(self.current_scope_id);
        match ns {
            Namespace::Ordinary => current_scope.symbols.insert(name, entry_ref),
            Namespace::Tag => current_scope.tags.insert(name, entry_ref),
            Namespace::Label => current_scope.labels.insert(name, entry_ref),
        };
        entry_ref
    }

    pub fn lookup_symbol(&self, name: NameId) -> Option<(SymbolEntryRef, ScopeId)> {
        self.lookup_symbol_from_ns(name, self.current_scope_id, Namespace::Ordinary)
    }

    pub fn lookup_tag(&self, name: NameId) -> Option<(SymbolEntryRef, ScopeId)> {
        self.lookup_symbol_from_ns(name, self.current_scope_id, Namespace::Tag)
    }

    pub fn lookup_symbol_from_ns(
        &self,
        name: NameId,
        start_scope: ScopeId,
        ns: Namespace,
    ) -> Option<(SymbolEntryRef, ScopeId)> {
        let mut scope_id = start_scope;
        loop {
            let scope = self.get_scope(scope_id);
            let maybe_entry = match ns {
                Namespace::Ordinary => scope.symbols.get(&name),
                Namespace::Tag => scope.tags.get(&name),
                Namespace::Label => scope.labels.get(&name),
            };
            if let Some(&entry_ref) = maybe_entry {
                return Some((entry_ref, scope_id));
            }
            if let Some(parent) = scope.parent {
                scope_id = parent;
            } else {
                break;
            }
        }
        None
    }

    pub fn lookup_symbol_in_scope(&self, name: NameId, scope_id: ScopeId) -> Option<SymbolEntryRef> {
        self.lookup_symbol_in_scope_ns(name, scope_id, Namespace::Ordinary)
    }

    pub fn lookup_symbol_in_scope_ns(&self, name: NameId, scope_id: ScopeId, ns: Namespace) -> Option<SymbolEntryRef> {
        let scope = self.get_scope(scope_id);
        match ns {
            Namespace::Ordinary => scope.symbols.get(&name).copied(),
            Namespace::Tag => scope.tags.get(&name).copied(),
            Namespace::Label => scope.labels.get(&name).copied(),
        }
    }

    fn push_symbol_entry(&mut self, entry: SymbolEntry) -> SymbolEntryRef {
        let index = self.entries.len() as u32 + 1;
        self.entries.push(entry);
        SymbolEntryRef::new(index).expect("SymbolEntryRef overflow")
    }

    pub fn get_symbol_entry(&self, index: SymbolEntryRef) -> &SymbolEntry {
        &self.entries[(index.get() - 1) as usize]
    }

    pub fn get_symbol_entry_mut(&mut self, index: SymbolEntryRef) -> &mut SymbolEntry {
        &mut self.entries[(index.get() - 1) as usize]
    }

    /// Merge a new symbol entry with an existing one in the global scope.
    /// This implements C11 6.9.2 for handling tentative definitions, extern declarations, and actual definitions.
    pub fn merge_global_symbol(
        &mut self,
        name: NameId,
        mut new_entry: SymbolEntry,
    ) -> Result<SymbolEntryRef, SymbolTableError> {
        let global_scope = ScopeId::GLOBAL;

        // Check if symbol already exists in global scope
        if let Some(existing_ref) = self.lookup_symbol_in_scope(name, global_scope) {
            let existing = self.get_symbol_entry_mut(existing_ref);

            // Both must be variables to merge
            let (existing_var, new_var) = match (&mut existing.kind, &mut new_entry.kind) {
                (SymbolKind::Variable { .. }, SymbolKind::Variable { .. }) => (existing, &mut new_entry),
                _ => {
                    // Not both variables, this is a real redefinition
                    debug!("Symbol '{}' redefinition: different kinds", name);
                    return Err(SymbolTableError::InvalidRedefinition { name });
                }
            };

            // Apply C11 6.9.2 merging rules
            match (existing_var.def_state, new_var.def_state) {
                (DefinitionState::Tentative, DefinitionState::Tentative) => {
                    // Multiple tentative definitions - OK
                    debug!("Merging tentative definitions for '{}'", name);
                }

                (DefinitionState::Tentative, DefinitionState::Defined) => {
                    // Tentative definition followed by actual definition
                    debug!("Converting tentative definition to defined for '{}'", name);
                    existing_var.def_state = DefinitionState::Defined;
                    if let SymbolKind::Variable { initializer, .. } = &mut new_var.kind
                        && let SymbolKind::Variable {
                            initializer: existing_init,
                            ..
                        } = &mut existing_var.kind
                    {
                        *existing_init = *initializer;
                    }
                }

                (DefinitionState::DeclaredOnly, DefinitionState::Defined) => {
                    // Extern declaration followed by actual definition
                    debug!("Converting extern declaration to defined for '{}'", name);
                    existing_var.def_state = DefinitionState::Defined;
                    if let SymbolKind::Variable { initializer, .. } = &mut new_var.kind
                        && let SymbolKind::Variable {
                            initializer: existing_init,
                            ..
                        } = &mut existing_var.kind
                    {
                        *existing_init = *initializer;
                    }
                }

                (DefinitionState::Tentative, DefinitionState::DeclaredOnly) => {
                    // Tentative definition followed by extern declaration - OK
                    debug!("Merging tentative definition with extern declaration for '{}'", name);
                    existing_var.def_state = DefinitionState::DeclaredOnly;
                }

                (DefinitionState::Defined, DefinitionState::Defined) => {
                    // Multiple actual definitions - error
                    debug!("Multiple definitions of '{}'", name);
                    return Err(SymbolTableError::InvalidRedefinition { name });
                }

                (DefinitionState::Defined, _) => {
                    // Already defined, ignore new declaration
                    debug!("Ignoring redundant declaration for already-defined '{}'", name);
                }

                (DefinitionState::DeclaredOnly, _) => {
                    // Already declared as extern, ignore new declaration
                    debug!("Ignoring redundant extern declaration for '{}'", name);
                }
            }

            Ok(existing_ref)
        } else {
            // Symbol doesn't exist, add it
            debug!(
                "Adding new global symbol '{}' with def_state {:?}",
                name, new_entry.def_state
            );
            Ok(self.add_symbol(name, new_entry))
        }
    }
}
