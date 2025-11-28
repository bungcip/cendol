//! Symbol table management and scope handling.
//!
//! This module provides the core data structures and operations for managing
//! symbols and scopes during semantic analysis. It maintains a hierarchical
//! scope structure and provides efficient symbol lookup and storage.

use hashbrown::HashMap;
use std::num::NonZeroU32;

use log::debug;

use crate::ast::*;

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

/// Scope types
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Global,
    File,
    Function,
    Block,
    FunctionPrototype,
}

/// Scope information
#[derive(Debug)]
pub struct Scope {
    pub parent: Option<ScopeId>,
    pub symbols: HashMap<Symbol, SymbolEntryRef>,
    pub kind: ScopeKind,
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
            kind: ScopeKind::Global,
            level: 0,
        });

        table
    }

    pub fn push_scope(&mut self, kind: ScopeKind) -> ScopeId {
        let new_scope_id = ScopeId::new(self.next_scope_id).unwrap();
        self.next_scope_id += 1;

        let new_scope = Scope {
            parent: Some(self.current_scope_id),
            symbols: HashMap::new(),
            kind,
            level: self.scopes[self.current_scope_id.get() as usize - 1].level + 1,
        };

        self.scopes.push(new_scope);
        self.current_scope_id = new_scope_id;
        debug!(
            "SymbolTable: Pushed scope. New current_scope_id: {}",
            self.current_scope_id.get()
        );
        new_scope_id
    }

    pub fn push_scope_with_id(&mut self, scope_id: ScopeId, kind: ScopeKind) -> ScopeId {
        // Update next_scope_id to ensure uniqueness
        if scope_id.get() >= self.next_scope_id {
            self.next_scope_id = scope_id.get() + 1;
        }

        let new_scope = Scope {
            parent: Some(self.current_scope_id),
            symbols: HashMap::new(),
            kind,
            level: self.scopes[self.current_scope_id.get() as usize - 1].level + 1,
        };

        // Ensure the scope vector is large enough
        while self.scopes.len() < scope_id.get() as usize {
            self.scopes.push(Scope {
                parent: None,
                symbols: HashMap::new(),
                kind: ScopeKind::Global,
                level: 0,
            });
        }

        // Replace the scope at the given index
        if scope_id.get() as usize <= self.scopes.len() {
            self.scopes[scope_id.get() as usize - 1] = new_scope;
        } else {
            self.scopes.push(new_scope);
        }

        self.current_scope_id = scope_id;
        debug!(
            "SymbolTable: Pushed scope with ID. New current_scope_id: {}",
            self.current_scope_id.get()
        );
        scope_id
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
        debug!(
            "SymbolTable: Set current_scope_id to {}",
            self.current_scope_id.get()
        );
    }

    pub fn get_scope(&self, scope_id: ScopeId) -> &Scope {
        &self.scopes[scope_id.get() as usize - 1]
    }

    pub fn get_scope_mut(&mut self, scope_id: ScopeId) -> &mut Scope {
        &mut self.scopes[scope_id.get() as usize - 1]
    }

    pub fn add_symbol(&mut self, name: Symbol, entry: SymbolEntry) -> SymbolEntryRef {
        let entry_ref = self.push_symbol_entry(entry);
        let current_scope = self.get_scope_mut(self.current_scope_id);
        current_scope.symbols.insert(name, entry_ref);
        entry_ref
    }

    pub fn lookup_symbol(&self, name: Symbol) -> Option<(SymbolEntryRef, ScopeId)> {
        self.lookup_symbol_from(name, self.current_scope_id)
    }

    pub fn lookup_symbol_from(&self, name: Symbol, start_scope: ScopeId) -> Option<(SymbolEntryRef, ScopeId)> {
        let mut scope_id = start_scope;
        loop {
            let scope = self.get_scope(scope_id);
            if let Some(&entry_ref) = scope.symbols.get(&name) {
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

    pub fn lookup_symbol_in_scope(
        &self,
        name: Symbol,
        scope_id: ScopeId,
    ) -> Option<SymbolEntryRef> {
        self.get_scope(scope_id).symbols.get(&name).copied()
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
}