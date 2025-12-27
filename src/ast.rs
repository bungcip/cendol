//! Abstract Syntax Tree (AST) for C11 compiler.
//!
//! This module provides the core AST data structures and APIs for representing
//! C11 programs. The AST is designed as a flattened storage system for efficiency,
//! with index-based references to child nodes and types.
//!
//! ## Architecture
//!
//! The AST is organized into focused submodules for better maintainability:
//!
//! - [`nodes`]: Node definitions, constructors, and builder patterns for AST nodes
//! - [`types`]: Type system representation and utilities for semantic analysis
//! - [`visitor`]: Visitor pattern implementation for AST traversal and transformation
//!
//! ## Key Features
//!
//! - **Flattened Storage**: All AST nodes are stored in contiguous vectors with index-based references
//! - **Interior Mutability**: Uses `Cell` for type annotations without requiring mutable AST access
//! - **Builder Patterns**: Ergonomic constructors for complex AST nodes
//! - **Visitor Pattern**: Clean separation of algorithms from AST structure
//! - **Type System**: Canonical types distinct from syntactic type specifiers
//!
//! ## Usage
//!
//! ```rust,ignore
//! use cendol::ast::{Ast, NodeKind};
//!
//! let mut ast = Ast::new();
//! let int_node = ast.push_node(Node::new(NodeKind::literal_int(42), span));
//! ```
//!
//! ## Compatibility
//!
//! This refactoring maintains full backward compatibility with existing code
//! while improving the internal organization and adding new ergonomic features.

use std::cell::Cell;
use std::num::NonZeroU32;

/// Represents an interned string using symbol_table crate.
/// Alias for GlobalSymbol from symbol_table crate with global feature.
pub type Symbol = symbol_table::GlobalSymbol;

pub use crate::source_manager::{SourceId, SourceLoc, SourceSpan};

// Submodules
pub mod nodes;
pub mod types;
pub mod utils;

// Re-export commonly used items for convenience
pub use nodes::*;
pub use types::*;

// Re-export operators that are used throughout the codebase
pub use nodes::{BinaryOp, UnaryOp};
pub use utils::extract_identifier;

/// The flattened AST storage.
/// Contains all AST nodes, types, and symbol entries in contiguous vectors.
pub struct Ast {
    pub nodes: Vec<Node>,
    pub types: Vec<Type>,
    pub symbol_entries: Vec<SymbolEntry>,
    pub root: Option<NodeRef>,
}

/// Node reference type for referencing child nodes.
pub type NodeRef = NonZeroU32;
pub type TypeRef = NonZeroU32;
pub type SymbolEntryRef = NonZeroU32;

/// Helper methods for Ast.
impl Default for Ast {
    fn default() -> Self {
        Self::new()
    }
}

impl Ast {
    /// Create a new empty AST
    pub fn new() -> Self {
        Ast {
            nodes: Vec::new(),
            types: Vec::new(),
            symbol_entries: Vec::new(),
            root: None,
        }
    }

    /// Set the root node of the AST
    pub(crate) fn set_root_node(&mut self, node_ref: NodeRef) {
        self.root = Some(node_ref);
    }

    /// Replace a node in the AST and update parent references
    /// Returns the reference to the new node
    pub(crate) fn replace_node(&mut self, old_node_ref: NodeRef, new_node: Node) -> NodeRef {
        // Replace the old node in the vector
        let old_index = (old_node_ref.get() - 1) as usize;
        self.nodes[old_index] = new_node;

        // Return the same reference since we're replacing in place
        old_node_ref
    }

    /// Add a node to the AST and return its reference
    pub(crate) fn push_node(&mut self, node: Node) -> NodeRef {
        let index = self.nodes.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.nodes.push(node);
        NodeRef::new(index).expect("NodeRef overflow")
    }

    /// Get a node by its reference
    pub fn get_node(&self, index: NodeRef) -> &Node {
        &self.nodes[(index.get() - 1) as usize]
    }

    /// Add a type to the AST and return its reference
    pub(crate) fn push_type(&mut self, ty: Type) -> TypeRef {
        let index = self.types.len() as u32 + 1;
        self.types.push(ty);
        TypeRef::new(index).expect("TypeRef overflow")
    }

    /// Get a type by its reference
    pub fn get_type(&self, index: TypeRef) -> &Type {
        let idx = (index.get() - 1) as usize;
        if idx >= self.types.len() {
            panic!(
                "Type index {} out of bounds: types vector has {} elements",
                index.get(),
                self.types.len()
            );
        }
        &self.types[idx]
    }
}

/// The primary AST node structure.
/// Stored in the flattened Vec<Node>, with index-based references.
/// Designed to be small and cache-friendly.
#[derive(Debug, Clone)]
pub struct Node {
    pub kind: NodeKind,
    pub span: SourceSpan,
    // Uses Cell for Interior Mutability: allows type checking to annotate the AST
    // without requiring mutable access to the entire tree structure.
    pub resolved_type: Cell<Option<TypeRef>>, // Hot data, now ref-based
    // After semantic analysis, for Ident nodes, this will point to the resolved symbol entry.
    pub resolved_symbol: Cell<Option<SymbolEntryRef>>, // Hot data, now ref-based
}

impl Node {
    /// Create a new node with the given kind and source span
    pub fn new(kind: NodeKind, span: SourceSpan) -> Self {
        Node {
            kind,
            span,
            resolved_symbol: Cell::new(None),
            resolved_type: Cell::new(None),
        }
    }
}

/// Represents the definition state of a symbol entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionState {
    Tentative, // int x;
    Defined,   // int x = ...;
    Declared,  // extern int x; or function prototype
}

/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
/// Symbol entries are stored in a separate Vec<SymbolEntry> with SymbolEntryRef references.
#[derive(Debug, Clone)]
pub struct SymbolEntry {
    pub name: Symbol,
    pub kind: SymbolKind, // e.g., Variable, Function, Typedef
    pub type_info: TypeRef,
    pub storage_class: Option<StorageClass>,
    pub scope_id: u32, // Reference to the scope where it's defined
    pub def_span: SourceSpan,
    pub def_state: DefinitionState,
    pub is_referenced: bool,
    pub is_completed: bool,
    // Add other relevant symbol information here (e.g., value for constants, linkage)
}

/// Defines the kind of symbol.
#[derive(Debug, Clone)]
pub enum SymbolKind {
    Variable {
        is_global: bool,
        is_static: bool,
        // Initializer might be an AST node or a constant value
        initializer: Option<NodeRef>,
    },
    Function {
        is_definition: bool,
        is_inline: bool,
        is_variadic: bool,
        parameters: Vec<FunctionParameter>,
    },
    Typedef {
        aliased_type: TypeRef,
    },
    EnumConstant {
        value: i64, // Resolved constant value
    },
    Label {
        is_defined: bool,
        is_used: bool,
    },
    Record {
        is_complete: bool,
        members: Vec<StructMember>,
        size: Option<usize>,
        alignment: Option<usize>,
    },
    EnumTag {
        is_complete: bool,
    },
    // Add other symbol kinds as needed (e.g., Macro, BlockScope)
}

/// Function parameter information
#[derive(Debug, Clone)]
pub struct FunctionParameter {
    pub param_type: TypeRef,
    pub name: Option<Symbol>,
}

/// Struct/union member information
#[derive(Debug, Clone)]
pub struct StructMember {
    pub name: Symbol,
    pub member_type: TypeRef,
    pub bit_field_size: Option<usize>,
    pub span: SourceSpan,
}

/// Enum constant information
#[derive(Debug, Clone)]
pub struct EnumConstant {
    pub name: Symbol,
    pub value: i64, // Resolved value
    pub span: SourceSpan,
}
