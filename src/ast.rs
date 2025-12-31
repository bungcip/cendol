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
//!
//! ## Key Features
//!
//! - **Flattened Storage**: All AST nodes are stored in contiguous vectors with index-based references
//! - **Interior Mutability**: Uses `Cell` for type annotations without requiring mutable AST access
//! - **Builder Patterns**: Ergonomic constructors for complex AST nodes
//! - **Type System**: Canonical types distinct from syntactic type specifiers
//!

use std::cell::Cell;
use std::num::NonZeroU32;

/// Represents an interned string using symbol_table crate.
/// Alias for GlobalSymbol from symbol_table crate with global feature.
pub type NameId = symbol_table::GlobalSymbol;

use crate::semantic::{QualType, ScopeId, SymbolRef, TypeRef};
pub use crate::source_manager::{SourceId, SourceLoc, SourceSpan};

// Submodules
pub mod nodes;
pub mod parsed_types;
pub mod utils;

// Re-export commonly used items for convenience
pub use nodes::*;
pub use parsed_types::*;

// Re-export operators that are used throughout the codebase
pub use nodes::{BinaryOp, UnaryOp};
pub use utils::extract_identifier;

/// The flattened AST storage.
/// Contains all AST nodes, types, symbol entries in contiguous vectors.
pub struct Ast {
    pub nodes: Vec<Node>,
    pub parsed_types: ParsedTypeArena, // syntax type
    scope_map: Vec<Option<ScopeId>>,   // index = NodeRef
}

/// Node reference type for referencing child nodes.
pub type NodeRef = NonZeroU32;

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
            parsed_types: ParsedTypeArena::new(),
            scope_map: Vec::new(),
        }
    }

    /// Replace a node content in the AST without changing reference
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

    /// get root node ref, by default its first node
    pub fn get_root(&self) -> NodeRef {
        NonZeroU32::new(1).unwrap()
    }

    pub fn scope_of(&self, node: NodeRef) -> ScopeId {
        self.scope_map[(node.get() - 1) as usize].expect("ICE: AST Node scope is not set")
    }

    /// attach new scope map for AST
    pub fn attach_scope_map(&mut self, scope_map: Vec<Option<ScopeId>>) {
        self.scope_map = scope_map;
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
    pub resolved_type: Cell<Option<QualType>>, // Hot data, now ref-based
}

impl Node {
    /// Create a new node with the given kind and source span
    pub fn new(kind: NodeKind, span: SourceSpan) -> Self {
        Node {
            kind,
            span,
            resolved_type: Cell::new(None),
        }
    }
}
