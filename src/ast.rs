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

use std::num::NonZeroU32;

/// Represents an interned string using symbol_table crate.
/// Alias for GlobalSymbol from symbol_table crate with global feature.
pub type NameId = symbol_table::GlobalSymbol;

use crate::semantic::{QualType, ScopeId, SemanticInfo, SymbolRef, TypeRef, ValueCategory};
pub use crate::source_manager::{SourceId, SourceLoc, SourceSpan};

// Submodules
// Submodules
pub mod dumper;
pub mod literal;
pub mod literal_parsing;
pub mod nodes;
pub mod parsed;
pub mod parsed_types;

// Re-export commonly used items for convenience
pub use nodes::*;
pub use parsed::*;
pub use parsed_types::*;

// Re-export operators that are used throughout the codebase
pub use nodes::{BinaryOp, UnaryOp};

/// The flattened AST storage.
/// Contains all AST nodes, types, symbol entries in contiguous vectors.
#[derive(Clone, Default)]
pub struct Ast {
    pub kinds: Vec<NodeKind>,
    pub spans: Vec<SourceSpan>,
    pub semantic_info: Option<SemanticInfo>, // Populated after type resolution
}

impl Ast {
    /// Create a new empty AST
    pub fn new() -> Self {
        Ast::default()
    }

    /// Add a node to the AST and return its reference
    pub(crate) fn push_node(&mut self, kind: NodeKind, span: SourceSpan) -> NodeRef {
        let index = self.kinds.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.kinds.push(kind);
        self.spans.push(span);
        NodeRef::new(index).expect("NodeRef overflow")
    }

    /// Add a dummy node to the AST and return its reference
    pub(crate) fn push_dummy(&mut self, span: SourceSpan) -> NodeRef {
        self.push_node(NodeKind::Dummy, span)
    }

    /// Get node kind by reference
    pub fn get_kind(&self, node_ref: NodeRef) -> &NodeKind {
        &self.kinds[node_ref.index()]
    }

    /// Get node span by reference
    pub fn get_span(&self, node_ref: NodeRef) -> SourceSpan {
        self.spans[node_ref.index()]
    }

    /// get root node ref
    pub fn get_root(&self) -> NodeRef {
        NodeRef::ROOT
    }

    pub fn scope_of(&self, node_ref: NodeRef) -> ScopeId {
        match &self.kinds[node_ref.index()] {
            NodeKind::TranslationUnit(data) => data.scope_id,
            NodeKind::Function(data) => data.scope_id,
            NodeKind::FunctionDecl(data) => data.scope_id,
            NodeKind::CompoundStatement(data) => data.scope_id,
            NodeKind::For(data) => data.scope_id,
            _ => panic!("ICE: Node {:?} does not have a scope", self.get_kind(node_ref)),
        }
    }

    /// attach semantic info side table for AST (populated after type resolution)
    pub fn attach_semantic_info(&mut self, semantic_info: SemanticInfo) {
        self.semantic_info = Some(semantic_info);
    }
}

/// Node reference type for referencing child nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct NodeRef(NonZeroU32);

impl NodeRef {
    pub const ROOT: NodeRef = NodeRef(NonZeroU32::new(1).unwrap());

    pub fn new(value: u32) -> Option<Self> {
        NonZeroU32::new(value).map(Self)
    }

    pub fn get(self) -> u32 {
        self.0.get()
    }

    pub fn index(self) -> usize {
        (self.get() - 1) as usize
    }

    /// Create an iterator over a range of consecutive NodeRefs, starting from `self`.
    #[inline]
    pub fn range(self, len: impl Into<u32>) -> NodeRefRange {
        NodeRefRange {
            current: self.get(),
            end: self.get() + len.into(),
        }
    }
}

/// An iterator over a contiguous range of `NodeRef`s.
#[derive(Clone, Debug)]
pub struct NodeRefRange {
    current: u32,
    end: u32,
}

impl Iterator for NodeRefRange {
    type Item = NodeRef;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let node = NodeRef::new(self.current).expect("NodeRef overflow in range");
            self.current += 1;
            Some(node)
        } else {
            None
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.end - self.current) as usize;
        (len, Some(len))
    }
}

impl ExactSizeIterator for NodeRefRange {}

impl Ast {
    /// Get the resolved type for a node (reads from attached semantic_info)
    pub fn get_resolved_type(&self, node_ref: NodeRef) -> Option<QualType> {
        self.semantic_info.as_ref()?.types[node_ref.index()]
    }

    /// Get the value category for a node (reads from attached semantic_info)
    pub fn get_value_category(&self, node_ref: NodeRef) -> Option<ValueCategory> {
        self.semantic_info
            .as_ref()?
            .value_categories
            .get(node_ref.index())
            .copied()
    }
}
