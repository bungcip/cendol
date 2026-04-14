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
pub type StringId = NameId;

use crate::semantic::{QualType, ScopeId, SemanticInfo, SymbolRef, ValueCategory};
pub use crate::source_manager::{SourceId, SourceSpan};

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
    pub(crate) kinds: Vec<NodeKind>,
    pub(crate) spans: Vec<SourceSpan>,
    pub literals: literal::LiteralTable,
    pub semantic_info: Option<SemanticInfo>, // Populated after type resolution
}

impl Ast {
    /// Create a new empty AST
    pub(crate) fn new() -> Self {
        Ast::default()
    }

    /// Add a node to the AST and return its reference
    pub(crate) fn push_node(&mut self, kind: NodeKind, span: SourceSpan) -> NodeRef {
        let node = self.next_node_ref();
        self.kinds.push(kind);
        self.spans.push(span);
        node
    }

    /// get the reference of the next node to be pushed
    #[inline]
    pub(crate) fn next_node_ref(&self) -> NodeRef {
        let index = self.kinds.len() as u32 + 1; // Start from 1 for NonZeroU32
        NodeRef::new(index).expect("NodeRef overflow")
    }

    /// Add a dummy node to the AST and return its reference
    #[inline]
    pub(crate) fn push_dummy(&mut self, span: SourceSpan) -> NodeRef {
        self.push_node(NodeKind::Dummy, span)
    }

    /// Get node kind by reference
    #[inline]
    pub(crate) fn get_kind(&self, node: NodeRef) -> &NodeKind {
        &self.kinds[node.index()]
    }

    /// Get node span by reference
    #[inline]
    pub(crate) fn get_span(&self, node: NodeRef) -> SourceSpan {
        self.spans[node.index()]
    }

    /// get root node ref
    #[inline]
    pub(crate) fn get_root(&self) -> NodeRef {
        NodeRef::ROOT
    }

    pub(crate) fn scope_of(&self, node: NodeRef) -> ScopeId {
        match &self.kinds[node.index()] {
            NodeKind::TranslationUnit(data) => data.scope_id,
            NodeKind::Function(data) => {
                let body_node = data.child_start.add_offset(data.param_len);
                self.scope_of(body_node) // delegate to CompoundStmt body (last child)
            }
            NodeKind::FunctionDecl(data) => data.scope_id,
            NodeKind::CompoundStmt(data) => data.scope_id,
            NodeKind::For(data) => data.scope_id,
            _ => unreachable!("ICE: Node {:?} does not have a scope", self.get_kind(node)),
        }
    }

    /// attach semantic info side table for AST (populated after type resolution)
    #[inline]
    pub(crate) fn attach_semantic_info(&mut self, semantic_info: SemanticInfo) {
        self.semantic_info = Some(semantic_info);
    }

    /// set the kind of an existing node
    #[inline]
    pub(crate) fn set_kind(&mut self, node: NodeRef, kind: NodeKind) {
        self.kinds[node.index()] = kind;
    }

    /// set the span of an existing node
    #[inline]
    pub(crate) fn set_span(&mut self, node: NodeRef, span: SourceSpan) {
        self.spans[node.index()] = span;
    }
}

/// Node reference type for referencing child nodes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub struct NodeRef(NonZeroU32);

impl NodeRef {
    pub const ROOT: NodeRef = NodeRef(NonZeroU32::new(1).unwrap());

    #[inline]
    pub(crate) fn new(value: u32) -> Option<Self> {
        NonZeroU32::new(value).map(Self)
    }

    #[inline]
    pub(crate) fn raw(self) -> u32 {
        self.0.get()
    }

    #[inline]
    pub(crate) fn add_offset(self, offset: u16) -> Self {
        NodeRef::new(self.raw() + offset as u32).expect("NodeRef overflow")
    }

    #[inline]
    pub(crate) fn index(self) -> usize {
        (self.raw() - 1) as usize
    }

    /// Create an iterator over a range of consecutive NodeRefs, starting from `self`.
    #[inline]
    pub(crate) fn range(self, len: impl Into<u32>) -> NodeRefRange {
        NodeRefRange {
            current: self.raw(),
            end: self.raw() + len.into(),
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
    pub(crate) fn get_resolved_type(&self, node: NodeRef) -> Option<QualType> {
        self.semantic_info.as_ref()?.types[node.index()]
    }

    /// Get resolved type for a node. panic if not resolved
    pub(crate) fn qual_type_of(&self, node: NodeRef) -> QualType {
        self.get_resolved_type(node).unwrap()
    }

    /// Get the value category for a node (reads from attached semantic_info)
    pub(crate) fn get_value_category(&self, node: NodeRef) -> Option<ValueCategory> {
        self.semantic_info.as_ref()?.value_categories.get(node.index()).copied()
    }

    /// get selected expression of generic selection
    pub(crate) fn get_generic_selection(&self, node: NodeRef) -> NodeRef {
        self.semantic_info
            .as_ref()
            .unwrap()
            .generic_selections
            .get(&node.index())
            .copied()
            .expect("Generic selection failed (should be caught by Analyzer)")
    }

    /// get selected branch of choose expression
    pub(crate) fn get_choose_expression(&self, node: NodeRef) -> NodeRef {
        self.semantic_info
            .as_ref()
            .unwrap()
            .choose_expressions
            .get(&node.index())
            .copied()
            .expect("Choose expression failed (should be caught by Analyzer)")
    }
}
