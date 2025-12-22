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
/// Contains all AST nodes, types, symbol entries, and initializers in contiguous vectors.
pub struct Ast {
    pub nodes: Vec<Node>,
    pub types: Vec<Type>,
    pub symbol_entries: Vec<SymbolEntry>,
    pub initializers: Vec<Initializer>,
    pub root: Option<NodeRef>,
}

/// Node reference type for referencing child nodes.
pub type NodeRef = NonZeroU32;
pub type TypeRef = NonZeroU32;
pub type SymbolEntryRef = NonZeroU32;
pub type InitializerRef = NonZeroU32;

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
            initializers: Vec::new(),
            root: None,
        }
    }

    /// Get the root node of the AST
    pub fn get_root_node(&self) -> Option<&Node> {
        self.root.map(|node_ref| self.get_node(node_ref))
    }

    /// Set the root node of the AST
    pub fn set_root_node(&mut self, node_ref: NodeRef) {
        self.root = Some(node_ref);
    }

    /// Replace a node in the AST and update parent references
    /// Returns the reference to the new node
    pub fn replace_node(&mut self, old_node_ref: NodeRef, new_node: Node) -> NodeRef {
        // First, push the new node to get its reference
        let new_node_ref = self.push_node(new_node);

        // Update parent references to point to the new node
        self.update_parent_references(old_node_ref, new_node_ref);

        new_node_ref
    }

    /// Update all parent nodes that reference the old node to reference the new node
    fn update_parent_references(&mut self, old_node_ref: NodeRef, new_node_ref: NodeRef) {
        // We need to traverse the AST to find parent nodes that reference the old node
        // This is a simplified approach - in a production compiler, we'd maintain parent pointers

        // If the old node is the root, update the root
        if let Some(root_ref) = self.root
            && root_ref == old_node_ref
        {
            self.root = Some(new_node_ref);
            return;
        }

        // Traverse the AST to find and update parent references
        // This is a breadth-first search approach
        let root_ref = self
            .root
            .expect("AST should have a root node for parent reference updates");
        let mut stack = vec![root_ref];

        while let Some(current_node_ref) = stack.pop() {
            let current_node = self.get_node(current_node_ref);

            // Check if this node contains references to the old node and update them
            let updated_node = self.update_node_references_in_node(current_node, old_node_ref, new_node_ref);

            // If the node was updated, replace it in the AST
            if let Some(updated_node) = updated_node {
                // We can't use replace_node here to avoid infinite recursion
                // Instead, we'll directly replace the node data
                let index = (current_node_ref.get() - 1) as usize;
                self.nodes[index] = updated_node;
            }

            // Continue traversal with children
            let children = self.get_children_for_traversal(current_node_ref);
            stack.extend(children);
        }
    }

    /// Helper function to get children for traversal
    fn get_children_for_traversal(&self, node_ref: NodeRef) -> Vec<NodeRef> {
        let node = self.get_node(node_ref);

        match &node.kind {
            NodeKind::TranslationUnit(nodes) => nodes.clone(),
            NodeKind::FunctionDef(func_def) => vec![func_def.body],
            NodeKind::CompoundStatement(nodes) => nodes.clone(),
            NodeKind::If(if_stmt) => {
                let mut children = vec![if_stmt.condition, if_stmt.then_branch];
                if let Some(else_branch) = if_stmt.else_branch {
                    children.push(else_branch);
                }
                children
            }
            NodeKind::While(while_stmt) => vec![while_stmt.condition, while_stmt.body],
            NodeKind::DoWhile(body, condition) => vec![*body, *condition],
            NodeKind::For(for_stmt) => {
                let mut children = vec![for_stmt.body];
                if let Some(init) = for_stmt.init {
                    children.insert(0, init);
                }
                if let Some(condition) = for_stmt.condition {
                    children.insert(1, condition);
                }
                if let Some(increment) = for_stmt.increment {
                    children.push(increment);
                }
                children
            }
            NodeKind::Switch(condition, body) => vec![*condition, *body],
            NodeKind::Case(expr, stmt) => vec![*expr, *stmt],
            NodeKind::CaseRange(start_expr, end_expr, stmt) => vec![*start_expr, *end_expr, *stmt],
            NodeKind::Default(stmt) => vec![*stmt],
            NodeKind::Label(_, stmt) => vec![*stmt],
            NodeKind::BinaryOp(_, left, right) => vec![*left, *right],
            NodeKind::Assignment(_, lhs, rhs) => vec![*lhs, *rhs],
            NodeKind::FunctionCall(func, args) => {
                let mut children = vec![*func];
                children.extend(args);
                children
            }
            NodeKind::Return(expr) => {
                if let Some(expr_ref) = expr {
                    vec![*expr_ref]
                } else {
                    Vec::new()
                }
            }
            NodeKind::UnaryOp(_, expr) => vec![*expr],
            NodeKind::Cast(_, expr) => vec![*expr],
            NodeKind::SizeOfExpr(expr) => vec![*expr],
            NodeKind::TernaryOp(cond, then_expr, else_expr) => vec![*cond, *then_expr, *else_expr],
            _ => Vec::new(),
        }
    }

    /// Update references within a node from old_ref to new_ref
    /// Returns Some(updated_node) if the node was modified, None otherwise
    fn update_node_references_in_node(&self, node: &Node, old_ref: NodeRef, new_ref: NodeRef) -> Option<Node> {
        match &node.kind {
            NodeKind::TranslationUnit(nodes) => {
                let updated_nodes: Vec<NodeRef> = nodes
                    .iter()
                    .map(|&node_ref| if node_ref == old_ref { new_ref } else { node_ref })
                    .collect();

                if updated_nodes != *nodes {
                    let mut new_node = node.clone();
                    if let NodeKind::TranslationUnit(ref_mut_nodes) = &mut new_node.kind {
                        *ref_mut_nodes = updated_nodes;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::FunctionDef(func_def) => {
                if func_def.body == old_ref {
                    let mut new_node = node.clone();
                    if let NodeKind::FunctionDef(ref_mut_func_def) = &mut new_node.kind {
                        ref_mut_func_def.body = new_ref;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::CompoundStatement(nodes) => {
                let updated_nodes: Vec<NodeRef> = nodes
                    .iter()
                    .map(|&node_ref| if node_ref == old_ref { new_ref } else { node_ref })
                    .collect();

                if updated_nodes != *nodes {
                    let mut new_node = node.clone();
                    if let NodeKind::CompoundStatement(ref_mut_nodes) = &mut new_node.kind {
                        *ref_mut_nodes = updated_nodes;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::If(if_stmt) => {
                let mut needs_update = false;
                let mut new_if_stmt = *if_stmt;

                if new_if_stmt.condition == old_ref {
                    new_if_stmt.condition = new_ref;
                    needs_update = true;
                }
                if new_if_stmt.then_branch == old_ref {
                    new_if_stmt.then_branch = new_ref;
                    needs_update = true;
                }
                if let Some(else_branch) = new_if_stmt.else_branch
                    && else_branch == old_ref
                {
                    new_if_stmt.else_branch = Some(new_ref);
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::If(ref_mut_if_stmt) = &mut new_node.kind {
                        *ref_mut_if_stmt = new_if_stmt;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::While(while_stmt) => {
                let mut needs_update = false;
                let mut new_while_stmt = *while_stmt;

                if new_while_stmt.condition == old_ref {
                    new_while_stmt.condition = new_ref;
                    needs_update = true;
                }
                if new_while_stmt.body == old_ref {
                    new_while_stmt.body = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::While(ref_mut_while_stmt) = &mut new_node.kind {
                        *ref_mut_while_stmt = new_while_stmt;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::DoWhile(body, condition) => {
                let mut needs_update = false;
                let mut new_body = *body;
                let mut new_condition = *condition;

                if new_body == old_ref {
                    new_body = new_ref;
                    needs_update = true;
                }
                if new_condition == old_ref {
                    new_condition = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::DoWhile(ref_mut_body, ref_mut_condition) = &mut new_node.kind {
                        *ref_mut_body = new_body;
                        *ref_mut_condition = new_condition;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::For(for_stmt) => {
                let mut needs_update = false;
                let mut new_for_stmt = *for_stmt;

                if let Some(init) = new_for_stmt.init
                    && init == old_ref
                {
                    new_for_stmt.init = Some(new_ref);
                    needs_update = true;
                }
                if let Some(condition) = new_for_stmt.condition
                    && condition == old_ref
                {
                    new_for_stmt.condition = Some(new_ref);
                    needs_update = true;
                }
                if let Some(increment) = new_for_stmt.increment
                    && increment == old_ref
                {
                    new_for_stmt.increment = Some(new_ref);
                    needs_update = true;
                }
                if new_for_stmt.body == old_ref {
                    new_for_stmt.body = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::For(ref_mut_for_stmt) = &mut new_node.kind {
                        *ref_mut_for_stmt = new_for_stmt;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Switch(condition, body) => {
                let mut needs_update = false;
                let mut new_condition = *condition;
                let mut new_body = *body;

                if new_condition == old_ref {
                    new_condition = new_ref;
                    needs_update = true;
                }
                if new_body == old_ref {
                    new_body = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::Switch(ref_mut_condition, ref_mut_body) = &mut new_node.kind {
                        *ref_mut_condition = new_condition;
                        *ref_mut_body = new_body;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Case(expr, stmt) => {
                let mut needs_update = false;
                let mut new_expr = *expr;
                let mut new_stmt = *stmt;

                if new_expr == old_ref {
                    new_expr = new_ref;
                    needs_update = true;
                }
                if new_stmt == old_ref {
                    new_stmt = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::Case(ref_mut_expr, ref_mut_stmt) = &mut new_node.kind {
                        *ref_mut_expr = new_expr;
                        *ref_mut_stmt = new_stmt;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::CaseRange(start_expr, end_expr, stmt) => {
                let mut needs_update = false;
                let mut new_start_expr = *start_expr;
                let mut new_end_expr = *end_expr;
                let mut new_stmt = *stmt;

                if new_start_expr == old_ref {
                    new_start_expr = new_ref;
                    needs_update = true;
                }
                if new_end_expr == old_ref {
                    new_end_expr = new_ref;
                    needs_update = true;
                }
                if new_stmt == old_ref {
                    new_stmt = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::CaseRange(ref_mut_start_expr, ref_mut_end_expr, ref_mut_stmt) = &mut new_node.kind
                    {
                        *ref_mut_start_expr = new_start_expr;
                        *ref_mut_end_expr = new_end_expr;
                        *ref_mut_stmt = new_stmt;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Default(stmt) => {
                if *stmt == old_ref {
                    let mut new_node = node.clone();
                    if let NodeKind::Default(ref_mut_stmt) = &mut new_node.kind {
                        *ref_mut_stmt = new_ref;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Label(_, stmt) => {
                if *stmt == old_ref {
                    let mut new_node = node.clone();
                    if let NodeKind::Label(_, ref_mut_stmt) = &mut new_node.kind {
                        *ref_mut_stmt = new_ref;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::BinaryOp(_op, left, right) => {
                let mut needs_update = false;
                let mut new_left = *left;
                let mut new_right = *right;

                if new_left == old_ref {
                    new_left = new_ref;
                    needs_update = true;
                }
                if new_right == old_ref {
                    new_right = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::BinaryOp(_, ref_mut_left, ref_mut_right) = &mut new_node.kind {
                        *ref_mut_left = new_left;
                        *ref_mut_right = new_right;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Assignment(_op, lhs, rhs) => {
                let mut needs_update = false;
                let mut new_lhs = *lhs;
                let mut new_rhs = *rhs;

                if new_lhs == old_ref {
                    new_lhs = new_ref;
                    needs_update = true;
                }
                if new_rhs == old_ref {
                    new_rhs = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::Assignment(_, ref_mut_lhs, ref_mut_rhs) = &mut new_node.kind {
                        *ref_mut_lhs = new_lhs;
                        *ref_mut_rhs = new_rhs;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::FunctionCall(func, args) => {
                let mut needs_update = false;
                let mut new_func = *func;
                let mut new_args = args.clone();

                if new_func == old_ref {
                    new_func = new_ref;
                    needs_update = true;
                }

                // Check and update arguments
                for arg in &mut new_args {
                    if *arg == old_ref {
                        *arg = new_ref;
                        needs_update = true;
                    }
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::FunctionCall(ref_mut_func, ref_mut_args) = &mut new_node.kind {
                        *ref_mut_func = new_func;
                        *ref_mut_args = new_args;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Return(expr) => {
                if let Some(expr_ref) = expr {
                    if *expr_ref == old_ref {
                        let mut new_node = node.clone();
                        if let NodeKind::Return(ref_mut_expr) = &mut new_node.kind {
                            *ref_mut_expr = Some(new_ref);
                        }
                        Some(new_node)
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            NodeKind::UnaryOp(_op, expr) => {
                if *expr == old_ref {
                    let mut new_node = node.clone();
                    if let NodeKind::UnaryOp(_, ref_mut_expr) = &mut new_node.kind {
                        *ref_mut_expr = new_ref;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::Cast(_ty, expr) => {
                if *expr == old_ref {
                    let mut new_node = node.clone();
                    if let NodeKind::Cast(_, ref_mut_expr) = &mut new_node.kind {
                        *ref_mut_expr = new_ref;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::SizeOfExpr(expr) => {
                if *expr == old_ref {
                    let mut new_node = node.clone();
                    if let NodeKind::SizeOfExpr(ref_mut_expr) = &mut new_node.kind {
                        *ref_mut_expr = new_ref;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            NodeKind::TernaryOp(cond, then_expr, else_expr) => {
                let mut needs_update = false;
                let mut new_cond = *cond;
                let mut new_then_expr = *then_expr;
                let mut new_else_expr = *else_expr;

                if new_cond == old_ref {
                    new_cond = new_ref;
                    needs_update = true;
                }
                if new_then_expr == old_ref {
                    new_then_expr = new_ref;
                    needs_update = true;
                }
                if new_else_expr == old_ref {
                    new_else_expr = new_ref;
                    needs_update = true;
                }

                if needs_update {
                    let mut new_node = node.clone();
                    if let NodeKind::TernaryOp(ref_mut_cond, ref_mut_then_expr, ref_mut_else_expr) = &mut new_node.kind
                    {
                        *ref_mut_cond = new_cond;
                        *ref_mut_then_expr = new_then_expr;
                        *ref_mut_else_expr = new_else_expr;
                    }
                    Some(new_node)
                } else {
                    None
                }
            }
            _ => None, // No children to update for other node types
        }
    }

    /// Add a node to the AST and return its reference
    pub fn push_node(&mut self, node: Node) -> NodeRef {
        let index = self.nodes.len() as u32 + 1; // Start from 1 for NonZeroU32
        self.nodes.push(node);
        NodeRef::new(index).expect("NodeRef overflow")
    }

    /// Get a node by its reference
    pub fn get_node(&self, index: NodeRef) -> &Node {
        &self.nodes[(index.get() - 1) as usize]
    }

    /// Add a type to the AST and return its reference
    pub fn push_type(&mut self, ty: Type) -> TypeRef {
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

    /// Add a symbol entry to the AST and return its reference
    pub fn push_symbol_entry(&mut self, entry: SymbolEntry) -> SymbolEntryRef {
        let index = self.symbol_entries.len() as u32 + 1;
        self.symbol_entries.push(entry);
        SymbolEntryRef::new(index).expect("SymbolEntryRef overflow")
    }

    /// Get a symbol entry by its reference
    pub fn get_symbol_entry(&self, index: SymbolEntryRef) -> &SymbolEntry {
        &self.symbol_entries[(index.get() - 1) as usize]
    }

    /// Add an initializer to the AST and return its reference
    pub fn push_initializer(&mut self, init: Initializer) -> InitializerRef {
        let index = self.initializers.len() as u32 + 1;
        self.initializers.push(init);
        InitializerRef::new(index).expect("InitializerRef overflow")
    }

    /// Get an initializer by its reference
    pub fn get_initializer(&self, index: InitializerRef) -> &Initializer {
        &self.initializers[(index.get() - 1) as usize]
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

/// Represents a resolved symbol entry from the symbol table.
/// This structure is typically populated during the semantic analysis phase.
/// Symbol entries are stored in a separate Vec<SymbolEntry> with SymbolEntryIndex references.
#[derive(Debug)]
pub struct SymbolEntry {
    pub name: Symbol,
    pub kind: SymbolKind, // e.g., Variable, Function, Typedef
    pub type_info: TypeRef,
    pub storage_class: Option<StorageClass>,
    pub scope_id: u32, // Reference to the scope where it's defined
    pub definition_span: SourceSpan,
    pub is_defined: bool,
    pub is_referenced: bool,
    pub is_completed: bool,
    // Add other relevant symbol information here (e.g., value for constants, linkage)
}

/// Defines the kind of symbol.
#[derive(Debug)]
pub enum SymbolKind {
    Variable {
        is_global: bool,
        is_static: bool,
        is_extern: bool,
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
    pub location: SourceSpan,
}

/// Enum constant information
#[derive(Debug, Clone)]
pub struct EnumConstant {
    pub name: Symbol,
    pub value: i64, // Resolved value
    pub location: SourceSpan,
}
