//! Name resolution visitor implementation.
// //!
// //! This module provides the NameResolver visitor that traverses the AST
// //! and resolves identifier references to their corresponding symbol entries
// //! in the symbol table. It handles scope lookup and marks symbols as referenced.

use std::cell::Cell;

use log::debug;

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::symbol_table::{ScopeId, SymbolTable};
use crate::semantic::utils::extract_function_info;
use crate::semantic::visitor::{SemanticVisitor, visit_node};

/// Context for name resolution
pub struct NameResolutionContext<'a> {
    pub symbol_table: &'a mut SymbolTable,
    pub diag: &'a mut DiagnosticEngine,
    pub current_scope: ScopeId,
}

/// Name resolver that implements the visitor pattern for name resolution.
/// This visitor traverses the AST and resolves identifier references to symbols.
pub struct NameResolver;

impl Default for NameResolver {
    fn default() -> Self {
        Self::new()
    }
}

impl NameResolver {
    /// Create a new name resolver
    pub fn new() -> Self {
        NameResolver
    }

    /// Resolve names in the AST starting from the given node
    pub fn resolve_names<'ast>(
        &mut self,
        ast: &'ast Ast,
        symbol_table: &'ast mut SymbolTable,
        diag: &'ast mut DiagnosticEngine,
        start_node: NodeRef,
    ) {
        let mut context = NameResolutionContext {
            symbol_table,
            diag,
            current_scope: ScopeId::GLOBAL,
        };

        self.walk_ast(ast, start_node, &mut context);
    }

    /// Walk the AST starting from the given node
    fn walk_ast<'a>(&mut self, ast: &'a Ast, node_ref: NodeRef, context: &mut NameResolutionContext<'a>) {
        // Visit the current node
        visit_node(self, ast, node_ref, context);

        // Recursively visit children based on node type
        let node = ast.get_node(node_ref);
        self.visit_children(ast, node, context);
    }

    /// Visit child nodes of the given node
    fn visit_children<'a>(&mut self, ast: &'a Ast, node: &Node, context: &mut NameResolutionContext<'a>) {
        match &node.kind {
            NodeKind::TranslationUnit(nodes) => {
                for &child in nodes {
                    self.walk_ast(ast, child, context);
                }
            }
            NodeKind::FunctionDef(func_def) => {
                // For function definitions, we need to resolve in the function scope
                let func_name = extract_function_info(&func_def.declarator)
                    .0
                    .unwrap_or_else(|| Symbol::new("<anonymous>"));
                if let Some((symbol_ref, _)) = context.symbol_table.lookup_symbol(func_name) {
                    let symbol_entry = context.symbol_table.get_symbol_entry(symbol_ref);
                    let func_scope_id = ScopeId::new(symbol_entry.scope_id).unwrap();
                    let old_scope = context.current_scope;
                    context.current_scope = func_scope_id;
                    self.walk_ast(ast, func_def.body, context);
                    context.current_scope = old_scope;
                } else {
                    // Fallback: process with current scope
                    self.walk_ast(ast, func_def.body, context);
                }
            }
            NodeKind::CompoundStatement(nodes) => {
                // For compound statements, we might need to handle scope changes
                // For now, just visit all children
                for &child in nodes {
                    self.walk_ast(ast, child, context);
                }
            }
            NodeKind::If(if_stmt) => {
                self.walk_ast(ast, if_stmt.condition, context);
                self.walk_ast(ast, if_stmt.then_branch, context);
                if let Some(else_branch) = if_stmt.else_branch {
                    self.walk_ast(ast, else_branch, context);
                }
            }
            NodeKind::While(while_stmt) => {
                self.walk_ast(ast, while_stmt.condition, context);
                self.walk_ast(ast, while_stmt.body, context);
            }
            NodeKind::DoWhile(body, condition) => {
                self.walk_ast(ast, *body, context);
                self.walk_ast(ast, *condition, context);
            }
            NodeKind::For(for_stmt) => {
                if let Some(init) = for_stmt.init {
                    self.walk_ast(ast, init, context);
                }
                if let Some(condition) = for_stmt.condition {
                    self.walk_ast(ast, condition, context);
                }
                if let Some(increment) = for_stmt.increment {
                    self.walk_ast(ast, increment, context);
                }
                self.walk_ast(ast, for_stmt.body, context);
            }
            NodeKind::Switch(condition, body) => {
                self.walk_ast(ast, *condition, context);
                self.walk_ast(ast, *body, context);
            }
            NodeKind::Case(expr, stmt) => {
                self.walk_ast(ast, *expr, context);
                self.walk_ast(ast, *stmt, context);
            }
            NodeKind::CaseRange(start_expr, end_expr, stmt) => {
                self.walk_ast(ast, *start_expr, context);
                self.walk_ast(ast, *end_expr, context);
                self.walk_ast(ast, *stmt, context);
            }
            NodeKind::Default(stmt) => {
                self.walk_ast(ast, *stmt, context);
            }
            NodeKind::Label(_, stmt) => {
                self.walk_ast(ast, *stmt, context);
            }
            NodeKind::BinaryOp(_, left, right) => {
                self.walk_ast(ast, *left, context);
                self.walk_ast(ast, *right, context);
            }
            NodeKind::Assignment(_, lhs, rhs) => {
                self.walk_ast(ast, *lhs, context);
                self.walk_ast(ast, *rhs, context);
            }
            NodeKind::FunctionCall(func, args) => {
                self.walk_ast(ast, *func, context);
                for &arg in args {
                    self.walk_ast(ast, arg, context);
                }
            }
            NodeKind::Return(Some(expr_ref)) => {
                self.walk_ast(ast, *expr_ref, context);
            }
            NodeKind::UnaryOp(_, expr) => {
                self.walk_ast(ast, *expr, context);
            }
            NodeKind::Cast(_, expr) => {
                self.walk_ast(ast, *expr, context);
            }
            NodeKind::SizeOfExpr(expr) => {
                self.walk_ast(ast, *expr, context);
            }
            NodeKind::TernaryOp(cond, then_expr, else_expr) => {
                self.walk_ast(ast, *cond, context);
                self.walk_ast(ast, *then_expr, context);
                self.walk_ast(ast, *else_expr, context);
            }
            NodeKind::PostIncrement(expr) | NodeKind::PostDecrement(expr) => {
                self.walk_ast(ast, *expr, context);
            }
            NodeKind::MemberAccess(object, _, _) => {
                self.walk_ast(ast, *object, context);
            }
            NodeKind::IndexAccess(array, index) => {
                self.walk_ast(ast, *array, context);
                self.walk_ast(ast, *index, context);
            }
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                self.walk_ast(ast, *expr_ref, context);
            }
            NodeKind::EnumConstant(_, Some(expr_ref)) => {
                self.walk_ast(ast, *expr_ref, context);
            }
            NodeKind::StaticAssert(condition, _) => {
                self.walk_ast(ast, *condition, context);
            }
            // Leaf nodes or nodes that don't need child traversal
            _ => {}
        }
    }
}

impl<'ast> SemanticVisitor<'ast> for NameResolver {
    type Context = NameResolutionContext<'ast>;

    fn visit_ident(
        &mut self,
        name: Symbol,
        resolved_symbol: &Cell<Option<SymbolEntryRef>>,
        span: SourceSpan,
        context: &mut Self::Context,
    ) {
        debug!(
            "Resolving identifier: {} in scope {}",
            name.as_str(),
            context.current_scope.get()
        );

        if let Some((symbol_ref, scope_id)) = context.symbol_table.lookup_symbol_from(name, context.current_scope) {
            debug!("Found symbol {} in scope {}", name.as_str(), scope_id.get());
            resolved_symbol.set(Some(symbol_ref));

            // Mark symbol as referenced
            let symbol_entry = context.symbol_table.get_symbol_entry_mut(symbol_ref);
            symbol_entry.is_referenced = true;
        } else {
            debug!(
                "Undeclared identifier: {} (expected scope: {}), checking symbol table contents",
                name.as_str(),
                context.current_scope.get()
            );
            // Debug: list all symbols in current scope and parent scopes
            let mut debug_scope = context.current_scope;
            while let Some(scope) = context.symbol_table.scopes.get(debug_scope.get() as usize - 1) {
                debug!(
                    "Scope {} (kind: {:?}) has {} symbols:",
                    debug_scope.get(),
                    scope.kind,
                    scope.symbols.len()
                );
                for (sym_name, sym_ref) in &scope.symbols {
                    let entry = context.symbol_table.get_symbol_entry(*sym_ref);
                    debug!("  Symbol: {} -> {:?}", sym_name.as_str(), entry.kind);
                }
                if let Some(parent) = scope.parent {
                    debug_scope = parent;
                } else {
                    break;
                }
            }
            context
                .diag
                .report_error(SemanticError::UndeclaredIdentifier { name, location: span });
        }
    }

    // Override visit_compound_statement to handle scope changes
    fn visit_compound_statement(&mut self, _statements: &[NodeRef], _span: SourceSpan, _context: &mut Self::Context) {
        // Scope handling is done in visit_children to maintain proper traversal order
    }

    // Override visit_function_def to handle scope changes
    fn visit_function_def(&mut self, _func_def: &FunctionDefData, _span: SourceSpan, _context: &mut Self::Context) {
        // Scope handling is done in visit_children to maintain proper traversal order
    }
}
