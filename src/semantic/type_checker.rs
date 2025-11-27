//! Type checking visitor implementation.
//!
//! This module provides the TypeChecker visitor that performs type checking
//! and type inference on the AST. It validates type compatibility, performs
//! implicit conversions, and ensures type safety according to C11 semantics.

use crate::ast::*;
use crate::diagnostic::DiagnosticEngine;
use crate::semantic::symbol_table::{ScopeId, SymbolTable};
use crate::semantic::utils::*;
use crate::semantic::visitor::{SemanticVisitor, visit_node};

/// Context for type checking
pub struct TypeCheckContext<'a> {
    pub symbol_table: &'a mut SymbolTable,
    pub diag: &'a mut DiagnosticEngine,
    pub current_scope: ScopeId,
}

/// Type checker that implements the visitor pattern for type checking.
/// This visitor traverses the AST and performs type checking operations.
pub struct TypeChecker;

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeChecker {
    /// Create a new type checker
    pub fn new() -> Self {
        TypeChecker
    }

    /// Perform type checking on the AST starting from the given node
    pub fn check_types<'ast>(
        &mut self,
        ast: &'ast Ast,
        symbol_table: &'ast mut SymbolTable,
        diag: &'ast mut DiagnosticEngine,
        start_node: NodeRef,
    ) {
        let mut context = TypeCheckContext {
            symbol_table,
            diag,
            current_scope: ScopeId::GLOBAL,
        };

        self.walk_ast(ast, start_node, &mut context);
    }

    /// Walk the AST starting from the given node
    fn walk_ast<'a>(&mut self, ast: &'a Ast, node_ref: NodeRef, context: &mut TypeCheckContext<'a>) {
        // Visit the current node
        visit_node(self, ast, node_ref, context);

        // Recursively visit children based on node type
        let node = ast.get_node(node_ref);
        self.visit_children(ast, node, context);
    }

    /// Visit child nodes of the given node
    fn visit_children<'a>(&mut self, ast: &'a Ast, node: &Node, context: &mut TypeCheckContext<'a>) {
        use crate::semantic::visitor::get_child_nodes;

        match &node.kind {
            NodeKind::FunctionDef(func_def) => {
                // For function definitions, we need to check in the function scope
                let func_name = extract_function_info(&func_def.declarator).0.unwrap_or_else(|| Symbol::new("<anonymous>"));
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
            _ => {
                for child in get_child_nodes(node) {
                    self.walk_ast(ast, child, context);
                }
            }
        }
    }
}

impl<'ast> SemanticVisitor<'ast> for TypeChecker {
    type Context = TypeCheckContext<'ast>;

    // Type checking implementations would go here
    // For now, this is a placeholder that can be extended with actual type checking logic

    fn visit_binary_op(&mut self, op: BinaryOp, left: NodeRef, right: NodeRef, span: SourceSpan, context: &mut Self::Context) {
        // Placeholder: In a full implementation, this would check type compatibility
        // for binary operations according to C11 rules
        let _ = (op, left, right, span, context);
    }

    fn visit_assignment(&mut self, op: BinaryOp, lhs: NodeRef, rhs: NodeRef, span: SourceSpan, context: &mut Self::Context) {
        // Placeholder: Check assignment compatibility
        let _ = (op, lhs, rhs, span, context);
    }

    fn visit_function_call(&mut self, func: NodeRef, args: &[NodeRef], span: SourceSpan, context: &mut Self::Context) {
        // Placeholder: Check function call arguments against function signature
        let _ = (func, args, span, context);
    }

    fn visit_cast(&mut self, target_type: TypeRef, expr: NodeRef, span: SourceSpan, context: &mut Self::Context) {
        // Placeholder: Validate cast legality
        let _ = (target_type, expr, span, context);
    }

    fn visit_return(&mut self, expr: Option<NodeRef>, span: SourceSpan, context: &mut Self::Context) {
        // Placeholder: Check return type compatibility with function return type
        let _ = (expr, span, context);
    }

    // Other type checking methods can be added here as needed
}

/// Extract function name and parameters from a declarator
fn extract_function_info(declarator: &Declarator) -> (Option<Symbol>, Vec<FunctionParameter>) {
    // Find the function declarator that has the identifier as its direct base
    let (name, params) = find_function_with_name(declarator);
    if let Some((func_decl, params)) = name.zip(params) {
        let func_params: Vec<FunctionParameter> = params
            .iter()
            .filter_map(|param| {
                if let Some(decl) = &param.declarator {
                    let param_name = extract_identifier(decl);
                    param_name.map(|name| FunctionParameter {
                        param_type: TypeRef::new(1).unwrap(), // Placeholder
                        name: Some(name),
                    })
                } else {
                    None
                }
            })
            .collect();
        (Some(func_decl), func_params)
    } else {
        (None, Vec::new())
    }
}

fn find_function_with_name(declarator: &Declarator) -> (Option<Symbol>, Option<&Vec<ParamData>>) {
    match declarator {
        Declarator::Function(base, params) => {
            if let Declarator::Identifier(name, _, _) = base.as_ref() {
                (Some(*name), Some(params))
            } else {
                find_function_with_name(base)
            }
        }
        Declarator::Pointer(_, Some(base)) => find_function_with_name(base),
        Declarator::Array(base, _) => find_function_with_name(base),
        _ => (None, None)
    }
}

fn extract_identifier(declarator: &Declarator) -> Option<Symbol> {
    match declarator {
        Declarator::Identifier(name, _, _) => Some(*name),
        Declarator::Pointer(_, Some(base)) => extract_identifier(base),
        Declarator::Array(base, _) => extract_identifier(base),
        Declarator::Function(base, _) => extract_identifier(base),
        Declarator::Abstract => None,
        _ => None
    }
}