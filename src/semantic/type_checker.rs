//! Type checking visitor implementation.
//!
//! This module provides the TypeChecker visitor that performs type checking
//! and type inference on the AST. It validates type compatibility, performs
//! implicit conversions, and ensures type safety according to C11 semantics.

use thin_vec::ThinVec;

use std::cell::Cell;

use crate::ast::*;
use crate::diagnostic::DiagnosticEngine;
use crate::semantic::symbol_table::{ScopeId, SymbolTable};
use crate::semantic::visitor::{SemanticVisitor, visit_node};

/// Context for type checking
pub struct TypeCheckContext<'a> {
    pub ast: &'a Ast,
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
            ast,
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
            NodeKind::Declaration(decl) => {
                // For declarations, we need to traverse into initializers
                for init_declarator in &decl.init_declarators {
                    if let Some(initializer) = &init_declarator.initializer {
                        self.walk_initializer(ast, initializer, context);
                    }
                }
                // Also traverse regular children
                for child in get_child_nodes(node) {
                    self.walk_ast(ast, child, context);
                }
            }
            _ => {
                for child in get_child_nodes(node) {
                    self.walk_ast(ast, child, context);
                }
            }
        }
    }

    /// Walk initializer recursively
    fn walk_initializer<'a>(&mut self, ast: &'a Ast, initializer: &Initializer, context: &mut TypeCheckContext<'a>) {
        match initializer {
            Initializer::Expression(expr_node) => {
                self.walk_ast(ast, *expr_node, context);
            }
            Initializer::List(designated_inits) => {
                for designated in designated_inits {
                    self.walk_initializer(ast, &designated.initializer, context);
                    // Also handle designators that might contain expressions
                    for designator in &designated.designation {
                        if let Designator::ArrayIndex(index_expr) = designator {
                            self.walk_ast(ast, *index_expr, context);
                        }
                    }
                }
            }
        }
    }
}

impl<'ast> SemanticVisitor<'ast> for TypeChecker {
    type Context = TypeCheckContext<'ast>;

    fn visit_binary_op(&mut self, op: BinaryOp, left: NodeRef, right: NodeRef, span: SourceSpan, context: &mut Self::Context) {
        // Get the types of the left and right operands
        let left_type = self.get_node_type(left, context);
        let right_type = self.get_node_type(right, context);


        // Check type compatibility based on the operation
        match op {
            BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                self.check_arithmetic_operation(left_type, right_type, op, span, context);
            }
            BinaryOp::Equal | BinaryOp::NotEqual | BinaryOp::Less | BinaryOp::LessEqual | BinaryOp::Greater | BinaryOp::GreaterEqual => {
                self.check_comparison_operation(left_type, right_type, span, context);
            }
            BinaryOp::LogicAnd | BinaryOp::LogicOr => {
                self.check_logical_operation(left_type, right_type, span, context);
            }
            BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor | BinaryOp::LShift | BinaryOp::RShift => {
                self.check_bitwise_operation(left_type, right_type, op, span, context);
            }
            BinaryOp::Comma => {
                // Comma operator: no type checking needed beyond operand types
            }
            // Assignment operations will be handled separately
            _ => {
                // For other operations, assume compatible for now
            }
        }
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

impl TypeChecker {
    /// Get the resolved type of a node
    fn get_node_type(&self, node_ref: NodeRef, context: &TypeCheckContext) -> Option<TypeRef> {
        let node = context.ast.get_node(node_ref);

        // First try to get the resolved type from the AST node
        if let Some(type_ref) = node.resolved_type.get() {
            return Some(type_ref);
        }

        // If not set, try to infer from the node kind
        match &node.kind {
            NodeKind::Ident(_name, resolved_symbol) => {
                // Try to get type from symbol table
                if let Some(symbol_ref) = resolved_symbol.get() {
                    let symbol_entry = context.symbol_table.get_symbol_entry(symbol_ref);
                    Some(symbol_entry.type_info)
                } else {
                    None
                }
            }
            NodeKind::LiteralInt(_) => {
                // Assume int type for integer literals
                Some(self.get_int_type(context))
            }
            _ => None,
        }
    }

    /// Get a reference to the int type
    fn get_int_type(&self, _context: &TypeCheckContext) -> TypeRef {
        // For now, assume the first type is int. In a real implementation,
        // we'd have a proper type registry
        TypeRef::new(1).unwrap()
    }

    /// Check arithmetic operation compatibility
    fn check_arithmetic_operation(&self, left_type: Option<TypeRef>, right_type: Option<TypeRef>, op: BinaryOp, span: SourceSpan, context: &mut TypeCheckContext) {
        if let (Some(left), Some(right)) = (left_type, right_type) {
            let left_ty = context.ast.get_type(left);
            let right_ty = context.ast.get_type(right);

            // Check if both are arithmetic types or pointers (for add/sub)
            let left_is_arithmetic = left_ty.is_arithmetic();
            let right_is_arithmetic = right_ty.is_arithmetic();
            let left_is_pointer = matches!(left_ty.kind, TypeKind::Pointer { .. });
            let right_is_pointer = matches!(right_ty.kind, TypeKind::Pointer { .. });

            match op {
                BinaryOp::Add => {
                    let is_valid = (left_is_pointer || left_is_arithmetic) && right_is_arithmetic ||
                                    left_is_arithmetic && right_is_pointer;
                    if !is_valid {
                        self.report_type_error("Invalid operands to binary +", left_ty, right_ty, span, context);
                    }
                }
                BinaryOp::Sub => {
                    if !((left_is_pointer || left_is_arithmetic) && right_is_arithmetic ||
                         left_is_pointer && right_is_pointer) {
                        self.report_type_error("Invalid operands to binary -", left_ty, right_ty, span, context);
                    }
                }
                BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
                    if !(left_is_arithmetic && right_is_arithmetic) {
                        let op_str = match op {
                            BinaryOp::Mul => "*",
                            BinaryOp::Div => "/",
                            BinaryOp::Mod => "%",
                            _ => "?",
                        };
                        self.report_type_error(&format!("Invalid operands to binary {}", op_str), left_ty, right_ty, span, context);
                    }
                }
                _ => {}
            }
        }
    }

    /// Check comparison operation compatibility
    fn check_comparison_operation(&self, left_type: Option<TypeRef>, right_type: Option<TypeRef>, span: SourceSpan, context: &mut TypeCheckContext) {
        if let (Some(left), Some(right)) = (left_type, right_type) {
            let left_ty = context.ast.get_type(left);
            let right_ty = context.ast.get_type(right);

            // Comparisons are allowed between arithmetic types and pointers
            let left_is_valid = left_ty.is_arithmetic() || matches!(left_ty.kind, TypeKind::Pointer { .. });
            let right_is_valid = right_ty.is_arithmetic() || matches!(right_ty.kind, TypeKind::Pointer { .. });

            if !left_is_valid || !right_is_valid {
                self.report_type_error("Invalid operands to comparison", left_ty, right_ty, span, context);
            }
        }
    }

    /// Check logical operation compatibility
    fn check_logical_operation(&self, left_type: Option<TypeRef>, right_type: Option<TypeRef>, span: SourceSpan, context: &mut TypeCheckContext) {
        if let (Some(left), Some(right)) = (left_type, right_type) {
            let left_ty = context.ast.get_type(left);
            let right_ty = context.ast.get_type(right);

            // Logical operations require scalar types
            if !left_ty.is_scalar() || !right_ty.is_scalar() {
                self.report_type_error("Invalid operands to logical operation", left_ty, right_ty, span, context);
            }
        }
    }

    /// Check bitwise operation compatibility
    fn check_bitwise_operation(&self, left_type: Option<TypeRef>, right_type: Option<TypeRef>, op: BinaryOp, span: SourceSpan, context: &mut TypeCheckContext) {
        if let (Some(left), Some(right)) = (left_type, right_type) {
            let left_ty = context.ast.get_type(left);
            let right_ty = context.ast.get_type(right);

            // Bitwise operations require integer types
            if !left_ty.is_integer() || !right_ty.is_integer() {
                let op_str = match op {
                    BinaryOp::BitAnd => "&",
                    BinaryOp::BitOr => "|",
                    BinaryOp::BitXor => "^",
                    BinaryOp::LShift => "<<",
                    BinaryOp::RShift => ">>",
                    _ => "?",
                };
                self.report_type_error(&format!("Invalid operands to binary {}", op_str), left_ty, right_ty, span, context);
            }
        }
    }

    /// Report a type mismatch error
    fn report_type_error(&self, message: &str, _left_ty: &Type, _right_ty: &Type, span: SourceSpan, context: &mut TypeCheckContext) {
        use crate::diagnostic::SemanticError;

        context.diag.report_error(SemanticError::TypeMismatch {
            expected: message.to_string(),
            found: "".to_string(),
            location: span,
        });
    }

}

/// Context for type resolution
pub struct TypeResolutionContext<'a> {
    pub symbol_table: &'a mut SymbolTable,
    pub diag: &'a mut DiagnosticEngine,
    pub current_scope: ScopeId,
}

/// Type resolver that sets resolved_type on AST nodes based on symbol information.
/// This runs after name resolution to populate type information.
pub struct TypeResolver;

impl Default for TypeResolver {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeResolver {
    /// Create a new type resolver
    pub fn new() -> Self {
        TypeResolver
    }

    /// Resolve types in the AST starting from the given node
    pub fn resolve_types<'ast>(
        &mut self,
        ast: &'ast Ast,
        symbol_table: &'ast mut SymbolTable,
        diag: &'ast mut DiagnosticEngine,
        start_node: NodeRef,
    ) {
        let mut context = TypeResolutionContext {
            symbol_table,
            diag,
            current_scope: ScopeId::GLOBAL,
        };

        self.walk_ast(ast, start_node, &mut context);
    }

    /// Walk the AST starting from the given node
    fn walk_ast<'a>(&mut self, ast: &'a Ast, node_ref: NodeRef, context: &mut TypeResolutionContext<'a>) {
        // Visit the current node
        visit_node(self, ast, node_ref, context);

        // Recursively visit children
        let node = ast.get_node(node_ref);
        self.visit_children(ast, node, context);
    }

    /// Visit child nodes of the given node
    fn visit_children<'a>(&mut self, ast: &'a Ast, node: &Node, context: &mut TypeResolutionContext<'a>) {
        use crate::semantic::visitor::get_child_nodes;

        match &node.kind {
            NodeKind::FunctionDef(func_def) => {
                // For function definitions, we need to resolve in the function scope
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

impl<'ast> SemanticVisitor<'ast> for TypeResolver {
    type Context = TypeResolutionContext<'ast>;

    fn visit_literal_int(&mut self, _value: i64, _span: SourceSpan, _context: &mut Self::Context) {
        // Literal ints have int type - but we need to set this on the node
        // For now, we'll assume the AST nodes already have types set during parsing
        // This is a simplification; in a full implementation, we'd set types here
    }

    fn visit_ident(&mut self, _name: Symbol, resolved_symbol: &Cell<Option<SymbolEntryRef>>, _span: SourceSpan, _context: &mut Self::Context) {
        if let Some(_symbol_ref) = resolved_symbol.get() {
            // Set the resolved type on the identifier node
            // Note: We can't directly modify the AST here because we have a borrow conflict
            // In a real implementation, we'd need to modify the AST structure to allow this
            // For now, we'll assume types are set elsewhere or use a different approach
        }
    }

    // Other visitor methods can be added as needed for type resolution
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

fn find_function_with_name(declarator: &Declarator) -> (Option<Symbol>, Option<&ThinVec<ParamData>>) {
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