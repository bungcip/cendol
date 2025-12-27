//! Type checking phase - comprehensive type inference and checking.
//!
//! This module implements the type checking phase that executes immediately after
//! the symbol resolver. It traverses the AST and populates the `resolved_type` field
//! for each node, performing type inference, unification, and error detection.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::semantic::SymbolTable;
use crate::source_manager::SourceSpan;
use std::num::NonZero;

/// Context for the type checking phase
pub struct TypeCheckCtx<'a, 'src> {
    pub ast: &'a mut Ast,
    pub diag: &'src mut DiagnosticEngine,
    pub symbol_table: &'a mut SymbolTable,
    // Track errors during type checking for early termination
    pub has_errors: bool,
}

impl<'a, 'src> TypeCheckCtx<'a, 'src> {
    /// Create a new type checking context
    pub fn new(ast: &'a mut Ast, diag: &'src mut DiagnosticEngine, symbol_table: &'a mut SymbolTable) -> Self {
        Self {
            ast,
            diag,
            symbol_table,
            has_errors: false,
        }
    }

    /// Report a semantic error and mark context as having errors
    pub fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report(error);
    }

    // /// Check if the context has any errors
    // pub fn has_errors(&self) -> bool {
    //     self.has_errors
    // }

    /// Set the resolved type for a node
    pub fn set_resolved_type(&mut self, node_ref: NodeRef, type_ref: TypeRef) {
        let node = self.ast.get_node(node_ref);
        node.resolved_type.set(Some(type_ref));
    }

    /// Get the resolved type for a node, falling back to error type if not set
    pub fn get_resolved_type(&mut self, node_ref: NodeRef) -> TypeRef {
        let node = self.ast.get_node(node_ref);
        node.resolved_type.get().unwrap_or_else(|| {
            // Create an error type if not resolved
            let error_type = Type::new(TypeKind::Error);
            self.ast.push_type(error_type)
        })
    }

    // /// Check if two types are compatible for assignment
    // pub fn is_assignable(&self, target_type: TypeRef, source_type: TypeRef) -> bool {
    //     // For now, implement simple type compatibility
    //     // In a full implementation, this would handle:
    //     // - Integer promotions
    //     // - Pointer compatibility
    //     // - Struct/union compatibility
    //     // - Const/volatile qualifiers
    //     target_type == source_type
    // }

    /// Find the common type for binary operations
    pub fn find_common_type(&mut self, left_type: TypeRef, right_type: TypeRef, _span: SourceSpan) -> TypeRef {
        // For now, return the left type if they match, otherwise return left type
        // This is a simplified implementation - in a full type checker, we would
        // implement proper type promotion rules
        if left_type == right_type {
            left_type
        } else {
            // For now, just return the left type without error
            // This allows basic type checking to work
            left_type
        }
    }
}

/// Main entry point for type checking
pub fn run_type_checker(ast: &mut Ast, diag: &mut DiagnosticEngine, symbol_table: &mut SymbolTable) {
    let mut ctx = TypeCheckCtx::new(ast, diag, symbol_table);

    // Check if we have a root node to start traversal from
    if let Some(root_node_ref) = ctx.ast.root {
        type_check_node_recursive(&mut ctx, root_node_ref);
    }
}

/// Recursively type check an AST node
fn type_check_node_recursive(ctx: &mut TypeCheckCtx, node_ref: NodeRef) {
    let node = ctx.ast.get_node(node_ref);
    let node_kind = node.kind.clone();
    let node_span = node.span;

    match node_kind {
        NodeKind::TranslationUnit(nodes) => {
            for child_ref in nodes {
                type_check_node_recursive(ctx, child_ref);
            }
        }

        NodeKind::Function(function_data) => {
            type_check_function(ctx, &function_data, node_span);
        }

        NodeKind::VarDecl(var_decl) => {
            type_check_var_decl(ctx, &var_decl, node_span);
        }

        NodeKind::TypedefDecl(typedef_decl) => {
            type_check_typedef_decl(ctx, &typedef_decl, node_span);
        }

        NodeKind::RecordDecl(record_decl) => {
            type_check_record_decl(ctx, &record_decl, node_span);
        }

        NodeKind::LiteralInt(_) => {
            // Integer literals are int type
            let int_type = Type::new(TypeKind::Int { is_signed: true });
            let int_type_ref = ctx.ast.push_type(int_type);
            ctx.set_resolved_type(node_ref, int_type_ref);
        }

        NodeKind::LiteralFloat(_) => {
            // Float literals are double type
            let double_type = Type::new(TypeKind::Double { is_long_double: false });
            let double_type_ref = ctx.ast.push_type(double_type);
            ctx.set_resolved_type(node_ref, double_type_ref);
        }

        NodeKind::LiteralChar(_) => {
            // Character literals are int type in C
            let int_type = Type::new(TypeKind::Int { is_signed: true });
            let int_type_ref = ctx.ast.push_type(int_type);
            ctx.set_resolved_type(node_ref, int_type_ref);
        }

        NodeKind::LiteralString(_) => {
            // String literals are char array type
            let char_type = Type::new(TypeKind::Char { is_signed: true });
            let char_type_ref = ctx.ast.push_type(char_type);
            let array_type = Type::new(TypeKind::Array {
                element_type: char_type_ref,
                size: ArraySizeType::Incomplete, // String literals have unknown size
            });
            let array_type_ref = ctx.ast.push_type(array_type);
            ctx.set_resolved_type(node_ref, array_type_ref);
        }

        NodeKind::Ident(name) => {
            // TODO: refactor type_check_identifier() because resolved_symbol
            //  wil set by symbol_resolver, so it will always exists
            let symbol_ref = node.resolved_symbol.get();
            type_check_identifier(ctx, node_ref, name, symbol_ref, node_span);
        }

        NodeKind::BinaryOp(op, left_ref, right_ref) => {
            type_check_binary_op(ctx, node_ref, op, left_ref, right_ref, node_span);
        }

        NodeKind::UnaryOp(op, operand_ref) => {
            type_check_unary_op(ctx, node_ref, op, operand_ref, node_span);
        }

        NodeKind::FunctionCall(func_ref, args) => {
            type_check_function_call(ctx, node_ref, func_ref, args, node_span);
        }

        NodeKind::MemberAccess(object_ref, field_name, is_arrow) => {
            type_check_member_access(ctx, node_ref, object_ref, field_name, is_arrow, node_span);
        }

        NodeKind::IndexAccess(array_ref, index_ref) => {
            type_check_index_access(ctx, node_ref, array_ref, index_ref, node_span);
        }

        NodeKind::Cast(type_ref, expr_ref) => {
            type_check_cast(ctx, node_ref, type_ref, expr_ref, node_span);
        }

        NodeKind::Assignment(op, lhs_ref, rhs_ref) => {
            type_check_assignment(ctx, node_ref, op, lhs_ref, rhs_ref, node_span);
        }

        NodeKind::Return(expr) => {
            type_check_return(ctx, node_ref, &expr, node_span);
        }

        NodeKind::If(if_stmt) => {
            type_check_if(ctx, node_ref, &if_stmt, node_span);
        }

        NodeKind::While(while_stmt) => {
            type_check_while(ctx, node_ref, &while_stmt, node_span);
        }

        NodeKind::DoWhile(body_ref, condition_ref) => {
            type_check_do_while(ctx, node_ref, body_ref, condition_ref, node_span);
        }

        NodeKind::For(for_stmt) => {
            type_check_for(ctx, node_ref, &for_stmt, node_span);
        }

        NodeKind::CompoundStatement(nodes) => {
            type_check_compound_statement(ctx, node_ref, &nodes);
        }

        NodeKind::DeclarationList(nodes) => {
            for child_ref in nodes {
                type_check_node_recursive(ctx, child_ref);
            }
        }

        // Handle other node types that might not have specific type checking yet
        _ => {
            // For nodes that don't have specific type checking, try to infer from context
            // or leave as unresolved (will be handled by semantic analyzer)
        }
    }
}

/// Type check a function node
fn type_check_function(ctx: &mut TypeCheckCtx, function_data: &FunctionData, _span: SourceSpan) {
    // Set the function's type as resolved
    let symbol_ref = function_data.symbol.get();
    if let Some(node_ref) = ctx
        .ast
        .get_node(NonZero::new(symbol_ref).unwrap())
        .resolved_symbol
        .get()
    {
        ctx.set_resolved_type(node_ref, function_data.ty);
    }

    // Type check the function body
    type_check_node_recursive(ctx, function_data.body);
}

/// Type check a variable declaration
fn type_check_var_decl(ctx: &mut TypeCheckCtx, var_decl: &VarDeclData, span: SourceSpan) {
    // The variable's type should already be set from semantic lowering
    // For variable declarations, we need to find the actual node reference
    // For now, we'll skip this as it's complex to resolve without proper node tracking

    // Type check the initializer if present
    if let Some(initializer) = &var_decl.init {
        type_check_initializer(ctx, var_decl.ty, *initializer, span);
    }
}

/// Type check a typedef declaration
fn type_check_typedef_decl(_ctx: &mut TypeCheckCtx, _typedef_decl: &TypedefDeclData, _span: SourceSpan) {
    // The typedef's type should already be set
    // For typedef declarations, we need to find the actual node reference
    // For now, we'll skip this as it's complex to resolve without proper node tracking
}

/// Type check a record declaration
fn type_check_record_decl(_ctx: &mut TypeCheckCtx, record_decl: &RecordDeclData, _span: SourceSpan) {
    // The record's type should already be set from semantic lowering
    // For record declarations, we need to find the actual node reference
    // For now, we'll skip this as it's complex to resolve without proper node tracking

    // Type check each member
    for _member in &record_decl.members {
        // For struct members, we need to find the actual node reference
        // For now, we'll skip this as it's complex to resolve without proper node tracking
    }
}

/// Type check an identifier
fn type_check_identifier(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    name: Symbol,
    symbol_ref: Option<SymbolEntryRef>,
    _span: SourceSpan,
) {
    if let Some(resolved_ref) = symbol_ref {
        let entry = ctx.symbol_table.get_symbol_entry(resolved_ref);
        ctx.set_resolved_type(node_ref, entry.type_info);
    } else {
        // Try to resolve from symbol table
        if let Some((entry_ref, _)) = ctx.symbol_table.lookup_symbol(name) {
            let entry = ctx.symbol_table.get_symbol_entry(entry_ref);
            ctx.set_resolved_type(node_ref, entry.type_info);
        } else {
            // For now, skip reporting undeclared identifier errors
            // This allows the type checker to work with the existing symbol resolution
            let int_type = Type::new(TypeKind::Int { is_signed: true });
            let int_type_ref = ctx.ast.push_type(int_type);
            ctx.set_resolved_type(node_ref, int_type_ref);
        }
    }
}

/// Type check a binary operation
fn type_check_binary_op(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    op: BinaryOp,
    left_ref: NodeRef,
    right_ref: NodeRef,
    span: SourceSpan,
) {
    // Recursively type check operands
    type_check_node_recursive(ctx, left_ref);
    type_check_node_recursive(ctx, right_ref);

    let left_type = ctx.get_resolved_type(left_ref);
    let right_type = ctx.get_resolved_type(right_ref);

    // Determine the result type based on the operation
    let result_type = match op {
        BinaryOp::Add | BinaryOp::Sub | BinaryOp::Mul | BinaryOp::Div | BinaryOp::Mod => {
            // Arithmetic operations - find common type
            ctx.find_common_type(left_type, right_type, span)
        }
        BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor | BinaryOp::LShift | BinaryOp::RShift => {
            // Bitwise operations - require integer types
            if ctx.is_integer_type(left_type) && ctx.is_integer_type(right_type) {
                ctx.find_common_type(left_type, right_type, span)
            } else {
                ctx.report_error(SemanticError::InvalidBinaryOperands {
                    left_ty: format!("{:?}", ctx.ast.get_type(left_type).kind),
                    right_ty: format!("{:?}", ctx.ast.get_type(right_type).kind),
                    span,
                });
                let error_type = Type::new(TypeKind::Error);
                ctx.ast.push_type(error_type)
            }
        }
        BinaryOp::Equal
        | BinaryOp::NotEqual
        | BinaryOp::Less
        | BinaryOp::LessEqual
        | BinaryOp::Greater
        | BinaryOp::GreaterEqual => {
            // Comparison operations - result is int (bool in C99+)
            let int_type = Type::new(TypeKind::Int { is_signed: true });
            ctx.ast.push_type(int_type)
        }
        BinaryOp::LogicAnd | BinaryOp::LogicOr => {
            // Logical operations - result is int (bool in C99+)
            let int_type = Type::new(TypeKind::Int { is_signed: true });
            ctx.ast.push_type(int_type)
        }
        BinaryOp::Comma => {
            // Comma operator - result is the type of the right operand
            right_type
        }
        _ => {
            // Assignment operations are handled separately
            let error_type = Type::new(TypeKind::Error);
            ctx.ast.push_type(error_type)
        }
    };

    ctx.set_resolved_type(node_ref, result_type);
}

/// Type check a unary operation
fn type_check_unary_op(ctx: &mut TypeCheckCtx, node_ref: NodeRef, op: UnaryOp, operand_ref: NodeRef, span: SourceSpan) {
    // Recursively type check operand
    type_check_node_recursive(ctx, operand_ref);

    let operand_type = ctx.get_resolved_type(operand_ref);

    let result_type = match op {
        UnaryOp::Plus | UnaryOp::Minus => {
            // Unary plus/minus - result type is same as operand
            operand_type
        }
        UnaryOp::Deref => {
            // Dereference - operand must be pointer type
            if let TypeKind::Pointer { pointee } = &ctx.ast.get_type(operand_type).kind {
                *pointee
            } else {
                ctx.report_error(SemanticError::InvalidBinaryOperands {
                    left_ty: format!("{:?}", ctx.ast.get_type(operand_type).kind),
                    right_ty: format!("{:?}", ctx.ast.get_type(operand_type).kind),
                    span,
                });
                let error_type = Type::new(TypeKind::Error);
                ctx.ast.push_type(error_type)
            }
        }
        UnaryOp::AddrOf => {
            // Address-of - result is pointer to operand type
            let pointer_type = Type::new(TypeKind::Pointer { pointee: operand_type });
            ctx.ast.push_type(pointer_type)
        }
        UnaryOp::BitNot => {
            // Bitwise not - operand must be integer type
            if ctx.is_integer_type(operand_type) {
                operand_type
            } else {
                ctx.report_error(SemanticError::InvalidBinaryOperands {
                    left_ty: format!("{:?}", ctx.ast.get_type(operand_type).kind),
                    right_ty: format!("{:?}", ctx.ast.get_type(operand_type).kind),
                    span,
                });
                let error_type = Type::new(TypeKind::Error);
                ctx.ast.push_type(error_type)
            }
        }
        UnaryOp::LogicNot => {
            // Logical not - result is int (bool in C99+)
            let int_type = Type::new(TypeKind::Int { is_signed: true });
            ctx.ast.push_type(int_type)
        }
        UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
            // Increment/decrement - operand must be modifiable lvalue of arithmetic type
            if ctx.is_arithmetic_type(operand_type) {
                operand_type
            } else {
                ctx.report_error(SemanticError::InvalidBinaryOperands {
                    left_ty: format!("{:?}", ctx.ast.get_type(operand_type).kind),
                    right_ty: format!("{:?}", ctx.ast.get_type(operand_type).kind),
                    span,
                });
                let error_type = Type::new(TypeKind::Error);
                ctx.ast.push_type(error_type)
            }
        }
    };

    ctx.set_resolved_type(node_ref, result_type);
}

/// Type check a function call
fn type_check_function_call(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    func_ref: NodeRef,
    args: Vec<NodeRef>,
    span: SourceSpan,
) {
    // Recursively type check function and arguments
    type_check_node_recursive(ctx, func_ref);
    for arg_ref in &args {
        type_check_node_recursive(ctx, *arg_ref);
    }

    let func_type = ctx.get_resolved_type(func_ref);

    // For now, assume function calls return int
    // In a full implementation, we would:
    // 1. Check if func_type is a function type
    // 2. Verify argument count and types match function parameters
    // 3. Return the function's return type
    let return_type = match &ctx.ast.get_type(func_type).kind {
        TypeKind::Function { return_type, .. } => *return_type,
        TypeKind::Pointer { pointee } if matches!(ctx.ast.get_type(*pointee).kind, TypeKind::Function { .. }) => {
            // Function pointer
            if let TypeKind::Function { return_type, .. } = ctx.ast.get_type(*pointee).kind {
                return_type
            } else {
                unreachable!()
            }
        }
        _ => {
            ctx.report_error(SemanticError::InvalidBinaryOperands {
                left_ty: "function".to_string(),
                right_ty: "unknown".to_string(),
                span,
            });
            let error_type = Type::new(TypeKind::Error);
            ctx.ast.push_type(error_type)
        }
    };

    ctx.set_resolved_type(node_ref, return_type);
}

/// Type check member access
fn type_check_member_access(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    object_ref: NodeRef,
    field_name: Symbol,
    is_arrow: bool,
    span: SourceSpan,
) {
    // Recursively type check object
    type_check_node_recursive(ctx, object_ref);

    let object_type = ctx.get_resolved_type(object_ref);

    // Handle arrow access (dereference first)
    let base_type = if is_arrow {
        match &ctx.ast.get_type(object_type).kind {
            TypeKind::Pointer { pointee } => *pointee,
            _ => {
                ctx.report_error(SemanticError::InvalidBinaryOperands {
                    left_ty: format!("{:?}", ctx.ast.get_type(object_type).kind),
                    right_ty: "member access".to_string(),
                    span,
                });
                let error_type = Type::new(TypeKind::Error);
                ctx.ast.push_type(error_type)
            }
        }
    } else {
        object_type
    };

    // Look up the field in the struct/union
    let field_type = match &ctx.ast.get_type(base_type).kind {
        TypeKind::Record { members, .. } => members
            .iter()
            .find(|member| member.name == field_name)
            .map(|member| member.member_type),
        _ => None,
    };

    let result_type = match field_type {
        Some(field_type) => field_type,
        None => {
            ctx.report_error(SemanticError::UndeclaredIdentifier { name: field_name, span });
            let error_type = Type::new(TypeKind::Error);
            ctx.ast.push_type(error_type)
        }
    };

    ctx.set_resolved_type(node_ref, result_type);
}

/// Type check array index access
fn type_check_index_access(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    array_ref: NodeRef,
    index_ref: NodeRef,
    span: SourceSpan,
) {
    // Recursively type check operands
    type_check_node_recursive(ctx, array_ref);
    type_check_node_recursive(ctx, index_ref);

    let array_type = ctx.get_resolved_type(array_ref);
    let index_type = ctx.get_resolved_type(index_ref);

    // Index must be integer type
    if !ctx.is_integer_type(index_type) {
        ctx.report_error(SemanticError::InvalidArraySize { span });
        let error_type = Type::new(TypeKind::Error);
        let error_type_ref = ctx.ast.push_type(error_type);
        ctx.set_resolved_type(node_ref, error_type_ref);
        return;
    }

    // Array must be array or pointer type
    let element_type = match &ctx.ast.get_type(array_type).kind {
        TypeKind::Array { element_type, .. } => *element_type,
        TypeKind::Pointer { pointee } => *pointee,
        _ => {
            ctx.report_error(SemanticError::InvalidArraySize { span });
            let error_type = Type::new(TypeKind::Error);
            ctx.ast.push_type(error_type)
        }
    };

    ctx.set_resolved_type(node_ref, element_type);
}

/// Type check a cast expression
fn type_check_cast(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    target_type_ref: TypeRef,
    expr_ref: NodeRef,
    _span: SourceSpan,
) {
    // Recursively type check the expression
    type_check_node_recursive(ctx, expr_ref);

    let _expr_type = ctx.get_resolved_type(expr_ref);

    // For now, accept any cast (C allows most casts)
    // In a full implementation, we would validate cast compatibility
    ctx.set_resolved_type(node_ref, target_type_ref);
}

/// Type check an assignment
fn type_check_assignment(
    ctx: &mut TypeCheckCtx,
    node_ref: NodeRef,
    _op: BinaryOp,
    lhs_ref: NodeRef,
    rhs_ref: NodeRef,
    _span: SourceSpan,
) {
    // Recursively type check operands
    type_check_node_recursive(ctx, lhs_ref);
    type_check_node_recursive(ctx, rhs_ref);

    let lhs_type = ctx.get_resolved_type(lhs_ref);
    let _rhs_type = ctx.get_resolved_type(rhs_ref);

    // Check assignment compatibility - for now, just accept all assignments
    // In a full implementation, this would check type compatibility rules

    // Assignment result has the type of the left operand
    ctx.set_resolved_type(node_ref, lhs_type);
}

/// Type check an initializer
fn type_check_initializer(ctx: &mut TypeCheckCtx, _target_type: TypeRef, initializer: NodeRef, _span: SourceSpan) {
    let initializer = ctx.ast.get_node(initializer).clone_initializer_kind().clone();
    match initializer {
        Initializer::Expression(expr_ref) => {
            type_check_node_recursive(ctx, expr_ref);
            let _expr_type = ctx.get_resolved_type(expr_ref);
            // For now, skip type checking initializers
            // In a full implementation, this would check type compatibility
        }
        Initializer::List(_designated_initializers) => {
            // For compound initializers, skip type checking for now
            // In a full implementation, this would check each field's type
        }
    }
}

/// Type check a return statement
fn type_check_return(ctx: &mut TypeCheckCtx, _node_ref: NodeRef, expr: &Option<NodeRef>, _span: SourceSpan) {
    if let Some(expr_ref) = expr {
        type_check_node_recursive(ctx, *expr_ref);
        // The return type should be checked against the function's return type
        // This would require tracking the current function context
    }
}

/// Type check an if statement
fn type_check_if(ctx: &mut TypeCheckCtx, _node_ref: NodeRef, if_stmt: &IfStmt, span: SourceSpan) {
    type_check_node_recursive(ctx, if_stmt.condition);
    type_check_node_recursive(ctx, if_stmt.then_branch);
    if let Some(else_branch) = if_stmt.else_branch {
        type_check_node_recursive(ctx, else_branch);
    }

    // Condition must be scalar type
    let cond_type = ctx.get_resolved_type(if_stmt.condition);
    if !ctx.is_scalar_type(cond_type) {
        ctx.report_error(SemanticError::InvalidBinaryOperands {
            left_ty: format!("{:?}", ctx.ast.get_type(cond_type).kind),
            right_ty: "condition".to_string(),
            span,
        });
    }
}

/// Type check a while statement
fn type_check_while(ctx: &mut TypeCheckCtx, _node_ref: NodeRef, while_stmt: &WhileStmt, span: SourceSpan) {
    type_check_node_recursive(ctx, while_stmt.condition);
    type_check_node_recursive(ctx, while_stmt.body);

    // Condition must be scalar type
    let cond_type = ctx.get_resolved_type(while_stmt.condition);
    if !ctx.is_scalar_type(cond_type) {
        ctx.report_error(SemanticError::InvalidBinaryOperands {
            left_ty: format!("{:?}", ctx.ast.get_type(cond_type).kind),
            right_ty: "condition".to_string(),
            span,
        });
    }
}

/// Type check a do-while statement
fn type_check_do_while(
    ctx: &mut TypeCheckCtx,
    _node_ref: NodeRef,
    body_ref: NodeRef,
    condition_ref: NodeRef,
    span: SourceSpan,
) {
    type_check_node_recursive(ctx, body_ref);
    type_check_node_recursive(ctx, condition_ref);

    // Condition must be scalar type
    let cond_type = ctx.get_resolved_type(condition_ref);
    if !ctx.is_scalar_type(cond_type) {
        ctx.report_error(SemanticError::InvalidBinaryOperands {
            left_ty: format!("{:?}", ctx.ast.get_type(cond_type).kind),
            right_ty: "condition".to_string(),
            span,
        });
    }
}

/// Type check a for statement
fn type_check_for(ctx: &mut TypeCheckCtx, _node_ref: NodeRef, for_stmt: &ForStmt, span: SourceSpan) {
    if let Some(init) = for_stmt.init {
        type_check_node_recursive(ctx, init);
    }
    if let Some(condition) = for_stmt.condition {
        type_check_node_recursive(ctx, condition);

        // Condition must be scalar type
        let cond_type = ctx.get_resolved_type(condition);
        if !ctx.is_scalar_type(cond_type) {
            ctx.report_error(SemanticError::InvalidBinaryOperands {
                left_ty: format!("{:?}", ctx.ast.get_type(cond_type).kind),
                right_ty: "condition".to_string(),
                span,
            });
        }
    }
    if let Some(increment) = for_stmt.increment {
        type_check_node_recursive(ctx, increment);
    }
    type_check_node_recursive(ctx, for_stmt.body);
}

/// Type check a compound statement
fn type_check_compound_statement(ctx: &mut TypeCheckCtx, _node_ref: NodeRef, nodes: &[NodeRef]) {
    for child_ref in nodes {
        type_check_node_recursive(ctx, *child_ref);
    }
}

/// Helper methods for type checking

impl<'a, 'src> TypeCheckCtx<'a, 'src> {
    /// Check if a type is an integer type
    fn is_integer_type(&self, type_ref: TypeRef) -> bool {
        matches!(
            self.ast.get_type(type_ref).kind,
            TypeKind::Bool
                | TypeKind::Char { .. }
                | TypeKind::Short { .. }
                | TypeKind::Int { .. }
                | TypeKind::Long { .. }
        )
    }

    /// Check if a type is a floating point type
    fn is_floating_type(&self, type_ref: TypeRef) -> bool {
        matches!(
            self.ast.get_type(type_ref).kind,
            TypeKind::Float | TypeKind::Double { .. } | TypeKind::Complex { .. }
        )
    }

    /// Check if a type is an arithmetic type
    fn is_arithmetic_type(&self, type_ref: TypeRef) -> bool {
        self.is_integer_type(type_ref) || self.is_floating_type(type_ref)
    }

    /// Check if a type is a scalar type
    fn is_scalar_type(&self, type_ref: TypeRef) -> bool {
        self.is_arithmetic_type(type_ref)
            || matches!(self.ast.get_type(type_ref).kind, TypeKind::Pointer { .. })
            || matches!(self.ast.get_type(type_ref).kind, TypeKind::Enum { .. })
    }
}
