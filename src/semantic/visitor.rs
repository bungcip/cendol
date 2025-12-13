//! AST Visitor trait for semantic analysis phases.
//!
//! This module defines the visitor pattern used by semantic analysis.
//! Each analysis phase (name resolution, type checking, etc.) implements
//! this trait to traverse the AST and perform their specific analysis.

use std::cell::Cell;

use crate::ast::*;

/// Trait for visiting AST nodes during semantic analysis.
/// Each method corresponds to a NodeKind variant and allows
/// analysis phases to perform specific operations on each node type.
pub trait SemanticVisitor<'ast> {
    /// Context passed to visitor methods
    type Context;

    /// Visit a literal integer node
    fn visit_literal_int(&mut self, _value: i64, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a literal float node
    fn visit_literal_float(&mut self, _value: f64, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a literal string node
    fn visit_literal_string(&mut self, _value: Symbol, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a literal character node
    fn visit_literal_char(&mut self, _value: u8, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an identifier node
    fn visit_ident(&mut self, _name: Symbol, _resolved_symbol: &Cell<Option<SymbolEntryRef>>, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a unary operation node
    fn visit_unary_op(&mut self, _op: UnaryOp, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a binary operation node
    fn visit_binary_op(&mut self, _op: BinaryOp, _left: NodeRef, _right: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a ternary operation node
    fn visit_ternary_op(&mut self, _cond: NodeRef, _then_expr: NodeRef, _else_expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a post-increment node
    fn visit_post_increment(&mut self, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a post-decrement node
    fn visit_post_decrement(&mut self, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an assignment node
    fn visit_assignment(&mut self, _op: BinaryOp, _lhs: NodeRef, _rhs: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a function call node
    fn visit_function_call(&mut self, _func: NodeRef, _args: &[NodeRef], _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a member access node
    fn visit_member_access(&mut self, _object: NodeRef, _field: Symbol, _is_arrow: bool, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an index access node
    fn visit_index_access(&mut self, _array: NodeRef, _index: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a cast node
    fn visit_cast(&mut self, _target_type: TypeRef, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a sizeof expression node
    fn visit_sizeof_expr(&mut self, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a sizeof type node
    fn visit_sizeof_type(&mut self, _target_type: TypeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an alignof node
    fn visit_alignof(&mut self, _target_type: TypeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a compound literal node
    fn visit_compound_literal(&mut self, _type_ref: TypeRef, _initializer: InitializerRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a generic selection node
    fn visit_generic_selection(&mut self, _controlling_expr: NodeRef, _associations: &[GenericAssociation], _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a va_arg node
    fn visit_va_arg(&mut self, _va_list_expr: NodeRef, _type_ref: TypeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a GNU statement expression node
    fn visit_gnu_statement_expression(&mut self, _compound_stmt: NodeRef, _result_expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a compound statement node
    fn visit_compound_statement(&mut self, _statements: &[NodeRef], _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an if statement node
    fn visit_if(&mut self, _stmt: &IfStmt, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a while statement node
    fn visit_while(&mut self, _stmt: &WhileStmt, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a do-while statement node
    fn visit_do_while(&mut self, _body: NodeRef, _condition: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a for statement node
    fn visit_for(&mut self, _stmt: &ForStmt, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a return statement node
    fn visit_return(&mut self, _expr: Option<NodeRef>, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a break statement node
    fn visit_break(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a continue statement node
    fn visit_continue(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a goto statement node
    fn visit_goto(&mut self, _label: Symbol, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a labeled statement node
    fn visit_label(&mut self, _label: Symbol, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a switch statement node
    fn visit_switch(&mut self, _condition: NodeRef, _body: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a case statement node
    fn visit_case(&mut self, _expr: NodeRef, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a case range statement node
    fn visit_case_range(&mut self, _start_expr: NodeRef, _end_expr: NodeRef, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a default statement node
    fn visit_default(&mut self, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an expression statement node
    fn visit_expression_statement(&mut self, _expr: Option<NodeRef>, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an empty statement node
    fn visit_empty_statement(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a declaration node
    fn visit_declaration(&mut self, _decl: &DeclarationData, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a function definition node
    fn visit_function_def(&mut self, _func_def: &FunctionDefData, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit an enum constant node
    fn visit_enum_constant(&mut self, _name: Symbol, _value_expr: Option<NodeRef>, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a static assert node
    fn visit_static_assert(&mut self, _condition: NodeRef, _message: Symbol, _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a translation unit node
    fn visit_translation_unit(&mut self, _declarations: &[NodeRef], _span: SourceSpan, _context: &mut Self::Context) {}

    /// Visit a dummy node
    fn visit_dummy(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}
}


/// Helper function to dispatch a node to the appropriate visitor method
pub fn visit_node<'ast, V: SemanticVisitor<'ast>>(
    visitor: &mut V,
    ast: &Ast,
    node_ref: NodeRef,
    context: &mut V::Context,
) {
    let node = ast.get_node(node_ref);

    match &node.kind {
        NodeKind::LiteralInt(value) => visitor.visit_literal_int(*value, node.span, context),
        NodeKind::LiteralFloat(value) => visitor.visit_literal_float(*value, node.span, context),
        NodeKind::LiteralString(value) => visitor.visit_literal_string(*value, node.span, context),
        NodeKind::LiteralChar(value) => visitor.visit_literal_char(*value, node.span, context),
        NodeKind::Ident(name, resolved_symbol) => visitor.visit_ident(*name, resolved_symbol, node.span, context),
        NodeKind::UnaryOp(op, expr) => visitor.visit_unary_op(*op, *expr, node.span, context),
        NodeKind::BinaryOp(op, left, right) => visitor.visit_binary_op(*op, *left, *right, node.span, context),
        NodeKind::TernaryOp(cond, then_expr, else_expr) => visitor.visit_ternary_op(*cond, *then_expr, *else_expr, node.span, context),
        NodeKind::PostIncrement(expr) => visitor.visit_post_increment(*expr, node.span, context),
        NodeKind::PostDecrement(expr) => visitor.visit_post_decrement(*expr, node.span, context),
        NodeKind::Assignment(op, lhs, rhs) => visitor.visit_assignment(*op, *lhs, *rhs, node.span, context),
        NodeKind::FunctionCall(func, args) => visitor.visit_function_call(*func, args, node.span, context),
        NodeKind::MemberAccess(object, field, is_arrow) => visitor.visit_member_access(*object, *field, *is_arrow, node.span, context),
        NodeKind::IndexAccess(array, index) => visitor.visit_index_access(*array, *index, node.span, context),
        NodeKind::Cast(target_type, expr) => visitor.visit_cast(*target_type, *expr, node.span, context),
        NodeKind::SizeOfExpr(expr) => visitor.visit_sizeof_expr(*expr, node.span, context),
        NodeKind::SizeOfType(target_type) => visitor.visit_sizeof_type(*target_type, node.span, context),
        NodeKind::AlignOf(target_type) => visitor.visit_alignof(*target_type, node.span, context),
        NodeKind::CompoundLiteral(type_ref, initializer) => visitor.visit_compound_literal(*type_ref, *initializer, node.span, context),
        NodeKind::GenericSelection(controlling_expr, associations) => visitor.visit_generic_selection(*controlling_expr, associations, node.span, context),
        NodeKind::VaArg(va_list_expr, type_ref) => visitor.visit_va_arg(*va_list_expr, *type_ref, node.span, context),
        NodeKind::GnuStatementExpression(compound_stmt, result_expr) => visitor.visit_gnu_statement_expression(*compound_stmt, *result_expr, node.span, context),
        NodeKind::CompoundStatement(statements) => visitor.visit_compound_statement(statements, node.span, context),
        NodeKind::If(stmt) => visitor.visit_if(stmt, node.span, context),
        NodeKind::While(stmt) => visitor.visit_while(stmt, node.span, context),
        NodeKind::DoWhile(body, condition) => visitor.visit_do_while(*body, *condition, node.span, context),
        NodeKind::For(stmt) => visitor.visit_for(stmt, node.span, context),
        NodeKind::Return(expr) => visitor.visit_return(*expr, node.span, context),
        NodeKind::Break => visitor.visit_break(node.span, context),
        NodeKind::Continue => visitor.visit_continue(node.span, context),
        NodeKind::Goto(label) => visitor.visit_goto(*label, node.span, context),
        NodeKind::Label(label, stmt) => visitor.visit_label(*label, *stmt, node.span, context),
        NodeKind::Switch(condition, body) => visitor.visit_switch(*condition, *body, node.span, context),
        NodeKind::Case(expr, stmt) => visitor.visit_case(*expr, *stmt, node.span, context),
        NodeKind::CaseRange(start_expr, end_expr, stmt) => visitor.visit_case_range(*start_expr, *end_expr, *stmt, node.span, context),
        NodeKind::Default(stmt) => visitor.visit_default(*stmt, node.span, context),
        NodeKind::ExpressionStatement(expr) => visitor.visit_expression_statement(*expr, node.span, context),
        NodeKind::EmptyStatement => visitor.visit_empty_statement(node.span, context),
        NodeKind::Declaration(decl) => visitor.visit_declaration(decl, node.span, context),
        NodeKind::FunctionDef(func_def) => visitor.visit_function_def(func_def, node.span, context),
        NodeKind::EnumConstant(name, value_expr) => visitor.visit_enum_constant(*name, *value_expr, node.span, context),
        NodeKind::StaticAssert(condition, message) => visitor.visit_static_assert(*condition, *message, node.span, context),
        NodeKind::TranslationUnit(declarations) => visitor.visit_translation_unit(declarations, node.span, context),
        NodeKind::Dummy => visitor.visit_dummy(node.span, context),
    }
}

/// Get the child nodes for a given node that should be visited in traversal order.
/// Returns an empty vector for nodes that require special handling (e.g., FunctionDef).
pub fn get_child_nodes(node: &Node) -> Vec<NodeRef> {
    match &node.kind {
        NodeKind::TranslationUnit(nodes) => nodes.to_vec(),
        NodeKind::FunctionDef(_) => vec![], // Special handling
        NodeKind::CompoundStatement(nodes) => nodes.to_vec(),
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
            let mut children = vec![];
            if let Some(init) = for_stmt.init {
                children.push(init);
            }
            if let Some(condition) = for_stmt.condition {
                children.push(condition);
            }
            if let Some(increment) = for_stmt.increment {
                children.push(increment);
            }
            children.push(for_stmt.body);
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
        NodeKind::Return(expr) => expr.map_or(vec![], |e| vec![e]),
        NodeKind::UnaryOp(_, expr) => vec![*expr],
        NodeKind::Cast(_, expr) => vec![*expr],
        NodeKind::SizeOfExpr(expr) => vec![*expr],
        NodeKind::TernaryOp(cond, then_expr, else_expr) => vec![*cond, *then_expr, *else_expr],
        NodeKind::PostIncrement(expr) | NodeKind::PostDecrement(expr) => vec![*expr],
        NodeKind::MemberAccess(object, _, _) => vec![*object],
        NodeKind::IndexAccess(array, index) => vec![*array, *index],
        NodeKind::ExpressionStatement(expr) => expr.map_or(vec![], |e| vec![e]),
        NodeKind::EnumConstant(_, value_expr) => value_expr.map_or(vec![], |e| vec![e]),
        NodeKind::StaticAssert(condition, _) => vec![*condition],
        NodeKind::GnuStatementExpression(compound_stmt, result_expr) => vec![*compound_stmt, *result_expr],
        // Leaf nodes or nodes that don't need child traversal
        _ => vec![],
    }
}