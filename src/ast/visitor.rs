//! AST Visitor pattern implementation.
//!
//! This module defines the visitor traits (`AstVisitor` and `AstMutVisitor`) for
//! traversing and transforming the AST. The visitor pattern allows for clean
//! separation of algorithms from the AST structure.

use std::cell::Cell;

use crate::ast::nodes::*;
use crate::ast::*;

/// Trait for visiting AST nodes during analysis.
/// Each method corresponds to a NodeKind variant and allows
/// analysis phases to perform specific operations on each node type.
///
/// This is the immutable visitor - it cannot modify the AST.
pub trait AstVisitor<'ast> {
    /// Context passed to visitor methods
    type Context;

    // --- Literals ---
    fn visit_literal_int(&mut self, _value: i64, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_literal_float(&mut self, _value: f64, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_literal_string(&mut self, _value: Symbol, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_literal_char(&mut self, _value: u8, _span: SourceSpan, _context: &mut Self::Context) {}

    // --- Expressions ---
    fn visit_ident(
        &mut self,
        _name: Symbol,
        _resolved_symbol: &Cell<Option<SymbolEntryRef>>,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_unary_op(&mut self, _op: UnaryOp, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_binary_op(
        &mut self,
        _op: BinaryOp,
        _left: NodeRef,
        _right: NodeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_ternary_op(
        &mut self,
        _cond: NodeRef,
        _then_expr: NodeRef,
        _else_expr: NodeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_post_increment(&mut self, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_post_decrement(&mut self, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_assignment(
        &mut self,
        _op: BinaryOp,
        _lhs: NodeRef,
        _rhs: NodeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_function_call(
        &mut self,
        _func: NodeRef,
        _args: &[NodeRef],
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_member_access(
        &mut self,
        _object: NodeRef,
        _field: Symbol,
        _is_arrow: bool,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_index_access(
        &mut self,
        _array: NodeRef,
        _index: NodeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_cast(&mut self, _target_type: TypeRef, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_sizeof_expr(&mut self, _expr: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_sizeof_type(&mut self, _target_type: TypeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_alignof(&mut self, _target_type: TypeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_compound_literal(
        &mut self,
        _type_ref: TypeRef,
        _initializer: InitializerRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_generic_selection(
        &mut self,
        _controlling_expr: NodeRef,
        _associations: &[GenericAssociation],
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_va_arg(
        &mut self,
        _va_list_expr: NodeRef,
        _type_ref: TypeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_gnu_statement_expression(
        &mut self,
        _compound_stmt: NodeRef,
        _result_expr: NodeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }

    // --- Statements ---
    fn visit_compound_statement(&mut self, _statements: &[NodeRef], _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_if(&mut self, _stmt: &IfStmt, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_while(&mut self, _stmt: &WhileStmt, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_do_while(&mut self, _body: NodeRef, _condition: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {
    }
    fn visit_for(&mut self, _stmt: &ForStmt, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_return(&mut self, _expr: Option<NodeRef>, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_break(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_continue(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_goto(&mut self, _label: Symbol, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_label(&mut self, _label: Symbol, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_switch(&mut self, _condition: NodeRef, _body: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_case(&mut self, _expr: NodeRef, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_case_range(
        &mut self,
        _start_expr: NodeRef,
        _end_expr: NodeRef,
        _stmt: NodeRef,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_default(&mut self, _stmt: NodeRef, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_expression_statement(&mut self, _expr: Option<NodeRef>, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_empty_statement(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}

    // --- Declarations ---
    fn visit_declaration(&mut self, _decl: &DeclarationData, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_function_def(&mut self, _func_def: &FunctionDefData, _span: SourceSpan, _context: &mut Self::Context) {}
    fn visit_enum_constant(
        &mut self,
        _name: Symbol,
        _value_expr: Option<NodeRef>,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }
    fn visit_static_assert(
        &mut self,
        _condition: NodeRef,
        _message: Symbol,
        _span: SourceSpan,
        _context: &mut Self::Context,
    ) {
    }

    // --- Top Level ---
    fn visit_translation_unit(&mut self, _declarations: &[NodeRef], _span: SourceSpan, _context: &mut Self::Context) {}

    // --- Special ---
    fn visit_dummy(&mut self, _span: SourceSpan, _context: &mut Self::Context) {}
}

/// Mutable visitor trait for transforming the AST.
/// This allows visitors to modify nodes in place.
pub trait AstMutVisitor<'ast> {
    /// Context passed to visitor methods
    type Context;

    // Same methods as AstVisitor but with &mut self for potential mutation
    // For brevity, only showing a few - in practice, all methods would be duplicated

    fn visit_literal_int(&mut self, _value: i64, _span: SourceSpan, _context: &mut Self::Context) -> i64 {
        _value
    }
    fn visit_literal_float(&mut self, _value: f64, _span: SourceSpan, _context: &mut Self::Context) -> f64 {
        _value
    }
    // ... other methods would return modified values or references

    // For statements that contain other nodes, return modified versions
    fn visit_if(&mut self, _stmt: &IfStmt, _span: SourceSpan, _context: &mut Self::Context) -> IfStmt {
        _stmt.clone() // Default: return unchanged
    }

    // Add all other methods similarly...
}

/// Helper function to dispatch a node to the appropriate visitor method
pub fn visit_node<'ast, V: AstVisitor<'ast>>(
    visitor: &mut V,
    ast: &'ast Ast,
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
        NodeKind::TernaryOp(cond, then_expr, else_expr) => {
            visitor.visit_ternary_op(*cond, *then_expr, *else_expr, node.span, context)
        }
        NodeKind::PostIncrement(expr) => visitor.visit_post_increment(*expr, node.span, context),
        NodeKind::PostDecrement(expr) => visitor.visit_post_decrement(*expr, node.span, context),
        NodeKind::Assignment(op, lhs, rhs) => visitor.visit_assignment(*op, *lhs, *rhs, node.span, context),
        NodeKind::FunctionCall(func, args) => visitor.visit_function_call(*func, args, node.span, context),
        NodeKind::MemberAccess(object, field, is_arrow) => {
            visitor.visit_member_access(*object, *field, *is_arrow, node.span, context)
        }
        NodeKind::IndexAccess(array, index) => visitor.visit_index_access(*array, *index, node.span, context),
        NodeKind::Cast(target_type, expr) => visitor.visit_cast(*target_type, *expr, node.span, context),
        NodeKind::SizeOfExpr(expr) => visitor.visit_sizeof_expr(*expr, node.span, context),
        NodeKind::SizeOfType(target_type) => visitor.visit_sizeof_type(*target_type, node.span, context),
        NodeKind::AlignOf(target_type) => visitor.visit_alignof(*target_type, node.span, context),
        NodeKind::CompoundLiteral(type_ref, initializer) => {
            visitor.visit_compound_literal(*type_ref, *initializer, node.span, context)
        }
        NodeKind::GenericSelection(controlling_expr, associations) => {
            visitor.visit_generic_selection(*controlling_expr, associations, node.span, context)
        }
        NodeKind::VaArg(va_list_expr, type_ref) => visitor.visit_va_arg(*va_list_expr, *type_ref, node.span, context),
        NodeKind::GnuStatementExpression(compound_stmt, result_expr) => {
            visitor.visit_gnu_statement_expression(*compound_stmt, *result_expr, node.span, context)
        }
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
        NodeKind::CaseRange(start_expr, end_expr, stmt) => {
            visitor.visit_case_range(*start_expr, *end_expr, *stmt, node.span, context)
        }
        NodeKind::Default(stmt) => visitor.visit_default(*stmt, node.span, context),
        NodeKind::ExpressionStatement(expr) => visitor.visit_expression_statement(*expr, node.span, context),
        NodeKind::EmptyStatement => visitor.visit_empty_statement(node.span, context),
        NodeKind::Declaration(decl) => visitor.visit_declaration(decl, node.span, context),
        NodeKind::FunctionDef(func_def) => visitor.visit_function_def(func_def, node.span, context),
        NodeKind::EnumConstant(name, value_expr) => visitor.visit_enum_constant(*name, *value_expr, node.span, context),
        NodeKind::StaticAssert(condition, message) => {
            visitor.visit_static_assert(*condition, *message, node.span, context)
        }
        NodeKind::TranslationUnit(declarations) => visitor.visit_translation_unit(declarations, node.span, context),
        NodeKind::Dummy => visitor.visit_dummy(node.span, context),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Ast;
    use crate::source_manager::SourceSpan;
    use std::cell::Cell;

    struct TestVisitor {
        visited_nodes: Vec<String>,
    }

    impl<'ast> AstVisitor<'ast> for TestVisitor {
        type Context = ();

        fn visit_literal_int(&mut self, value: i64, _: SourceSpan, _: &mut Self::Context) {
            self.visited_nodes.push(format!("LiteralInt({})", value));
        }

        fn visit_binary_op(&mut self, op: BinaryOp, _: NodeRef, _: NodeRef, _: SourceSpan, _: &mut Self::Context) {
            self.visited_nodes.push(format!("BinaryOp({:?})", op));
        }

        fn visit_ident(
            &mut self,
            name: Symbol,
            _: &Cell<Option<SymbolEntryRef>>,
            _: SourceSpan,
            _: &mut Self::Context,
        ) {
            self.visited_nodes.push(format!("Ident({})", name));
        }

        fn visit_function_def(&mut self, _: &FunctionDefData, _: SourceSpan, _: &mut Self::Context) {
            self.visited_nodes.push("FunctionDef".to_string());
        }

        fn visit_compound_statement(&mut self, _: &[NodeRef], _: SourceSpan, _: &mut Self::Context) {
            self.visited_nodes.push("CompoundStatement".to_string());
        }

        fn visit_return(&mut self, _: Option<NodeRef>, _: SourceSpan, _: &mut Self::Context) {
            self.visited_nodes.push("Return".to_string());
        }
    }

    #[test]
    fn test_walk_ast() {
        let mut ast = Ast::new();

        // Create a simple function definition: int main() { return 1 + 2; }
        let lit1 = ast.push_node(Node::new(NodeKind::LiteralInt(1), SourceSpan::empty()));
        let lit2 = ast.push_node(Node::new(NodeKind::LiteralInt(2), SourceSpan::empty()));
        let add_expr = ast.push_node(Node::new(
            NodeKind::BinaryOp(BinaryOp::Add, lit1, lit2),
            SourceSpan::empty(),
        ));
        let return_stmt = ast.push_node(Node::new(NodeKind::Return(Some(add_expr)), SourceSpan::empty()));
        let compound_stmt = ast.push_node(Node::new(
            NodeKind::CompoundStatement(vec![return_stmt]),
            SourceSpan::empty(),
        ));

        let func_def_data = FunctionDefData {
            specifiers: vec![DeclSpecifier::TypeSpecifier(TypeSpecifier::Int)].into(),
            declarator: Declarator::Identifier(
                "main".into(),
                Default::default(),
                Some(Box::new(Declarator::Function(
                    Box::new(Declarator::Abstract),
                    vec![].into(),
                ))),
            ),
            body: compound_stmt,
        };

        let func_def = ast.push_node(Node::new(NodeKind::FunctionDef(func_def_data), SourceSpan::empty()));

        let mut visitor = TestVisitor {
            visited_nodes: Vec::new(),
        };

        walk_ast(&mut visitor, &ast, func_def, &mut ());

        let expected_nodes = vec![
            "FunctionDef",
            "CompoundStatement",
            "Return",
            "BinaryOp(Add)",
            "LiteralInt(1)",
            "LiteralInt(2)",
        ];

        assert_eq!(visitor.visited_nodes, expected_nodes);
    }
}

fn walk_declarator<'ast, V: AstVisitor<'ast>>(
    visitor: &mut V,
    ast: &'ast Ast,
    declarator: &Declarator,
    context: &mut V::Context,
) {
    match declarator {
        Declarator::Identifier(_, _, Some(d)) => {
            walk_declarator(visitor, ast, d, context);
        }
        Declarator::Pointer(_, Some(d)) => {
            walk_declarator(visitor, ast, d, context);
        }
        Declarator::Array(d, size) => {
            walk_declarator(visitor, ast, d, context);
            match size {
                ArraySize::Expression { expr, .. } => {
                    walk_ast(visitor, ast, *expr, context);
                }
                ArraySize::VlaSpecifier { size: Some(s), .. } => {
                    walk_ast(visitor, ast, *s, context);
                }
                _ => {}
            }
        }
        Declarator::Function(d, params) => {
            walk_declarator(visitor, ast, d, context);
            for p in params {
                if let Some(decl) = &p.declarator {
                    walk_declarator(visitor, ast, decl, context);
                }
            }
        }
        _ => {}
    }
}

fn walk_initializer<'ast, V: AstVisitor<'ast>>(
    visitor: &mut V,
    ast: &'ast Ast,
    initializer: &Initializer,
    context: &mut V::Context,
) {
    match initializer {
        Initializer::Expression(expr) => {
            walk_ast(visitor, ast, *expr, context);
        }
        Initializer::List(list) => {
            for item in list {
                for designator in &item.designation {
                    if let Designator::ArrayIndex(expr) = designator {
                        walk_ast(visitor, ast, *expr, context);
                    }
                }
                walk_initializer(visitor, ast, &item.initializer, context);
            }
        }
    }
}

/// Helper function for walking the AST with a visitor
pub fn walk_ast<'ast, V: AstVisitor<'ast>>(
    visitor: &mut V,
    ast: &'ast Ast,
    node_ref: NodeRef,
    context: &mut V::Context,
) {
    // Visit the current node
    visit_node(visitor, ast, node_ref, context);

    // Recursively visit children based on node type
    let node = ast.get_node(node_ref);

    match &node.kind {
        // Expressions
        NodeKind::UnaryOp(_, expr)
        | NodeKind::PostIncrement(expr)
        | NodeKind::PostDecrement(expr)
        | NodeKind::SizeOfExpr(expr) => {
            walk_ast(visitor, ast, *expr, context);
        }
        NodeKind::BinaryOp(_, left, right)
        | NodeKind::Assignment(_, left, right)
        | NodeKind::IndexAccess(left, right) => {
            walk_ast(visitor, ast, *left, context);
            walk_ast(visitor, ast, *right, context);
        }
        NodeKind::TernaryOp(cond, then, else_) => {
            walk_ast(visitor, ast, *cond, context);
            walk_ast(visitor, ast, *then, context);
            walk_ast(visitor, ast, *else_, context);
        }
        NodeKind::FunctionCall(func, args) => {
            walk_ast(visitor, ast, *func, context);
            for &arg in args {
                walk_ast(visitor, ast, arg, context);
            }
        }
        NodeKind::MemberAccess(object, ..) => {
            walk_ast(visitor, ast, *object, context);
        }
        NodeKind::Cast(_, expr) => {
            walk_ast(visitor, ast, *expr, context);
        }
        NodeKind::GenericSelection(controlling_expr, associations) => {
            walk_ast(visitor, ast, *controlling_expr, context);
            for assoc in associations {
                walk_ast(visitor, ast, assoc.result_expr, context);
            }
        }
        NodeKind::VaArg(va_list, _) => {
            walk_ast(visitor, ast, *va_list, context);
        }
        NodeKind::CompoundLiteral(_, initializer_ref) => {
            let initializer = ast.get_initializer(*initializer_ref);
            walk_initializer(visitor, ast, initializer, context);
        }
        NodeKind::GnuStatementExpression(compound_stmt, result_expr) => {
            walk_ast(visitor, ast, *compound_stmt, context);
            walk_ast(visitor, ast, *result_expr, context);
        }

        // Statements
        NodeKind::CompoundStatement(items) => {
            for &item in items {
                walk_ast(visitor, ast, item, context);
            }
        }
        NodeKind::If(if_stmt) => {
            walk_ast(visitor, ast, if_stmt.condition, context);
            walk_ast(visitor, ast, if_stmt.then_branch, context);
            if let Some(else_branch) = if_stmt.else_branch {
                walk_ast(visitor, ast, else_branch, context);
            }
        }
        NodeKind::While(while_stmt) => {
            walk_ast(visitor, ast, while_stmt.condition, context);
            walk_ast(visitor, ast, while_stmt.body, context);
        }
        NodeKind::DoWhile(body, condition) => {
            walk_ast(visitor, ast, *body, context);
            walk_ast(visitor, ast, *condition, context);
        }
        NodeKind::For(for_stmt) => {
            if let Some(init) = for_stmt.init {
                walk_ast(visitor, ast, init, context);
            }
            if let Some(cond) = for_stmt.condition {
                walk_ast(visitor, ast, cond, context);
            }
            if let Some(inc) = for_stmt.increment {
                walk_ast(visitor, ast, inc, context);
            }
            walk_ast(visitor, ast, for_stmt.body, context);
        }
        NodeKind::Return(expr) => {
            if let Some(e) = expr {
                walk_ast(visitor, ast, *e, context);
            }
        }
        NodeKind::Label(_, stmt) | NodeKind::Default(stmt) => {
            walk_ast(visitor, ast, *stmt, context);
        }
        NodeKind::Switch(cond, body) => {
            walk_ast(visitor, ast, *cond, context);
            walk_ast(visitor, ast, *body, context);
        }
        NodeKind::Case(expr, stmt) => {
            walk_ast(visitor, ast, *expr, context);
            walk_ast(visitor, ast, *stmt, context);
        }
        NodeKind::CaseRange(start, end, stmt) => {
            walk_ast(visitor, ast, *start, context);
            walk_ast(visitor, ast, *end, context);
            walk_ast(visitor, ast, *stmt, context);
        }
        NodeKind::ExpressionStatement(expr) => {
            if let Some(e) = expr {
                walk_ast(visitor, ast, *e, context);
            }
        }

        // Declarations
        NodeKind::Declaration(decl) => {
            for init_declarator in &decl.init_declarators {
                if let Some(initializer) = &init_declarator.initializer {
                    walk_initializer(visitor, ast, initializer, context);
                }
                walk_declarator(visitor, ast, &init_declarator.declarator, context);
            }
        }
        NodeKind::FunctionDef(func_def) => {
            walk_declarator(visitor, ast, &func_def.declarator, context);
            walk_ast(visitor, ast, func_def.body, context);
        }
        NodeKind::EnumConstant(_, value) => {
            if let Some(v) = value {
                walk_ast(visitor, ast, *v, context);
            }
        }
        NodeKind::StaticAssert(cond, _) => {
            walk_ast(visitor, ast, *cond, context);
        }

        // Top Level
        NodeKind::TranslationUnit(decls) => {
            for &decl in decls {
                walk_ast(visitor, ast, decl, context);
            }
        }

        // Literals, Idents, Simple statements - no children to walk
        NodeKind::LiteralInt(_)
        | NodeKind::LiteralFloat(_)
        | NodeKind::LiteralString(_)
        | NodeKind::LiteralChar(_)
        | NodeKind::Ident(_, _)
        | NodeKind::SizeOfType(_)
        | NodeKind::AlignOf(_)
        | NodeKind::Break
        | NodeKind::Continue
        | NodeKind::Goto(_)
        | NodeKind::EmptyStatement
        | NodeKind::Dummy => {}
    }
}
