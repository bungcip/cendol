//! Test cases for the type checker phase
//!
//! This module contains comprehensive tests for the type checker functionality,
//! including type inference, type unification, and error detection.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine};
use crate::semantic::SymbolTable;
use crate::semantic::type_checker::run_type_checker;

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_test_ast() -> (Ast, DiagnosticEngine, SymbolTable) {
        let ast = Ast::new();
        let diag = DiagnosticEngine::default();
        let symbol_table = SymbolTable::new();

        (ast, diag, symbol_table)
    }

    #[test]
    fn test_integer_literal_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create an integer literal node
        let int_node = Node::new(NodeKind::LiteralInt(42), SourceSpan::empty());
        let int_ref = ast.push_node(int_node);
        ast.set_root_node(int_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the resolved type is int
        let resolved_type = ast.get_node(int_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }

    #[test]
    fn test_float_literal_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create a float literal node
        let float_node = Node::new(NodeKind::LiteralFloat(3.14), SourceSpan::empty());
        let float_ref = ast.push_node(float_node);
        ast.set_root_node(float_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the resolved type is double
        let resolved_type = ast.get_node(float_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Double { is_long_double: false }));
    }

    #[test]
    fn test_char_literal_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create a character literal node
        let char_node = Node::new(NodeKind::LiteralChar(b'A'), SourceSpan::empty());
        let char_ref = ast.push_node(char_node);
        ast.set_root_node(char_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the resolved type is int (C character literals are int)
        let resolved_type = ast.get_node(char_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }

    #[test]
    fn test_string_literal_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create a string literal node
        let string_node = Node::new(NodeKind::LiteralString(Symbol::new("hello")), SourceSpan::empty());
        let string_ref = ast.push_node(string_node);
        ast.set_root_node(string_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the resolved type is char array
        let resolved_type = ast.get_node(string_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        if let TypeKind::Array { element_type, size } = &type_info.kind {
            let element_type_info = ast.get_type(*element_type);
            assert!(matches!(element_type_info.kind, TypeKind::Char { is_signed: true }));
            assert!(matches!(size, ArraySizeType::Incomplete));
        } else {
            panic!("Expected array type for string literal");
        }
    }

    #[test]
    fn test_binary_operation_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create two integer literals
        let left_node = Node::new(NodeKind::LiteralInt(10), SourceSpan::empty());
        let left_ref = ast.push_node(left_node);

        let right_node = Node::new(NodeKind::LiteralInt(20), SourceSpan::empty());
        let right_ref = ast.push_node(right_node);

        // Create a binary addition operation
        let bin_op_node = Node::new(
            NodeKind::BinaryOp(BinaryOp::Add, left_ref, right_ref),
            SourceSpan::empty(),
        );
        let bin_op_ref = ast.push_node(bin_op_node);
        ast.set_root_node(bin_op_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the binary operation has int type
        let resolved_type = ast.get_node(bin_op_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }

    #[test]
    fn test_unary_operation_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create an integer literal
        let operand_node = Node::new(NodeKind::LiteralInt(42), SourceSpan::empty());
        let operand_ref = ast.push_node(operand_node);

        // Create a unary minus operation
        let unary_node = Node::new(NodeKind::UnaryOp(UnaryOp::Minus, operand_ref), SourceSpan::empty());
        let unary_ref = ast.push_node(unary_node);
        ast.set_root_node(unary_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the unary operation has int type
        let resolved_type = ast.get_node(unary_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }

    #[test]
    fn test_identifier_resolution() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create a variable declaration first (this would normally be done by symbol resolver)
        let var_name = Symbol::new("test_var");
        let var_type = Type::new(TypeKind::Int { is_signed: true });
        let var_type_ref = ast.push_type(var_type);

        let var_node = Node::new(
            NodeKind::VarDecl(VarDeclData {
                name: var_name,
                ty: var_type_ref,
                storage: None,
                init: None,
            }),
            SourceSpan::empty(),
        );
        let _ = ast.push_node(var_node);

        // Create an identifier node
        let ident_node = Node::new(NodeKind::Ident(var_name), SourceSpan::empty());
        let ident_ref = ast.push_node(ident_node);
        ast.set_root_node(ident_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the identifier has the correct type
        let resolved_type = ast.get_node(ident_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }

    #[test]
    fn test_assignment_type_compatibility() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create an integer literal
        let int_node = Node::new(NodeKind::LiteralInt(42), SourceSpan::empty());
        let int_ref = ast.push_node(int_node);

        // Create a float literal
        let float_node = Node::new(NodeKind::LiteralFloat(3.14), SourceSpan::empty());
        let float_ref = ast.push_node(float_node);

        // Create an assignment (this would normally be part of a larger expression)
        let assign_node = Node::new(
            NodeKind::Assignment(BinaryOp::Assign, int_ref, float_ref),
            SourceSpan::empty(),
        );
        let assign_ref = ast.push_node(assign_node);
        ast.set_root_node(assign_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the assignment has the type of the left operand
        let resolved_type = ast.get_node(assign_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }

    #[test]
    fn test_error_handling_undeclared_identifier() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create an identifier that doesn't exist
        let unknown_name = Symbol::new("unknown_var");
        let ident_node = Node::new(NodeKind::Ident(unknown_name), SourceSpan::empty());
        let ident_ref = ast.push_node(ident_node);
        ast.set_root_node(ident_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that an error was reported
        assert!(diag.has_errors());

        // Check that the identifier has error type
        let resolved_type = ast.get_node(ident_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Error));
    }

    #[test]
    fn test_complex_expression_type() {
        let (mut ast, mut diag, mut symbol_table) = setup_test_ast();

        // Create a complex expression: (10 + 20) * 2
        let ten_node = Node::new(NodeKind::LiteralInt(10), SourceSpan::empty());
        let ten_ref = ast.push_node(ten_node);

        let twenty_node = Node::new(NodeKind::LiteralInt(20), SourceSpan::empty());
        let twenty_ref = ast.push_node(twenty_node);

        let add_node = Node::new(
            NodeKind::BinaryOp(BinaryOp::Add, ten_ref, twenty_ref),
            SourceSpan::empty(),
        );
        let add_ref = ast.push_node(add_node);

        let two_node = Node::new(NodeKind::LiteralInt(2), SourceSpan::empty());
        let two_ref = ast.push_node(two_node);

        let mul_node = Node::new(NodeKind::BinaryOp(BinaryOp::Mul, add_ref, two_ref), SourceSpan::empty());
        let mul_ref = ast.push_node(mul_node);
        ast.set_root_node(mul_ref);

        // Run type checker
        run_type_checker(&mut ast, &mut diag, &mut symbol_table);

        // Check that the final result has int type
        let resolved_type = ast.get_node(mul_ref).resolved_type.get().unwrap();
        let type_info = ast.get_type(resolved_type);

        assert!(matches!(type_info.kind, TypeKind::Int { is_signed: true }));
    }
}
