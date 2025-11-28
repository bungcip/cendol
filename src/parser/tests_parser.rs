#![cfg(test)]
use crate::ast::{Ast, Node};
use crate::diagnostic::DiagnosticEngine;
use crate::lang_options::LangOptions;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::pp::Preprocessor;
use crate::source_manager::SourceManager;
use target_lexicon::Triple;

fn parse_expression(source: &str) -> (Ast, Node) {
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::new();
    let lang_opts = LangOptions::c11();
    let target_info = Triple::unknown();
    let source_id = sm.add_file("test.c", source);

    let mut pp = Preprocessor::new(
        &mut sm,
        &mut diag,
        lang_opts.clone(),
        target_info.clone(),
        &crate::pp::PreprocessorConfig {
            max_include_depth: 200,
            system_include_paths: Vec::new(),
        },
    );
    let pp_tokens = pp.process(source_id, &Default::default()).unwrap();

    let mut lexer = Lexer::new(&sm, &mut diag, &lang_opts, &target_info, &pp_tokens);
    let tokens = lexer.tokenize_all();

    let mut ast = Ast::new();
    let mut parser = Parser::new(&tokens, &mut ast, &mut diag);
    let expr_result = parser.parse_expression(crate::parser::BindingPower::MIN);
    assert!(diag.diagnostics.is_empty());

    match expr_result {
        Ok(crate::parser::ParseExprOutput::Expression(node_ref)) => {
            let node = ast.get_node(node_ref).clone();
            (ast, node)
        }
        _ => panic!("Expected expression"),
    }
}

#[test]
fn test_simple_addition() {
    let (_ast, node) = parse_expression("1 + 2");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    BinaryOp:
      - Add
      - 1
      - 2
    ");
}

#[test]
fn test_unary_operators() {
    let (_ast, node) = parse_expression("-1");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    UnaryOp:
      - Minus
      - 1
    ");
}

#[test]
fn test_precedence() {
    let (_ast, node) = parse_expression("1 + 2 * 3");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    BinaryOp:
      - Add
      - 1
      - 4
    ");
}

#[test]
fn test_parenthesized_expression() {
    let (_ast, node) = parse_expression("(1 + 2) * 3");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    BinaryOp:
      - Mul
      - 3
      - 4
    ");
}

#[test]
fn test_assignment() {
    let (_ast, node) = parse_expression("a = 1");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    BinaryOp:
      - Assign
      - 1
      - 2
    ");
}

#[test]
fn test_function_call() {
    let (_ast, node) = parse_expression("foo(1, 2)");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    FunctionCall:
      - 1
      - - 4
    ");
}

#[test]
fn test_member_access() {
    let (_ast, node) = parse_expression("a.b");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    MemberAccess:
      - 1
      - b
      - false
    ");
}

#[test]
fn test_array_indexing() {
    let (_ast, node) = parse_expression("a[1]");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    IndexAccess:
      - 1
      - 2
    ");
}

#[test]
fn test_sizeof_expression() {
    let (_ast, node) = parse_expression("sizeof(a)");
    insta::assert_yaml_snapshot!(&node.kind, @"SizeOfExpr: 1");
}

#[test]
fn test_complex_expression() {
    let (_ast, node) = parse_expression("a + b * c[d] - e.f");
    insta::assert_yaml_snapshot!(&node.kind, @r"
    BinaryOp:
      - Add
      - 1
      - 9
    ");
}
