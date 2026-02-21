use crate::parser::declarations;
use crate::parser::statements::parse_compound_statement;
use crate::tests::parser_utils::{resolve_node, setup_compound, setup_source, setup_statement};

#[test]
fn test_label_with_expression_statement() {
    let resolved = setup_statement("start: x = 1;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - start
      - ExpressionStatement:
          Assignment:
            - Assign
            - Ident: x
            - LiteralInt: 1
    ");
}

#[test]
fn test_label_with_compound_statement() {
    let resolved = setup_statement("block: { int x = 1; }");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - block
      - CompoundStatement:
          - Declaration:
              specifiers:
                - int
              init_declarators:
                - name: x
                  initializer:
                    LiteralInt: 1
    ");
}

#[test]
fn test_label_with_if_statement() {
    let resolved = setup_statement("if_label: if (x) y = 1;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - if_label
      - If:
          - Ident: x
          - ExpressionStatement:
              Assignment:
                - Assign
                - Ident: y
                - LiteralInt: 1
          - ~
    ");
}

#[test]
fn test_label_with_while_loop() {
    let resolved = setup_statement("loop_start: while (x < 10) x++;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - loop_start
      - While:
          - BinaryOp:
              - Less
              - Ident: x
              - LiteralInt: 10
          - ExpressionStatement:
              PostIncrement:
                Ident: x
    ");
}

#[test]
fn test_multiple_labels_sequence() {
    // Test consecutive labels (like "next:" and "foo:" in the goto test)
    let resolved = setup_statement("label1: label2: return 0;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - label1
      - Label:
          - label2
          - Return:
              LiteralInt: 0
    ");
}

#[test]
fn test_goto_with_complex_label_name() {
    let resolved = setup_statement("goto error_handler_1;");
    insta::assert_yaml_snapshot!(&resolved, @"Goto: error_handler_1");
}

#[test]
fn test_label_followed_by_goto() {
    let resolved = setup_statement("target: goto target;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - target
      - Goto: target
    ");
}

#[test]
fn test_label_with_numeric_suffix() {
    let resolved = setup_statement("_label123: return 1;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - _label123
      - Return:
          LiteralInt: 1
    ");
}

#[test]
fn test_label_followed_by_compound_statement_with_declaration() {
    let resolved = setup_statement("declare: { int x = 5; }");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - declare
      - CompoundStatement:
          - Declaration:
              specifiers:
                - int
              init_declarators:
                - name: x
                  initializer:
                    LiteralInt: 5
    ");
}

#[test]
fn test_label_followed_by_function_call() {
    let resolved = setup_statement("call_func: foo();");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - call_func
      - ExpressionStatement:
          FunctionCall:
            - Ident: foo
            - []
    ");
}

#[test]
fn test_label_with_break_statement() {
    let resolved = setup_statement("break_point: break;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - break_point
      - Break
    ");
}

#[test]
fn test_label_with_continue_statement() {
    let resolved = setup_statement("continue_loop: continue;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - continue_loop
      - Continue
    ");
}

#[test]
fn test_label_followed_by_empty_statement() {
    let resolved = setup_statement("empty: ;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Label:
      - empty
      - Empty
    ");
}

#[test]
fn test_multiple_statements_with_labels() {
    // This tests a more complex scenario with multiple labels and statements
    // We test that the parser can handle multiple labeled statements
    let source = r"
    success:
      0;
      return 0;
    next:
    foo:  
      goto success;
      return 1;";
    let resolved = setup_compound(source);

    // Just verify it parses as a label
    insta::assert_yaml_snapshot!(&resolved, @r"
    CompoundStatement:
      - Label:
          - success
          - ExpressionStatement:
              LiteralInt: 0
      - Return:
          LiteralInt: 0
      - Label:
          - next
          - Label:
              - foo
              - Goto: success
      - Return:
          LiteralInt: 1
    ");
}

#[test]
fn test_case_range_statement() {
    let resolved = setup_statement("case 1 ... 10: x = 1;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    CaseRange:
      - LiteralInt: 1
      - LiteralInt: 10
      - ExpressionStatement:
          Assignment:
            - Assign
            - Ident: x
            - LiteralInt: 1
    ");
}

#[test]
fn test_ambiguous_compound_statement() {
    // This looks like it could be a declaration `T x;` if T is a typedef,
    // or a multiplication `T * x;` if T is an identifier.
    // However, since T is not defined as a typedef, it should be parsed as an Expression statement.
    // The `parse_compound_statement` logic tries declaration first, fails, then tries statement.
    let source = "T * x;";
    let resolved = setup_compound(source);
    insta::assert_yaml_snapshot!(&resolved, @r"
    CompoundStatement:
      - ExpressionStatement:
          BinaryOp:
            - Mul
            - Ident: T
            - Ident: x
    ");
}

#[test]
fn test_ambiguous_compound_statement_with_typedef() {
    // Here we define T as a typedef.
    // Inside the block, `T x;` should be parsed as a declaration.
    let source = "typedef int T; { T x; }";
    let (ast, stmt_result) = setup_source(source, |parser| {
        // Parse the typedef first
        let _ = declarations::parse_declaration(parser).unwrap();
        // Then parse the compound statement
        parse_compound_statement(parser)
    });

    let resolved = match stmt_result {
        Ok((node_ref, _)) => resolve_node(&ast, node_ref),
        _ => panic!("Expected multi statement block"),
    };

    insta::assert_yaml_snapshot!(&resolved, @r#"
    CompoundStatement:
      - Declaration:
          specifiers:
            - "TypedefName(\"T\")"
          init_declarators:
            - name: x
    "#);
}

#[test]
fn test_compound_statement_error_recovery() {
    let source = "int main() { int 1; }";
    crate::tests::test_utils::run_fail_with_message(
        source,
        "expected Expected declarator or identifier after type specifier",
    );
}

#[test]
fn test_for_statement_with_declaration() {
    let source = "for (int i = 0; i < 10; i++) {}";
    let resolved = setup_statement(source);
    insta::assert_yaml_snapshot!(&resolved, @r"
    For:
      - Declaration:
          specifiers:
            - int
          init_declarators:
            - name: i
              initializer:
                LiteralInt: 0
      - BinaryOp:
          - Less
          - Ident: i
          - LiteralInt: 10
      - PostIncrement:
          Ident: i
      - CompoundStatement: []
    ");
}
#[test]
fn test_for_statement_with_declaration_no_init() {
    let source = "for (int i; i < 10; i++) {}";
    let resolved = setup_statement(source);
    insta::assert_yaml_snapshot!(&resolved, @r"
    For:
      - Declaration:
          specifiers:
            - int
          init_declarators:
            - name: i
      - BinaryOp:
          - Less
          - Ident: i
          - LiteralInt: 10
      - PostIncrement:
          Ident: i
      - CompoundStatement: []
    ");
}
