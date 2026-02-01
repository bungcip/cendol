use crate::tests::parser_utils::setup_expr;

#[test]
fn test_simple_addition() {
    let resolved = setup_expr("1 + 2");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - LiteralInt: 1
      - LiteralInt: 2
    ");
}

#[test]
fn test_generic_selection_with_assignment() {
    let resolved = setup_expr("_Generic(x = 10, int: 1, default: 0)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Assignment:
          - Assign
          - Ident: x
          - LiteralInt: 10
      - - type_name: type_1
          result_expr:
            LiteralInt: 1
        - type_name: ~
          result_expr:
            LiteralInt: 0
    ");
}

#[test]
fn test_unary_operators() {
    let resolved = setup_expr("-1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    UnaryOp:
      - Minus
      - LiteralInt: 1
    ");
}

#[test]
fn test_precedence() {
    let resolved = setup_expr("1 + 2 * 3");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - LiteralInt: 1
      - BinaryOp:
          - Mul
          - LiteralInt: 2
          - LiteralInt: 3
    ");
}

#[test]
fn test_parenthesized_expression() {
    let resolved = setup_expr("(1 + 2) * 3");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Mul
      - BinaryOp:
          - Add
          - LiteralInt: 1
          - LiteralInt: 2
      - LiteralInt: 3
    ");
}

#[test]
fn test_assignment() {
    let resolved = setup_expr("a = 1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Assignment:
      - Assign
      - Ident: a
      - LiteralInt: 1
    ");
}

#[test]
fn test_function_call() {
    let resolved = setup_expr("foo(1, 2)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    FunctionCall:
      - Ident: foo
      - - LiteralInt: 1
        - LiteralInt: 2
    ");
}

#[test]
fn test_member_access() {
    let resolved = setup_expr("a.b");
    insta::assert_yaml_snapshot!(&resolved, @r"
    MemberAccess:
      - Ident: a
      - b
      - false
    ");
}

#[test]
fn test_array_indexing() {
    let resolved = setup_expr("a[1]");
    insta::assert_yaml_snapshot!(&resolved, @r"
    IndexAccess:
      - Ident: a
      - LiteralInt: 1
    ");
}

#[test]
fn test_sizeof_expression() {
    let resolved = setup_expr("sizeof(a)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    SizeOfExpr:
      Ident: a
    ");
}

#[test]
fn test_complex_expression() {
    let resolved = setup_expr("a + b * c[d] - e.f");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Sub
      - BinaryOp:
          - Add
          - Ident: a
          - BinaryOp:
              - Mul
              - Ident: b
              - IndexAccess:
                  - Ident: c
                  - Ident: d
      - MemberAccess:
          - Ident: e
          - f
          - false
    ");
}

#[test]
fn test_attribute_in_cast() {
    let resolved = setup_expr("(__attribute__((__noinline__)) int) 1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Cast:
      - parsed_type_1_1
      - LiteralInt: 1
    ");
}

#[test]
fn test_gnu_statement_expression() {
    let resolved = setup_expr("({ int x = 1; x + 2; })");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GnuStatementExpression:
      - CompoundStatement:
          - Declaration:
              specifiers:
                - int
              init_declarators:
                - name: x
                  initializer:
                    LiteralInt: 1
          - ExpressionStatement:
              BinaryOp:
                - Add
                - Ident: x
                - LiteralInt: 2
      - BinaryOp:
          - Add
          - Ident: x
          - LiteralInt: 2
    ");
}

#[test]
fn test_generic_selection_simple() {
    let resolved = setup_expr("_Generic(a, int: a_f)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: a
      - - type_name: type_1
          result_expr:
            Ident: a_f
    ");
}

#[test]
fn test_generic_selection_with_multiple_associations() {
    let resolved = setup_expr("_Generic(a, int: a_f, const int: b_f)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: a
      - - type_name: type_1
          result_expr:
            Ident: a_f
        - type_name: type_2
          result_expr:
            Ident: b_f
    ");
}

#[test]
fn test_generic_selection_with_default() {
    let resolved = setup_expr("_Generic(a, int: a_f, default: b_f)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: a
      - - type_name: type_1
          result_expr:
            Ident: a_f
        - type_name: ~
          result_expr:
            Ident: b_f
    ");
}

#[test]
fn test_generic_selection_with_function_call() {
    let resolved = setup_expr("_Generic(a, int: a_f)()");
    insta::assert_yaml_snapshot!(&resolved, @r"
    FunctionCall:
      - GenericSelection:
          - Ident: a
          - - type_name: type_1
              result_expr:
                Ident: a_f
      - []
    ");
}

#[test]
fn test_generic_selection_with_qualified_type() {
    let resolved = setup_expr("_Generic(i, const int: 1/1, default: 0)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: i
      - - type_name: type_1
          result_expr:
            BinaryOp:
              - Div
              - LiteralInt: 1
              - LiteralInt: 1
        - type_name: ~
          result_expr:
            LiteralInt: 0
    ");
}

#[test]
fn test_generic_selection_with_pointer_types() {
    let resolved = setup_expr("_Generic(ptr, int *:1, int * const:2, default:20)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    GenericSelection:
      - Ident: ptr
      - - type_name: type_1
          result_expr:
            LiteralInt: 1
        - type_name: type_2
          result_expr:
            LiteralInt: 2
        - type_name: ~
          result_expr:
            LiteralInt: 20
    ");
}

#[test]
fn test_chained_assignment() {
    let resolved = setup_expr("a = b = c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Assignment:
      - Assign
      - Ident: a
      - Assignment:
          - Assign
          - Ident: b
          - Ident: c
    ");
}

#[test]
fn test_ternary_with_assignment() {
    let resolved = setup_expr("a ? b : c = 1");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Assignment:
      - Assign
      - TernaryOp:
          - Ident: a
          - Ident: b
          - Ident: c
      - LiteralInt: 1
    ");
}

#[test]
fn test_ternary_with_assignment_in_middle_operand() {
    let resolved = setup_expr("a ? b = 1 : c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    TernaryOp:
      - Ident: a
      - Assignment:
          - Assign
          - Ident: b
          - LiteralInt: 1
      - Ident: c
    ");
}

#[test]
fn test_chained_subtraction() {
    let resolved = setup_expr("a - b - c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Sub
      - BinaryOp:
          - Sub
          - Ident: a
          - Ident: b
      - Ident: c
    ");
}

#[test]
fn test_array_indexing_with_expression() {
    let resolved = setup_expr("a[b + c]");
    insta::assert_yaml_snapshot!(&resolved, @r"
    IndexAccess:
      - Ident: a
      - BinaryOp:
          - Add
          - Ident: b
          - Ident: c
    ");
}

#[test]
fn test_compound_literal() {
    let resolved = setup_expr("(int){1}");
    insta::assert_yaml_snapshot!(&resolved, @r"
    CompoundLiteral:
      - parsed_type_1
      - InitializerList:
          - LiteralInt: 1
    ");
}

#[test]
fn test_compound_literal_struct() {
    let resolved = setup_expr("(struct Point){.x=1, .y=2}");
    insta::assert_yaml_snapshot!(&resolved, @r"
    CompoundLiteral:
      - parsed_type_1
      - InitializerList:
          - LiteralInt: 1
          - LiteralInt: 2
    ");
}

#[test]
fn test_postfix_operator_precedence() {
    // Test that postfix operators bind tighter than binary operators
    let resolved = setup_expr("a.b + c");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - MemberAccess:
          - Ident: a
          - b
          - false
      - Ident: c
    ");

    // Test chaining of postfix operators
    let resolved = setup_expr("foo()->bar[0]++");
    insta::assert_yaml_snapshot!(&resolved, @r"
    PostIncrement:
      IndexAccess:
        - MemberAccess:
            - FunctionCall:
                - Ident: foo
                - []
            - bar
            - true
        - LiteralInt: 0
    ");

    // Test a complex expression with mixed operators
    let resolved = setup_expr("++a * b.c[d--] + foo(1, 2)");
    insta::assert_yaml_snapshot!(&resolved, @r"
    BinaryOp:
      - Add
      - BinaryOp:
          - Mul
          - UnaryOp:
              - PreIncrement
              - Ident: a
          - IndexAccess:
              - MemberAccess:
                  - Ident: b
                  - c
                  - false
              - PostDecrement:
                  Ident: d
      - FunctionCall:
          - Ident: foo
          - - LiteralInt: 1
            - LiteralInt: 2
    ");
}
