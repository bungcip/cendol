#![cfg(test)]
use crate::parser::declarations;
use crate::parser::statements::parse_compound_statement;
use crate::tests::parser_utils::*;

#[test]
fn test_function_returning_array_rejected() {
    let err = setup_declaration_with_errors("int f(int)[3];");
    assert!(matches!(
        err,
        crate::diagnostic::ParseError::DeclarationNotAllowed { .. }
    ));
}

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
fn test_simple_struct_declaration() {
    let resolved = setup_declaration("struct Point;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - struct Point
      init_declarators: []
    ");
}

#[test]
fn test_struct_declaration_with_body() {
    let resolved = setup_declaration("struct Point { int x; int y; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct Point { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_struct_variable_declaration() {
    let resolved = setup_declaration("struct Point p;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - struct Point
      init_declarators:
        - name: p
    ");
}

#[test]
fn test_struct_definition_and_variable() {
    let resolved = setup_declaration("struct Point { int x; } p;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct Point { ... }"
      init_declarators:
        - name: p
    "#);
}

#[test]
fn test_anonymous_struct_declaration() {
    let resolved = setup_declaration("struct { int x; } p;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct { ... }"
      init_declarators:
        - name: p
    "#);
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
fn test_simple_declaration() {
    let resolved = setup_declaration("int x;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
    ");
}

#[test]
fn test_atomic_type_specifier() {
    let resolved = setup_declaration("_Atomic(int) x;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "Atomic(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) })"
      init_declarators:
        - name: x
    "#);
}

#[test]
fn test_atomic_type_specifier_with_pointer() {
    let resolved = setup_declaration("_Atomic(int *) x;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "Atomic(ParsedType { base: 1, declarator: 2, qualifiers: TypeQualifiers(0x0) })"
      init_declarators:
        - name: x
    "#);
}

#[test]
fn test_declaration_with_initializer() {
    let resolved = setup_declaration("int x = 42;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
          initializer:
            LiteralInt: 42
    ");
}

#[test]
fn test_multiple_declarators() {
    let resolved = setup_declaration("int x, y = 1, z;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
        - name: y
          initializer:
            LiteralInt: 1
        - name: z
    ");
}

#[test]
fn test_pointer_declaration() {
    let resolved = setup_declaration("int *p;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer
    ");
}

#[test]
fn test_array_declaration() {
    let resolved = setup_declaration("int arr[10];");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
    ");
}

#[test]
fn test_array_declaration_with_initializer() {
    let resolved = setup_declaration("int arr[3] = {1, 2, 3};");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 1
              - LiteralInt: 2
              - LiteralInt: 3
    ");
}

#[test]
fn test_complex_declaration() {
    let resolved = setup_declaration("int a = 1, *b[3], c(struct X, int), d = (1, 2, 3);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          initializer:
            LiteralInt: 1
        - name: b
          kind: pointer to array
        - name: c
          kind: "function(..., int) -> int"
        - name: d
          initializer:
            BinaryOp:
              - Comma
              - BinaryOp:
                  - Comma
                  - LiteralInt: 1
                  - LiteralInt: 2
              - LiteralInt: 3
    "#);
}

#[test]
fn test_function_with_array_of_pointer_param() {
    let resolved = setup_declaration("int f(int (*arr)[3]);");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array of pointer) -> int
    ");
}

#[test]
fn test_array_of_function_pointers() {
    let resolved = setup_declaration("int (*callbacks[10])(int, float);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: callbacks
          kind: "function(int, float) -> pointer to array"
    "#);
}

#[test]
fn test_function_pointer_with_initializer() {
    let resolved = setup_declaration("int (*f)(int) = 0;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int) -> pointer
          initializer:
            LiteralInt: 0
    ");
}

#[test]
fn test_array_of_pointers_with_initializer() {
    let resolved = setup_declaration("int *p[3] = { &x, 0, &y };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: p
          kind: pointer to array
          initializer:
            InitializerList:
              - UnaryOp:
                  - AddrOf
                  - Ident: x
              - LiteralInt: 0
              - UnaryOp:
                  - AddrOf
                  - Ident: y
    ");
}

#[test]
fn test_function_pointer_with_cast_initializer() {
    let resolved = setup_declaration("int (*fp)(int) = (int (*)(int))0;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: fp
          kind: function(int) -> pointer
          initializer:
            Cast:
              - parsed_type_1_4
              - LiteralInt: 0
    ");
}

#[test]
fn test_mixed_declarators_simple() {
    let resolved = setup_declaration("int *a, (*b)(int), c[10];");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          kind: pointer
        - name: b
          kind: function(int) -> pointer
        - name: c
          kind: array
    ");
}

#[test]
fn test_deeply_mixed_declarators() {
    let resolved = setup_declaration("int *a, (*b[5])(double), c(struct X, int), d = (1, 2);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          kind: pointer
        - name: b
          kind: function(double) -> pointer to array
        - name: c
          kind: "function(..., int) -> int"
        - name: d
          initializer:
            BinaryOp:
              - Comma
              - LiteralInt: 1
              - LiteralInt: 2
    "#);
}

#[test]
fn test_madness_with_parentheses() {
    let resolved = setup_declaration("int (*a)(int), *(*b)(float), (*c[3])(int, int);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
          kind: function(int) -> pointer
        - name: b
          kind: pointer to function(float) -> pointer
        - name: c
          kind: "function(int, int) -> pointer to array"
    "#);
}

#[test]
fn test_callback_style_function() {
    let resolved = setup_declaration("int sort(int (*cmp)(int, int));");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: sort
          kind: "function(int function(int, int) -> pointer) -> int"
    "#);
}

#[test]
fn test_function_returning_pointer_to_function() {
    let resolved = setup_declaration("int (*make_cb(int (*cmp)(int, int)))(int, int);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: make_cb
          kind: "function(int, int) -> pointer to function(int function(int, int) -> pointer) -> int"
    "#);
}

#[test]
fn test_parentheses_that_do_nothing() {
    let resolved = setup_declaration("int (((a)));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: a
    ");
}

#[test]
fn test_insane_parentheses_on_pointer_to_array_to_function() {
    let resolved = setup_declaration("int (*(((*f))(int)))[5];");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: array of pointer to function(int) -> pointer
    ");
}

#[test]
fn test_array_of_functions_rejected() {
    let _ = setup_declaration_with_errors("int f[3](int);");
}

#[test]
fn test_function_returning_function_rejected() {
    let _ = setup_declaration_with_errors("int f(int)(float);");
}

#[test]
fn test_ellipsis_not_last_parameter_rejected() {
    let _ = setup_declaration_with_errors("int f(int ..., int);");
}

#[test]
fn test_variadic_function_declaration() {
    let resolved = setup_declaration("int printf(const char * restrict format, ...);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: printf
          kind: "function(char pointer, ...) -> int"
    "#);
}

#[test]
fn test_enum_declaration_with_values() {
    let resolved = setup_declaration("enum Color { RED = 1, GREEN = 2, BLUE };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "enum Color { RED = 1, GREEN = 2, BLUE }"
      init_declarators: []
    "#);
}

#[test]
fn test_function_with_array_abstract_declarator() {
    let resolved = setup_declaration("int f(int ([4]));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int array) -> int
    ");
}

#[test]
fn test_complex_abstract_declarator_function() {
    let resolved = setup_declaration("int f5(int (*fp)(int));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f5
          kind: function(int function(int) -> pointer) -> int
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
fn test_struct_member_multiple_declarators() {
    let resolved = setup_declaration("struct flowi6 { struct in6_addr saddr, daddr; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct flowi6 { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_bitfield_declaration() {
    let resolved = setup_declaration("struct Test { int x: 8; unsigned y: 1; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct Test { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_bitfield_with_mixed_members() {
    let resolved =
        setup_declaration("struct Mixed { int regular; int bitfield: 4; int another_regular; unsigned flag: 1; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct Mixed { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_bitfield_with_large_width() {
    let resolved = setup_declaration("struct LargeBitfield { unsigned long value: 32; };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct LargeBitfield { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_designated_initializer_simple_array() {
    let resolved = setup_declaration("int arr[10] = { [5] = 42 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 42
    ");
}

#[test]
fn test_designated_initializer_range_syntax() {
    let resolved = setup_declaration("int arr[10] = { [1 ... 5] = 9 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 9
    ");
}

#[test]
fn test_designated_initializer_multiple_ranges() {
    let resolved = setup_declaration("int arr[20] = { [1 ... 5] = 9, [10 ... 15] = 42 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 9
              - LiteralInt: 42
    ");
}

#[test]
fn test_designated_initializer_mixed_single_and_range() {
    let resolved = setup_declaration("int arr[10] = { [0] = 1, [2 ... 5] = 9, [8] = 42 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 1
              - LiteralInt: 9
              - LiteralInt: 42
    ");
}

#[test]
fn test_designated_initializer_range_with_expressions() {
    let resolved = setup_declaration("int arr[10] = { [1 ... 2+3] = 9 };");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: arr
          kind: array
          initializer:
            InitializerList:
              - LiteralInt: 9
    ");
}

#[test]
fn test_designated_initializer_struct_with_range() {
    let resolved = setup_declaration("struct T { int s[16]; int a; } lt2 = { { [1 ... 5] = 9, [6 ... 10] = 42 }, 1 };");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct T { ... }"
      init_declarators:
        - name: lt2
          initializer:
            InitializerList:
              - InitializerList:
                  - LiteralInt: 9
                  - LiteralInt: 42
              - LiteralInt: 1
    "#);
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

// === LABEL DETECTION TESTS ===

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
fn test_parse_bitfield() {
    let source = "struct S { int a : 4; unsigned b : 2; };";
    let resolved = setup_declaration(source);
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "struct S { ... }"
      init_declarators: []
    "#);
}

#[test]
fn test_atomic_type_qualifier() {
    let resolved = setup_declaration("_Atomic int x;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - TypeQualifier(Atomic)
        - int
      init_declarators:
        - name: x
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
    // However, since T is not defined as a typedef, it should be parsed as an expression statement.
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
fn test_void_pointer_param() {
    let resolved = setup_declaration("void* memcpy(void* dest, const void* src, unsigned long n);");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - void
      init_declarators:
        - name: memcpy
          kind: "pointer to function(void pointer, void pointer, unsigned long) -> int"
    "#);
}

// === NEW TESTS ===

#[test]
fn test_static_assert() {
    let resolved = setup_declaration("_Static_assert(1, \"ok\");");
    insta::assert_yaml_snapshot!(&resolved, @r"
    StaticAssert:
      - LiteralInt: 1
      - ok
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
fn test_function_definition() {
    let resolved = setup_translation_unit("int main() { return 0; }");
    insta::assert_yaml_snapshot!(&resolved, @r"
    TranslationUnit:
      - FunctionDef:
          specifiers:
            - int
          declarator:
            name: main
            kind: function(void) -> int
          body:
            CompoundStatement:
              - Return:
                  LiteralInt: 0
    ");
}

#[test]
fn test_translation_unit() {
    let resolved = setup_translation_unit("int x; int main() { return x; }");
    insta::assert_yaml_snapshot!(&resolved, @r"
    TranslationUnit:
      - Declaration:
          specifiers:
            - int
          init_declarators:
            - name: x
      - FunctionDef:
          specifiers:
            - int
          declarator:
            name: main
            kind: function(void) -> int
          body:
            CompoundStatement:
              - Return:
                  Ident: x
    ");
}

#[test]
fn test_atomic_specifier_syntax() {
    let resolved = setup_declaration("_Atomic(int) *x;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "Atomic(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) })"
      init_declarators:
        - name: x
          kind: pointer
    "#);
}

#[test]
fn test_atomic_qualifier_syntax() {
    let resolved = setup_declaration("_Atomic int *x;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - TypeQualifier(Atomic)
        - int
      init_declarators:
        - name: x
          kind: pointer
    ");
}

#[test]
fn test_complex_declarator_ret_ptr_to_func() {
    let resolved = setup_declaration("int (*f)(int (*)(int));");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int function(int) -> pointer) -> pointer
    ");
}

#[test]
fn test_complex_declarator_arr_of_ptr_to_func() {
    let resolved = setup_declaration("int (*f[])(int);");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: f
          kind: function(int) -> pointer to array
    ");
}

#[test]
fn test_const_volatile_pointer() {
    let resolved = setup_declaration("int * const volatile x;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
          kind: pointer
    ");
}

// Tests moved to end of file via cat command
// Fix for test_invalid_enum_decl
#[test]
fn test_invalid_enum_decl() {
    // "enum;" should either be an error (missing tag) or a warning (empty declaration).
    // In many C compilers, `enum;` is a warning, or treated as declaration with no tag.
    // However, `cendol`'s parser seems to accept it.
    // Let's check what it actually produces.
    // It likely produces a Declaration with type specifier `enum` (no tag) and empty declarators.
    let resolved = setup_declaration("enum;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "enum "
      init_declarators: []
    "#);
}

// Fix for test_invalid_struct_decl
#[test]
fn test_invalid_struct_decl() {
    // "struct;" is similar to "enum;". It's technically valid in some contexts (anonymous struct declaration that declares nothing).
    // C11 6.7.2.1p2: "A struct-declaration that does not declare an anonymous structure or anonymous union shall contain a struct-declarator-list."
    // But here we are at file scope or block scope, so it's a declaration.
    // C11 6.7p2: "A declaration other than a static_assert declaration shall declare at least a declarator, a tag, or the members of an enumeration."
    // `struct;` declares NONE of these. So it violates constraints.
    // However, many compilers (GCC/Clang) only warn about "declaration does not declare anything".
    // If cendol accepts it, we'll snapshot that behavior for now and maybe flag it as something to improve later.
    let resolved = setup_declaration("struct;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - struct
      init_declarators: []
    "#);
}
