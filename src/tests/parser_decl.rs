use crate::driver::artifact::CompilePhase;
use crate::tests::parser_utils::{setup_declaration, setup_declaration_with_errors, setup_translation_unit};
use crate::tests::test_utils::run_pass;

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
fn test_static_assert() {
    let resolved = setup_declaration("_Static_assert(1, \"ok\");");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    StaticAssert:
      - LiteralInt: 1
      - "3"
    "#);
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

#[test]
fn test_invalid_enum_decl() {
    let resolved = setup_declaration("enum;");
    insta::assert_yaml_snapshot!(&resolved, @r#"
    Declaration:
      specifiers:
        - "enum "
      init_declarators: []
    "#);
}

#[test]
fn test_invalid_struct_decl() {
    let resolved = setup_declaration("struct;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - struct
      init_declarators: []
    ");
}

#[test]
fn test_enum_with_non_literal_value() {
    use crate::ast::parsed::ParsedNodeKind;
    use crate::ast::parsed_types::ParsedBaseTypeNode;

    let source = "sizeof(enum { A = 1 + 1 })";

    let (ast, expr_result) = crate::tests::parser_utils::setup_source(source, |parser| {
        parser.parse_expression(crate::parser::BindingPower::MIN)
    });

    let node_ref = expr_result.expect("Failed to parse expression");
    let node = ast.get_node(node_ref);

    let constants_info = if let ParsedNodeKind::SizeOfType(type_ref) = &node.kind {
        let base_node = ast.parsed_types.get_base_type(type_ref.base);
        match base_node {
            ParsedBaseTypeNode::Enum { enumerators, .. } => {
                let range = enumerators.expect("Expected enumerators");
                let constants = ast.parsed_types.get_enum_constants(range);
                constants
                    .iter()
                    .map(|c| (c.name.to_string(), c.value))
                    .collect::<Vec<_>>()
            }
            _ => panic!("Expected Enum base type"),
        }
    } else {
        panic!("Expected SizeOfType node, got {:?}", node.kind);
    };

    insta::assert_yaml_snapshot!(constants_info, @r"
    - - A
      - ~
    ");
}

#[test]
fn test_function_returning_array_rejected() {
    let err = setup_declaration_with_errors("int f(int)[3];");
    assert!(matches!(
        err,
        crate::diagnostic::ParseError::DeclarationNotAllowed { .. }
    ));
}

#[test]
fn test_parse_noreturn_function_declaration() {
    let resolved = setup_declaration("_Noreturn void foo();");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - Noreturn
        - void
      init_declarators:
        - name: foo
          kind: function(void) -> int
    ");
}

#[test]
fn test_cast_attribute_pointer() {
    // This reproduces the issue: int b = ( (int(ATTR *)(void)) function_pointer)();
    let resolved = setup_declaration("int x = (int (__attribute__((unused)) *) (void)) 0;");
    insta::assert_yaml_snapshot!(resolved, @r"
    Declaration:
      specifiers:
        - int
      init_declarators:
        - name: x
          initializer:
            Cast:
              - parsed_type_1_3
              - LiteralInt: 0
    ");
}

#[test]
fn test_param_attribute_int() {
    // Verify that (ATTR int) is still parsed as a parameter list.
    let resolved = setup_declaration("void foo(int (__attribute__((unused)) int));");
    insta::assert_yaml_snapshot!(resolved, @r"
    Declaration:
      specifiers:
        - void
      init_declarators:
        - name: foo
          kind: function(function(int) -> int) -> int
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

#[test]
fn test_complex_function_param_declarators() {
    let code = r#"
/* The following are all valid decls, even though some subtypes
   are incomplete.  */
enum E *e;
const enum E *e1;
enum E const *e2;
struct S *s;
const struct S *s1;
struct S const *s2;

/* Various strangely looking declarators, which are all valid
   and have to map to the same numbered typedefs. */
typedef int (*fptr1)();
int f1 (int (), int);
typedef int (*fptr2)(int x);
int f2 (int (int x), int);
typedef int (*fptr3)(int);
int f3 (int (int), int);
typedef int (*fptr4[4])(int);
int f4 (int (*[4])(int), int);
typedef int (*fptr5)(fptr1);
int f5 (int (int()), fptr1);

int f1 (fptr1 fp, int i)
{
  return (*fp)(i);
}
int f2 (fptr2 fp, int i)
{
  return (*fp)(i);
}
int f3 (fptr3 fp, int i)
{
  return (*fp)(i);
}
int f4 (fptr4 fp, int i)
{
  return (*fp[i])(i);
}
int f5 (fptr5 fp, fptr1 i)
{
  return fp(i);
}
int f8 (int ([4]), int);
int main () { return 0; }
"#;
    run_pass(code, CompilePhase::SemanticLowering);
}

#[test]
fn test_struct_attribute_error_recovery() {
    // Test error recovery when __attribute__ is malformed before tag
    // expected: struct __attribute__ S; -> struct S;
    let resolved = setup_declaration("struct __attribute__ S;");
    insta::assert_yaml_snapshot!(&resolved, @r"
    Declaration:
      specifiers:
        - struct S
      init_declarators: []
    ");

    // Test error recovery when __attribute__ is malformed after definition
    // expected: struct S { } __attribute__; -> struct S { };
    let resolved_def = setup_declaration("struct S { } __attribute__;");
    insta::assert_yaml_snapshot!(&resolved_def, @r#"
    Declaration:
      specifiers:
        - "struct S { ... }"
      init_declarators: []
    "#);
}
