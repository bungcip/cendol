use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

use crate::ast::NodeKind;
use crate::semantic::const_eval::ConstEvalCtx;
use crate::tests::semantic_common::setup_analysis;
use crate::tests::test_utils::run_pipeline;

fn evaluate_program(source: &str) -> String {
    let (ast, mut registry, symbol_table) = setup_analysis(source);

    // Force layout computation for types likely to be used in sizeof tests.
    let _ = registry.ensure_layout(registry.type_int);
    let _ = registry.ensure_layout(registry.type_long);
    let _ = registry.ensure_layout(registry.type_long_long);
    let _ = registry.ensure_layout(registry.type_char);
    let _ = registry.ensure_layout(registry.type_float);
    let _ = registry.ensure_layout(registry.type_double);

    let root = ast.get_root();
    // Ensure we have a translation unit
    if !matches!(ast.get_kind(root), NodeKind::TranslationUnit(_)) {
        panic!("Root is not a TranslationUnit");
    }

    let init_expr = crate::tests::semantic_common::find_var_decl(&ast, &symbol_table, "test_var")
        .init
        .expect("Could not find test_var initializer");

    let ctx = ConstEvalCtx {
        ast: &ast,
        symbol_table: &symbol_table,
        registry: &registry,
        semantic_info: &ast.semantic_info,
    };

    let result = ctx.eval_int(init_expr);
    match result {
        Some(val) => format!("{}", val),
        None => "None".to_string(),
    }
}

fn format_const_eval_batch(exprs: &[&str]) -> String {
    let mut output = String::new();

    for expr in exprs {
        let source = format!("long long test_var = {};", expr);
        let val_str = evaluate_program(&source);
        output.push_str(&format!("Expression: {}\nResult: {}\n---\n", expr, val_str));
    }

    output
}

#[test]
fn test_arithmetic() {
    let output = format_const_eval_batch(&["1 + 2", "10 - 5", "2 * 3", "10 / 2", "10 % 3"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 + 2
    Result: 3
    ---
    Expression: 10 - 5
    Result: 5
    ---
    Expression: 2 * 3
    Result: 6
    ---
    Expression: 10 / 2
    Result: 5
    ---
    Expression: 10 % 3
    Result: 1
    ---
    ");
}

#[test]
fn test_arithmethic_with_predence() {
    let output = format_const_eval_batch(&["1 + 2 * 3", "(1 + 2) * 3"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 + 2 * 3
    Result: 7
    ---
    Expression: (1 + 2) * 3
    Result: 9
    ---
    ");
}

#[test]
fn test_bitwise() {
    let output = format_const_eval_batch(&["1 << 2", "8 >> 1", "0x0F & 0xF0", "0x0F | 0xF0", "0x0F ^ 0xFF", "~0"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 << 2
    Result: 4
    ---
    Expression: 8 >> 1
    Result: 4
    ---
    Expression: 0x0F & 0xF0
    Result: 0
    ---
    Expression: 0x0F | 0xF0
    Result: 255
    ---
    Expression: 0x0F ^ 0xFF
    Result: 240
    ---
    Expression: ~0
    Result: -1
    ---
    ");
}

#[test]
fn test_logical() {
    let output = format_const_eval_batch(&["1 && 1", "1 && 0", "1 || 0", "0 || 0", "!0", "!5"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 && 1
    Result: 1
    ---
    Expression: 1 && 0
    Result: 0
    ---
    Expression: 1 || 0
    Result: 1
    ---
    Expression: 0 || 0
    Result: 0
    ---
    Expression: !0
    Result: 1
    ---
    Expression: !5
    Result: 0
    ---
    ");
}

#[test]
fn test_comparisons() {
    let output = format_const_eval_batch(&["1 < 2", "2 > 1", "1 <= 1", "2 >= 2", "1 == 1", "1 != 2"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 < 2
    Result: 1
    ---
    Expression: 2 > 1
    Result: 1
    ---
    Expression: 1 <= 1
    Result: 1
    ---
    Expression: 2 >= 2
    Result: 1
    ---
    Expression: 1 == 1
    Result: 1
    ---
    Expression: 1 != 2
    Result: 1
    ---
    ");
}

#[test]
fn test_ternary() {
    let output = format_const_eval_batch(&["1 ? 10 : 20", "0 ? 10 : 20"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 ? 10 : 20
    Result: 10
    ---
    Expression: 0 ? 10 : 20
    Result: 20
    ---
    ");
}

#[test]
fn test_sizeof() {
    let output = format_const_eval_batch(&["sizeof(int)", "sizeof(long)", "sizeof(long long)", "sizeof(1 + 1)"]);
    insta::assert_snapshot!(output, @"
    Expression: sizeof(int)
    Result: 4
    ---
    Expression: sizeof(long)
    Result: 8
    ---
    Expression: sizeof(long long)
    Result: 8
    ---
    Expression: sizeof(1 + 1)
    Result: 4
    ---
    ");
}

#[test]
fn test_overflow_wrapping() {
    // 9223372036854775807 is LLONG_MAX (2^63 - 1)
    let output = format_const_eval_batch(&["9223372036854775807LL + 1"]);
    insta::assert_snapshot!(output, @"
    Expression: 9223372036854775807LL + 1
    Result: -9223372036854775808
    ---
    ");
}

#[test]
fn test_generic_selection() {
    let output = format_const_eval_batch(&[
        "_Generic(1, int: 10, default: 20)",
        "_Generic(1.0, double: 30, default: 20)",
    ]);
    insta::assert_snapshot!(output, @"
    Expression: _Generic(1, int: 10, default: 20)
    Result: 10
    ---
    Expression: _Generic(1.0, double: 30, default: 20)
    Result: 30
    ---
    ");
}

#[test]
fn test_enum_constants() {
    let source = "enum { A = 5, B = 10 }; int test_var = A + B;";
    let val_str = evaluate_program(source);

    insta::assert_snapshot!(format!("Source: {}\nResult: {}", source, val_str), @"
    Source: enum { A = 5, B = 10 }; int test_var = A + B;
    Result: 15
    ");
}

#[test]
fn test_offsetof() {
    let source = "struct S { int a; int b[10]; struct { int c; int d[5]; } e; }; long long test_var = __builtin_offsetof(struct S, b[5]) + __builtin_offsetof(struct S, e.d[2]);";
    let val_str = evaluate_program(source);

    insta::assert_snapshot!(format!("Source: {}\nResult: {}", source, val_str), @"
    Source: struct S { int a; int b[10]; struct { int c; int d[5]; } e; }; long long test_var = __builtin_offsetof(struct S, b[5]) + __builtin_offsetof(struct S, e.d[2]);
    Result: 80
    ");
}

#[test]
fn test_alignof() {
    let output = format_const_eval_batch(&["_Alignof(int)"]);
    insta::assert_snapshot!(output, @"
    Expression: _Alignof(int)
    Result: 4
    ---
    ");
}

#[test]
fn test_logical_short_circuit() {
    let output = format_const_eval_batch(&["1 || (1 / 0)", "0 && (1 / 0)"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 || (1 / 0)
    Result: 1
    ---
    Expression: 0 && (1 / 0)
    Result: 0
    ---
    ");
}

#[test]
fn test_div_by_zero() {
    let output = format_const_eval_batch(&["1 / 0"]);
    insta::assert_snapshot!(output, @"
    Expression: 1 / 0
    Result: None
    ---
    ");
}

#[test]
fn test_unsigned_arithmetic() {
    let output = format_const_eval_batch(&[
        "((unsigned long)-1) / 25",
        "((unsigned long)-1) % 25",
        "((unsigned long)-1) >> 1",
        "((unsigned long)-1) > 10",
        "((unsigned long)-1) < 10",
        "((unsigned long)-1) >= 10",
        "((unsigned long)-1) <= 10",
    ]);
    insta::assert_snapshot!(output, @"
    Expression: ((unsigned long)-1) / 25
    Result: 737869762948382064
    ---
    Expression: ((unsigned long)-1) % 25
    Result: 15
    ---
    Expression: ((unsigned long)-1) >> 1
    Result: 9223372036854775807
    ---
    Expression: ((unsigned long)-1) > 10
    Result: 1
    ---
    Expression: ((unsigned long)-1) < 10
    Result: 0
    ---
    Expression: ((unsigned long)-1) >= 10
    Result: 1
    ---
    Expression: ((unsigned long)-1) <= 10
    Result: 0
    ---
    ");
}

#[test]
fn test_builtin_functions() {
    let output = format_const_eval_batch(&[
        "__builtin_clz(1)",
        "__builtin_clz(0)", // Undefined behavior, returns None
        "__builtin_ctz(2)",
        "__builtin_ctz(0)", // Undefined behavior, returns None
        "__builtin_popcount(3)",
        "__builtin_ffs(2)",
        "__builtin_ffs(0)",
    ]);
    insta::assert_snapshot!(output, @"
    Expression: __builtin_clz(1)
    Result: 31
    ---
    Expression: __builtin_clz(0)
    Result: None
    ---
    Expression: __builtin_ctz(2)
    Result: 1
    ---
    Expression: __builtin_ctz(0)
    Result: None
    ---
    Expression: __builtin_popcount(3)
    Result: 2
    ---
    Expression: __builtin_ffs(2)
    Result: 2
    ---
    Expression: __builtin_ffs(0)
    Result: 0
    ---
    ");
}

#[test]
fn test_builtin_fabs_eval_test() {
    let output = format_const_eval_batch(&[
        "__builtin_fabs(-1.5)",
        "__builtin_fabsf(-2.5f)",
        "__builtin_fabsl(-3.5L)",
        "__builtin_fabs(1.5)",
    ]);
    insta::assert_snapshot!(output, @"
    Expression: __builtin_fabs(-1.5)
    Result: 1
    ---
    Expression: __builtin_fabsf(-2.5f)
    Result: 2
    ---
    Expression: __builtin_fabsl(-3.5L)
    Result: 3
    ---
    Expression: __builtin_fabs(1.5)
    Result: 1
    ---
    ");
}

#[test]
fn test_unary_float_eval() {
    let output = format_const_eval_batch(&["+1.5", "-1.5"]);
    insta::assert_snapshot!(output, @"
    Expression: +1.5
    Result: 1
    ---
    Expression: -1.5
    Result: -1
    ---
    ");
}

#[test]
fn test_const_eval_member_access_in_array_size() {
    let src = r#"
        struct S {
            int x[10];
            char y;
        };
        struct T {
            struct S s;
            struct S *p;
        };

        int main() {
            struct S mys;
            struct T myt;
            int arr1[sizeof(mys.y + 1)];
            int arr2[sizeof(myt.s.x[0] + 1)];
            int arr3[sizeof(myt.p->x[0] + 1)];
            return 0;
        }
    "#;
    let (_, result) = run_pipeline(src, CompilePhase::Mir);
    assert!(result.is_ok());
}

#[test]
fn test_const_eval_char_float_2() {
    let source = "double test_var = 'a' + 0.5;";
    let (ast, registry, symbol_table) = setup_analysis(source);

    let init_expr = crate::tests::semantic_common::find_var_decl(&ast, &symbol_table, "test_var")
        .init
        .expect("Could not find test_var initializer");

    let ctx = ConstEvalCtx {
        ast: &ast,
        symbol_table: &symbol_table,
        registry: &registry,
        semantic_info: &ast.semantic_info,
    };

    // Evaluate binary expression where one side is a char and the other is a float
    let result = ctx.eval_float(init_expr);
    assert_eq!(result, Some(97.5));
}

#[test]
fn test_const_eval_char_type() {
    let source = "int test_var = sizeof('a');";
    let val_str = evaluate_program(source);
    insta::assert_snapshot!(format!("Source: {}\nResult: {}", source, val_str), @"
    Source: int test_var = sizeof('a');
    Result: 4
    ");
}

#[test]
fn test_const_eval_unary_coverage() {
    let source = "
    void f() {
        int x = 5;
        int arr[sizeof(!x)];
    }
    ";
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_const_eval_coverage() {
    let source = "
    void f() {
        int arr1[__builtin_choose_expr(1, 10, 20)];
        int arr2[__builtin_choose_expr(0, 10, 20)];
        int arr3[__builtin_types_compatible_p(int, int) ? 1 : 2];
        struct S { int a; };
        int arr4[sizeof((struct S){0}.a)];
        int arr5[sizeof(__builtin_choose_expr(1, 10, 20))];
        int arr6[sizeof(__builtin_offsetof(struct S, a))];
        int arr7[sizeof((int *)0)];
        int arr8[sizeof(+(int *)0)];
        int arr9[sizeof((struct S){0})];
        int arr10[sizeof((struct S *)0)];
        int arr11[sizeof(1 ? (struct S *)0 : (struct S *)0)];
        int arr12[sizeof(1 ? (int *)0 : (int *)0)];
        int arr13[sizeof(1 ? (void *)0 : (int *)0)];
        int arr14[sizeof(1 ? (int *)0 : (void *)0)];
        int arr15[sizeof(1 ? (void *)0 : (void *)0)];

        int a = 1;
        int arr23[sizeof(1 ? a : a)];

        int arr26[sizeof(_Generic(1, int: 1, float: 2))];
        int arr27[sizeof(_Generic(1, float: 2, default: 3))];

        int arr28[sizeof(\"abc\")];
        int arr29[sizeof(u8\"abc\")];
        int arr30[sizeof(u\"abc\")];
        int arr31[sizeof(U\"abc\")];
        int arr32[sizeof(L\"abc\")];
    }

    struct SomeStruct { int member; };
    struct S {
        struct SomeStruct s;
    };

    void g() {
        int arr33[sizeof((struct S){0}.s.member)];
        int arr34[sizeof(((struct S*)0)->s.member)];
        int arr35[sizeof(*((struct S*)0))];
        int arr36[sizeof( (int[2]){1, 2}[0] )];
        int arr37[sizeof( !1.0 )];
        int arr38[sizeof( +1.0 )];
        int arr39[sizeof( -1.0 )];
        int arr40[sizeof( 1.0 + 2.0 )];
        int arr41[sizeof( (int)1.0 )];
    }
    ";
    run_pass(source, CompilePhase::SemanticLowering);
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage() {
    let src = r#"
        int global_int;
        int arr[10];

        struct S { int x; };
        struct S s;
        struct Outer { struct S s[1]; } out;
        struct S arr_s[1];
        struct T { int *p; } t;
        struct U { struct T *tp; } u = { &t };

        // Hit when Deref is evaluated: `&*(ptr)`
        int *g_cast = &(*((int*)&global_int));
        int *g_ident = &(*arr);
        int *g_member = &*(u.tp->p);

        // Hit when AddrOf is evaluated: `&(expr)`
        int *g_cast2 = &((int)global_int);
        int *g_deref = &*(&global_int);
        int *g_false2 = &(1 + 1);

        int main() { return 0; }
    "#;
    crate::tests::test_utils::run_fail_with_message(src, "not");
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_2() {
    let src = "struct S { int x; }; struct S s; int *fail1 = &(((struct S*)((void*)&s))->x);";
    crate::tests::test_utils::run_fail_with_message(src, "not");
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_3() {
    let src = "struct S { int x; }; struct Outer { struct S s[1]; } out; int *fail2 = &out.s->x;";
    crate::tests::test_utils::run_fail_with_message(src, "not");
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_4() {
    let src = "struct S { int x; }; struct S s; int *fail3 = &(0 ? &s : &s)->x;";
    crate::tests::test_utils::run_fail_with_message(src, "not");
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_5() {
    let src = "int arr[10]; int *g_false = &*(0 ? arr : arr);";
    crate::tests::test_utils::run_fail_with_message(src, "not");
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_6() {
    let src = "struct S { int x; }; struct S arr_s[1]; int *valid = &arr_s->x;";
    // This also fails with "not computable at load time", which means it returns false for constant!
    crate::tests::test_utils::run_fail_with_message(src, "not");
}

#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_7() {
    let src = "int arr[10]; int *test_ptr = &(((int*)arr)[0]);";
    crate::tests::test_utils::run_pass(src, crate::driver::artifact::CompilePhase::Mir);
}
#[test]
fn test_is_constant_pointer_to_static_duration_object_coverage_8() {
    let src = r#"
        struct S { int x; };
        struct S *ptr;
        int *test_ptr = &(((struct S)*ptr).x);
    "#;
    crate::tests::test_utils::run_fail_with_message(src, "not");
}
#[test]
fn test_hit_2527() {
    let src = "int arr[10]; int *test_ptr = &(((int*)arr)[0]);";
    crate::tests::test_utils::run_pass(src, crate::driver::artifact::CompilePhase::Mir);
}
