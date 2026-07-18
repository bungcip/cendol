//! Tests for Struct/Union/Array lowering and access
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::{run_c_code_exit_status, setup_cranelift};
use crate::tests::test_utils::run_pass;
use insta::assert_snapshot;

#[test]
fn test_compile_struct_pointer_access() {
    let source = r#"
            int main() {
                struct S { int x; int y; } s;
                struct S *p;
                p = &s;
                s.x = 1;
                p->y = 2;
                return p->y + p->x - 3;
            }
        "#;
    let clif_dump = setup_cranelift(source);
    insta::assert_snapshot!(
        clif_dump,
        @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 8, align = 4
        ss1 = explicit_slot 8, align = 8
        ss2 = explicit_slot 4, align = 4
        ss3 = explicit_slot 4, align = 4

    block0:
        v0 = stack_addr.i64 ss0
        v29 = stack_addr.i64 ss1
        store notrap v0, v29
        v1 = iconst.i32 1
        v2 = stack_addr.i64 ss0
        v3 = iconst.i64 0
        v4 = iadd v2, v3  ; v3 = 0
        store v1, v4  ; v1 = 1
        v5 = iconst.i32 2
        v28 = stack_addr.i64 ss1
        v6 = load.i64 notrap v28
        v7 = iconst.i64 4
        v8 = iadd v6, v7  ; v7 = 4
        store v5, v8  ; v5 = 2
        v27 = stack_addr.i64 ss1
        v9 = load.i64 notrap v27
        v10 = iconst.i64 4
        v11 = iadd v9, v10  ; v10 = 4
        v12 = load.i32 v11
        v26 = stack_addr.i64 ss1
        v13 = load.i64 notrap v26
        v14 = iconst.i64 0
        v15 = iadd v13, v14  ; v14 = 0
        v16 = load.i32 v15
        v17 = iadd v12, v16
        v25 = stack_addr.i64 ss2
        store notrap v17, v25
        v24 = stack_addr.i64 ss2
        v18 = load.i32 notrap v24
        v19 = iconst.i32 3
        v20 = isub v18, v19  ; v19 = 3
        v23 = stack_addr.i64 ss3
        store notrap v20, v23
        v22 = stack_addr.i64 ss3
        v21 = load.i32 notrap v22
        return v21
    }
    "
    );
}

#[test]
fn test_compile_union_field_access() {
    let source = r#"
            int main() {
                union U { int a; int b; } u;
                u.a = 1;
                u.b = 3;
                if (u.a != 3 || u.b != 3)
                    return 1;
                return 0;
            }
        "#;

    let clif_dump = setup_cranelift(source);

    // Expect loads/stores with zero offset (union fields share offset 0)
    assert!(
        clif_dump.contains("iconst.i64 0"),
        "expected zero offset constant in IR"
    );
    assert!(clif_dump.contains("store"), "expected store instruction in IR");
    assert!(clif_dump.contains("load"), "expected load instruction in IR");
}

#[test]
fn test_array_literal_codegen() {
    run_pass(
        r#"
        int main() {
            int a[2] = {1, 2};
            if (a[0] != 1) return 1;
            if (a[1] != 2) return 2;
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_struct_literal_codegen() {
    run_pass(
        r#"
        int main() {
            struct S { int x; int y; } s = {1, 2};
            if (s.x != 1) return 1;
            if (s.y != 2) return 2;
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_array_literal_initialization_fix() {
    let source = r#"
        int main() {
            char s[] = "hello";
            return 0;
        }
    "#;

    let clif_dump = setup_cranelift(source);
    assert_snapshot!(clif_dump, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 6
        gv0 = symbol colocated userextname0
        sig0 = (i64, i64, i64) -> i64 system_v
        fn0 = u0:1 sig0

    block0:
        v0 = symbol_value.i64 gv0
        v1 = stack_addr.i64 ss0
        v2 = iconst.i64 6
        v3 = call fn0(v1, v0, v2)  ; v2 = 6
        v4 = iconst.i32 0
        return v4  ; v4 = 0
    }
    ");
}

#[test]
fn test_nested_struct_compound_literal_init() {
    let source = r#"
        struct A { int x; };
        struct B { struct A a; };
        struct B b = { (struct A){1} };
        int main() { return 0; }
    "#;

    // This should not crash with "StructLiteral with non-record type"
    let _ = setup_cranelift(source);
}

#[test]
fn test_array_in_condition_fix() {
    let source = r#"
        int main() {
            int a[5];
            if (a) {
                return 174;
            }
            return 0;
        }
    "#;

    // This should not panic during compilation and should generate valid IR
    let clif_dump = setup_cranelift(source);

    // We expect the array 'a' to decay to a pointer, which is then handled in 'if'
    assert!(
        clif_dump.contains("stack_addr.i64"),
        "Expected stack_addr for array 'a' in condition"
    );
}

#[test]
fn test_arrow_on_array_deref_panic_regression() {
    let source = r#"
        struct Point { int x; int y; };
        int main() {
            struct Point pts[2] = {{1, 2}, {3, 4}};
            return pts->x;
        }
    "#;

    // This should not panic during MIR generation
    let clif_dump = setup_cranelift(source);

    // We expect the array 'pts' to decay to a pointer, then dereferenced for member 'x'
    assert!(
        clif_dump.contains("stack_addr.i64"),
        "Expected stack_addr for array 'pts'"
    );
}

#[test]
fn test_compound_literal_address_at_file_scope() {
    let source = r#"
        struct S { int x, y; };
        struct S *p = &(struct S){1, 2};
        int main() {
            if (p->x != 1 || p->y != 2) return 1;
            return 0;
        }
    "#;

    // This should not panic during MIR generation and should exit with status 0
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0);
}

#[test]
fn test_vla_static_pointer() {
    // p must be 10 even though sz is changed to 20
    let source = r#"
    int main() {
        int sz = 10;
        static char (*p)[sz];
        int result = sizeof(*p);
        if (result != 10) return 1;
        sz = 20;
        return 0;
    }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn test_global_struct_init_compound_literal() {
    let source = r#"
        struct S { int x, y; };
        struct S gs = (struct S){1, 2};
        int main() {
            if (gs.x != 1 || gs.y != 2) return 1;
            return 0;
        }
    "#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0);
}

#[test]
fn test_global_wrap_function_ptr() {
    let source = r#"
        struct Wrap { void (*func)(void); };
        int global = 0;
        void inc() { global++; }
        struct Wrap wrap = (struct Wrap){inc};
        int main() {
            wrap.func();
            if (global != 1) return 1;
            return 0;
        }
    "#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0);
}

#[test]
fn test_void_cast_on_array_parameter_regression() {
    let source = r#"
        void f(int a[const volatile 10]) {
            (void)a;
        }
        int main() {
            int x[10];
            f(x);
            return 0;
        }
    "#;
    // This previously panicked in clif_gen due to the (void)a cast.
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0);
}

#[test]
fn test_array_with_large_zero_init() {
    // this must be fast
    let source = r#"
        int bigarray[2147483647];
        int main() { return 0; }
    "#;
    run_pass(source, CompilePhase::EmitObject);
}

#[test]
fn test_array_size_in_tenary() {
    let code = r#"
    int main() {
        // This array size calculation relies on constant folding of the ternary operator.
        // If it fails, it might be treated as a VLA of size 0 or cause a crash.
        int a[1 ? 1 : 10];

        a[0] = 42;
        return a[0];
    }
    "#;
    let output = run_c_code_exit_status(code);
    assert_eq!(output, 42);
}

#[test]
fn test_struct_identity_cast_cranelift_ir() {
    let src = "
        struct S { int a; };
        void foo() {
            struct S s;
            struct S s2 = (struct S)s;
        }
    ";

    let clif_output = setup_cranelift(src);
    insta::assert_snapshot!(clif_output, @"
    ; Function: foo
    function u0:0() system_v {
        ss0 = explicit_slot 4, align = 4
        ss1 = explicit_slot 4, align = 4
        sig0 = (i64, i64, i64) -> i64 system_v
        fn0 = u0:1 sig0

    block0:
        v0 = stack_addr.i64 ss0
        v1 = stack_addr.i64 ss1
        v2 = iconst.i64 4
        v3 = call fn0(v1, v0, v2)  ; v2 = 4
        return
    }
    ");
}

#[test]
fn test_store_truncation_overflow_regression() {
    let source = r#"
typedef unsigned char u8;

int main() {
    // Layout: field at 0. padding/sentinel at 1..7.
    // If we increment field, and it stores 4 bytes, it will overwrite 1,2,3.

    struct {
        u8 val;
        u8 pad[7];
    } s;

    // Initialize
    s.val = 10;
    for(int i=0; i<7; i++) s.pad[i] = 0xAA;

    // Increment (s.val++ -> Assign(s.val, Add(s.val, 1)))
    // If store size is not truncated to u8, it writes 4 bytes.
    s.val++;

    if (s.val != 11) return 1;

    for(int i=0; i<3; i++) {
        if (s.pad[i] != 0xAA) {
            return 2;
        }
    }

    return 0;
}
"#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0, "Memory corruption detected in store truncation");
}
