//! Tests for Struct/Union/Array lowering and access
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::test_utils::run_pass;

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
