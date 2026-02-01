//! Tests for Struct/Union/Array lowering and access
use crate::ast::NameId;
use crate::driver::artifact::CompilePhase;
use crate::mir::codegen::{ClifOutput, EmitKind, MirToCraneliftLowerer};
use crate::mir::{MirModuleId, MirStmt, MirType, Operand, Place, Terminator};
use crate::tests::codegen_common::setup_cranelift;
use crate::tests::semantic_common::run_pass;

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
        @r"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 8
        ss1 = explicit_slot 8
        ss2 = explicit_slot 4
        ss3 = explicit_slot 4

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
    println!("{}", clif_dump);

    // Expect loads/stores with zero offset (union fields share offset 0)
    assert!(
        clif_dump.contains("iconst.i64 0"),
        "expected zero offset constant in IR"
    );
    assert!(clif_dump.contains("store"), "expected store instruction in IR");
    assert!(clif_dump.contains("load"), "expected load instruction in IR");
}

#[test]
fn test_alloc_dealloc_codegen() {
    let mut builder = crate::mir::MirBuilder::new(MirModuleId::new(1).unwrap(), 8);

    let int_type_id = builder.add_type(MirType::I32);
    let ptr_type_id = builder.add_type(MirType::Pointer { pointee: int_type_id });
    let void_type_id = builder.add_type(MirType::Void);

    let func_id = builder.define_function(NameId::new("main"), vec![], void_type_id, false);
    builder.set_current_function(func_id);

    let entry_block_id = builder.create_block();
    builder.set_current_block(entry_block_id);
    builder.set_function_entry_block(func_id, entry_block_id);

    let local_p_id = builder.create_local(Some(NameId::new("p")), ptr_type_id, false);

    // p = alloc(...)
    builder.add_statement(MirStmt::Alloc(Place::Local(local_p_id), int_type_id));

    // dealloc(p)
    builder.add_statement(MirStmt::Dealloc(Operand::Copy(Box::new(Place::Local(local_p_id)))));

    builder.set_terminator(Terminator::Return(None));

    let mir = builder.consume();
    let lowerer = MirToCraneliftLowerer::new(mir);
    let result = lowerer.compile_module(EmitKind::Clif);

    match result {
        Ok(ClifOutput::ClifDump(clif_ir)) => {
            insta::assert_snapshot!(clif_ir, @r"
            ; Function: main
            function u0:0() system_v {
                ss0 = explicit_slot 8
                sig0 = (i64) -> i64 system_v
                sig1 = (i64) system_v
                fn0 = u0:1 sig0
                fn1 = u0:2 sig1

            block0:
                v0 = iconst.i64 4
                v1 = call fn0(v0)  ; v0 = 4
                v4 = stack_addr.i64 ss0
                store notrap v1, v4
                v3 = stack_addr.i64 ss0
                v2 = load.i64 notrap v3
                call fn1(v2)
                return
            }
            ");
        }
        Ok(ClifOutput::ObjectFile(_)) => panic!("Expected Clif dump, got object file"),
        Err(e) => panic!("MIR to Cranelift lowering failed: {}", e),
    }
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
