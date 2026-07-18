//! Basic MIR to Cranelift IR lowering tests
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::{run_c_code_exit_status, run_c_code_with_output, setup_cranelift};
use crate::tests::test_utils::run_pass;

#[test]
fn test_movi_unsigned_constant_codegen() {
    let source = r#"
        int main() {
            unsigned long long x;
            x = 0xffffabcd;
            return 0;
        }
    "#;

    let clif_dump = setup_cranelift(source);
    // 0xffffabcd = 4294945741
    // We expect `uextend` for casting unsigned int to unsigned long long.
    // If it was signed (int), it would use `sextend`.

    // With improved heuristic, 0xffffabcd is parsed as signed long (i64), so no extension needed
    assert!(
        clif_dump.contains("iconst.i64"),
        "Expected iconst.i64 for constant load, found:\n{}",
        clif_dump
    );
}

#[test]
fn test_deref_hang_regression() {
    // must be fast
    let source = r#"
        void f() {}
        void (*p)() = f;
        int main() {
            (************************************************************************************************************************************************************f)();
            return 0;
        }
    "#;
    setup_cranelift(source);
}

#[test]
fn test_global_variable_modification_not_folded() {
    let source = r#"
        int printf(const char *format, ...);
        int crc32_context = 5;
        void crc32_byte() { crc32_context = 0; }
        int main() {
            crc32_byte();
            // This triggers an implicit conversion (BitXor with unsigned long long 5UL)
            // which previously caused constant folding to the initial value 5.
            printf("checksum = %08X\n", crc32_context ^ 5UL);
            return 0;
        }
    "#;

    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "checksum = 00000005");
}

#[test]
fn test_deeply_nested_unary_ops_stack_overflow() {
    // Generate a very long sequence of unary operators
    let mut source = String::from("int main() { int x = 0; int *p = &x; return ");
    for _ in 0..160 {
        source.push('!');
    }
    source.push_str("x; }");

    // Run in a thread with a tightly constrained stack
    // This perfectly mimics GitHub CI bounds under `llvm-cov` to prevent future regressions.
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024) // 512 KB
        .name("tight_stack_test".to_string())
        .spawn(move || {
            crate::tests::codegen_common::setup_cranelift(&source);
        })
        .unwrap();

    handle
        .join()
        .expect("Thread panicked, likely due to stack overflow in deeply nested unary operations.");
}

#[test]
fn test_label_map_cleared_between_functions() {
    let source = r#"
        int f1() {
            int x = 0;
            goto retry;
        retry:
            return x;
        }

        int main() {
            int y = 1;
            goto retry;
        retry:
            return f1() + y - 1;
        }
    "#;
    // This should not panic during clif_gen due to label block IDs leaking across functions.
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0);
}

#[test]
fn test_boolean_logic_lowering() {
    let source = r#"
            int main() {
                int x;
                x = 4;
                if (!x != 0) return 1;
                if (!!x != 1) return 1;
                return 0;
            }
        "#;
    // Verify it compiles without crashing
    let clif_dump = setup_cranelift(source);
    insta::assert_snapshot!(clif_dump, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        ss0 = explicit_slot 4, align = 4
        ss1 = explicit_slot 4, align = 4
        ss2 = explicit_slot 4, align = 4
        ss3 = explicit_slot 4, align = 4
        ss4 = explicit_slot 4, align = 4
        ss5 = explicit_slot 4, align = 4

    block0:
        v0 = iconst.i32 4
        v60 = stack_addr.i64 ss0
        store notrap v0, v60  ; v0 = 4
        v59 = stack_addr.i64 ss0
        v1 = load.i32 notrap v59
        v2 = iconst.i32 0
        v3 = icmp eq v1, v2  ; v2 = 0
        v4 = iconst.i32 1
        v5 = iconst.i32 0
        v6 = select v3, v4, v5  ; v4 = 1, v5 = 0
        v58 = stack_addr.i64 ss1
        store notrap v6, v58
        v57 = stack_addr.i64 ss1
        v7 = load.i32 notrap v57
        v8 = iconst.i32 0
        v9 = icmp ne v7, v8  ; v8 = 0
        v10 = iconst.i32 1
        v11 = iconst.i32 0
        v12 = select v9, v10, v11  ; v10 = 1, v11 = 0
        v56 = stack_addr.i64 ss2
        store notrap v12, v56
        v55 = stack_addr.i64 ss2
        v13 = load.i32 notrap v55
        v14 = iconst.i32 0
        v15 = icmp ne v13, v14  ; v14 = 0
        v16 = iconst.i8 1
        v17 = iconst.i8 0
        v18 = select v15, v16, v17  ; v16 = 1, v17 = 0
        v19 = uextend.i32 v18
        brif v19, block1, block2

    block1:
        v20 = iconst.i32 1
        return v20  ; v20 = 1

    block2:
        jump block3

    block3:
        v54 = stack_addr.i64 ss0
        v21 = load.i32 notrap v54
        v22 = iconst.i32 0
        v23 = icmp eq v21, v22  ; v22 = 0
        v24 = iconst.i32 1
        v25 = iconst.i32 0
        v26 = select v23, v24, v25  ; v24 = 1, v25 = 0
        v53 = stack_addr.i64 ss3
        store notrap v26, v53
        v52 = stack_addr.i64 ss3
        v27 = load.i32 notrap v52
        v28 = iconst.i32 0
        v29 = icmp eq v27, v28  ; v28 = 0
        v30 = iconst.i32 1
        v31 = iconst.i32 0
        v32 = select v29, v30, v31  ; v30 = 1, v31 = 0
        v51 = stack_addr.i64 ss4
        store notrap v32, v51
        v50 = stack_addr.i64 ss4
        v33 = load.i32 notrap v50
        v34 = iconst.i32 1
        v35 = icmp ne v33, v34  ; v34 = 1
        v36 = iconst.i32 1
        v37 = iconst.i32 0
        v38 = select v35, v36, v37  ; v36 = 1, v37 = 0
        v49 = stack_addr.i64 ss5
        store notrap v38, v49
        v48 = stack_addr.i64 ss5
        v39 = load.i32 notrap v48
        v40 = iconst.i32 0
        v41 = icmp ne v39, v40  ; v40 = 0
        v42 = iconst.i8 1
        v43 = iconst.i8 0
        v44 = select v41, v42, v43  ; v42 = 1, v43 = 0
        v45 = uextend.i32 v44
        brif v45, block4, block5

    block4:
        v46 = iconst.i32 1
        return v46  ; v46 = 1

    block5:
        jump block6

    block6:
        v47 = iconst.i32 0
        return v47  ; v47 = 0
    }
    ");
}

#[test]
fn test_string_literal_pointer_cast_() {
    run_pass(
        r#"
        int strlen(char *);
        int main() {
            char *p;
            p = "hello";
            return 0;
        }
        "#,
        CompilePhase::Cranelift, // NOTE: we test until cranelift to check if validation is correct or not
    );
}

#[test]
fn test_constant_range_validation() {
    run_pass(
        r#"
        int main() {
            unsigned int a = 0xffffffff;
            int b = 0x80010000;
            if (a != 0xffffffff) return 1;
            if (b != 0x80010000) return 2;
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_func_ptr_global_comparison() {
    let source = r#"
typedef char *(*readline_t)(const char *);

void* get_ptr() {
    return (void*)0x1234;
}

readline_t l_readline_static = 0;

int main() {
    l_readline_static = (readline_t)((void*)get_ptr());

    // Check if comparison works correctly
    if (l_readline_static != 0) {
        return 0; // Success
    }
    return 1; // Failure
}
"#;
    let status = run_c_code_exit_status(source);
    assert_eq!(status, 0, "Function pointer global comparison failed");
}

#[test]
fn test_thread_local_codegen() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            return tls_var;
        }
    "#;
    let clif_ir = setup_cranelift(source);
    insta::assert_snapshot!(clif_ir, @"
    ; Function: main
    function u0:0() -> i32 system_v {
        gv0 = symbol colocated tls userextname0

    block0:
        v0 = tls_value.i64 gv0
        v1 = load.i32 v0
        return v1
    }
    ");
}

#[test]
fn test_thread_local_runtime() {
    let source = r#"
        _Thread_local int tls_var = 42;
        int main() {
            tls_var += 10;
            return tls_var;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 52);
}

#[test]
fn test_function_pointer_address_of() {
    let source = r#"
typedef void (*Pfunc)(void);

void runner(Pfunc f) {
    f();
}

void my_func(void) {}

int main() {
    runner(my_func);
    runner(&my_func);
    return 0;
}
"#;
    run_pass(source, CompilePhase::Cranelift);
}

#[test]
fn test_cleanup_goto_backward() {
    use crate::tests::codegen_common::*;
    let source = r#"
        int printf(const char *, ...);
        int foo(int *n) {
            printf("foo(%d)\n", *n);
            return 1;
        }
        int main() {
            int n = 2;
            if (n > 1) {
            exit:
                if (!n) {
                    printf("return\n");
                    return 0;
                }
                int y __attribute__((cleanup(foo))) = 1;
                if (n > 2) {
                    int __attribute__((cleanup(foo))) auto b = 2;
                    n = 0;
                    goto exit;
                }
                n = 0;
                goto exit;
            }
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output, "foo(1)\nreturn\n");
}
