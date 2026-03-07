use super::semantic_common::setup_mir;
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_nested_scope_shadowing() {
    let source = r#"
        typedef struct s s;
        struct s {
            int x;
        };

        int main() {
            struct s s;
            s.x = 1;
            {
                int s = 2;
                if (s != 2) return 1;
            }
            return s.x - 1;
        }
        "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn allows_parameter_to_shadow_typedef() {
    let source = r#"
typedef int T;
void f(int T) {
    T = 1;
}

int main() {
    f(0);
    return 0;
}
        "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn allows_typedef_and_struct_tag_with_same_name() {
    run_pass(
        r#"
typedef int T;
struct T { int i; };
int main() {
    struct T var;
    var.i = 0;
    T other_var = 1;
    return 0;
}
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_function_redefinition_with_prototype() {
    let source = r#"
            int x;
            int x = 3;
            int x;

            int main();

            void *
            foo()
            {
                return &main;
            }

            int
            main()
            {
                if (x != 3)
                    return 0;

                x = 0;
                return x;
            }
        "#;

    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump, @r"
        type %t0 = i32
        type %t1 = void
        type %t2 = ptr<%t1>
        type %t3 = fn() -> %t0
        type %t4 = ptr<%t3>

        global @x: i32 = const 3

        fn main() -> i32
        {
          locals {
            %1: i32
          }

          bb2:
            %1 = @x != const 3
            cond_br %1, bb3, bb4

          bb3:
            return const 0

          bb4:
            br bb5

          bb5:
            @x = const 0
            return @x
        }

        fn foo() -> ptr<void>
        {

          bb1:
            return const main
        }
        ");
}

#[test]
fn rejects_conflicting_typedef_redefinition() {
    let source = r#"
typedef int T;
typedef float T;
        "#;
    run_fail_with_message(source, "redefinition of 'T' with a different type");
}

#[test]
fn allows_compatible_typedef_redefinition() {
    run_pass(
        r#"
        typedef int T;
        typedef int T;
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn allows_function_parameter_to_shadow_typedef() {
    run_pass(
        r#"
typedef int T;
void foo(T T) {}
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn rejects_variable_declaration_conflicting_with_typedef() {
    run_fail_with_message(
        r#"
typedef int T;
int T;
        "#,
        "redefinition of 'T'",
    );
}

#[test]
fn rejects_typedef_declaration_conflicting_with_variable() {
    run_fail_with_message(
        r#"
int T;
typedef int T;
        "#,
        "redefinition of 'T'",
    );
}

#[test]
fn rejects_extern_variable_declaration_conflicting_with_typedef() {
    run_fail_with_message(
        r#"
typedef int T;
extern int T;
        "#,
        "redefinition of 'T'",
    );
}

// Consolidated from guardian_typedef_constraints.rs and semantic_negative.rs
#[test]
fn test_typedef_redefinition_compatible_but_not_same() {
    run_fail_with_message(
        r#"
        typedef int A[];
        typedef int A[10];
        "#,
        "redefinition of 'A' with a different type",
    );
}

#[test]
fn test_typedef_redefinition_defines_new_struct() {
    run_fail_with_message(
        r#"
        typedef struct { int x; } S;
        typedef struct { int x; } S;
        "#,
        "redefinition of 'S'",
    );
}

#[test]
fn test_typedef_redefinition_using_same_tag_ok() {
    run_pass(
        r#"
        struct s { int x; };
        typedef struct s S;
        typedef struct s S;
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_typedef_redefinition_function_params_ok() {
    run_pass(
        r#"
        typedef int (*F)(int a);
        typedef int (*F)(int b);
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_typedef_redefinition_function_params_different_type_rejects() {
    run_fail_with_message(
        r#"
        typedef int (*F)(int a);
        typedef int (*F)(float b);
        "#,
        "redefinition of 'F' with a different type",
    );
}

#[test]
fn test_undeclared_variable() {
    run_fail_with_message(
        r#"
        int main() {
            x = 5;
        }
        "#,
        "Undeclared",
    );
}

// Consolidated from guardian_linkage.rs and guardian_tentative_definitions.rs
#[test]
fn test_static_followed_by_extern_variable_ok() {
    run_pass(
        r#"
        static int x;
        extern int x;
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_block_scope_static_shadowing_global_is_ok() {
    run_pass(
        r#"
        int x;
        void f(void) {
            static int x; // Shadows global x, no linkage conflict
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_block_scope_extern_refers_to_global_static() {
    run_pass(
        r#"
        static int x;
        void f(void) {
            extern int x;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_followed_by_plain_variable_ok() {
    run_pass(
        r#"
        static int x;
        int x;
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_followed_by_extern_function_ok() {
    run_pass(
        r#"
        static void f(void);
        extern void f(void);
        void f(void) {}
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_file_scope_tentative_external_linkage_ok() {
    run_pass("int arr[]; int main() { return 0; }", CompilePhase::Mir);
}

#[test]
fn test_extern_incomplete_array_ok() {
    run_pass("extern int arr[];", CompilePhase::Mir);
    run_pass("void f() { extern int arr[]; }", CompilePhase::Mir);
}

#[test]
fn test_void_parameter_ok() {
    run_pass("void f(void) {}", CompilePhase::Mir);
}

#[test]
fn test_array_parameter_decay_ok() {
    run_pass("void f(int arr[]) {}", CompilePhase::Mir);
}

#[test]
fn test_incomplete_type_in_prototype_ok() {
    run_pass("struct S; void f(struct S s);", CompilePhase::Mir);
    run_pass("void f(int arr[]);", CompilePhase::Mir);
}

#[test]
fn test_initialized_array_block_scope_ok() {
    run_pass("void f() { int a[] = {1, 2, 3}; }", CompilePhase::Mir);
}

#[test]
fn test_variable_visible_in_its_own_initializer() {
    run_pass(
        r#"
        int main() {
            int x = sizeof(x);
            void *p = &p;
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_global_variable_visible_in_its_own_initializer() {
    run_pass(
        r#"
        int x = sizeof(x);
        void *p = &p;
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_global_variable_alignment_mismatch() {
    let source = r#"
        _Alignas(8) int foo;
        _Alignas(16) int foo;
    "#;
    run_fail_with_message(source, "redefinition");
}
