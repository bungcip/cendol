use super::semantic_common::setup_mir;
use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_exit_status;
use crate::tests::test_utils::{run_fail_with_message, run_pass, setup_diagnostics_output};

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

#[cfg(test)]
mod tests {
    use super::*;

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
            %1 = @x != cast<i32>(const 3)
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
            return cast<ptr<void>>(const main)
        }
        ");
    }
}

#[test]
fn rejects_conflicting_typedef_redefinition() {
    let source = r#"
typedef int T;
typedef float T;
        "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 2

    Level: Error
    Message: redefinition of 'T' with a different type
    Span: SourceSpan(source_id=SourceId(2), start=16, end=32)

    Level: Note
    Message: previous definition is here
    Span: SourceSpan(source_id=SourceId(2), start=1, end=15)
    ");
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
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
        CompilePhase::Mir,
        "redefinition of 'T'",
    );
}
