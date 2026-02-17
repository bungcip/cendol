use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_typedef_inline_prohibited() {
    run_fail_with_message(
        "typedef inline int f(void);",
        CompilePhase::Mir,
        "'inline' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_typedef_noreturn_prohibited() {
    run_fail_with_message(
        "typedef _Noreturn void f(void);",
        CompilePhase::Mir,
        "'_Noreturn' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_tag_decl_inline_prohibited() {
    run_fail_with_message(
        "void f() { inline struct S; }",
        CompilePhase::Mir,
        "'inline' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_tag_decl_noreturn_prohibited() {
    run_fail_with_message(
        "void f() { _Noreturn struct S; }",
        CompilePhase::Mir,
        "'_Noreturn' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_struct_member_inline_prohibited() {
    run_fail_with_message(
        "struct S { inline int (*f)(void); };",
        CompilePhase::Mir,
        "'inline' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_struct_member_noreturn_prohibited() {
    run_fail_with_message(
        "struct S { _Noreturn int (*f)(void); };",
        CompilePhase::Mir,
        "'_Noreturn' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_variable_inline_prohibited() {
    run_fail_with_message(
        "inline int x;",
        CompilePhase::Mir,
        "'inline' function specifier appears on non-function declaration",
    );
}

#[test]
fn test_variable_noreturn_prohibited() {
    run_fail_with_message(
        "_Noreturn int x;",
        CompilePhase::Mir,
        "'_Noreturn' function specifier appears on non-function declaration",
    );
}
