use super::semantic_common::{setup_diagnostics_output, run_pass};
use crate::driver::artifact::CompilePhase;

#[test]
fn test_assign_struct_to_int() {
    let output = setup_diagnostics_output(
        r#"
        struct A { int x; };
        int main() {
            struct A a;
            int i;
            i = a;
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found struct A
    Location: 6:13
    "###);
}

#[test]
fn test_assign_int_to_struct() {
    let output = setup_diagnostics_output(
        r#"
        struct A { int x; };
        int main() {
            struct A a;
            a = 10;
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found int
    Location: 5:13
    "###);
}

#[test]
fn test_assign_incompatible_struct() {
    let output = setup_diagnostics_output(
        r#"
        struct A { int x; };
        struct B { int x; };

        int main() {
            struct A a;
            struct B b;
            a = b; 
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found struct B
    Location: 8:13
    "###);
}

#[test]
fn test_assign_incompatible_pointers() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int a = 10;
            int *p = &a;
            float *f;
            f = p;
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected <pointer>, found <pointer>
    Location: 6:13
    "###);
}

#[test]
fn test_assign_int_to_pointer() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int *p;
            p = 5; // Invalid (except 0)
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected <pointer>, found int
    Location: 4:13
    "###);
}

#[test]
fn test_assign_pointer_to_int() {
    let output = setup_diagnostics_output(
        r#"
        int main() {
            int i;
            int *p;
            i = p; // Invalid without cast
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found <pointer>
    Location: 5:13
    "###);
}

#[test]
fn test_assign_struct_mismatch() {
    let output = setup_diagnostics_output(
        r#"
        struct A { int x; };
        struct B { int x; };
        int main() {
            struct A a;
            struct B b;
            a = b;
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found struct B
    Location: 7:13
    "###);
}

#[test]
fn test_assign_valid_void_ptr() {
    run_pass(
        r#"
        int main() {
            int a;
            int *p = &a;
            void *v;
            v = p; // int* -> void* OK
            p = v; // void* -> int* OK
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_assign_valid_null_ptr() {
    run_pass(
        r#"
        int main() {
            int *p;
            p = 0; // OK
            p = (void*)0; // OK
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_assign_pointer_to_bool() {
    run_pass(
        r#"
        int main() {
            int *p;
            _Bool b;
            b = p; // OK
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_assign_valid_arithmetic() {
    run_pass(
        r#"
        int main() {
            int i;
            float f;
            i = 3.14; // OK (conversion)
            f = 10;   // OK (conversion)
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_void_init_variable() {
    let output = setup_diagnostics_output(
        r#"
        void foo() {}

        int main() {
            int x = foo();
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found void
    Location: 5:21
    "###);
}

#[test]
fn test_void_assign_variable() {
    let output = setup_diagnostics_output(
        r#"
        void foo() {}

        int main() {
            int x;
            x = foo();
            return 0;
        }
    "#);
    insta::assert_snapshot!(output, @r###"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found void
    Location: 6:13
    "###);
}

#[test]
fn test_assign_enum_to_int() {
    run_pass(
        r#"
        enum E { X };
        int main() {
            enum E e = X;
            int i = e;
            return i;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_assign_int_to_enum() {
    run_pass(
        r#"
        enum E { X };
        int main() {
            enum E e;
            e = 0;
            return e;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_enum_constant_assignment() {
    run_pass(
        r#"
        enum E { X };
        int main() {
            enum E e;
            e = X;
            return e;
        }
    "#,
        CompilePhase::Mir,
    );
}
