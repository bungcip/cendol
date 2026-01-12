use super::semantic_common::{run_fail_with_diagnostic, run_fail_with_message, run_pass};
use crate::driver::artifact::CompilePhase;

#[test]
fn test_assign_struct_to_int() {
    run_fail_with_message(
        r#"
        struct A { int x; };
        int main() {
            struct A a;
            int i;
            i = a;
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch",
    );
}

#[test]
fn test_assign_int_to_struct() {
    run_fail_with_message(
        r#"
        struct A { int x; };
        int main() {
            struct A a;
            a = 10;
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch",
    );
}

#[test]
fn test_assign_incompatible_struct() {
    run_fail_with_diagnostic(
        r#"
        struct A { int x; };
        struct B { int x; };

        int main() {
            struct A a;
            struct B b;
            a = b; 
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch: expected struct A, found struct B",
        8,
        13,
    );
}

#[test]
fn test_assign_incompatible_pointers() {
    run_fail_with_message(
        r#"
        int main() {
            int a = 10;
            int *p = &a;
            float *f;
            f = p;
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch", // pointers to different types are incompatible
    );
}

#[test]
fn test_assign_int_to_pointer() {
    run_fail_with_message(
        r#"
        int main() {
            int *p;
            p = 5; // Invalid (except 0)
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch",
    );
}

#[test]
fn test_assign_pointer_to_int() {
    run_fail_with_message(
        r#"
        int main() {
            int i;
            int *p;
            i = p; // Invalid without cast
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch",
    );
}

#[test]
fn test_assign_struct_mismatch() {
    run_fail_with_message(
        r#"
        struct A { int x; };
        struct B { int x; };
        int main() {
            struct A a;
            struct B b;
            a = b;
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch",
    );
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
    run_fail_with_message(
        r#"
        void foo() {}

        int main() {
            int x = foo();
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch", // or "initializing 'int' with an expression of incompatible type 'void'"
    );
}

#[test]
fn test_void_assign_variable() {
    run_fail_with_message(
        r#"
        void foo() {}

        int main() {
            int x;
            x = foo();
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "type mismatch",
    );
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
