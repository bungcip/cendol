use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_array_completion_composite() {
    run_pass(
        r#"
        extern int a[];
        int a[10];
        int main() {
            return sizeof(a) - 10 * sizeof(int);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_array_of_pointers_composite() {
    run_pass(
        r#"
        extern int *a[];
        extern int *a[10];
        int main() {
            return sizeof(a) - 10 * sizeof(int*);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_conflicting_array_composite() {
    run_fail_with_message(
        r#"
        extern int a[5];
        extern int a[10];
        "#,
        "conflicting types",
    );
}

#[test]
fn test_array_completion_reverse() {
    run_pass(
        r#"
        int a[10];
        extern int a[];
        int main() {
            return sizeof(a) - 10 * sizeof(int);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_function_composite_type() {
    run_pass(
        r#"
        int f(int a[]);
        int f(int a[5]) {
            return 0;
        }
        int main() {
            return f(0);
        }
        "#,
        CompilePhase::Mir,
    );
}

// Consolidated from guardian_struct_member_constraints.rs and semantic_negative.rs
#[test]
fn test_void_member_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            void v;
        };
        "#,
        "incomplete type",
    );
}

#[test]
fn test_incomplete_struct_member_prohibited() {
    run_fail_with_message(
        r#"
        struct Incomplete;
        struct T {
            struct Incomplete s;
        };
        "#,
        "incomplete type",
    );
}

#[test]
fn test_function_member_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            void f(void);
        };
        "#,
        "member 'f' has function type",
    );
}

#[test]
fn test_vla_member_prohibited() {
    run_fail_with_message(
        r#"
        void f(int n) {
            struct S {
                int a[n];
            };
        }
        "#,
        "variably modified type",
    );
}

#[test]
fn test_fam_in_union_prohibited() {
    run_fail_with_message(
        r#"
        union U {
            int x;
            int a[];
        };
        "#,
        "incomplete/VLA array in union",
    );
}

#[test]
fn test_fam_not_last_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            int a[];
            int x;
        };
        "#,
        "flexible array member must be the last member of a structure",
    );
}

#[test]
fn test_fam_in_otherwise_empty_struct_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            int a[];
        };
        "#,
        "flexible array member in otherwise empty structure",
    );
}

#[test]
fn test_duplicate_member() {
    run_fail_with_message(
        r#"
        struct A {
            int x;
            float x;
        };
        "#,
        "duplicate member",
    );
}

#[test]
fn test_bitfield_invalid_type() {
    run_fail_with_message(
        r#"
        struct A {
            float x : 3;
        };
        "#,
        "bit-field",
    );
}

#[test]
fn test_recursive_struct_definition() {
    run_fail_with_message(
        r#"
        struct A {
            struct A x;
        };
        "#,
        "recursive type definition",
    );
}

#[test]
fn test_member_access_on_non_struct() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 5;
            x.field = 10;
        }
        "#,
        "not a structure or union",
    );
}

// Consolidated from guardian_bitfields.rs
#[test]
fn test_bitfield_zero_width_unnamed() {
    run_pass(r#"struct S { int x : 1; int : 0; int y : 1; };"#, CompilePhase::Mir);
}

#[test]
fn test_bitfield_width_exceeds_type() {
    run_fail_with_message(
        r#"struct S { char c : 9; };"#,
        "width of bit-field (9 bits) exceeds width of its type (8 bits)",
    );
}

#[test]
fn test_atomic_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            _Atomic int x : 1;
        };
        "#,
        "bit-field shall not have an atomic type",
    );
}

#[test]
fn test_atomic_specifier_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            _Atomic(int) x : 1;
        };
        "#,
        "bit-field shall not have an atomic type",
    );
}

#[test]
fn test_unnamed_atomic_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            _Atomic int : 1;
        };
        "#,
        "bit-field shall not have an atomic type",
    );
}

#[test]
fn test_atomic_typedef_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        typedef _Atomic int atomic_int;
        struct S {
            atomic_int x : 1;
        };
        "#,
        "bit-field shall not have an atomic type",
    );
}

#[test]
fn test_atomic_volatile_bitfield_prohibited() {
    run_fail_with_message(
        r#"
        struct S {
            _Atomic volatile int x : 1;
        };
        "#,
        "bit-field shall not have an atomic type",
    );
}

#[test]
fn test_volatile_bitfield_allowed() {
    run_pass(
        r#"
        struct S {
            volatile int x : 1;
        };
        "#,
        CompilePhase::Mir,
    );
}
