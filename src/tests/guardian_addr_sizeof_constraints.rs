use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_address_of_bitfield_prohibited() {
    // C11 6.5.3.2p1: The operand of the unary & operator shall not be a bit-field.
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            int *p = &s.x;
            return 0;
        }
        "#,
        "cannot take address of bit-field",
    );
}

#[test]
fn test_address_of_register_prohibited() {
    // C11 6.5.3.2p1: The operand of the unary & operator shall not be a register variable.
    run_fail_with_message(
        r#"
        int main() {
            register int x = 0;
            int *p = &x;
            return 0;
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_sizeof_bitfield_prohibited() {
    // C11 6.5.3.4p1: The sizeof operator shall not be applied to a bit-field member.
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return sizeof(s.x);
        }
        "#,
        "cannot apply 'sizeof' to a bit-field",
    );
}

#[test]
fn test_address_of_bitfield_in_generic_prohibited() {
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            int *p = &_Generic(0, int: s.x);
            return 0;
        }
        "#,
        "cannot take address of bit-field",
    );
}

#[test]
fn test_sizeof_bitfield_in_generic_prohibited() {
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            return sizeof(_Generic(0, int: s.x));
        }
        "#,
        "cannot apply 'sizeof' to a bit-field",
    );
}

#[test]
fn test_address_of_array_member() {
    // Regression test: taking address of array member should give pointer to array, not decay first
    // &s.k where s.k is int[15] should give int(*)[15], not int*
    run_pass(
        r#"
        struct A
        {
            int k[15];
        };
        int main()
        {
            struct A s;
            int (*p)[15] = &s.k;
            return 35;
        }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_address_of_array_member_of_different_type() {
    // Another test with different array type
    run_pass(
        r#"
        struct S {
            double values[5];
        };
        int main() {
            struct S s;
            double (*p)[5] = &s.values;
            return 0;
        }
        "#,
        CompilePhase::Cranelift,
    );
}
