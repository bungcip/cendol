use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_selection_bitfield_constraints() {
    // C11 6.5.3.4p1: "The sizeof operator shall not be applied to... a bit-field member."
    // C11 6.5.3.2p1: "The operand of the unary & operator shall be... an lvalue that designates an object that is not a bit-field..."
    // Even when wrapped in _Generic, these constraints must be enforced on the selected expression.

    // 1. sizeof(bit-field) via _Generic
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

    // 2. &(bit-field) via _Generic
    run_fail_with_message(
        r#"
        struct S { int x : 1; };
        int main() {
            struct S s;
            void *p = &_Generic(0, int: s.x);
        }
        "#,
        "cannot take address of bit-field",
    );
}

#[test]
fn test_generic_selection_register_constraints() {
    // C11 6.5.3.2p1: "The operand of the unary & operator shall be... an lvalue that designates an object... not declared with the register storage-class specifier."

    run_fail_with_message(
        r#"
        int main() {
            register int x = 0;
            void *p = &_Generic(0, int: x);
        }
        "#,
        "cannot take address of 'register' variable",
    );
}

#[test]
fn test_generic_selection_lvalue_preservation() {
    // Verify that _Generic preserves lvalue-ness for assignments.
    run_pass(
        r#"
        int main() {
            int x = 0;
            _Generic(0, int: x) = 10;
            return x == 10 ? 0 : 1;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_lvalue_conversion_strips_qualifiers() {
    // C11 6.5.1.1p2: "The type of the controlling expression is the type of the expression
    // as it would have been after lvalue conversion... are applied."
    // 6.3.2.1p2: "...if the lvalue has a qualified type, the rvalue has the unqualified
    // version of the type."

    // Thus, _Generic(const_int_lvalue, ...) should match 'int', not 'const int'.
    run_pass(
        r#"
        int main() {
            const int ci = 0;
            _Static_assert(_Generic(ci, int: 1, const int: 0), "Should match int");

            const volatile int cvi = 0;
            _Static_assert(_Generic(cvi, int: 1, const int: 0, volatile int: 0, const volatile int: 0), "Should match int");

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_matches_qualified_pointer_types() {
    // Pointer to qualified types are NOT stripped by lvalue conversion,
    // only the top-level qualifier of the pointer itself is stripped.
    run_pass(
        r#"
        int main() {
            const int *pci;
            _Static_assert(_Generic(pci, const int *: 1, int *: 0), "Should match const int *");

            int * const cpi = 0;
            // cpi is 'const pointer to int'. Lvalue conversion strips top-level const.
            // Result is 'pointer to int'.
            _Static_assert(_Generic(cpi, int *: 1, int * const: 0), "Should match int *");

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_atomic_lvalue_conversion() {
    run_pass(
        r#"
        int main() {
            _Atomic int ai = 0;
            // Lvalue conversion strips _Atomic.
            _Static_assert(_Generic(ai, int: 1, _Atomic int: 0), "Should match int");

            _Atomic(int *) pai = 0;
            // Lvalue conversion strips _Atomic. Result is int *.
            _Static_assert(_Generic(pai, int *: 1, _Atomic(int *): 0), "Should match int *");

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_rejects_compatible_array_types() {
    run_fail_with_message(
        r#"
        int main() {
            int a[10];
            return _Generic(&a, int(*)[10]: 1, int(*)[]: 2);
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_generic_selection_rejects_compatible_enum_type() {
    run_fail_with_message(
        r#"
        enum E { A = -1 };
        int main() {
            // enum E is compatible with 'int' because it has a negative value
            return _Generic(0, int: 1, enum E: 2);
        }
        "#,
        "compatible with previously specified type",
    );

    run_fail_with_message(
        r#"
        enum E { A };
        int main() {
            // enum E is compatible with 'int' (A=0 fits in int)
            return _Generic(0, int: 1, enum E: 2);
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_generic_selection_rejects_compatible_function_pointers() {
    // Parameter names don't affect compatibility
    run_fail_with_message(
        r#"
        int main() {
            return _Generic((void(*)(int))0, void(*)(int x): 1, void(*)(int y): 2);
        }
        "#,
        "compatible with previously specified type",
    );
}

#[test]
fn test_generic_selection_qualifier_compatibility_constraints() {
    // C11 6.5.1.1p2: "No two generic associations in the same generic selection
    // shall specify compatible types."

    // 1. int and const int are NOT compatible types and can both be present.
    run_pass(
        r#"
        int main() {
            return _Generic(0, int: 1, const int: 2);
        }
        "#,
        CompilePhase::Mir,
    );

    // 2. Exact same types are compatible and must be rejected.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, int: 1, int: 2);
        }
        "#,
        "compatible with previously specified type 'int'",
    );
}

#[test]
fn generic_selection_distinguishes_atomic_types() {
    // C11 6.5.1.1p2: "No two generic associations in the same generic selection
    // shall specify compatible types."
    // 6.7.3p10: "For two qualified types to be compatible, both shall have the identically
    // qualified version of a compatible type."
    // _Atomic int and int are not compatible.

    // 1. int and _Atomic int are NOT compatible and can both be present.
    run_pass(
        r#"
        int main() {
            _Atomic int a = 0;
            // Matches int because lvalue conversion drops _Atomic.
            return _Generic(a, int: 1, _Atomic int: 2);
        }
        "#,
        CompilePhase::Mir,
    );

    // 2. Two _Atomic int associations are compatible and must be rejected.
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, _Atomic int: 1, _Atomic int: 2);
        }
        "#,
        "compatible with previously specified type '_Atomic int'",
    );
}

#[test]
fn test_generic_incomplete_array_allowed() {
    // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type, or the void type.
    // An incomplete array decays to a pointer, which IS a complete object type.
    run_pass(
        r#"
        extern int a[];
        int main() {
            return _Generic(a, int*: 1, default: 0);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_function_allowed() {
    // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type, or the void type.
    // A function type decays to a function pointer, which IS a complete object type.
    run_pass(
        r#"
        void f(void);
        int main() {
            return _Generic(f, void(*)(void): 1, default: 0);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_incomplete_struct_prohibited() {
    // C11 6.5.1.1p2: The controlling expression shall be an expression of a complete object type, or the void type.
    run_fail_with_message(
        r#"
        struct S;
        extern struct S s;
        int main() {
            return _Generic(s, default: 1);
        }
        "#,
        "controlling expression type 'struct S' is an incomplete type",
    );
}

#[test]
fn test_generic_void_allowed() {
    // C11 6.5.1.1p2 explicitly allows the void type for the controlling expression.
    run_pass(
        r#"
        int main() {
            return _Generic((void)0, default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_complete_object_types_allowed() {
    run_pass(
        r#"
        struct S { int x; };
        int main() {
            int i;
            struct S s;
            int a[10];
            _Generic(i, int: 1);
            _Generic(s, struct S: 1);
            _Generic(a, int*: 1);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_selection_npc_preservation() {
    // _Generic should act as a null pointer constant if the selected branch is one.
    run_pass(
        r#"
        int main() {
            void *p = _Generic(0, int: 0);
            void *q = _Generic(0, int: (void*)0);
            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
