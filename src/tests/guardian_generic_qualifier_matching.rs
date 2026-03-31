use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

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
