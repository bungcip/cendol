use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_builtin_types_compatible_p_basic() {
    run_pass(
        r#"
        _Static_assert(__builtin_types_compatible_p(int, int), "int should be compatible with int");
        _Static_assert(__builtin_types_compatible_p(int, signed int), "int should be compatible with signed int");
        _Static_assert(!__builtin_types_compatible_p(int, long), "int should not be compatible with long");
        _Static_assert(__builtin_types_compatible_p(const int, const int), "const int should be compatible with const int");
        _Static_assert(__builtin_types_compatible_p(int, const int), "int should be compatible with const int (qualifiers ignored)");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_pointers() {
    run_pass(
        r#"
        _Static_assert(__builtin_types_compatible_p(int*, int*), "int* should be compatible with int*");
        _Static_assert(!__builtin_types_compatible_p(int*, char*), "int* should not be compatible with char*");
        _Static_assert(__builtin_types_compatible_p(void*, void*), "void* should be compatible with void*");

        _Static_assert(__builtin_types_compatible_p(int * const, int *), "int * const should be compatible with int * (top-level qualifier ignored)");
        _Static_assert(!__builtin_types_compatible_p(const int *, int *), "const int * should not be compatible with int * (not a top-level qualifier)");

        _Static_assert(__builtin_types_compatible_p(volatile int, int), "volatile int should be compatible with int");
        _Static_assert(__builtin_types_compatible_p(const volatile int, int), "const volatile int should be compatible with int");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_typedef() {
    run_pass(
        r#"
        typedef int my_int;
        _Static_assert(__builtin_types_compatible_p(int, my_int), "int should be compatible with my_int");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_enum() {
    run_pass(
        r#"
        enum E { A };
        _Static_assert(__builtin_types_compatible_p(enum E, unsigned int), "enum E should be compatible with its underlying type (unsigned int)");

        enum E2 { B = -1 };
        _Static_assert(__builtin_types_compatible_p(enum E2, int), "enum E2 should be compatible with its underlying type (int)");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_struct() {
    run_pass(
        r#"
        struct S { int x; };
        _Static_assert(__builtin_types_compatible_p(struct S, struct S), "struct S should be compatible with struct S");

        struct S2 { int x; };
        _Static_assert(!__builtin_types_compatible_p(struct S, struct S2), "struct S should not be compatible with struct S2");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}

#[test]
fn test_builtin_types_compatible_p_array() {
    run_pass(
        r#"
        _Static_assert(__builtin_types_compatible_p(int[10], int[10]), "int[10] should be compatible with int[10]");
        _Static_assert(!__builtin_types_compatible_p(int[10], int[11]), "int[10] should not be compatible with int[11]");
        _Static_assert(__builtin_types_compatible_p(int[], int[10]), "int[] should be compatible with int[10]");

        int main() { return 0; }
        "#,
        CompilePhase::Cranelift,
    );
}
