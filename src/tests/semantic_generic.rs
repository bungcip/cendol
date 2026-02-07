use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_generic_controlling_expression_must_be_complete() {
    run_fail_with_message(
        r#"
        void foo();
        int main() {
            return _Generic(foo(), default: 1);
        }
        "#,
        CompilePhase::Mir,
        "controlling expression type 'void' is an incomplete type",
    );
}

#[test]
fn test_generic_controlling_expression_incomplete_struct() {
    run_fail_with_message(
        r#"
        struct A;
        void f(struct A* p) {
            _Generic(*p, default: 1);
        }
        "#,
        CompilePhase::Mir,
        "controlling expression type 'struct A' is an incomplete type",
    );
}

#[test]
fn test_generic_association_must_be_complete() {
    run_fail_with_message(
        r#"
        struct Incomplete;
        int main() {
            return _Generic(0, struct Incomplete: 1, default: 0);
        }
        "#,
        CompilePhase::Mir,
        "generic association specifies incomplete type 'struct Incomplete'",
    );
}

#[test]
fn test_generic_association_void_is_incomplete() {
    run_fail_with_message(
        r#"
        int main() {
            return _Generic(0, void: 1, default: 0);
        }
        "#,
        CompilePhase::Mir,
        "generic association specifies incomplete type 'void'",
    );
}

#[test]
fn test_generic_allows_array_decay() {
    // This should pass because array decays to pointer, which is complete.
    run_pass(
        r#"
        int main() {
            int a[10];
            return _Generic(a, int*: 0, default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_allows_function_decay() {
    run_pass(
        r#"
        void f() {}
        int main() {
            return _Generic(f, void (*)(void): 0, default: 1);
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_qualifiers_distinct() {
    run_pass(
        r#"
        int main() {
            int i = 0;
            const int ci = 0;
            // int and const int are distinct types, so both can appear in associations.
            // Note: _Generic controlling expression undergoes lvalue conversion, dropping qualifiers.
            // So 'ci' (const int) becomes 'int', matching 'int' association.
            int r1 = _Generic(ci, int: 1, const int: 2);
            int r2 = _Generic(i, int: 1, const int: 2);
            return r1 + r2;
        }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_generic_pointer_qualifiers_distinct() {
    run_pass(
        r#"
        int main() {
            int *p;
            // int *, const int *, and int * const are all distinct types.
            // p is int *. Matches int *.
            int r1 = _Generic(p, int *: 1, const int *: 2, int * const: 3);

            const int *cp;
            // cp is const int *. Matches const int *.
            int r2 = _Generic(cp, int *: 1, const int *: 2, int * const: 3);

            int * const pc = 0;
            // pc is int * const. Lvalue conversion drops top-level const -> int *. Matches int *.
            // Note: int * const association is unreachable for lvalues, but valid as distinct type.
            int r3 = _Generic(pc, int *: 1, const int *: 2, int * const: 3);

            return 0;
        }
        "#,
        CompilePhase::Mir,
    );
}
