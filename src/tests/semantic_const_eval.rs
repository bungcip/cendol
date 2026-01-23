use crate::driver::artifact::CompilePhase;
use crate::tests::semantic_common::run_pass;

#[test]
fn test_sizeof_in_static_assert() {
    run_pass(
        r#"
        _Static_assert(sizeof(int) > 0, "sizeof(int) should be greater than 0");
        int main() {}
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_alignof_in_static_assert() {
    run_pass(
        r#"
        _Static_assert(_Alignof(int) > 0, "_Alignof(int) should be greater than 0");
        int main() {}
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_sizeof_struct_in_static_assert() {
    run_pass(
        r#"
        struct s { char c; int i; };
        _Static_assert(sizeof(struct s) == 8, "sizeof(struct s) should be 8");
        int main() {}
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_alignof_struct_in_static_assert() {
    run_pass(
        r#"
        struct s { char c; int i; };
        _Static_assert(_Alignof(struct s) == 4, "_Alignof(struct s) should be 4");
        int main() {}
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_sizeof_in_array_dimension() {
    run_pass(
        r#"
        int arr[sizeof(int)];
        _Static_assert(sizeof(arr) == sizeof(int) * sizeof(int), "size of array should be size of int");
        int main() {}
    "#,
        CompilePhase::Mir,
    );
}
