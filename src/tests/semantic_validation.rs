use crate::driver::artifact::CompilePhase;
use crate::tests::codegen_common::run_c_code_with_output;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn rejects_modulo_on_non_integer() {
    run_fail_with_message(
        r#"
        int main() {
            double x = 1.0;
            double y = 2.0;
            x % y;
            return 0;
        }
        "#,
        "Invalid operands for binary operation: have 'double' and 'double'",
    );
}

#[test]
fn accepts_modulo_on_integer() {
    run_pass(
        r#"
        int main() {
            int x = 1;
            int y = 2;
            x % y;
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn rejects_bitnot_on_non_integer() {
    run_fail_with_message(
        r#"
        int main() {
            double x = 1.0;
            ~x;
            return 0;
        }
    "#,
        "Invalid operand for unary operation: have 'double'",
    );
}

#[test]
fn rejects_conflicting_storage_classes() {
    run_fail_with_message(
        r#"
        extern static int x;
    "#,
        "conflicting storage class specifiers",
    );
}

#[test]
fn rejects_variable_as_typedef_in_cast() {
    run_fail_with_message(
        r#"
        int main() {
            int my_var = 10;
            (my_var) 1;
        }
    "#,
        "Unexpected token: expected ;, found IntegerConstant(1, None, 10)",
    );
}

#[test]
fn rejects_pointer_plus_pointer() {
    run_fail_with_message(
        "int main(){int *x; int *y; x+y;}",
        "Invalid operands for binary operation",
    );
}

#[test]
fn rejects_struct_in_if_condition() {
    run_fail_with_message(
        "struct A{int a; int b;}; int main(){struct A a; if(a){return 12;} return 3;}",
        "type mismatch: expected scalar type",
    );
}

#[test]
fn rejects_struct_in_for_condition() {
    run_fail_with_message(
        "struct A{int a; int b;}; int main(){struct A a; for(;a;){return 12;} return 3;}",
        "type mismatch: expected scalar type",
    );
}

#[test]
fn rejects_struct_in_while_condition() {
    run_fail_with_message(
        "struct A{int a; int b;}; int main(){struct A a; while(a){return 12;} return 3;}",
        "type mismatch: expected scalar type",
    );
}

#[test]
fn rejects_struct_in_do_while_condition() {
    run_fail_with_message(
        "struct A{int a; int b;}; int main(){struct A a; do{return 12;}while(a); return 3;}",
        "type mismatch: expected scalar type",
    );
}

#[test]
fn rejects_void_pointer_arithmetic() {
    run_fail_with_message(
        "int main(void){void *p = 0; p += 3;}",
        "Invalid operands for binary operation",
    );
}

#[test]
fn rejects_struct_compound_assignment() {
    run_fail_with_message(
        "struct A{int a; int b;}; int main(){struct A a; struct A b; b *= a; return 3;}",
        "Invalid operands for binary operation",
    );
}

#[test]
fn rejects_struct_logical_or() {
    run_fail_with_message(
        "struct A{int a; int b;}; int main(){struct A a; struct A b; b || a; return 3;}",
        "Invalid operands for binary operation",
    );
}

#[test]
fn rejects_thread_local_on_function() {
    let src = "
        _Thread_local void my_func(void);
    ";
    run_fail_with_message(src, "_Thread_local is not allowed here");
}

#[test]
fn test_struct_init_in_array_regression() {
    let source = r#"
    int printf(const char *fmt, ...);
    struct Inner {
      long i;
    };
    struct Outer {
      struct Inner b;
      int j;
    };
    int main(void) {
        struct Inner v = {3};
        struct Outer s[] = {v, 6, 7};

        printf("%ld %d %ld %d", s[0].b.i, s[0].j, s[1].b.i, s[1].j);
        return 0;
    }
    "#;

    let output = run_c_code_with_output(source);
    assert_eq!(output, "3 6 7 0");
}
