use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_diagnostic, run_fail_with_message, run_pass};

#[test]
fn test_static_assert_pass() {
    run_pass(
        r#"
        int main() {
            _Static_assert(1, "This should pass");
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn rejects_modulo_on_non_integer() {
    run_fail_with_diagnostic(
        r#"
        int main() {
            double x = 1.0;
            double y = 2.0;
            x % y;
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "Invalid operands for binary operation: have 'double' and 'double'",
        5,
        13,
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
    run_fail_with_diagnostic(
        r#"
        int main() {
            double x = 1.0;
            ~x;
            return 0;
        }
    "#,
        CompilePhase::Mir,
        "Invalid operand for unary operation: have 'double'",
        4,
        13,
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
        "Unexpected token: expected Semicolon, found IntegerConstant(1, None, 10)",
    );
}

#[test]
fn test_static_assert_fail() {
    run_fail_with_message(
        r#"
        int main() {
            _Static_assert(0, "This should fail");
            return 0;
        }
    "#,
        "static assertion failed: \"This should fail\"",
    );
}

#[test]
fn test_static_assert_file_scope_fail() {
    run_fail_with_message(
        r#"
        _Static_assert(0, "This should fail");
        int main() {
            return 0;
        }
    "#,
        "static assertion failed: \"This should fail\"",
    );
}

#[test]
fn test_static_assert_non_constant() {
    run_fail_with_message(
        r#"
        int main() {
            int x = 1;
            _Static_assert(x, "error");
            return 0;
        }
    "#,
        "expression in static assertion is not constant",
    );
}

#[test]
fn test_static_assert_comparison() {
    run_pass(
        r#"
        _Static_assert(1 < 2, "This should pass");
        _Static_assert(2 > 1, "This should pass");
        _Static_assert(1 == 1, "This should pass");
        _Static_assert(1 != 2, "This should pass");
        _Static_assert(1 <= 1, "This should pass");
        _Static_assert(1 >= 1, "This should pass");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_logical() {
    run_pass(
        r#"
        _Static_assert(1 && 1, "This should pass");
        _Static_assert(1 || 0, "This should pass");
        _Static_assert(0 || 1, "This should pass");
        _Static_assert(!(0), "This should pass");
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_const_eval_negative_numbers() {
    run_pass(
        r#"
        _Static_assert(-1 < 0, "Negative one should be less than zero");
        _Static_assert(-1 == -1, "Negative one should equal negative one");
        _Static_assert(0 - 1 == -1, "Subtraction should yield negative");
        _Static_assert(+1 == 1, "Unary plus should work");
        
        // Bitwise not: ~0 is -1 (in 2s complement)
        _Static_assert(~0 == -1, "Bitwise not of zero should be -1");
        
        int main() {
            return 0;
        }
    "#,
        CompilePhase::Mir,
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
