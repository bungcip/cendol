use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::{run_fail_with_message, run_pass};

#[test]
fn test_static_assert_in_struct() {
    run_pass(
        "struct S { int x; _Static_assert(1, \"msg\"); }; int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_in_union() {
    run_pass(
        "union U { int x; _Static_assert(1, \"msg\"); }; int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_top_level() {
    run_pass(
        "_Static_assert(1, \"msg\"); int main() { return 0; }",
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_in_function() {
    run_pass(
        "int main() { _Static_assert(1, \"msg\"); return 0; }",
        CompilePhase::Mir,
    );
}

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
fn static_assert_accepts_float_cast_to_int() {
    run_pass(
        r#"
        _Static_assert((int)1.0, "should pass");
        _Static_assert((int)0.5 == 0, "should pass (truncation)");
        _Static_assert((int)1.9 == 1, "should pass (truncation)");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn static_assert_rejects_uncast_float() {
    run_fail_with_message(
        r#"
        _Static_assert(1.0, "should fail");
        "#,
        "type mismatch: expected integer type, found double",
    );
}

#[test]
fn static_assert_rejects_float_expression_in_cast() {
    // C11 6.6p6: "floating constants that are the immediate operands of casts"
    run_fail_with_message(
        r#"
        _Static_assert((int)(1.0 + 1.0), "should fail");
        "#,
        "expression in static assertion is not constant",
    );
}

#[test]
fn constant_cast_performs_truncation() {
    run_pass(
        r#"
        _Static_assert((char)257 == 1, "should pass (assuming 8-bit char)");
        _Static_assert((unsigned char)-1 == 255, "should pass");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn static_assert_rejects_out_of_range_float() {
    run_fail_with_message(
        r#"
        _Static_assert((int)1e20, "should fail");
        "#,
        "expression in static assertion is not constant",
    );
}

#[test]
fn static_assert_rejects_pointer_type() {
    run_fail_with_message(
        r#"
        _Static_assert((void*)0, "should fail");
        "#,
        "type mismatch: expected integer type, found void*",
    );
}

#[test]
fn static_assert_bool_cast() {
    run_pass(
        r#"
        _Static_assert((_Bool)2, "should pass");
        _Static_assert((_Bool)0.5, "should pass");
        _Static_assert(!((_Bool)0.0), "should pass");
        int main() { return 0; }
        "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_float_logical_and_comparison() {
    let code = r#"
        _Static_assert(2.0 || (2.0 == 2.0), "");
        _Static_assert(0.0 || 1.0, "");
        _Static_assert(1.5 != 2.5, "");
        _Static_assert(3.14 > 3.0, "");
    "#;
    run_pass(code, CompilePhase::Mir);
}
