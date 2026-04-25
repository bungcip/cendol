use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;
use crate::tests::test_utils::{run_fail_with_message, run_fail_with_message_and_std, run_pass, run_pass_with_std};

#[test]
fn test_static_assert_in_function() {
    run_pass(r#"void foo() { _Static_assert(1, "msg"); }"#, CompilePhase::Mir);
}

#[test]
fn test_static_assert_in_struct() {
    run_pass(r#"struct S { int x; _Static_assert(1, "msg"); };"#, CompilePhase::Mir);
}

#[test]
fn test_static_assert_c23_one_arg() {
    run_pass_with_std("_Static_assert(1 == 1);", CompilePhase::Mir, CStandard::C23);
}

#[test]
fn test_static_assert_keyword() {
    run_pass_with_std(r#"static_assert(1 == 1, "msg");"#, CompilePhase::Mir, CStandard::C23);
    run_pass_with_std("static_assert(1 == 1);", CompilePhase::Mir, CStandard::C23);
}

#[test]
fn test_static_assert_c23_fail_no_msg() {
    run_fail_with_message_and_std("_Static_assert(1 == 0);", "static assertion failed", CStandard::C23);
}

#[test]
fn test_static_assert_fail_with_msg() {
    run_fail_with_message(r#"_Static_assert(1 == 0, "failure message");"#, "failure message");
}

#[test]
fn test_static_assert_c11_no_message_fails() {
    // Current default is C11
    run_fail_with_message("_Static_assert(1);", "expected ',' followed by a string literal");
}

#[test]
fn test_static_assert_c11_keyword_fails() {
    // In C11, 'static_assert' is not a keyword, so it should be an undeclared identifier or similar
    run_fail_with_message(
        r#"int main() { static_assert(1, "ok"); }"#,
        "Undeclared identifier 'static_assert'",
    );
}

#[test]
fn test_static_assert_keyword_fail_no_msg() {
    run_fail_with_message_and_std("static_assert(0);", "static assertion failed", CStandard::C23);
}

#[test]
fn test_static_assert_in_union() {
    run_pass(r#"union U { int x; _Static_assert(1, "msg"); }; "#, CompilePhase::Mir);
}

#[test]
fn test_static_assert_at_top_level() {
    run_pass(r#"_Static_assert(1, "msg");"#, CompilePhase::Mir);
    run_fail_with_message(
        r#"_Static_assert(0, "This should fail");"#,
        "static assertion failed: This should fail",
    );
}

#[test]
fn test_static_assert_non_constant() {
    run_fail_with_message(
        r#"
        void foo() {
            int x = 1;
            _Static_assert(x, "error");
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
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_negative_numbers() {
    run_pass(
        r#"
        _Static_assert(-1 < 0, "Negative one should be less than zero");
        _Static_assert(-1 == -1, "Negative one should equal negative one");
        _Static_assert(0 - 1 == -1, "Subtraction should yield negative");
        _Static_assert(+1 == 1, "Unary plus should work");
        
        // Bitwise not: ~0 is -1 (in 2s complement)
        _Static_assert(~0 == -1, "Bitwise not of zero should be -1");
    "#,
        CompilePhase::Mir,
    );
}

#[test]
fn test_static_assert_type_mismatch() {
    run_fail_with_message(
        r#"
        _Static_assert(1.0, "should fail");
        "#,
        "type mismatch: expected integer type, found double",
    );
    run_fail_with_message(
        r#"
        _Static_assert((void*)0, "should fail");
        "#,
        "type mismatch: expected integer type, found void*",
    );
}

#[test]
fn test_static_assert_rejects_float_expression_in_cast() {
    // C11 6.6p6: "floating constants that are the immediate operands of casts"
    run_fail_with_message(
        r#"
        _Static_assert((int)(1.0 + 1.0), "should fail");
        "#,
        "expression in static assertion is not constant",
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
fn test_static_assert_cast() {
    run_pass(
        r#"
        _Static_assert((char)257 == 1, "should pass (assuming 8-bit char)");
        _Static_assert((unsigned char)-1 == 255, "should pass");
        _Static_assert((int)1.0, "should pass");
        _Static_assert((int)0.5 == 0, "should pass (truncation)");
        _Static_assert((int)1.9 == 1, "should pass (truncation)");
        _Static_assert((_Bool)2, "should pass (casted to 1)");
        _Static_assert((_Bool)0.5, "should pass (casted to 1)");
        _Static_assert(!((_Bool)0.0), "should pass");
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
        _Static_assert((_Bool)(2.5 + 1.5), "");
        _Static_assert(!(_Bool)(1.5 - 1.5), "");
    "#;
    run_pass(code, CompilePhase::Mir);
}
