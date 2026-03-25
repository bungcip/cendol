use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

#[test]
fn test_complex_real_lvalue() {
    let source = r#"
        int main() {
            _Complex double c;
            __real__ c = 1.0;
            __imag__ c = 2.0;
            if (__real__ c != 1.0) return 1;
            if (__imag__ c != 2.0) return 2;
            return 0;
        }
    "#;
    test_utils::run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_complex_inc_dec() {
    let source = r#"
        int main() {
            _Complex double c = 1.0 + 2.0i;
            c++;
            if (__real__ c != 2.0) return 1;
            if (__imag__ c != 2.0) return 2;

            ++c;
            if (__real__ c != 3.0) return 3;

            c--;
            if (__real__ c != 2.0) return 4;

            --c;
            if (__real__ c != 1.0) return 5;

            return 0;
        }
    "#;
    test_utils::run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_real_type_lvalue_real_imag() {
    let source = r#"
        int main() {
            double d = 5.0;
            __real__ d = 10.0;
            if (d != 10.0) return 1;

            // __imag__ d is an rvalue zero, so this should still be a semantic error if assigned to
            // but we can read from it
            double i = __imag__ d;
            if (i != 0.0) return 2;

            return 0;
        }
    "#;
    test_utils::run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_complex_lvalue_in_expressions() {
    let source = r#"
        int main() {
            _Complex double c = 1.0 + 2.0i;
            double *p = &(__real__ c);
            *p = 5.0;
            if (__real__ c != 5.0) return 1;

            double *q = &(__imag__ c);
            *q = 10.0;
            if (__imag__ c != 10.0) return 2;

            return 0;
        }
    "#;
    test_utils::run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_imag_lvalue_rejected() {
    // __imag__ on a real type is an rvalue (0) and should be rejected for assignment
    let source = r#"
        int main() {
            double d = 5.0;
            __imag__ d = 1.0;
            return 0;
        }
    "#;
    test_utils::run_fail_with_message(source, "Expression is not assignable");
}
