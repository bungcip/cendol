use crate::{
    driver::artifact::CompilePhase,
    tests::{codegen_common::run_c_code_exit_status, test_utils::run_pass},
};

#[test]
fn test_float_to_bool_cast_nan() {
    let source = r#"
        int main() {
            _Bool b = (_Bool)(0.0/0.0);
            return b;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_ternary_nan() {
    let source = r#"
        int main() {
            return (0.0/0.0) ? 1 : 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_if_nan() {
    let source = r#"
        int main() {
            if (0.0/0.0) {
                return 1;
            } else {
                return 0;
            }
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_while_nan() {
    let source = r#"
        int main() {
            int i = 0;
            while (0.0/0.0) {
                i++;
                if (i >= 1) break;
            }
            return i;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 1);
}

#[test]
fn test_float_condition_zero() {
    let source = r#"
        int main() {
            return 0.0 ? 1 : 0;
        }
    "#;
    assert_eq!(run_c_code_exit_status(source), 0);
}

#[test]
fn float_to_int_out_of_bounds() {
    run_pass(
        "
        int printf(const char *format, ...);
        int main() {
            // These conversions cause undefined behavior in C11 6.3.1.4p1
            // because the floating-point value cannot be represented in the integer type.
            // However, the compiler should not emit trapping instructions (like ud2 on x64)
            // that crash the program, but instead provide a fallback behavior (e.g. saturation or indefinite value),
            // which is expected by some real-world programs like Lua.

            double d1 = 1e20;
            long long l1 = (long long)d1;

            double d2 = -1e20;
            long long l2 = (long long)d2;

            double d3 = 1.0 / 0.0; // Infinity
            long long l3 = (long long)d3;

            double d4 = 0.0 / 0.0; // NaN
            long long l4 = (long long)d4;

            printf(\"%lld %lld %lld %lld\\n\", l1, l2, l3, l4);
            return 0;
        }
        ",
        CompilePhase::EmitObject,
    );
}
