use crate::tests::codegen_common::run_c_code_with_output;

#[test]
fn test_float_to_bool_cast_nan() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            _Bool b = (_Bool)(0.0/0.0);
            printf("%d\n", b);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "1");
}

#[test]
fn test_float_condition_ternary_nan() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            printf("%d\n", (0.0/0.0) ? 1 : 0);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "1");
}

#[test]
fn test_float_condition_if_nan() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            if (0.0/0.0) {
                printf("1\n");
            } else {
                printf("0\n");
            }
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "1");
}

#[test]
fn test_float_condition_while_nan() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            int i = 0;
            while (0.0/0.0) {
                printf("1\n");
                i++;
                if (i >= 1) break;
            }
            if (i == 0) printf("0\n");
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "1");
}

#[test]
fn test_float_condition_zero() {
    let source = r#"
        int printf(const char*, ...);
        int main() {
            printf("%d\n", 0.0 ? 1 : 0);
            return 0;
        }
    "#;
    let output = run_c_code_with_output(source);
    assert_eq!(output.trim(), "0");
}
