use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

#[test]
fn test_usual_arithmetic_conversions() {
    let source_complex = r#"
        int main() {
            _Complex double a = 1.0;
            long double b = 2.0;
            return 0;
        }
    "#;
    let (_, result_complex) = run_pipeline(source_complex, CompilePhase::Mir);
    assert!(result_complex.is_ok());

    let source_complex_addition = r#"
        int main() {
            _Complex double a = 1.0;
            double b = 2.0;
            a + b;
            return 0;
        }
    "#;
    let (_, result_complex_addition) = run_pipeline(source_complex_addition, CompilePhase::Mir);
    assert!(result_complex_addition.is_ok());

    let source_long_double = r#"
        int main() {
            long double a = 1.0;
            double b = 2.0;
            a + b;
            return 0;
        }
    "#;
    let (_, result_long_double) = run_pipeline(source_long_double, CompilePhase::Mir);
    assert!(result_long_double.is_ok());

    let source_long_long_unsigned_long = r#"
        int main() {
            long long a = 1;
            unsigned long b = 2;
            a + b;
            return 0;
        }
    "#;
    let (_, result_long_long_unsigned_long) = run_pipeline(source_long_long_unsigned_long, CompilePhase::Mir);
    assert!(result_long_long_unsigned_long.is_ok());
}
