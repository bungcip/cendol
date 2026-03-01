use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pipeline;

#[test]
fn test_complex_type_conversions() {
    let source = r#"
        int main() {
            _Complex double cd;
            double d = 1.0;
            cd + d;
            return 0;
        }
    "#;
    let (_, result) = run_pipeline(source, CompilePhase::Mir);
    assert!(result.is_ok());
}
