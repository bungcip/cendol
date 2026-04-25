use crate::tests::test_utils::run_pipeline;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_recursive_type_error() {
    let source = r#"
        struct Node {
            struct Node next;
        };
    "#;

    let (driver, result) = run_pipeline(source, CompilePhase::SemanticLowering);
    assert!(result.is_err());

    let diagnostics = driver.get_diagnostics();
    assert!(diagnostics.iter().any(|d| d.message.contains("recursive")));
}
