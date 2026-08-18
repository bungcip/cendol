use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_fail;

#[test]
fn test_indirection_requires_pointer() {
    let src = r#"
        int main() {
            int x = 42;
            return *x;
        }
    "#;

    let artifact = run_fail(src, CompilePhase::Mir);
    let diags = &artifact.de.diagnostics;

    assert_eq!(diags.len(), 1);

    let diag = &diags[0];

    assert_eq!(
        diag.message,
        "indirection requires pointer operand ('int' invalid)"
    );

    let line_col = artifact.sm.get_line_column(diag.span.start());
    assert_eq!(line_col, Some((4, 20))); // point to `*x`
}
