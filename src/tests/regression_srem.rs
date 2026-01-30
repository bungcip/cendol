//! Regression tests for issues found during development.

use crate::tests::semantic_common::run_pass;
use crate::driver::artifact::CompilePhase;

#[test]
fn test_srem_segmentation_fault() {
    let source = r#"
int main() {
    int i = 0;
    int c = 0;
    while (i < 5000) {
        if (i % 2 == 0) {
            c++;
        }
        i++;
    }
    return 0;
}
"#;
    run_pass(source, CompilePhase::EmitObject);
}

#[test]
fn test_srem_negative_numbers() {
    let source = r#"
int main() {
    int x = -10;
    int y = 3;
    int z = x % y;
    if (z == -1) {
        return 0;
    }
    return 1;
}
"#;
    run_pass(source, CompilePhase::EmitObject);
}
