use cendol::compiler::CompilerError;
use cendol::test_utils::compile_and_run;

type TestResult = Result<(), CompilerError>;

#[test]
fn test_switch_basic() -> TestResult {
    let c_code = r#"
        int main() {
            int x = 2;
            int y = 0;
            switch (x) {
                case 1: y = 1; break;
                case 2: y = 2; break;
                case 3: y = 3; break;
                default: y = 4;
            }
            return y;
        }
    "#;
    assert_eq!(compile_and_run(c_code, "test_switch_basic")?, 2);
    Ok(())
}

#[test]
fn test_switch_fallthrough() -> TestResult {
    let c_code = r#"
        int main() {
            int x = 1;
            int y = 0;
            switch (x) {
                case 1: y = 1;
                case 2: y += 2;
                case 3: y += 3;
                default: y += 4;
            }
            return y;
        }
    "#;
    assert_eq!(compile_and_run(c_code, "test_switch_fallthrough")?, 10);
    Ok(())
}

#[test]
fn test_switch_default() -> TestResult {
    let c_code = r#"
        int main() {
            int x = 5;
            int y = 0;
            switch (x) {
                case 1: y = 1; break;
                case 2: y = 2; break;
                default: y = 4;
            }
            return y;
        }
    "#;
    assert_eq!(compile_and_run(c_code, "test_switch_default")?, 4);
    Ok(())
}

#[test]
fn test_switch_no_match() -> TestResult {
    let c_code = r#"
        int main() {
            int x = 5;
            int y = 0;
            switch (x) {
                case 1: y = 1; break;
                case 2: y = 2; break;
            }
            return y;
        }
    "#;
    assert_eq!(compile_and_run(c_code, "test_switch_no_match")?, 0);
    Ok(())
}
