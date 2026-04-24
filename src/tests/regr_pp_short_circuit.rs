use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_pp_conditional_short_circuit() {
    let source = r#"
#if 1 ? 1 : (1/0)
#endif

#if 0 ? (1/0) : 1
#endif

#if 3 != (-1 ? 3 : (0/0))
#error "Should not reach here"
#endif

int main() { return 0; }
"#;
    run_pass(source, CompilePhase::Preprocess);
}

#[test]
fn test_pp_logical_and_short_circuit() {
    let source = r#"
#if 0 && (1/0)
#endif

int main() { return 0; }
"#;
    run_pass(source, CompilePhase::Preprocess);
}

#[test]
fn test_pp_logical_or_short_circuit() {
    let source = r#"
#if 1 || (1/0)
#endif

int main() { return 0; }
"#;
    run_pass(source, CompilePhase::Preprocess);
}

#[test]
fn test_pp_conditional_unsigned_promotion() {
    let source = r#"
#if (1 ? 1 : 1u) < -1
#else
#error "Should be truthy if unsigned"
#endif

int main() { return 0; }
"#;
    run_pass(source, CompilePhase::Preprocess);
}
