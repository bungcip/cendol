use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils::run_pass;

#[test]
fn test_atomic_load_store_mir() {
    let source = r#"
        _Atomic int i;
        int main() {
            i = 42;
            int j = i;
            return j;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_atomic_compound_assignment_mir() {
    let source = r#"
        _Atomic int i;
        int main() {
            i += 1;
            i *= 2;
            return i;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_atomic_inc_dec_mir() {
    let source = r#"
        _Atomic int i;
        int main() {
            i++;
            ++i;
            i--;
            --i;
            return i;
        }
    "#;
    run_pass(source, CompilePhase::Mir);
}

#[test]
fn test_atomic_codegen() {
    let source = r#"
        _Atomic int i;
        int main() {
            i = 42;
            i += 1;
            i++;
            return i;
        }
    "#;
    run_pass(source, CompilePhase::EmitObject);
}
