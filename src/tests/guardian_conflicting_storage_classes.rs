use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;
use crate::tests::test_utils::run_fail_with_diagnostic;
use crate::tests::test_utils::run_fail_with_message_and_std;

#[test]
fn test_multiple_storage_classes_rejected() {
    run_fail_with_diagnostic(
        "static extern int x;",
        CompilePhase::SemanticLowering,
        "conflicting storage class specifiers",
        1,
        1,
    );
}

#[test]
fn test_typedef_with_storage_class_rejected() {
    run_fail_with_diagnostic(
        "typedef static int y;",
        CompilePhase::SemanticLowering,
        "conflicting storage class specifiers",
        1,
        1,
    );
}

#[test]
fn test_thread_local_with_register_rejected() {
    run_fail_with_diagnostic(
        "_Thread_local register int z;",
        CompilePhase::SemanticLowering,
        "conflicting storage class specifiers",
        1,
        1,
    );
}

#[test]
fn test_constexpr_with_extern_rejected() {
    run_fail_with_message_and_std(
        "constexpr extern int w;",
        "conflicting storage class specifiers",
        CStandard::C23,
    );
}

#[test]
fn test_duplicate_storage_class_rejected() {
    run_fail_with_diagnostic(
        r#"
        int main() {
            auto auto int x;
        }
        "#,
        CompilePhase::SemanticLowering,
        "conflicting storage class specifiers",
        3,
        13,
    );
}
