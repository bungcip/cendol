use super::test_utils::run_pass_with_std;
use crate::driver::artifact::CompilePhase;
use crate::lang_options::CStandard;

#[test]
fn test_typeof_unqual_type_direct() {
    run_pass_with_std(
        r#"
        int main() {
            typeof_unqual(const int) y = 5;
            y = 10;
            return 0;
        }
        "#,
        CompilePhase::Mir,
        CStandard::C23,
    );
}
