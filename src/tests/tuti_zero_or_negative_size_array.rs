use crate::lang_options::CStandard;
use crate::tests::test_utils::run_fail_with_message_and_std;

#[test]
fn test_zero_size_array_c23() {
    let src = r#"
int main() {
    int arr[] = {};
    return 0;
}
"#;
    run_fail_with_message_and_std(src, "zero or negative size array 'arr'", CStandard::C23);
}
