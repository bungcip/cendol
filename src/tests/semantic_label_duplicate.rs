use crate::tests::test_utils::*;

#[test]
fn test_duplicate_label() {
    let source = "
    int main(void) {
        label: ;
        label: ;
        return 0;
    }
    ";
    run_fail_with_message(source, "redefinition");
}
