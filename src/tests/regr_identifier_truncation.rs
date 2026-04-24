
use crate::tests::semantic_common::setup_analysis;

#[test]
fn test_identifier_before_question() {
    // This test reproduces the truncation bug where 'l2?' is lexed as 'l' and '2' and '?'
    // or rather 'l' (truncated) and then '2' is left over.
    // In the SDS case, it was 'l2?' in a ternary expression.
    let source = r#"
    int main() {
        int l2 = 42;
        return l2? 1 : 0;
    }
    "#;
    setup_analysis(source);
}

#[test]
fn test_identifier_before_backslash() {
    let source = r#"
    int main() {
        int l2 = 42;
        return l2\
    ? 1 : 0;
    }
    "#;
    setup_analysis(source);
}
