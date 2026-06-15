use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_usual_arithmetic_conversions_non_arithmetic() {
    let source = r#"
        int main() {
            struct A { int x; } a;
            1 ? a : 5;
            return 0;
        }
    "#;
    run_fail_with_message(source, "type mismatch: expected struct A, found int");
}
