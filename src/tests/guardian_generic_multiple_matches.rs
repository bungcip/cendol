use crate::tests::test_utils::run_fail_with_message;

#[test]
fn test_generic_matches_multiple_associations() {
    // int(*)[] is compatible with both int(*)[10] and int(*)[20].
    // But int(*)[10] and int(*)[20] are NOT compatible with each other.
    run_fail_with_message(
        r#"
        int main() {
            int (*p)[];
            return _Generic(p, int(*)[10]: 1, int(*)[20]: 2);
        }
        "#,
        "matches multiple associations",
    );
}
