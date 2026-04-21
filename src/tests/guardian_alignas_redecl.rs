use crate::tests::test_utils::run_fail_with_message;

#[test]
fn rejects_alignas_on_second_declaration() {
    // C11 6.7.5p5: If an identifier is declared with an alignment specifier in one
    // declaration and without one in another declaration of the same identifier,
    // then the first declaration of the identifier shall specify the alignment specifier.
    run_fail_with_message(
        r#"
        int x;
        _Alignas(8) int x;
        "#,
        "alignment specifier must be specified in the first declaration",
    );
}

#[test]
fn rejects_conflicting_alignas() {
    // C11 6.7.5p5: ... if there are multiple declarations with alignment specifiers,
    // they shall all specify the same alignment.
    run_fail_with_message(
        r#"
        _Alignas(8) int x;
        _Alignas(16) int x;
        "#,
        "conflicting alignment specifiers",
    );
}
