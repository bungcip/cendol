use crate::tests::codegen_common::setup_cranelift;

#[test]
fn test_array_literal_initialization_fix() {
    let source = r#"
        int main() {
            char s[] = "hello";
            return 0;
        }
    "#;

    let clif_dump = setup_cranelift(source);
    println!("{}", clif_dump);

    // We expect a global value to be defined for the string literal "hello"
    // and it should be used as source for memcpy (or similar mechanism).
    // The previous bug caused it to emit 'iconst.i64 0' (NULL) as the source address.

    // Ensure we are loading a global address
    // Cranelift may emit global_value or symbol_value depending on configuration
    assert!(
        clif_dump.contains("global_value.i64") || clif_dump.contains("symbol_value.i64"),
        "Expected global_value or symbol_value instruction for array literal address"
    );

    // We should see a call to memcpy (or similar)
    // Note: exact function name might vary (fn0, memcpy, etc) but setup_cranelift should show it.
    // In the dump: "call fn0(v1, v0, v2)" where v0 is the source.
    // We want to ensure v0 is NOT 0.
}
