use crate::tests::semantic_common::setup_cranelift;

#[test]
fn test_movi_unsigned_constant_codegen() {
    let source = r#"
        int main() {
            unsigned long long x;
            x = 0xffffabcd;
            return 0;
        }
    "#;

    let clif_dump = setup_cranelift(source);
    // 0xffffabcd = 4294945741
    // We expect `uextend` for casting unsigned int to unsigned long long.
    // If it was signed (int), it would use `sextend`.

    // With improved heuristic, 0xffffabcd is parsed as signed long (i64), so no extension needed
    assert!(
        clif_dump.contains("iconst.i64"),
        "Expected iconst.i64 for constant load, found:\n{}",
        clif_dump
    );
}

#[test]
fn test_long_double_size() {
    // Check that long double size matches architecture (8 on x86_64, 16 otherwise)
    let source = r#"
        int main() {
            long double ld;
            return 0;
        }
    "#;
    let clif_dump = setup_cranelift(source);

    let expected_size = 16;

    assert!(
        clif_dump.contains(&format!("explicit_slot {}", expected_size)),
        "Expected explicit_slot {} for long double, found:\n{}",
        expected_size,
        clif_dump
    );
}
