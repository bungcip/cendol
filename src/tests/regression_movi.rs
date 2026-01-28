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

    assert!(
        clif_dump.contains("uextend.i64"),
        "Expected uextend.i64 for unsigned constant extension, found:\n{}",
        clif_dump
    );
}

#[test]
fn test_long_double_size() {
    // Check that long double is treated as 16 bytes (size of F128)
    let source = r#"
        int main() {
            long double ld;
            return 0;
        }
    "#;
    let clif_dump = setup_cranelift(source);
    // We expect a stack slot of size 16
    assert!(
        clif_dump.contains("explicit_slot 16"),
        "Expected explicit_slot 16 for long double, found:\n{}",
        clif_dump
    );
}
