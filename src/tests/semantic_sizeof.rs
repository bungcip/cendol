use crate::tests::test_utils;

#[test]
fn test_sizeof_layout_crash() {
    // This test reproduces a crash where sizeof(T) caused a panic because the layout of T was not computed.
    // The fix ensures that layout is computed for the type operand of sizeof.
    let src = r#"
    int main() {
        int x, *p;

        if (sizeof(0) < 2) return 1;
        if (sizeof 0 < 2) return 1;
        if (sizeof(char) < 1) return 1;
        if (sizeof(int) - 2 < 0) return 1;
        if (sizeof(&x) != sizeof p) return 1;
        return 0;
    }
    "#;

    // Run the pipeline up to MIR generation, which triggers the layout requirement.
    let _ = test_utils::run_pipeline_to_mir(src);
}
