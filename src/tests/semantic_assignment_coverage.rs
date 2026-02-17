use super::semantic_common::setup_mir;

#[test]
fn test_compound_assignments() {
    let source = r#"
        int main() {
            int a = 10;
            int b = 3;

            a += b;
            a -= b;
            a *= b;
            a /= b;
            a %= b;

            a <<= b;
            a >>= b;

            a &= b;
            a ^= b;
            a |= b;

            return a;
        }
    "#;

    let mir_dump = setup_mir(source);
    insta::assert_snapshot!(mir_dump);
}
