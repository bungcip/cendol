use crate::tests::semantic_common::setup_mir;

#[test]
fn test_complex_ops_float() {
    let src = r#"
        void test(float _Complex a, float _Complex b) {
            float _Complex add = a + b;
            float _Complex sub = a - b;
            float _Complex mul = a * b;
            float _Complex div = a / b;
            float _Complex neg = -a;
            float _Complex conj = ~a;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_complex_ops_double() {
    let src = r#"
        void test(double _Complex a, double _Complex b) {
            double _Complex add = a + b;
            double _Complex sub = a - b;
            double _Complex mul = a * b;
            double _Complex div = a / b;
            double _Complex neg = -a;
            double _Complex conj = ~a;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir);
}

#[test]
fn test_complex_comparison() {
    let src = r#"
        int test(float _Complex a, float _Complex b) {
            int eq = (a == b);
            int ne = (a != b);
            return eq + ne;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir);
}
