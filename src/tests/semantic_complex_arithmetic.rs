use crate::tests::test_utils::run_pipeline_to_mir;

#[test]
fn test_complex_addition() {
    let source = r#"
        int main() {
            float _Complex a, b, c;
            c = a + b;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
#[should_panic]
fn test_complex_relational_error() {
    let source = r#"
        int main() {
            float _Complex a, b;
            int res = (a < b);
            return 0;
        }
    "#;
    run_pipeline_to_mir(source);
}

#[test]
fn test_complex_subtraction() {
    let source = r#"
        int main() {
            double _Complex a, b, c;
            c = a - b;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_multiplication() {
    let source = r#"
        int main() {
            float _Complex a, b, c;
            c = a * b;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_division() {
    let source = r#"
        int main() {
            double _Complex a, b, c;
            c = a / b;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_comparison() {
    let source = r#"
        int main() {
            float _Complex a, b;
            int eq = (a == b);
            int ne = (a != b);
            return eq + ne;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_conjugate() {
    let source = r#"
        int main() {
            float _Complex a, b;
            b = ~a;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_real_interaction() {
    let source = r#"
        int main() {
            float _Complex a;
            float b;
            a = a + b;
            a = b + a;
            a = a * b;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}
