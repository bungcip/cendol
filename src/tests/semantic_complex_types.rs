use crate::tests::test_utils::run_pipeline_to_mir;

#[test]
fn test_complex_declarations() {
    let source = r#"
        int main() {
            float _Complex fc;
            double _Complex dc;
            long double _Complex ldc;
            _Complex c; // Defaults to double _Complex
            return 0;
        }
    "#;
    let outputs = run_pipeline_to_mir(source);
    let artifact = outputs.units.values().next().unwrap();
    let mir = artifact.mir_program.as_ref().unwrap();

    // Verify that we have some record types for complex numbers
    let mut found_complex = false;
    for ty in mir.types.values() {
        if let crate::mir::MirType::Record { name, .. } = ty
            && name.as_str().contains("_Complex_")
        {
            found_complex = true;
            break;
        }
    }
    assert!(found_complex, "Should have found complex record types in MIR");
}

#[test]
fn test_complex_generic() {
    let source = r#"
        int main() {
            float _Complex fc;
            double _Complex dc;
            int is_float_complex = _Generic(fc, float _Complex: 1, default: 0);
            int is_double_complex = _Generic(dc, double _Complex: 1, default: 0);
            return is_float_complex + is_double_complex;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
    // If it compiles and lowers to MIR, semantic analysis (including _Generic) passed.
}

#[test]
fn test_complex_order() {
    let source = r#"
        int main() {
            float _Complex fc1;
            _Complex float fc2;
            int same = _Generic(fc1, float _Complex: _Generic(fc2, float _Complex: 1, default: 0), default: 0);
            return same;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_atomic() {
    let source = r#"
        int main() {
            _Atomic float _Complex afc;
            _Atomic(_Complex double) adc;
            return 0;
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

#[test]
fn test_complex_long_double() {
    let source = r#"
        int main() {
            long double _Complex ldc;
            return _Generic(ldc, long double _Complex: 1, default: 0);
        }
    "#;
    let _mir = run_pipeline_to_mir(source);
}

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
