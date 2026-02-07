use crate::tests::{semantic_common::setup_mir, test_utils::run_pipeline_to_mir};

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
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = f32
    type %t2 = struct _Complex_float { real: %t1, imag: %t1 }

    fn test(%param0: %t2, %param1: %t2) -> void
    {
      locals {
        %add: %t2
        %4: f32
        %5: f32
        %6: %t2
        %7: %t2
        %sub: %t2
        %9: f32
        %10: f32
        %11: %t2
        %12: %t2
        %mul: %t2
        %14: f32
        %15: f32
        %16: f32
        %17: f32
        %18: f32
        %19: f32
        %20: %t2
        %21: %t2
        %div: %t2
        %23: f32
        %24: f32
        %25: f32
        %26: f32
        %27: f32
        %28: f32
        %29: f32
        %30: f32
        %31: f32
        %32: f32
        %33: f32
        %34: %t2
        %35: %t2
        %neg: %t2
        %37: f32
        %38: f32
        %39: %t2
        %conj: %t2
        %41: f32
        %42: %t2
      }

      bb1:
        %4 = %param0.field_0 fadd %param1.field_0
        %5 = %param0.field_1 fadd %param1.field_1
        %6 = struct{0: %4, 1: %5}
        %7 = %6
        %add = %7
        %9 = %param0.field_0 fsub %param1.field_0
        %10 = %param0.field_1 fsub %param1.field_1
        %11 = struct{0: %9, 1: %10}
        %12 = %11
        %sub = %12
        %14 = %param0.field_0 fmul %param1.field_0
        %15 = %param0.field_1 fmul %param1.field_1
        %16 = %14 fsub %15
        %17 = %param0.field_0 fmul %param1.field_1
        %18 = %param0.field_1 fmul %param1.field_0
        %19 = %17 fadd %18
        %20 = struct{0: %16, 1: %19}
        %21 = %20
        %mul = %21
        %23 = %param1.field_0 fmul %param1.field_0
        %24 = %param1.field_1 fmul %param1.field_1
        %25 = %23 fadd %24
        %26 = %param0.field_0 fmul %param1.field_0
        %27 = %param0.field_1 fmul %param1.field_1
        %28 = %26 fadd %27
        %29 = %28 fdiv %25
        %30 = %param0.field_1 fmul %param1.field_0
        %31 = %param0.field_0 fmul %param1.field_1
        %32 = %30 fsub %31
        %33 = %32 fdiv %25
        %34 = struct{0: %29, 1: %33}
        %35 = %34
        %div = %35
        %37 = fneg %param0.field_0
        %38 = fneg %param0.field_1
        %39 = struct{0: %37, 1: %38}
        %neg = %39
        %41 = fneg %param0.field_1
        %42 = struct{0: %param0.field_0, 1: %41}
        %conj = %42
        return
    }
    ");
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
    insta::assert_snapshot!(mir, @r"
    type %t0 = void
    type %t1 = f64
    type %t2 = struct _Complex_double { real: %t1, imag: %t1 }

    fn test(%param0: %t2, %param1: %t2) -> void
    {
      locals {
        %add: %t2
        %4: f64
        %5: f64
        %6: %t2
        %7: %t2
        %sub: %t2
        %9: f64
        %10: f64
        %11: %t2
        %12: %t2
        %mul: %t2
        %14: f64
        %15: f64
        %16: f64
        %17: f64
        %18: f64
        %19: f64
        %20: %t2
        %21: %t2
        %div: %t2
        %23: f64
        %24: f64
        %25: f64
        %26: f64
        %27: f64
        %28: f64
        %29: f64
        %30: f64
        %31: f64
        %32: f64
        %33: f64
        %34: %t2
        %35: %t2
        %neg: %t2
        %37: f64
        %38: f64
        %39: %t2
        %conj: %t2
        %41: f64
        %42: %t2
      }

      bb1:
        %4 = %param0.field_0 fadd %param1.field_0
        %5 = %param0.field_1 fadd %param1.field_1
        %6 = struct{0: %4, 1: %5}
        %7 = %6
        %add = %7
        %9 = %param0.field_0 fsub %param1.field_0
        %10 = %param0.field_1 fsub %param1.field_1
        %11 = struct{0: %9, 1: %10}
        %12 = %11
        %sub = %12
        %14 = %param0.field_0 fmul %param1.field_0
        %15 = %param0.field_1 fmul %param1.field_1
        %16 = %14 fsub %15
        %17 = %param0.field_0 fmul %param1.field_1
        %18 = %param0.field_1 fmul %param1.field_0
        %19 = %17 fadd %18
        %20 = struct{0: %16, 1: %19}
        %21 = %20
        %mul = %21
        %23 = %param1.field_0 fmul %param1.field_0
        %24 = %param1.field_1 fmul %param1.field_1
        %25 = %23 fadd %24
        %26 = %param0.field_0 fmul %param1.field_0
        %27 = %param0.field_1 fmul %param1.field_1
        %28 = %26 fadd %27
        %29 = %28 fdiv %25
        %30 = %param0.field_1 fmul %param1.field_0
        %31 = %param0.field_0 fmul %param1.field_1
        %32 = %30 fsub %31
        %33 = %32 fdiv %25
        %34 = struct{0: %29, 1: %33}
        %35 = %34
        %div = %35
        %37 = fneg %param0.field_0
        %38 = fneg %param0.field_1
        %39 = struct{0: %37, 1: %38}
        %neg = %39
        %41 = fneg %param0.field_1
        %42 = struct{0: %param0.field_0, 1: %41}
        %conj = %42
        return
    }
    ");
}

#[test]
fn test_complex_comparison_v2() {
    let src = r#"
        int test(float _Complex a, float _Complex b) {
            int eq = (a == b);
            int ne = (a != b);
            return eq + ne;
        }
    "#;
    let mir = setup_mir(src);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = f32
    type %t2 = struct _Complex_float { real: %t1, imag: %t1 }
    type %t3 = bool

    fn test(%param0: %t2, %param1: %t2) -> i32
    {
      locals {
        %eq: i32
        %4: bool
        %5: bool
        %6: i32
        %7: i32
        %ne: i32
        %9: bool
        %10: bool
        %11: i32
        %12: i32
        %13: i32
      }

      bb1:
        %4 = %param0.field_0 feq %param1.field_0
        %5 = %param0.field_1 feq %param1.field_1
        %6 = %4 & %5
        %7 = %6
        %eq = %7
        %9 = %param0.field_0 fne %param1.field_0
        %10 = %param0.field_1 fne %param1.field_1
        %11 = %9 | %10
        %12 = %11
        %ne = %12
        %13 = %eq + %ne
        return %13
    }
    ");
}
