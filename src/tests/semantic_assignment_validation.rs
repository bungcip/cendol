use super::semantic_common::{setup_diagnostics_output, setup_mir};

#[test]
fn test_assign_struct_to_int() {
    let source = r#"
        struct A { int x; };
        int main() {
            struct A a;
            int i;
            i = a;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found struct A
    Span: SourceSpan(source_id=SourceId(2), start=106, end=111)
    ");
}

#[test]
fn test_assign_int_to_struct() {
    let source = r#"
        struct A { int x; };
        int main() {
            struct A a;
            a = 10;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found int
    Span: SourceSpan(source_id=SourceId(2), start=87, end=93)
    ");
}

#[test]
fn test_assign_incompatible_struct() {
    let source = r#"
        struct A { int x; };
        struct B { int x; };

        int main() {
            struct A a;
            struct B b;
            a = b; 
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found struct B
    Span: SourceSpan(source_id=SourceId(2), start=141, end=146)
    ");
}

#[test]
fn test_assign_incompatible_pointers() {
    let source = r#"
        int main() {
            int a = 10;
            int *p = &a;
            float *f;
            f = p;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected <pointer>, found <pointer>
    Span: SourceSpan(source_id=SourceId(2), start=105, end=110)
    ");
}

#[test]
fn test_assign_int_to_pointer() {
    let source = r#"
        int main() {
            int *p;
            p = 5; // Invalid (except 0)
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected <pointer>, found int
    Span: SourceSpan(source_id=SourceId(2), start=54, end=59)
    ");
}

#[test]
fn test_assign_pointer_to_int() {
    let source = r#"
        int main() {
            int i;
            int *p;
            i = p; // Invalid without cast
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found <pointer>
    Span: SourceSpan(source_id=SourceId(2), start=73, end=78)
    ");
}

#[test]
fn test_assign_struct_mismatch() {
    let source = r#"
        struct A { int x; };
        struct B { int x; };
        int main() {
            struct A a;
            struct B b;
            a = b;
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected struct A, found struct B
    Span: SourceSpan(source_id=SourceId(2), start=140, end=145)
    ");
}

#[test]
fn test_assign_valid_void_ptr() {
    let source = r#"
        int main() {
            int a;
            int *p = &a;
            void *v;
            v = p; // int* -> void* OK
            p = v; // void* -> int* OK
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = ptr<%t0>
    type %t2 = void
    type %t3 = ptr<%t2>

    fn main() -> i32
    {
      locals {
        %a: i32
        %p: ptr<i32>
        %v: ptr<void>
      }

      bb1:
        %p = addr_of(%a)
        %v = cast<ptr<void>>(%p)
        %p = cast<ptr<i32>>(%v)
        return const 0
    }
    ");
}

#[test]
fn test_assign_valid_null_ptr() {
    let source = r#"
        int main() {
            int *p;
            p = 0; // OK
            p = (void*)0; // OK
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = ptr<%t0>
    type %t2 = void
    type %t3 = ptr<%t2>

    fn main() -> i32
    {
      locals {
        %p: ptr<i32>
      }

      bb1:
        %p = cast<ptr<i32>>(const 0)
        %p = cast<ptr<i32>>(const 0)
        return const 0
    }
    ");
}

#[test]
fn test_assign_pointer_to_bool() {
    let source = r#"
        int main() {
            int *p;
            _Bool b;
            b = p; // OK
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = ptr<%t0>
    type %t2 = bool

    fn main() -> i32
    {
      locals {
        %p: ptr<i32>
        %b: bool
      }

      bb1:
        %b = %p
        return const 0
    }
    ");
}

#[test]
fn test_assign_valid_arithmetic() {
    let source = r#"
        int main() {
            int i;
            float f;
            i = 3.14; // OK (conversion)
            f = 10;   // OK (conversion)
            return 0;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32
    type %t1 = f32
    type %t2 = f64

    fn main() -> i32
    {
      locals {
        %i: i32
        %f: f32
      }

      bb1:
        %i = cast<i32>(const 3.14)
        %f = cast<f32>(const 10)
        return const 0
    }
    ");
}

#[test]
fn test_void_init_variable() {
    let source = r#"
        void foo() {}

        int main() {
            int x = foo();
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found void
    Span: SourceSpan(source_id=SourceId(2), start=65, end=70)
    ");
}

#[test]
fn test_void_assign_variable() {
    let source = r#"
        void foo() {}

        int main() {
            int x;
            x = foo();
            return 0;
        }
    "#;
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output, @r"
    Diagnostics count: 1

    Level: Error
    Message: type mismatch: expected int, found void
    Span: SourceSpan(source_id=SourceId(2), start=76, end=85)
    ");
}

#[test]
fn test_assign_enum_to_int() {
    let source = r#"
        enum E { X };
        int main() {
            enum E e = X;
            int i = e;
            return i;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
        %i: i32
      }

      bb1:
        %e = const 0
        %i = %e
        return %i
    }
    ");
}

#[test]
fn test_assign_int_to_enum() {
    let source = r#"
        enum E { X };
        int main() {
            enum E e;
            e = 0;
            return e;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
      }

      bb1:
        %e = const 0
        return %e
    }
    ");
}

#[test]
fn test_enum_constant_assignment() {
    let source = r#"
        enum E { X };
        int main() {
            enum E e;
            e = X;
            return e;
        }
    "#;
    let mir = setup_mir(source);
    insta::assert_snapshot!(mir, @r"
    type %t0 = i32

    fn main() -> i32
    {
      locals {
        %e: i32
      }

      bb1:
        %e = const 0
        return %e
    }
    ");
}
