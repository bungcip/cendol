use super::semantic_common::setup_diagnostics_output;

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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
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
    let output = setup_diagnostics_output(source);
    insta::assert_snapshot!(output);
}
