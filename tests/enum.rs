use cendol::test_utils::compile_and_run;

#[test]
fn test_enum() {
    let source = r#"
        enum Color { RED, GREEN, BLUE };
        int main() {
            return BLUE;
        }
    "#;
    let result = compile_and_run(source, "test_enum").unwrap();
    assert_eq!(result, 2);
}

#[test]
fn test_enum_with_initializers() {
    let source = r#"
        enum Color { RED = 5, GREEN, BLUE };
        int main() {
            return GREEN;
        }
    "#;
    let result = compile_and_run(source, "test_enum_with_initializers").unwrap();
    assert_eq!(result, 6);
}

#[test]
fn test_enum_with_gaps() {
    let source = r#"
        enum Color { RED = 1, GREEN = 3, BLUE };
        int main() {
            return BLUE;
        }
    "#;
    let result = compile_and_run(source, "test_enum_with_gaps").unwrap();
    assert_eq!(result, 4);
}

#[test]
#[should_panic]
fn test_invalid_enum_initializer() {
    let source = r#"
        enum Color { RED = 1.5, GREEN, BLUE };
        int main() {
            return 0;
        }
    "#;
    compile_and_run(source, "test_invalid_enum_initializer").unwrap();
}
