mod common;
use common::compile_and_run;

#[test]
fn test_for_loop_with_declaration() {
    let input = r#"
    int main() {
        int a = 0;
        int b = 0;
        for (int i = 0; i < 5; i = i + 1) {
            a = a + 1;
            b = b + 1;
        }
        return b;
    }
    "#;
    let exit_code = compile_and_run(input, "for_loop_with_declaration").unwrap();
    assert_eq!(exit_code, 5);
}

#[test]
fn test_for_loop_with_empty_body() {
    let input = r#"
    int main() {
        for (int i = 0; i < 5; i++);
        return 0;
    }
    "#;
    let exit_code = compile_and_run(input, "for_loop_with_empty_body").unwrap();
    assert_eq!(exit_code, 0);
}

#[test]
fn test_for_loop_with_empty_init() {
    let input = r#"
    int main() {
        int i = 0;
        int a = 0;
        for (; i < 5; i++) {
            a = a + 1;
        }
        return a;
    }
    "#;
    let exit_code = compile_and_run(input, "for_loop_with_empty_init").unwrap();
    assert_eq!(exit_code, 5);
}
