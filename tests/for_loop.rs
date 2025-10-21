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
