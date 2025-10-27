mod common;

#[test]
fn test_float_add() {
    let c_program = r#"
        int main() {
            float a = 1.5;
            float b = 2.5;
            float c = a + b;
            return (int)c;
        }
    "#;
    let result = common::compile_and_run(c_program, "float_add").unwrap();
    assert_eq!(result, 4);
}
