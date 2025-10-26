use cendol::test_utils::compile_and_run;

#[test]
fn test_long_long_declaration() {
    let input = r#"
    int main() {
        long long x = 10;
        return x;
    }
    "#;
    let exit_code = compile_and_run(input, "long_long_declaration").unwrap();
    assert_eq!(exit_code, 10);
}

#[test]
fn test_long_long_assignment() {
    let input = r#"
    int main() {
        long long x;
        x = 20;
        return x;
    }
    "#;
    let exit_code = compile_and_run(input, "long_long_assignment").unwrap();
    assert_eq!(exit_code, 20);
}

#[test]
fn test_long_long_addition() {
    let input = r#"
    int main() {
        long long x = 10;
        long long y = 20;
        return x + y;
    }
    "#;
    let exit_code = compile_and_run(input, "long_long_addition").unwrap();
    assert_eq!(exit_code, 30);
}

#[test]
fn test_long_long_large_number() {
    let input = r#"
    int main() {
        long long x = 5000000000;
        return x > 0;
    }
    "#;
    let exit_code = compile_and_run(input, "long_long_large_number").unwrap();
    assert_eq!(exit_code, 1);
}
