use crate::tests::pp_common::setup_preprocessor_test_with_diagnostics;

fn run_pp(src: &str) -> String {
    let result = setup_preprocessor_test_with_diagnostics(src, None);
    match result {
        Ok((tokens, _)) => {
            let mut output = String::new();
            for token in tokens {
                // Simplified reconstruction
                output.push_str(token.get_text());
                output.push(' ');
            }
            output
        }
        Err(_) => String::new(),
    }
}

#[test]
fn test_brace_comma_separation() {
    let src = r#"
#define CNT(x, y) 2
CNT({1, 2})
"#;
    // Should be parsed as 2 arguments: "{1" and " 2}"
    // The macro expansion should result in "2"
    let expected = "2";

    // With current buggy implementation, it sees 1 argument "{1, 2}" and fails macro expansion or errors.
    // If it errors, run_pp returns empty string.
    // If it sees 1 argument, it might error "InvalidMacroParameter" because CNT expects 2.
    // So the output would be empty or error diagnostic.

    // Let's assert what we expect AFTER the fix.
    // But since I need to verify failure first, I can comment this out or expect failure.
    // However, the instructions say "Tests must fail on the old behavior and pass after the change".
    // If the test fails, `cargo test` fails. That's good.

    let output = run_pp(src);
    // Removing whitespaces for easier comparison
    let output_clean: String = output.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(output_clean, expected);
}

#[test]
fn test_bracket_comma_separation() {
    let src = r#"
#define CNT(x, y) 2
CNT([1, 2])
"#;
    // Should be parsed as 2 arguments: "[1" and " 2]"
    let expected = "2";
    let output = run_pp(src);
    let output_clean: String = output.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(output_clean, expected);
}

#[test]
fn test_paren_comma_protection() {
    let src = r#"
#define ID(x) x
ID((1, 2))
"#;
    // Should be parsed as 1 argument: "(1, 2)"
    let expected = "(1,2)";
    let output = run_pp(src);
    let output_clean: String = output.chars().filter(|c| !c.is_whitespace()).collect();
    assert_eq!(output_clean, expected);
}

#[test]
fn test_brace_fails_if_one_arg_expected() {
    let src = r#"
#define ID(x) x
ID({1, 2})
"#;
    // Current behavior: parses as 1 arg "{1, 2}". Output is "{1, 2}".
    // Correct behavior: parses as 2 args. Error "InvalidMacroParameter".

    // We want to verify that currently it passes (incorrectly) or we can assert expected correct behavior (failure).
    // If we assert correct behavior, the test will fail now.

    let result = setup_preprocessor_test_with_diagnostics(src, None);
    // Expect error
    assert!(
        result.is_err()
            || result
                .unwrap()
                .1
                .iter()
                .any(|d| d.message.contains("Invalid macro parameter"))
    );
}
