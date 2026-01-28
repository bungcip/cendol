use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_stringification_whitespace_handling() {
    let src = r#"
#define STR(x) #x
const char* s1 = STR(a+b);
const char* s2 = STR(a + b);
const char* s3 = STR( f(a, b) );
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_va_args_stringification() {
    let src = r#"
#define STR(...) #__VA_ARGS__
const char* s = STR(a, b, c);
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}
