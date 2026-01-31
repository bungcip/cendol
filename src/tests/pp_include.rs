use crate::pp::PPConfig;
use crate::tests::pp_common::setup_multi_file_pp_snapshot;

// Basic Include tests
#[test]
fn test_include_same_file_twice_without_pragma_once() {
    let files = vec![
        ("header_test_twice.h", "OK"),
        (
            "main.c",
            "#include \"header_test_twice.h\"\n#include \"header_test_twice.h\"",
        ),
    ];
    let (tokens, _) = setup_multi_file_pp_snapshot(files, "main.c", None);
    insta::assert_yaml_snapshot!(tokens, @r"
    - kind: Identifier
      text: OK
    - kind: Identifier
      text: OK
    ");
}

#[test]
fn test_circular_include_in_memory() {
    let files = vec![
        ("mem_a.h", "#include \"mem_b.h\""),
        ("mem_b.h", "#include \"mem_a.h\""),
        ("mem_main.c", "#include \"mem_a.h\""),
    ];
    let config = PPConfig {
        max_include_depth: 10,
        ..Default::default()
    };
    let (_, diags) = setup_multi_file_pp_snapshot(files, "mem_main.c", Some(config));
    insta::assert_yaml_snapshot!(diags, @r#"- "Fatal Error: IncludeDepthExceeded""#);
}
