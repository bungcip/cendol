use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_digraph_bracket() {
    let src = r#"
<: 1, 2 :>
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_brace() {
    let src = r#"
<% 1; 2; %>
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_hash() {
    let src = r#"
%:define FOO 1
FOO
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_hashhash() {
    let src = r#"
#define CONCAT(a, b) a %:%: b
CONCAT(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_hashhash_with_digraph_hash() {
    let src = r#"
%:define CONCAT(a, b) a %:%: b
CONCAT(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_skipping() {
    let src = r#"
%:if 0
  this is skipped;
  <: %> %:%:
%:else
  this is not skipped
%:endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_mixed() {
    let src = r#"
%:define M(a, b) a %:%: b
int x <: 1 :> = <% M(1, 2) %>;
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_digraph_line_splice() {
    let src = r#"
%\
:define FOO 1
FOO

#define CONCAT(a, b) a %\
:\
%\
: b
CONCAT(1, 2)
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}
