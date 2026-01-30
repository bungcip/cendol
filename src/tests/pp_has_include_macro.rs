use crate::tests::pp_common::setup_pp_snapshot;

#[test]
fn test_has_include_macro() {
    let src = r#"
#define STDDEF <stddef.h>
#if __has_include(STDDEF)
int x = 1;
#else
int x = 0;
#endif

#define QUOTED "stdint.h"
#if __has_include(QUOTED)
int y = 1;
#else
int y = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}

#[test]
fn test_has_include_literal_protection() {
    let src = r#"
// Make sure stddef is defined as a macro
#define stddef BROKEN

// Literal include should NOT expand stddef
#if __has_include(<stddef.h>)
int z = 1;
#else
int z = 0;
#endif

// Computed include where macro is expanded inside should fail
#define H <stddef.h>
#if __has_include(H)
int w = 1;
#else
int w = 0;
#endif
"#;
    let tokens = setup_pp_snapshot(src);
    insta::assert_yaml_snapshot!(tokens);
}
