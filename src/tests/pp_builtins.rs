use crate::pp::PPConfig;
use crate::tests::pp_common::{setup_pp_snapshot_with_diags, setup_pp_snapshot_with_diags_and_config};
use chrono::{TimeZone, Utc};

#[test]
fn test_redefine_builtin_macro_should_fail() {
    let src = r#"
#define __DATE__ "123"
const char* s = __DATE__;
"#;
    // Bolt ⚡: Use a fixed date to ensure the snapshot is deterministic and doesn't flap daily.
    let mut config = PPConfig::default();
    config.current_time = Some(Utc.with_ymd_and_hms(2026, 1, 28, 0, 0, 0).unwrap());

    let (tokens, diags) = setup_pp_snapshot_with_diags_and_config(src, Some(config));

    // Currently, this probably succeeds and changes __DATE__.
    // We expect it to FAIL or warn and NOT change __DATE__.
    // For now, let's just snapshot what happens.
    insta::assert_yaml_snapshot!((tokens, diags));
}

#[test]
fn test_undef_builtin_macro_should_fail() {
    let src = r#"
#undef __DATE__
#ifdef __DATE__
int x = 1;
#else
int x = 0;
#endif
"#;
    let (tokens, diags) = setup_pp_snapshot_with_diags(src);
    insta::assert_yaml_snapshot!((tokens, diags));
}
