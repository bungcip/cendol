
use assert_cmd::Command;
use predicates::prelude::*;

#[test]
fn test_verbose_output() {
    let mut cmd = Command::cargo_bin("cendol").unwrap();
    cmd.arg("--verbose")
        .arg("tests/external.c")
        .assert()
        .stderr(predicate::str::contains("[VERBOSE] Verbose output enabled"))
        .failure();
}
