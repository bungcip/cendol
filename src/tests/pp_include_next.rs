use crate::pp::{PPConfig, Preprocessor};
use crate::tests::test_utils::setup_sm_and_diag;
use std::fs::File;
use std::io::Write;
use tempfile::TempDir;

#[test]
fn test_include_next_quoted() {
    // Create temporary directories
    let dir1 = TempDir::new().unwrap();
    let dir2 = TempDir::new().unwrap();

    // dir1/foo.h
    let foo1_path = dir1.path().join("foo.h");
    {
        let mut file = File::create(&foo1_path).unwrap();
        writeln!(file, "#define FOO_1 1").unwrap();
    }

    // dir2/foo.h
    let foo2_path = dir2.path().join("foo.h");
    {
        let mut file = File::create(&foo2_path).unwrap();
        writeln!(file, "#include_next \"foo.h\"").unwrap();
        writeln!(file, "#define FOO_2 1").unwrap();
    }

    // main.c
    let main_path = dir2.path().join("main.c");
    {
        let mut file = File::create(&main_path).unwrap();
        writeln!(file, "#include \"foo.h\"").unwrap();
    }

    // Setup configuration
    let mut config = PPConfig::default();
    // Search order: dir2, dir1
    config.quoted_include_paths.push(dir2.path().to_path_buf());
    config.quoted_include_paths.push(dir1.path().to_path_buf());

    let (mut sm, mut diag) = setup_sm_and_diag();

    // Add main file
    let source_id = sm.add_file_from_path(&main_path, None).unwrap();

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);

    // Process
    let _ = pp.process(source_id, &config).unwrap();

    // Verify macros
    // We expect FOO_1 and FOO_2 to be defined if both files were processed.
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_1")));
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_2")));
}

#[test]
fn test_include_next_angled() {
    // Create temporary directories
    let dir1 = TempDir::new().unwrap();
    let dir2 = TempDir::new().unwrap();

    // dir1/foo.h
    let foo1_path = dir1.path().join("foo.h");
    {
        let mut file = File::create(&foo1_path).unwrap();
        writeln!(file, "#define FOO_1 1").unwrap();
    }

    // dir2/foo.h
    let foo2_path = dir2.path().join("foo.h");
    {
        let mut file = File::create(&foo2_path).unwrap();
        writeln!(file, "#include_next <foo.h>").unwrap();
        writeln!(file, "#define FOO_2 1").unwrap();
    }

    // main.c
    let main_path = dir2.path().join("main.c");
    {
        let mut file = File::create(&main_path).unwrap();
        writeln!(file, "#include <foo.h>").unwrap();
    }

    // Setup configuration
    let mut config = PPConfig::default();
    // Search order: dir2, dir1
    config.angled_include_paths.push(dir2.path().to_path_buf());
    config.angled_include_paths.push(dir1.path().to_path_buf());

    let (mut sm, mut diag) = setup_sm_and_diag();

    // Add main file
    let source_id = sm.add_file_from_path(&main_path, None).unwrap();

    let mut pp = Preprocessor::new(&mut sm, &mut diag, &config);

    // Process
    let _ = pp.process(source_id, &config).unwrap();

    // Verify macros
    // We expect FOO_1 and FOO_2 to be defined if both files were processed.
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_1")));
    assert!(pp.is_macro_defined(&crate::ast::StringId::new("FOO_2")));
}
