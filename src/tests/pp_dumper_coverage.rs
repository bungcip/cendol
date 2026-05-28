use crate::pp::{PPToken, PPTokenFlags, PPTokenKind, dumper::PPDumper};
use crate::source_manager::{FileKind, SourceLoc, SourceManager};

#[test]
fn test_dumper_with_includes() {
    let mut sm = SourceManager::new();

    // Create file 1
    let id1 = sm.add_buffer(b"int x;".to_vec(), "file1.c", None, FileKind::Real);

    // Create file 2
    let id2 = sm.add_buffer(b"int y;".to_vec(), "file2.h", None, FileKind::Real);

    // Construct tokens
    // File 1: int x;
    let t1 = PPToken::new(
        PPTokenKind::Identifier("int".into()),
        PPTokenFlags::empty(),
        SourceLoc::new(id1, 0),
        3,
    );
    // Switch to File 2: int y;
    let t2 = PPToken::new(
        PPTokenKind::Identifier("int".into()),
        PPTokenFlags::empty(),
        SourceLoc::new(id2, 0),
        3,
    );
    let t3 = PPToken::new(
        PPTokenKind::Identifier("y".into()),
        PPTokenFlags::empty(),
        SourceLoc::new(id2, 4),
        1,
    );
    let t4 = PPToken::new(PPTokenKind::Semicolon, PPTokenFlags::empty(), SourceLoc::new(id2, 5), 1);
    // Switch back to File 1: ;
    // "int x;" -> ';' is at offset 5
    let t5 = PPToken::new(PPTokenKind::Semicolon, PPTokenFlags::empty(), SourceLoc::new(id1, 5), 1);

    let tokens = vec![t1, t2, t3, t4, t5];

    let dumper = PPDumper::new(&tokens, &sm, false);
    let mut buf = Vec::new();
    dumper.dump(&mut buf).unwrap();

    let output = String::from_utf8(buf).unwrap();

    // We expect:
    // int
    // # 1 "file2.h" 1
    // int y;
    // # 1 "file1.c" 1
    // ;

    assert!(output.contains("# 1 \"file2.h\" 1"));
    assert!(output.contains("# 1 \"file1.c\" 1"));
    assert!(output.contains("int y;"));
}

#[test]
fn test_dumper_regression_out_of_bounds() {
    let mut sm = SourceManager::new();

    // Create file1.c (root file, small buffer)
    let id1 = sm.add_buffer(b"short;".to_vec(), "file1.c", None, FileKind::Real);
    let id1_loc = SourceLoc::new(id1, 0);

    // Create file2.h (included file, larger buffer, token at larger offset)
    // include_loc is set to id1_loc
    let file2_content = b"/* some header comment */\n\nint larger_offset_identifier;".to_vec();
    let id2 = sm.add_buffer(file2_content, "file2.h", Some(id1_loc), FileKind::Real);

    // Construct a token in file2.h at a large offset (31) exceeding the length of file1.c (6 bytes)
    let t_included = PPToken::new(
        PPTokenKind::Identifier("larger_offset_identifier".into()),
        PPTokenFlags::empty(),
        SourceLoc::new(id2, 31),
        24,
    );

    let tokens = vec![t_included];

    let dumper = PPDumper::new(&tokens, &sm, false);
    let mut buf = Vec::new();
    // This should not panic now with the bounds-check/correct-buffer resolution fix
    dumper.dump(&mut buf).unwrap();

    let output = String::from_utf8(buf).unwrap();
    assert!(output.contains("larger_offset_identifier"));
}
