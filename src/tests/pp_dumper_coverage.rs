use crate::pp::{PPToken, PPTokenKind, PPTokenFlags, dumper::PPDumper};
use crate::source_manager::{SourceManager, SourceLoc};

#[test]
fn test_dumper_with_includes() {
    let mut sm = SourceManager::new();

    // Create file 1
    let id1 = sm.add_buffer(b"int x;".to_vec(), "file1.c", None);
    sm.calculate_line_starts(id1);

    // Create file 2
    let id2 = sm.add_buffer(b"int y;".to_vec(), "file2.h", None);
    sm.calculate_line_starts(id2);

    // Construct tokens
    // File 1: int x;
    let t1 = PPToken::new(PPTokenKind::Identifier("int".into()), PPTokenFlags::empty(), SourceLoc::new(id1, 0), 3);
    // Switch to File 2: int y;
    let t2 = PPToken::new(PPTokenKind::Identifier("int".into()), PPTokenFlags::empty(), SourceLoc::new(id2, 0), 3);
    let t3 = PPToken::new(PPTokenKind::Identifier("y".into()), PPTokenFlags::empty(), SourceLoc::new(id2, 4), 1);
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
