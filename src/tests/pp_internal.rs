use crate::ast::StringId;
use crate::diagnostic::DiagnosticEngine;
use crate::pp::{HeaderSearch, PPConfig, PPToken, PPTokenFlags, PPTokenKind, Preprocessor};
use crate::source_manager::{SourceLoc, SourceManager};

fn create_dummy_preprocessor<'a>(sm: &'a mut SourceManager, diag: &'a mut DiagnosticEngine) -> Preprocessor<'a> {
    let config = PPConfig::default();
    Preprocessor::new(sm, diag, &config)
}

#[test]
fn test_header_search_resolution() {
    use std::fs::File;

    // Create temporary directories for search paths
    let temp_dir = tempfile::tempdir().unwrap();
    let system_dir = temp_dir.path().join("system");
    let angled_dir = temp_dir.path().join("angled");
    let framework_dir = temp_dir.path().join("framework");
    let local_dir = temp_dir.path().join("local");

    std::fs::create_dir(&system_dir).unwrap();
    std::fs::create_dir(&angled_dir).unwrap();
    std::fs::create_dir(&framework_dir).unwrap();
    std::fs::create_dir(&local_dir).unwrap();

    // Create dummy headers
    File::create(system_dir.join("sys.h")).unwrap();
    File::create(angled_dir.join("ang.h")).unwrap();
    File::create(framework_dir.join("frm.h")).unwrap();
    File::create(local_dir.join("loc.h")).unwrap();

    let mut search = HeaderSearch {
        system_path: Vec::new(),
        framework_path: Vec::new(),
        quoted_includes: Vec::new(),
        angled_includes: Vec::new(),
    };

    search.add_system_path(system_dir.clone());
    search.add_angled_path(angled_dir.clone());
    search.add_framework_path(framework_dir.clone());

    // Test angled includes (<header.h>)
    // Should find in angled_path
    let resolved = search.resolve_path("ang.h", true, &local_dir);
    assert_eq!(resolved.unwrap(), angled_dir.join("ang.h"));

    // Should find in system_path
    let resolved = search.resolve_path("sys.h", true, &local_dir);
    assert_eq!(resolved.unwrap(), system_dir.join("sys.h"));

    // Should find in framework_path
    let resolved = search.resolve_path("frm.h", true, &local_dir);
    assert_eq!(resolved.unwrap(), framework_dir.join("frm.h"));

    // Should NOT find local header for angled include (unless in search path)
    let resolved = search.resolve_path("loc.h", true, &local_dir);
    assert!(resolved.is_none());

    // Test quoted includes ("header.h")
    // Should find in current dir first
    let resolved = search.resolve_path("loc.h", false, &local_dir);
    assert_eq!(resolved.unwrap(), local_dir.join("loc.h"));

    // Should fallback to system/angled/framework
    let resolved = search.resolve_path("sys.h", false, &local_dir);
    assert_eq!(resolved.unwrap(), system_dir.join("sys.h"));
}

#[test]
fn test_destringize() {
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::default();
    let pp = create_dummy_preprocessor(&mut sm, &mut diag);

    // Test case 1: No escape sequences
    assert_eq!(pp.destringize("\"hello\""), "hello");

    // Test case 2: Simple escape sequences
    assert_eq!(pp.destringize("\"a\\nb\\tc\\r\\\\d\\\'e\\\"f\""), "a\nb\tc\r\\d\'e\"f");

    // Test case 3: Octal escapes
    assert_eq!(pp.destringize("\"\\123\""), "S");
    assert_eq!(pp.destringize("\"\\0\""), "\0");
    assert_eq!(pp.destringize("\"\\7\""), "\x07");
    assert_eq!(pp.destringize("\"a\\123b\""), "aSb");

    // Test case 4: Hexadecimal escapes
    assert_eq!(pp.destringize("\"\\x41\""), "A");
    assert_eq!(pp.destringize("\"\\x1b\""), "\x1b");
    assert_eq!(pp.destringize("\"a\\x41g\""), "aAg");
    assert_eq!(pp.destringize("\"\\x0a\""), "\n");

    // Test case 5: Mixed and complex cases
    assert_eq!(pp.destringize("\"a\\\\\\\"b\\tc\\123d\\x41g\""), "a\\\"b\tcSdAg");

    // Test case 6: Empty string
    assert_eq!(pp.destringize("\"\""), "");
}

#[test]
fn test_stringify_tokens_utf8() {
    let mut sm = SourceManager::new();
    let mut diag = DiagnosticEngine::default();

    let utf8_text = "⚡ Bolt ⚡";
    let sid = sm.add_buffer(utf8_text.as_bytes().to_vec(), "test.c", None);

    let text_with_escapes = "a\"b\\c";
    let sid2 = sm.add_buffer(text_with_escapes.as_bytes().to_vec(), "test2.c", None);

    let pp = create_dummy_preprocessor(&mut sm, &mut diag);

    let token = PPToken::new(
        PPTokenKind::Identifier(StringId::new(utf8_text)),
        PPTokenFlags::empty(),
        SourceLoc::new(sid, 0),
        utf8_text.len() as u16,
    );

    let stringified = pp.stringify_tokens(&[token], SourceLoc::builtin()).unwrap();
    if let PPTokenKind::StringLiteral(s) = stringified.kind {
        assert_eq!(s.as_str(), "\"⚡ Bolt ⚡\"");
    } else {
        panic!("Expected StringLiteral");
    }

    // Test with escaping
    let token2 = PPToken::new(
        PPTokenKind::Identifier(StringId::new(text_with_escapes)),
        PPTokenFlags::empty(),
        SourceLoc::new(sid2, 0),
        text_with_escapes.len() as u16,
    );

    let stringified2 = pp.stringify_tokens(&[token2], SourceLoc::builtin()).unwrap();
    if let PPTokenKind::StringLiteral(s) = stringified2.kind {
        assert_eq!(s.as_str(), "\"a\\\"b\\\\c\"");
    } else {
        panic!("Expected StringLiteral");
    }
}
