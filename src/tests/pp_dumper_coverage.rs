use crate::ast::StringId;
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind, dumper::PPDumper};
use crate::source_manager::{SourceLoc, SourceManager};

#[test]
fn test_dumper_line_markers_and_macro_expansion() {
    let mut sm = SourceManager::new();
    let id1 = sm.add_buffer(b"int main() { return 0; }".to_vec(), "file1.c", None);
    let id2 = sm.add_buffer(b"int foo = 42;".to_vec(), "file2.c", None);

    // Ensure line starts are calculated for file1 so line numbers are correct
    sm.calculate_line_starts(id1);
    sm.calculate_line_starts(id2);

    let mut tokens = Vec::new();

    // 1. Token from file1: "int"
    // Location: file1, offset 0
    tokens.push(PPToken::new(
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenFlags::empty(),
        SourceLoc::new(id1, 0),
        3,
    ));

    // 2. Token from file2: "int" (triggers file transition to file2)
    // Location: file2, offset 0
    tokens.push(PPToken::new(
        PPTokenKind::Identifier(StringId::new("int")),
        PPTokenFlags::empty(),
        SourceLoc::new(id2, 0),
        3,
    ));

    // 3. Token from file1: "return" (triggers file transition back to file1)
    // Location: file1, offset 13 ("return" starts at 13 in "int main() { return 0; }")
    tokens.push(PPToken::new(
        PPTokenKind::Identifier(StringId::new("return")),
        PPTokenFlags::empty(),
        SourceLoc::new(id1, 13),
        6,
    ));

    // 4. Macro expanded token: "0"
    // Location: file1, offset 20 ("0" starts at 20).
    // Preceded by space in source (" return 0;"), so should print space if logic works.
    tokens.push(PPToken::new(
        PPTokenKind::Number(StringId::new("0")),
        PPTokenFlags::MACRO_EXPANDED,
        SourceLoc::new(id1, 20),
        1,
    ));

    // 5. Another macro expanded token: ";"
    // Location: file1, offset 21 (";" starts at 21).
    // Should print space between consecutive macro tokens.
    tokens.push(PPToken::new(
        PPTokenKind::Semicolon,
        PPTokenFlags::MACRO_EXPANDED,
        SourceLoc::new(id1, 21),
        1,
    ));

    let dumper = PPDumper::new(&tokens, &sm, false);
    let mut buffer = Vec::new();
    dumper.dump(&mut buffer).unwrap();

    let output = String::from_utf8(buffer).unwrap();
    println!("Output:\n{}", output);

    assert!(output.contains("# 1 \"file2.c\" 1"));
    assert!(output.contains("# 1 \"file1.c\" 1"));
    // Use generic assertions that are robust to spacing details, but ensure markers are present
    // and content appears.

    // Check specific sequence for macro expansion logic verification
    // "return" comes from file1.
    // "0" is macro expanded, but checks whitespace before it.
    // In "int main() { return 0; }", there is a space at index 19.
    // So dumper should emit " ".
    // Then "0".
    // Then space between macro tokens.
    // Then ";".
    // So "return 0 ;"

    assert!(output.contains("return 0 ;"));
}
