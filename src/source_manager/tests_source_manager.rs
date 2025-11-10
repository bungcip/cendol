use super::*;
use std::num::NonZeroU32;

#[test]
fn test_source_loc_new() {
    let source_id = SourceId(NonZeroU32::new(1).unwrap());
    let offset = 100;
    let loc = SourceLoc::new(source_id, offset);

    assert_eq!(loc.source_id(), source_id);
    assert_eq!(loc.offset(), offset);
}

#[test]
fn test_source_loc_packing() {
    // Test basic packing/unpacking
    let source_id = SourceId(NonZeroU32::new(5).unwrap());
    let offset = 12345;
    let loc = SourceLoc::new(source_id, offset);

    assert_eq!(loc.source_id(), source_id);
    assert_eq!(loc.offset(), offset);
}

#[test]
fn test_source_loc_max_offset() {
    let source_id = SourceId(NonZeroU32::new(1).unwrap());
    let max_offset = (1 << 22) - 1; // 4 MiB - 1
    let loc = SourceLoc::new(source_id, max_offset);

    assert_eq!(loc.offset(), max_offset);
}

#[test]
#[should_panic(expected = "Offset exceeds 4 MiB limit")]
fn test_source_loc_offset_overflow() {
    let source_id = SourceId(NonZeroU32::new(1).unwrap());
    let overflow_offset = 1 << 22; // 4 MiB
    SourceLoc::new(source_id, overflow_offset);
}

#[test]
fn test_source_loc_max_file_id() {
    let max_id = 1023;
    let source_id = SourceId(NonZeroU32::new(max_id).unwrap());
    let offset = 0;
    let loc = SourceLoc::new(source_id, offset);

    assert_eq!(loc.source_id().0.get(), max_id);
}

#[test]
#[should_panic(expected = "SourceId exceeds 1023 limit")]
fn test_source_loc_file_id_overflow() {
    let overflow_id = 1024;
    let source_id = SourceId(NonZeroU32::new(overflow_id).unwrap());
    let offset = 0;
    SourceLoc::new(source_id, offset);
}

#[test]
fn test_source_span_new() {
    let start = SourceLoc::new(SourceId(NonZeroU32::new(1).unwrap()), 10);
    let end = SourceLoc::new(SourceId(NonZeroU32::new(1).unwrap()), 20);
    let span = SourceSpan::new(start, end);

    assert_eq!(span.start, start);
    assert_eq!(span.end, end);
}

#[test]
fn test_source_span_empty() {
    let empty = SourceSpan::empty();
    assert_eq!(empty.start.0, 0);
    assert_eq!(empty.end.0, 0);
}

#[test]
fn test_source_span_source_id() {
    let source_id = SourceId(NonZeroU32::new(42).unwrap());
    let start = SourceLoc::new(source_id, 0);
    let end = SourceLoc::new(source_id, 10);
    let span = SourceSpan::new(start, end);

    assert_eq!(span.source_id(), source_id);
}

#[test]
fn test_source_manager_add_file() {
    let mut sm = SourceManager::new();
    let content = "Hello\nWorld\n";
    let file_id = sm.add_file("test.c", content);

    assert_eq!(file_id.0.get(), 1);
    assert_eq!(sm.get_file_content(file_id), content);
}

#[test]
fn test_source_manager_get_source_text() {
    let mut sm = SourceManager::new();
    let content = "Hello World!";
    let file_id = sm.add_file("test.c", content);

    let start = SourceLoc::new(file_id, 6);
    let end = SourceLoc::new(file_id, 11);
    let span = SourceSpan::new(start, end);

    assert_eq!(sm.get_source_text(span), "World");
}

#[test]
fn test_source_manager_get_line_column() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3";
    let file_id = sm.add_file("test.c", content);

    // Position at 'l' in "line2"
    let loc = SourceLoc::new(file_id, 6); // "line1\n" is 6 bytes
    let (line, col) = sm.get_line_column(loc).unwrap();

    assert_eq!(line, 2);
    assert_eq!(col, 1);
}

#[test]
fn test_source_manager_get_line_column_end_of_file() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2";
    let file_id = sm.add_file("test.c", content);

    // Position at end of file
    let loc = SourceLoc::new(file_id, content.len() as u32);
    let (line, col) = sm.get_line_column(loc).unwrap();

    assert_eq!(line, 2);
    assert_eq!(col, 6); // "line2" is 5 chars + 1 for 1-based
}

#[test]
fn test_source_manager_multiple_files() {
    let mut sm = SourceManager::new();
    let file1_id = sm.add_file("file1.c", "content1");
    let file2_id = sm.add_file("file2.c", "content2");

    assert_eq!(file1_id.0.get(), 1);
    assert_eq!(file2_id.0.get(), 2);

    assert_eq!(sm.get_file_content(file1_id), "content1");
    assert_eq!(sm.get_file_content(file2_id), "content2");
}

#[test]
fn test_source_manager_get_buffer() {
    let mut sm = SourceManager::new();
    let content = "test content";
    let file_id = sm.add_file("test.c", content);

    let buffer = sm.get_buffer(file_id);
    assert_eq!(buffer, content.as_bytes());
}

#[test]
fn test_source_manager_get_file_info() {
    let mut sm = SourceManager::new();
    let content = "test";
    let file_id = sm.add_file("test.c", content);

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.file_id, file_id);
    assert_eq!(info.path, std::path::PathBuf::from("test.c"));
    assert_eq!(info.size, 4);
}

#[test]
#[should_panic(expected = "Invalid span range")]
fn test_source_manager_get_source_text_invalid_range() {
    let mut sm = SourceManager::new();
    let content = "short";
    let file_id = sm.add_file("test.c", content);

    let start = SourceLoc::new(file_id, 3);
    let end = SourceLoc::new(file_id, 10); // Beyond content length
    let span = SourceSpan::new(start, end);

    sm.get_source_text(span);
}

#[test]
fn test_source_manager_line_starts_calculation() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3\n";
    let file_id = sm.add_file("test.c", content);

    let info = sm.get_file_info(file_id).unwrap();
    // Should have line starts at 0, 6, 12, 18
    assert_eq!(info.line_starts, vec![0, 6, 12, 18]);
}

#[test]
fn test_source_manager_empty_file() {
    let mut sm = SourceManager::new();
    let file_id = sm.add_file("empty.c", "");

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.size, 0);
    assert_eq!(info.line_starts, vec![0]);
}

#[test]
fn test_source_manager_file_without_newlines() {
    let mut sm = SourceManager::new();
    let content = "no newlines here";
    let file_id = sm.add_file("no_nl.c", content);

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.line_starts, vec![0]);
}

#[test]
fn test_source_manager_add_file_bytes() {
    let mut sm = SourceManager::new();
    let bytes = b"byte content";
    let file_id = sm.add_file_bytes("bytes.c", bytes.to_vec());

    assert_eq!(sm.get_buffer(file_id), bytes);
}

#[test]
fn test_source_manager_add_buffer() {
    let mut sm = SourceManager::new();
    let buffer = b"buffer content".to_vec();
    let file_id = sm.add_buffer(buffer.clone(), "buffer.c");

    assert_eq!(sm.get_buffer(file_id), buffer);
}
