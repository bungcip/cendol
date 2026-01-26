use crate::source_manager::*;

#[test]
fn test_source_loc_packing() {
    // Test basic packing/unpacking
    let source_id = SourceId::new(1);
    let offset = 12345;
    let loc = SourceLoc::new(source_id, offset);

    assert_eq!(loc.source_id(), source_id);
    assert_eq!(loc.offset(), offset);
}

#[test]
fn test_source_loc_max_offset() {
    let source_id = SourceId::new(1);
    let max_offset = (1 << 24) - 1; // 16 MiB - 1
    let loc = SourceLoc::new(source_id, max_offset);

    assert_eq!(loc.offset(), max_offset);
}

#[test]
fn test_source_loc_max_file_id() {
    let max_id = 1023;
    let source_id = SourceId::new(max_id);
    let offset = 0;
    let loc = SourceLoc::new(source_id, offset);

    assert_eq!(loc.source_id().0.get(), max_id);
}

#[test]
fn test_source_span_new() {
    let start = SourceLoc::new(SourceId::new(1), 10);
    let end = SourceLoc::new(SourceId::new(1), 20);
    let span = SourceSpan::new(start, end);

    assert_eq!(span.start(), start);
    assert_eq!(span.end(), end);
}

#[test]
fn test_source_span_empty() {
    let empty = SourceSpan::empty();
    assert_eq!(empty.start().source_id(), SourceId::new(1));
    assert_eq!(empty.start().offset(), 0);
    assert_eq!(empty.end().offset(), 0);
}

#[test]
fn test_source_span_source_id() {
    let source_id = SourceId::new(42);
    let start = SourceLoc::new(source_id, 0);
    let end = SourceLoc::new(source_id, 10);
    let span = SourceSpan::new(start, end);

    assert_eq!(span.source_id(), source_id);
}

#[test]
fn test_source_manager_get_source_text() {
    let mut sm = SourceManager::new();
    let content = "Hello World!";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);

    let start = SourceLoc::new(file_id, 6);
    let end = SourceLoc::new(file_id, 11);
    let span = SourceSpan::new(start, end);

    assert_eq!(sm.get_source_text(span), "World");
}

#[test]
fn test_source_manager_get_line_column() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);
    sm.calculate_line_starts_for_test(file_id);

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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);
    sm.calculate_line_starts_for_test(file_id);

    // Position at end of file
    let loc = SourceLoc::new(file_id, content.len() as u32);
    let (line, col) = sm.get_line_column(loc).unwrap();

    assert_eq!(line, 2);
    assert_eq!(col, 6); // "line2" is 5 chars + 1 for 1-based
}

#[test]
fn test_source_manager_get_line_column_before_start() {
    let mut sm = SourceManager::new();
    let content = "content";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);

    // Manually set line starts to start at offset 5
    // This simulates a scenario where we have some prefix that is not part of the lines
    // or simply an invalid state we want to ensure doesn't crash
    sm.set_line_starts(file_id, vec![5]);

    // Query location at offset 2 (before the first line start)
    let loc = SourceLoc::new(file_id, 2);
    let (line, col) = sm.get_line_column(loc).unwrap();

    // Expecting line 0 (invalid/before start) and column 1
    // This exercises the else branch in get_line_column where line becomes u32::MAX
    // and is handled by returning line 0 and column 0+1 = 1.
    assert_eq!(line, 0);
    assert_eq!(col, 1);
}

#[test]
fn test_source_manager_multiple_files() {
    let mut sm = SourceManager::new();
    let file1_id = sm.add_buffer("content1".as_bytes().to_vec(), "file1.c", None);
    let file2_id = sm.add_buffer("content2".as_bytes().to_vec(), "file2.c", None);

    assert_eq!(file1_id.0.get(), 2);
    assert_eq!(file2_id.0.get(), 3);

    assert_eq!(sm.get_buffer(file1_id), "content1".as_bytes());
    assert_eq!(sm.get_buffer(file2_id), "content2".as_bytes());
}

#[test]
fn test_source_manager_get_buffer() {
    let mut sm = SourceManager::new();
    let content = "test content";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);

    let buffer = sm.get_buffer(file_id);
    assert_eq!(buffer, content.as_bytes());
}

#[test]
fn test_source_manager_get_file_info() {
    let mut sm = SourceManager::new();
    let content = "test";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);

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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);

    let start = SourceLoc::new(file_id, 3);
    let end = SourceLoc::new(file_id, 10); // Beyond content length
    let span = SourceSpan::new(start, end);

    sm.get_source_text(span);
}

#[test]
fn test_source_manager_empty_file() {
    let mut sm = SourceManager::new();
    let file_id = sm.add_buffer("".as_bytes().to_vec(), "empty.c", None);

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.size, 0);
}

#[test]
fn test_source_manager_file_without_newlines() {
    let mut sm = SourceManager::new();
    let content = "no newlines here";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "no_nl.c", None);

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.size, content.len() as u32);
}

#[test]
fn test_source_manager_add_buffer() {
    let mut sm = SourceManager::new();
    let bytes = b"byte content";
    let file_id = sm.add_buffer(bytes.to_vec(), "bytes.c", None);

    assert_eq!(sm.get_buffer(file_id), bytes);
}

#[test]
fn test_line_map_empty() {
    let line_map = LineMap::new();
    assert!(line_map.entries.is_empty());
    assert_eq!(line_map.entries.len(), 0);
}

#[test]
fn test_line_map_add_entry() {
    let mut line_map = LineMap::new();
    let entry = LineDirective::new(10, 100, Some("test.c".to_string()));
    line_map.add_entry(entry);

    assert!(!line_map.entries.is_empty());
    assert_eq!(line_map.entries.len(), 1);
}

#[test]
fn test_line_map_presumed_location_no_mapping() {
    let line_map = LineMap::new();
    let (line, file) = line_map.presumed_location(5);
    assert_eq!(line, 5);
    assert_eq!(file, None);
}

#[test]
fn test_line_map_presumed_location_with_mapping() {
    let mut line_map = LineMap::new();
    // #line 100 at physical line 10
    line_map.add_entry(LineDirective::new(10, 100, Some("mapped.c".to_string())));

    // Query physical line 15 (5 lines after the directive)
    let (line, file) = line_map.presumed_location(15);
    assert_eq!(line, 105); // 100 + (15 - 10)
    assert_eq!(file, Some("mapped.c"));
}

#[test]
fn test_line_map_presumed_location_multiple_entries() {
    let mut line_map = LineMap::new();
    // #line 100 at physical line 10
    line_map.add_entry(LineDirective::new(10, 100, Some("first.c".to_string())));
    // #line 200 at physical line 20
    line_map.add_entry(LineDirective::new(20, 200, Some("second.c".to_string())));

    // Query physical line 15 (should use first mapping)
    let (line, file) = line_map.presumed_location(15);
    assert_eq!(line, 105); // 100 + (15 - 10)
    assert_eq!(file, Some("first.c"));

    // Query physical line 25 (should use second mapping)
    let (line, file) = line_map.presumed_location(25);
    assert_eq!(line, 205); // 200 + (25 - 20)
    assert_eq!(file, Some("second.c"));
}

#[test]
fn test_line_map_presumed_location_before_first_entry() {
    let mut line_map = LineMap::new();
    // #line 100 at physical line 10
    line_map.add_entry(LineDirective::new(10, 100, Some("test.c".to_string())));

    // Query physical line 5 (before first mapping)
    let (line, file) = line_map.presumed_location(5);
    assert_eq!(line, 5); // No mapping, use physical
    assert_eq!(file, None);
}

#[test]
fn test_line_map_presumed_location_filename_only() {
    let mut line_map = LineMap::new();
    // #line 1 at physical line 5, filename change only
    line_map.add_entry(LineDirective::new(5, 1, Some("newfile.c".to_string())));

    // Query physical line 10
    let (line, file) = line_map.presumed_location(10);
    assert_eq!(line, 6); // 1 + (10 - 5)
    assert_eq!(file, Some("newfile.c"));
}

#[test]
fn test_line_directive_ord() {
    let entry1 = LineDirective::new(10, 100, None);
    let entry2 = LineDirective::new(20, 200, None);
    let entry3 = LineDirective::new(10, 150, None);

    assert!(entry1 < entry2);
    assert_eq!(entry1.cmp(&entry3), std::cmp::Ordering::Equal); // Same physical line
}

#[test]
fn test_source_manager_get_presumed_location() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3\nline4\nline5";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);
    sm.calculate_line_starts_for_test(file_id);

    // Add a line mapping: at physical line 3, logical line 100
    {
        let line_map = sm.get_line_map_mut(file_id).unwrap();
        line_map.add_entry(LineDirective::new(3, 100, Some("logical.c".to_string())));
    }

    // Query location at physical line 4, column 2
    let loc = SourceLoc::new(file_id, 19); // Position in "line4" (line 4, col 2)
    let presumed = sm.get_presumed_location(loc);

    assert_eq!(presumed, Some((101, 2, Some("logical.c")))); // line 100 + 1, col 2
}

#[test]
fn test_source_manager_get_presumed_location_no_mapping() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c", None);
    sm.calculate_line_starts_for_test(file_id);

    // No line mappings
    let loc = SourceLoc::new(file_id, 7); // "line1\nl" position
    let presumed = sm.get_presumed_location(loc);

    assert_eq!(presumed, Some((2, 2, Some("test.c")))); // physical line 2, col 2
}

#[test]
fn test_line_map_performance_many_lookups() {
    let mut line_map = LineMap::new();

    // Add many line directives
    for i in 0..100 {
        line_map.add_entry(LineDirective::new(i * 10, i * 100, None));
    }

    // Perform many lookups
    for i in 0..1000 {
        let physical_line = i % 1000;
        let _ = line_map.presumed_location(physical_line);
    }

    // Test should complete quickly (binary search is O(log n))
    assert!(line_map.entries.len() == 100);
}

#[test]
fn test_struct_sizes() {
    assert_eq!(std::mem::size_of::<SourceLoc>(), 8);
    assert_eq!(std::mem::size_of::<SourceSpan>(), 8);
}

#[test]
#[should_panic(expected = "SourceSpan offset exceeds 16 MiB limit")]
fn test_source_span_offset_overflow() {
    let source_id = SourceId::new(1);
    let start = SourceLoc::new(source_id, 1 << 24); // 16 MiB
    let end = SourceLoc::new(source_id, (1 << 24) + 10);
    SourceSpan::new(start, end);
}

#[test]
fn test_source_span_length_limit() {
    let source_id = SourceId::new(1);
    // Length 70000 > 65535
    let start = SourceLoc::new(source_id, 0);
    let end = SourceLoc::new(source_id, 70000);
    let span = SourceSpan::new(start, end);

    // Should be capped at 65535
    assert_eq!(span.end().offset() - span.start().offset(), 65535);
}

#[test]
fn test_source_span_new_with_length() {
    let source_id = SourceId::new(1);
    let offset = 100;
    let length = 50;
    let span = SourceSpan::new_with_length(source_id, offset, length);

    assert_eq!(span.source_id(), source_id);
    assert_eq!(span.start().offset(), offset);
    assert_eq!(span.end().offset(), offset + length);
}

#[test]
fn test_source_span_new_with_length_limit() {
    let source_id = SourceId::new(1);
    let offset = 100;
    let length = 70000; // > 65535
    let span = SourceSpan::new_with_length(source_id, offset, length);

    // Should be capped at 65535
    assert_eq!(span.end().offset() - span.start().offset(), 65535);
}

#[test]
#[should_panic(expected = "SourceSpan offset exceeds 16 MiB limit")]
fn test_source_span_new_with_length_offset_overflow() {
    let source_id = SourceId::new(1);
    let offset = 1 << 24; // 16 MiB
    let length = 10;
    SourceSpan::new_with_length(source_id, offset, length);
}

#[test]
fn test_source_manager_edge_cases() {
    let mut sm = SourceManager::new();

    // 1. Invalid SourceID
    let invalid_id = SourceId::new(999);
    let loc = SourceLoc::new(invalid_id, 0);
    assert_eq!(sm.get_line_column(loc), None);
    assert_eq!(sm.get_presumed_location(loc), None);

    // Test helper methods with invalid ID (should not panic)
    sm.set_line_starts(invalid_id, vec![0, 10]);
    sm.calculate_line_starts_for_test(invalid_id);
    assert!(sm.get_line_map_mut(invalid_id).is_none());

    // 2. Empty line_starts (file added but not analyzed/calculated)
    let file_id = sm.add_buffer(b"content".to_vec(), "test.c", None);
    // Note: add_buffer initializes line_starts as empty
    let loc = SourceLoc::new(file_id, 5);
    // Should default to line 1, column offset+1
    assert_eq!(sm.get_line_column(loc), Some((1, 6)));
}

#[test]
fn test_virtual_buffer_newlines() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3";
    // Virtual buffers calculate line starts immediately
    let file_id = sm.add_virtual_buffer(content.as_bytes().to_vec(), "macro", None);

    // Check line 2
    let loc = SourceLoc::new(file_id, 6); // Start of "line2"
    let (line, col) = sm.get_line_column(loc).unwrap();
    assert_eq!(line, 2);
    assert_eq!(col, 1);

    // Check line 3
    let loc3 = SourceLoc::new(file_id, 12); // Start of "line3"
    let (line3, col3) = sm.get_line_column(loc3).unwrap();
    assert_eq!(line3, 3);
    assert_eq!(col3, 1);
}

#[test]
#[should_panic(expected = "invalid source_id SourceId(999)")]
fn test_source_manager_get_buffer_invalid_id() {
    let sm = SourceManager::new();
    let invalid_id = SourceId::new(999);
    sm.get_buffer(invalid_id);
}

#[test]
fn test_add_file_from_path_error() {
    let mut sm = SourceManager::new();
    let result = sm.add_file_from_path(std::path::Path::new("non_existent_file_xyz.c"), None);
    assert!(result.is_err());
}

#[test]
fn test_source_manager_get_file_id() {
    let mut sm = SourceManager::new();
    let content = "some content";
    let path = "test_path.c";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), path, None);

    // Test finding existing file
    let found_id = sm.get_file_id(path);
    assert_eq!(found_id, Some(file_id));

    // Test non-existent file
    let not_found = sm.get_file_id("non_existent.c");
    assert_eq!(not_found, None);
}
