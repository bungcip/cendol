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
    let max_offset = (1 << 22) - 1; // 4 MiB - 1
    let loc = SourceLoc::new(source_id, max_offset);

    assert_eq!(loc.offset(), max_offset);
}

#[test]
#[should_panic(expected = "Offset exceeds 4 MiB limit")]
fn test_source_loc_offset_overflow() {
    let source_id = SourceId::new(1);
    let overflow_offset = 1 << 22; // 4 MiB
    SourceLoc::new(source_id, overflow_offset);
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
#[should_panic(expected = "SourceId exceeds 1023 limit")]
fn test_source_loc_file_id_overflow() {
    let overflow_id = 1024;
    let source_id = SourceId::new(overflow_id);
    let offset = 0;
    SourceLoc::new(source_id, offset);
}

#[test]
fn test_source_span_new() {
    let start = SourceLoc::new(SourceId::new(1), 10);
    let end = SourceLoc::new(SourceId::new(1), 20);
    let span = SourceSpan::new(start, end);

    assert_eq!(span.start, start);
    assert_eq!(span.end, end);
}

#[test]
fn test_source_span_empty() {
    let empty = SourceSpan::empty();
    assert_eq!(empty.start.source_id(), SourceId::new(1));
    assert_eq!(empty.start.offset(), 0);
    assert_eq!(empty.end.offset(), 0);
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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");

    let start = SourceLoc::new(file_id, 6);
    let end = SourceLoc::new(file_id, 11);
    let span = SourceSpan::new(start, end);

    assert_eq!(sm.get_source_text(span), "World");
}

#[test]
fn test_source_manager_get_line_column() {
    let mut sm = SourceManager::new();
    let content = "line1\nline2\nline3";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");
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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");
    sm.calculate_line_starts_for_test(file_id);

    // Position at end of file
    let loc = SourceLoc::new(file_id, content.len() as u32);
    let (line, col) = sm.get_line_column(loc).unwrap();

    assert_eq!(line, 2);
    assert_eq!(col, 6); // "line2" is 5 chars + 1 for 1-based
}

#[test]
fn test_source_manager_multiple_files() {
    let mut sm = SourceManager::new();
    let file1_id = sm.add_buffer("content1".as_bytes().to_vec(), "file1.c");
    let file2_id = sm.add_buffer("content2".as_bytes().to_vec(), "file2.c");

    assert_eq!(file1_id.0.get(), 2);
    assert_eq!(file2_id.0.get(), 3);

    assert_eq!(sm.get_buffer(file1_id), "content1".as_bytes());
    assert_eq!(sm.get_buffer(file2_id), "content2".as_bytes());
}

#[test]
fn test_source_manager_get_buffer() {
    let mut sm = SourceManager::new();
    let content = "test content";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");

    let buffer = sm.get_buffer(file_id);
    assert_eq!(buffer, content.as_bytes());
}

#[test]
fn test_source_manager_get_file_info() {
    let mut sm = SourceManager::new();
    let content = "test";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");

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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");

    let start = SourceLoc::new(file_id, 3);
    let end = SourceLoc::new(file_id, 10); // Beyond content length
    let span = SourceSpan::new(start, end);

    sm.get_source_text(span);
}

#[test]
fn test_source_manager_empty_file() {
    let mut sm = SourceManager::new();
    let file_id = sm.add_buffer("".as_bytes().to_vec(), "empty.c");

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.size, 0);
}

#[test]
fn test_source_manager_file_without_newlines() {
    let mut sm = SourceManager::new();
    let content = "no newlines here";
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "no_nl.c");

    let info = sm.get_file_info(file_id).unwrap();
    assert_eq!(info.size, content.len() as u32);
}

#[test]
fn test_source_manager_add_buffer() {
    let mut sm = SourceManager::new();
    let bytes = b"byte content";
    let file_id = sm.add_buffer(bytes.to_vec(), "bytes.c");

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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");
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
    let file_id = sm.add_buffer(content.as_bytes().to_vec(), "test.c");
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
