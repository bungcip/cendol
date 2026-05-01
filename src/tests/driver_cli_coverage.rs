use crate::driver::cli::PathOrBuffer;
use std::path::PathBuf;

#[test]
fn test_path_or_buffer_coverage() {
    // is_external_object tests
    let obj = PathOrBuffer::Path(PathBuf::from("test.o"));
    assert!(obj.is_external_object());

    let a = PathOrBuffer::Path(PathBuf::from("libtest.a"));
    assert!(a.is_external_object());

    let versioned_so = PathOrBuffer::Path(PathBuf::from("libtest.so.1"));
    assert!(versioned_so.is_external_object());

    let dylib = PathOrBuffer::Path(PathBuf::from("libtest.dylib.2"));
    assert!(dylib.is_external_object());

    let no_ext = PathOrBuffer::Path(PathBuf::from("test"));
    assert!(!no_ext.is_external_object());

    let buf = PathOrBuffer::Buffer("test.c".to_string(), vec![]);
    assert!(!buf.is_external_object());

    // is_source_file tests
    let c_file = PathOrBuffer::Path(PathBuf::from("test.c"));
    assert!(c_file.is_source_file());

    let i_file = PathOrBuffer::Path(PathBuf::from("test.i"));
    assert!(i_file.is_source_file());

    let no_ext_src = PathOrBuffer::Path(PathBuf::from("test"));
    assert!(!no_ext_src.is_source_file());

    let buf_src = PathOrBuffer::Buffer("test.c".to_string(), vec![]);
    assert!(buf_src.is_source_file());
}
