use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use std::path::PathBuf;

/// A unique identifier for a file.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Default, serde::Serialize)]
pub struct FileId(pub u32);

impl Display for FileId {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        fmt.write_str("FileId(")?;
        fmt.write_str(self.0.to_string().as_str())?;
        fmt.write_str(")")
    }
}

/// Represents a single compressed source location (file_id + offset).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default, serde::Serialize)]
pub struct SourceLocation(u32);

impl SourceLocation {
    const OFFSET_BITS: u32 = 22; // 4 MB max per file
    const OFFSET_MASK: u32 = (1 << Self::OFFSET_BITS) - 1;

    #[inline(always)]
    pub fn new(file_id: FileId, offset: u32) -> Self {
        assert!(
            file_id.0 < (1 << (32 - Self::OFFSET_BITS)),
            "file_id overflow"
        );
        assert!(offset < (1 << Self::OFFSET_BITS), "offset overflow");
        let value = (file_id.0 << Self::OFFSET_BITS) | (offset & Self::OFFSET_MASK);
        Self(value)
    }

    #[inline(always)]
    pub fn file_id(&self) -> FileId {
        FileId(self.0 >> Self::OFFSET_BITS)
    }

    #[inline(always)]
    pub fn offset(&self) -> u32 {
        self.0 & Self::OFFSET_MASK
    }

    #[inline(always)]
    pub fn raw(&self) -> u32 {
        self.0
    }
}

/// Represents a span in a source file.
#[derive(Clone, Copy, PartialEq, Eq, Default, serde::Serialize)]
pub struct SourceSpan {
    pub start: SourceLocation,
    pub end: SourceLocation,
}

impl SourceSpan {
    pub fn new(start: SourceLocation, end: SourceLocation) -> Self {
        assert_eq!(
            start.file_id(),
            end.file_id(),
            "Span across files not allowed"
        );
        Self { start, end }
    }

    pub fn file_id(&self) -> FileId {
        self.start.file_id()
    }

    pub fn start_offset(&self) -> u32 {
        self.start.offset()
    }

    pub fn end_offset(&self) -> u32 {
        self.end.offset()
    }
}

impl Debug for SourceSpan {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "SourceSpan(fileid={}, offset={}..{})", self.start.file_id().0, self.start.offset(), self.end.offset())
    }
}

/// Represents a single loaded source file with precomputed line positions.
#[derive(Clone)]
pub struct SourceFile {
    pub id: FileId,
    pub name: PathBuf,
    pub content: String,
    pub line_starts: Vec<u32>, // offset of each lines
}

impl SourceFile {
    pub fn new(id: FileId, name: PathBuf, content: String) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in content.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }
        Self {
            id,
            name,
            content,
            line_starts,
        }
    }

    pub fn lookup_line_col(&self, offset: u32) -> (u32, u32) {
        let line = match self.line_starts.binary_search(&offset) {
            Ok(l) => l,
            Err(next) => next.saturating_sub(1),
        };
        let col = offset - self.line_starts[line];
        (line as u32 + 1, col + 1)
    }
}

/// Central registry for all source files.
#[derive(Default, Clone)]
pub struct SourceMap {
    pub files: HashMap<FileId, SourceFile>,
}

impl SourceMap {
    pub fn insert(&mut self, file: SourceFile) {
        self.files.insert(file.id, file);
    }

    pub fn get(&self, id: FileId) -> Option<&SourceFile> {
        self.files.get(&id)
    }

    pub fn lookup_line_col(&self, file_id: FileId, offset: u32) -> Option<(u32, u32)> {
        self.files.get(&file_id).map(|f| f.lookup_line_col(offset))
    }

    pub fn lookup_span(&self, span: &SourceSpan) -> Option<((u32, u32), (u32, u32))> {
        self.files.get(&span.file_id()).map(|f| {
            (
                f.lookup_line_col(span.start_offset()),
                f.lookup_line_col(span.end_offset()),
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::source::{SourceLocation, FileId};

    #[test]
    fn source_loc_equality(){
        // checking if implementation is right
        let a = SourceLocation::new(FileId(0), 10);
        let b = SourceLocation::new(FileId(0), 10);
        assert_eq!(a, b);
    }

    #[test]
    fn source_loc_offset(){
        // checking if implementation is right
        let a = SourceLocation::new(FileId(0), 10);
        assert_eq!(a.file_id(), FileId(0));
        assert_eq!(a.offset(), 10);
    }

}