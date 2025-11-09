use std::{collections::HashMap, num::NonZeroU32, path::PathBuf};

/// Source ID for identifying source files
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceId(pub NonZeroU32);

impl std::fmt::Display for SourceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SourceId({})", self.0)
    }
}

/// Packed file ID and byte offset in a single u32.
/// - Bits 0-21: Byte Offset (max 4 MiB file size)
/// - Bits 22-31: Source ID Index (max 1023 unique source files)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceLoc(pub u32);

impl SourceLoc {
    const OFFSET_MASK: u32 = (1 << 22) - 1; // 22 bits for offset
    const ID_SHIFT: u32 = 22; // Shift for SourceId

    pub fn new(source_id: SourceId, offset: u32) -> Self {
        assert!(offset <= Self::OFFSET_MASK, "Offset exceeds 4 MiB limit");
        assert!(
            source_id.0.get() <= (1 << (32 - Self::ID_SHIFT)) - 1,
            "SourceId exceeds 1023 limit"
        );

        let packed = (offset & Self::OFFSET_MASK) | (source_id.0.get() << Self::ID_SHIFT);
        SourceLoc(packed)
    }

    pub fn source_id(&self) -> SourceId {
        SourceId(
            NonZeroU32::new((self.0 >> Self::ID_SHIFT) & ((1 << (32 - Self::ID_SHIFT)) - 1))
                .expect("Invalid SourceId"),
        )
    }

    pub fn offset(&self) -> u32 {
        self.0 & Self::OFFSET_MASK
    }
}

/// Represents a range in the source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceSpan {
    pub start: SourceLoc,
    pub end: SourceLoc,
}

impl SourceSpan {
    pub fn new(start: SourceLoc, end: SourceLoc) -> Self {
        Self { start, end }
    }

    pub fn empty() -> Self {
        Self {
            start: SourceLoc(0),
            end: SourceLoc(0),
        }
    }

    pub fn source_id(&self) -> SourceId {
        self.start.source_id()
    }
}

/// File information for tracking source files
#[derive(Debug)]
pub struct FileInfo {
    pub file_id: SourceId,
    pub path: PathBuf,
    pub size: u32,
    pub buffer_index: usize,   // Index into buffers Vec
    pub line_starts: Vec<u32>, // Line start offsets for efficient line lookup
}

/// Manages source files and locations
/// File size limit: 4 MiB per file (22-bit offset in SourceLoc)
/// Maximum files: 1023 unique source files (10-bit file ID in SourceLoc)
pub struct SourceManager {
    files: Vec<SourceFile>,
    buffers: Vec<Vec<u8>>, // Use Rust Vec<u8>
    file_infos: HashMap<SourceId, FileInfo>,
    next_file_id: u32,
}

impl SourceManager {
    pub fn new() -> Self {
        SourceManager {
            files: Vec::new(),
            buffers: Vec::new(),
            file_infos: HashMap::new(),
            next_file_id: 1, // Start from 1 for NonZeroU32
        }
    }

    /// Add a file to the source manager from a file path
    /// Since we only support UTF-8, we can read directly as bytes and assume validity
    pub fn add_file_from_path(
        &mut self,
        path: &std::path::Path,
    ) -> Result<SourceId, std::io::Error> {
        let buffer = std::fs::read(path)?;
        let path_str = path.to_str().unwrap_or("<invalid-utf8>");
        Ok(self.add_file_bytes(path_str, buffer))
    }

    /// Add a file to the source manager with raw bytes (UTF-8 assumed)
    pub fn add_file_bytes(&mut self, path: &str, buffer: Vec<u8>) -> SourceId {
        let file_id = SourceId(NonZeroU32::new(self.next_file_id).expect("File ID overflow"));
        self.next_file_id += 1;

        let size = buffer.len() as u32;
        let buffer_index = self.buffers.len();
        self.buffers.push(buffer);

        // Calculate line starts
        let line_starts = self.calculate_line_starts(&self.buffers[buffer_index]);

        let file_info = FileInfo {
            file_id,
            path: PathBuf::from(path),
            size,
            buffer_index,
            line_starts,
        };

        self.file_infos.insert(file_id, file_info);

        file_id
    }

    /// Add a file to the source manager
    pub fn add_file(&mut self, path: &str, content: &str) -> SourceId {
        let file_id = SourceId(NonZeroU32::new(self.next_file_id).expect("File ID overflow"));
        self.next_file_id += 1;

        // Convert content to bytes
        let buffer = content.as_bytes().to_vec();
        let size = buffer.len() as u32;
        let buffer_index = self.buffers.len();
        self.buffers.push(buffer);

        // Calculate line starts
        let line_starts = self.calculate_line_starts(&self.buffers[buffer_index]);

        let file_info = FileInfo {
            file_id,
            path: PathBuf::from(path),
            size,
            buffer_index,
            line_starts,
        };

        self.file_infos.insert(file_id, file_info);

        file_id
    }

    /// Add a buffer to the source manager
    pub fn add_buffer(&mut self, buffer: Vec<u8>, path: &str) -> SourceId {
        let file_id = SourceId(NonZeroU32::new(self.next_file_id).expect("File ID overflow"));
        self.next_file_id += 1;

        let size = buffer.len() as u32;
        let buffer_index = self.buffers.len();
        self.buffers.push(buffer);

        // Calculate line starts
        let line_starts = self.calculate_line_starts(&self.buffers[buffer_index]);

        let file_info = FileInfo {
            file_id,
            path: PathBuf::from(path),
            size,
            buffer_index,
            line_starts,
        };

        self.file_infos.insert(file_id, file_info);

        file_id
    }

    /// Get the buffer for a given source ID
    /// Since SourceId is always valid (we panic if not found), we can use indexing
    pub fn get_buffer(&self, source_id: SourceId) -> &[u8] {
        let info = self.file_infos.get(&source_id).expect("Invalid SourceId");
        &self.buffers[info.buffer_index][..]
    }

    /// Get file content as string for a given source ID
    /// Since we only support UTF-8, we can assume the bytes are valid UTF-8
    pub fn get_file_content(&self, source_id: SourceId) -> String {
        let buffer = self.get_buffer(source_id);
        unsafe { String::from_utf8_unchecked(buffer.to_vec()) }
    }

    /// Get file info for a given source ID
    pub fn get_file_info(&self, source_id: SourceId) -> Option<&FileInfo> {
        self.file_infos.get(&source_id)
    }

    /// Get the source text for a given span
    /// Since we only support UTF-8, we can assume the bytes are valid UTF-8
    pub fn get_source_text(&self, span: SourceSpan) -> &str {
        let buffer = self.get_buffer(span.source_id());
        let start = span.start.offset() as usize;
        let end = span.end.offset() as usize;

        if start <= end && end <= buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) }
        } else {
            panic!("Invalid span range");
        }
    }

    /// Calculate line start offsets for a buffer
    fn calculate_line_starts(&self, buffer: &[u8]) -> Vec<u32> {
        let mut line_starts = vec![0]; // First line starts at offset 0

        for (i, &byte) in buffer.iter().enumerate() {
            if byte == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }

        line_starts
    }

    /// Get line and column for a source location
    pub fn get_line_column(&self, loc: SourceLoc) -> Option<(u32, u32)> {
        let file_info = self.get_file_info(loc.source_id())?;
        let offset = loc.offset();

        // Binary search to find the line
        let line_starts = &file_info.line_starts;
        let mut left = 0;
        let mut right = line_starts.len();

        while left < right {
            let mid = left + (right - left) / 2;
            if line_starts[mid] <= offset {
                left = mid + 1;
            } else {
                right = mid;
            }
        }

        let line = (left - 1) as u32;
        let column = if line < line_starts.len() as u32 {
            offset - line_starts[line as usize]
        } else {
            0
        };

        Some((line + 1, column + 1)) // 1-based indexing
    }
}

/// Placeholder for SourceFile - may be expanded in the future
#[derive(Debug)]
pub struct SourceFile {
    // Placeholder - implementation may vary based on needs
}

impl Default for SourceManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests;
