use std::{num::NonZeroU32, path::PathBuf, cmp::Ordering};
use hashbrown::HashMap;

/// Source ID for identifying source files
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceId(pub NonZeroU32);

impl std::fmt::Display for SourceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SourceId({})", self.0)
    }
}

impl SourceId {
    /// create a new SourceId from a u32. panics if id is zero.
    pub fn new(id: u32) -> Self {
        SourceId(NonZeroU32::new(id).expect("SourceId must be non-zero"))
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
            source_id.0.get() < (1 << (32 - Self::ID_SHIFT)),
            "SourceId exceeds 1023 limit"
        );

        let packed = (offset & Self::OFFSET_MASK) | (source_id.0.get() << Self::ID_SHIFT);
        SourceLoc(packed)
    }

    pub fn empty() -> Self {
        SourceLoc(0)
    }

    /// built-in source location (SourceId = 1, offset = 0)
    pub fn builtin() -> Self {
        SourceLoc::new(SourceId::new(1), 0)
    }

    pub fn source_id(&self) -> SourceId {
        SourceId::new((self.0 >> Self::ID_SHIFT) & ((1 << (32 - Self::ID_SHIFT)) - 1))
    }

    pub fn offset(&self) -> u32 {
        self.0 & Self::OFFSET_MASK
    }
}

impl std::fmt::Display for SourceLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SourceLoc(source_id={}, offset={})",
            self.source_id(),
            self.offset()
        )
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
            start: SourceLoc::empty(),
            end: SourceLoc::empty(),
        }
    }

    pub fn source_id(&self) -> SourceId {
        self.start.source_id()
    }
}

impl std::fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SourceSpan(source_id={}, start={}, end={})",
            self.source_id(),
            self.start.offset(),
            self.end.offset()
        )
    }
}

/// Represents a single #line directive entry
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineDirective {
    pub physical_line: u32,
    pub logical_line: u32,
    pub logical_file: Option<String>,
}

impl LineDirective {
    pub fn new(physical_line: u32, logical_line: u32, logical_file: Option<String>) -> Self {
        LineDirective {
            physical_line,
            logical_line,
            logical_file,
        }
    }
}

impl Ord for LineDirective {
    fn cmp(&self, other: &Self) -> Ordering {
        self.physical_line.cmp(&other.physical_line)
    }
}

impl PartialOrd for LineDirective {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Stores all #line directives for a single file, sorted by physical line
#[derive(Debug, Clone, Default)]
pub struct LineMap {
    entries: Vec<LineDirective>,
}

impl LineMap {
    pub fn new() -> Self {
        LineMap {
            entries: Vec::new(),
        }
    }

    /// Add a line directive entry. Must be added in sorted order by physical_line.
    pub fn add_entry(&mut self, entry: LineDirective) {
        // Ensure monotonic addition
        if let Some(last) = self.entries.last() {
            assert!(entry.physical_line >= last.physical_line, "Line directives must be added in sorted order");
        }
        self.entries.push(entry);
    }

    /// Find the presumed location for a given physical line
    pub fn presumed_location(&self, physical_line: u32) -> (u32, Option<&str>) {
        // Binary search to find the last entry where physical_line <= target
        let idx = self.entries.partition_point(|e| e.physical_line <= physical_line);

        if idx == 0 {
            // No mapping, use physical line
            (physical_line, None)
        } else {
            let entry = &self.entries[idx - 1];
            let logical_line = entry.logical_line + (physical_line - entry.physical_line);
            // If entry has no logical file, it means no change from physical file
            (logical_line, entry.logical_file.as_deref())
        }
    }

    /// Check if the LineMap is empty (no #line directives)
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Get the number of entries
    pub fn len(&self) -> usize {
        self.entries.len()
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
    pub line_map: LineMap,     // #line directive mappings
}

/// Manages source files and locations
/// File size limit: 4 MiB per file (22-bit offset in SourceLoc)
/// Maximum files: 1023 unique source files (10-bit file ID in SourceLoc)
pub struct SourceManager {
    buffers: Vec<Vec<u8>>, // Use Rust Vec<u8>
    file_infos: HashMap<SourceId, FileInfo>,
    next_file_id: u32,
}

impl SourceManager {
    pub fn new() -> Self {
        SourceManager {
            buffers: Vec::new(),
            file_infos: HashMap::new(),
            next_file_id: 2, // Start from 2, reserve 1 for built-ins
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
        Ok(self.add_buffer(buffer, path_str))
    }

    /// Add a buffer to the source manager with raw bytes (UTF-8 assumed)
    pub fn add_buffer(&mut self, buffer: Vec<u8>, path: &str) -> SourceId {
        let file_id = SourceId::new(self.next_file_id);
        self.next_file_id += 1;

        let size = buffer.len() as u32;
        let buffer_index = self.buffers.len();
        self.buffers.push(buffer);

        let file_info = FileInfo {
            file_id,
            path: PathBuf::from(path),
            size,
            buffer_index,
            line_starts: Vec::new(),
            line_map: LineMap::new(),
        };

        self.file_infos.insert(file_id, file_info);

        file_id
    }

    /// Add a virtual buffer for macro expansions (Level B support)
    /// Virtual buffers contain expanded macro text with proper sequential locations
    pub fn add_virtual_buffer(&mut self, buffer: Vec<u8>, name: &str) -> SourceId {
        let file_id = SourceId::new(self.next_file_id);
        self.next_file_id += 1;

        let size = buffer.len() as u32;
        let buffer_index = self.buffers.len();
        self.buffers.push(buffer);

        // Calculate line starts for the virtual buffer
        let mut line_starts = vec![0]; // First line starts at offset 0
        for (i, &byte) in self.buffers[buffer_index].iter().enumerate() {
            if byte == b'\n' {
                line_starts.push((i + 1) as u32);
            }
        }

        let file_info = FileInfo {
            file_id,
            path: PathBuf::from(format!("<{}>", name)), // Virtual files use <> notation
            size,
            buffer_index,
            line_starts,
            line_map: LineMap::new(),
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


    /// Get file info for a given source ID
    pub fn get_file_info(&self, source_id: SourceId) -> Option<&FileInfo> {
        self.file_infos.get(&source_id)
    }

    /// Get file info for a given source ID
    pub fn get_file_id(&self, path: &str) -> Option<SourceId> {
        for (id, info) in self.file_infos.iter() {
            if info.path == std::path::Path::new(path) {
                return Some(*id);
            }
        }
        None
    }

    /// Get mutable access to the LineMap for a given source ID
    pub fn get_line_map_mut(&mut self, source_id: SourceId) -> Option<&mut LineMap> {
        self.file_infos.get_mut(&source_id).map(|fi| &mut fi.line_map)
    }

    /// Set line starts for a given source ID
    pub fn set_line_starts(&mut self, source_id: SourceId, line_starts: Vec<u32>) {
        if let Some(file_info) = self.file_infos.get_mut(&source_id) {
            file_info.line_starts = line_starts;
        }
    }

    /// Calculate line starts for a given source ID (for testing)
    #[cfg(test)]
    pub fn calculate_line_starts_for_test(&mut self, source_id: SourceId) {
        if let Some(file_info) = self.file_infos.get_mut(&source_id) {
            let buffer = &self.buffers[file_info.buffer_index];
            let mut line_starts = vec![0]; // First line starts at offset 0

            for (i, &byte) in buffer.iter().enumerate() {
                if byte == b'\n' {
                    line_starts.push((i + 1) as u32);
                }
            }

            file_info.line_starts = line_starts;
        }
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


    /// Get line and column for a source location
    pub fn get_line_column(&self, loc: SourceLoc) -> Option<(u32, u32)> {
        let file_info = self.get_file_info(loc.source_id())?;
        let offset = loc.offset();

        let line_starts = &file_info.line_starts;
        if line_starts.is_empty() {
            // If line_starts not calculated yet, assume single line starting at 0
            return Some((1, offset + 1));
        }

        // Binary search to find the line
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

    /// Get the presumed location (logical line and file) for a source location
    pub fn get_presumed_location(&self, loc: SourceLoc) -> Option<(u32, u32, Option<&str>)> {
        let file_info = self.get_file_info(loc.source_id())?;
        let physical_line = self.get_line_column(loc)?.0;

        let (logical_line, logical_file) = file_info.line_map.presumed_location(physical_line);
        let column = self.get_line_column(loc)?.1;

        // If no logical file specified, use the physical filename
        let filename = logical_file.or_else(|| file_info.path.to_str());

        Some((logical_line, column, filename))
    }
}


impl Default for SourceManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests_source_manager;
