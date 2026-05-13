use hashbrown::HashMap;
use serde::Serialize;
use std::sync::Arc;
use std::{
    cmp::Ordering,
    num::NonZeroU32,
    path::{Path, PathBuf},
};

/// Source ID for identifying source files
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct SourceId(pub(crate) NonZeroU32);

impl std::fmt::Display for SourceId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SourceId({})", self.0)
    }
}

impl SourceId {
    /// create a new SourceId from a u32. panics if id is zero.
    pub(crate) fn new(id: u32) -> Self {
        SourceId(NonZeroU32::new(id).expect("SourceId must be non-zero"))
    }

    fn to_u32(self) -> u32 {
        self.0.get()
    }
}

/// Source ID and byte offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct SourceLoc {
    pub(crate) source_id: SourceId,
    pub(crate) offset: u32,
}

impl Default for SourceLoc {
    fn default() -> Self {
        Self::builtin()
    }
}

impl SourceLoc {
    pub(crate) fn new(source_id: SourceId, offset: u32) -> Self {
        SourceLoc { source_id, offset }
    }

    /// built-in source location (SourceId = 1, offset = 0)
    pub(crate) fn builtin() -> Self {
        SourceLoc::new(SourceId::new(1), 0)
    }

    pub(crate) fn source_id(&self) -> SourceId {
        self.source_id
    }

    pub(crate) fn offset(&self) -> u32 {
        self.offset
    }
}

impl std::fmt::Display for SourceLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "SourceLoc(source_id={}, offset={})", self.source_id, self.offset)
    }
}

/// Represents a range in the source file.
/// Packed representation (64 bits total):
/// - Bits 0-23: Offset (24 bits) - Max 16 MiB
/// - Bits 24-39: Length (16 bits) - Max 64 KiB
/// - Bits 40-63: SourceId (24 bits) - Max ~16M files
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize)]
pub struct SourceSpan(u64);

impl Default for SourceSpan {
    fn default() -> Self {
        Self::empty()
    }
}

impl SourceSpan {
    const OFFSET_BITS: u64 = 24;
    const LENGTH_BITS: u64 = 16;
    const SOURCE_ID_BITS: u64 = 24;

    const OFFSET_MASK: u64 = (1 << Self::OFFSET_BITS) - 1;
    const LENGTH_MASK: u64 = (1 << Self::LENGTH_BITS) - 1;
    const SOURCE_ID_MASK: u64 = (1 << Self::SOURCE_ID_BITS) - 1;

    const LENGTH_SHIFT: u64 = Self::OFFSET_BITS;
    const SOURCE_ID_SHIFT: u64 = Self::OFFSET_BITS + Self::LENGTH_BITS;

    const MAX_OFFSET: u32 = Self::OFFSET_MASK as u32;
    const MAX_LENGTH: u32 = Self::LENGTH_MASK as u32;
    const MAX_SOURCE_ID: u32 = Self::SOURCE_ID_MASK as u32;

    pub(crate) fn new(start: SourceLoc, end: SourceLoc) -> Self {
        if start.source_id != end.source_id {
            // Panic removed: When start and end are in different files (e.g. usage of macro vs macro expansion),
            // we cannot represent the span correctly in our packed format.
            // Gracefully degrade to a zero-length span at the start location.
            return Self::new_with_length(start.source_id, start.offset, 0);
        }

        let length = end.offset.saturating_sub(start.offset);
        Self::new_with_length(start.source_id, start.offset, length)
    }

    pub(crate) fn new_with_length(source_id: SourceId, offset: u32, length: u32) -> Self {
        let id = source_id.to_u32();
        assert!(id <= Self::MAX_SOURCE_ID, "SourceId exceeds 24-bit limit: {}", id);
        assert!(
            offset <= Self::MAX_OFFSET,
            "SourceSpan offset exceeds 16 MiB limit: {}",
            offset
        );

        let len = length.min(Self::MAX_LENGTH);

        Self((offset as u64) | ((len as u64) << Self::LENGTH_SHIFT) | ((id as u64) << Self::SOURCE_ID_SHIFT))
    }

    pub(crate) fn empty() -> Self {
        Self::new(SourceLoc::builtin(), SourceLoc::builtin())
    }

    pub(crate) fn from_loc(loc: SourceLoc) -> Self {
        Self::new(loc, loc)
    }

    pub(crate) fn start(&self) -> SourceLoc {
        let offset = (self.0 & Self::OFFSET_MASK) as u32;
        SourceLoc {
            source_id: self.source_id(),
            offset,
        }
    }

    pub(crate) fn end(&self) -> SourceLoc {
        let offset = (self.0 & Self::OFFSET_MASK) as u32;
        let length = ((self.0 >> Self::LENGTH_SHIFT) & Self::LENGTH_MASK) as u32;
        SourceLoc {
            source_id: self.source_id(),
            offset: offset + length,
        }
    }

    pub(crate) fn source_id(&self) -> SourceId {
        let id = ((self.0 >> Self::SOURCE_ID_SHIFT) & Self::SOURCE_ID_MASK) as u32;
        SourceId::new(id)
    }

    pub(crate) fn is_source_id_builtin(&self) -> bool {
        self.source_id().to_u32() == 1
    }

    /// Merge two source spans into a single span covering both
    pub(crate) fn merge(self, other: SourceSpan) -> SourceSpan {
        let id1 = self.source_id();
        let id2 = other.source_id();

        if id1 != id2 {
            return self;
        }

        let start1 = self.start().offset;
        let end1 = self.end().offset;
        let start2 = other.start().offset;
        let end2 = other.end().offset;

        let min_start = start1.min(start2);
        let max_end = end1.max(end2);

        let start_loc = SourceLoc::new(id1, min_start);
        let end_loc = SourceLoc::new(id1, max_end);

        Self::new(start_loc, end_loc)
    }
}

impl std::fmt::Display for SourceSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SourceSpan(source_id={}, start={}, end={})",
            self.source_id(),
            self.start().offset,
            self.end().offset
        )
    }
}

/// Represents a single #line directive entry
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LineDirective {
    pub(crate) physical_line: u32,
    pub(crate) logical_line: u32,
    pub(crate) logical_file: Option<String>,
}

impl LineDirective {
    pub(crate) fn new(physical_line: u32, logical_line: u32, logical_file: Option<String>) -> Self {
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

/// Indicates the kind of source file
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum FileKind {
    /// A real file on disk
    Real,
    /// A built-in header (e.g. stddef.h)
    Builtin,
    /// Synthetic content (command line defines, magic macros, etc)
    Synthetic,
    /// A virtual buffer for macro expansion or pasted tokens
    MacroExpansion,
}

/// Stores all #line directives for a single file, sorted by physical line
#[derive(Debug, Clone, Default)]
pub struct LineMap {
    pub(crate) entries: Vec<LineDirective>,
}

impl LineMap {
    pub(crate) fn new() -> Self {
        LineMap { entries: Vec::new() }
    }

    /// Add a line directive entry. Must be added in sorted order by physical_line.
    pub(crate) fn add_entry(&mut self, entry: LineDirective) {
        // Ensure monotonic addition
        if let Some(last) = self.entries.last() {
            assert!(
                entry.physical_line >= last.physical_line,
                "Line directives must be added in sorted order"
            );
        }
        self.entries.push(entry);
    }

    /// Find the presumed location for a given physical line
    pub(crate) fn presumed_location(&self, physical_line: u32) -> (u32, Option<&str>) {
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
}

/// File information for tracking source files
#[derive(Debug)]
pub struct FileInfo {
    pub(crate) path: PathBuf,
    pub(crate) buffer: Arc<[u8]>,
    pub(crate) cached_string: std::sync::OnceLock<String>,
    pub(crate) kind: FileKind,
    pub line_starts: Vec<u32>,          // Line start offsets for efficient line lookup
    pub line_map: LineMap,              // #line directive mappings
    pub include_loc: Option<SourceLoc>, // Location where this file was included/expanded from
}

/// Manages source files and locations
/// File size limit: 4 MiB per file (22-bit offset in SourceLoc)
/// Maximum files: 1023 unique source files (10-bit file ID in SourceLoc)
pub struct SourceManager {
    file_infos: Vec<FileInfo>,
    path_to_id: HashMap<PathBuf, SourceId>,
}

impl Default for SourceManager {
    fn default() -> Self {
        Self {
            file_infos: Vec::new(),
            path_to_id: HashMap::new(),
        }
    }
}

impl SourceManager {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Add a file to the source manager from a file path
    /// Since we only support UTF-8, we can read directly as bytes and assume validity
    pub(crate) fn add_file(
        &mut self,
        path: &std::path::Path,
        include_loc: Option<SourceLoc>,
    ) -> Result<SourceId, std::io::Error> {
        // Bolt ⚡: First check cache with the raw path to avoid expensive canonicalize() syscall.
        if let Some(id) = self.path_to_id.get(path) {
            return Ok(*id);
        }

        // Bolt ⚡: Canonicalize path to deduplicate files reached via different paths.
        // This avoids redundant disk I/O, memory allocations, and SIMD calculations.
        // It also correctly implements #pragma once for the same physical file.
        let canonical = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());

        if let Some(&id) = self.path_to_id.get(&canonical) {
            self.path_to_id.insert(path.to_path_buf(), id);
            return Ok(id);
        }

        let buffer = std::fs::read(&canonical)?;
        let id = self.add_buffer(buffer, canonical, include_loc, FileKind::Real);

        // Also map the original input path to this ID if it was different.
        self.path_to_id.insert(path.to_path_buf(), id);

        Ok(id)
    }

    /// Add a buffer to the source manager with raw bytes (UTF-8 assumed)
    pub(crate) fn add_buffer(
        &mut self,
        buffer: Vec<u8>,
        path: impl Into<PathBuf>,
        include_loc: Option<SourceLoc>,
        kind: FileKind,
    ) -> SourceId {
        let path = path.into();

        // Bolt ⚡: Ensure line starts are always computed upon file addition.
        // This centralizes line tracking and avoids redundant $O(N)$ scans later.
        let line_starts = if kind == FileKind::MacroExpansion {
            // Macro expansions are usually treated as single lines for diagnostic purposes
            vec![0]
        } else {
            compute_line_starts(&buffer)
        };

        let file_id = SourceId::new(self.file_infos.len() as u32 + 2);
        if kind == FileKind::Real || kind == FileKind::Builtin {
            // Only map path for real files and built-in headers.
            // This avoids unnecessary map insertions for short-lived virtual buffers.
            self.path_to_id.insert(path.clone(), file_id);
        }

        let file_info = FileInfo {
            path,
            buffer: Arc::from(buffer),
            cached_string: std::sync::OnceLock::new(),
            kind,
            line_starts,
            line_map: LineMap::new(),
            include_loc,
        };

        self.file_infos.push(file_info);

        file_id
    }

    /// Get the buffer for a given source ID
    /// Since SourceId is always valid (we panic if not found), we can use indexing
    /// use get_source_text to get &str from SourceSpan instead if you need text
    pub(crate) fn get_buffer(&self, source_id: SourceId) -> &[u8] {
        &self
            .get_file_info(source_id)
            .unwrap_or_else(|| panic!("invalid source_id {source_id}"))
            .buffer[..]
    }

    /// Get the buffer for a given source ID, returning None if not found
    pub(crate) fn get_buffer_safe(&self, source_id: SourceId) -> Option<&[u8]> {
        self.get_file_info(source_id).map(|info| &info.buffer[..])
    }

    /// Get the buffer as an Arc for a given source ID.
    /// This allows shared ownership without cloning the entire buffer.
    pub(crate) fn get_buffer_arc(&self, source_id: SourceId) -> Arc<[u8]> {
        self.get_file_info(source_id)
            .unwrap_or_else(|| panic!("invalid source_id {source_id}"))
            .buffer
            .clone()
    }

    /// Get file info for a given source ID
    pub(crate) fn get_file_info(&self, source_id: SourceId) -> Option<&FileInfo> {
        self.file_infos.get(source_id.to_u32().checked_sub(2)? as usize)
    }

    /// Get source ID for a given file path
    pub(crate) fn get_file_id(&self, path: &str) -> Option<SourceId> {
        self.path_to_id.get(Path::new(path)).copied()
    }

    /// Get the source string for a given source ID, with caching
    pub(crate) fn get_source_str(&self, source_id: SourceId) -> &str {
        if let Some(info) = self.get_file_info(source_id) {
            info.cached_string.get_or_init(|| {
                // If the buffer is not valid UTF-8, we just use an empty string or lossy conversion
                // Standard C files should be valid UTF-8/ASCII for the most part.
                String::from_utf8_lossy(&info.buffer).into_owned()
            })
        } else {
            ""
        }
    }

    /// Get a "window" of lines around a given offset.
    /// Returns (start_offset, end_offset, start_line_number)
    pub(crate) fn get_line_window(&self, source_id: SourceId, offset: u32, window: usize) -> (u32, u32, u32) {
        let Some(info) = self.get_file_info(source_id) else {
            return (0, 0, 1);
        };

        if info.line_starts.is_empty() {
            return (0, info.buffer.len() as u32, 1);
        }

        // Find current line index
        let current_line_idx = info
            .line_starts
            .partition_point(|&start| start <= offset)
            .saturating_sub(1);

        let start_line_idx = current_line_idx.saturating_sub(window);
        let end_line_idx = (current_line_idx + window).min(info.line_starts.len() - 1);

        let start_offset = info.line_starts[start_line_idx];
        let end_offset = if end_line_idx + 1 < info.line_starts.len() {
            info.line_starts[end_line_idx + 1]
        } else {
            info.buffer.len() as u32
        };

        (start_offset, end_offset, start_line_idx as u32 + 1)
    }

    /// Get mutable access to the LineMap for a given source ID
    pub(crate) fn get_line_map_mut(&mut self, source_id: SourceId) -> Option<&mut LineMap> {
        self.file_infos
            .get_mut(source_id.to_u32().checked_sub(2)? as usize)
            .map(|fi| &mut fi.line_map)
    }

    /// Get the source text for a given span
    /// Since we only support UTF-8, we can assume the bytes are valid UTF-8
    #[cfg(test)]
    pub(crate) fn get_source_text(&self, span: SourceSpan) -> &str {
        let buffer = self.get_buffer(span.source_id());
        let start = span.start().offset() as usize;
        let end = span.end().offset() as usize;

        if start <= end && end <= buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&buffer[start..end]) }
        } else {
            panic!("Invalid span range");
        }
    }

    /// Get line and column for a source location
    pub(crate) fn get_line_column(&self, loc: SourceLoc) -> Option<(u32, u32)> {
        let file_info = self.get_file_info(loc.source_id())?;
        let offset = loc.offset();

        let line_starts = &file_info.line_starts;
        if line_starts.is_empty() {
            // If line_starts not calculated yet, assume single line starting at 0
            return Some((1, offset + 1));
        }

        // Use partition_point which performs a binary search
        let idx = line_starts.partition_point(|&start| start <= offset);

        if idx == 0 {
            return Some((0, 1));
        }

        // idx is the index of the first element GREATER than offset.
        // The line index corresponds to the element immediately preceding usage.
        let line_idx = idx - 1;
        let line_start = line_starts[line_idx];
        let column = offset - line_start;

        Some((line_idx as u32 + 1, column + 1)) // 1-based indexing
    }

    /// Get the presumed location (logical line and file) for a source location
    pub(crate) fn get_presumed_location(&self, loc: SourceLoc) -> Option<(u32, u32, Option<&str>)> {
        let file_info = self.get_file_info(loc.source_id())?;
        let (physical_line, column) = self.get_line_column(loc)?;

        let (logical_line, logical_file) = file_info.line_map.presumed_location(physical_line);

        // If no logical file specified, use the physical filename
        let filename = logical_file.or_else(|| file_info.path.to_str());

        Some((logical_line, column, filename))
    }
}

/// ⚡ Bolt: Optimized line start calculation using memchr.
fn compute_line_starts(buffer: &[u8]) -> Vec<u32> {
    // Two-pass approach using memchr is significantly faster than manual byte loops.
    // First pass counts newlines to pre-allocate exactly.
    let newline_count = memchr::memchr_iter(b'\n', buffer).count();
    let mut line_starts = Vec::with_capacity(newline_count + 1);
    line_starts.push(0);

    // Second pass populates the offsets.
    line_starts.extend(memchr::memchr_iter(b'\n', buffer).map(|pos| (pos + 1) as u32));
    line_starts
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let span = SourceSpan::empty();
        assert_eq!(span.start(), SourceLoc::builtin());
        assert_eq!(span.end(), SourceLoc::builtin());
        assert_eq!(span.source_id().to_u32(), 1);
    }

    #[test]
    fn test_builtin() {
        let span = SourceSpan::empty();
        assert!(span.is_source_id_builtin());

        let builtin = SourceLoc::builtin();
        let other = SourceLoc::new(SourceId::new(2), 0);

        let merged = SourceSpan::from_loc(builtin).merge(SourceSpan::from_loc(other));
        assert_eq!(
            merged,
            SourceSpan::empty(),
            "Merging spans from different source IDs should return the first span unchanged"
        );
    }

    #[test]
    fn test_source_manager_get_buffer_arc_invalid() {
        let sm = SourceManager::new();
        // ID 1 is builtin, so it should panic because it's less than 2
        let result = std::panic::catch_unwind(|| {
            sm.get_buffer_arc(SourceId::new(1));
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_sourceloc_default() {
        assert_eq!(SourceLoc::default(), SourceLoc::builtin());
    }

    #[test]
    fn test_sourcespan_display() {
        let span = SourceSpan::empty();
        assert_eq!(format!("{}", span), "SourceSpan(source_id=SourceId(1), start=0, end=0)");
    }
}
