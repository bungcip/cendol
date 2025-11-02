use crate::preprocessor::token::IncludeKind;
pub use crate::source::{FileId, SourceFile, SourceMap};
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::Path;
use std::path::PathBuf;

/// Handles file loading and lookup.
#[derive(Clone)]
pub struct FileManager {
    files: HashMap<FileId, PathBuf>,
    path_to_id: HashMap<PathBuf, FileId>,
    next_id: u32,
    include_paths: Vec<PathBuf>,
    stdin_content: Option<String>,
    stdin_path: PathBuf,
    pub source_map: SourceMap,
}

impl Default for FileManager {
    fn default() -> Self {
        Self::new()
    }
}

impl FileManager {
    pub fn new() -> Self {
        FileManager {
            files: HashMap::new(),
            path_to_id: HashMap::new(),
            next_id: 0,
            include_paths: Vec::new(),
            stdin_content: None,
            stdin_path: PathBuf::from("<stdin>"),
            source_map: SourceMap::default(),
        }
    }

    pub fn add_include_path(&mut self, path: &str) {
        self.include_paths.push(PathBuf::from(path));
    }

    /// Opens a file (or stdin) and registers it in the SourceMap.
    pub fn open(&mut self, path: &str) -> Result<FileId, io::Error> {
        if path == "<stdin>" {
            if self.stdin_content.is_none() {
                self.stdin_content = Some(std::io::read_to_string(std::io::stdin())?);
            }
            let file_id = FileId(u32::MAX);
            if self.source_map.get(file_id).is_none() {
                let content = self.stdin_content.clone().unwrap_or_default();
                let src_file = SourceFile::new(file_id, PathBuf::from("<stdin>"), content);
                self.source_map.insert(src_file);
            }
            return Ok(file_id);
        }

        if path == "<cmdline>" {
            let file_id = FileId(self.next_id);
            self.next_id = self.next_id.checked_add(1).expect("ran out of file ids");
            let path_buf = PathBuf::from("<cmdline>");
            self.files.insert(file_id, path_buf.clone());
            self.path_to_id.insert(path_buf.clone(), file_id);
            let src_file = SourceFile::new(file_id, path_buf, "".to_string());
            self.source_map.insert(src_file);
            return Ok(file_id);
        }

        let canonical = fs::canonicalize(PathBuf::from(path))?;
        if let Some(&existing_id) = self.path_to_id.get(&canonical) {
            return Ok(existing_id);
        }

        let content = fs::read_to_string(&canonical)?;
        let file_id = FileId(self.next_id);
        self.next_id = self.next_id.checked_add(1).expect("ran out of file ids");

        self.files.insert(file_id, canonical.clone());
        self.path_to_id.insert(canonical.clone(), file_id);
        let src_file = SourceFile::new(file_id, canonical, content);
        self.source_map.insert(src_file);
        Ok(file_id)
    }

    /// Registers a file with provided content without reading from disk.
    pub fn register_file(&mut self, path: &str, content: &str) -> Result<FileId, io::Error> {
        if path == "<stdin>" {
            let file_id = FileId(u32::MAX);
            if self.source_map.get(file_id).is_none() {
                let src_file =
                    SourceFile::new(file_id, PathBuf::from("<stdin>"), content.to_string());
                self.source_map.insert(src_file);
            }
            return Ok(file_id);
        }

        if path == "<cmdline>" {
            let file_id = FileId(self.next_id);
            self.next_id = self.next_id.checked_add(1).expect("ran out of file ids");
            let path_buf = PathBuf::from("<cmdline>");
            self.files.insert(file_id, path_buf.clone());
            self.path_to_id.insert(path_buf.clone(), file_id);
            let src_file = SourceFile::new(file_id, path_buf, content.to_string());
            self.source_map.insert(src_file);
            return Ok(file_id);
        }

        let path_buf = PathBuf::from(path);
        let canonical = if path_buf.exists() {
            fs::canonicalize(&path_buf)?
        } else {
            path_buf
        };

        if let Some(&existing_id) = self.path_to_id.get(&canonical) {
            return Ok(existing_id);
        }

        let file_id = FileId(self.next_id);
        self.next_id = self.next_id.checked_add(1).expect("ran out of file ids");

        self.files.insert(file_id, canonical.clone());
        self.path_to_id.insert(canonical.clone(), file_id);
        let src_file = SourceFile::new(file_id, canonical, content.to_string());
        self.source_map.insert(src_file);
        Ok(file_id)
    }

    /// Opens an include file with include path resolution and deduplication.
    pub fn open_include(
        &mut self,
        path: &str,
        kind: IncludeKind,
        includer: FileId,
    ) -> Result<FileId, io::Error> {
        // Build search paths:
        let mut search_paths: Vec<PathBuf> = Vec::new();

        if kind == IncludeKind::Local
            && includer.0 != u32::MAX
            && let Some(includer_path) = self.files.get(&includer)
            && let Some(parent) = includer_path.parent()
        {
            search_paths.push(parent.to_path_buf());
        }

        search_paths.extend(self.include_paths.clone());

        for base in &search_paths {
            let full = base.join(path);
            if full.exists() && full.is_file() {
                let canonical = fs::canonicalize(&full)?;
                if let Some(&existing_id) = self.path_to_id.get(&canonical) {
                    return Ok(existing_id);
                }

                let content = fs::read_to_string(&canonical)?;
                let file_id = FileId(self.next_id);
                self.next_id = self.next_id.checked_add(1).expect("ran out of file ids");

                self.files.insert(file_id, canonical.clone());
                self.path_to_id.insert(canonical.clone(), file_id);
                let src_file = SourceFile::new(file_id, canonical, content);
                self.source_map.insert(src_file);
                return Ok(file_id);
            }
        }

        // Try direct path as fallback
        let direct = PathBuf::from(path);
        if direct.exists() && direct.is_file() {
            let canonical = fs::canonicalize(&direct)?;
            if let Some(&existing_id) = self.path_to_id.get(&canonical) {
                return Ok(existing_id);
            }

            let content = fs::read_to_string(&canonical)?;
            let file_id = FileId(self.next_id);
            self.next_id = self.next_id.checked_add(1).expect("ran out of file ids");

            self.files.insert(file_id, canonical.clone());
            self.path_to_id.insert(canonical.clone(), file_id);
            let src_file = SourceFile::new(file_id, canonical, content);
            self.source_map.insert(src_file);
            return Ok(file_id);
        }

        Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!("Included file not found: {}", path),
        ))
    }

    /// Read file content via SourceMap.
    pub fn read(&self, file_id: FileId) -> Option<&str> {
        self.source_map.get(file_id).map(|f| f.content.as_str())
    }

    /// Get path of a file id (or "<stdin>" for stdin)
    pub fn get_path(&self, file_id: FileId) -> Option<&PathBuf> {
        if file_id.0 == u32::MAX {
            Some(&self.stdin_path)
        } else {
            self.files.get(&file_id)
        }
    }

    /// get filename from file_id as path, panic if file_id not exists
    pub fn get_filename(&self, file_id: FileId) -> &Path {
        let path = self.get_path(file_id);
        match path {
            Some(path) => path.as_path(),
            None => panic!("file_id({file_id}) not exists"),
        }
    }

}
