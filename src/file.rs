use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

/// A unique identifier for a file.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, serde::Serialize)]
pub struct FileId(pub u32);

/// Manages files, providing a centralized way to access and read them.
#[derive(Clone)]
pub struct FileManager {
    files: HashMap<FileId, PathBuf>,
    next_id: u32,
    include_paths: Vec<PathBuf>,
    stdin_content: Option<String>,
    stdin_path: PathBuf,
}

impl Default for FileManager {
    fn default() -> Self {
        Self::new()
    }
}

impl FileManager {
    /// Creates a new `FileManager`.
    pub fn new() -> Self {
        FileManager {
            files: HashMap::new(),
            next_id: 0,
            include_paths: Vec::new(),
            stdin_content: None,
            stdin_path: PathBuf::from("<stdin>"),
        }
    }

    /// Adds an include path to the `FileManager`.
    pub fn add_include_path(&mut self, path: &str) {
        self.include_paths.push(PathBuf::from(path));
    }

    /// Opens a file and returns its `FileId`.
    pub fn open(&mut self, path: &str) -> Result<FileId, std::io::Error> {
        if path == "<stdin>" {
            if self.stdin_content.is_none() {
                self.stdin_content = Some(std::io::read_to_string(std::io::stdin())?);
            }
            return Ok(FileId(u32::MAX));
        }
        let path_buf = PathBuf::from(path);
        let file_id = FileId(self.next_id);
        self.files.insert(file_id, path_buf);
        self.next_id += 1;
        Ok(file_id)
    }

    pub fn open_include(
        &mut self,
        path: &str,
        kind: crate::preprocessor::token::IncludeKind,
        includer: FileId,
    ) -> Result<FileId, std::io::Error> {
        let mut search_paths = Vec::new();

        if kind == crate::preprocessor::token::IncludeKind::Local
            && let Some(includer_path) = self.files.get(&includer)
            && let Some(parent) = includer_path.parent()
        {
            search_paths.push(parent.to_path_buf());
        }

        search_paths.extend(self.include_paths.clone());

        for search_path in &search_paths {
            let full_path = search_path.join(path);
            if full_path.exists() {
                let file_id = FileId(self.next_id);
                self.files.insert(file_id, full_path);
                self.next_id += 1;
                return Ok(file_id);
            }
        }

        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("File not found: {}", path),
        ))
    }

    /// Reads the content of a file given its `FileId`.
    pub fn read(&self, file_id: FileId) -> Result<String, std::io::Error> {
        if file_id.0 == u32::MAX {
            if let Some(content) = &self.stdin_content {
                Ok(content.clone())
            } else {
                Err(std::io::Error::new(
                    std::io::ErrorKind::NotFound,
                    "Stdin not available",
                ))
            }
        } else if let Some(path) = self.files.get(&file_id) {
            fs::read_to_string(path)
        } else {
            Err(std::io::Error::new(
                std::io::ErrorKind::NotFound,
                "File not found",
            ))
        }
    }

    /// Gets the path of a file given its `FileId`.
    pub fn get_path(&self, file_id: FileId) -> Option<&PathBuf> {
        if file_id.0 == u32::MAX {
            Some(&self.stdin_path)
        } else {
            self.files.get(&file_id)
        }
    }
}
