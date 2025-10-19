use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

/// A unique identifier for a file.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct FileId(pub u32);

/// Manages files, providing a centralized way to access and read them.
pub struct FileManager {
    files: HashMap<FileId, PathBuf>,
    next_id: u32,
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
        }
    }

    /// Opens a file and returns its `FileId`.
    pub fn open(&mut self, path: &str) -> Result<FileId, std::io::Error> {
        let path_buf = PathBuf::from(path);
        let file_id = FileId(self.next_id);
        self.files.insert(file_id, path_buf);
        self.next_id += 1;
        Ok(file_id)
    }

    /// Reads the content of a file given its `FileId`.
    pub fn read(&self, file_id: FileId) -> Result<String, std::io::Error> {
        if let Some(path) = self.files.get(&file_id) {
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
        self.files.get(&file_id)
    }
}
