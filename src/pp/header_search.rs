use rustc_hash::FxHashMap;
use std::cell::RefCell;
use std::path::{Path, PathBuf};

/// Manages header search paths and include resolution
#[derive(Clone)]
pub(crate) struct HeaderSearch {
    pub(crate) system_path: Vec<PathBuf>,
    pub(crate) framework_path: Vec<PathBuf>,
    pub(crate) quoted_includes: Vec<PathBuf>,
    pub(crate) angled_includes: Vec<PathBuf>,
    /// Cache for resolved paths: (include_path, is_angled, current_dir) -> resolved_path
    pub(crate) resolve_cache: RefCell<FxHashMap<(String, bool, PathBuf), Option<PathBuf>>>,
    /// Cache for resolved next paths: (include_path, is_angled, current_dir) -> resolved_path
    pub(crate) resolve_next_cache: RefCell<FxHashMap<(String, bool, PathBuf), Option<PathBuf>>>,
}

impl HeaderSearch {
    pub(crate) fn new() -> Self {
        HeaderSearch {
            system_path: Vec::new(),
            framework_path: Vec::new(),
            quoted_includes: Vec::new(),
            angled_includes: Vec::new(),
            resolve_cache: RefCell::new(FxHashMap::default()),
            resolve_next_cache: RefCell::new(FxHashMap::default()),
        }
    }

    /// Add a system include path
    pub(crate) fn add_system_path(&mut self, path: PathBuf) {
        self.system_path.push(path);
    }

    /// Add a quoted include path (-iquote)
    pub(crate) fn add_quoted_path(&mut self, path: PathBuf) {
        self.quoted_includes.push(path);
    }

    /// Add an angled include path (-I)
    pub(crate) fn add_angled_path(&mut self, path: PathBuf) {
        self.angled_includes.push(path);
    }

    /// Add a framework path
    pub(crate) fn add_framework_path(&mut self, path: PathBuf) {
        self.framework_path.push(path);
    }

    /// Resolve an include path to an absolute path
    pub(crate) fn resolve_path(&self, include_path: &str, is_angled: bool, current_dir: &Path) -> Option<PathBuf> {
        let key = (include_path.to_string(), is_angled, current_dir.to_path_buf());
        if let Some(cached) = self.resolve_cache.borrow().get(&key) {
            return cached.clone();
        }

        let result = if is_angled {
            // Angled includes: search angled_includes, then system_path, then framework_path
            self.check_paths(&self.angled_includes, include_path)
                .or_else(|| self.check_paths(&self.system_path, include_path))
                .or_else(|| self.check_paths(&self.framework_path, include_path))
        } else {
            // Quoted includes: search current_dir, then quoted_includes, then angled_includes, then system_path, then framework_path
            let candidate = current_dir.join(include_path);
            if candidate.exists() {
                Some(candidate)
            } else {
                self.check_paths(&self.quoted_includes, include_path)
                    .or_else(|| self.check_paths(&self.angled_includes, include_path))
                    .or_else(|| self.check_paths(&self.system_path, include_path))
                    .or_else(|| self.check_paths(&self.framework_path, include_path))
            }
        };

        self.resolve_cache.borrow_mut().insert(key, result.clone());
        result
    }

    /// Helper to check a list of paths for an include file
    fn check_paths<P: AsRef<Path>>(&self, paths: &[P], include_path: &str) -> Option<PathBuf> {
        for path in paths {
            let candidate = path.as_ref().join(include_path);
            if candidate.exists() {
                return Some(candidate);
            }
        }
        None
    }

    /// Resolve an include path for #include_next, skipping the search path valid for current_dir
    pub(crate) fn resolve_next_path(&self, include_path: &str, is_angled: bool, current_dir: &Path) -> Option<PathBuf> {
        let key = (include_path.to_string(), is_angled, current_dir.to_path_buf());
        if let Some(cached) = self.resolve_next_cache.borrow().get(&key) {
            return cached.clone();
        }

        let mut found_current = false;

        let paths_to_search: &[&[PathBuf]] = if !is_angled {
            &[
                &self.quoted_includes,
                &self.angled_includes,
                &self.system_path,
                &self.framework_path,
            ]
        } else {
            &[&self.angled_includes, &self.system_path, &self.framework_path]
        };

        let mut result = None;
        'outer: for path_list in paths_to_search {
            for path in *path_list {
                if !found_current && current_dir.starts_with(path) {
                    found_current = true;
                    continue;
                }

                if found_current {
                    let candidate = path.join(include_path);
                    if candidate.exists() {
                        result = Some(candidate);
                        break 'outer;
                    }
                }
            }
        }

        self.resolve_next_cache.borrow_mut().insert(key, result.clone());
        result
    }
}
