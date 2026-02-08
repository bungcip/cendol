use std::path::{Path, PathBuf};

/// Manages header search paths and include resolution
#[derive(Clone)]
pub(crate) struct HeaderSearch {
    pub(crate) system_path: Vec<PathBuf>,
    pub(crate) framework_path: Vec<PathBuf>,
    pub(crate) quoted_includes: Vec<String>,
    pub(crate) angled_includes: Vec<String>,
}

impl HeaderSearch {
    /// Add a system include path
    pub(crate) fn add_system_path(&mut self, path: PathBuf) {
        self.system_path.push(path);
    }

    /// Add a quoted include path (-iquote)
    pub(crate) fn add_quoted_path(&mut self, path: PathBuf) {
        self.quoted_includes.push(path.to_string_lossy().to_string());
    }

    /// Add an angled include path (-I)
    pub(crate) fn add_angled_path(&mut self, path: PathBuf) {
        self.angled_includes.push(path.to_string_lossy().to_string());
    }

    /// Add a framework path
    pub(crate) fn add_framework_path(&mut self, path: PathBuf) {
        self.framework_path.push(path);
    }

    /// Resolve an include path to an absolute path
    pub(crate) fn resolve_path(&self, include_path: &str, is_angled: bool, current_dir: &Path) -> Option<PathBuf> {
        if is_angled {
            // Angled includes: search angled_includes, then system_path, then framework_path
            self.check_paths(&self.angled_includes, include_path)
                .or_else(|| self.check_paths(&self.system_path, include_path))
                .or_else(|| self.check_paths(&self.framework_path, include_path))
        } else {
            // Quoted includes: search current_dir, then quoted_includes, then angled_includes, then system_path, then framework_path
            let candidate = current_dir.join(include_path);
            if candidate.exists() {
                return Some(candidate);
            }
            self.check_paths(&self.quoted_includes, include_path)
                .or_else(|| self.check_paths(&self.angled_includes, include_path))
                .or_else(|| self.check_paths(&self.system_path, include_path))
                .or_else(|| self.check_paths(&self.framework_path, include_path))
        }
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
        let mut found_current = false;

        if !is_angled {
            for path_str in &self.quoted_includes {
                let path: &Path = Path::new(path_str);
                if !found_current {
                    if current_dir.starts_with(path) {
                        found_current = true;
                        continue;
                    }
                }

                if found_current {
                    let candidate = path.join(include_path);
                    if candidate.exists() {
                        return Some(candidate);
                    }
                }
            }
        }

        for path_str in &self.angled_includes {
            let path: &Path = Path::new(path_str);
            if !found_current {
                if current_dir.starts_with(path) {
                    found_current = true;
                    continue;
                }
            }

            if found_current {
                let candidate = path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
        }

        for path in &self.system_path {
            if !found_current {
                if current_dir.starts_with(path) {
                    found_current = true;
                    continue;
                }
            }

            if found_current {
                let candidate = path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
        }

        for path in &self.framework_path {
            if !found_current {
                if current_dir.starts_with(path) {
                    found_current = true;
                    continue;
                }
            }

            if found_current {
                let candidate = path.join(include_path);
                if candidate.exists() {
                    return Some(candidate);
                }
            }
        }

        None
    }
}
