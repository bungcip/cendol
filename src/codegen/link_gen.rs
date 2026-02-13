//! Linking executable/library from object files.
//!
//! This module provides functionality for linking compiled object files
//! into final executables or libraries using an external linker (clang).

use std::path::{Path, PathBuf};
use std::process::Command;

/// Configuration for the linker.
#[derive(Debug, Clone, Default)]
pub(crate) struct LinkConfig {
    /// Output file path
    pub output_path: PathBuf,
    /// Library search paths (-L)
    pub library_paths: Vec<PathBuf>,
    /// Libraries to link (-l)
    pub libraries: Vec<String>,
    /// Optimization level (e.g., "0", "1", "2", "3", "s")
    pub optimization: Option<String>,
    /// Include debug info (-g)
    pub debug_info: bool,
    /// Verbose output
    pub verbose: bool,
    /// Use a specific linker
    pub fuse_ld: Option<String>,
}

/// Error type for linking operations.
#[derive(Debug)]
pub(crate) enum LinkError {
    /// IO error during linking
    IoError(String),
    /// Linker returned non-zero exit code
    LinkFailed,
}

impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LinkError::IoError(msg) => write!(f, "IO error: {}", msg),
            LinkError::LinkFailed => write!(f, "Linking failed"),
        }
    }
}

impl std::error::Error for LinkError {}

/// Links object files into an executable or library.
pub(crate) struct LinkGen;

impl LinkGen {
    /// Link object files into an executable using clang.
    ///
    /// # Arguments
    /// * `object_files` - Paths to object files to link
    /// * `config` - Linking configuration
    ///
    /// # Returns
    /// * `Ok(())` on success
    /// * `Err(LinkError)` on failure
    pub(crate) fn link<P: AsRef<Path>>(object_files: &[P], config: &LinkConfig) -> Result<(), LinkError> {
        if object_files.is_empty() {
            return Ok(());
        }

        let mut clang_cmd = Command::new("clang");

        // Add object files
        for obj in object_files {
            clang_cmd.arg(obj.as_ref());
        }

        // Add library paths
        for path in &config.library_paths {
            clang_cmd.arg("-L").arg(path);
        }

        // Add libraries
        for lib in &config.libraries {
            clang_cmd.arg(format!("-l{}", lib));
        }

        // Add optimization flags if present
        if let Some(opt) = &config.optimization {
            clang_cmd.arg(format!("-O{}", opt));
        }

        // Add debug info if requested
        if config.debug_info {
            clang_cmd.arg("-g");
        }

        if let Some(linker) = &config.fuse_ld {
            clang_cmd.arg(format!("-fuse-ld={}", linker));
        }

        // Default to linking math library
        if !config.libraries.contains(&"m".to_string()) {
            clang_cmd.arg("-lm");
        }

        // Suppress linker warnings about deprecated libc functions
        clang_cmd.arg("-Wl,-w");

        // Set output path
        clang_cmd.arg("-o").arg(&config.output_path);

        if config.verbose {
            println!("Executing linker: {:?}", clang_cmd);
        }

        let status = clang_cmd
            .status()
            .map_err(|e| LinkError::IoError(format!("Failed to execute clang for linking: {}", e)))?;

        if !status.success() {
            return Err(LinkError::LinkFailed);
        }

        // Set executable permissions on the output file (Unix only)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            if let Ok(metadata) = std::fs::metadata(&config.output_path) {
                let mut permissions = metadata.permissions();
                permissions.set_mode(0o755); // rwxr-xr-x
                if let Err(e) = std::fs::set_permissions(&config.output_path, permissions) {
                    eprintln!("Warning: Failed to set executable permissions: {}", e);
                }
            }
        }

        Ok(())
    }
}
