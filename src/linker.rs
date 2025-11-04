//! This module is responsible for linking the compiled object file.
//! It will search for a linker in the system and use it to link the object file.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

/// Link the given object file to an executable.
///
/// This function will search for a linker in the system and use it to link the object file.
/// It will also link against the C standard library.
///
/// # Arguments
///
/// * `object_filename` - The name of the object file to link.
/// * `output_filename` - The name of the executable to create.
/// * `working_dir` - The directory to run the linker in.
///
/// # Returns
///
/// A `Result` with the `ExitStatus` of the linker, or a `String` with an error message.
pub fn link(
    object_filename: &str,
    output_filename: &str,
    working_dir: &Path,
) -> Result<ExitStatus, String> {
    let linker = find_linker().ok_or("No linker found")?;
    let (crt1, crti, crtn, ld_linux) = find_crt_files()?;
    let mut command = Command::new(&linker);
    command
        .current_dir(working_dir)
        .arg("-dynamic-linker")
        .arg(ld_linux)
        .arg(crt1)
        .arg(crti)
        .arg(object_filename)
        .arg("-lc")
        .arg("-o")
        .arg(output_filename)
        .arg(crtn);

    command
        .status()
        .map_err(|e| format!("Failed to execute linker: {}", e))
}

/// Searches for an available linker in the system.
///
/// The linkers are searched in the following order:
/// 1. wild
/// 2. mold
/// 3. gold
/// 4. ld
///
/// # Returns
///
/// An `Option` with the name of the found linker, or `None` if no linker is found.
pub fn find_linker() -> Option<String> {
    for linker in &["wild", "mold", "gold", "ld"] {
        if is_in_path(linker) {
            return Some(linker.to_string());
        }
    }
    None
}

/// Finds the necessary CRT files for linking.
///
/// # Returns
///
/// A `Result` with a tuple of the paths to the CRT files, or a `String` with an error message.
fn find_crt_files() -> Result<(PathBuf, PathBuf, PathBuf, PathBuf), String> {
    let search_paths = [
        "/usr/lib/x86_64-linux-gnu",
        "/usr/lib64",
        "/lib/x86_64-linux-gnu",
        "/lib64",
    ];

    let crt1 = find_file("crt1.o", &search_paths).ok_or("crt1.o not found")?;
    let crti = find_file("crti.o", &search_paths).ok_or("crti.o not found")?;
    let crtn = find_file("crtn.o", &search_paths).ok_or("crtn.o not found")?;
    let ld_linux = find_file("ld-linux-x86-64.so.2", &search_paths)
        .ok_or("ld-linux-x86-64.so.2 not found")?;

    Ok((crt1, crti, crtn, ld_linux))
}

/// Finds a file in a list of directories.
///
/// # Arguments
///
/// * `filename` - The name of the file to find.
/// * `search_paths` - A list of directories to search in.
///
/// # Returns
///
/// An `Option` with the `PathBuf` of the found file, or `None` if the file is not found.
fn find_file(filename: &str, search_paths: &[&str]) -> Option<PathBuf> {
    for path in search_paths {
        let pb = PathBuf::from(path).join(filename);
        if pb.exists() {
            return Some(pb);
        }
    }
    None
}

/// Checks if a program is in the system's PATH.
fn is_in_path(program: &str) -> bool {
    if let Ok(path) = std::env::var("PATH") {
        for p in path.split(':') {
            let p_str = format!("{}/{}", p, program);
            if std::fs::metadata(p_str).is_ok() {
                return true;
            }
        }
    }
    false
}
