//! CLI parsing and configuration module
//!
//! This module handles command-line argument parsing using clap and
//! provides configuration structures for the compiler driver.

use clap::{Args, Parser as CliParser};
use std::path::PathBuf;
use target_lexicon::Triple;

use crate::{
    driver::artifact::CompilePhase,
    lang_options::{CStandard, LangFlags, LangOptions},
};

/// CLI interface using clap
#[derive(CliParser, Debug)]
#[clap(name = "cendol", about = "C11 Compiler written in Rust", allow_hyphen_values = true)]
pub struct Cli {
    /// Input C source files
    #[clap(value_parser, required = true)]
    pub input_files: Vec<PathBuf>,

    /// Output file for AST dump
    #[clap(short, long, value_name = "FILE")]
    pub output: Option<PathBuf>,

    /// Enable verbose diagnostic output
    #[clap(short, long)]
    pub verbose: bool,

    /// Dump AST after parser phase
    #[clap(long)]
    pub dump_ast_after_parser: bool,

    /// Dump AST after semantic lowering phase
    #[clap(long)]
    pub dump_ast_after_semantic_lowering: bool,

    /// Dump MIR (Mid-level Intermediate Representation) to console
    #[clap(long)]
    pub dump_mir: bool,

    /// Dump Cranelift IR (Intermediate Representation) to console
    #[clap(long)]
    pub dump_cranelift: bool,

    /// Preprocess only, output preprocessed source to stdout
    #[clap(short = 'E')]
    pub preprocess_only: bool,

    /// Preprocessor options
    #[clap(flatten)]
    pub preprocessor: PreprocessorOptions,

    /// Suppress line markers in preprocessor output
    #[clap(short = 'P')]
    pub suppress_line_markers: bool,

    /// Retain comments in preprocessor output
    #[clap(short = 'C', long = "retain-comments")]
    pub retain_comments: bool,

    /// Include search paths
    #[clap(short = 'I', long = "include-path", value_name = "DIR", action = clap::ArgAction::Append)]
    pub include_paths: Vec<PathBuf>,

    /// Preprocessor macro definitions
    #[clap(short = 'D', long = "define", value_name = "NAME[=VALUE]", action = clap::ArgAction::Append)]
    pub defines: Vec<String>,

    /// Compiler warnings
    #[clap(short = 'W', action = clap::ArgAction::Append)]
    pub warnings: Vec<String>,

    /// Enable all warnings
    #[clap(long = "Wall")]
    pub wall: bool,

    /// Set C language standard (e.g., c99, c11)
    #[clap(long = "std", value_name = "STANDARD")]
    pub c_standard: Option<CStandard>,

    /// Target triple (e.g. x86_64-unknown-linux-gnu)
    #[clap(long = "target", value_name = "TRIPLE")]
    pub target: Option<String>,
}

#[derive(Args, Debug)]
pub struct PreprocessorOptions {
    /// Maximum include depth
    #[clap(long, default_value = "100")]
    pub max_include_depth: usize,
}

/// input file can be path to file or string buffer pair (filename, buffer)
#[derive(Debug, Clone)]
pub enum PathOrBuffer {
    Path(PathBuf),
    Buffer(String, Vec<u8>),
}

/// Configuration for compilation
#[derive(Debug)]
pub struct CompileConfig {
    pub input_files: Vec<PathOrBuffer>,
    pub output_path: Option<PathBuf>,
    pub stop_after: CompilePhase,

    pub verbose: bool,
    pub preprocessor: crate::pp::PPConfig,
    pub suppress_line_markers: bool,
    pub include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
    pub warnings: Vec<String>,
    pub lang_options: LangOptions,
    pub target: Triple,
}

impl Default for CompileConfig {
    fn default() -> Self {
        Self {
            input_files: Vec::new(),
            output_path: None,
            stop_after: CompilePhase::EmitObject,
            verbose: false,
            preprocessor: crate::pp::PPConfig::default(),
            suppress_line_markers: false,
            include_paths: Vec::new(),
            defines: Vec::new(),
            warnings: Vec::new(),
            lang_options: LangOptions::default(),
            target: Triple::host(),
        }
    }
}

impl CompileConfig {
    /// Create a new CompileConfig from a string of source code
    /// it used by tests infrastructure
    #[cfg(test)]
    pub(crate) fn from_virtual_file(source: String, stop_after: CompilePhase) -> Self {
        let filename = "example.c";
        let source = source.into_bytes();

        Self {
            input_files: vec![PathOrBuffer::Buffer(filename.to_string(), source)],
            stop_after,
            target: Triple::host(),
            ..Default::default()
        }
    }
}

impl Cli {
    /// Validate input files and check for option-like filenames
    fn validate_input_files(&self) -> Result<(), String> {
        for input_file in &self.input_files {
            let file_name = input_file.to_string_lossy();
            if file_name.starts_with('-') {
                return Err(format!("File '{}' not found: No such file or directory", file_name)
                    + "\n"
                    + "If this is meant to be a command-line option, place it before the filename.\n"
                    + &format!(
                        "Example: {} -o output_file",
                        std::env::args().next().unwrap_or("cendol".to_string())
                    ));
            }
        }
        Ok(())
    }

    /// Convert CLI arguments into compilation configuration
    pub fn into_config(self) -> Result<CompileConfig, String> {
        // Validate input files first
        self.validate_input_files()?;

        // Parse defines
        let defines = self
            .defines
            .iter()
            .map(|def| {
                if let Some(eq_pos) = def.find('=') {
                    let name = def[..eq_pos].to_string();
                    let value = Some(def[eq_pos + 1..].to_string());
                    (name, value)
                } else {
                    (def.clone(), None)
                }
            })
            .collect();

        // Handle -Wall flag by adding "all" to warnings if -Wall is specified
        let mut warnings = self.warnings;
        if self.wall {
            warnings.push("all".to_string());
        }

        // Build language options
        let flags = LangFlags::empty();

        let lang_options = LangOptions {
            flags,
            c_standard: self.c_standard,
        };

        // Build preprocessor configuration with include paths
        let mut system_include_paths = Vec::new();

        // Add user-specified include paths as system include paths
        for path in &self.include_paths {
            system_include_paths.push(path.clone());
        }

        // Add default system include paths
        system_include_paths.push(PathBuf::from("/usr/include"));

        // Add architecture-specific include paths
        let arch_paths = [
            "/usr/include/x86_64-linux-gnu",
            "/usr/include/x86_64-linux-gnu/c++/13",
            "/usr/include/c++/13",
        ];

        for arch_path in &arch_paths {
            let path = PathBuf::from(arch_path);
            if path.exists() {
                system_include_paths.push(path);
            }
        }

        let stop_after = if self.preprocess_only {
            CompilePhase::Preprocess
        } else if self.dump_ast_after_parser {
            CompilePhase::Parse
        } else if self.dump_ast_after_semantic_lowering {
            CompilePhase::SemanticLowering
        } else if self.dump_mir {
            CompilePhase::Mir
        } else if self.dump_cranelift {
            CompilePhase::Cranelift
        } else {
            CompilePhase::EmitObject
        };

        let target_triple = if let Some(t) = self.target {
            t.parse::<Triple>()
                .map_err(|e| format!("Invalid target triple: {}", e))?
        } else {
            Triple::host()
        };

        Ok(CompileConfig {
            input_files: self.input_files.into_iter().map(PathOrBuffer::Path).collect(),
            output_path: self.output,
            stop_after,
            verbose: self.verbose,
            preprocessor: crate::pp::PPConfig {
                max_include_depth: self.preprocessor.max_include_depth,
                system_include_paths,
                target: target_triple.clone(),
                ..Default::default()
            },
            suppress_line_markers: self.suppress_line_markers,
            include_paths: self.include_paths,
            defines,
            warnings,
            lang_options,
            target: target_triple,
        })
    }
}
