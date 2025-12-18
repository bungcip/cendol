//! CLI parsing and configuration module
//!
//! This module handles command-line argument parsing using clap and
//! provides configuration structures for the compiler driver.

use clap::{Args, Parser as CliParser};
use std::path::PathBuf;

use crate::lang_options::LangOptions;

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

    /// Dump parser state
    #[clap(long)]
    pub dump_parser: bool,

    /// Generate HTML AST dump
    #[clap(long)]
    pub dump_ast: bool,

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

    /// Enable pedantic mode (strict standards compliance)
    #[clap(long = "pedantic")]
    pub pedantic: bool,

    /// Enable all warnings
    #[clap(long = "Wall")]
    pub wall: bool,

    /// Set C language standard (e.g., c99, c11)
    #[clap(long = "std", value_name = "STANDARD")]
    pub c_standard: Option<String>,
}

#[derive(Args, Debug)]
pub struct PreprocessorOptions {
    /// Maximum include depth
    #[clap(long, default_value = "100")]
    pub max_include_depth: usize,
}

/// Configuration for compilation
#[derive(Debug)]
pub struct CompileConfig {
    pub input_files: Vec<PathBuf>,
    pub output_path: Option<PathBuf>,
    pub dump_ast: bool,
    pub dump_parser: bool,
    pub preprocess_only: bool,
    pub verbose: bool,
    pub preprocessor: crate::pp::PPConfig,
    pub suppress_line_markers: bool,
    pub include_paths: Vec<PathBuf>,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
    pub warnings: Vec<String>,
    pub lang_options: LangOptions,
    _temp_file: Option<tempfile::TempPath>,
}

impl CompileConfig {
    /// Create a new CompileConfig from a string of source code
    pub fn from_source_code(source: String) -> Self {
        use std::io::Write;
        let mut tmpfile = tempfile::Builder::new().suffix(".c").tempfile().unwrap();
        write!(tmpfile, "{}", source).unwrap();
        let temp_path = tmpfile.into_temp_path();
        let path = temp_path.to_path_buf();

        Self {
            input_files: vec![path],
            output_path: None,
            dump_ast: false,
            dump_parser: false,
            preprocess_only: false,
            verbose: false,
            preprocessor: crate::pp::PPConfig::default(),
            suppress_line_markers: false,
            include_paths: vec![],
            defines: vec![],
            warnings: vec![],
            lang_options: LangOptions::default(),
            _temp_file: Some(temp_path),
        }
    }
}

impl Cli {
    /// Convert CLI arguments into compilation configuration
    pub fn into_config(self) -> CompileConfig {
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
        let lang_options = LangOptions {
            c11: false, // Default to false, will be overridden by -std flag
            gnu_mode: false,
            ms_extensions: false,
            pedantic: self.pedantic,
            c_standard: self.c_standard,
        };

        CompileConfig {
            input_files: self.input_files,
            output_path: self.output,
            dump_ast: self.dump_ast,
            dump_parser: self.dump_parser,
            preprocess_only: self.preprocess_only,
            verbose: self.verbose,
            preprocessor: crate::pp::PPConfig {
                max_include_depth: self.preprocessor.max_include_depth,
                ..Default::default()
            },
            suppress_line_markers: self.suppress_line_markers,
            include_paths: self.include_paths,
            defines,
            warnings,
            lang_options,
            _temp_file: None,
        }
    }
}
