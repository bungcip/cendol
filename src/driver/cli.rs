//! CLI parsing and configuration module
//!
//! This module handles command-line argument parsing using clap and
//! provides configuration structures for the compiler driver.

use clap::{Args, Parser as CliParser};
use std::path::PathBuf;

/// CLI interface using clap
#[derive(CliParser, Debug)]
#[clap(name = "cendol", about = "C11 Compiler written in Rust")]
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
        }
    }
}
