//! CLI parsing and configuration module
//!
//! This module handles command-line argument parsing using clap and
//! provides configuration structures for the compiler driver.

use clap::{Args, Parser as CliParser};
use std::path::PathBuf;
use target_lexicon::Triple;

use crate::{
    driver::artifact::CompilePhase,
    lang_options::{CStandard, LangOptions},
};

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

    /// Include search paths
    #[clap(short = 'I', long = "include-path", value_name = "DIR", action = clap::ArgAction::Append)]
    pub include_paths: Vec<PathBuf>,

    /// Preprocessor macro definitions
    #[clap(short = 'D', long = "define", value_name = "NAME[=VALUE]", action = clap::ArgAction::Append)]
    pub defines: Vec<String>,

    /// Compiler warnings (e.g., -Wall, -Wshadow)
    #[clap(short = 'W', action = clap::ArgAction::Append)]
    pub warnings: Vec<String>,

    /// Issue all the warnings demanded by strict ISO C
    #[clap(long)]
    pub pedantic: bool,

    /// Issue all the warnings demanded by strict ISO C as errors
    #[clap(long)]
    pub pedantic_errors: bool,

    /// Set C language standard (e.g., c99, c11)
    #[clap(long = "std", value_name = "STANDARD")]
    pub c_standard: Option<CStandard>,

    /// Target triple (e.g. x86_64-unknown-linux-gnu)
    #[clap(long = "target", value_name = "TRIPLE")]
    pub target: Option<String>,

    /// Optimization level (e.g., -O0, -O1, -O2, -O3, -Os, -Oz)
    #[clap(short = 'O', action = clap::ArgAction::Set)]
    pub optimization: Option<String>,

    /// Linked libraries (e.g., -lm)
    #[clap(short = 'l', action = clap::ArgAction::Append)]
    pub libraries: Vec<String>,

    /// Library search paths (e.g., -L/usr/local/lib)
    #[clap(short = 'L', action = clap::ArgAction::Append)]
    pub library_paths: Vec<PathBuf>,

    /// Compile only, do not link
    #[clap(short = 'c')]
    pub compile_only: bool,

    /// Generate debug information
    #[clap(short = 'g')]
    pub debug_info: bool,
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
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
    pub warnings: Vec<String>,
    pub lang_options: LangOptions,
    pub target: Triple,

    pub optimization: Option<String>,
    pub libraries: Vec<String>,
    pub library_paths: Vec<PathBuf>,
    pub compile_only: bool,
    pub debug_info: bool,
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
            defines: Vec::new(),
            warnings: Vec::new(),
            lang_options: LangOptions::default(),
            target: Triple::host(),
            optimization: None,
            libraries: Vec::new(),
            library_paths: Vec::new(),
            compile_only: false,
            debug_info: false,
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
            // Allow files starting with '-' if they exist, or if they have an extension that looks like a C file
            if file_name.starts_with('-') && !input_file.exists() {
                // If it starts with - and doesn't exist, it might be an unrecognized flag
                // but clap should have handled it if it was a valid flag.
                // However, some flags like -O2 or -Wshadow might not be explicitly defined in clap yet.
                // So we should only error if it's definitely NOT meant to be a flag.

                // For now, let's keep it but maybe we should allow it if we want to ignore unknown flags?
                // Actually, the user wants us to support these flags.
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
    pub(crate) fn into_config(self) -> Result<CompileConfig, String> {
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
        // Actually, with short='W' and append, -Wall will result in "all" in warnings.
        // Handle -Wall flag by adding "all" to warnings if -Wall is specified
        // Actually, with short='W' and append, -Wall will result in "all" in warnings.
        let mut warnings = self.warnings;

        if self.pedantic {
            warnings.push("pedantic".to_string());
        }
        if self.pedantic_errors {
            warnings.push("pedantic-errors".to_string());
        }

        // Build language options

        let lang_options = LangOptions {
            c_standard: self.c_standard,
        };

        // Build preprocessor configuration with include paths
        let mut system_include_paths = Vec::new();

        // Add user-specified include paths as system include paths
        for path in &self.include_paths {
            system_include_paths.push(path.clone());
        }

        // Add default system include paths
        if std::path::Path::new("custom-include").exists() {
            system_include_paths.push(PathBuf::from("custom-include"));
        }
        system_include_paths.push(PathBuf::from("/usr/include"));

        // Add architecture-specific include paths
        let arch_paths = ["/usr/include/x86_64-linux-gnu"];

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
            defines,
            warnings,
            lang_options,
            target: target_triple,
            optimization: self.optimization,
            libraries: self.libraries,
            library_paths: self.library_paths,
            compile_only: self.compile_only,
            debug_info: self.debug_info,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_cli_into_config_and_validation() {
        // Test case: Valid configuration with defines and specific stop_after
        let cli = Cli {
            input_files: vec![PathBuf::from("test.c")],
            output: Some(PathBuf::from("out")),
            verbose: true,
            dump_ast_after_parser: false,
            dump_ast_after_semantic_lowering: false,
            dump_mir: true,
            dump_cranelift: false,
            preprocess_only: false,
            preprocessor: PreprocessorOptions { max_include_depth: 50 },
            suppress_line_markers: true,
            include_paths: vec![PathBuf::from("inc")],
            defines: vec!["FOO=1".to_string(), "BAR".to_string()],
            warnings: vec!["all".to_string()],
            pedantic: false,
            pedantic_errors: false,
            c_standard: None,
            target: Some("x86_64-unknown-linux-gnu".to_string()),
            optimization: Some("2".to_string()),
            libraries: vec!["m".to_string()],
            library_paths: vec![PathBuf::from("/lib")],
            compile_only: true,
            debug_info: true,
        };

        let config = cli.into_config().expect("Failed to create config");

        assert_eq!(config.stop_after, CompilePhase::Mir);
        assert!(config.verbose);
        assert!(config.suppress_line_markers);
        assert_eq!(config.preprocessor.max_include_depth, 50);
        assert_eq!(config.target.to_string(), "x86_64-unknown-linux-gnu");

        let defines: Vec<_> = config.defines.into_iter().collect();
        assert!(defines.contains(&("FOO".to_string(), Some("1".to_string()))));
        assert!(defines.contains(&("BAR".to_string(), None)));

        // Test error case: Input file starting with '-' that does not exist
        let cli_error = Cli {
            input_files: vec![PathBuf::from("-nonexistent")],
            output: None,
            verbose: false,
            dump_ast_after_parser: false,
            dump_ast_after_semantic_lowering: false,
            dump_mir: false,
            dump_cranelift: false,
            preprocess_only: false,
            preprocessor: PreprocessorOptions { max_include_depth: 100 },
            suppress_line_markers: false,
            include_paths: vec![],
            defines: vec![],
            warnings: vec![],
            pedantic: false,
            pedantic_errors: false,
            c_standard: None,
            target: None,
            optimization: None,
            libraries: vec![],
            library_paths: vec![],
            compile_only: false,
            debug_info: false,
        };

        let err = cli_error.into_config().unwrap_err();
        assert!(err.contains("File '-nonexistent' not found"));
        assert!(err.contains("meant to be a command-line option"));
    }
}
