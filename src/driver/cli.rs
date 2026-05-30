//! CLI parsing and configuration module
//!
//! This module handles command-line argument parsing using clap and
//! provides configuration structures for the compiler driver.

use clap::{Args, Parser as CliParser};
use std::path::PathBuf;
use target_lexicon::{DefaultToHost, Triple};

use crate::{
    driver::artifact::CompilePhase,
    lang_options::{CStandard, LangOptions, SignedOverflowMode},
};

/// CLI interface using clap
#[derive(CliParser, Debug, Default)]
#[clap(name = "cendol", version, about = "C11 Compiler written in Rust")]
pub struct Cli {
    /// Input C source files
    #[clap(value_parser, required = true)]
    pub input_files: Vec<PathBuf>,

    /// Output file for AST dump
    #[clap(short, long, value_name = "FILE")]
    pub output: Option<PathBuf>,

    /// Enable verbose diagnostic output
    #[clap(short, long, action = clap::ArgAction::SetTrue)]
    pub verbose: bool,

    /// Dump AST after parser phase
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_ast_after_parser: bool,

    /// Dump AST after semantic lowering phase
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_ast_after_semantic_lowering: bool,

    /// Dump MIR (Mid-level Intermediate Representation) to console
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_mir: bool,

    /// Dump Cranelift IR (Intermediate Representation) to console
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub dump_cranelift: bool,

    /// Preprocess only, output preprocessed source to stdout
    #[clap(short = 'E', action = clap::ArgAction::SetTrue)]
    pub preprocess_only: bool,

    /// Preprocessor options
    #[clap(flatten)]
    pub preprocessor: PreprocessorOptions,

    /// Suppress line markers in preprocessor output
    #[clap(short = 'P', action = clap::ArgAction::SetTrue)]
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
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub pedantic: bool,

    /// Issue all the warnings demanded by strict ISO C as errors
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub pedantic_errors: bool,

    /// Set C language standard (e.g., c99, c11)
    #[clap(long = "std", value_name = "STANDARD")]
    pub c_standard: Option<CStandard>,

    /// Set default symbol visibility (e.g., default, hidden, protected, internal)
    #[clap(long = "fvisibility", value_name = "VISIBILITY")]
    pub fvisibility: Option<crate::lang_options::Visibility>,

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
    #[clap(short = 'c', action = clap::ArgAction::SetTrue, overrides_with = "compile_only")]
    pub compile_only: bool,

    /// Generate debug information
    #[clap(short = 'g', action = clap::ArgAction::SetTrue, overrides_with = "debug_info")]
    pub debug_info: bool,

    /// Strip symbols (ignored)
    #[clap(short = 's', action = clap::ArgAction::SetTrue, overrides_with = "strip")]
    pub strip: bool,

    /// Pass -rdynamic to linker (ignored)
    #[clap(long = "rdynamic", action = clap::ArgAction::SetTrue, overrides_with = "rdynamic")]
    pub rdynamic: bool,

    /// Create a shared library
    #[clap(long = "shared", action = clap::ArgAction::SetTrue, overrides_with = "shared")]
    pub shared: bool,

    /// Pass arguments to linker
    #[clap(short = 'X', long = "linker-arg", value_name = "ARG", action = clap::ArgAction::Append)]
    pub linker_args: Vec<String>,

    /// Use a specific linker
    #[clap(long = "fuse-ld", value_name = "LINKER")]
    pub fuse_ld: Option<String>,

    /// Maximum number of errors to report (default: 1)
    #[clap(long = "fmax-errors", value_name = "N")]
    pub fmax_errors: Option<usize>,

    /// Treat signed integer overflow as well-defined (wrapping)
    #[clap(long = "fwrapv", overrides_with = "fno_wrapv", overrides_with = "fstrict_overflow", overrides_with = "fno_strict_overflow", overrides_with = "ftrapv", overrides_with = "fno_trapv", action = clap::ArgAction::SetTrue)]
    pub fwrapv: bool,

    /// Treat signed integer overflow as undefined behavior
    #[clap(long = "fno-wrapv", overrides_with = "fwrapv", overrides_with = "fstrict_overflow", overrides_with = "fno_strict_overflow", overrides_with = "ftrapv", overrides_with = "fno_trapv", action = clap::ArgAction::SetTrue)]
    pub fno_wrapv: bool,

    /// Treat signed integer overflow as undefined behavior
    #[clap(long = "fstrict-overflow", overrides_with = "fwrapv", overrides_with = "fno_wrapv", overrides_with = "fno_strict_overflow", overrides_with = "ftrapv", overrides_with = "fno_trapv", action = clap::ArgAction::SetTrue)]
    pub fstrict_overflow: bool,

    /// Treat signed integer overflow as well-defined (wrapping)
    #[clap(long = "fno-strict-overflow", overrides_with = "fwrapv", overrides_with = "fno_wrapv", overrides_with = "fstrict_overflow", overrides_with = "ftrapv", overrides_with = "fno_trapv", action = clap::ArgAction::SetTrue)]
    pub fno_strict_overflow: bool,

    /// Generate traps for signed overflow on addition, subtraction, and multiplication
    #[clap(long = "ftrapv", overrides_with = "fwrapv", overrides_with = "fno_wrapv", overrides_with = "fstrict_overflow", overrides_with = "fno_strict_overflow", overrides_with = "fno_trapv", action = clap::ArgAction::SetTrue)]
    pub ftrapv: bool,

    /// Do not generate traps for signed overflow
    #[clap(long = "fno-trapv", overrides_with = "fwrapv", overrides_with = "fno_wrapv", overrides_with = "fstrict_overflow", overrides_with = "fno_strict_overflow", overrides_with = "ftrapv", action = clap::ArgAction::SetTrue)]
    pub fno_trapv: bool,

    /// Generate position-independent code
    #[clap(long = "fPIC", overrides_with = "f_no_pic", action = clap::ArgAction::SetTrue)]
    pub f_pic: bool,

    /// Do not generate position-independent code
    #[clap(long = "fno-PIC", overrides_with = "f_pic", action = clap::ArgAction::SetTrue)]
    pub f_no_pic: bool,

    /// GCC/Clang compatible flags to ignore (e.g., -fno-stack-protector)
    #[clap(short = 'f', action = clap::ArgAction::Append)]
    pub ignored_f_flags: Vec<String>,

    /// GCC/Clang compatible flags to ignore (e.g., -MD, -MP, -MF, -MT)
    #[clap(short = 'M', action = clap::ArgAction::Append)]
    pub ignored_m_flags: Vec<String>,

    /// Print timing information for each compilation phase
    #[clap(long, action = clap::ArgAction::SetTrue)]
    pub timing: bool,

    /// Suppress all warnings
    #[clap(short = 'w', action = clap::ArgAction::SetTrue)]
    pub suppress_warnings: bool,
}

#[derive(Args, Debug, Default)]
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

impl PathOrBuffer {
    pub(crate) fn is_external_object(&self) -> bool {
        match self {
            PathOrBuffer::Path(path) => {
                if let Some(ext) = path.extension().and_then(|s| s.to_str()) {
                    let is_known_ext = matches!(ext, "o" | "obj" | "a" | "so" | "dylib" | "dll");
                    let is_versioned_so = || {
                        let filename = path.file_name().and_then(|s| s.to_str()).unwrap_or("");
                        filename.contains(".so.") || filename.contains(".dylib.")
                    };
                    is_known_ext || is_versioned_so()
                } else {
                    false
                }
            }
            PathOrBuffer::Buffer(_, _) => false,
        }
    }

    pub(crate) fn is_source_file(&self) -> bool {
        match self {
            PathOrBuffer::Path(path) => {
                if let Some(ext) = path.extension().and_then(|s| s.to_str()) {
                    matches!(ext, "c" | "i")
                } else {
                    false
                }
            }
            PathOrBuffer::Buffer(_, _) => true,
        }
    }
}

/// Configuration for compilation
#[derive(Debug, Default)]
pub struct CompileConfig {
    pub input_files: Vec<PathOrBuffer>,
    pub output_path: Option<PathBuf>,
    pub stop_after: CompilePhase,

    pub verbose: bool,
    pub preprocessor: crate::pp::PPConfig,
    pub suppress_line_markers: bool,
    pub defines: Vec<(String, Option<String>)>, // NAME -> VALUE
    pub warnings: Vec<String>,
    pub c_standard: CStandard,
    pub lang_options: LangOptions,
    pub target: DefaultToHost,

    pub optimization: Option<String>,
    pub libraries: Vec<String>,
    pub library_paths: Vec<PathBuf>,
    pub compile_only: bool,
    pub debug_info: bool,
    pub shared: bool,
    pub linker_args: Vec<String>,
    pub fuse_ld: Option<String>,
    pub fmax_errors: Option<usize>,
    pub ignored_f_flags: Vec<String>,
    pub ignored_m_flags: Vec<String>,
    pub timing: bool,
    pub suppress_warnings: bool,
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
        let mut warnings = self.warnings;

        if self.pedantic {
            warnings.push("pedantic".to_string());
        }
        if self.pedantic_errors {
            warnings.push("pedantic-errors".to_string());
        }

        // Build language options

        let mut signed_overflow_mode = SignedOverflowMode::Wrap;
        if self.fno_wrapv || self.fstrict_overflow {
            signed_overflow_mode = SignedOverflowMode::Undefined;
        }
        if self.fwrapv || self.fno_strict_overflow || self.fno_trapv {
            signed_overflow_mode = SignedOverflowMode::Wrap;
        }
        if self.ftrapv {
            signed_overflow_mode = SignedOverflowMode::Trap;
        }

        let mut fpic = true;
        if self.f_no_pic {
            fpic = false;
        }
        if self.f_pic {
            fpic = true;
        }

        let c_standard = self.c_standard.unwrap_or_default();
        let lang_options = crate::lang_options::LangOptions {
            c_standard,
            pedantic: self.pedantic,
            pedantic_errors: self.pedantic_errors,
            signed_overflow_mode,
            fpic,
            visibility: self.fvisibility.unwrap_or_default(),
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
        system_include_paths.push(PathBuf::from("/usr/local/include"));

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
                c_standard,
                pedantic: self.pedantic,
                pedantic_errors: self.pedantic_errors,
                ..Default::default()
            },
            suppress_line_markers: self.suppress_line_markers,
            defines,
            warnings,
            c_standard,
            lang_options,
            target: DefaultToHost(target_triple),
            optimization: self.optimization,
            libraries: self.libraries,
            library_paths: self.library_paths,
            compile_only: self.compile_only,
            debug_info: self.debug_info,
            shared: self.shared,
            linker_args: self.linker_args,
            fuse_ld: self.fuse_ld,
            fmax_errors: self.fmax_errors,
            ignored_f_flags: self.ignored_f_flags,
            ignored_m_flags: self.ignored_m_flags,
            timing: self.timing,
            suppress_warnings: self.suppress_warnings,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_path_or_buffer() {
        // Source files
        assert!(PathOrBuffer::Path(PathBuf::from("test.c")).is_source_file());
        assert!(PathOrBuffer::Path(PathBuf::from("test.i")).is_source_file());
        assert!(!PathOrBuffer::Path(PathBuf::from("test.o")).is_source_file());
        assert!(!PathOrBuffer::Path(PathBuf::from("test_no_ext")).is_source_file());

        // External objects
        assert!(PathOrBuffer::Path(PathBuf::from("test.o")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("test.obj")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("test.a")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("test.so")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("test.dylib")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("test.dll")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("libtest.so.1")).is_external_object());
        assert!(PathOrBuffer::Path(PathBuf::from("libtest.dylib.1")).is_external_object());
        assert!(!PathOrBuffer::Path(PathBuf::from("test.c")).is_external_object());
        assert!(!PathOrBuffer::Path(PathBuf::from("test_no_ext")).is_external_object());

        // Buffers
        assert!(PathOrBuffer::Buffer("test".to_string(), vec![]).is_source_file());
        assert!(!PathOrBuffer::Buffer("test".to_string(), vec![]).is_external_object());
    }

    #[test]
    fn test_cli_into_config_and_validation() {
        // Test case: Valid configuration with defines and specific stop_after
        let cli = Cli {
            input_files: vec![PathBuf::from("test.c")],
            output: Some(PathBuf::from("out")),
            verbose: true,
            dump_mir: true,
            preprocessor: PreprocessorOptions { max_include_depth: 50 },
            suppress_line_markers: true,
            include_paths: vec![PathBuf::from("inc")],
            defines: vec!["FOO=1".to_string(), "BAR".to_string()],
            warnings: vec!["all".to_string()],
            target: Some("x86_64-unknown-linux-gnu".to_string()),
            optimization: Some("2".to_string()),
            libraries: vec!["m".to_string()],
            library_paths: vec![PathBuf::from("/lib")],
            compile_only: true,
            debug_info: true,
            fuse_ld: Some("lld".to_string()),
            fmax_errors: Some(5),
            ..Default::default()
        };

        let config = cli.into_config().expect("Failed to create config");

        assert_eq!(config.fuse_ld, Some("lld".to_string()));
        assert_eq!(config.fmax_errors, Some(5));
        assert_eq!(config.stop_after, CompilePhase::Mir);
        assert!(config.verbose);
        assert!(config.suppress_line_markers);
        assert_eq!(config.preprocessor.max_include_depth, 50);
        assert_eq!(config.target.0.to_string(), "x86_64-unknown-linux-gnu");

        let defines: Vec<_> = config.defines.into_iter().collect();
        assert!(defines.contains(&("FOO".to_string(), Some("1".to_string()))));
        assert!(defines.contains(&("BAR".to_string(), None)));

        // Test error case: Input file starting with '-' that does not exist
        let cli_error = Cli {
            input_files: vec![PathBuf::from("-nonexistent")],
            preprocessor: PreprocessorOptions { max_include_depth: 100 },
            ..Default::default()
        };

        let err = cli_error.into_config().unwrap_err();
        assert!(err.contains("File '-nonexistent' not found"));
        assert!(err.contains("meant to be a command-line option"));
    }

    #[test]
    fn test_cli_config_features() {
        let cli = Cli {
            input_files: vec![PathBuf::from("dummy.c")],
            dump_ast_after_parser: true,
            dump_ast_after_semantic_lowering: true,
            dump_cranelift: true,
            preprocess_only: true,
            preprocessor: PreprocessorOptions { max_include_depth: 100 },
            pedantic: true,
            pedantic_errors: true,
            ..Default::default()
        };

        // This tests testing the default bounds, pedantic bounds, and dump priorities
        let config = cli.into_config().unwrap();
        assert_eq!(config.stop_after, CompilePhase::Preprocess);
        assert!(config.warnings.contains(&"pedantic".to_string()));
        assert!(config.warnings.contains(&"pedantic-errors".to_string()));
        assert_eq!(config.target.0, Triple::host());
    }

    #[test]
    fn test_cli_dump_flags_coverage() {
        use clap::Parser;

        let cli1 = Cli::parse_from(["cendol", "dummy.c", "--dump-ast-after-parser"]);
        assert_eq!(cli1.into_config().unwrap().stop_after, CompilePhase::Parse);

        let cli2 = Cli::parse_from(["cendol", "dummy.c", "--dump-ast-after-semantic-lowering"]);
        assert_eq!(cli2.into_config().unwrap().stop_after, CompilePhase::SemanticLowering);

        let cli3 = Cli::parse_from(["cendol", "dummy.c", "--dump-mir"]);
        assert_eq!(cli3.into_config().unwrap().stop_after, CompilePhase::Mir);

        let cli4 = Cli::parse_from(["cendol", "dummy.c", "--dump-cranelift"]);
        assert_eq!(cli4.into_config().unwrap().stop_after, CompilePhase::Cranelift);

        let cli5 = Cli::parse_from(["cendol", "dummy.c"]);
        assert_eq!(cli5.into_config().unwrap().stop_after, CompilePhase::EmitObject);
    }

    #[test]
    fn test_cli_fwrapv() {
        use clap::Parser;

        // Default should be Wrap
        let cli1 = Cli::parse_from(["cendol", "dummy.c"]);
        assert_eq!(
            cli1.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Explicit -fwrapv
        let cli2 = Cli::parse_from(["cendol", "dummy.c", "--fwrapv"]);
        assert_eq!(
            cli2.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Explicit -fno-wrapv
        let cli3 = Cli::parse_from(["cendol", "dummy.c", "--fno-wrapv"]);
        assert_eq!(
            cli3.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Undefined
        );

        // Last one wins: -fwrapv -fno-wrapv -> Undefined
        let cli4 = Cli::parse_from(["cendol", "dummy.c", "--fwrapv", "--fno-wrapv"]);
        assert_eq!(
            cli4.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Undefined
        );

        // Last one wins: -fno-wrapv -fwrapv -> Wrap
        let cli5 = Cli::parse_from(["cendol", "dummy.c", "--fno-wrapv", "--fwrapv"]);
        assert_eq!(
            cli5.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Explicit -fstrict-overflow
        let cli6 = Cli::parse_from(["cendol", "dummy.c", "--fstrict-overflow"]);
        assert_eq!(
            cli6.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Undefined
        );

        // Explicit -fno-strict-overflow
        let cli7 = Cli::parse_from(["cendol", "dummy.c", "--fno-strict-overflow"]);
        assert_eq!(
            cli7.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Mix: -fstrict-overflow -fno-strict-overflow -> Wrap
        let cli8 = Cli::parse_from(["cendol", "dummy.c", "--fstrict-overflow", "--fno-strict-overflow"]);
        assert_eq!(
            cli8.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Mix: -fno-strict-overflow -fstrict-overflow -> Undefined
        let cli9 = Cli::parse_from(["cendol", "dummy.c", "--fno-strict-overflow", "--fstrict-overflow"]);
        assert_eq!(
            cli9.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Undefined
        );

        // Mix: -fwrapv -fstrict-overflow -> Undefined
        let cli10 = Cli::parse_from(["cendol", "dummy.c", "--fwrapv", "--fstrict-overflow"]);
        assert_eq!(
            cli10.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Undefined
        );

        // Mix: -fstrict-overflow -fwrapv -> Wrap
        let cli11 = Cli::parse_from(["cendol", "dummy.c", "--fstrict-overflow", "--fwrapv"]);
        assert_eq!(
            cli11.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );
    }

    #[test]
    fn test_cli_ftrapv() {
        use clap::Parser;

        // Default should be Wrap (i.e. not Trap)
        let cli1 = Cli::parse_from(["cendol", "dummy.c"]);
        assert_eq!(
            cli1.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Explicit -ftrapv
        let cli2 = Cli::parse_from(["cendol", "dummy.c", "--ftrapv"]);
        assert_eq!(
            cli2.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Trap
        );

        // Explicit -fno-trapv
        let cli3 = Cli::parse_from(["cendol", "dummy.c", "--fno-trapv"]);
        assert_eq!(
            cli3.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Last one wins: -ftrapv -fno-trapv -> Wrap
        let cli4 = Cli::parse_from(["cendol", "dummy.c", "--ftrapv", "--fno-trapv"]);
        assert_eq!(
            cli4.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Wrap
        );

        // Last one wins: -fno-trapv -ftrapv -> Trap
        let cli5 = Cli::parse_from(["cendol", "dummy.c", "--fno-trapv", "--ftrapv"]);
        assert_eq!(
            cli5.into_config().unwrap().lang_options.signed_overflow_mode,
            SignedOverflowMode::Trap
        );
    }
}
