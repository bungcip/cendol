//! CLI parsing and configuration module
//!
//! This module handles command-line argument parsing with a custom parser
//! that natively supports GCC/Clang-style single-dash long options
//! (e.g., `-std=c99`, `-fwrapv`, `-fPIC`, `-Wl,...`).

use std::{cmp, path::PathBuf};

use target_lexicon::{DefaultToHost, Triple};

use crate::{
    driver::artifact::CompilePhase,
    lang_options::{CStandard, LangOptions, PedanticMode, SignedOverflowMode, Visibility},
};

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

// ── Help / Version ──────────────────────────────────────────────────────

fn print_help() {
    println!(
        "\
cendol {} — C11 Compiler written in Rust

USAGE:
    cendol [OPTIONS] <FILE>...

GENERAL OPTIONS:
    -o <FILE>                   Output file
    -v, --verbose               Enable verbose diagnostic output
    -w                          Suppress all warnings
    --help                      Print this help message
    --version                   Print version information
    --timing                    Print timing information for each compilation phase
    --max-include-depth <N>     Maximum include depth (default: 100)

LANGUAGE & STANDARD:
    -std=<STANDARD>             Set C language standard (c11, c17, c23)
    -pedantic                   Issue all warnings demanded by strict ISO C
    -pedantic-errors            Issue all ISO C warnings as errors

PREPROCESSOR:
    -E                          Preprocess only, output to stdout
    -P                          Suppress line markers in preprocessor output
    -I <DIR>                    Add include search path
    -D <NAME>[=<VALUE>]         Define preprocessor macro

WARNINGS:
    -W<WARNING>                 Enable warning (e.g., -Wall, -Wextra, -Wshadow)

OPTIMIZATION:
    -O<LEVEL>                   Optimization level (0, 1, 2, 3, s, z)

CODE GENERATION:
    -c                          Compile only, do not link
    -g                          Generate debug information
    -s                          Strip symbols (ignored)
    -target=<TRIPLE>            Target triple (e.g., x86_64-unknown-linux-gnu)
    -fPIC                       Generate position-independent code (default)
    -fno-PIC                    Disable position-independent code
    -fvisibility=<VIS>          Set default symbol visibility (default, hidden, protected, internal)
    -shared                     Create a shared library

SIGNED OVERFLOW:
    -fwrapv                     Treat signed integer overflow as wrapping (default)
    -fno-wrapv                  Treat signed integer overflow as undefined
    -fstrict-overflow           Treat signed integer overflow as undefined
    -fno-strict-overflow        Treat signed integer overflow as wrapping
    -ftrapv                     Generate traps for signed overflow
    -fno-trapv                  Do not generate traps for signed overflow
    -fmax-errors=<N>            Maximum number of errors to report

LINKING:
    -l <LIB>                    Link library
    -L <DIR>                    Library search path
    -fuse-ld=<LINKER>           Use a specific linker
    -Xlinker <ARG>              Pass argument to linker
    -Wl,<ARGS>                  Pass comma-separated arguments to linker
    -rdynamic                   Pass -rdynamic to linker (ignored)
    -pthread                    Link with pthread support
    --linker-arg=<ARG>          Pass argument to linker (alternative form)

DEBUGGING:
    --dump-ast-after-parser             Dump AST after parser phase
    --dump-ast-after-semantic-lowering  Dump AST after semantic lowering phase
    --dump-mir                          Dump MIR to console
    --dump-cranelift                    Dump Cranelift IR to console",
        env!("CARGO_PKG_VERSION")
    );
}

fn print_version() {
    println!("cendol {}", env!("CARGO_PKG_VERSION"));
}

// ── Error type ──────────────────────────────────────────────────────────

/// Error from argument parsing (not a compiler error, exits immediately)
#[derive(Debug)]
pub enum ArgError {
    /// A hard error — print and exit(1)
    Error(String),
    /// --help was requested — exit(0)
    Help,
    /// --version was requested — exit(0)
    Version,
}

impl std::fmt::Display for ArgError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArgError::Error(msg) => write!(f, "{}", msg),
            ArgError::Help => write!(f, ""),
            ArgError::Version => write!(f, ""),
        }
    }
}

// ── Main parser ─────────────────────────────────────────────────────────

/// Parse command-line arguments from an iterator and return a CompileConfig.
///
/// This is the primary entry point for CLI parsing. It handles GCC/Clang
/// style arguments natively (single-dash long options, `-f*` flags, etc.).
pub(crate) fn parse_args_from<I>(args: I) -> Result<CompileConfig, ArgError>
where
    I: IntoIterator<Item = String>,
{
    let mut iter = args.into_iter().peekable();

    // Skip argv[0] (program name)
    let _program = iter.next();

    // Accumulate raw parsed values
    let mut input_files: Vec<PathBuf> = Vec::new();
    let mut output: Option<PathBuf> = None;
    let mut verbose = false;
    let mut suppress_line_markers = false;
    let mut include_paths: Vec<PathBuf> = Vec::new();
    let mut defines: Vec<String> = Vec::new();
    let mut warnings: Vec<String> = Vec::new();
    let mut c_standard: Option<CStandard> = None;
    let mut pedantic_mode = PedanticMode::Default;
    let mut fvisibility: Option<Visibility> = None;
    let mut target: Option<String> = None;
    let mut optimization: Option<String> = None;
    let mut libraries: Vec<String> = Vec::new();
    let mut library_paths: Vec<PathBuf> = Vec::new();
    let mut compile_only = false;
    let mut debug_info = false;
    let mut strip = false;
    let mut rdynamic = false;
    let mut shared = false;
    let mut linker_args: Vec<String> = Vec::new();
    let mut fuse_ld: Option<String> = None;
    let mut fmax_errors: Option<usize> = None;
    let mut ignored_f_flags: Vec<String> = Vec::new();
    let mut ignored_m_flags: Vec<String> = Vec::new();
    let mut timing = false;
    let mut suppress_warnings = false;
    let mut max_include_depth: usize = 100;
    let mut stop_after = CompilePhase::EmitObject;

    // For "last wins" semantics on overflow flags, we record each flag in order.
    #[derive(Clone, Copy)]
    enum OverflowFlag {
        Wrapv,
        NoWrapv,
        StrictOverflow,
        NoStrictOverflow,
        Trapv,
        NoTrapv,
    }
    let mut overflow_flags: Vec<OverflowFlag> = Vec::new();

    // For "last wins" on PIC flags
    #[derive(Clone, Copy)]
    enum PicFlag {
        Pic,
        NoPic,
    }
    let mut pic_flags: Vec<PicFlag> = Vec::new();

    while let Some(arg) = iter.next() {
        if !arg.starts_with('-') || arg == "-" {
            // positional argument → input file
            input_files.push(PathBuf::from(arg));
            continue;
        }

        // Double-dash terminator: everything after is positional
        if arg == "--" {
            for rest in &mut iter {
                input_files.push(PathBuf::from(rest));
            }
            break;
        }

        match arg.as_str() {
            // ── Help / Version ──
            "--help" | "-help" => return Err(ArgError::Help),
            "--version" | "-version" => return Err(ArgError::Version),

            // ── Simple boolean flags ──
            "-v" | "--verbose" => verbose = true,
            "-E" => stop_after = cmp::min(stop_after, CompilePhase::Preprocess),
            "-P" => suppress_line_markers = true,
            "-c" => compile_only = true,
            "-g" => debug_info = true,
            "-s" => strip = true,
            "-w" => suppress_warnings = true,
            "-rdynamic" => rdynamic = true,
            "-shared" | "--shared" => shared = true,
            "-pedantic" => pedantic_mode = PedanticMode::Warning,
            "-pedantic-errors" => pedantic_mode = PedanticMode::Error,
            "-pthread" => linker_args.push("-Wl,-pthread".to_string()),
            "--timing" => timing = true,

            // ── Dump flags ──
            "--dump-ast-after-parser" => stop_after = cmp::min(stop_after, CompilePhase::Parse),
            "--dump-ast-after-semantic-lowering" => stop_after = cmp::min(stop_after, CompilePhase::SemanticLowering),
            "--dump-mir" => stop_after = cmp::min(stop_after, CompilePhase::Mir),
            "--dump-cranelift" => stop_after = cmp::min(stop_after, CompilePhase::Cranelift),

            // ── Signed overflow flags ("last wins") ──
            "-fwrapv" => overflow_flags.push(OverflowFlag::Wrapv),
            "-fno-wrapv" => overflow_flags.push(OverflowFlag::NoWrapv),
            "-fstrict-overflow" => overflow_flags.push(OverflowFlag::StrictOverflow),
            "-fno-strict-overflow" => overflow_flags.push(OverflowFlag::NoStrictOverflow),
            "-ftrapv" => overflow_flags.push(OverflowFlag::Trapv),
            "-fno-trapv" => overflow_flags.push(OverflowFlag::NoTrapv),

            // ── PIC flags ("last wins") ──
            "-fPIC" => pic_flags.push(PicFlag::Pic),
            "-fno-PIC" => pic_flags.push(PicFlag::NoPic),

            _ => {
                // ── Flags with values ──

                // -o <FILE> or -o<FILE>
                if arg == "-o" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -o".to_string()))?;
                    output = Some(PathBuf::from(val));
                } else if let Some(rest) = arg.strip_prefix("-o") {
                    output = Some(PathBuf::from(rest));
                }
                // -std=<STANDARD>
                else if let Some(val) = arg.strip_prefix("-std=") {
                    c_standard = Some(val.parse::<CStandard>().map_err(ArgError::Error)?);
                }
                // -target=<TRIPLE> or -target <TRIPLE>
                else if arg == "-target" || arg == "--target" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -target".to_string()))?;
                    target = Some(val);
                } else if let Some(val) = arg.strip_prefix("-target=").or_else(|| arg.strip_prefix("--target=")) {
                    target = Some(val.to_string());
                }
                // -fvisibility=<VIS>
                else if let Some(val) = arg.strip_prefix("-fvisibility=") {
                    fvisibility = Some(val.parse::<Visibility>().map_err(ArgError::Error)?);
                }
                // -fuse-ld=<LINKER>
                else if let Some(val) = arg.strip_prefix("-fuse-ld=") {
                    fuse_ld = Some(val.to_string());
                }
                // -fmax-errors=<N>
                else if let Some(val) = arg.strip_prefix("-fmax-errors=") {
                    fmax_errors = Some(
                        val.parse::<usize>()
                            .map_err(|_| ArgError::Error(format!("invalid value for -fmax-errors: '{}'", val)))?,
                    );
                }
                // -O<level> (handles -O, -O0, -O1, -O2, -O3, -Os, -Oz)
                else if arg == "-O" {
                    optimization = Some("1".to_string());
                } else if let Some(level) = arg.strip_prefix("-O") {
                    optimization = Some(level.to_string());
                }
                // -I<DIR> or -I <DIR>
                else if arg == "-I" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -I".to_string()))?;
                    include_paths.push(PathBuf::from(val));
                } else if let Some(rest) = arg.strip_prefix("-I") {
                    include_paths.push(PathBuf::from(rest));
                }
                // -D<NAME>[=<VALUE>] or -D <NAME>[=<VALUE>]
                else if arg == "-D" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -D".to_string()))?;
                    defines.push(val);
                } else if let Some(rest) = arg.strip_prefix("-D") {
                    defines.push(rest.to_string());
                }
                // -W<WARNING> (e.g., -Wall, -Wextra, -Wshadow)
                // Also handle -W as alias for -Wextra
                else if arg == "-W" {
                    warnings.push("extra".to_string());
                } else if let Some(rest) = arg.strip_prefix("-W") {
                    // -Wl,... is a linker pass-through
                    if let Some(linker_val) = rest.strip_prefix("l,") {
                        linker_args.push(format!("-Wl,{}", linker_val));
                    } else {
                        warnings.push(rest.to_string());
                    }
                }
                // -l<LIB> or -l <LIB>
                else if arg == "-l" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -l".to_string()))?;
                    libraries.push(val);
                } else if let Some(rest) = arg.strip_prefix("-l") {
                    libraries.push(rest.to_string());
                }
                // -L<DIR> or -L <DIR>
                else if arg == "-L" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -L".to_string()))?;
                    library_paths.push(PathBuf::from(val));
                } else if let Some(rest) = arg.strip_prefix("-L") {
                    library_paths.push(PathBuf::from(rest));
                }
                // -Xlinker <ARG> (next arg is the linker arg)
                else if arg == "-Xlinker" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for -Xlinker".to_string()))?;
                    if val.starts_with("-Wl,") {
                        linker_args.push(val);
                    } else {
                        linker_args.push(format!("-Wl,{}", val));
                    }
                }
                // --linker-arg=<ARG> (alternative form)
                else if let Some(val) = arg.strip_prefix("--linker-arg=") {
                    linker_args.push(val.to_string());
                } else if arg == "--linker-arg" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for --linker-arg".to_string()))?;
                    linker_args.push(val);
                }
                // --max-include-depth <N>
                else if arg == "--max-include-depth" {
                    let val = iter
                        .next()
                        .ok_or_else(|| ArgError::Error("missing argument for --max-include-depth".to_string()))?;
                    max_include_depth = val
                        .parse::<usize>()
                        .map_err(|_| ArgError::Error(format!("invalid value for --max-include-depth: '{}'", val)))?;
                } else if let Some(val) = arg.strip_prefix("--max-include-depth=") {
                    max_include_depth = val
                        .parse::<usize>()
                        .map_err(|_| ArgError::Error(format!("invalid value for --max-include-depth: '{}'", val)))?;
                }
                // -g<anything> → treat as -g (ignore debug level suffix like -g3, -ggdb)
                else if arg.starts_with("-g") {
                    debug_info = true;
                }
                // -M<flag> → ignored dependency flags (e.g., -MD, -MP, -MF, -MT)
                else if let Some(rest) = arg.strip_prefix("-M") {
                    // -MF and -MT take an argument
                    if rest == "F" || rest == "T" {
                        let _ = iter.next(); // consume the next arg
                    }
                    ignored_m_flags.push(rest.to_string());
                }
                // -f<flag> → catch-all for unrecognized -f flags
                else if let Some(rest) = arg.strip_prefix("-f") {
                    ignored_f_flags.push(rest.to_string());
                }
                // Unknown flag starting with '-' that doesn't exist as a file
                else {
                    let path = PathBuf::from(&arg);
                    if path.exists() {
                        input_files.push(path);
                    } else {
                        return Err(ArgError::Error(format!(
                            "cendol: error: unrecognized command-line option '{}'",
                            arg
                        )));
                    }
                }
            }
        }
    }

    // ── Validation ──────────────────────────────────────────────────────

    if input_files.is_empty() {
        return Err(ArgError::Error("cendol: error: no input files".to_string()));
    }

    // ── Resolve "last wins" flags ───────────────────────────────────────

    let mut signed_overflow_mode = SignedOverflowMode::Wrap;
    for flag in &overflow_flags {
        match flag {
            OverflowFlag::Wrapv | OverflowFlag::NoStrictOverflow | OverflowFlag::NoTrapv => {
                signed_overflow_mode = SignedOverflowMode::Wrap;
            }
            OverflowFlag::NoWrapv | OverflowFlag::StrictOverflow => {
                signed_overflow_mode = SignedOverflowMode::Undefined;
            }
            OverflowFlag::Trapv => {
                signed_overflow_mode = SignedOverflowMode::Trap;
            }
        }
    }

    let mut fpic = true;
    for flag in &pic_flags {
        match flag {
            PicFlag::Pic => fpic = true,
            PicFlag::NoPic => fpic = false,
        }
    }

    // ── Build warnings list ─────────────────────────────────────────────

    if pedantic_mode == PedanticMode::Warning {
        warnings.push("pedantic".to_string());
    }
    if pedantic_mode == PedanticMode::Error {
        warnings.push("pedantic-errors".to_string());
    }

    // ── Parse defines ───────────────────────────────────────────────────

    let parsed_defines = defines
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

    // ── Build target triple ─────────────────────────────────────────────

    let target_triple = if let Some(t) = target {
        t.parse::<Triple>()
            .map_err(|e| ArgError::Error(format!("Invalid target triple: {}", e)))?
    } else {
        Triple::host()
    };

    // ── Build include paths ─────────────────────────────────────────────

    let mut system_include_paths = Vec::new();
    let mut add_path = |path: PathBuf| {
        if let Ok(canonical) = path.canonicalize() {
            system_include_paths.push(canonical);
        } else {
            system_include_paths.push(path);
        }
    };

    for path in &include_paths {
        add_path(path.clone());
    }

    if std::path::Path::new("custom-include").exists() {
        add_path(PathBuf::from("custom-include"));
    }
    add_path(PathBuf::from("/usr/include"));
    add_path(PathBuf::from("/usr/local/include"));

    let arch_paths = ["/usr/include/x86_64-linux-gnu"];
    for arch_path in &arch_paths {
        let path = PathBuf::from(arch_path);
        if path.exists() {
            add_path(path);
        }
    }

    // ── Build final config ──────────────────────────────────────────────

    let c_standard = c_standard.unwrap_or_default();
    let lang_options = LangOptions {
        c_standard,
        pedantic_mode,
        signed_overflow_mode,
        fpic,
        visibility: fvisibility.unwrap_or_default(),
    };

    let _ = strip; // intentionally ignored
    let _ = rdynamic; // intentionally ignored

    Ok(CompileConfig {
        input_files: input_files.into_iter().map(PathOrBuffer::Path).collect(),
        output_path: output,
        stop_after,
        verbose,
        preprocessor: crate::pp::PPConfig {
            max_include_depth,
            system_include_paths,
            lang_options,
            target: target_triple.clone(),
            ..Default::default()
        },
        suppress_line_markers,
        defines: parsed_defines,
        warnings,
        c_standard,
        lang_options,
        target: DefaultToHost(target_triple),
        optimization,
        libraries,
        library_paths,
        compile_only,
        debug_info,
        shared,
        linker_args,
        fuse_ld,
        fmax_errors,
        ignored_f_flags,
        ignored_m_flags,
        timing,
        suppress_warnings,
    })
}

/// Parse arguments from `std::env::args()`.
pub fn parse_args() -> Result<CompileConfig, ArgError> {
    parse_args_from(std::env::args())
}

// ── Public re-exports for the help/version actions ──────────────────────

impl ArgError {
    /// Handle the error by printing the appropriate message and returning the exit code.
    pub fn exit_code(&self) -> i32 {
        match self {
            ArgError::Error(_) => 1,
            ArgError::Help | ArgError::Version => 0,
        }
    }

    /// Print the appropriate output for this error.
    pub fn print(&self) {
        match self {
            ArgError::Error(msg) => eprintln!("{}", msg),
            ArgError::Help => print_help(),
            ArgError::Version => print_version(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    /// Helper: parse from a list of &str (prepending "cendol" as argv[0])
    fn parse(args: &[&str]) -> Result<CompileConfig, ArgError> {
        let v: Vec<String> = args.iter().map(|s| s.to_string()).collect();
        parse_args_from(v)
    }

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
    fn test_basic_config() {
        let config = parse(&[
            "cendol",
            "test.c",
            "-o",
            "out",
            "-v",
            "--dump-mir",
            "-I",
            "inc",
            "-DFOO=1",
            "-DBAR",
            "-Wall",
            "-target=x86_64-unknown-linux-gnu",
            "-O2",
            "-lm",
            "-L/lib",
            "-c",
            "-g",
            "-fuse-ld=lld",
            "-fmax-errors=5",
        ])
        .unwrap();

        assert_eq!(config.fuse_ld, Some("lld".to_string()));
        assert_eq!(config.fmax_errors, Some(5));
        assert_eq!(config.stop_after, CompilePhase::Mir);
        assert!(config.verbose);
        assert_eq!(config.target.0.to_string(), "x86_64-unknown-linux-gnu");

        let defines: Vec<_> = config.defines.into_iter().collect();
        assert!(defines.contains(&("FOO".to_string(), Some("1".to_string()))));
        assert!(defines.contains(&("BAR".to_string(), None)));
    }

    #[test]
    fn test_dump_flags_coverage() {
        let c1 = parse(&["cendol", "dummy.c", "--dump-ast-after-parser"]).unwrap();
        assert_eq!(c1.stop_after, CompilePhase::Parse);

        let c2 = parse(&["cendol", "dummy.c", "--dump-ast-after-semantic-lowering"]).unwrap();
        assert_eq!(c2.stop_after, CompilePhase::SemanticLowering);

        let c3 = parse(&["cendol", "dummy.c", "--dump-mir"]).unwrap();
        assert_eq!(c3.stop_after, CompilePhase::Mir);

        let c4 = parse(&["cendol", "dummy.c", "--dump-cranelift"]).unwrap();
        assert_eq!(c4.stop_after, CompilePhase::Cranelift);

        let c5 = parse(&["cendol", "dummy.c"]).unwrap();
        assert_eq!(c5.stop_after, CompilePhase::EmitObject);
    }

    #[test]
    fn test_signed_overflow_mode() {
        // Default should be Wrap
        let c1 = parse(&["cendol", "dummy.c"]).unwrap();
        assert_eq!(c1.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Explicit -fwrapv
        let c2 = parse(&["cendol", "dummy.c", "-fwrapv"]).unwrap();
        assert_eq!(c2.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Explicit -fno-wrapv
        let c3 = parse(&["cendol", "dummy.c", "-fno-wrapv"]).unwrap();
        assert_eq!(c3.lang_options.signed_overflow_mode, SignedOverflowMode::Undefined);

        // Last one wins: -fwrapv -fno-wrapv -> Undefined
        let c4 = parse(&["cendol", "dummy.c", "-fwrapv", "-fno-wrapv"]).unwrap();
        assert_eq!(c4.lang_options.signed_overflow_mode, SignedOverflowMode::Undefined);

        // Last one wins: -fno-wrapv -fwrapv -> Wrap
        let c5 = parse(&["cendol", "dummy.c", "-fno-wrapv", "-fwrapv"]).unwrap();
        assert_eq!(c5.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Explicit -fstrict-overflow
        let c6 = parse(&["cendol", "dummy.c", "-fstrict-overflow"]).unwrap();
        assert_eq!(c6.lang_options.signed_overflow_mode, SignedOverflowMode::Undefined);

        // Explicit -fno-strict-overflow
        let c7 = parse(&["cendol", "dummy.c", "-fno-strict-overflow"]).unwrap();
        assert_eq!(c7.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Mix: -fstrict-overflow -fno-strict-overflow -> Wrap
        let c8 = parse(&["cendol", "dummy.c", "-fstrict-overflow", "-fno-strict-overflow"]).unwrap();
        assert_eq!(c8.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Mix: -fno-strict-overflow -fstrict-overflow -> Undefined
        let c9 = parse(&["cendol", "dummy.c", "-fno-strict-overflow", "-fstrict-overflow"]).unwrap();
        assert_eq!(c9.lang_options.signed_overflow_mode, SignedOverflowMode::Undefined);

        // Mix: -fwrapv -fstrict-overflow -> Undefined
        let c10 = parse(&["cendol", "dummy.c", "-fwrapv", "-fstrict-overflow"]).unwrap();
        assert_eq!(c10.lang_options.signed_overflow_mode, SignedOverflowMode::Undefined);

        // Mix: -fstrict-overflow -fwrapv -> Wrap
        let c11 = parse(&["cendol", "dummy.c", "-fstrict-overflow", "-fwrapv"]).unwrap();
        assert_eq!(c11.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Explicit -ftrapv
        let c12 = parse(&["cendol", "dummy.c", "-ftrapv"]).unwrap();
        assert_eq!(c12.lang_options.signed_overflow_mode, SignedOverflowMode::Trap);

        // Explicit -fno-trapv
        let c13 = parse(&["cendol", "dummy.c", "-fno-trapv"]).unwrap();
        assert_eq!(c13.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Last one wins: -ftrapv -fno-trapv -> Wrap
        let c14 = parse(&["cendol", "dummy.c", "-ftrapv", "-fno-trapv"]).unwrap();
        assert_eq!(c14.lang_options.signed_overflow_mode, SignedOverflowMode::Wrap);

        // Last one wins: -fno-trapv -ftrapv -> Trap
        let c15 = parse(&["cendol", "dummy.c", "-fno-trapv", "-ftrapv"]).unwrap();
        assert_eq!(c15.lang_options.signed_overflow_mode, SignedOverflowMode::Trap);
    }

    #[test]
    fn test_fvisibility_parsing() {
        let c1 = parse(&["cendol", "test.c", "-fvisibility=hidden"]).unwrap();
        assert_eq!(c1.lang_options.visibility, Visibility::Hidden);

        let c2 = parse(&["cendol", "test.c", "-fvisibility=default"]).unwrap();
        assert_eq!(c2.lang_options.visibility, Visibility::Default);

        let c3 = parse(&["cendol", "test.c", "-fvisibility=protected"]).unwrap();
        assert_eq!(c3.lang_options.visibility, Visibility::Protected);

        let c4 = parse(&["cendol", "test.c", "-fvisibility=internal"]).unwrap();
        assert_eq!(c4.lang_options.visibility, Visibility::Internal);

        let c5 = parse(&["cendol", "test.c", "-fvisibility=unknown"]);
        assert!(c5.is_err());
    }

    #[test]
    fn test_no_input_files() {
        let result = parse(&["cendol"]);
        assert!(result.is_err());
    }

    #[test]
    fn test_help_and_version() {
        let r1 = parse(&["cendol", "--help"]);
        assert!(matches!(r1, Err(ArgError::Help)));

        let r2 = parse(&["cendol", "--version"]);
        assert!(matches!(r2, Err(ArgError::Version)));
    }

    #[test]
    fn test_o_juxtaposed() {
        let config = parse(&["cendol", "test.c", "-oout"]).unwrap();
        assert_eq!(config.output_path, Some(PathBuf::from("out")));
    }

    #[test]
    fn test_wl_linker_args() {
        let config = parse(&["cendol", "test.c", "-Wl,-rpath,/usr/lib"]).unwrap();
        assert_eq!(config.linker_args, vec!["-Wl,-rpath,/usr/lib"]);
    }

    #[test]
    fn test_xlinker() {
        let config = parse(&["cendol", "test.c", "-Xlinker", "-rpath"]).unwrap();
        assert_eq!(config.linker_args, vec!["-Wl,-rpath"]);
    }

    #[test]
    fn test_pthread() {
        let config = parse(&["cendol", "test.c", "-pthread"]).unwrap();
        assert!(config.linker_args.contains(&"-Wl,-pthread".to_string()));
    }

    #[test]
    fn test_std_option() {
        let c1 = parse(&["cendol", "test.c", "-std=c23"]).unwrap();
        assert_eq!(c1.c_standard, CStandard::C23);

        let c2 = parse(&["cendol", "test.c", "-std=c11"]).unwrap();
        assert_eq!(c2.c_standard, CStandard::C11);
    }

    #[test]
    fn test_optimization_bare_o() {
        let config = parse(&["cendol", "test.c", "-O"]).unwrap();
        assert_eq!(config.optimization, Some("1".to_string()));
    }

    #[test]
    fn test_w_bare_maps_to_extra() {
        let config = parse(&["cendol", "test.c", "-W"]).unwrap();
        assert!(config.warnings.contains(&"extra".to_string()));
    }

    #[test]
    fn test_g_with_suffix() {
        let config = parse(&["cendol", "test.c", "-ggdb3"]).unwrap();
        assert!(config.debug_info);
    }

    #[test]
    fn test_double_dash_terminator() {
        let config = parse(&["cendol", "--", "-weird-file.c"]).unwrap();
        assert_eq!(config.input_files.len(), 1);
    }

    #[test]
    fn test_fpic_last_wins() {
        let c1 = parse(&["cendol", "test.c", "-fPIC"]).unwrap();
        assert!(c1.lang_options.fpic);

        let c2 = parse(&["cendol", "test.c", "-fno-PIC"]).unwrap();
        assert!(!c2.lang_options.fpic);

        let c3 = parse(&["cendol", "test.c", "-fPIC", "-fno-PIC"]).unwrap();
        assert!(!c3.lang_options.fpic);

        let c4 = parse(&["cendol", "test.c", "-fno-PIC", "-fPIC"]).unwrap();
        assert!(c4.lang_options.fpic);
    }

    #[test]
    fn test_unrecognized_f_flags_are_ignored() {
        let config = parse(&["cendol", "test.c", "-fno-stack-protector", "-fomit-frame-pointer"]).unwrap();
        assert!(config.ignored_f_flags.contains(&"no-stack-protector".to_string()));
        assert!(config.ignored_f_flags.contains(&"omit-frame-pointer".to_string()));
    }
}
