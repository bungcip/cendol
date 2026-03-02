with open('src/driver/cli.rs', 'r') as f:
    content = f.read()

test_code = """
    #[test]
    fn test_cli_dump_flags_coverage() {
        use clap::Parser;

        let cli1 = Cli::parse_from(&["cendol", "dummy.c", "--dump-ast-after-parser"]);
        assert_eq!(cli1.into_config().unwrap().stop_after, CompilePhase::Parse);

        let cli2 = Cli::parse_from(&["cendol", "dummy.c", "--dump-ast-after-semantic-lowering"]);
        assert_eq!(cli2.into_config().unwrap().stop_after, CompilePhase::SemanticLowering);

        let cli3 = Cli::parse_from(&["cendol", "dummy.c", "--dump-mir"]);
        assert_eq!(cli3.into_config().unwrap().stop_after, CompilePhase::Mir);

        let cli4 = Cli::parse_from(&["cendol", "dummy.c", "--dump-cranelift"]);
        assert_eq!(cli4.into_config().unwrap().stop_after, CompilePhase::Cranelift);

        let cli5 = Cli::parse_from(&["cendol", "dummy.c"]);
        assert_eq!(cli5.into_config().unwrap().stop_after, CompilePhase::EmitObject);
    }
"""

if "test_cli_dump_flags_coverage" not in content:
    content = content.replace('use std::path::PathBuf;', 'use std::path::PathBuf;\n    use clap::Parser;')
    content = content.rsplit('}', 1)[0] + test_code + '\n}\n'
    with open('src/driver/cli.rs', 'w') as f:
        f.write(content)
