use crate::driver::artifact::CompilePhase;
use crate::driver::cli::{Cli, CompileConfig, PathOrBuffer};
use crate::driver::compiler::CompilerDriver;
use crate::lang_options::Visibility;
use clap::Parser;

#[test]
fn test_visibility_cli_parsing() {
    // Test parsing of single-dash option mapping via args processing
    // Simulate main.rs args preprocessing
    let original_args = vec![
        "cendol".to_string(),
        "test.c".to_string(),
        "-fvisibility=hidden".to_string(),
    ];
    let preprocessed_args: Vec<String> = original_args
        .into_iter()
        .map(|arg| {
            if arg.starts_with("-std=")
                || arg.starts_with("-target=")
                || arg.starts_with("-fuse-ld=")
                || arg == "-rdynamic"
                || arg.starts_with("-fvisibility=")
            {
                format!("-{}", arg)
            } else {
                arg
            }
        })
        .collect();

    let cli = Cli::parse_from(preprocessed_args);
    assert_eq!(cli.fvisibility, Some(Visibility::Hidden));
    let config = cli.into_config().unwrap();
    assert_eq!(config.lang_options.visibility, Visibility::Hidden);

    // Test other visibility options
    let cli_default = Cli::parse_from(["cendol", "test.c", "--fvisibility=default"]);
    assert_eq!(cli_default.fvisibility, Some(Visibility::Default));
    assert_eq!(
        cli_default.into_config().unwrap().lang_options.visibility,
        Visibility::Default
    );

    let cli_protected = Cli::parse_from(["cendol", "test.c", "--fvisibility=protected"]);
    assert_eq!(cli_protected.fvisibility, Some(Visibility::Protected));
    assert_eq!(
        cli_protected.into_config().unwrap().lang_options.visibility,
        Visibility::Protected
    );

    let cli_internal = Cli::parse_from(["cendol", "test.c", "--fvisibility=internal"]);
    assert_eq!(cli_internal.fvisibility, Some(Visibility::Internal));
    assert_eq!(
        cli_internal.into_config().unwrap().lang_options.visibility,
        Visibility::Internal
    );
}

#[test]
fn test_visibility_invalid_cli() {
    let res = Cli::try_parse_from(["cendol", "test.c", "--fvisibility=unknown"]);
    assert!(res.is_err());
}

#[test]
fn test_lower_mir_linkage_mapping() {
    use crate::codegen::clif_gen::lower_mir_linkage;
    use crate::mir::MirLinkage;
    use cranelift_module::Linkage;

    // Internal linkage always maps to Local linkage regardless of visibility
    assert_eq!(
        lower_mir_linkage(MirLinkage::Internal, Visibility::Default),
        Linkage::Local
    );
    assert_eq!(
        lower_mir_linkage(MirLinkage::Internal, Visibility::Hidden),
        Linkage::Local
    );

    // Import linkage always maps to Import linkage regardless of visibility
    assert_eq!(
        lower_mir_linkage(MirLinkage::Import, Visibility::Default),
        Linkage::Import
    );
    assert_eq!(
        lower_mir_linkage(MirLinkage::Import, Visibility::Hidden),
        Linkage::Import
    );

    // External linkage maps depending on visibility:
    assert_eq!(
        lower_mir_linkage(MirLinkage::External, Visibility::Default),
        Linkage::Export
    );
    assert_eq!(
        lower_mir_linkage(MirLinkage::External, Visibility::Hidden),
        Linkage::Hidden
    );
    assert_eq!(
        lower_mir_linkage(MirLinkage::External, Visibility::Protected),
        Linkage::Export
    );
    assert_eq!(
        lower_mir_linkage(MirLinkage::External, Visibility::Internal),
        Linkage::Hidden
    );
}

#[test]
fn test_compilation_with_hidden_visibility() {
    let source = "int foo(void) { return 42; }";
    let mut config = CompileConfig {
        input_files: vec![PathOrBuffer::Buffer("test.c".into(), source.as_bytes().to_vec())],
        ..Default::default()
    };
    config.lang_options.visibility = Visibility::Hidden;
    config.stop_after = CompilePhase::Cranelift;
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run();
    assert!(result.is_ok());
}

#[test]
fn test_pragma_visibility_codegen() {
    use crate::tests::test_utils::run_pipeline_to_mir;
    let source = r#"
        #pragma GCC visibility push(hidden)
        void hidden_func(void) {}
        int hidden_var = 123;
        #pragma GCC visibility pop

        void default_func(void) {}
        int default_var = 456;
    "#;
    let outputs = run_pipeline_to_mir(source);
    let artifact = outputs.units.values().next().unwrap();
    let mir = artifact.mir_program.as_ref().unwrap();

    let hidden_func = mir.functions.iter().find(|f| f.name.as_str() == "hidden_func").unwrap();
    assert_eq!(hidden_func.visibility, Visibility::Hidden);

    let hidden_var = mir.globals.iter().find(|g| g.name.as_str() == "hidden_var").unwrap();
    assert_eq!(hidden_var.visibility, Visibility::Hidden);

    let default_func = mir
        .functions
        .iter()
        .find(|f| f.name.as_str() == "default_func")
        .unwrap();
    assert_eq!(default_func.visibility, Visibility::Default);

    let default_var = mir.globals.iter().find(|g| g.name.as_str() == "default_var").unwrap();
    assert_eq!(default_var.visibility, Visibility::Default);
}
