use crate::driver::artifact::CompilePhase;
use crate::driver::cli::CompileConfig;
use crate::driver::compiler::CompilerDriver;
use crate::lang_options::CStandard;

pub(crate) fn run_pass_c23(source: &str) {
    let mut config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::Mir);
    config.lang_options.c_standard = CStandard::C23;
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(CompilePhase::Mir);
    if result.is_err() {
        panic!("Compilation failed unexpectedly: {:?}", driver.get_diagnostics());
    }
}

pub(crate) fn run_fail_c23(source: &str, msg: &str) {
    let mut config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::Mir);
    config.lang_options.c_standard = CStandard::C23;
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(CompilePhase::Mir);
    assert!(result.is_err(), "Compilation should have failed");
    let has_msg = driver.get_diagnostics().iter().any(|d| d.message.contains(msg));
    if !has_msg {
        panic!(
            "Expected error message containing '{}', but got: {:?}",
            msg,
            driver.get_diagnostics()
        );
    }
}

#[test]
fn test_c23_bool_keywords() {
    let source = "
    int main() {
        bool a = true;
        bool b = false;
        return a + b;
    }
    ";
    run_pass_c23(source);
}

#[test]
fn test_c11_bool_keywords_identifiers() {
    let source = "
    int main() {
        int true = 1;
        int false = 0;
        int bool = true + false;
        return bool;
    }
    ";
    // This is valid C11 code without stdbool.h, should pass
    let mut config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::Mir);
    config.lang_options.c_standard = CStandard::C11;
    let mut driver = CompilerDriver::from_config(config);
    let result = driver.run_pipeline(CompilePhase::Mir);
    if result.is_err() {
        panic!("C11 compilation failed unexpectedly: {:?}", driver.get_diagnostics());
    }
}

#[test]
fn test_c23_bool_as_identifier_fails() {
    let source = "
    int main() {
        int true = 1;
        return true;
    }
    ";
    run_fail_c23(source, "Expected declarator or identifier after type specifier");
}
