use cendol::driver::{Cli, CompilerDriver, DriverError};
use clap::Parser;

fn main() {
    env_logger::init();

    // Preprocess arguments to support single-dash long options specific to GCC/Clang compatibility.
    // Clap does not strictly support single-dash long options (e.g. -std=c99), so we manually
    // map them to double-dash options (e.g. --std=c99) before parsing.
    let args = std::env::args().map(|arg| {
        if arg.starts_with("-std=")
            || arg.starts_with("-target=")
            || arg.starts_with("-fuse-ld=")
            || arg == "-rdynamic"
            || arg.starts_with("-fvisibility=")
        {
            format!("-{}", arg)
        } else if arg == "-pedantic" {
            "--pedantic".to_string()
        } else if arg == "-pedantic-errors" {
            "--pedantic-errors".to_string()
        } else if arg == "-fwrapv" {
            "--fwrapv".to_string()
        } else if arg == "-fno-wrapv" {
            "--fno-wrapv".to_string()
        } else if arg == "-fstrict-overflow" {
            "--fstrict-overflow".to_string()
        } else if arg == "-fno-strict-overflow" {
            "--fno-strict-overflow".to_string()
        } else if arg == "-ftrapv" {
            "--ftrapv".to_string()
        } else if arg == "-fno-trapv" {
            "--fno-trapv".to_string()
        } else if arg == "-fPIC" {
            "--fPIC".to_string()
        } else if arg == "-fno-PIC" {
            "--fno-PIC".to_string()
        } else if arg == "-O" {
            "-O1".to_string()
        } else if arg == "-W" {
            "-Wextra".to_string()
        } else if arg.starts_with("-g") && arg != "-g" {
            "-g".to_string()
        } else if arg == "-pthread" {
            "--linker-arg=-pthread".to_string()
        } else if arg == "-shared" {
            "--shared".to_string()
        } else if arg.starts_with("-Wl,") {
            format!("--linker-arg={}", arg)
        } else if arg == "-Xlinker" {
            "--linker-arg".to_string()
        } else {
            arg
        }
    });

    let cli = Cli::parse_from(args);

    match CompilerDriver::new(cli) {
        Ok(mut driver) => {
            match driver.run() {
                Ok(_) => std::process::exit(0),
                Err(e) => {
                    match e {
                        DriverError::IoError(e) => eprintln!("I/O error: {:?}", e),
                        DriverError::CompilationFailed => (), // diagnostic already printed by driver.run()
                        DriverError::LinkingFailed => (),     // error already printed by LinkGen
                    };
                    std::process::exit(1);
                }
            }
        }
        Err(e) => {
            eprintln!("Failed to initialize compiler: {}", e);
            std::process::exit(1);
        }
    }
}
