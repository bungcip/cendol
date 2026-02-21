use cendol::driver::{Cli, CompilerDriver, DriverError};
use clap::Parser;

fn main() {
    env_logger::init();

    // Preprocess arguments to support single-dash long options specific to GCC/Clang compatibility.
    // Clap does not strictly support single-dash long options (e.g. -std=c99), so we manually
    // map them to double-dash options (e.g. --std=c99) before parsing.
    let args = std::env::args().map(|arg| {
        if arg.starts_with("-std=") || arg.starts_with("-target=") || arg.starts_with("-fuse-ld=") {
            format!("-{}", arg)
        } else if arg == "-pedantic" {
            "--pedantic".to_string()
        } else if arg == "-pedantic-errors" {
            "--pedantic-errors".to_string()
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
