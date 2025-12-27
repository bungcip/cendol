use cendol::driver::{Cli, CompilerDriver, DriverError};
use clap::Parser;

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    match CompilerDriver::new(cli) {
        Ok(mut driver) => {
            match driver.run() {
                Ok(_) => std::process::exit(0),
                Err(e) => {
                    match e {
                        DriverError::IoError(e) => eprintln!("I/O error: {:?}", e),
                        DriverError::CompilationFailed => (), // diagnostic already printed by driver.run()
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
