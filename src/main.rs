use cendol::driver::{Cli, CompilerDriver};
use clap::Parser;

fn main() {
    env_logger::init();
    let cli = Cli::parse();

    match CompilerDriver::new(cli) {
        Ok(mut driver) => {
            if let Err(e) = driver.run() {
                eprintln!("Compilation failed: {:?}", e);
                std::process::exit(1);
            }
        }
        Err(e) => {
            eprintln!("Failed to initialize compiler: {}", e);
            std::process::exit(1);
        }
    }
}
