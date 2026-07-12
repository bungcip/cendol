use cendol::driver::cli::parse_args;
use cendol::driver::{CompilerDriver, DriverError};

fn main() {
    env_logger::init();

    let config = match parse_args() {
        Ok(config) => config,
        Err(e) => {
            e.print();
            std::process::exit(e.exit_code());
        }
    };

    let mut driver = CompilerDriver::from_config(config);
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
