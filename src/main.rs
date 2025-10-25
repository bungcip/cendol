use cendol::compiler::{Cli, Compiler};
use cendol::error::{Report, report};
use clap::Parser as ClapParser;
use std::process::exit;

/// The main entry point for the application.
///
/// Parses command-line arguments and runs the compiler.
fn main() {
    if let Err(report_data) = run() {
        report(&report_data);
        exit(1);
    }
}

/// Runs the compiler.
///
/// This function reads the input file, preprocesses it, parses the tokens,
/// generates code, and optionally links the output.
///
/// # Returns
///
/// A `Result` which is `Ok` on success or an `Error` on failure.
fn run() -> Result<(), Report> {
    let cli = Cli::parse();
    let mut compiler = Compiler::new(&cli);
    compiler.compile(&cli)
}
