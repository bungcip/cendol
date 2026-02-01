//! Compiler driver module
//!
//! This module provides the main entry point for the C compiler,
//! coordinating the compilation pipeline from CLI parsing to output generation.

pub mod artifact;
pub mod cli;
pub mod compiler;

// Re-export public API
pub use cli::Cli;
pub use compiler::{CompilerDriver, DriverError};
