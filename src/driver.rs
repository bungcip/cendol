//! Compiler driver module
//!
//! This module provides the main entry point for the C compiler,
//! coordinating the compilation pipeline from CLI parsing to output generation.

pub mod cli;
pub mod compiler;
pub mod output;

// Re-export public API
pub use cli::Cli;
pub use compiler::{CompilerDriver, CompilerError};
