//! Compiler driver module
//!
//! This module provides the main entry point for the C compiler,
//! coordinating the compilation pipeline from CLI parsing to output generation.

pub mod artifact;
pub mod cli;
pub mod compiler;

// Re-export public API
pub use artifact::CompilePhase;
pub use cli::CompileConfig;
pub use compiler::{CompilerDriver, DriverError};
