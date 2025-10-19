//! A C compiler implemented in Rust.

pub mod file;

/// Contains the code generation components.
pub mod codegen;
/// Contains common data structures and types.
pub mod common;
/// Contains the error types for the application.
pub mod error;
pub mod parser;
/// Contains the preprocessor.
pub mod preprocessor;
