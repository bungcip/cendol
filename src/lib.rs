//! A C compiler implemented in Rust.

/// Contains the error types for the application.
pub mod error;
/// Contains the code generation components.
pub mod codegen;
/// Contains common data structures and types.
pub mod common;
pub mod parser;
/// Contains the preprocessor.
pub mod preprocessor;
