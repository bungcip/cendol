#![allow(unused_imports)]
//! A C compiler implemented in Rust.
pub mod file;
pub mod dumper;
pub mod source;

/// Contains the code generation components.
pub mod codegen;
/// Contains common data structures and types.
pub mod common;
/// Contains the compiler.
pub mod compiler;
/// Contains the error types for the application.
pub mod error;
/// Contains the logger.
pub mod logger;
pub mod parser;
/// Contains the preprocessor.
pub mod preprocessor;
/// Contains the semantic analyzer.
pub mod semantic;

pub mod types;

pub mod test_utils;

use source::{FileId, SourceLocation, SourceSpan};
use symbol_table::GlobalSymbol as StringId;
