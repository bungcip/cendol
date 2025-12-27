//! Semantic analysis module.
//!
//! This module provides comprehensive semantic analysis for C11 code, including:
//! - Symbol collection and scope management
//! - Name resolution
//! - Type checking
//! - Semantic validation
//! - MIR construction with multi-declarator support
//!
//! The analysis is performed in distinct phases using the visitor pattern
//! for clean separation of concerns and maintainable code.

pub mod lowerer;
pub mod resolver;
pub mod symbol_table;
#[cfg(test)]
pub mod tests_mir;
#[cfg(test)]
pub mod tests_resolver;
#[cfg(test)]
pub mod tests_type_checker;
pub mod type_checker;

// Re-export key types for public API
pub use lowerer::AstToMirLowerer;
pub use symbol_table::{Namespace, ScopeId, ScopeKind, SymbolTable};
