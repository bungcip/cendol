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

pub mod analyzer;
pub mod lower;
pub mod symbol_table;

// Re-export key types for public API
pub use analyzer::SemanticAnalyzer;
pub use lower::{DeclSpecInfo, LowerCtx};
pub use symbol_table::{Scope, ScopeId, ScopeKind, SymbolTable};
