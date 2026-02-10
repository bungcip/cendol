//! Code generation module.
//!
//! This module provides the complete code generation pipeline:
//! - MirGen: AST → MIR (Mid-level Intermediate Representation)
//! - ClifGen: MIR → Cranelift IR

pub mod clif_gen;
pub mod mir_gen;

pub(crate) mod mir_gen_expression;
pub(crate) mod mir_gen_initializer;
pub(crate) mod mir_gen_ops;

// Re-export key types for public API
pub use clif_gen::{ClifOutput, EmitKind};

// Re-export crate-internal types
pub(crate) use clif_gen::ClifGen;
pub(crate) use mir_gen::MirGen;
