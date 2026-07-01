//! Inline assembly data structures.

use crate::ir::entities::InlineAsmId;
use alloc::string::String;
use alloc::vec::Vec;
use cranelift_entity::PrimaryMap;

#[cfg(feature = "enable-serde")]
use serde_derive::{Deserialize, Serialize};

/// Describes an inline assembly operand constraint.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub enum AsmConstraintKind {
    /// Any general-purpose register.
    GeneralReg,
    /// Any floating-point register.
    FloatReg,
    /// A specific physical register by name (e.g. "rax", "rcx").
    FixedReg(String),
    /// A memory operand.
    Memory,
    /// An immediate operand.
    Immediate,
}

/// A single operand for an inline assembly block.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct AsmOperand {
    /// The constraint for this operand.
    pub constraint: AsmConstraintKind,
    /// True if this operand is written to (output).
    pub is_output: bool,
    /// True if this operand is both read and written.
    pub is_read_write: bool,
}

/// Data associated with an inline assembly instruction.
///
/// This is stored in the `DataFlowGraph` and referenced by `InlineAsmId`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct InlineAsmData {
    /// The assembly template string with placeholders like `$0`, `$1`.
    pub template: String,
    /// Constraints for each operand (inputs and outputs).
    pub operands: Vec<AsmOperand>,
    /// List of clobbered register names (e.g. "rax", "memory", "cc").
    pub clobbers: Vec<String>,
    /// If true, this assembly block has side effects and must not be optimized away.
    pub is_volatile: bool,
}

/// A set of inline assembly blocks, stored in the DFG.
#[derive(Clone, Debug, PartialEq, Hash)]
#[cfg_attr(feature = "enable-serde", derive(Serialize, Deserialize))]
pub struct InlineAsmSet {
    inline_asms: PrimaryMap<InlineAsmId, InlineAsmData>,
}

impl InlineAsmSet {
    /// Create an empty set.
    pub fn new() -> Self {
        Self {
            inline_asms: PrimaryMap::new(),
        }
    }

    /// Add a new inline assembly block and return its id.
    pub fn push(&mut self, data: InlineAsmData) -> InlineAsmId {
        self.inline_asms.push(data)
    }

    /// Get the data for an inline assembly block.
    pub fn get(&self, id: InlineAsmId) -> &InlineAsmData {
        &self.inline_asms[id]
    }

    /// Clear all inline assembly data.
    pub fn clear(&mut self) {
        self.inline_asms.clear();
    }
}
