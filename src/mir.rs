//! Mid-level Intermediate Representation (MIR) for C11 compiler.
//!
//! This module provides the MIR data structures and APIs for representing
//! C11 programs after semantic analysis. The MIR is designed to be:
//! - Typed: All entities have explicit types
//! - Explicit: All C semantics are made explicit
//! - Cranelift-friendly: Easy to lower to Cranelift IR
//! - Non-SSA: Uses basic blocks with explicit control flow

use serde::Serialize;
use std::num::NonZeroU32;

use crate::ast::NameId;
use crate::semantic::FieldLayout;

pub mod dumper;
pub mod validation;

macro_rules! mir_id {
    ($name:ident, $doc:expr) => {
        #[doc = $doc]
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
        #[repr(transparent)]
        pub struct $name(NonZeroU32);

        impl $name {
            #[inline]
            pub(crate) fn new(val: u32) -> Option<Self> {
                NonZeroU32::new(val).map(Self)
            }

            #[inline]
            pub(crate) fn get(self) -> u32 {
                self.0.get()
            }

            #[inline]
            pub(crate) fn index(self) -> usize {
                (self.0.get() - 1) as usize
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.0.get())
            }
        }
    };
}

mir_id!(GlobalId, "Unique identifier for MIR global variables");
mir_id!(MirFunctionId, "Unique identifier for MIR functions");
mir_id!(MirBlockId, "Unique identifier for MIR blocks");
mir_id!(MirStmtId, "Unique identifier for MIR statements");
mir_id!(LocalId, "Unique identifier for MIR locals");
mir_id!(TypeId, "Unique identifier for MIR types");
mir_id!(ConstValueId, "Unique identifier for MIR constant values");

/// Function linkage - distinguishes between internal, external, and imported functions
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub(crate) enum MirLinkage {
    Internal, // Defined in this module, not exported
    External, // Defined in this module, exported
    Import,   // Declared but defined elsewhere
}

/// MIR Module - Top-level container for MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MirModule {
    pub(crate) functions: Vec<MirFunctionId>,
    pub(crate) globals: Vec<GlobalId>,
    pub(crate) types: Vec<MirType>,
    pub(crate) constants: Vec<ConstValue>,
    pub(crate) pointer_width: u8, // Width of a pointer in bytes (e.g., 4 or 8)
}

impl MirModule {
    fn new() -> Self {
        Self {
            functions: Vec::new(),
            globals: Vec::new(),
            types: Vec::new(),
            constants: Vec::new(),
            pointer_width: 8, // Default to 64-bit pointers
        }
    }
}

/// MIR Function - Represents a C function in MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MirFunction {
    pub(crate) name: NameId,
    pub(crate) return_type: TypeId,
    pub(crate) params: Vec<LocalId>,

    pub(crate) linkage: MirLinkage,
    pub(crate) is_variadic: bool, // Track if this function is variadic

    // Only valid if linkage is Defined (Internal or External)
    pub(crate) locals: Vec<LocalId>,
    pub(crate) blocks: Vec<MirBlockId>,
    pub(crate) entry_block: Option<MirBlockId>,
}

impl MirFunction {
    fn new(name: NameId, return_type: TypeId, linkage: MirLinkage) -> Self {
        Self {
            name,
            return_type,
            params: Vec::new(),
            linkage,
            is_variadic: false,
            locals: Vec::new(),
            blocks: Vec::new(),
            entry_block: None,
        }
    }

    pub(crate) fn new_defined(name: NameId, return_type: TypeId, linkage: MirLinkage) -> Self {
        assert!(
            linkage != MirLinkage::Import,
            "Cannot create defined function with Import linkage"
        );
        Self::new(name, return_type, linkage)
    }

    fn new_extern(name: NameId, return_type: TypeId) -> Self {
        Self::new(name, return_type, MirLinkage::Import)
    }
}

/// MIR Block - Basic block with statements and terminator
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MirBlock {
    pub(crate) statements: Vec<MirStmtId>,
    pub(crate) terminator: Terminator,
}

impl MirBlock {
    pub(crate) fn new() -> Self {
        Self {
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        }
    }
}

/// MIR Statement - Individual operations within a block
/// Only contains side-effect operations, no control flow
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum MirStmt {
    Assign(Place, Rvalue),
    // Function calls - dest is None if void or result is ignored
    Call {
        target: CallTarget,
        args: Vec<Operand>,
        dest: Option<Place>,
    },
    BuiltinVaStart(Place, Operand),
    BuiltinVaEnd(Place),
    BuiltinVaCopy(Place, Place),
    AtomicStore(Operand, Operand, AtomicMemOrder),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) enum AtomicMemOrder {
    // Relaxed,
    // Consume,
    // Acquire,
    // Release,
    // AcqRel,
    SeqCst,
}

/// Terminator - Control flow terminators for basic blocks
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum Terminator {
    Goto(MirBlockId),
    If(Operand, MirBlockId, MirBlockId),
    Return(Option<Operand>),
    Unreachable,
    Trap,
}

/// Bitfield information for struct fields
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub(crate) struct BitFieldInfo {
    pub(crate) width: u16,
    pub(crate) offset: u16,
    pub(crate) is_signed: bool,
}

impl BitFieldInfo {
    pub(crate) fn truncate(&self, val: i64) -> i64 {
        let mask = if self.width == 64 {
            !0u64
        } else {
            (1u64 << self.width) - 1
        };
        let mask_signed = mask as i64;
        if self.is_signed && self.width < 64 {
            // Sign extend from bit_info.width
            let shift = 64 - self.width;
            ((val as u64) << shift) as i64 >> shift
        } else {
            val & mask_signed
        }
    }
}

/// Place - Represents a storage location (local variable or memory)
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum Place {
    Local(LocalId),
    Deref(Box<Operand>),
    Global(GlobalId),
    // Aggregate access
    StructField(Box<Place>, /* struct index */ usize, Option<BitFieldInfo>),
    ArrayIndex(Box<Place>, Box<Operand>),
}

/// Operand - Represents values used in MIR operations
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum Operand {
    Copy(Box<Place>),
    Constant(ConstValueId),
    // Address operations
    AddressOf(Box<Place>),
    // Type conversion
    Cast(TypeId, Box<Operand>),
}

/// Rvalue - Right-hand side values in assignments
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum Rvalue {
    Use(Operand),
    BinaryIntOp(BinaryIntOp, Operand, Operand),
    BinaryFloatOp(BinaryFloatOp, Operand, Operand),
    UnaryIntOp(UnaryIntOp, Operand),
    UnaryFloatOp(UnaryFloatOp, Operand),
    PtrAdd(Operand, Operand),
    PtrSub(Operand, Operand),
    PtrDiff(Operand, Operand),
    StructLiteral(Vec<(usize, Operand)>),
    ArrayLiteral(Vec<Operand>),
    BuiltinVaArg(Place, TypeId),
    AtomicLoad(Operand, AtomicMemOrder),
    AtomicExchange(Operand, Operand, AtomicMemOrder),
    AtomicCompareExchange(Operand, Operand, Operand, bool, AtomicMemOrder, AtomicMemOrder),
    AtomicFetchOp(BinaryIntOp, Operand, Operand, AtomicMemOrder),
}

/// Call target - represents how a function is called
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum CallTarget {
    Direct(MirFunctionId), // Direct call to a known function
    Indirect(Operand),     // Indirect call via function pointer
}

/// Integer binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub(crate) enum BinaryIntOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    LShift,
    RShift,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinaryIntOp {
    pub(super) fn is_comparison(&self) -> bool {
        matches!(self, Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge)
    }
}

/// Floating-point binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub(crate) enum BinaryFloatOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl BinaryFloatOp {
    pub(super) fn is_comparison(&self) -> bool {
        matches!(self, Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge)
    }
}

/// Integer unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub(crate) enum UnaryIntOp {
    Neg,
    BitwiseNot,
    LogicalNot,
    Popcount,
    Clz,
    Ctz,
    Ffs,
    Bswap16,
    Bswap32,
    Bswap64,
}

/// Floating-point unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub(crate) enum UnaryFloatOp {
    Neg,
    Abs,
}

/// Type - MIR type system
// - All Struct/Union have a stable NameId
// - No anonymous record types exist in MIR
// - No anonymous members exist in MIR
// - Field names are unique within a record
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum MirType {
    Void,
    Bool,

    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    F80, // x87 extended precision (padded to 128 bits)
    F128,
    Pointer {
        pointee: TypeId,
    },
    Array {
        element: TypeId,
        size: usize,
        layout: MirArrayLayout,
    },
    Function {
        return_type: TypeId,
        params: Vec<TypeId>,
        is_variadic: bool,
    },
    Record {
        name: NameId,
        field_types: Vec<TypeId>,
        field_names: Vec<NameId>,
        is_union: bool,
        layout: MirRecordLayout,
    },
}
impl MirType {
    pub(super) fn is_signed(&self) -> bool {
        matches!(self, MirType::I8 | MirType::I16 | MirType::I32 | MirType::I64)
    }

    pub(super) fn is_void(&self) -> bool {
        matches!(self, MirType::Void)
    }

    pub(super) fn is_bool(&self) -> bool {
        matches!(self, MirType::Bool)
    }

    pub(super) fn is_pointer(&self) -> bool {
        matches!(self, MirType::Pointer { .. })
    }

    pub(super) fn is_float(&self) -> bool {
        matches!(self, MirType::F32 | MirType::F64 | MirType::F80 | MirType::F128)
    }

    pub(super) fn is_aggregate(&self) -> bool {
        matches!(
            self,
            MirType::Record { .. } | MirType::Array { .. } | MirType::F80 | MirType::F128
        )
    }

    pub(super) fn is_int(&self) -> bool {
        matches!(
            self,
            MirType::I8
                | MirType::I16
                | MirType::I32
                | MirType::I64
                | MirType::U8
                | MirType::U16
                | MirType::U32
                | MirType::U64
                | MirType::Bool
        )
    }

    pub(super) fn is_complex(&self) -> bool {
        if let MirType::Record { name, .. } = self {
            name.as_str().starts_with("_Complex")
        } else {
            false
        }
    }

    pub(super) fn width(&self) -> u32 {
        match self {
            MirType::I8 | MirType::U8 | MirType::Bool => 8,
            MirType::I16 | MirType::U16 => 16,
            MirType::I32 | MirType::U32 | MirType::F32 => 32,
            MirType::I64 | MirType::U64 | MirType::F64 => 64,
            MirType::F80 | MirType::F128 => 128,
            MirType::Pointer { .. } => 64, // Assume 64-bit pointers
            _ => 0,                        // Others have no intrinsic "width" in this context
        }
    }

    /// Truncate an integer value to the width of this type.
    /// Handles sign extension if this is a signed type.
    pub(super) fn truncate_int(&self, val: i64) -> i64 {
        if self.is_bool() {
            return (val != 0) as i64;
        }

        if !self.is_int() && !self.is_pointer() {
            return val;
        }

        let width = self.width();
        if width >= 64 {
            return val;
        }

        // Apply bitmask for the width
        let mask = if width > 0 { (1u64 << width) - 1 } else { 0 };
        let truncated = (val as u64) & mask;

        if self.is_signed() {
            // Sign-extend if the MSB of the truncated value is set
            let sign_bit = 1u64 << (width - 1);
            if (truncated & sign_bit) != 0 {
                // To sign-extend, we set all bits above 'width' to 1
                return (truncated | !mask) as i64;
            }
        }

        truncated as i64
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MirFieldLayout {
    pub(crate) offset: u64,
    pub(crate) bit_width: Option<u16>,
    pub(crate) bit_offset: Option<u16>,
    pub(crate) is_signed: bool,
}

impl MirFieldLayout {
    pub(crate) fn new(offset: u64) -> Self {
        Self {
            offset,
            bit_width: None,
            bit_offset: None,
            is_signed: false,
        }
    }

    pub(crate) fn signed(self, value: bool) -> Self {
        Self {
            offset: self.offset,
            bit_offset: self.bit_offset,
            bit_width: self.bit_width,
            is_signed: value,
        }
    }

    pub(crate) fn from(fl: &FieldLayout) -> Self {
        Self {
            offset: fl.offset,
            bit_width: fl.bit_width,
            bit_offset: fl.bit_offset,
            is_signed: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MirRecordLayout {
    pub(crate) size: u64,
    pub(crate) align: u16,
    pub(crate) fields: Vec<MirFieldLayout>,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub(crate) struct MirArrayLayout {
    pub(crate) size: u64,
    pub(crate) align: u16,
    pub(crate) stride: u64,
}

/// Constant Value Kind - discriminant for ConstValue
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) enum ConstValueKind {
    Int(i64),
    Float(f64),
    Bool(bool),
    Null, // pointer null
    Zero, // memset / padding / zero-init
    // Aggregate constants
    StructLiteral(Vec<(usize, ConstValueId)>),
    ArrayLiteral(Vec<ConstValueId>),
    // Address constants
    GlobalAddress(GlobalId, /* offset */ i64),
    FunctionAddress(MirFunctionId),
}

/// Constant Value - Literal values in MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct ConstValue {
    pub(crate) ty: TypeId,
    pub(crate) kind: ConstValueKind,
}

/// Local - Represents a local variable or parameter
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub(crate) struct Local {
    pub(crate) name: Option<NameId>,
    pub(crate) type_id: TypeId,
    pub(crate) is_param: bool,
    pub(crate) alignment: Option<u16>, // Alignment in bytes
}

impl Local {
    pub(crate) fn new(name: Option<NameId>, type_id: TypeId, is_param: bool) -> Self {
        Self {
            name,
            type_id,
            is_param,
            alignment: None,
        }
    }
}

/// Global - Represents a global variable
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub(crate) struct Global {
    pub(crate) name: NameId,
    pub(crate) type_id: TypeId,
    pub(crate) is_constant: bool,
    pub(crate) is_tls: bool,
    pub(crate) initial_value: Option<ConstValueId>,
    pub(crate) alignment: Option<u16>, // Max alignment in bytes
    pub(crate) linkage: MirLinkage,
}

impl Global {
    pub(crate) fn new(name: NameId, type_id: TypeId, is_constant: bool, is_tls: bool, linkage: MirLinkage) -> Self {
        Self {
            name,
            type_id,
            is_constant,
            is_tls,
            initial_value: None,
            alignment: None,
            linkage,
        }
    }
}

/// MIR Builder - Builds MIR from AST
pub(crate) struct MirBuilder {
    module: MirModule,
    current_function: Option<MirFunctionId>,
    current_block: Option<MirBlockId>,
    next_local_id: u32,
    next_block_id: u32,
    next_stmt_id: u32,
    next_global_id: u32,
    next_type_id: u32,
    next_const_id: u32,
    anonymous_global_counter: u32,
    // State tracking
    functions: Vec<MirFunction>,
    blocks: Vec<MirBlock>,
    locals: Vec<Local>,
    globals: Vec<Global>,
    types: Vec<MirType>,
    constants: Vec<ConstValue>,
    // Statement storage with ID mapping
    statements: Vec<MirStmt>,
}

/// Complete semantic analysis output containing the full MIR program representation
/// Includes all functions, blocks, instructions, and type definitions.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub(crate) struct MirProgram {
    pub(crate) module: MirModule,
    pub(crate) functions: Vec<MirFunction>,
    pub(crate) blocks: Vec<MirBlock>,
    pub(crate) locals: Vec<Local>,
    pub(crate) globals: Vec<Global>,
    pub(crate) types: Vec<MirType>,
    pub(crate) constants: Vec<ConstValue>,
    pub(crate) statements: Vec<MirStmt>,
    pub(crate) pointer_width: u8,
}

impl MirProgram {
    pub(crate) fn get_type(&self, id: TypeId) -> &MirType {
        self.types.get(id.index()).expect("ICE: Type ID not found")
    }
    pub(crate) fn get_local(&self, id: LocalId) -> &Local {
        self.locals.get(id.index()).expect("ICE: Local ID not found")
    }

    pub(crate) fn get_constant(&self, id: ConstValueId) -> &ConstValue {
        self.constants.get(id.index()).expect("ICE: Constant ID not found")
    }

    pub(crate) fn get_statement(&self, id: MirStmtId) -> &MirStmt {
        self.statements.get(id.index()).expect("ICE: Statement ID not found")
    }
    pub(crate) fn get_function(&self, id: MirFunctionId) -> &MirFunction {
        self.functions.get(id.index()).expect("ICE: Function ID not found")
    }
    pub(crate) fn get_global(&self, id: GlobalId) -> &Global {
        self.globals.get(id.index()).expect("ICE: Global ID not found")
    }
    pub(crate) fn get_block(&self, id: MirBlockId) -> &MirBlock {
        self.blocks.get(id.index()).expect("ICE: Block ID not found")
    }
}

impl MirBuilder {
    pub(crate) fn new(pointer_width: u8) -> Self {
        let mut module = MirModule::new();
        module.pointer_width = pointer_width;
        Self {
            module,
            current_function: None,
            current_block: None,
            next_local_id: 1,
            next_block_id: 1,
            next_stmt_id: 1,
            next_global_id: 1,
            next_type_id: 1,
            next_const_id: 1,
            anonymous_global_counter: 0,
            functions: Vec::new(),
            blocks: Vec::new(),
            locals: Vec::new(),
            globals: Vec::new(),
            types: Vec::new(),
            constants: Vec::new(),
            statements: Vec::new(),
        }
    }

    pub(crate) fn create_local(&mut self, name: Option<NameId>, type_id: TypeId, is_param: bool) -> LocalId {
        let local_id = LocalId::new(self.next_local_id).unwrap();
        self.next_local_id += 1;

        let local = Local::new(name, type_id, is_param);
        self.locals.push(local);

        if let Some(func_id) = self.current_function
            && let Some(func) = self.functions.get_mut(func_id.index())
        {
            if is_param {
                func.params.push(local_id);
            } else {
                func.locals.push(local_id);
            }
        }

        local_id
    }

    pub(crate) fn set_local_alignment(&mut self, local_id: LocalId, alignment: u16) {
        if let Some(local) = self.locals.get_mut(local_id.index()) {
            local.alignment = Some(alignment);
        }
    }

    /// Create a new basic block
    pub(crate) fn create_block(&mut self) -> MirBlockId {
        let func_id = self.current_function.expect("no current function");
        let func = &self.functions[func_id.index()];

        assert!(
            func.linkage != MirLinkage::Import,
            "cannot create blocks for extern function"
        );

        let block_id = MirBlockId::new(self.next_block_id).unwrap();
        self.next_block_id += 1;

        let block = MirBlock::new();
        self.blocks.push(block);

        if let Some(func) = self.functions.get_mut(func_id.index()) {
            func.blocks.push(block_id);
        }

        block_id
    }

    /// Add a statement to the current block
    pub(crate) fn add_stmt(&mut self, stmt: MirStmt) -> MirStmtId {
        let stmt_id = MirStmtId::new(self.next_stmt_id).unwrap();
        self.next_stmt_id += 1;

        // Store statement
        self.statements.push(stmt);

        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get_mut(block_id.index())
        {
            // Only add statement if the block is not yet terminated
            if matches!(block.terminator, Terminator::Unreachable) {
                block.statements.push(stmt_id);
            }
        }

        stmt_id
    }

    /// Set the terminator for the current block
    pub(crate) fn set_terminator(&mut self, terminator: Terminator) {
        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get_mut(block_id.index())
        {
            // Only overwrite if the current terminator is Unreachable (default)
            // This preserves existing control flow (e.g. from goto) and prevents
            // overwriting it with subsequent unreachable terminators.
            if matches!(block.terminator, Terminator::Unreachable) {
                block.terminator = terminator;
            }
        }
    }

    /// Set the current block
    pub(crate) fn set_current_block(&mut self, block_id: MirBlockId) {
        self.current_block = Some(block_id);
    }

    /// Check if the current block has a non-unreachable terminator
    /// Since terminators always exist, this checks if the terminator is meaningful
    /// (i.e., not just the default Unreachable terminator)
    pub(crate) fn current_block_has_terminator(&self) -> bool {
        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get(block_id.index())
        {
            return !matches!(block.terminator, Terminator::Unreachable);
        }
        false
    }

    /// Declare a function (extern - no body)
    pub(crate) fn declare_function(
        &mut self,
        name: NameId,
        param_types: Vec<TypeId>,
        return_type: TypeId,
        is_variadic: bool,
    ) -> MirFunctionId {
        let func_id = MirFunctionId::new(self.functions.len() as u32 + 1).unwrap();
        let mut func = MirFunction::new_extern(name, return_type);
        func.is_variadic = is_variadic;

        // Create locals for each parameter.
        // Temporarily clear current_function so these params don't get added to the function currently being compiled.
        let saved_func = self.current_function.take();
        for (i, &param_type) in param_types.iter().enumerate() {
            let param_name = Some(NameId::new(format!("param{}", i)));
            let local_id = self.create_local(param_name, param_type, true);
            func.params.push(local_id);
        }
        self.current_function = saved_func;

        self.functions.push(func);
        self.module.functions.push(func_id);

        func_id
    }

    /// Define a function (has body)
    pub(crate) fn define_function(
        &mut self,
        name: NameId,
        param_types: Vec<TypeId>,
        return_type: TypeId,
        is_variadic: bool,
        linkage: MirLinkage,
    ) -> MirFunctionId {
        let func_id = MirFunctionId::new(self.functions.len() as u32 + 1).unwrap();
        let mut func = MirFunction::new_defined(name, return_type, linkage);
        func.is_variadic = is_variadic;

        // Create locals for each parameter
        for (i, &param_type) in param_types.iter().enumerate() {
            let param_name = Some(NameId::new(format!("param{}", i)));
            let local_id = self.create_local(param_name, param_type, true);
            func.params.push(local_id);
        }

        self.functions.push(func);
        self.module.functions.push(func_id);

        func_id
    }

    /// Set current function
    pub(crate) fn set_current_function(&mut self, func_id: MirFunctionId) {
        self.current_function = Some(func_id);
        if let Some(func) = self.functions.get(func_id.index())
            && let Some(entry_block) = func.entry_block
        {
            self.current_block = Some(entry_block);
        }
    }

    /// Create a new global variable with initial value
    pub(crate) fn create_global_with_init(
        &mut self,
        name: NameId,
        type_id: TypeId,
        is_constant: bool,
        is_tls: bool,
        linkage: MirLinkage,
        initial_value: Option<ConstValueId>,
    ) -> GlobalId {
        let global_id = GlobalId::new(self.next_global_id).unwrap();
        self.next_global_id += 1;

        let mut global = Global::new(name, type_id, is_constant, is_tls, linkage);
        global.initial_value = initial_value;
        self.globals.push(global);
        self.module.globals.push(global_id);

        global_id
    }

    pub(crate) fn set_global_initializer(&mut self, global_id: GlobalId, init_id: ConstValueId) {
        if let Some(global) = self.globals.get_mut(global_id.index()) {
            global.initial_value = Some(init_id);
        }
    }

    pub(crate) fn set_global_alignment(&mut self, global_id: GlobalId, alignment: u16) {
        if let Some(global) = self.globals.get_mut(global_id.index()) {
            global.alignment = Some(alignment);
        }
    }

    /// Add a type to the module with interning
    pub(crate) fn add_type(&mut self, mir_type: MirType) -> TypeId {
        // Check if type already exists (type interning)
        for (i, existing_type) in self.types.iter().enumerate() {
            if existing_type == &mir_type {
                return TypeId::new((i + 1) as u32).unwrap();
            }
        }

        // Type doesn't exist, create new one
        let type_id = TypeId::new(self.next_type_id).unwrap();
        self.next_type_id += 1;

        self.types.push(mir_type.clone());
        self.module.types.push(mir_type);

        type_id
    }

    /// Update an existing type previously inserted with `add_type`.
    /// This replaces the type entry in both the internal map and the module vector.
    pub(crate) fn update_type(&mut self, type_id: TypeId, mir_type: MirType) {
        self.types[type_id.index()] = mir_type.clone();
        let idx = (type_id.get() - 1) as usize;
        if idx < self.module.types.len() {
            self.module.types[idx] = mir_type;
        }
    }

    pub(crate) fn get_type(&self, type_id: TypeId) -> &MirType {
        self.types
            .get(type_id.index())
            .expect("Type ID not found in MirBuilder")
    }

    /// Create a constant value
    pub(crate) fn create_constant(&mut self, ty: TypeId, kind: ConstValueKind) -> ConstValueId {
        let const_id = ConstValueId::new(self.next_const_id).unwrap();
        self.next_const_id += 1;

        let value = ConstValue { ty, kind };
        self.constants.push(value.clone());
        self.module.constants.push(value);

        const_id
    }

    /// Consumes the builder and returns all the generated MIR components.
    /// This is the preferred way to get the final MIR, as it avoids cloning.
    pub(crate) fn consume(self) -> MirProgram {
        let pointer_width = self.module.pointer_width;
        MirProgram {
            module: self.module,
            functions: self.functions,
            blocks: self.blocks,
            locals: self.locals,
            globals: self.globals,
            types: self.types,
            constants: self.constants,
            statements: self.statements,
            pointer_width,
        }
    }

    /// Get all functions for validation
    pub(crate) fn get_functions(&self) -> &Vec<MirFunction> {
        &self.functions
    }

    /// Get all constants for validation
    pub(crate) fn get_constants(&self) -> &Vec<ConstValue> {
        &self.constants
    }

    pub(crate) fn get_function(&self, id: MirFunctionId) -> &MirFunction {
        self.functions.get(id.index()).expect("ICE: Function ID not found")
    }

    pub(crate) fn get_global(&self, id: GlobalId) -> &Global {
        self.globals.get(id.index()).expect("ICE: Global ID not found")
    }

    pub(crate) fn get_local(&self, id: LocalId) -> &Local {
        self.locals.get(id.index()).expect("ICE: Local ID not found")
    }

    pub(crate) fn get_constant(&self, id: ConstValueId) -> &ConstValue {
        self.constants.get(id.index()).expect("ICE: Constant ID not found")
    }

    /// Set the entry block for a function
    pub(crate) fn set_function_entry_block(&mut self, func_id: MirFunctionId, block_id: MirBlockId) {
        if let Some(func) = self.functions.get_mut(func_id.index()) {
            assert!(func.linkage != MirLinkage::Import);
            func.entry_block = Some(block_id);
        }
    }

    pub(crate) fn get_next_anon_global_name(&mut self) -> NameId {
        let name = format!(".L.str{}", self.anonymous_global_counter);
        self.anonymous_global_counter += 1;
        NameId::new(name)
    }
}
