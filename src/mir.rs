//! Mid-level Intermediate Representation (MIR) for C11 compiler.
//!
//! This module provides the MIR data structures and APIs for representing
//! C11 programs after semantic analysis. The MIR is designed to be:
//! - Typed: All entities have explicit types
//! - Explicit: All C semantics are made explicit
//! - Cranelift-friendly: Easy to lower to Cranelift IR
//! - Non-SSA: Uses basic blocks with explicit control flow

use hashbrown::HashMap;
use serde::Serialize;
use std::num::NonZeroU32;

use crate::ast::NameId;

pub mod dumper;
pub mod validation;

/// Unique identifier for MIR global variables
pub type GlobalId = NonZeroU32;

/// Unique identifier for MIR modules
pub type MirModuleId = NonZeroU32;

/// Unique identifier for MIR functions
pub type MirFunctionId = NonZeroU32;

/// Unique identifier for MIR blocks
pub type MirBlockId = NonZeroU32;

/// Unique identifier for MIR statements
pub type MirStmtId = NonZeroU32;

/// Unique identifier for MIR locals
pub type LocalId = NonZeroU32;

/// Unique identifier for MIR types
pub type TypeId = NonZeroU32;

/// Unique identifier for MIR constant values
pub type ConstValueId = NonZeroU32;

/// Function kind - distinguishes between defined and extern functions
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub enum MirFunctionKind {
    Extern,
    DefinedInternal,
    DefinedExternal,
}

/// MIR Module - Top-level container for MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MirModule {
    pub id: MirModuleId,
    pub functions: Vec<MirFunctionId>,
    pub globals: Vec<GlobalId>,
    pub types: Vec<MirType>,
    pub constants: Vec<ConstValue>,
    pub pointer_width: u8, // Width of a pointer in bytes (e.g., 4 or 8)
}

impl MirModule {
    pub(crate) fn new(id: MirModuleId) -> Self {
        Self {
            id,
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
pub struct MirFunction {
    pub id: MirFunctionId,
    pub name: NameId,
    pub return_type: TypeId,
    pub params: Vec<LocalId>,

    pub kind: MirFunctionKind,
    pub is_variadic: bool, // Track if this function is variadic

    // Only valid if kind is Defined
    pub locals: Vec<LocalId>,
    pub blocks: Vec<MirBlockId>,
    pub entry_block: Option<MirBlockId>,
}

impl MirFunction {
    pub(crate) fn new(
        id: MirFunctionId,
        name: NameId,
        return_type: TypeId,
        kind: MirFunctionKind,
    ) -> Self {
        Self {
            id,
            name,
            return_type,
            params: Vec::new(),
            kind,
            is_variadic: false,
            locals: Vec::new(),
            blocks: Vec::new(),
            entry_block: None,
        }
    }

    pub(crate) fn new_defined(
        id: MirFunctionId,
        name: NameId,
        return_type: TypeId,
        kind: MirFunctionKind,
    ) -> Self {
        debug_assert!(matches!(
            kind,
            MirFunctionKind::DefinedInternal | MirFunctionKind::DefinedExternal
        ));
        Self::new(id, name, return_type, kind)
    }

    fn new_extern(id: MirFunctionId, name: NameId, return_type: TypeId) -> Self {
        Self::new(id, name, return_type, MirFunctionKind::Extern)
    }
}

/// MIR Block - Basic block with statements and terminator
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MirBlock {
    pub id: MirBlockId,
    pub statements: Vec<MirStmtId>,
    pub terminator: Terminator,
}

impl MirBlock {
    pub(crate) fn new(id: MirBlockId) -> Self {
        Self {
            id,
            statements: Vec::new(),
            terminator: Terminator::Unreachable,
        }
    }
}

/// MIR Statement - Individual operations within a block
/// Only contains side-effect operations, no control flow
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum MirStmt {
    Assign(Place, Rvalue),
    Store(Operand, Place),
    // Function calls - dest is None if void or result is ignored
    Call {
        target: CallTarget,
        args: Vec<Operand>,
        dest: Option<Place>,
    },
    // Memory operations
    Alloc(Place, TypeId),
    Dealloc(Operand),
    BuiltinVaStart(Place, Operand),
    BuiltinVaEnd(Place),
    BuiltinVaCopy(Place, Place),
    AtomicStore(Operand, Operand, AtomicMemOrder),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
pub enum AtomicMemOrder {
    Relaxed,
    Consume,
    Acquire,
    Release,
    AcqRel,
    SeqCst,
}

/// Terminator - Control flow terminators for basic blocks
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Terminator {
    Goto(MirBlockId),
    If(Operand, MirBlockId, MirBlockId),
    Return(Option<Operand>),
    Unreachable,
}

/// Place - Represents a storage location (local variable or memory)
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Place {
    Local(LocalId),
    Deref(Box<Operand>),
    Global(GlobalId),
    // Aggregate access
    StructField(Box<Place>, /* struct index */ usize),
    ArrayIndex(Box<Place>, Box<Operand>),
}

/// Operand - Represents values used in MIR operations
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Operand {
    Copy(Box<Place>),
    Constant(ConstValueId),
    // Address operations
    AddressOf(Box<Place>),
    // Type conversion
    Cast(TypeId, Box<Operand>),
}

/// Rvalue - Right-hand side values in assignments
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Rvalue {
    Use(Operand),
    BinaryIntOp(BinaryIntOp, Operand, Operand),
    BinaryFloatOp(BinaryFloatOp, Operand, Operand),
    UnaryIntOp(UnaryIntOp, Operand),
    UnaryFloatOp(UnaryFloatOp, Operand),
    Cast(TypeId, Operand),
    PtrAdd(Operand, Operand),
    PtrSub(Operand, Operand),
    PtrDiff(Operand, Operand),
    // Aggregate construction
    StructLiteral(Vec<(usize, Operand)>),
    ArrayLiteral(Vec<Operand>),
    // Memory operations
    Load(Operand),
    BuiltinVaArg(Place, TypeId),
    AtomicLoad(Operand, AtomicMemOrder),
    AtomicExchange(Operand, Operand, AtomicMemOrder),
    AtomicCompareExchange(Operand, Operand, Operand, bool, AtomicMemOrder, AtomicMemOrder),
    AtomicFetchOp(BinaryIntOp, Operand, Operand, AtomicMemOrder),
}

/// Call target - represents how a function is called
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum CallTarget {
    Direct(MirFunctionId), // Direct call to a known function
    Indirect(Operand),     // Indirect call via function pointer
}

/// Integer binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum BinaryIntOp {
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
    pub(crate) fn is_comparison(&self) -> bool {
        matches!(self, Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge)
    }
}

/// Floating-point binary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum BinaryFloatOp {
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
    pub(crate) fn is_comparison(&self) -> bool {
        matches!(self, Self::Eq | Self::Ne | Self::Lt | Self::Le | Self::Gt | Self::Ge)
    }
}

/// Integer unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum UnaryIntOp {
    Neg,
    BitwiseNot,
    LogicalNot,
}

/// Floating-point unary operations
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum UnaryFloatOp {
    Neg,
}

/// Type - MIR type system
// - All Struct/Union have a stable NameId
// - No anonymous record types exist in MIR
// - No anonymous members exist in MIR
// - Field names are unique within a record
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum MirType {
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
    pub(crate) fn is_signed(&self) -> bool {
        matches!(self, MirType::I8 | MirType::I16 | MirType::I32 | MirType::I64)
    }

    pub(crate) fn is_void(&self) -> bool {
        matches!(self, MirType::Void)
    }

    pub(crate) fn is_pointer(&self) -> bool {
        matches!(self, MirType::Pointer { .. })
    }

    pub(crate) fn is_float(&self) -> bool {
        matches!(self, MirType::F32 | MirType::F64 | MirType::F80 | MirType::F128)
    }

    pub(crate) fn is_aggregate(&self) -> bool {
        matches!(self, MirType::Record { .. } | MirType::Array { .. })
    }

    pub(crate) fn is_int(&self) -> bool {
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

    pub(crate) fn width(&self) -> u32 {
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
    pub(crate) fn truncate_int(&self, val: i64) -> i64 {
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
pub struct MirRecordLayout {
    pub size: u64,
    pub alignment: u64,
    pub field_offsets: Vec<u64>,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub struct MirArrayLayout {
    pub size: u64,
    pub align: u64,
    pub stride: u64,
}

/// Constant Value Kind - discriminant for ConstValue
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ConstValueKind {
    Int(i64),
    Float(f64),
    Bool(bool),
    Null, // pointer null
    Zero, // memset / padding / zero-init
    // Aggregate constants
    StructLiteral(Vec<(usize, ConstValueId)>),
    ArrayLiteral(Vec<ConstValueId>),
    // Address constants
    GlobalAddress(GlobalId),
    FunctionAddress(MirFunctionId),
}

/// Constant Value - Literal values in MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct ConstValue {
    pub ty: TypeId,
    pub kind: ConstValueKind,
}

/// Local - Represents a local variable or parameter
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub struct Local {
    pub id: LocalId,
    pub name: Option<NameId>,
    pub type_id: TypeId,
    pub is_param: bool,
    pub alignment: Option<u32>, // Alignment in bytes
}

impl Local {
    pub(crate) fn new(id: LocalId, name: Option<NameId>, type_id: TypeId, is_param: bool) -> Self {
        Self {
            id,
            name,
            type_id,
            is_param,
            alignment: None,
        }
    }
}

/// Global - Represents a global variable
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub struct Global {
    pub id: GlobalId,
    pub name: NameId,
    pub type_id: TypeId,
    pub is_constant: bool,
    pub initial_value: Option<ConstValueId>,
    pub alignment: Option<u32>, // Max alignment in bytes
}

impl Global {
    pub(crate) fn new(id: GlobalId, name: NameId, type_id: TypeId, is_constant: bool) -> Self {
        Self {
            id,
            name,
            type_id,
            is_constant,
            initial_value: None,
            alignment: None,
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
    functions: HashMap<MirFunctionId, MirFunction>,
    blocks: HashMap<MirBlockId, MirBlock>,
    locals: HashMap<LocalId, Local>,
    globals: HashMap<GlobalId, Global>,
    types: HashMap<TypeId, MirType>,
    constants: HashMap<ConstValueId, ConstValue>,
    // Statement storage with ID mapping
    statements: HashMap<MirStmtId, MirStmt>,
}

/// Complete semantic analysis output containing the full MIR program representation
/// Includes all functions, blocks, instructions, and type definitions.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MirProgram {
    pub module: MirModule,
    pub functions: HashMap<MirFunctionId, MirFunction>,
    pub blocks: HashMap<MirBlockId, MirBlock>,
    pub locals: HashMap<LocalId, Local>,
    pub globals: HashMap<GlobalId, Global>,
    pub types: HashMap<TypeId, MirType>,
    pub constants: HashMap<ConstValueId, ConstValue>,
    pub statements: HashMap<MirStmtId, MirStmt>,
    pub pointer_width: u8,
}

impl MirProgram {
    /// get type or panic if not found
    pub(crate) fn get_type(&self, id: TypeId) -> &MirType {
        match self.types.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Type ID {id} not found"),
        }
    }
    pub(crate) fn get_local(&self, id: LocalId) -> &Local {
        match self.locals.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Local ID {id} not found"),
        }
    }
    pub(crate) fn get_function(&self, id: MirFunctionId) -> &MirFunction {
        match self.functions.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Function ID {id} not found"),
        }
    }
    pub(crate) fn get_global(&self, id: GlobalId) -> &Global {
        match self.globals.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Global ID {id} not found"),
        }
    }
}

impl MirBuilder {
    pub(crate) fn new(module_id: MirModuleId, pointer_width: u8) -> Self {
        let mut module = MirModule::new(module_id);
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
            functions: HashMap::new(),
            blocks: HashMap::new(),
            locals: HashMap::new(),
            globals: HashMap::new(),
            types: HashMap::new(),
            constants: HashMap::new(),
            statements: HashMap::new(),
        }
    }

    /// Create a new local variable
    pub(crate) fn create_local(&mut self, name: Option<NameId>, type_id: TypeId, is_param: bool) -> LocalId {
        let local_id = LocalId::new(self.next_local_id).unwrap();
        self.next_local_id += 1;

        let local = Local::new(local_id, name, type_id, is_param);
        self.locals.insert(local_id, local);

        if let Some(func_id) = self.current_function
            && let Some(func) = self.functions.get_mut(&func_id)
        {
            if is_param {
                func.params.push(local_id);
            } else {
                func.locals.push(local_id);
            }
        }

        local_id
    }

    pub(crate) fn set_local_alignment(&mut self, local_id: LocalId, alignment: u32) {
        if let Some(local) = self.locals.get_mut(&local_id) {
            local.alignment = Some(alignment);
        }
    }

    /// Create a new basic block
    pub(crate) fn create_block(&mut self) -> MirBlockId {
        let func_id = self.current_function.expect("no current function");
        let func = self.functions.get(&func_id).unwrap();

        assert!(
            matches!(
                func.kind,
                MirFunctionKind::DefinedInternal | MirFunctionKind::DefinedExternal
            ),
            "cannot create blocks for extern function"
        );

        let block_id = MirBlockId::new(self.next_block_id).unwrap();
        self.next_block_id += 1;

        let block = MirBlock::new(block_id);
        self.blocks.insert(block_id, block);

        if let Some(func) = self.functions.get_mut(&func_id) {
            func.blocks.push(block_id);
        }

        block_id
    }

    /// Add a statement to the current block
    pub(crate) fn add_statement(&mut self, stmt: MirStmt) -> MirStmtId {
        let stmt_id = MirStmtId::new(self.next_stmt_id).unwrap();
        self.next_stmt_id += 1;

        // Store statement in the HashMap
        self.statements.insert(stmt_id, stmt.clone());

        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get_mut(&block_id)
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
            && let Some(block) = self.blocks.get_mut(&block_id)
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
            && let Some(block) = self.blocks.get(&block_id)
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
        let func_id = MirFunctionId::new(self.module.functions.len() as u32 + 1).unwrap();
        let mut func = MirFunction::new_extern(func_id, name, return_type);
        func.is_variadic = is_variadic;

        // Create locals for each parameter
        for (i, &param_type) in param_types.iter().enumerate() {
            let param_name = Some(NameId::new(format!("param{}", i)));
            let local_id = self.create_local(param_name, param_type, true);
            func.params.push(local_id);
        }

        self.functions.insert(func_id, func);
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
        kind: MirFunctionKind,
    ) -> MirFunctionId {
        let func_id = MirFunctionId::new(self.module.functions.len() as u32 + 1).unwrap();
        let mut func = MirFunction::new_defined(func_id, name, return_type, kind);
        func.is_variadic = is_variadic;

        // Create locals for each parameter
        for (i, &param_type) in param_types.iter().enumerate() {
            let param_name = Some(NameId::new(format!("param{}", i)));
            let local_id = self.create_local(param_name, param_type, true);
            func.params.push(local_id);
        }

        self.functions.insert(func_id, func);
        self.module.functions.push(func_id);

        func_id
    }

    /// Set current function
    pub(crate) fn set_current_function(&mut self, func_id: MirFunctionId) {
        self.current_function = Some(func_id);
        if let Some(func) = self.functions.get(&func_id)
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
        initial_value: Option<ConstValueId>,
    ) -> GlobalId {
        let global_id = GlobalId::new(self.next_global_id).unwrap();
        self.next_global_id += 1;

        let mut global = Global::new(global_id, name, type_id, is_constant);
        global.initial_value = initial_value;
        self.globals.insert(global_id, global);
        self.module.globals.push(global_id);

        global_id
    }

    pub(crate) fn set_global_initializer(&mut self, global_id: GlobalId, init_id: ConstValueId) {
        if let Some(global) = self.globals.get_mut(&global_id) {
            global.initial_value = Some(init_id);
        }
    }

    pub(crate) fn set_global_alignment(&mut self, global_id: GlobalId, alignment: u32) {
        if let Some(global) = self.globals.get_mut(&global_id) {
            global.alignment = Some(alignment);
        }
    }

    /// Add a type to the module with interning
    pub(crate) fn add_type(&mut self, mir_type: MirType) -> TypeId {
        // Check if type already exists (type interning)
        for (existing_id, existing_type) in &self.types {
            if existing_type == &mir_type {
                return *existing_id;
            }
        }

        // Type doesn't exist, create new one
        let type_id = TypeId::new(self.next_type_id).unwrap();
        self.next_type_id += 1;

        self.types.insert(type_id, mir_type.clone());
        self.module.types.push(mir_type);

        type_id
    }

    /// Update an existing type previously inserted with `add_type`.
    /// This replaces the type entry in both the internal map and the module vector.
    pub(crate) fn update_type(&mut self, type_id: TypeId, mir_type: MirType) {
        self.types.insert(type_id, mir_type.clone());
        let idx = (type_id.get() - 1) as usize;
        if idx < self.module.types.len() {
            self.module.types[idx] = mir_type;
        }
    }

    pub(crate) fn get_type(&self, type_id: TypeId) -> &MirType {
        self.types.get(&type_id).expect("Type ID not found in MirBuilder")
    }

    /// Create a constant value
    pub(crate) fn create_constant(&mut self, ty: TypeId, kind: ConstValueKind) -> ConstValueId {
        let const_id = ConstValueId::new(self.next_const_id).unwrap();
        self.next_const_id += 1;

        let value = ConstValue { ty, kind };
        self.constants.insert(const_id, value.clone());
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
    pub(crate) fn get_functions(&self) -> &HashMap<MirFunctionId, MirFunction> {
        &self.functions
    }

    /// Get all constants for validation
    pub(crate) fn get_constants(&self) -> &HashMap<ConstValueId, ConstValue> {
        &self.constants
    }

    pub(crate) fn get_globals(&self) -> &HashMap<GlobalId, Global> {
        &self.globals
    }

    pub(crate) fn get_locals(&self) -> &HashMap<LocalId, Local> {
        &self.locals
    }

    /// Set the entry block for a function
    pub(crate) fn set_function_entry_block(&mut self, func_id: MirFunctionId, block_id: MirBlockId) {
        if let Some(func) = self.functions.get_mut(&func_id) {
            assert!(matches!(
                func.kind,
                MirFunctionKind::DefinedInternal | MirFunctionKind::DefinedExternal
            ));
            func.entry_block = Some(block_id);
        }
    }

    pub(crate) fn get_next_anonymous_global_name(&mut self) -> NameId {
        let name = format!(".L.str{}", self.anonymous_global_counter);
        self.anonymous_global_counter += 1;
        NameId::new(name)
    }
}
