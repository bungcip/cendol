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
use std::fmt;
use std::num::NonZeroU32;

use crate::ast::NameId;

pub mod codegen;
pub mod validation;

#[cfg(test)]
pub mod tests_codegen;

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
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum MirFunctionKind {
    Defined,
    Extern,
}

/// MIR Module - Top-level container for MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MirModule {
    pub id: MirModuleId,
    pub functions: Vec<MirFunctionId>,
    pub globals: Vec<GlobalId>,
    pub types: Vec<MirType>,
    pub constants: Vec<ConstValue>,
}

impl MirModule {
    pub fn new(id: MirModuleId) -> Self {
        Self {
            id,
            functions: Vec::new(),
            globals: Vec::new(),
            types: Vec::new(),
            constants: Vec::new(),
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

    // Only valid if kind is Defined
    pub locals: Vec<LocalId>,
    pub blocks: Vec<MirBlockId>,
    pub entry_block: Option<MirBlockId>,
}

impl MirFunction {
    pub fn new_defined(id: MirFunctionId, name: NameId, return_type: TypeId) -> Self {
        Self {
            id,
            name,
            return_type,
            params: Vec::new(),
            kind: MirFunctionKind::Defined,
            locals: Vec::new(),
            blocks: Vec::new(),
            entry_block: None,
        }
    }

    pub fn new_extern(id: MirFunctionId, name: NameId, return_type: TypeId) -> Self {
        Self {
            id,
            name,
            return_type,
            params: Vec::new(),
            kind: MirFunctionKind::Extern,
            locals: Vec::new(),
            blocks: Vec::new(),
            entry_block: None,
        }
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
    pub fn new(id: MirBlockId) -> Self {
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
    // Function calls with side effects only (void calls or calls where result is ignored)
    Call(CallTarget, Vec<Operand>),
    // Memory operations
    Alloc(Place, TypeId),
    Dealloc(Operand),
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
    StructField(Box<Place>, /* index */ usize),
    ArrayIndex(Box<Place>, Box<Operand>),
}

/// Operand - Represents values used in MIR operations
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum Operand {
    Copy(Box<Place>),
    Move(Box<Place>),
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
    BinaryOp(BinaryOp, Operand, Operand),
    UnaryOp(UnaryOp, Operand),
    Cast(TypeId, Operand),
    PtrAdd(Operand, Operand),
    // Aggregate construction
    StructLiteral(Vec<(usize, Operand)>),
    ArrayLiteral(Vec<Operand>),
    // Memory operations
    Load(Operand),
    // Function calls that return a value (NON-VOID ONLY)
    Call(CallTarget, Vec<Operand>),
}

/// Call target - represents how a function is called
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum CallTarget {
    Direct(MirFunctionId), // Direct call to a known function
    Indirect(Operand),     // Indirect call via function pointer
}

/// Binary operations
/// This is different from AST binary ops as some C semantics are made explicit here
/// So thereis no assignment ops
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum BinaryOp {
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
    Equal,
    NotEqual,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    LogicAnd,
    LogicOr,
    Comma,
}

/// Unary operations
/// This is different from AST unary ops as some C semantics are made explicit here
/// So no increment/decrement ops because they are desugared into assignments
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[repr(u8)]
pub enum UnaryOp {
    Neg,
    Not,
    AddrOf,
    Deref,
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
    Int {
        is_signed: bool,
        width: u8,
    },
    Float {
        width: u8,
    },
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
    },
    Record {
        name: NameId,                  // unlike in C, in MIR we must have name
        fields: Vec<(NameId, TypeId)>, // unlike in C, in MIR we must have name
        is_union: bool,
        layout: MirRecordLayout,
    },
    Enum {
        name: NameId,
        variants: Vec<(NameId, i64)>,
    },
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MirRecordLayout {
    pub size: u16,
    pub alignment: u16,
    pub field_offsets: Vec<u16>,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct MirArrayLayout {
    pub size: u16,
    pub align: u16,
    pub stride: u16,
}

/// Constant Value - Literal values in MIR
#[derive(Debug, Clone, PartialEq, Serialize)]
pub enum ConstValue {
    Int(i64),
    Float(f64),
    Bool(bool),
    Null,
    Zero,
    // String literals
    String(String),
    // Aggregate constants
    StructLiteral(Vec<(usize, ConstValueId)>),
    ArrayLiteral(Vec<ConstValueId>),
    // Address constants
    GlobalAddress(GlobalId),
    FunctionAddress(MirFunctionId),
}

/// Local - Represents a local variable or parameter
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Local {
    pub id: LocalId,
    pub name: Option<NameId>,
    pub type_id: TypeId,
    pub is_param: bool,
}

impl Local {
    pub fn new(id: LocalId, name: Option<NameId>, type_id: TypeId, is_param: bool) -> Self {
        Self {
            id,
            name,
            type_id,
            is_param,
        }
    }
}

/// Global - Represents a global variable
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Global {
    pub id: GlobalId,
    pub name: NameId,
    pub type_id: TypeId,
    pub is_constant: bool,
    pub initial_value: Option<ConstValueId>,
}

impl Global {
    pub fn new(id: GlobalId, name: NameId, type_id: TypeId, is_constant: bool) -> Self {
        Self {
            id,
            name,
            type_id,
            is_constant,
            initial_value: None,
        }
    }
}

/// MIR Builder - Builds MIR from AST
pub struct MirBuilder {
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

impl MirBuilder {
    pub fn new(module_id: MirModuleId) -> Self {
        Self {
            module: MirModule::new(module_id),
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
    pub fn create_local(&mut self, name: Option<NameId>, type_id: TypeId, is_param: bool) -> LocalId {
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

    /// Create a new basic block
    pub fn create_block(&mut self) -> MirBlockId {
        let func_id = self.current_function.expect("no current function");
        let func = self.functions.get(&func_id).unwrap();

        assert!(
            matches!(func.kind, MirFunctionKind::Defined),
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
    pub fn add_statement(&mut self, stmt: MirStmt) -> MirStmtId {
        let stmt_id = MirStmtId::new(self.next_stmt_id).unwrap();
        self.next_stmt_id += 1;

        // Store statement in the HashMap
        self.statements.insert(stmt_id, stmt.clone());

        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get_mut(&block_id)
        {
            block.statements.push(stmt_id);
        }

        stmt_id
    }

    /// Set the terminator for the current block
    pub fn set_terminator(&mut self, terminator: Terminator) {
        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get_mut(&block_id)
        {
            block.terminator = terminator;
        }
    }

    /// Set the current block
    pub fn set_current_block(&mut self, block_id: MirBlockId) {
        self.current_block = Some(block_id);
    }

    /// Check if the current block has a non-unreachable terminator
    /// Since terminators always exist, this checks if the terminator is meaningful
    /// (i.e., not just the default Unreachable terminator)
    pub fn current_block_has_terminator(&self) -> bool {
        if let Some(block_id) = self.current_block
            && let Some(block) = self.blocks.get(&block_id)
        {
            return !matches!(block.terminator, Terminator::Unreachable);
        }
        false
    }

    /// Declare a function (extern - no body)
    pub fn declare_function(&mut self, name: NameId, param_types: Vec<TypeId>, return_type: TypeId) -> MirFunctionId {
        let func_id = MirFunctionId::new(self.module.functions.len() as u32 + 1).unwrap();
        let mut func = MirFunction::new_extern(func_id, name, return_type);

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
    pub fn define_function(&mut self, name: NameId, param_types: Vec<TypeId>, return_type: TypeId) -> MirFunctionId {
        let func_id = MirFunctionId::new(self.module.functions.len() as u32 + 1).unwrap();
        let mut func = MirFunction::new_defined(func_id, name, return_type);

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
    pub fn set_current_function(&mut self, func_id: MirFunctionId) {
        self.current_function = Some(func_id);
        if let Some(func) = self.functions.get(&func_id)
            && let Some(entry_block) = func.entry_block
        {
            self.current_block = Some(entry_block);
        }
    }

    /// Create a new global variable
    pub fn create_global(&mut self, name: NameId, type_id: TypeId, is_constant: bool) -> GlobalId {
        let global_id = GlobalId::new(self.next_global_id).unwrap();
        self.next_global_id += 1;

        let global = Global::new(global_id, name, type_id, is_constant);
        self.globals.insert(global_id, global);
        self.module.globals.push(global_id);

        global_id
    }

    /// Create a new global variable with initial value
    pub fn create_global_with_init(
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

    pub fn set_global_initializer(&mut self, global_id: GlobalId, init_id: ConstValueId) {
        if let Some(global) = self.globals.get_mut(&global_id) {
            global.initial_value = Some(init_id);
        }
    }

    /// Add a type to the module with interning
    pub fn add_type(&mut self, mir_type: MirType) -> TypeId {
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

    /// Create a constant value
    pub fn create_constant(&mut self, value: ConstValue) -> ConstValueId {
        let const_id = ConstValueId::new(self.next_const_id).unwrap();
        self.next_const_id += 1;

        self.constants.insert(const_id, value.clone());
        self.module.constants.push(value);

        const_id
    }

    /// Get the current MIR module
    pub fn get_module(&self) -> &MirModule {
        &self.module
    }

    /// Finalize the module by updating all references
    pub fn finalize_module(&mut self) -> MirModule {
        // Return the accumulated module directly
        // This preserves the insertion order of types and constants,
        // which is crucial for maintaining correct ID-to-index mapping
        self.module.clone()
    }

    /// Get all functions for validation
    pub fn get_functions(&self) -> &HashMap<MirFunctionId, MirFunction> {
        &self.functions
    }

    /// Get all blocks for validation
    pub fn get_blocks(&self) -> &HashMap<MirBlockId, MirBlock> {
        &self.blocks
    }

    /// Get all locals for validation
    pub fn get_locals(&self) -> &HashMap<LocalId, Local> {
        &self.locals
    }

    /// Get all globals for validation
    pub fn get_globals(&self) -> &HashMap<GlobalId, Global> {
        &self.globals
    }

    /// Get all globals for validation (mutable)
    pub fn get_globals_mut(&mut self) -> &mut HashMap<GlobalId, Global> {
        &mut self.globals
    }

    /// Get all types for validation
    pub fn get_types(&self) -> &HashMap<TypeId, MirType> {
        &self.types
    }

    /// Get all constants for validation
    pub fn get_constants(&self) -> &HashMap<ConstValueId, ConstValue> {
        &self.constants
    }

    /// Get all statements for validation
    pub fn get_statements(&self) -> &HashMap<MirStmtId, MirStmt> {
        &self.statements
    }

    /// Set the entry block for a function
    pub fn set_function_entry_block(&mut self, func_id: MirFunctionId, block_id: MirBlockId) {
        if let Some(func) = self.functions.get_mut(&func_id) {
            assert!(matches!(func.kind, MirFunctionKind::Defined));
            func.entry_block = Some(block_id);
        }
    }

    pub fn get_next_anonymous_global_name(&mut self) -> NameId {
        let name = format!(".L.str{}", self.anonymous_global_counter);
        self.anonymous_global_counter += 1;
        NameId::new(name)
    }

    pub fn update_record_fields(&mut self, type_id: TypeId, fields: Vec<(NameId, TypeId)>) {
        let type_index = (type_id.get() - 1) as usize;
        if let Some(mir_type) = self.module.types.get_mut(type_index)
            && let MirType::Record { fields: old_fields, .. } = mir_type
        {
            *old_fields = fields.clone();
        }
        if let Some(mir_type) = self.types.get_mut(&type_id)
            && let MirType::Record { fields: old_fields, .. } = mir_type
        {
            *old_fields = fields;
        }
    }
}

/// Display implementations for debugging
impl fmt::Display for MirModule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MirModule(id: {})", self.id.get())?;
        writeln!(f, "  Functions: {:?}", self.functions)?;
        writeln!(f, "  Globals: {:?}", self.globals)?;
        writeln!(f, "  Types: {:?}", self.types)?;
        writeln!(f, "  Constants: {:?}", self.constants)?;
        Ok(())
    }
}

impl fmt::Display for MirFunction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "MirFunction(id: {}, name: {}, kind: {:?})",
            self.id.get(),
            self.name,
            self.kind
        )?;
        writeln!(f, "  Return type: {:?}", self.return_type)?;
        writeln!(f, "  Params: {:?}", self.params)?;
        writeln!(f, "  Locals: {:?}", self.locals)?;
        writeln!(f, "  Blocks: {:?}", self.blocks)?;
        if let Some(entry_block) = self.entry_block {
            writeln!(f, "  Entry block: {:?}", entry_block)?;
        } else {
            writeln!(f, "  Entry block: None")?;
        }
        Ok(())
    }
}

impl fmt::Display for MirBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MirBlock(id: {})", self.id.get())?;
        writeln!(f, "  Statements: {:?}", self.statements)?;
        writeln!(f, "  Terminator: {:?}", self.terminator)?;
        Ok(())
    }
}

impl fmt::Display for MirStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MirStmt::Assign(place, operand) => write!(f, "Assign({:?}, {:?})", place, operand),
            MirStmt::Store(operand, place) => write!(f, "Store({:?}, {:?})", operand, place),
            MirStmt::Call(call_target, operands) => write!(f, "Call({:?}, {:?})", call_target, operands),
            MirStmt::Alloc(place, type_id) => write!(f, "Alloc({:?}, {})", place, type_id.get()),
            MirStmt::Dealloc(operand) => write!(f, "Dealloc({:?})", operand),
        }
    }
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Goto(block) => write!(f, "Goto({})", block.get()),
            Terminator::If(cond, then_block, else_block) => {
                write!(f, "If({:?}, {}, {})", cond, then_block.get(), else_block.get())
            }
            Terminator::Return(operand) => write!(f, "Return({:?})", operand),
            Terminator::Unreachable => write!(f, "Unreachable"),
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Place::Local(local) => write!(f, "Local({})", local.get()),
            Place::Deref(operand) => write!(f, "Deref({:?})", operand),
            Place::Global(global) => write!(f, "Global({})", global.get()),
            Place::StructField(place, field_idx) => write!(f, "StructField({:?}, {})", place, field_idx),
            Place::ArrayIndex(place, index) => write!(f, "ArrayIndex({:?}, {:?})", place, index),
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Copy(place) => write!(f, "Copy({:?})", place),
            Operand::Move(place) => write!(f, "Move({:?})", place),
            Operand::Constant(const_id) => write!(f, "Constant({})", const_id.get()),
            Operand::AddressOf(place) => write!(f, "AddressOf({:?})", place),
            Operand::Cast(type_id, operand) => write!(f, "Cast({}, {:?})", type_id.get(), operand),
        }
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(operand) => write!(f, "Use({:?})", operand),
            Rvalue::BinaryOp(op, left, right) => write!(f, "BinaryOp({:?}, {:?}, {:?})", op, left, right),
            Rvalue::UnaryOp(op, operand) => write!(f, "UnaryOp({:?}, {:?})", op, operand),
            Rvalue::Cast(type_id, operand) => write!(f, "Cast({}, {:?})", type_id.get(), operand),
            Rvalue::PtrAdd(base, offset) => write!(f, "PtrAdd({:?}, {:?})", base, offset),
            Rvalue::StructLiteral(fields) => write!(f, "StructLiteral({:?})", fields),
            Rvalue::ArrayLiteral(elements) => write!(f, "ArrayLiteral({:?})", elements),
            Rvalue::Load(operand) => write!(f, "Load({:?})", operand),
            Rvalue::Call(call_target, operands) => write!(f, "Call({:?}, {:?})", call_target, operands),
        }
    }
}

impl fmt::Display for MirType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MirType::Void => write!(f, "void"),
            MirType::Bool => write!(f, "bool"),
            MirType::Int { is_signed, width } => write!(f, "{}{}", if *is_signed { "i" } else { "u" }, width),
            MirType::Float { width } => write!(f, "f{}", width),
            MirType::Pointer { pointee } => write!(f, "*{}", pointee.get()),
            MirType::Array { element, size, .. } => write!(f, "[{}]{}", size, element.get()),
            MirType::Function { return_type, params } => write!(f, "fn({:?}) -> {}", params, return_type.get()),
            MirType::Record {
                name, fields, is_union, ..
            } => {
                let kind = if *is_union { "union" } else { "struct" };
                write!(f, "{} {} {{ {:?} }}", kind, name, fields)
            }
            MirType::Enum { name, variants } => write!(f, "enum {} {{ {:?} }}", name, variants),
        }
    }
}

impl fmt::Display for ConstValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstValue::Int(val) => write!(f, "{}", val),
            ConstValue::Float(val) => write!(f, "{}", val),
            ConstValue::Bool(val) => write!(f, "{}", val),
            ConstValue::Null => write!(f, "null"),
            ConstValue::Zero => write!(f, "zeroinit"),
            ConstValue::String(val) => write!(f, "{}", val),
            ConstValue::StructLiteral(fields) => write!(f, "StructLiteral({:?})", fields),
            ConstValue::ArrayLiteral(elements) => write!(f, "ArrayLiteral({:?})", elements),
            ConstValue::GlobalAddress(global_id) => write!(f, "GlobalAddress({})", global_id.get()),
            ConstValue::FunctionAddress(func_id) => write!(f, "FunctionAddress({})", func_id.get()),
        }
    }
}

impl fmt::Display for CallTarget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CallTarget::Direct(func_id) => write!(f, "Direct({})", func_id.get()),
            CallTarget::Indirect(operand) => write!(f, "Indirect({:?})", operand),
        }
    }
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Local(id: {}, name: {:?}, type: {}, is_param: {})",
            self.id.get(),
            self.name,
            self.type_id.get(),
            self.is_param
        )
    }
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Global(id: {}, name: {}, type: {}, is_constant: {})",
            self.id.get(),
            self.name,
            self.type_id.get(),
            self.is_constant
        )
    }
}
