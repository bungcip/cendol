//! MIR to Cranelift IR lowering module
//!
//! This module provides the mechanical translation from MIR to Cranelift IR.
//! The translation follows these rules:
//! - No C logic
//! - No type inference
//! - Assume MIR is valid
//! - 1:1 mapping from MIR to Cranelift

use crate::ast::NameId;
use crate::driver::compiler::SemaOutput;
use crate::mir::{
    BinaryOp, CallTarget, ConstValue, ConstValueId, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId,
    MirFunctionKind, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId,
};
use cranelift::codegen::ir::{StackSlot, StackSlotData, StackSlotKind};
use cranelift::prelude::{
    AbiParam, FunctionBuilderContext, InstBuilder, IntCC, MemFlags, Signature, Type, Value, types,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use hashbrown::HashMap;
use hashbrown::HashSet;
use target_lexicon::Triple;

/// emitted from codegen
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmitKind {
    Object,
    Clif,
}

pub enum ClifOutput {
    ObjectFile(Vec<u8>),
    ClifDump(String),
}

/// Helper function to convert MIR type to Cranelift type
/// Returns None for void types, as they don't have a representation in Cranelift
fn mir_type_to_cranelift_type(mir_type: &MirType) -> Option<Type> {
    match mir_type {
        MirType::Void => None,
        MirType::Int { width, is_signed: _ } => {
            match width {
                8 => Some(types::I8),
                16 => Some(types::I16),
                32 => Some(types::I32),
                64 => Some(types::I64),
                _ => Some(types::I32), // Default to 32-bit
            }
        }
        MirType::Float { width } => {
            match width {
                32 => Some(types::F32),
                64 => Some(types::F64),
                _ => Some(types::F32), // Default to 32-bit float
            }
        }
        _ => Some(types::I32), // Default to i32 for other types (bool, pointer, etc.)
    }
}

/// Helper function to get the size of a MIR type in bytes
fn mir_type_size(mir_type: &MirType, mir: &SemaOutput) -> Result<u32, String> {
    match mir_type {
        MirType::Int { width, .. } => Ok((*width / 8) as u32),
        MirType::Float { width } => Ok((*width / 8) as u32),
        MirType::Pointer { .. } => Ok(8), // Assuming 64-bit pointers for now
        MirType::Array { element, size } => {
            let element_type = mir.get_type(*element);
            Ok(mir_type_size(element_type, mir)? * (*size as u32))
        }
        MirType::Struct { fields, .. } => {
            let mut total_size = 0;
            for (_, field_type_id) in fields {
                let field_type = mir.get_type(*field_type_id);
                total_size += mir_type_size(field_type, mir)?;
            }
            Ok(total_size)
        }
        MirType::Bool => Ok(1),
        MirType::Void => Ok(0),
        // For other complex types, let's have a default, though this should be comprehensive.
        _ => Ok(4), // Default size for other types
    }
}

/// Standalone function to emit a proper function call that actually invokes the function
fn emit_function_call_impl(
    call_target: &CallTarget,
    args: &[Operand],
    builder: &mut FunctionBuilder,
    mir: &SemaOutput,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    module: &mut ObjectModule,
) -> Result<Value, String> {
    match call_target {
        CallTarget::Direct(func_id) => {
            // Look up the function in our MIR functions
            let func = mir.get_function(*func_id);

            // Get the return type for this function
            let return_type = mir_type_to_cranelift_type(mir.get_type(func.return_type));

            // Resolve function arguments to Cranelift values
            let mut arg_values = Vec::new();
            for arg in args {
                match resolve_operand_to_value(
                    arg,
                    builder,
                    types::I32, // Default to int for now
                    cranelift_stack_slots,
                    mir,
                    module,
                ) {
                    Ok(value) => arg_values.push(value),
                    Err(e) => return Err(format!("Failed to resolve function argument: {}", e)),
                }
            }

            // Create a function signature by building it directly
            let mut sig = Signature::new(builder.func.signature.call_conv);

            // Only add return parameter if the function has a non-void return type
            if let Some(ret_type) = return_type {
                sig.returns.push(AbiParam::new(ret_type));
            }

            // Add parameter types to signature
            for &param_id in &func.params {
                let param_local = mir.get_local(param_id);
                let param_type = mir_type_to_cranelift_type(mir.get_type(param_local.type_id)).unwrap();
                sig.params.push(AbiParam::new(param_type));
            }

            // Declare the function in the module if not already declared
            let linkage = match func.kind {
                MirFunctionKind::Extern => cranelift_module::Linkage::Import,
                MirFunctionKind::Defined => cranelift_module::Linkage::Export,
            };

            let func_decl = module
                .declare_function(func.name.as_str(), linkage, &sig)
                .map_err(|e| format!("Failed to declare function {}: {:?}", func.name, e))?;

            // Get a local reference to the declared function
            let local_callee = module.declare_func_in_func(func_decl, builder.func);

            // Generate the actual function call
            let call_inst = builder.ins().call(local_callee, &arg_values);

            // Extract the return value from the call instruction
            let call_results = builder.inst_results(call_inst);
            if !call_results.is_empty() {
                Ok(call_results[0])
            } else {
                // For void functions, return a dummy value (this won't be used)
                Ok(builder.ins().iconst(types::I32, 0))
            }
        }
        CallTarget::Indirect(_func_operand) => {
            // For indirect calls (function pointers), return 0 for now
            // TODO: Implement proper indirect function calls using call_indirect
            Ok(builder.ins().iconst(types::I32, 0))
        }
    }
}

/// Helper function to resolve a MIR operand to a Cranelift value
#[allow(clippy::too_many_arguments)]
fn resolve_operand_to_value(
    operand: &Operand,
    builder: &mut FunctionBuilder,
    expected_type: Type,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &SemaOutput,
    module: &mut ObjectModule,
) -> Result<Value, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = mir.constants.get(const_id).expect("constant id not found");
            match const_value {
                ConstValue::Int(val) => Ok(builder.ins().iconst(expected_type, *val)),
                ConstValue::Float(val) => {
                    // Use the appropriate float constant based on expected type
                    if expected_type == types::F64 {
                        Ok(builder.ins().f64const(*val))
                    } else {
                        Ok(builder.ins().f32const(*val as f32))
                    }
                }
                ConstValue::Bool(val) => {
                    let int_val = if *val { 1 } else { 0 };
                    Ok(builder.ins().iconst(expected_type, int_val))
                }
                ConstValue::Null => Ok(builder.ins().iconst(expected_type, 0)),
                ConstValue::String(_) => {
                    // For now, treat string constants as pointers to null
                    Ok(builder.ins().iconst(expected_type, 0))
                }
                _ => Ok(builder.ins().iconst(expected_type, 0)),
            }
        }
        Operand::Copy(place) | Operand::Move(place) => {
            resolve_place_to_value(place, builder, expected_type, cranelift_stack_slots, mir, module)
        }
        Operand::Cast(_, operand) => {
            // For now, just resolve the inner operand
            // TODO: Handle actual type conversions
            resolve_operand_to_value(operand, builder, expected_type, cranelift_stack_slots, mir, module)
        }
        Operand::AddressOf(place) => {
            // The value of an AddressOf operand is the address of the place.
            resolve_place_to_addr(place, builder, cranelift_stack_slots, mir, module)
        }
    }
}

/// Helper function to resolve a MIR place to a Cranelift value
#[allow(clippy::too_many_arguments)]
fn resolve_place_to_value(
    place: &Place,
    builder: &mut FunctionBuilder,
    expected_type: Type,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &SemaOutput,
    module: &mut ObjectModule,
) -> Result<Value, String> {
    match place {
        Place::Local(local_id) => {
            // A local place is resolved by loading from its stack slot
            if let Some(stack_slot) = cranelift_stack_slots.get(local_id) {
                Ok(builder.ins().stack_load(expected_type, *stack_slot, 0))
            } else {
                Err(format!("Stack slot not found for local {}", local_id.get()))
            }
        }
        Place::Global(_global_id) => {
            // First, get the memory address of the global.
            let addr = resolve_place_to_addr(
                place, // Pass the current place
                builder,
                cranelift_stack_slots,
                mir,
                module,
            )?;

            // Then, load the value from that address.
            Ok(builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
        Place::Deref(operand) => {
            // The address is the value of the operand, so we load from that value
            let addr = resolve_operand_to_value(
                operand,
                builder,
                types::I64, // Assume pointer size
                cranelift_stack_slots,
                mir,
                module,
            )?;
            Ok(builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
        Place::StructField(base_place, field_index) => {
            // Get the address of the struct field
            let addr = resolve_place_to_addr(
                &Place::StructField(base_place.clone(), *field_index),
                builder,
                cranelift_stack_slots,
                mir,
                module,
            )?;
            Ok(builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
        Place::ArrayIndex(base_place, index_operand) => {
            // Get the address of the array element
            let addr = resolve_place_to_addr(
                &Place::ArrayIndex(base_place.clone(), index_operand.clone()),
                builder,
                cranelift_stack_slots,
                mir,
                module,
            )?;
            Ok(builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
    }
}

/// Helper function to get the TypeId of a place
fn get_place_type_id(place: &Place, mir: &SemaOutput) -> Result<TypeId, String> {
    match place {
        Place::Local(local_id) => Ok(mir.get_local(*local_id).type_id),
        Place::Global(global_id) => Ok(mir.get_global(*global_id).type_id),
        Place::Deref(operand) => {
            // To get the type of a dereference, we need the type of the operand,
            // which should be a pointer. The resulting type is the pointee.
            // For now, we'll try to extract the type from the operand if it's a place.
            match operand.as_ref() {
                Operand::Copy(place_box) | Operand::Move(place_box) => get_place_type_id(place_box, mir),
                _ => Err("Cannot determine type for deref operand".to_string()),
            }
        }
        Place::StructField(base_place, field_index) => {
            let base_type_id = get_place_type_id(base_place, mir)?;
            let base_type = mir.get_type(base_type_id);
            match base_type {
                MirType::Struct { fields, .. } => fields
                    .get(*field_index)
                    .map(|(_, type_id)| *type_id)
                    .ok_or_else(|| "Field index out of bounds".to_string()),
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    if let MirType::Struct { fields, .. } = pointee_type {
                        fields
                            .get(*field_index)
                            .map(|(_, type_id)| *type_id)
                            .ok_or_else(|| "Field index out of bounds".to_string())
                    } else {
                        Err("Base of StructField is not a struct type".to_string())
                    }
                }
                _ => Err("Base of StructField is not a struct type".to_string()),
            }
        }
        Place::ArrayIndex(base_place, _) => {
            let base_type_id = get_place_type_id(base_place, mir)?;
            let base_type = mir.get_type(base_type_id);
            match base_type {
                MirType::Array { element, .. } => Ok(*element),
                MirType::Pointer { pointee } => Ok(*pointee),
                _ => Err("Base of ArrayIndex is not an array or pointer".to_string()),
            }
        }
    }
}

/// Helper function to resolve a MIR place to a memory address
fn resolve_place_to_addr(
    place: &Place,
    builder: &mut FunctionBuilder,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &SemaOutput,
    module: &mut ObjectModule,
) -> Result<Value, String> {
    match place {
        Place::Local(local_id) => {
            if let Some(stack_slot) = cranelift_stack_slots.get(local_id) {
                Ok(builder.ins().stack_addr(types::I64, *stack_slot, 0))
            } else {
                Err(format!("Stack slot not found for local {}", local_id.get()))
            }
        }
        Place::Global(global_id) => {
            let global = mir.get_global(*global_id);
            let global_val = module
                .declare_data(global.name.as_str(), cranelift_module::Linkage::Export, true, false)
                .map_err(|e| format!("Failed to declare global data: {:?}", e))?;
            let local_id = module.declare_data_in_func(global_val, builder.func);
            // Use I64 for addresses
            Ok(builder.ins().global_value(types::I64, local_id))
        }
        Place::Deref(operand) => {
            // The address is the value of the operand itself (which should be a pointer).
            resolve_operand_to_value(
                operand,
                builder,
                types::I64, // Assume pointers are 64-bit
                cranelift_stack_slots,
                mir,
                module,
            )
        }
        Place::StructField(base_place, field_index) => {
            // Get the base address of the struct
            let base_addr = resolve_place_to_addr(base_place, builder, cranelift_stack_slots, mir, module)?;

            // We need to find the type of the base_place to calculate the offset
            let base_place_type_id = get_place_type_id(base_place, mir).map_err(|e| e.to_string())?;

            let base_type = mir.get_type(base_place_type_id);

            let (struct_fields, is_pointer) = match base_type {
                MirType::Struct { fields, .. } => (fields, false),
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    if let MirType::Struct { fields, .. } = pointee_type {
                        (fields, true)
                    } else {
                        return Err("Base of StructField is not a struct type".to_string());
                    }
                }
                _ => return Err("Base of StructField is not a struct type".to_string()),
            };

            let mut offset = 0;
            for i in 0..*field_index {
                let (_, field_type_id) = struct_fields.get(i).ok_or("Field index out of bounds")?;
                let field_type = mir.get_type(*field_type_id);
                offset += mir_type_size(field_type, mir)?;
            }

            let final_addr = if is_pointer {
                // If the base is a pointer, we need to load the address it points to first
                builder.ins().load(types::I64, MemFlags::new(), base_addr, 0)
            } else {
                base_addr
            };

            let offset_val = builder.ins().iconst(types::I64, offset as i64);
            Ok(builder.ins().iadd(final_addr, offset_val))
        }
        Place::ArrayIndex(base_place, index_operand) => {
            // Get the base address of the array/pointer
            let base_addr = resolve_place_to_addr(base_place, builder, cranelift_stack_slots, mir, module)?;

            // Resolve the index operand to a value
            let index_val = resolve_operand_to_value(
                index_operand,
                builder,
                types::I64, // Use I64 for index calculations
                cranelift_stack_slots,
                mir,
                module,
            )?;

            // Determine the size of the element by getting the type of the base place
            let base_place_type_id = get_place_type_id(base_place, mir).map_err(|e| e.to_string())?;

            let base_type = mir.get_type(base_place_type_id);

            let element_size = match base_type {
                MirType::Array { element, .. } => {
                    let element_type = mir.get_type(*element);
                    mir_type_size(element_type, mir)?
                }
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    mir_type_size(pointee_type, mir)?
                }
                _ => return Err("Base of ArrayIndex is not an array or pointer".to_string()),
            };

            let element_size_val = builder.ins().iconst(types::I64, element_size as i64);
            let offset = builder.ins().imul(index_val, element_size_val);

            Ok(builder.ins().iadd(base_addr, offset))
        }
    }
}
/// MIR to Cranelift IR Lowerer
pub struct MirToCraneliftLowerer {
    builder_context: FunctionBuilderContext,
    module: ObjectModule,
    mir: SemaOutput, // NOTE: need better nama
    cranelift_stack_slots: HashMap<LocalId, StackSlot>,
    // Store compiled functions for dumping
    compiled_functions: HashMap<String, String>,

    emit_kind: EmitKind,
}

/// NOTE: we use panic!() to ICE because codegen rely on correct MIR, so if we give invalid MIR, then problem is in previous phase
impl MirToCraneliftLowerer {
    pub fn new(mir: SemaOutput) -> Self {
        let triple = Triple::host();
        let builder = ObjectBuilder::new(
            cranelift::prelude::isa::lookup(triple)
                .unwrap()
                .finish(cranelift::prelude::settings::Flags::new(
                    cranelift::prelude::settings::builder(),
                ))
                .unwrap(),
            "main",
            cranelift_module::default_libcall_names(),
        )
        .unwrap();
        let module = ObjectModule::new(builder);

        Self {
            builder_context: FunctionBuilderContext::new(),
            // ctx: module.make_context(),
            module,
            mir,
            cranelift_stack_slots: HashMap::new(),
            compiled_functions: HashMap::new(),
            emit_kind: EmitKind::Object,
        }
    }

    pub(crate) fn compile_module(mut self, emit_kind: EmitKind) -> Result<ClifOutput, String> {
        self.emit_kind = emit_kind;
        self.populate_state();

        // Define all global variables in the module
        for (_global_id, global) in &self.mir.globals {
            let data_id = self
                .module
                .declare_data(global.name.as_str(), Linkage::Export, true, false)
                .map_err(|e| format!("Failed to declare global data: {:?}", e))?;

            let mut data_description = DataDescription::new();

            if let Some(const_id) = global.initial_value {
                if let Some(const_val) = self.mir.constants.get(&const_id) {
                    let initial_value_bytes = match const_val {
                        ConstValue::Int(val) => val.to_le_bytes().to_vec(),
                        ConstValue::Float(val) => {
                            let global_type = self.mir.get_type(global.type_id);
                            if let MirType::Float { width } = global_type {
                                if *width == 64 {
                                    val.to_le_bytes().to_vec()
                                } else {
                                    (*val as f32).to_le_bytes().to_vec()
                                }
                            } else {
                                (*val as f32).to_le_bytes().to_vec()
                            }
                        }
                        ConstValue::Bool(val) => vec![*val as u8],
                        ConstValue::Null => {
                            let pointer_size = self.module.target_config().pointer_bytes() as usize;
                            vec![0; pointer_size]
                        }
                        ConstValue::String(s) => {
                            let mut bytes = s.as_bytes().to_vec();
                            bytes.push(0);
                            bytes
                        }
                        _ => {
                            let global_type = self.mir.get_type(global.type_id);
                            let size = mir_type_size(global_type, &self.mir)? as usize;
                            vec![0; size]
                        }
                    };
                    data_description.define(initial_value_bytes.into_boxed_slice());
                } else {
                    let global_type = self.mir.get_type(global.type_id);
                    let size = mir_type_size(global_type, &self.mir)? as usize;
                    data_description.define_zeroinit(size);
                }
            } else {
                let global_type = self.mir.get_type(global.type_id);
                let size = mir_type_size(global_type, &self.mir)? as usize;
                data_description.define_zeroinit(size);
            }

            self.module
                .define_data(data_id, &data_description)
                .map_err(|e| format!("Failed to define global data: {:?}", e))?;
        }

        // Lower all functions that have definitions (not just declarations)
        for func_id in self.mir.module.functions.clone() {
            // Only lower functions that are defined (have bodies)
            if let Some(func) = self.mir.functions.get(&func_id)
                && matches!(func.kind, MirFunctionKind::Defined) {
                    self.lower_function(func_id)
                        .map_err(|e| format!("Error lowering function: {}", e))?;
                }
        }

        // Finalize and return the compiled code
        let product = self.module.finish();
        let code = product
            .object
            .write()
            .map_err(|e| format!("Failed to write object file: {:?}", e))?;

        if emit_kind == EmitKind::Object {
            Ok(ClifOutput::ObjectFile(code))
        } else {
            // For Clif dump, concatenate all function IRs
            let mut clif_dump = String::new();
            for (func_name, func_ir) in &self.compiled_functions {
                clif_dump.push_str(&format!("; Function: {}\n", func_name));
                clif_dump.push_str(func_ir);
                clif_dump.push_str("\n\n");
            }
            Ok(ClifOutput::ClifDump(clif_dump))
        }
    }

    /// Populate state from MIR module
    fn populate_state(&mut self) {
        // Populate types from the MIR module
        for (index, mir_type) in self.mir.module.types.iter().enumerate() {
            let type_id = TypeId::new((index + 1) as u32).unwrap(); // Types are 1-indexed
            self.mir.types.insert(type_id, mir_type.clone());
        }

        // Populate constants from the MIR module
        for (index, const_value) in self.mir.module.constants.iter().enumerate() {
            let const_id = ConstValueId::new((index + 1) as u32).unwrap(); // Constants are 1-indexed
            self.mir.constants.insert(const_id, const_value.clone());
        }

        // The globals and functions are already populated in the constructor
        // from the semantic analyzer, but we need to make sure constants are also
        // accessible through the globals' initial_value field
        // No additional population needed for globals as they're set in constructor

        // If no functions were found, create a default main function
        if self.mir.functions.is_empty() {
            let func_id = MirFunctionId::new(1).unwrap();
            let mut func = MirFunction::new_defined(func_id, NameId::new("main"), TypeId::new(1).unwrap());

            let entry_block_id = MirBlockId::new(1).unwrap();
            let mut entry_block = MirBlock::new(entry_block_id);

            // Default to returning 0
            let return_const_id = ConstValueId::new((self.mir.constants.len() + 1) as u32).unwrap();
            self.mir.constants.insert(return_const_id, ConstValue::Int(0));
            let return_operand = Operand::Constant(return_const_id);
            entry_block.terminator = Terminator::Return(Some(return_operand));

            func.entry_block = Some(entry_block_id);
            func.blocks.push(entry_block_id);

            self.mir.functions.insert(func_id, func);
            self.mir.blocks.insert(entry_block_id, entry_block);
        }
    }

    /// Lower a MIR function to Cranelift IR using 3-phase algorithm
    fn lower_function(&mut self, func_id: MirFunctionId) -> Result<(), String> {
        let func = self.mir.get_function(func_id);
        // Create a fresh context for this function
        let mut func_ctx = self.module.make_context();

        // Set up function signature using the actual return type from MIR
        func_ctx.func.signature.params.clear();

        // Get the return type from MIR and convert to Cranelift type
        let return_type = self.mir.get_type(func.return_type);
        let return_type_opt = mir_type_to_cranelift_type(return_type);

        // Add parameters from MIR function signature
        let mut param_types = Vec::new();
        for &param_id in &func.params {
            let param_local = self.mir.get_local(param_id);
            let param_type = mir_type_to_cranelift_type(self.mir.get_type(param_local.type_id)).unwrap();
            func_ctx.func.signature.params.push(AbiParam::new(param_type));
            param_types.push(param_type);
        }

        // Only add return parameter if the function has a non-void return type
        if let Some(return_type) = return_type_opt {
            func_ctx.func.signature.returns.push(AbiParam::new(return_type));
        }

        // Create a function builder with the fresh context
        let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut self.builder_context);

        // Create variables for function parameters (will be defined when we switch to entry block)
        // We'll handle this after creating all blocks

        self.cranelift_stack_slots.clear(); // Clear for each function

        // Combine locals and params for slot allocation
        let all_locals: Vec<LocalId> = func.locals.iter().chain(func.params.iter()).cloned().collect();

        for &local_id in &all_locals {
            let local = self.mir.get_local(local_id);
            let local_type = self.mir.get_type(local.type_id);
            let size = mir_type_size(local_type, &self.mir)?;

            // Don't allocate space for zero-sized types
            if size > 0 {
                let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 0));
                self.cranelift_stack_slots.insert(local_id, slot);
            }
        }
        // PHASE 1️⃣ — Create all Cranelift blocks first (no instructions)
        let mut cl_blocks = HashMap::new();

        for &block_id in &func.blocks {
            let cl_block = builder.create_block();
            cl_blocks.insert(block_id, cl_block);
        }

        // PHASE 2️⃣ — Lower block content (without sealing)

        // Use worklist algorithm for proper traversal
        let mut worklist = vec![func.entry_block.expect("Defined function must have entry block")];
        let mut visited = HashSet::new();

        while let Some(current_block_id) = worklist.pop() {
            if visited.contains(&current_block_id) {
                continue;
            }
            visited.insert(current_block_id);

            let cl_block = cl_blocks
                .get(&current_block_id)
                .ok_or_else(|| format!("Block {} not found in mapping", current_block_id.get()))?;
            builder.switch_to_block(*cl_block);

            // If this is the entry block, set up its parameters
            if Some(current_block_id) == func.entry_block {
                // Add function parameters as block parameters
                for &param_type in &param_types {
                    builder.append_block_param(*cl_block, param_type);
                }

                // Store incoming parameter values into their stack slots
                let param_values: Vec<Value> = builder.block_params(*cl_block).to_vec();
                for (&param_id, param_value) in func.params.iter().zip(param_values.into_iter()) {
                    if let Some(stack_slot) = self.cranelift_stack_slots.get(&param_id) {
                        builder.ins().stack_store(param_value, *stack_slot, 0);
                    }
                }
            }

            // Get the MIR block
            let mir_block = self
                .mir
                .blocks
                .get(&current_block_id)
                .ok_or_else(|| format!("Block {} not found in MIR", current_block_id.get()))?;

            // ========================================================================
            // SECTION 1: Process statements within this block
            // ========================================================================
            let statements_to_process: Vec<MirStmt> = mir_block
                .statements
                .iter()
                .filter_map(|&stmt_id| self.mir.statements.get(&stmt_id).cloned())
                .collect();

            // Process statements
            for stmt in &statements_to_process {
                match stmt {
                    MirStmt::Assign(place, rvalue) => {
                        // Process the rvalue to get a Cranelift value first
                        let rvalue_result = match rvalue {
                            Rvalue::Use(operand) => resolve_operand_to_value(
                                operand,
                                &mut builder,
                                types::I32, // Assuming i32 for now
                                &self.cranelift_stack_slots,
                                &self.mir,
                                &mut self.module,
                            ),
                            Rvalue::Call(call_target, args) => emit_function_call_impl(
                                call_target,
                                args,
                                &mut builder,
                                &self.mir,
                                &self.cranelift_stack_slots,
                                &mut self.module,
                            ),
                            Rvalue::BinaryOp(op, left_operand, right_operand) => {
                                let left_val = resolve_operand_to_value(
                                    left_operand,
                                    &mut builder,
                                    types::I32,
                                    &self.cranelift_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let right_val = resolve_operand_to_value(
                                    right_operand,
                                    &mut builder,
                                    types::I32,
                                    &self.cranelift_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let result_val = match op {
                                    BinaryOp::Add => builder.ins().iadd(left_val, right_val),
                                    BinaryOp::Sub => builder.ins().isub(left_val, right_val),
                                    BinaryOp::Mul => builder.ins().imul(left_val, right_val),
                                    BinaryOp::Div => builder.ins().sdiv(left_val, right_val),
                                    BinaryOp::Mod => builder.ins().srem(left_val, right_val),
                                    BinaryOp::BitAnd => builder.ins().band(left_val, right_val),
                                    BinaryOp::BitOr => builder.ins().bor(left_val, right_val),
                                    BinaryOp::BitXor => builder.ins().bxor(left_val, right_val),
                                    BinaryOp::LShift => builder.ins().ishl(left_val, right_val),
                                    BinaryOp::RShift => builder.ins().sshr(left_val, right_val),
                                    BinaryOp::Equal => {
                                        let cmp_val = builder.ins().icmp(IntCC::Equal, left_val, right_val);
                                        builder.ins().uextend(types::I32, cmp_val)
                                    }
                                    BinaryOp::NotEqual => {
                                        let cmp_val = builder.ins().icmp(IntCC::NotEqual, left_val, right_val);
                                        builder.ins().uextend(types::I32, cmp_val)
                                    }
                                    BinaryOp::Less => {
                                        let cmp_val = builder.ins().icmp(IntCC::SignedLessThan, left_val, right_val);
                                        builder.ins().uextend(types::I32, cmp_val)
                                    }
                                    BinaryOp::LessEqual => {
                                        let cmp_val =
                                            builder.ins().icmp(IntCC::SignedLessThanOrEqual, left_val, right_val);
                                        builder.ins().uextend(types::I32, cmp_val)
                                    }
                                    BinaryOp::Greater => {
                                        let cmp_val = builder.ins().icmp(IntCC::SignedGreaterThan, left_val, right_val);
                                        builder.ins().uextend(types::I32, cmp_val)
                                    }
                                    BinaryOp::GreaterEqual => {
                                        let cmp_val =
                                            builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val);
                                        builder.ins().uextend(types::I32, cmp_val)
                                    }
                                    BinaryOp::LogicAnd | BinaryOp::LogicOr => builder.ins().band(left_val, right_val),
                                    BinaryOp::Comma => right_val,
                                };
                                Ok(result_val)
                            }
                            _ => Ok(builder.ins().iconst(types::I32, 0)),
                        };

                        // Now, assign the resolved value to the place
                        if let Ok(value) = rvalue_result {
                            match place {
                                Place::Local(local_id) => {
                                    // Check if this local has a stack slot (non-void types)
                                    if let Some(stack_slot) = self.cranelift_stack_slots.get(local_id) {
                                        builder.ins().stack_store(value, *stack_slot, 0);
                                    } else {
                                        // This local doesn't have a stack slot (likely a void type)
                                        // Check if it's actually a void type to provide a better warning
                                        if let Some(local) = self.mir.locals.get(local_id)
                                            && let Some(local_type) = self.mir.types.get(&local.type_id)
                                            && !matches!(local_type, MirType::Void)
                                        {
                                            eprintln!("Warning: Stack slot not found for local {}", local_id.get());
                                        }
                                    }
                                }
                                _ => {
                                    // This covers StructField, ArrayIndex, Deref, and Global assignments
                                    match resolve_place_to_addr(
                                        place,
                                        &mut builder,
                                        &self.cranelift_stack_slots,
                                        &self.mir,
                                        &mut self.module,
                                    ) {
                                        Ok(addr) => {
                                            builder.ins().store(MemFlags::new(), value, addr, 0);
                                        }
                                        Err(e) => {
                                            eprintln!("Warning: Failed to resolve place address for assignment: {}", e);
                                        }
                                    }
                                }
                            }
                        } else if let Err(e) = rvalue_result {
                            eprintln!("Warning: Failed to resolve rvalue: {}", e);
                        }
                    }

                    MirStmt::Store(operand, place) => {
                        // We need to determine the correct type for the operand
                        let place_type_id = get_place_type_id(place, &self.mir)?;
                        let place_type = self.mir.get_type(place_type_id);
                        let cranelift_type = mir_type_to_cranelift_type(place_type)
                            .ok_or_else(|| "Cannot store to a void type".to_string())?;

                        let value = resolve_operand_to_value(
                            operand,
                            &mut builder,
                            cranelift_type,
                            &self.cranelift_stack_slots,
                            &self.mir,
                            &mut self.module,
                        )?;

                        // Now, store the value into the place
                        match place {
                            Place::Local(local_id) => {
                                let stack_slot = self
                                    .cranelift_stack_slots
                                    .get(local_id)
                                    .ok_or_else(|| format!("Stack slot not found for local {}", local_id.get()))?;
                                builder.ins().stack_store(value, *stack_slot, 0);
                            }
                            _ => {
                                // For other places, resolve to an address and store
                                let addr = resolve_place_to_addr(
                                    place,
                                    &mut builder,
                                    &self.cranelift_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                builder.ins().store(MemFlags::new(), value, addr, 0);
                            }
                        }
                    }

                    MirStmt::Alloc(_place, _type_id) => {
                        // TODO: Implement allocation operations
                        // Alloc operations allocate memory for a place with a specific type
                        todo!("Alloc operation not implemented yet");
                    }

                    MirStmt::Dealloc(_operand) => {
                        // TODO: Implement deallocation operations
                        // Dealloc operations free previously allocated memory
                        todo!("Dealloc operation not implemented yet");
                    }
                }
            }

            // ========================================================================
            // SECTION 2: Process terminator (control flow)
            // ========================================================================
            match &mir_block.terminator {
                Terminator::Goto(target) => {
                    let target_cl_block = cl_blocks
                        .get(target)
                        .ok_or_else(|| format!("Target block {} not found", target.get()))?;
                    builder.ins().jump(*target_cl_block, &[]);
                    worklist.push(*target);
                }

                Terminator::If(cond, then_bb, else_bb) => {
                    let cond_val = resolve_operand_to_value(
                        cond,
                        &mut builder,
                        types::I32,
                        &self.cranelift_stack_slots,
                        &self.mir,
                        &mut self.module,
                    )?;

                    let then_cl_block = cl_blocks
                        .get(then_bb)
                        .ok_or_else(|| format!("'Then' block {} not found", then_bb.get()))?;
                    let else_cl_block = cl_blocks
                        .get(else_bb)
                        .ok_or_else(|| format!("'Else' block {} not found", else_bb.get()))?;

                    builder.ins().brif(cond_val, *then_cl_block, &[], *else_cl_block, &[]);

                    worklist.push(*then_bb);
                    worklist.push(*else_bb);
                }

                Terminator::Return(opt) => {
                    if let Some(operand) = opt {
                        if let Some(ret_type) = return_type_opt {
                            let return_value = resolve_operand_to_value(
                                operand,
                                &mut builder,
                                ret_type,
                                &self.cranelift_stack_slots,
                                &self.mir,
                                &mut self.module,
                            )?;
                            builder.ins().return_(&[return_value]);
                        } else {
                            return Err("Returning a value from a void function".to_string());
                        }
                    } else {
                        builder.ins().return_(&[]);
                    }
                }

                Terminator::Unreachable => {
                    // For unreachable, default to appropriate return based on function type
                    if let Some(ret_type) = return_type_opt {
                        let return_value = builder.ins().iconst(ret_type, 0);
                        builder.ins().return_(&[return_value]);
                    } else {
                        // Void function
                        builder.ins().return_(&[]);
                    }
                }
            }
        }

        // PHASE 3️⃣ — Seal blocks with correct order
        for &mir_block_id in &func.blocks {
            let cl_block = cl_blocks.get(&mir_block_id).expect("Block not found in mapping");
            builder.seal_block(*cl_block);
        }

        // Finalize the function
        builder.finalize();

        // Now declare and define the function
        let linkage = match func.kind {
            MirFunctionKind::Extern => cranelift_module::Linkage::Import,
            MirFunctionKind::Defined => cranelift_module::Linkage::Export,
        };

        let id = self
            .module
            .declare_function(func.name.as_str(), linkage, &func_ctx.func.signature)
            .map_err(|e| format!("Failed to declare function {}: {:?}", func.name, e))?;

        // Only define the function body if it's a defined function (not extern)
        if matches!(func.kind, MirFunctionKind::Defined) {
            self.module
                .define_function(id, &mut func_ctx)
                .map_err(|e| format!("Failed to define function {}: {:?}", func.name, e))?;
        }

        if self.emit_kind == EmitKind::Clif {
            // Store the function IR string for dumping
            let func_ir = func_ctx.func.to_string();
            self.compiled_functions.insert(func.name.to_string(), func_ir);
        }

        Ok(())
    }
}
