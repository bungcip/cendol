//! MIR to Cranelift IR lowering module
//!
//! This module provides the mechanical translation from MIR to Cranelift IR.
//! The translation follows these rules:
//! - No C logic
//! - Assume MIR is valid

use crate::ast::NameId;
use crate::mir::MirProgram;
use crate::mir::{
    BinaryFloatOp, BinaryIntOp, CallTarget, ConstValue, ConstValueId, GlobalId, LocalId, MirBlock, MirBlockId,
    MirFunction, MirFunctionId, MirFunctionKind, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId,
    UnaryFloatOp, UnaryIntOp,
};
use cranelift::codegen::ir::{StackSlot, StackSlotData, StackSlotKind};
use cranelift::prelude::{
    AbiParam, Block, Configurable, FloatCC, FunctionBuilderContext, InstBuilder, IntCC, MemFlags, Signature, Type,
    Value, types,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
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
fn convert_type(mir_type: &MirType) -> Option<Type> {
    match mir_type {
        MirType::Void => None,
        MirType::Bool => Some(types::I8), // Booleans as i8 (standard C)

        MirType::I8 | MirType::U8 => Some(types::I8),
        MirType::I16 | MirType::U16 => Some(types::I16),
        MirType::I32 | MirType::U32 => Some(types::I32),
        MirType::I64 | MirType::U64 => Some(types::I64),
        MirType::F32 => Some(types::F32),
        MirType::F64 => Some(types::F64),
        MirType::Pointer { .. } => Some(types::I64), // Pointers are 64-bit on most modern systems

        MirType::Array { .. } | MirType::Record { .. } => None,
        MirType::Function { .. } => Some(types::I64), // Function pointers
    }
}

/// Helper function to get the size of a MIR type in bytes
pub(crate) fn mir_type_size(mir_type: &MirType, mir: &MirProgram) -> Result<u32, String> {
    match mir_type {
        MirType::I8 | MirType::U8 => Ok(1),
        MirType::I16 | MirType::U16 => Ok(2),
        MirType::I32 | MirType::U32 => Ok(4),
        MirType::I64 | MirType::U64 => Ok(8),
        MirType::F32 => Ok(4),
        MirType::F64 => Ok(8),

        MirType::Pointer { .. } => Ok(mir.pointer_width as u32),
        MirType::Array { layout, .. } => Ok(layout.size as u32),
        MirType::Record { layout, .. } => Ok(layout.size as u32),
        MirType::Bool => Ok(1),
        MirType::Void => Ok(0),
        // For other complex types, let's have a default, though this should be comprehensive.
        _ => Ok(4), // Default size for other types
    }
}

/// Helper function to get type layout information for emit_const
pub(crate) fn get_type_layout(mir_type: &MirType, _mir: &MirProgram) -> Result<MirType, String> {
    Ok(mir_type.clone())
}

/// Context for constant emission
pub(crate) struct EmitContext<'a> {
    pub mir: &'a MirProgram,
    pub func_id_map: &'a HashMap<MirFunctionId, FuncId>,
    pub data_id_map: &'a HashMap<GlobalId, DataId>,
}

/// Helper to emit integer constants
fn emit_const_int(val: i64, layout: &MirType, output: &mut Vec<u8>) -> Result<(), String> {
    match layout {
        MirType::I8 | MirType::U8 => {
            let bytes = (val as i8).to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::I16 | MirType::U16 => {
            let bytes = (val as i16).to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::I32 | MirType::U32 => {
            let bytes = (val as i32).to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::I64 | MirType::U64 => {
            let bytes = val.to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::Bool => {
            let byte = if val != 0 { 1u8 } else { 0u8 };
            output.push(byte);
        }
        MirType::Pointer { .. } => {
            let bytes = (val).to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        _ => {
            let bytes = (val as i32).to_le_bytes();
            output.extend_from_slice(&bytes);
        }
    }
    Ok(())
}

/// Helper to emit float constants
fn emit_const_float(val: f64, layout: &MirType, output: &mut Vec<u8>) -> Result<(), String> {
    match layout {
        MirType::F32 => {
            let bytes = (val as f32).to_bits().to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::F64 => {
            let bytes = val.to_bits().to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        _ => {
            let bytes = val.to_bits().to_le_bytes();
            output.extend_from_slice(&bytes);
        }
    }
    Ok(())
}

/// Helper to emit struct constants
fn emit_const_struct(
    fields: &[(usize, ConstValueId)],
    layout: &MirType,
    output: &mut Vec<u8>,
    ctx: &EmitContext,
    mut module: Option<&mut ObjectModule>,
    mut data_description: Option<&mut DataDescription>,
    base_offset: u32,
) -> Result<(), String> {
    match layout {
        MirType::Record {
            layout: record_layout,
            field_types,
            ..
        } => {
            // Initialize the entire struct with zeros
            let struct_size = record_layout.size as usize;
            let mut struct_bytes = vec![0u8; struct_size];

            // Emit each field at its proper offset
            for (field_index, field_const_id) in fields {
                if *field_index < record_layout.field_offsets.len() {
                    let field_offset = record_layout.field_offsets[*field_index] as usize;

                    let field_type_id = field_types
                        .get(*field_index)
                        .ok_or_else(|| format!("Field index {} out of bounds", field_index))?;

                    let field_type = ctx.mir.get_type(*field_type_id);

                    let mut field_bytes = Vec::new();
                    emit_const(
                        *field_const_id,
                        field_type,
                        &mut field_bytes,
                        ctx,
                        reborrow_module(&mut module),
                        reborrow_data_description(&mut data_description),
                        base_offset + field_offset as u32,
                    )?;

                    // Copy the field bytes into the struct buffer
                    if field_offset + field_bytes.len() <= struct_size {
                        struct_bytes[field_offset..field_offset + field_bytes.len()].copy_from_slice(&field_bytes);
                    } else {
                        return Err(format!(
                            "Field emission overflow: offset {} + size {} > struct size {}",
                            field_offset,
                            field_bytes.len(),
                            struct_size
                        ));
                    }
                }
            }
            output.extend_from_slice(&struct_bytes);
            Ok(())
        }
        _ => Err("StructLiteral with non-record type".to_string()),
    }
}

/// Helper to emit array constants
fn emit_const_array(
    elements: &[ConstValueId],
    layout: &MirType,
    output: &mut Vec<u8>,
    ctx: &EmitContext,
    mut module: Option<&mut ObjectModule>,
    mut data_description: Option<&mut DataDescription>,
    base_offset: u32,
) -> Result<(), String> {
    match layout {
        MirType::Array {
            element,
            size,
            layout: array_layout,
        } => {
            // Emit each element according to the array layout
            for (i, element_const_id) in elements.iter().enumerate() {
                if i >= *size {
                    break; // Don't emit more elements than the array size
                }

                let element_type = ctx.mir.get_type(*element);
                let element_size = mir_type_size(element_type, ctx.mir)? as usize;

                // Calculate offset for this element
                let element_offset = (i * array_layout.stride as usize) as u32;

                emit_const(
                    *element_const_id,
                    element_type,
                    output,
                    ctx,
                    reborrow_module(&mut module),
                    reborrow_data_description(&mut data_description),
                    base_offset + element_offset,
                )?;

                // Add padding if needed for stride > element size
                if array_layout.stride as usize > element_size {
                    let padding = array_layout.stride as usize - element_size;
                    output.extend_from_slice(&vec![0u8; padding]);
                }
            }

            // Fill remaining space with zeros if array is partially initialized
            let emitted_size = elements.len() * array_layout.stride as usize;
            if emitted_size < array_layout.size as usize {
                let remaining = array_layout.size as usize - emitted_size;
                output.extend_from_slice(&vec![0u8; remaining]);
            }
            Ok(())
        }
        _ => Err("ArrayLiteral with non-array type".to_string()),
    }
}

/// Emit a constant value to the output buffer based on its type layout
pub(crate) fn emit_const(
    const_id: ConstValueId,
    layout: &MirType,
    output: &mut Vec<u8>,
    ctx: &EmitContext,
    mut module: Option<&mut ObjectModule>,
    mut data_description: Option<&mut DataDescription>,
    offset: u32,
) -> Result<(), String> {
    let const_value = ctx
        .mir
        .constants
        .get(&const_id)
        .ok_or_else(|| format!("Constant ID {} not found", const_id.get()))?;

    match const_value {
        ConstValue::Int(val) => emit_const_int(*val, layout, output),
        ConstValue::Float(val) => emit_const_float(*val, layout, output),
        ConstValue::Bool(val) => {
            let byte = if *val { 1u8 } else { 0u8 };
            output.push(byte);
            Ok(())
        }
        ConstValue::Null => {
            // Emit null as all zeros (pointer-sized)
            let null_bytes = 0i64.to_le_bytes();
            output.extend_from_slice(&null_bytes);
            Ok(())
        }
        ConstValue::Zero => {
            // Emit zeros for the entire type size
            let size = mir_type_size(layout, ctx.mir)? as usize;
            output.extend_from_slice(&vec![0u8; size]);
            Ok(())
        }
        ConstValue::GlobalAddress(global_id) => {
            // Handle Global Relocation
            if let (Some(dd), Some(mod_obj)) = (&mut data_description, &mut module) {
                if let Some(&data_id) = ctx.data_id_map.get(global_id) {
                    let global_val = mod_obj.declare_data_in_data(data_id, dd);
                    dd.write_data_addr(offset, global_val, 0);
                } else {
                    return Err(format!(
                        "Global ID {} not found in map during relocation",
                        global_id.get()
                    ));
                }
            }

            // Emit zero placeholder
            let addr_bytes = 0i64.to_le_bytes();
            output.extend_from_slice(&addr_bytes);
            Ok(())
        }
        ConstValue::FunctionAddress(func_id) => {
            // Handle Function Relocation
            if let (Some(dd), Some(mod_obj)) = (&mut data_description, &mut module) {
                if let Some(&clif_func_id) = ctx.func_id_map.get(func_id) {
                    let func_ref = mod_obj.declare_func_in_data(clif_func_id, dd);
                    dd.write_function_addr(offset, func_ref);
                } else {
                    println!(
                        "Warning: Function ID {} not found in map during relocation. Maps available: {:?}",
                        func_id.get(),
                        ctx.func_id_map.keys()
                    );
                }
            }

            // Emit zero placeholder
            let addr_bytes = 0i64.to_le_bytes();
            output.extend_from_slice(&addr_bytes);
            Ok(())
        }
        ConstValue::StructLiteral(fields) => {
            emit_const_struct(fields, layout, output, ctx, module, data_description, offset)
        }
        ConstValue::ArrayLiteral(elements) => {
            emit_const_array(elements, layout, output, ctx, module, data_description, offset)
        }
        ConstValue::Cast(_type_id, inner_id) => {
            emit_const(*inner_id, layout, output, ctx, module, data_description, offset)
        }
    }
}

fn reborrow_module<'b>(m: &'b mut Option<&mut ObjectModule>) -> Option<&'b mut ObjectModule> {
    m.as_mut().map(|inner| &mut **inner)
}

fn reborrow_data_description<'b>(dd: &'b mut Option<&mut DataDescription>) -> Option<&'b mut DataDescription> {
    dd.as_mut().map(|inner| &mut **inner)
}

/// Helper to prepare a function signature for a call
fn prepare_call_signature(
    call_conv: cranelift::codegen::isa::CallConv,
    return_type_id: TypeId,
    param_types: &[TypeId],
    args: &[Operand],
    mir: &MirProgram,
    is_variadic: bool,
) -> Signature {
    let mut sig = Signature::new(call_conv);

    // Return type
    let return_mir_type = mir.get_type(return_type_id);
    let return_type_opt = match convert_type(return_mir_type) {
        Some(t) => Some(t),
        None if matches!(return_mir_type, MirType::Record { .. } | MirType::Array { .. }) => Some(types::I64),
        None => None,
    };
    if let Some(ret_type) = return_type_opt {
        sig.returns.push(AbiParam::new(ret_type));
    }

    // Fixed parameters
    for &param_type_id in param_types {
        let mir_type = mir.get_type(param_type_id);
        let param_type = match convert_type(mir_type) {
            Some(t) => t,
            None if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) => types::I64,
            None => types::I32, // Should not happen for valid MIR
        };
        sig.params.push(AbiParam::new(param_type));
    }

    // Variadic arguments (if any) - structs are expanded to multiple I64 slots
    for arg in args.iter().skip(param_types.len()) {
        let arg_type_id = get_operand_type_id(arg, mir).ok();
        if let Some(type_id) = arg_type_id {
            let mir_type = mir.get_type(type_id);
            if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) {
                // For structs/arrays, calculate how many I64 slots we need
                let size = mir_type_size(mir_type, mir).unwrap_or(8);
                let num_slots = size.div_ceil(8) as usize; // Round up to nearest 8 bytes
                for _ in 0..num_slots {
                    sig.params.push(AbiParam::new(types::I64));
                }
                continue;
            }
        }
        let mut arg_type = get_operand_cranelift_type(arg, mir).unwrap_or(types::I32);
        // Normalized Variadic Signature hack: promote variadic GPR args to i64
        if is_variadic && arg_type.is_int() && arg_type.bits() < 64 {
            arg_type = types::I64;
        }
        sig.params.push(AbiParam::new(arg_type));
    }

    // Normalized Variadic Signature hack: Ensure at least 16 slots for variadic functions
    // This matches the 16-slot spill area in setup_signature
    if is_variadic {
        let current_gpr_count = sig.params.len();
        let total_variadic_slots = 16;
        if current_gpr_count < total_variadic_slots {
            for _ in 0..(total_variadic_slots - current_gpr_count) {
                sig.params.push(AbiParam::new(types::I64));
            }
        }
    }

    sig
}

/// Helper to resolve call arguments to values
fn resolve_call_arguments(
    args: &[Operand],
    sig: &Signature,
    builder: &mut FunctionBuilder,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &MirProgram,
    module: &mut ObjectModule,
) -> Result<Vec<Value>, String> {
    let mut arg_values = Vec::new();
    for i in 0..sig.params.len() {
        let param_type = sig.params[i].value_type;
        if i < args.len() {
            let arg = &args[i];
            match resolve_operand_to_value(arg, builder, param_type, cranelift_stack_slots, mir, module) {
                Ok(value) => arg_values.push(value),
                Err(e) => return Err(format!("Failed to resolve function argument: {}", e)),
            }
        } else {
            // Padding for variadic normalized signature (SysV x86_64 hack)
            arg_values.push(builder.ins().iconst(param_type, 0));
        }
    }
    Ok(arg_values)
}

/// Helper to resolve variadic call arguments, expanding structs to multiple I64 values
fn resolve_variadic_call_arguments(
    args: &[Operand],
    fixed_param_count: usize,
    sig: &Signature,
    builder: &mut FunctionBuilder,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &MirProgram,
    module: &mut ObjectModule,
) -> Result<Vec<Value>, String> {
    let mut arg_values = Vec::new();
    let mut sig_idx = 0;

    for (arg_idx, arg) in args.iter().enumerate() {
        if sig_idx >= sig.params.len() {
            break;
        }

        let param_type = sig.params[sig_idx].value_type;

        // Check if this is a variadic struct argument
        if arg_idx >= fixed_param_count
            && let Ok(type_id) = get_operand_type_id(arg, mir)
        {
            let mir_type = mir.get_type(type_id);
            if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) {
                // Get the struct address
                let struct_addr =
                    resolve_operand_to_value(arg, builder, types::I64, cranelift_stack_slots, mir, module)?;

                // Calculate how many I64 slots this struct needs
                let size = mir_type_size(mir_type, mir).unwrap_or(8);
                let num_slots = size.div_ceil(8) as usize;

                // Load each I64 chunk from the struct
                for slot in 0..num_slots {
                    let offset = (slot * 8) as i32;
                    let value = builder.ins().load(types::I64, MemFlags::new(), struct_addr, offset);
                    arg_values.push(value);
                    sig_idx += 1;
                }
                continue;
            }
        }

        // Non-struct argument (or fixed param)
        match resolve_operand_to_value(arg, builder, param_type, cranelift_stack_slots, mir, module) {
            Ok(value) => arg_values.push(value),
            Err(e) => return Err(format!("Failed to resolve function argument: {}", e)),
        }
        sig_idx += 1;
    }

    // Padding for remaining signature params (variadic slot padding)
    while sig_idx < sig.params.len() {
        let param_type = sig.params[sig_idx].value_type;
        arg_values.push(builder.ins().iconst(param_type, 0));
        sig_idx += 1;
    }

    Ok(arg_values)
}

/// Standalone function to emit a proper function call that actually invokes the function
fn emit_function_call_impl(
    call_target: &CallTarget,
    args: &[Operand],
    builder: &mut FunctionBuilder,
    mir: &MirProgram,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    module: &mut ObjectModule,
    expected_type: Type,
) -> Result<Value, String> {
    match call_target {
        CallTarget::Direct(func_id) => {
            let func = mir.get_function(*func_id);
            // Collect parameter types
            let param_types: Vec<TypeId> = func.params.iter().map(|&p| mir.get_local(p).type_id).collect();

            if func.is_variadic {
                // 1. Declare the function with its canonical signature (fixed params only)
                // We pass empty args here so it only creates fixed params signature
                let canonical_sig = prepare_call_signature(
                    builder.func.signature.call_conv,
                    func.return_type,
                    &param_types,
                    &[], // No extra args for canonical declaration
                    mir,
                    func.is_variadic,
                );

                let linkage = match func.kind {
                    MirFunctionKind::Extern => cranelift_module::Linkage::Import,
                    MirFunctionKind::Defined => cranelift_module::Linkage::Export,
                };

                let func_decl = module
                    .declare_function(func.name.as_str(), linkage, &canonical_sig)
                    .map_err(|e| format!("Failed to declare variadic function {}: {:?}", func.name, e))?;

                // 2. Get the function address
                let func_ref = module.declare_func_in_func(func_decl, builder.func);
                let func_addr = builder.ins().func_addr(types::I64, func_ref);

                // 3. Construct the call-site signature with all arguments (fixed + variadic)
                let call_sig = prepare_call_signature(
                    builder.func.signature.call_conv,
                    func.return_type,
                    &param_types,
                    args,
                    mir,
                    func.is_variadic,
                );
                // 4. Resolve arguments (use variadic version for struct expansion)
                let arg_values = resolve_variadic_call_arguments(
                    args,
                    param_types.len(),
                    &call_sig,
                    builder,
                    cranelift_stack_slots,
                    mir,
                    module,
                )?;

                // 5. Perform indirect call
                let sig_ref = builder.import_signature(call_sig);
                let call_inst = builder.ins().call_indirect(sig_ref, func_addr, &arg_values);

                let call_results = builder.inst_results(call_inst);
                if !call_results.is_empty() {
                    Ok(call_results[0])
                } else {
                    Ok(builder.ins().iconst(expected_type, 0))
                }
            } else {
                // Regular (non-variadic) function call
                let sig = prepare_call_signature(
                    builder.func.signature.call_conv,
                    func.return_type,
                    &param_types,
                    args,
                    mir,
                    func.is_variadic,
                );

                // Resolve arguments before declaring function to ensure types match?
                // No, we resolve against the signature.
                let arg_values = resolve_call_arguments(args, &sig, builder, cranelift_stack_slots, mir, module)?;

                let linkage = match func.kind {
                    MirFunctionKind::Extern => cranelift_module::Linkage::Import,
                    MirFunctionKind::Defined => cranelift_module::Linkage::Export,
                };

                let func_decl = module
                    .declare_function(func.name.as_str(), linkage, &sig)
                    .map_err(|e| format!("Failed to declare function {}: {:?}", func.name, e))?;

                let local_callee = module.declare_func_in_func(func_decl, builder.func);
                let call_inst = builder.ins().call(local_callee, &arg_values);

                let call_results = builder.inst_results(call_inst);
                if !call_results.is_empty() {
                    Ok(call_results[0])
                } else {
                    Ok(builder.ins().iconst(expected_type, 0))
                }
            }
        }
        CallTarget::Indirect(func_operand) => {
            // 1. Get the type of the function pointer
            let func_ptr_type_id = get_operand_type_id(func_operand, mir)
                .map_err(|e| format!("Failed to get function pointer type: {}", e))?;

            let func_ptr_type = mir.get_type(func_ptr_type_id);

            // 2. It must be a pointer to a function OR a function type (if it was dereferenced)
            let ((return_type_id, param_types), is_function_type) = match func_ptr_type {
                MirType::Pointer { pointee } => match mir.get_type(*pointee) {
                    MirType::Function { return_type, params } => ((*return_type, params.clone()), false),
                    _ => {
                        return Err(format!(
                            "Indirect call operand points to non-function type: {:?}",
                            mir.get_type(*pointee)
                        ));
                    }
                },
                MirType::Function { return_type, params } => ((*return_type, params.clone()), true),
                _ => return Err(format!("Indirect call operand is not a pointer: {:?}", func_ptr_type)),
            };

            // 3. Construct the signature
            let is_variadic_func = match mir.get_type(func_ptr_type_id) {
                MirType::Pointer { pointee } => match mir.get_type(*pointee) {
                    MirType::Function { .. } => {
                        // For now we don't have is_variadic in MirType::Function
                        false
                    }
                    _ => false,
                },
                _ => false,
            };

            let sig = prepare_call_signature(
                builder.func.signature.call_conv,
                return_type_id,
                &param_types,
                args,
                mir,
                is_variadic_func,
            );

            // 4. Resolve the function pointer operand to a value
            let callee_val = if is_function_type {
                // If the operand has Function type, it means it's an l-value representing the function (like *ptr).
                // We need its address.
                match func_operand {
                    Operand::Copy(place) => resolve_place_to_addr(place, builder, cranelift_stack_slots, mir, module)?,
                    _ => {
                        resolve_operand_to_value(func_operand, builder, types::I64, cranelift_stack_slots, mir, module)?
                    }
                }
            } else {
                resolve_operand_to_value(
                    func_operand,
                    builder,
                    types::I64, // Function pointers are I64
                    cranelift_stack_slots,
                    mir,
                    module,
                )?
            };

            // 5. Resolve arguments
            let arg_values = resolve_call_arguments(args, &sig, builder, cranelift_stack_slots, mir, module)?;

            // 6. Import signature
            let sig_ref = builder.import_signature(sig);

            // 7. Call indirect
            let call_inst = builder.ins().call_indirect(sig_ref, callee_val, &arg_values);

            // Extract the return value from the call instruction
            let call_results = builder.inst_results(call_inst);
            if !call_results.is_empty() {
                Ok(call_results[0])
            } else {
                Ok(builder.ins().iconst(types::I32, 0))
            }
        }
    }
}

/// Helper function to convert boolean to integer (0 or 1)
fn emit_bool_to_int(val: Value, target_type: Type, builder: &mut FunctionBuilder) -> Value {
    let one = builder.ins().iconst(target_type, 1);
    let zero = builder.ins().iconst(target_type, 0);
    builder.ins().select(val, one, zero)
}

/// Helper function to emit a memcpy call
fn emit_memcpy(
    dest: Value,
    src: Value,
    size: i64,
    builder: &mut FunctionBuilder,
    module: &mut ObjectModule,
) -> Result<(), String> {
    let mut sig = Signature::new(builder.func.signature.call_conv);
    sig.params.push(AbiParam::new(types::I64)); // dest
    sig.params.push(AbiParam::new(types::I64)); // src
    sig.params.push(AbiParam::new(types::I64)); // size
    sig.returns.push(AbiParam::new(types::I64)); // returns dest (ignored)

    let callee = module
        .declare_function("memcpy", Linkage::Import, &sig)
        .map_err(|e| format!("Failed to declare memcpy: {:?}", e))?;
    let local_callee = module.declare_func_in_func(callee, builder.func);

    let size_val = builder.ins().iconst(types::I64, size);
    builder.ins().call(local_callee, &[dest, src, size_val]);
    Ok(())
}

/// Helper function to emit a type conversion in Cranelift
fn emit_type_conversion(val: Value, from: Type, to: Type, is_signed: bool, builder: &mut FunctionBuilder) -> Value {
    if from == to {
        return val;
    }

    // Float to Float
    if from.is_float() && to.is_float() {
        let from_width = from.bits();
        let to_width = to.bits();
        if from_width < to_width {
            return builder.ins().fpromote(to, val);
        } else if from_width > to_width {
            return builder.ins().fdemote(to, val);
        } else {
            return val;
        }
    }

    // Integer to Float
    if from.is_int() && to.is_float() {
        return if is_signed {
            builder.ins().fcvt_from_sint(to, val)
        } else {
            builder.ins().fcvt_from_uint(to, val)
        };
    }

    // Float to Integer
    if from.is_float() && to.is_int() {
        let to_width = to.bits();
        if to_width < 32 {
            // Cranelift x64 backend doesn't support fcvt_to_sint/uint for < 32-bit targets
            // Convert to I32 first, then reduce
            let intermediate = if is_signed {
                builder.ins().fcvt_to_sint(types::I32, val)
            } else {
                builder.ins().fcvt_to_uint(types::I32, val)
            };
            return builder.ins().ireduce(to, intermediate);
        }

        return if is_signed {
            builder.ins().fcvt_to_sint(to, val)
        } else {
            builder.ins().fcvt_to_uint(to, val)
        };
    }

    // General Integer/Pointer/Bool conversions (Extension/Reduction/Bitcast)
    let from_width = from.bits();
    let to_width = to.bits();

    if from_width < to_width {
        // Extension
        if is_signed {
            builder.ins().sextend(to, val)
        } else {
            builder.ins().uextend(to, val)
        }
    } else if from_width > to_width {
        // Reduction
        builder.ins().ireduce(to, val)
    } else {
        // Same width, diff types (e.g. I64 <-> F64 bitcast, or I32 <-> F32 bitcast, or Pointer types)
        // Note: Float bitcasts usually handled above if involving floats, but check standard bitcast rules.
        // Actually bitcast works for any same-sized types.
        builder.ins().bitcast(to, MemFlags::new(), val)
    }
}

/// Helper function to resolve a MIR operand to a Cranelift value
fn resolve_operand_to_value(
    operand: &Operand,
    builder: &mut FunctionBuilder,
    expected_type: Type,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &MirProgram,
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
                ConstValue::GlobalAddress(global_id) => {
                    // Get the global variable and return its address
                    // This handles the array-to-pointer decay for string literals
                    let global = mir.get_global(*global_id);
                    let global_val = module
                        .declare_data(global.name.as_str(), Linkage::Export, true, false)
                        .map_err(|e| format!("Failed to declare global data: {:?}", e))?;
                    let local_id = module.declare_data_in_func(global_val, builder.func);
                    // Global addresses are always pointer-sized (i64)
                    let addr = builder.ins().global_value(types::I64, local_id);
                    Ok(emit_type_conversion(addr, types::I64, expected_type, false, builder))
                }
                ConstValue::FunctionAddress(func_id) => {
                    let func = mir.get_function(*func_id);

                    let mut sig = Signature::new(builder.func.signature.call_conv);

                    // Return type
                    if let Some(ret_type) = convert_type(mir.get_type(func.return_type)) {
                        sig.returns.push(AbiParam::new(ret_type));
                    }

                    // Params
                    for &param_id in &func.params {
                        let param_local = mir.get_local(param_id);
                        let mir_type = mir.get_type(param_local.type_id);
                        let param_type = match convert_type(mir_type) {
                            Some(t) => t,
                            None if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) => types::I64,
                            None => types::I32,
                        };
                        sig.params.push(AbiParam::new(param_type));
                    }

                    let linkage = match func.kind {
                        MirFunctionKind::Extern => Linkage::Import,
                        MirFunctionKind::Defined => Linkage::Export,
                    };

                    let func_decl = module
                        .declare_function(func.name.as_str(), linkage, &sig)
                        .map_err(|e| format!("Failed to declare function {}: {:?}", func.name, e))?;

                    let func_ref = module.declare_func_in_func(func_decl, builder.func);
                    let addr = builder.ins().func_addr(types::I64, func_ref);
                    Ok(emit_type_conversion(addr, types::I64, expected_type, false, builder))
                }
                ConstValue::Cast(type_id, inner_id) => {
                    let mir_type = mir.get_type(*type_id);
                    let target_type = convert_type(mir_type).unwrap_or(types::I32);

                    // For constant casts, we still recursively resolve but with the target type
                    let temp_op = Operand::Constant(*inner_id);
                    let val =
                        resolve_operand_to_value(&temp_op, builder, target_type, cranelift_stack_slots, mir, module)?;

                    Ok(emit_type_conversion(
                        val,
                        target_type,
                        expected_type,
                        is_operand_signed(&temp_op, mir),
                        builder,
                    ))
                }
                _ => Ok(builder.ins().iconst(expected_type, 0)),
            }
        }
        Operand::Copy(place) => {
            // Determine the correct type from the place itself
            let place_type_id =
                get_place_type_id(place, mir).map_err(|e| format!("Failed to get place type: {}", e))?;
            let place_type = mir.get_type(place_type_id);

            if matches!(place_type, MirType::Record { .. } | MirType::Array { .. }) {
                // For aggregate types, resolving the operand value means getting its address
                let addr = resolve_place_to_addr(place, builder, cranelift_stack_slots, mir, module)?;
                return Ok(emit_type_conversion(addr, types::I64, expected_type, false, builder));
            }

            let place_cranelift_type =
                convert_type(place_type).ok_or_else(|| format!("Unsupported place type: {:?}", place_type))?;

            let val = resolve_place_to_value(place, builder, place_cranelift_type, cranelift_stack_slots, mir, module)?;
            Ok(emit_type_conversion(
                val,
                place_cranelift_type,
                expected_type,
                place_type.is_signed(),
                builder,
            ))
        }
        Operand::Cast(type_id, inner_operand) => {
            let inner_type = get_operand_cranelift_type(inner_operand, mir)?;
            let inner_val =
                resolve_operand_to_value(inner_operand, builder, inner_type, cranelift_stack_slots, mir, module)?;

            let mir_type = mir.get_type(*type_id);
            let target_type = convert_type(mir_type).unwrap_or(types::I32);

            let converted = emit_type_conversion(
                inner_val,
                inner_type,
                target_type,
                is_operand_signed(inner_operand, mir),
                builder,
            );
            Ok(emit_type_conversion(
                converted,
                target_type,
                expected_type,
                mir_type.is_signed(),
                builder,
            ))
        }
        Operand::AddressOf(place) => {
            // The value of an AddressOf operand is the address of the place.
            let addr = resolve_place_to_addr(place, builder, cranelift_stack_slots, mir, module)?;
            Ok(emit_type_conversion(addr, types::I64, expected_type, false, builder))
        }
    }
}

/// Helper function to resolve a MIR place to a Cranelift value
fn resolve_place_to_value(
    place: &Place,
    builder: &mut FunctionBuilder,
    expected_type: Type,
    cranelift_stack_slots: &HashMap<LocalId, StackSlot>,
    mir: &MirProgram,
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

/// Helper function to get the Cranelift Type of an operand
fn get_operand_cranelift_type(operand: &Operand, mir: &MirProgram) -> Result<Type, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = mir.constants.get(const_id).expect("constant id not found");
            match const_value {
                // Integer literals in MIR are typically used in integer-sized contexts
                // Default to I32 so common small integer constants (like `4`) match i32
                // places instead of being treated as 64-bit immediates.
                ConstValue::Int(_) => Ok(types::I32),
                ConstValue::Float(_) => Ok(types::F64),
                ConstValue::Bool(_) => Ok(types::I32),
                // Null/Zero/Global addresses are pointer-sized
                ConstValue::Null | ConstValue::Zero | ConstValue::GlobalAddress(_) => Ok(types::I64),
                ConstValue::FunctionAddress(_) => Ok(types::I64),
                ConstValue::StructLiteral(_) => Ok(types::I32),
                ConstValue::ArrayLiteral(_) => Ok(types::I32),
                ConstValue::Cast(type_id, _) => {
                    let mir_type = mir.get_type(*type_id);
                    if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) {
                        return Ok(types::I64);
                    }
                    Ok(convert_type(mir_type).unwrap_or(types::I32))
                }
            }
        }
        Operand::Copy(place) => {
            let place_type_id = get_place_type_id(place, mir)?;
            let place_type = mir.get_type(place_type_id);
            if matches!(place_type, MirType::Record { .. } | MirType::Array { .. }) {
                return Ok(types::I64);
            }
            convert_type(place_type).ok_or_else(|| format!("Unsupported place type: {:?}", place_type))
        }
        Operand::Cast(type_id, _) => {
            let mir_type = mir.get_type(*type_id);
            if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) {
                return Ok(types::I64);
            }
            Ok(convert_type(mir_type).unwrap_or(types::I32))
        }
        Operand::AddressOf(_) => Ok(types::I64), // AddressOf always returns a pointer
    }
}

/// Helper function to check if a MIR type is signed
fn is_operand_signed(operand: &Operand, mir: &MirProgram) -> bool {
    match operand {
        Operand::Copy(place) => {
            if let Ok(type_id) = get_place_type_id(place, mir) {
                return mir.get_type(type_id).is_signed();
            }
        }
        Operand::Cast(type_id, _) => {
            return mir.get_type(*type_id).is_signed();
        }
        Operand::Constant(const_id) => {
            if let Some(ConstValue::Cast(type_id, _)) = mir.constants.get(const_id) {
                return mir.get_type(*type_id).is_signed();
            }
            // Default to signed for integer constants
            return true;
        }
        _ => {}
    }
    false
}

/// Helper function to get the TypeId of an operand
fn get_operand_type_id(operand: &Operand, mir: &MirProgram) -> Result<TypeId, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = mir.constants.get(const_id).expect("constant id not found");
            match const_value {
                ConstValue::Cast(type_id, _) => Ok(*type_id),
                _ => Err("Cannot determine type of raw constant operand".to_string()),
            }
        }
        Operand::Copy(place) => get_place_type_id(place, mir),
        Operand::Cast(type_id, _) => Ok(*type_id),
        Operand::AddressOf(place) => {
            // AddressOf returns a pointer to the place's type.
            // We need to find or create this pointer type in MIR.
            // Actually, for PtrAdd scaling, we only care about the base type of the pointer.
            let place_type_id = get_place_type_id(place, mir)?;
            // We need the TypeId for ptr<place_type_id>
            // Let's see if we can find it in the type table.
            for (id, ty) in &mir.types {
                if let MirType::Pointer { pointee } = ty
                    && *pointee == place_type_id
                {
                    return Ok(*id);
                }
            }
            Err("Pointer type not found in MIR types".to_string())
        }
    }
}

/// Helper function to get the TypeId of a place
fn get_place_type_id(place: &Place, mir: &MirProgram) -> Result<TypeId, String> {
    match place {
        Place::Local(local_id) => {
            let tid = mir.get_local(*local_id).type_id;

            Ok(tid)
        }
        Place::Global(global_id) => {
            let tid = mir.get_global(*global_id).type_id;

            Ok(tid)
        }
        Place::Deref(operand) => {
            // To get the type of a dereference, we need the type of the operand,
            // which should be a pointer. The resulting type is the pointee.
            let operand_type_id = get_operand_type_id(operand, mir)?;
            let operand_type = mir.get_type(operand_type_id);
            match operand_type {
                MirType::Pointer { pointee } => Ok(*pointee),
                _ => Err("Cannot determine type for deref operand".to_string()),
            }
        }
        Place::StructField(base_place, field_index) => {
            let base_type_id = get_place_type_id(base_place, mir)?;
            let base_type = mir.get_type(base_type_id);
            match base_type {
                MirType::Record { field_types, .. } => field_types
                    .get(*field_index)
                    .copied()
                    .ok_or_else(|| "Field index out of bounds".to_string()),
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    if let MirType::Record { field_types, .. } = pointee_type {
                        field_types
                            .get(*field_index)
                            .copied()
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
    mir: &MirProgram,
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
            let linkage = if global.initial_value.is_some() {
                cranelift_module::Linkage::Export
            } else {
                cranelift_module::Linkage::Import
            };

            let global_val = module
                .declare_data(global.name.as_str(), linkage, true, false)
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

            // We need to find the type of the base_place to get the pre-computed field offset
            let base_place_type_id = get_place_type_id(base_place, mir).map_err(|e| e.to_string())?;

            let base_type = mir.get_type(base_place_type_id);

            let (field_offset, is_pointer) = match base_type {
                MirType::Record { layout, .. } => {
                    let offset = layout
                        .field_offsets
                        .get(*field_index)
                        .copied()
                        .ok_or_else(|| format!("Field index {} out of bounds", field_index))?;
                    (offset, false)
                }
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    if let MirType::Record { layout, .. } = pointee_type {
                        let offset = layout
                            .field_offsets
                            .get(*field_index)
                            .copied()
                            .ok_or_else(|| format!("Field index {} out of bounds", field_index))?;
                        (offset, true)
                    } else {
                        return Err("Base of StructField is not a struct type".to_string());
                    }
                }
                _ => return Err("Base of StructField is not a struct type".to_string()),
            };

            let final_addr = if is_pointer {
                // If the base is a pointer, we need to load the address it points to first
                builder.ins().load(types::I64, MemFlags::new(), base_addr, 0)
            } else {
                base_addr
            };

            let offset_val = builder.ins().iconst(types::I64, field_offset as i64);
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

            // Determine the element size using pre-computed layout information
            let base_place_type_id = get_place_type_id(base_place, mir).map_err(|e| e.to_string())?;
            let base_type = mir.get_type(base_place_type_id);

            // If the base is a pointer, we must load the pointer value from the base address
            // before adding the element offset. For arrays, the base address is already
            // the address of the first element.
            let (element_size, final_base_addr) = match base_type {
                MirType::Array { layout, .. } => (layout.stride as u32, base_addr),
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    let size = mir_type_size(pointee_type, mir)?;
                    let loaded_ptr = builder.ins().load(types::I64, MemFlags::new(), base_addr, 0);
                    (size, loaded_ptr)
                }
                _ => return Err("Base of ArrayIndex is not an array or pointer".to_string()),
            };

            let element_size_val = builder.ins().iconst(types::I64, element_size as i64);
            let offset = builder.ins().imul(index_val, element_size_val);

            Ok(builder.ins().iadd(final_base_addr, offset))
        }
    }
}
/// Helper to lower a single MIR statement
fn lower_statement(
    stmt: &MirStmt,
    builder: &mut FunctionBuilder,
    mir: &MirProgram,
    clif_stack_slots: &HashMap<LocalId, StackSlot>,
    module: &mut ObjectModule,
    va_spill_slot: Option<StackSlot>,
    func: &MirFunction,
) -> Result<(), String> {
    match stmt {
        MirStmt::Assign(place, rvalue) => {
            let place_type_id = get_place_type_id(place, mir)?;
            let place_mir_type = mir.get_type(place_type_id);
            let expected_type = match convert_type(place_mir_type) {
                Some(t) => t,
                None if matches!(place_mir_type, MirType::Record { .. } | MirType::Array { .. }) => types::I64,
                None => return Err("Cannot assign to void type".to_string()),
            };

            // Process the rvalue to get a Cranelift value first
            let rvalue_result = match rvalue {
                Rvalue::Use(operand) => {
                    resolve_operand_to_value(operand, builder, expected_type, clif_stack_slots, mir, module)
                }
                Rvalue::Cast(type_id, operand) => {
                    let inner_cranelift_type = get_operand_cranelift_type(operand, mir)?;
                    let inner_val = resolve_operand_to_value(
                        operand,
                        builder,
                        inner_cranelift_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    let target_mir_type = mir.get_type(*type_id);
                    let target_cranelift_type =
                        convert_type(target_mir_type).ok_or_else(|| "Cannot cast to void type".to_string())?;

                    let converted = emit_type_conversion(
                        inner_val,
                        inner_cranelift_type,
                        target_cranelift_type,
                        is_operand_signed(operand, mir),
                        builder,
                    );

                    Ok(emit_type_conversion(
                        converted,
                        target_cranelift_type,
                        expected_type,
                        target_mir_type.is_signed(),
                        builder,
                    ))
                }
                Rvalue::UnaryIntOp(op, operand) => {
                    let operand_cranelift_type = get_operand_cranelift_type(operand, mir)?;
                    let val = resolve_operand_to_value(
                        operand,
                        builder,
                        operand_cranelift_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    match op {
                        UnaryIntOp::Neg => Ok(builder.ins().ineg(val)),
                        UnaryIntOp::LogicalNot => {
                            let is_zero = builder.ins().icmp_imm(IntCC::Equal, val, 0);
                            Ok(emit_bool_to_int(is_zero, expected_type, builder))
                        }
                        UnaryIntOp::BitwiseNot => Ok(builder.ins().bnot(val)),
                    }
                }
                Rvalue::UnaryFloatOp(op, operand) => {
                    let operand_cranelift_type = get_operand_cranelift_type(operand, mir)?;
                    let val = resolve_operand_to_value(
                        operand,
                        builder,
                        operand_cranelift_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    match op {
                        UnaryFloatOp::Neg => Ok(builder.ins().fneg(val)),
                    }
                }
                Rvalue::PtrAdd(base, offset) => {
                    let base_type_id = get_operand_type_id(base, mir)?;
                    let base_type = mir.get_type(base_type_id);
                    let pointee_size = if let MirType::Pointer { pointee } = base_type {
                        let pointee_type = mir.get_type(*pointee);
                        mir_type_size(pointee_type, mir)?
                    } else {
                        return Err("PtrAdd base is not a pointer type".to_string());
                    };

                    let base_val = resolve_operand_to_value(base, builder, types::I64, clif_stack_slots, mir, module)?;
                    let offset_val =
                        resolve_operand_to_value(offset, builder, types::I64, clif_stack_slots, mir, module)?;

                    let scaled_offset = if pointee_size > 1 {
                        let size_val = builder.ins().iconst(types::I64, pointee_size as i64);
                        builder.ins().imul(offset_val, size_val)
                    } else {
                        offset_val
                    };
                    Ok(builder.ins().iadd(base_val, scaled_offset))
                }
                Rvalue::PtrSub(base, offset) => {
                    let base_type_id = get_operand_type_id(base, mir)?;
                    let base_type = mir.get_type(base_type_id);
                    let pointee_size = if let MirType::Pointer { pointee } = base_type {
                        let pointee_type = mir.get_type(*pointee);
                        mir_type_size(pointee_type, mir)?
                    } else {
                        return Err("PtrSub base is not a pointer type".to_string());
                    };

                    let base_val = resolve_operand_to_value(base, builder, types::I64, clif_stack_slots, mir, module)?;
                    let offset_val =
                        resolve_operand_to_value(offset, builder, types::I64, clif_stack_slots, mir, module)?;

                    let scaled_offset = if pointee_size > 1 {
                        let size_val = builder.ins().iconst(types::I64, pointee_size as i64);
                        builder.ins().imul(offset_val, size_val)
                    } else {
                        offset_val
                    };
                    Ok(builder.ins().isub(base_val, scaled_offset))
                }
                Rvalue::PtrDiff(left, right) => {
                    let left_type_id = get_operand_type_id(left, mir)?;
                    let left_type = mir.get_type(left_type_id);
                    let pointee_size = if let MirType::Pointer { pointee } = left_type {
                        let pointee_type = mir.get_type(*pointee);
                        mir_type_size(pointee_type, mir)?
                    } else {
                        return Err("PtrDiff left operand is not a pointer type".to_string());
                    };

                    let left_val = resolve_operand_to_value(left, builder, types::I64, clif_stack_slots, mir, module)?;
                    let right_val =
                        resolve_operand_to_value(right, builder, types::I64, clif_stack_slots, mir, module)?;

                    let diff = builder.ins().isub(left_val, right_val);
                    if pointee_size > 1 {
                        let size_val = builder.ins().iconst(types::I64, pointee_size as i64);
                        Ok(builder.ins().sdiv(diff, size_val))
                    } else {
                        Ok(diff)
                    }
                }
                Rvalue::Load(operand) => {
                    let addr = resolve_operand_to_value(operand, builder, types::I64, clif_stack_slots, mir, module)?;
                    Ok(builder.ins().load(expected_type, MemFlags::new(), addr, 0))
                }
                Rvalue::Call(call_target, args) => {
                    emit_function_call_impl(call_target, args, builder, mir, clif_stack_slots, module, expected_type)
                }
                Rvalue::BinaryIntOp(op, left_operand, right_operand) => {
                    let left_cranelift_type = get_operand_cranelift_type(left_operand, mir)
                        .map_err(|e| format!("Failed to get left operand type: {}", e))?;
                    let right_cranelift_type = get_operand_cranelift_type(right_operand, mir)
                        .map_err(|e| format!("Failed to get right operand type: {}", e))?;

                    // For Add/Sub operations on Pointers, we treat them as I64
                    let (final_left_type, final_right_type) = match op {
                        BinaryIntOp::Add | BinaryIntOp::Sub => {
                            if left_cranelift_type == types::I64 && right_cranelift_type == types::I32 {
                                // Pointer + int constant
                                (types::I64, types::I64)
                            } else if left_cranelift_type == types::I32 && right_cranelift_type == types::I64 {
                                // int constant + pointer
                                (types::I64, types::I64)
                            } else {
                                (left_cranelift_type, right_cranelift_type)
                            }
                        }
                        _ => (left_cranelift_type, right_cranelift_type),
                    };

                    let left_val = resolve_operand_to_value(
                        left_operand,
                        builder,
                        final_left_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    let right_val = resolve_operand_to_value(
                        right_operand,
                        builder,
                        final_right_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    let result_val = match op {
                        BinaryIntOp::Add => builder.ins().iadd(left_val, right_val),
                        BinaryIntOp::Sub => builder.ins().isub(left_val, right_val),
                        BinaryIntOp::Mul => builder.ins().imul(left_val, right_val),
                        BinaryIntOp::Div => {
                            if is_operand_signed(left_operand, mir) {
                                builder.ins().sdiv(left_val, right_val)
                            } else {
                                builder.ins().udiv(left_val, right_val)
                            }
                        }
                        BinaryIntOp::Mod => {
                            if is_operand_signed(left_operand, mir) {
                                builder.ins().srem(left_val, right_val)
                            } else {
                                builder.ins().urem(left_val, right_val)
                            }
                        }
                        BinaryIntOp::BitAnd => builder.ins().band(left_val, right_val),
                        BinaryIntOp::BitOr => builder.ins().bor(left_val, right_val),
                        BinaryIntOp::BitXor => builder.ins().bxor(left_val, right_val),
                        BinaryIntOp::LShift => builder.ins().ishl(left_val, right_val),
                        BinaryIntOp::RShift => {
                            if is_operand_signed(left_operand, mir) {
                                builder.ins().sshr(left_val, right_val)
                            } else {
                                builder.ins().ushr(left_val, right_val)
                            }
                        }
                        BinaryIntOp::Eq => {
                            let cmp_val = builder.ins().icmp(IntCC::Equal, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryIntOp::Ne => {
                            let cmp_val = builder.ins().icmp(IntCC::NotEqual, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryIntOp::Lt => {
                            let cmp_val = builder.ins().icmp(IntCC::SignedLessThan, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryIntOp::Le => {
                            let cmp_val = builder.ins().icmp(IntCC::SignedLessThanOrEqual, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryIntOp::Gt => {
                            let cmp_val = builder.ins().icmp(IntCC::SignedGreaterThan, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryIntOp::Ge => {
                            let cmp_val = builder.ins().icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                    };

                    let from_type = match op {
                        BinaryIntOp::Eq
                        | BinaryIntOp::Ne
                        | BinaryIntOp::Lt
                        | BinaryIntOp::Le
                        | BinaryIntOp::Gt
                        | BinaryIntOp::Ge => types::I32,
                        _ => final_left_type,
                    };

                    Ok(emit_type_conversion(
                        result_val,
                        from_type,
                        expected_type,
                        true,
                        builder,
                    ))
                }
                Rvalue::BinaryFloatOp(op, left_operand, right_operand) => {
                    let left_cranelift_type = get_operand_cranelift_type(left_operand, mir)
                        .map_err(|e| format!("Failed to get left operand type: {}", e))?;
                    let right_cranelift_type = get_operand_cranelift_type(right_operand, mir)
                        .map_err(|e| format!("Failed to get right operand type: {}", e))?;

                    let left_val = resolve_operand_to_value(
                        left_operand,
                        builder,
                        left_cranelift_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    let right_val = resolve_operand_to_value(
                        right_operand,
                        builder,
                        right_cranelift_type,
                        clif_stack_slots,
                        mir,
                        module,
                    )?;

                    let result_val = match op {
                        BinaryFloatOp::Add => builder.ins().fadd(left_val, right_val),
                        BinaryFloatOp::Sub => builder.ins().fsub(left_val, right_val),
                        BinaryFloatOp::Mul => builder.ins().fmul(left_val, right_val),
                        BinaryFloatOp::Div => builder.ins().fdiv(left_val, right_val),
                        BinaryFloatOp::Eq => {
                            let cmp_val = builder.ins().fcmp(FloatCC::Equal, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryFloatOp::Ne => {
                            let cmp_val = builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryFloatOp::Lt => {
                            let cmp_val = builder.ins().fcmp(FloatCC::LessThan, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryFloatOp::Le => {
                            let cmp_val = builder.ins().fcmp(FloatCC::LessThanOrEqual, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryFloatOp::Gt => {
                            let cmp_val = builder.ins().fcmp(FloatCC::GreaterThan, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                        BinaryFloatOp::Ge => {
                            let cmp_val = builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val);
                            emit_bool_to_int(cmp_val, types::I32, builder)
                        }
                    };

                    let from_type = match op {
                        BinaryFloatOp::Eq
                        | BinaryFloatOp::Ne
                        | BinaryFloatOp::Lt
                        | BinaryFloatOp::Le
                        | BinaryFloatOp::Gt
                        | BinaryFloatOp::Ge => types::I32,
                        _ => left_cranelift_type,
                    };

                    Ok(emit_type_conversion(
                        result_val,
                        from_type,
                        expected_type,
                        true,
                        builder,
                    ))
                }
                Rvalue::BuiltinVaArg(ap, type_id) => {
                    // SysV AMD64 ABI va_list structure:
                    // struct { gp_offset, fp_offset, overflow_arg_area, reg_save_area }
                    //
                    // For GP types: if gp_offset < 48, fetch from reg_save_area + gp_offset
                    //               else fetch from overflow_arg_area

                    let ap_addr = resolve_place_to_addr(ap, builder, clif_stack_slots, mir, module)?;

                    // Load fields from va_list
                    let gp_offset = builder.ins().load(types::I32, MemFlags::new(), ap_addr, 0);
                    let overflow_arg_area = builder.ins().load(types::I64, MemFlags::new(), ap_addr, 8);
                    let reg_save_area = builder.ins().load(types::I64, MemFlags::new(), ap_addr, 16);

                    let mir_type = mir.get_type(*type_id);
                    let size = mir_type_size(mir_type, mir)?;
                    let aligned_size = size.div_ceil(8) * 8; // Round up to 8 bytes

                    // Create a stack slot to hold the result address (for merging paths)
                    let result_slot =
                        builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 0));

                    // Check if arg fits in our spill area (gp_offset < 128 for 16 slots)
                    let threshold = builder.ins().iconst(types::I32, 128);
                    let fits_in_regs = builder.ins().icmp(IntCC::UnsignedLessThan, gp_offset, threshold);

                    // Create blocks for the two paths
                    let reg_block = builder.create_block();
                    let overflow_block = builder.create_block();
                    let merge_block = builder.create_block();

                    builder.ins().brif(fits_in_regs, reg_block, &[], overflow_block, &[]);

                    // Reg path: fetch from reg_save_area + gp_offset
                    builder.switch_to_block(reg_block);
                    builder.seal_block(reg_block);
                    let gp_offset_i64 = builder.ins().uextend(types::I64, gp_offset);
                    let arg_addr_reg = builder.ins().iadd(reg_save_area, gp_offset_i64);
                    // Store result address
                    builder.ins().stack_store(arg_addr_reg, result_slot, 0);
                    // Update gp_offset
                    let size_i32 = builder.ins().iconst(types::I32, aligned_size as i64);
                    let new_gp_offset = builder.ins().iadd(gp_offset, size_i32);
                    builder.ins().store(MemFlags::new(), new_gp_offset, ap_addr, 0);
                    builder.ins().jump(merge_block, &[]);

                    // Overflow path: fetch from overflow_arg_area
                    builder.switch_to_block(overflow_block);
                    builder.seal_block(overflow_block);
                    // Store result address
                    builder.ins().stack_store(overflow_arg_area, result_slot, 0);
                    // Update overflow_arg_area
                    let aligned_size_i64 = builder.ins().iconst(types::I64, aligned_size as i64);
                    let new_overflow_area = builder.ins().iadd(overflow_arg_area, aligned_size_i64);
                    builder.ins().store(MemFlags::new(), new_overflow_area, ap_addr, 8);
                    builder.ins().jump(merge_block, &[]);

                    // Merge block: load the arg address from stack and get the value
                    builder.switch_to_block(merge_block);
                    builder.seal_block(merge_block);
                    let arg_addr = builder.ins().stack_load(types::I64, result_slot, 0);

                    // Load the value from the address
                    let value = if let Some(clif_type) = convert_type(mir_type) {
                        // Simple type (scalar)
                        builder.ins().load(clif_type, MemFlags::new(), arg_addr, 0)
                    } else {
                        // Aggregate type (struct/array) - return the address
                        // The caller will memcpy from this address
                        arg_addr
                    };

                    Ok(value)
                }
                _ => Ok(builder.ins().iconst(expected_type, 0)),
            };

            // Now, assign the resolved value to the place
            if let Ok(value) = rvalue_result {
                let place_type_id = get_place_type_id(place, mir).unwrap();
                let mir_type = mir.get_type(place_type_id);

                if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) {
                    // For aggregate types, the value is an address (returned by va_arg or similar)
                    let dest_addr = resolve_place_to_addr(place, builder, clif_stack_slots, mir, module)?;
                    let size = mir_type_size(mir_type, mir)? as i64;
                    emit_memcpy(dest_addr, value, size, builder, module)?;
                } else {
                    match place {
                        Place::Local(local_id) => {
                            // Check if this local has a stack slot (non-void types)
                            if let Some(stack_slot) = clif_stack_slots.get(local_id) {
                                builder.ins().stack_store(value, *stack_slot, 0);
                            } else {
                                // This local doesn't have a stack slot (likely a void type)
                                // Check if it's actually a void type to provide a better warning
                                if let Some(local) = mir.locals.get(local_id)
                                    && let Some(local_type) = mir.types.get(&local.type_id)
                                    && !matches!(local_type, MirType::Void)
                                {
                                    eprintln!("Warning: Stack slot not found for local {}", local_id.get());
                                }
                            }
                        }
                        _ => {
                            // This covers StructField, ArrayIndex, Deref, and Global assignments
                            match resolve_place_to_addr(place, builder, clif_stack_slots, mir, module) {
                                Ok(addr) => {
                                    builder.ins().store(MemFlags::new(), value, addr, 0);
                                }
                                Err(e) => {
                                    eprintln!("Warning: Failed to resolve place address for assignment: {}", e);
                                }
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
            let place_type_id = get_place_type_id(place, mir)?;
            let place_type = mir.get_type(place_type_id);
            let cranelift_type = convert_type(place_type).ok_or_else(|| "Cannot store to a void type".to_string())?;

            let value = resolve_operand_to_value(operand, builder, cranelift_type, clif_stack_slots, mir, module)?;

            // Now, store the value into the place
            match place {
                Place::Local(local_id) => {
                    let stack_slot = clif_stack_slots
                        .get(local_id)
                        .ok_or_else(|| format!("Stack slot not found for local {}", local_id.get()))?;
                    builder.ins().stack_store(value, *stack_slot, 0);
                }
                _ => {
                    // For other places, resolve to an address and store
                    let addr = resolve_place_to_addr(place, builder, clif_stack_slots, mir, module)?;
                    builder.ins().store(MemFlags::new(), value, addr, 0);
                }
            }
        }

        MirStmt::Call(call_target, args) => {
            // Handle function calls that don't return values (side-effect only calls)
            // This is used for void function calls or calls where the result is ignored
            let _ = emit_function_call_impl(call_target, args, builder, mir, clif_stack_slots, module, types::I32)?; // Ignore return value as this is a side-effect only call
        }

        MirStmt::Alloc(place, type_id) => {
            // Get the size of the type to be allocated
            let alloc_type = mir.get_type(*type_id);
            let size = mir_type_size(alloc_type, mir)?;

            // Define the `malloc` function signature (size_t -> void*)
            // In Cranelift, this would be (i64) -> i64 for a 64-bit target
            let mut malloc_sig = Signature::new(builder.func.signature.call_conv);
            malloc_sig.params.push(AbiParam::new(types::I64));
            malloc_sig.returns.push(AbiParam::new(types::I64));

            // Declare `malloc` if not already declared
            let malloc_func = module
                .declare_function("malloc", Linkage::Import, &malloc_sig)
                .map_err(|e| format!("Failed to declare malloc: {:?}", e))?;
            let local_malloc = module.declare_func_in_func(malloc_func, builder.func);

            // Call `malloc` with the calculated size
            let size_val = builder.ins().iconst(types::I64, size as i64);
            let call_inst = builder.ins().call(local_malloc, &[size_val]);
            let alloc_ptr = builder.inst_results(call_inst)[0];

            // Store the returned pointer into the destination place
            match place {
                Place::Local(local_id) => {
                    if let Some(stack_slot) = clif_stack_slots.get(local_id) {
                        builder.ins().stack_store(alloc_ptr, *stack_slot, 0);
                    } else {
                        eprintln!("Warning: Stack slot not found for local {}", local_id.get());
                    }
                }
                _ => {
                    let addr = resolve_place_to_addr(place, builder, clif_stack_slots, mir, module)?;
                    builder.ins().store(MemFlags::new(), alloc_ptr, addr, 0);
                }
            }
        }

        MirStmt::Dealloc(operand) => {
            // Resolve the operand to get the pointer to be freed
            let ptr_val = resolve_operand_to_value(
                operand,
                builder,
                types::I64, // Pointers are i64
                clif_stack_slots,
                mir,
                module,
            )?;

            // Define the `free` function signature (void* -> void)
            let mut free_sig = Signature::new(builder.func.signature.call_conv);
            free_sig.params.push(AbiParam::new(types::I64));

            // Declare `free` if not already declared
            let free_func = module
                .declare_function("free", Linkage::Import, &free_sig)
                .map_err(|e| format!("Failed to declare free: {:?}", e))?;
            let local_free = module.declare_func_in_func(free_func, builder.func);

            // Call `free` with the pointer
            builder.ins().call(local_free, &[ptr_val]);
        }
        MirStmt::BuiltinVaStart(ap, _last) => {
            // SysV AMD64 ABI va_list structure (24 bytes):
            // struct {
            //     unsigned int gp_offset;      // offset 0, 4 bytes
            //     unsigned int fp_offset;      // offset 4, 4 bytes
            //     void *overflow_arg_area;     // offset 8, 8 bytes
            //     void *reg_save_area;         // offset 16, 8 bytes
            // }
            //
            // We use a 16-slot (128-byte) spill area to capture all variadic args.
            // gp_offset starts after fixed params, and we use 128 as the threshold.

            let ap_addr = resolve_place_to_addr(ap, builder, clif_stack_slots, mir, module)?;

            // Calculate gp_offset: fixed_params * 8 (each GP register is 8 bytes)
            let fixed_param_count = func.params.len() as i32;
            let gp_offset = fixed_param_count * 8;
            let gp_offset_val = builder.ins().iconst(types::I32, gp_offset as i64);
            builder.ins().store(MemFlags::new(), gp_offset_val, ap_addr, 0);

            // fp_offset: 128 (16 slots * 8 bytes = 128, indicates end of our spill area)
            // This is the threshold where we'd switch to overflow_arg_area
            let fp_offset_val = builder.ins().iconst(types::I32, 128);
            builder.ins().store(MemFlags::new(), fp_offset_val, ap_addr, 4);

            // overflow_arg_area: pointer past the 16-slot spill area
            // In practice, with 16 slots, we rarely need this
            let overflow_area = if let Some(spill_slot) = va_spill_slot {
                // Point past the 16-slot spill area (128 bytes)
                let base = builder.ins().stack_addr(types::I64, spill_slot, 0);
                let offset = builder.ins().iconst(types::I64, 128);
                builder.ins().iadd(base, offset)
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            builder.ins().store(MemFlags::new(), overflow_area, ap_addr, 8);

            // reg_save_area: pointer to start of register save area (our spill slot)
            let reg_save_area = if let Some(spill_slot) = va_spill_slot {
                builder.ins().stack_addr(types::I64, spill_slot, 0)
            } else {
                builder.ins().iconst(types::I64, 0)
            };
            builder.ins().store(MemFlags::new(), reg_save_area, ap_addr, 16);
        }
        MirStmt::BuiltinVaEnd(_) => {
            // BuiltinVaEnd is a no-op
        }
        MirStmt::BuiltinVaCopy(dst, src) => {
            let dst_addr = resolve_place_to_addr(dst, builder, clif_stack_slots, mir, module)?;
            let src_addr = resolve_place_to_addr(src, builder, clif_stack_slots, mir, module)?;

            // Copy all 24 bytes of the va_list struct
            // gp_offset (4 bytes)
            let gp_offset = builder.ins().load(types::I32, MemFlags::new(), src_addr, 0);
            builder.ins().store(MemFlags::new(), gp_offset, dst_addr, 0);
            // fp_offset (4 bytes)
            let fp_offset = builder.ins().load(types::I32, MemFlags::new(), src_addr, 4);
            builder.ins().store(MemFlags::new(), fp_offset, dst_addr, 4);
            // overflow_arg_area (8 bytes)
            let overflow_area = builder.ins().load(types::I64, MemFlags::new(), src_addr, 8);
            builder.ins().store(MemFlags::new(), overflow_area, dst_addr, 8);
            // reg_save_area (8 bytes)
            let reg_save_area = builder.ins().load(types::I64, MemFlags::new(), src_addr, 16);
            builder.ins().store(MemFlags::new(), reg_save_area, dst_addr, 16);
        }
    }
    Ok(())
}

/// Helper to lower a terminator
fn lower_terminator(
    terminator: &Terminator,
    builder: &mut FunctionBuilder,
    clif_blocks: &HashMap<MirBlockId, Block>,
    worklist: &mut Vec<MirBlockId>,
    return_type_opt: Option<Type>,
    mir: &MirProgram,
    clif_stack_slots: &HashMap<LocalId, StackSlot>,
    module: &mut ObjectModule,
) -> Result<(), String> {
    match terminator {
        Terminator::Goto(target) => {
            let target_cl_block = clif_blocks
                .get(target)
                .ok_or_else(|| format!("Target block {} not found", target.get()))?;
            builder.ins().jump(*target_cl_block, &[]);
            worklist.push(*target);
        }

        Terminator::If(cond, then_bb, else_bb) => {
            let cond_val = resolve_operand_to_value(cond, builder, types::I32, clif_stack_slots, mir, module)?;

            let then_cl_block = clif_blocks
                .get(then_bb)
                .ok_or_else(|| format!("'Then' block {} not found", then_bb.get()))?;
            let else_cl_block = clif_blocks
                .get(else_bb)
                .ok_or_else(|| format!("'Else' block {} not found", else_bb.get()))?;

            builder.ins().brif(cond_val, *then_cl_block, &[], *else_cl_block, &[]);

            worklist.push(*then_bb);
            worklist.push(*else_bb);
        }

        Terminator::Return(opt) => {
            if let Some(operand) = opt {
                if let Some(ret_type) = return_type_opt {
                    let return_value =
                        resolve_operand_to_value(operand, builder, ret_type, clif_stack_slots, mir, module)?;
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
    Ok(())
}

fn setup_signature(
    func: &MirFunction,
    mir: &MirProgram,
    func_ctx: &mut Signature,
) -> Result<(Option<Type>, Vec<Type>), String> {
    // Set up function signature using the actual return type from MIR
    func_ctx.params.clear();

    // Get the return type from MIR and convert to Cranelift type
    let return_mir_type = mir.get_type(func.return_type);
    let return_type_opt = match convert_type(return_mir_type) {
        Some(t) => Some(t),
        None if matches!(return_mir_type, MirType::Record { .. } | MirType::Array { .. }) => Some(types::I64),
        None => None, // Void
    };

    // Add parameters from MIR function signature
    let mut param_types = Vec::new();
    for &param_id in &func.params {
        let param_local = mir.get_local(param_id);
        let mir_type = mir.get_type(param_local.type_id);
        let param_type = match convert_type(mir_type) {
            Some(t) => t,
            None if matches!(mir_type, MirType::Record { .. } | MirType::Array { .. }) => types::I64,
            None => return Err(format!("Unsupported parameter type for local {}", param_id.get())),
        };
        func_ctx.params.push(AbiParam::new(param_type));
        param_types.push(param_type);
    }

    if func.is_variadic {
        // Add 16 total I64 parameters to capture variadic arguments (6 GPRs + 10 stack slots)
        // This allows variadic functions to receive many struct args that expand to multiple I64s
        let fixed_params_count = func.params.len();
        let total_variadic_slots = 16; // Support up to 16 I64 slots for variadic args
        if fixed_params_count < total_variadic_slots {
            for _ in 0..(total_variadic_slots - fixed_params_count) {
                func_ctx.params.push(AbiParam::new(types::I64));
            }
        }
    }

    // Only add return parameter if the function has a non-void return type
    if let Some(return_type) = return_type_opt {
        func_ctx.returns.push(AbiParam::new(return_type));
    }

    Ok((return_type_opt, param_types))
}

fn allocate_stack_slots(
    func: &MirFunction,
    mir: &MirProgram,
    builder: &mut FunctionBuilder,
    clif_stack_slots: &mut HashMap<LocalId, StackSlot>,
) -> Result<(), String> {
    clif_stack_slots.clear(); // Clear for each function

    // Combine locals and params for slot allocation
    let all_locals: Vec<LocalId> = func.locals.iter().chain(func.params.iter()).cloned().collect();

    for &local_id in &all_locals {
        let local = mir.get_local(local_id);
        let local_type = mir.get_type(local.type_id);
        let size = mir_type_size(local_type, mir)?;

        // Don't allocate space for zero-sized types
        if size > 0 {
            let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 0));
            clif_stack_slots.insert(local_id, slot);
        }
    }
    Ok(())
}

fn finalize_function_processing(
    func: &MirFunction,
    module: &mut ObjectModule,
    func_ctx: &mut cranelift::codegen::Context,
    emit_kind: EmitKind,
    compiled_functions: &mut HashMap<String, String>,
) -> Result<(), String> {
    // Now declare and define the function
    let linkage = match func.kind {
        MirFunctionKind::Extern => cranelift_module::Linkage::Import,
        MirFunctionKind::Defined => cranelift_module::Linkage::Export,
    };

    let id = module
        .declare_function(func.name.as_str(), linkage, &func_ctx.func.signature)
        .map_err(|e| format!("Failed to declare function {}: {:?}", func.name, e))?;

    // Only define the function body if it's a defined function (not extern)
    if matches!(func.kind, MirFunctionKind::Defined) {
        module
            .define_function(id, func_ctx)
            .map_err(|e| format!("Failed to define function {}: {:?}", func.name, e))?;
    }

    if emit_kind == EmitKind::Clif {
        // Store the function IR string for dumping
        let func_ir = func_ctx.func.to_string();
        compiled_functions.insert(func.name.to_string(), func_ir);
    }

    Ok(())
}

/// MIR to Cranelift IR Lowerer
pub(crate) struct MirToCraneliftLowerer {
    builder_context: FunctionBuilderContext,
    module: ObjectModule,
    mir: MirProgram, // NOTE: need better nama
    clif_stack_slots: HashMap<LocalId, StackSlot>,
    // Store compiled functions for dumping
    compiled_functions: HashMap<String, String>,

    emit_kind: EmitKind,

    // Mappings for relocations
    func_id_map: HashMap<MirFunctionId, FuncId>,
    data_id_map: HashMap<GlobalId, DataId>,

    // Variadic spill area for the current function
    va_spill_slot: Option<StackSlot>,
}

/// NOTE: we use panic!() to ICE because codegen rely on correct MIR, so if we give invalid MIR, then problem is in previous phase
impl MirToCraneliftLowerer {
    pub(crate) fn new(mir: MirProgram) -> Self {
        let triple = Triple::host();
        let mut flag_builder = cranelift::prelude::settings::builder();
        flag_builder.set("is_pic", "true").unwrap();
        let builder = ObjectBuilder::new(
            cranelift::prelude::isa::lookup(triple)
                .unwrap()
                .finish(cranelift::prelude::settings::Flags::new(flag_builder))
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
            clif_stack_slots: HashMap::new(),
            compiled_functions: HashMap::new(),
            emit_kind: EmitKind::Object,
            func_id_map: HashMap::new(),
            data_id_map: HashMap::new(),
            va_spill_slot: None,
        }
    }

    pub(crate) fn compile_module(mut self, emit_kind: EmitKind) -> Result<ClifOutput, String> {
        self.emit_kind = emit_kind;
        self.populate_state();

        // Pass 1: Declare all global variables
        for (global_id, global) in &self.mir.globals {
            let linkage = if global.initial_value.is_some() {
                Linkage::Export
            } else {
                Linkage::Import
            };

            let data_id = self
                .module
                .declare_data(global.name.as_str(), linkage, true, false)
                .map_err(|e| format!("Failed to declare global data: {:?}", e))?;

            self.data_id_map.insert(*global_id, data_id);
        }

        // Pass 2: Declare all functions
        for (func_id, func) in &self.mir.functions {
            let linkage = match func.kind {
                MirFunctionKind::Extern => Linkage::Import,
                MirFunctionKind::Defined => Linkage::Export,
            };

            // Calculate signature for declaration
            let mut sig = self.module.make_signature();
            setup_signature(func, &self.mir, &mut sig)?;

            let clif_func_id = self
                .module
                .declare_function(func.name.as_str(), linkage, &sig)
                .map_err(|e| format!("Failed to declare function {}: {:?}", func.name, e))?;

            self.func_id_map.insert(*func_id, clif_func_id);
        }

        // Pass 3: Define Global Variables (with relocations)
        for (global_id, global) in &self.mir.globals {
            if let Some(const_id) = global.initial_value {
                let data_id = *self.data_id_map.get(global_id).unwrap();

                let mut data_description = DataDescription::new();
                let global_type = self.mir.get_type(global.type_id);
                let layout = get_type_layout(global_type, &self.mir)
                    .map_err(|e| format!("Failed to get layout for global {}: {}", global.name, e))?;

                let mut initial_value_bytes = Vec::new();
                // Enable relocations by passing data_description and maps
                let ctx = EmitContext {
                    mir: &self.mir,
                    func_id_map: &self.func_id_map,
                    data_id_map: &self.data_id_map,
                };
                emit_const(
                    const_id,
                    &layout,
                    &mut initial_value_bytes,
                    &ctx,
                    Some(&mut self.module),
                    Some(&mut data_description),
                    0,
                )
                .map_err(|e| format!("Failed to emit constant for global {}: {}", global.name, e))?;

                data_description.define(initial_value_bytes.into_boxed_slice());

                self.module
                    .define_data(data_id, &data_description)
                    .map_err(|e| format!("Failed to define global data: {:?}", e))?;
            }
        }

        // Pass 4: Define Functions (Lower bodies)
        // We can't iterate on `&self.mir.module.functions` directly because `lower_function`
        // needs a mutable borrow of `self`. Instead, we iterate by index to avoid cloning the
        // function list, which would cause a heap allocation.
        for i in 0..self.mir.module.functions.len() {
            let func_id = self.mir.module.functions[i];
            // Only lower functions that are defined (have bodies)
            if let Some(func) = self.mir.functions.get(&func_id)
                && matches!(func.kind, MirFunctionKind::Defined)
            {
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

        let (return_type_opt, param_types) = setup_signature(func, &self.mir, &mut func_ctx.func.signature)?;

        // Create a function builder with the fresh context
        let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut self.builder_context);

        allocate_stack_slots(func, &self.mir, &mut builder, &mut self.clif_stack_slots)?;

        // PHASE 1️⃣ — Create all Cranelift blocks first (no instructions)
        let mut clif_blocks = HashMap::new();

        for &block_id in &func.blocks {
            clif_blocks.insert(block_id, builder.create_block());
        }

        // PHASE 2️⃣ — Lower block content (without sealing)
        let mut va_spill_slot = None;

        // Use worklist algorithm for proper traversal
        let mut worklist = vec![func.entry_block.expect("Defined function must have entry block")];
        let mut visited = HashSet::new();

        while let Some(current_block_id) = worklist.pop() {
            if visited.contains(&current_block_id) {
                continue;
            }
            visited.insert(current_block_id);

            let clif_block = clif_blocks
                .get(&current_block_id)
                .ok_or_else(|| format!("Block {} not found in mapping", current_block_id.get()))?;
            builder.switch_to_block(*clif_block);

            // Setup entry block parameters
            if Some(current_block_id) == func.entry_block {
                // Step 1: Add ALL block parameters first (fixed params)
                for &param_type in &param_types {
                    builder.append_block_param(*clif_block, param_type);
                }

                // Step 2: Add variadic block parameters if needed (still before any instructions)
                if func.is_variadic {
                    let fixed_param_count = func.params.len();
                    let total_variadic_slots = 16; // Must match setup_signature
                    if fixed_param_count < total_variadic_slots {
                        let extra_count = total_variadic_slots - fixed_param_count;
                        for _ in 0..extra_count {
                            builder.append_block_param(*clif_block, types::I64);
                        }
                    }
                }

                // Step 3: NOW emit instructions - store fixed params to stack slots
                let param_values: Vec<Value> = builder.block_params(*clif_block).to_vec();

                for (next_param_idx, &param_id) in func.params.iter().enumerate() {
                    let param_value = param_values[next_param_idx];
                    if let Some(stack_slot) = self.clif_stack_slots.get(&param_id) {
                        builder.ins().stack_store(param_value, *stack_slot, 0);
                    }
                }

                // Step 4: Handle variadic spill area - save all 16 slots
                if func.is_variadic {
                    let total_slots = 16;
                    let spill_size = total_slots * 8; // 128 bytes for 16 I64 slots
                    let spill_slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        spill_size as u32,
                        0,
                    ));
                    let all_param_values = builder.block_params(*clif_block).to_vec();
                    for (i, val) in all_param_values
                        .iter()
                        .enumerate()
                        .take(total_slots.min(all_param_values.len()))
                    {
                        builder.ins().stack_store(*val, spill_slot, (i * 8) as i32);
                    }
                    va_spill_slot = Some(spill_slot);
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
                lower_statement(
                    stmt,
                    &mut builder,
                    &self.mir,
                    &self.clif_stack_slots,
                    &mut self.module,
                    va_spill_slot,
                    func,
                )?;
            }

            // ========================================================================
            // SECTION 2: Process terminator (control flow)
            // ========================================================================
            lower_terminator(
                &mir_block.terminator,
                &mut builder,
                &clif_blocks,
                &mut worklist,
                return_type_opt,
                &self.mir,
                &self.clif_stack_slots,
                &mut self.module,
            )?;
        }

        // PHASE 3️⃣ — Seal blocks with correct order
        for &mir_block_id in &func.blocks {
            let cl_block = clif_blocks.get(&mir_block_id).expect("Block not found in mapping");
            builder.seal_block(*cl_block);
        }

        // Finalize the function
        builder.finalize();
        self.va_spill_slot = va_spill_slot;

        finalize_function_processing(
            func,
            &mut self.module,
            &mut func_ctx,
            self.emit_kind,
            &mut self.compiled_functions,
        )?;

        Ok(())
    }
}
