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
    MirFunctionKind, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId, UnaryOp,
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
fn convert_type(mir_type: &MirType) -> Option<Type> {
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
        MirType::Pointer { .. } => Some(types::I64), // Pointers are 64-bit on most modern systems
        MirType::Bool => Some(types::I32),           // Booleans as 32-bit integers
        MirType::Array { .. } => Some(types::I32),   // Arrays - need element type context
        MirType::Record { .. } => Some(types::I32),  // Records - need field context
        MirType::Function { .. } => Some(types::I64), // Function pointers
        MirType::Enum { .. } => Some(types::I32),    // Enums as integers
    }
}

/// Helper function to get the size of a MIR type in bytes
pub(crate) fn mir_type_size(mir_type: &MirType, _mir: &SemaOutput) -> Result<u32, String> {
    match mir_type {
        MirType::Int { width, .. } => Ok((*width / 8) as u32),
        MirType::Float { width } => Ok((*width / 8) as u32),
        MirType::Pointer { .. } => Ok(8), // Assuming 64-bit pointers for now
        MirType::Array { layout, .. } => Ok(layout.size as u32),
        MirType::Record { layout, .. } => Ok(layout.size as u32),
        MirType::Bool => Ok(1),
        MirType::Void => Ok(0),
        // For other complex types, let's have a default, though this should be comprehensive.
        _ => Ok(4), // Default size for other types
    }
}

/// Helper function to get type layout information for emit_const
pub(crate) fn get_type_layout(mir_type: &MirType, _mir: &SemaOutput) -> Result<MirType, String> {
    Ok(mir_type.clone())
}

/// Emit a constant value to the output buffer based on its type layout
pub(crate) fn emit_const(
    const_id: ConstValueId,
    _type_id: TypeId,
    layout: &MirType,
    output: &mut Vec<u8>,
    mir: &SemaOutput,
) -> Result<(), String> {
    let const_value = mir
        .constants
        .get(&const_id)
        .ok_or_else(|| format!("Constant ID {} not found", const_id.get()))?;

    match const_value {
        ConstValue::Int(val) => {
            match layout {
                MirType::Int { width, is_signed: _ } => match width {
                    8 | 16 | 32 | 64 => {
                        let bytes = val.to_le_bytes();
                        let size = (width / 8) as usize;
                        output.extend_from_slice(&bytes[0..size]);
                    }
                    _ => {
                        let bytes = (*val as i32).to_le_bytes();
                        output.extend_from_slice(&bytes);
                    }
                },
                MirType::Bool => {
                    let byte = if *val != 0 { 1u8 } else { 0u8 };
                    output.push(byte);
                }
                MirType::Pointer { .. } => {
                    // For pointers, treat as 64-bit integer
                    let bytes = (*val).to_le_bytes();
                    output.extend_from_slice(&bytes);
                }
                _ => {
                    // Default to 32-bit integer representation
                    let bytes = (*val as i32).to_le_bytes();
                    output.extend_from_slice(&bytes);
                }
            }
        }
        ConstValue::Float(val) => {
            match layout {
                MirType::Float { width } => match width {
                    32 => {
                        let bytes = (*val as f32).to_bits().to_le_bytes();
                        output.extend_from_slice(&bytes);
                    }
                    64 => {
                        let bytes = val.to_bits().to_le_bytes();
                        output.extend_from_slice(&bytes);
                    }
                    _ => {
                        let bytes = (*val as f32).to_bits().to_le_bytes();
                        output.extend_from_slice(&bytes);
                    }
                },
                _ => {
                    // Default to 64-bit float representation
                    let bytes = val.to_bits().to_le_bytes();
                    output.extend_from_slice(&bytes);
                }
            }
        }
        ConstValue::Bool(val) => {
            let byte = if *val { 1u8 } else { 0u8 };
            output.push(byte);
        }
        ConstValue::Null => {
            // Emit null as all zeros (pointer-sized)
            let null_bytes = 0i64.to_le_bytes();
            output.extend_from_slice(&null_bytes);
        }
        ConstValue::Zero => {
            // Emit zeros for the entire type size
            let size = mir_type_size(layout, mir)? as usize;
            output.extend_from_slice(&vec![0u8; size]);
        }
        ConstValue::GlobalAddress(global_id) => {
            // For global addresses, emit as pointer-sized integer
            let addr_bytes = (global_id.get() as i64).to_le_bytes();
            output.extend_from_slice(&addr_bytes);
        }
        ConstValue::FunctionAddress(func_id) => {
            // For function addresses, emit as pointer-sized integer
            let addr_bytes = (func_id.get() as i64).to_le_bytes();
            output.extend_from_slice(&addr_bytes);
        }
        ConstValue::StructLiteral(fields) => {
            match layout {
                MirType::Record {
                    layout: record_layout,
                    fields: type_fields,
                    ..
                } => {
                    // Initialize the entire struct with zeros
                    let struct_size = record_layout.size as usize;
                    let mut struct_bytes = vec![0u8; struct_size];

                    // Emit each field at its proper offset
                    for (field_index, field_const_id) in fields {
                        if *field_index < record_layout.field_offsets.len() {
                            let field_offset = record_layout.field_offsets[*field_index] as usize;

                            let (_field_name, field_type_id) = type_fields
                                .get(*field_index)
                                .ok_or_else(|| format!("Field index {} out of bounds", field_index))?;

                            let field_type = mir.get_type(*field_type_id);

                            let mut field_bytes = Vec::new();
                            emit_const(*field_const_id, *field_type_id, field_type, &mut field_bytes, mir)?;

                            // Copy the field bytes into the struct buffer
                            // Make sure we don't overflow the struct buffer
                            if field_offset + field_bytes.len() <= struct_size {
                                struct_bytes[field_offset..field_offset + field_bytes.len()]
                                    .copy_from_slice(&field_bytes);
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
                }
                _ => return Err("StructLiteral with non-record type".to_string()),
            }
        }
        ConstValue::ArrayLiteral(elements) => {
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

                        let element_type = mir.get_type(*element);
                        emit_const(*element_const_id, *element, element_type, output, mir)?;

                        // Add padding if needed for stride > element size
                        let element_size = mir_type_size(element_type, mir)? as usize;
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
                }
                _ => return Err("ArrayLiteral with non-array type".to_string()),
            }
        }
        ConstValue::Cast(_type_id, inner_id) => {
            // For now, just emit the inner constant. The layout already determines the size/format.
            emit_const(*inner_id, *_type_id, layout, output, mir)?;
        }
    }

    Ok(())
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
            let return_type = convert_type(mir.get_type(func.return_type));

            // Create a function signature by building it directly
            let mut sig = Signature::new(builder.func.signature.call_conv);

            // Only add return parameter if the function has a non-void return type
            if let Some(ret_type) = return_type {
                sig.returns.push(AbiParam::new(ret_type));
            }

            // For variadic functions, we need to create a signature that matches the actual arguments
            // being passed, not just the fixed parameters
            if func.is_variadic {
                // For variadic functions, use the actual types of the arguments
                // Fixed parameters should have their declared types, variadic args should have their actual types
                for (i, arg) in args.iter().enumerate() {
                    if i < func.params.len() {
                        // This is a fixed parameter, use its declared type
                        let param_id = func.params[i];
                        let param_local = mir.get_local(param_id);
                        let param_type = convert_type(mir.get_type(param_local.type_id)).unwrap();
                        sig.params.push(AbiParam::new(param_type));
                    } else {
                        // This is a variadic argument, determine its type from the operand
                        let arg_type = get_operand_cranelift_type(arg, mir).unwrap_or(types::I32);
                        sig.params.push(AbiParam::new(arg_type));
                    }
                }
            } else {
                // For non-variadic functions, use the fixed parameter types from the function signature
                for &param_id in &func.params {
                    let param_local = mir.get_local(param_id);
                    let param_type = convert_type(mir.get_type(param_local.type_id)).unwrap();
                    sig.params.push(AbiParam::new(param_type));
                }
            }

            // Resolve function arguments to Cranelift values based on the signature we just built
            let mut arg_values = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let param_type = sig.params[i].value_type;
                match resolve_operand_to_value(arg, builder, param_type, cranelift_stack_slots, mir, module) {
                    Ok(value) => arg_values.push(value),
                    Err(e) => return Err(format!("Failed to resolve function argument: {}", e)),
                }
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
        CallTarget::Indirect(func_operand) => {
            // 1. Get the type of the function pointer
            let func_ptr_type_id = get_operand_type_id(func_operand, mir)
                .map_err(|e| format!("Failed to get function pointer type: {}", e))?;

            let func_ptr_type = mir.get_type(func_ptr_type_id);

            // 2. It must be a pointer to a function
            let (return_type_id, param_type_ids) = match func_ptr_type {
                MirType::Pointer { pointee } => match mir.get_type(*pointee) {
                    MirType::Function { return_type, params } => (*return_type, params),
                    _ => {
                        return Err(format!(
                            "Indirect call operand points to non-function type: {:?}",
                            mir.get_type(*pointee)
                        ));
                    }
                },
                _ => return Err(format!("Indirect call operand is not a pointer: {:?}", func_ptr_type)),
            };

            // 3. Construct the signature
            let mut sig = Signature::new(builder.func.signature.call_conv);

            // Return type
            let return_type_opt = convert_type(mir.get_type(return_type_id));
            if let Some(ret_type) = return_type_opt {
                sig.returns.push(AbiParam::new(ret_type));
            }

            // Params
            // First add fixed parameters from the function type
            for &param_type_id in param_type_ids {
                let param_type = convert_type(mir.get_type(param_type_id)).unwrap();
                sig.params.push(AbiParam::new(param_type));
            }

            // If there are more arguments than parameters, it's a variadic call.
            // Add the extra arguments to the signature.
            for arg in args.iter().skip(param_type_ids.len()) {
                let arg_type = get_operand_cranelift_type(arg, mir).unwrap_or(types::I32);
                sig.params.push(AbiParam::new(arg_type));
            }

            // 4. Resolve the function pointer operand to a value
            let callee_val = resolve_operand_to_value(
                func_operand,
                builder,
                types::I64, // Function pointers are I64
                cranelift_stack_slots,
                mir,
                module,
            )?;

            // 5. Resolve arguments
            let mut arg_values = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                // Ensure we have a parameter type for this argument
                // This handles both fixed and variadic arguments because we extended sig.params above
                if i >= sig.params.len() {
                    return Err(format!(
                        "Argument count mismatch: expected at most {}, got {}",
                        sig.params.len(),
                        args.len()
                    ));
                }

                let param_type = sig.params[i].value_type;
                match resolve_operand_to_value(arg, builder, param_type, cranelift_stack_slots, mir, module) {
                    Ok(value) => arg_values.push(value),
                    Err(e) => return Err(format!("Failed to resolve indirect call argument: {}", e)),
                }
            }

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

/// Helper function to emit a type conversion in Cranelift
fn emit_type_conversion(val: Value, from: Type, to: Type, is_signed: bool, builder: &mut FunctionBuilder) -> Value {
    if from == to {
        return val;
    }

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
        // Same width, diff types (e.g. i32 and f32) - not fully handled yet
        // Bitcast for now if they have same size
        val
    }
}

/// Helper function to resolve a MIR operand to a Cranelift value
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

/// Helper function to get the Cranelift Type of an operand
fn get_operand_cranelift_type(operand: &Operand, mir: &SemaOutput) -> Result<Type, String> {
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
                    Ok(convert_type(mir_type).unwrap_or(types::I32))
                }
            }
        }
        Operand::Copy(place) => {
            let place_type_id = get_place_type_id(place, mir)?;
            let place_type = mir.get_type(place_type_id);
            convert_type(place_type).ok_or_else(|| format!("Unsupported place type: {:?}", place_type))
        }
        Operand::Cast(type_id, _) => {
            let mir_type = mir.get_type(*type_id);
            Ok(convert_type(mir_type).unwrap_or(types::I32))
        }
        Operand::AddressOf(_) => Ok(types::I64), // AddressOf always returns a pointer
    }
}

/// Helper function to check if a MIR type is signed
fn is_operand_signed(operand: &Operand, mir: &SemaOutput) -> bool {
    match operand {
        Operand::Copy(place) => {
            if let Ok(type_id) = get_place_type_id(place, mir)
                && let MirType::Int { is_signed, .. } = mir.get_type(type_id)
            {
                return *is_signed;
            }
        }
        Operand::Cast(type_id, _) => {
            if let MirType::Int { is_signed, .. } = mir.get_type(*type_id) {
                return *is_signed;
            }
        }
        Operand::Constant(const_id) => {
            if let Some(ConstValue::Cast(type_id, _)) = mir.constants.get(const_id)
                && let MirType::Int { is_signed, .. } = mir.get_type(*type_id)
            {
                return *is_signed;
            }
            // Default to signed for integer constants
            return true;
        }
        _ => {}
    }
    false
}

/// Helper function to get the TypeId of an operand
fn get_operand_type_id(operand: &Operand, mir: &SemaOutput) -> Result<TypeId, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = mir.constants.get(const_id).expect("constant id not found");
            match const_value {
                ConstValue::Cast(type_id, _) => Ok(*type_id),
                _ => {
                    // This is tricky because raw constants in MIR don't always have an explicit TypeId
                    // associated with them in the Operand enum if they aren't cast.
                    // However, PtrAdd base should usually be a Copy(Place) or a Cast.
                    // For now, let's try to infer or panic if we can't.
                    Err("Cannot determine type of raw constant operand".to_string())
                }
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
fn get_place_type_id(place: &Place, mir: &SemaOutput) -> Result<TypeId, String> {
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
                MirType::Record { fields, .. } => fields
                    .get(*field_index)
                    .map(|(_, type_id)| *type_id)
                    .ok_or_else(|| "Field index out of bounds".to_string()),
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    if let MirType::Record { fields, .. } = pointee_type {
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
/// MIR to Cranelift IR Lowerer
pub(crate) struct MirToCraneliftLowerer {
    builder_context: FunctionBuilderContext,
    module: ObjectModule,
    mir: SemaOutput, // NOTE: need better nama
    clif_stack_slots: HashMap<LocalId, StackSlot>,
    // Store compiled functions for dumping
    compiled_functions: HashMap<String, String>,

    emit_kind: EmitKind,
}

/// NOTE: we use panic!() to ICE because codegen rely on correct MIR, so if we give invalid MIR, then problem is in previous phase
impl MirToCraneliftLowerer {
    pub(crate) fn new(mir: SemaOutput) -> Self {
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
            clif_stack_slots: HashMap::new(),
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
                let global_type = self.mir.get_type(global.type_id);
                let layout = get_type_layout(global_type, &self.mir)
                    .map_err(|e| format!("Failed to get layout for global {}: {}", global.name, e))?;

                let mut initial_value_bytes = Vec::new();
                emit_const(const_id, global.type_id, &layout, &mut initial_value_bytes, &self.mir)
                    .map_err(|e| format!("Failed to emit constant for global {}: {}", global.name, e))?;
                data_description.define(initial_value_bytes.into_boxed_slice());
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

        // Set up function signature using the actual return type from MIR
        func_ctx.func.signature.params.clear();

        // Get the return type from MIR and convert to Cranelift type
        let return_type = self.mir.get_type(func.return_type);
        let return_type_opt = convert_type(return_type);

        // Add parameters from MIR function signature
        let mut param_types = Vec::new();
        for &param_id in &func.params {
            let param_local = self.mir.get_local(param_id);
            let param_type = convert_type(self.mir.get_type(param_local.type_id)).unwrap();
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

        self.clif_stack_slots.clear(); // Clear for each function

        // Combine locals and params for slot allocation
        let all_locals: Vec<LocalId> = func.locals.iter().chain(func.params.iter()).cloned().collect();

        for &local_id in &all_locals {
            let local = self.mir.get_local(local_id);
            let local_type = self.mir.get_type(local.type_id);
            let size = mir_type_size(local_type, &self.mir)?;

            // Don't allocate space for zero-sized types
            if size > 0 {
                let slot = builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 0));
                self.clif_stack_slots.insert(local_id, slot);
            }
        }
        // PHASE 1️⃣ — Create all Cranelift blocks first (no instructions)
        let mut clif_blocks = HashMap::new();

        for &block_id in &func.blocks {
            clif_blocks.insert(block_id, builder.create_block());
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

            let clif_block = clif_blocks
                .get(&current_block_id)
                .ok_or_else(|| format!("Block {} not found in mapping", current_block_id.get()))?;
            builder.switch_to_block(*clif_block);

            // If this is the entry block, set up its parameters
            if Some(current_block_id) == func.entry_block {
                // Add function parameters as block parameters
                for &param_type in &param_types {
                    builder.append_block_param(*clif_block, param_type);
                }

                // Store incoming parameter values into their stack slots
                let param_values: Vec<Value> = builder.block_params(*clif_block).to_vec();
                for (&param_id, param_value) in func.params.iter().zip(param_values.into_iter()) {
                    if let Some(stack_slot) = self.clif_stack_slots.get(&param_id) {
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
                        let place_type_id = get_place_type_id(place, &self.mir)?;
                        let place_mir_type = self.mir.get_type(place_type_id);
                        let expected_type =
                            convert_type(place_mir_type).ok_or_else(|| "Cannot assign to void type".to_string())?;

                        // Process the rvalue to get a Cranelift value first
                        let rvalue_result = match rvalue {
                            Rvalue::Use(operand) => resolve_operand_to_value(
                                operand,
                                &mut builder,
                                expected_type,
                                &self.clif_stack_slots,
                                &self.mir,
                                &mut self.module,
                            ),
                            Rvalue::Cast(type_id, operand) => {
                                let inner_cranelift_type = get_operand_cranelift_type(operand, &self.mir)?;
                                let inner_val = resolve_operand_to_value(
                                    operand,
                                    &mut builder,
                                    inner_cranelift_type,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let target_mir_type = self.mir.get_type(*type_id);
                                let target_cranelift_type = convert_type(target_mir_type)
                                    .ok_or_else(|| "Cannot cast to void type".to_string())?;

                                let converted = emit_type_conversion(
                                    inner_val,
                                    inner_cranelift_type,
                                    target_cranelift_type,
                                    is_operand_signed(operand, &self.mir),
                                    &mut builder,
                                );

                                Ok(emit_type_conversion(
                                    converted,
                                    target_cranelift_type,
                                    expected_type,
                                    target_mir_type.is_signed(),
                                    &mut builder,
                                ))
                            }
                            Rvalue::UnaryOp(op, operand) => {
                                let operand_cranelift_type = get_operand_cranelift_type(operand, &self.mir)?;
                                let val = resolve_operand_to_value(
                                    operand,
                                    &mut builder,
                                    operand_cranelift_type,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                match op {
                                    UnaryOp::Neg => Ok(builder.ins().ineg(val)),
                                    UnaryOp::LogicalNot => {
                                        let is_zero = builder.ins().icmp_imm(IntCC::Equal, val, 0);
                                        Ok(builder.ins().uextend(expected_type, is_zero))
                                    }
                                    UnaryOp::BitwiseNot => Ok(builder.ins().bnot(val)),
                                    _ => Err(format!("Unsupported unary op in Assign: {:?}", op)),
                                }
                            }
                            Rvalue::PtrAdd(base, offset) => {
                                let base_type_id = get_operand_type_id(base, &self.mir)?;
                                let base_type = self.mir.get_type(base_type_id);
                                let pointee_size = if let MirType::Pointer { pointee } = base_type {
                                    let pointee_type = self.mir.get_type(*pointee);
                                    mir_type_size(pointee_type, &self.mir)?
                                } else {
                                    return Err("PtrAdd base is not a pointer type".to_string());
                                };

                                let base_val = resolve_operand_to_value(
                                    base,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                let offset_val = resolve_operand_to_value(
                                    offset,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let scaled_offset = if pointee_size > 1 {
                                    let size_val = builder.ins().iconst(types::I64, pointee_size as i64);
                                    builder.ins().imul(offset_val, size_val)
                                } else {
                                    offset_val
                                };
                                Ok(builder.ins().iadd(base_val, scaled_offset))
                            }
                            Rvalue::PtrSub(base, offset) => {
                                let base_type_id = get_operand_type_id(base, &self.mir)?;
                                let base_type = self.mir.get_type(base_type_id);
                                let pointee_size = if let MirType::Pointer { pointee } = base_type {
                                    let pointee_type = self.mir.get_type(*pointee);
                                    mir_type_size(pointee_type, &self.mir)?
                                } else {
                                    return Err("PtrSub base is not a pointer type".to_string());
                                };

                                let base_val = resolve_operand_to_value(
                                    base,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                let offset_val = resolve_operand_to_value(
                                    offset,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let scaled_offset = if pointee_size > 1 {
                                    let size_val = builder.ins().iconst(types::I64, pointee_size as i64);
                                    builder.ins().imul(offset_val, size_val)
                                } else {
                                    offset_val
                                };
                                Ok(builder.ins().isub(base_val, scaled_offset))
                            }
                            Rvalue::PtrDiff(left, right) => {
                                let left_type_id = get_operand_type_id(left, &self.mir)?;
                                let left_type = self.mir.get_type(left_type_id);
                                let pointee_size = if let MirType::Pointer { pointee } = left_type {
                                    let pointee_type = self.mir.get_type(*pointee);
                                    mir_type_size(pointee_type, &self.mir)?
                                } else {
                                    return Err("PtrDiff left operand is not a pointer type".to_string());
                                };

                                let left_val = resolve_operand_to_value(
                                    left,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                let right_val = resolve_operand_to_value(
                                    right,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let diff = builder.ins().isub(left_val, right_val);
                                if pointee_size > 1 {
                                    let size_val = builder.ins().iconst(types::I64, pointee_size as i64);
                                    Ok(builder.ins().sdiv(diff, size_val))
                                } else {
                                    Ok(diff)
                                }
                            }
                            Rvalue::Load(operand) => {
                                let addr = resolve_operand_to_value(
                                    operand,
                                    &mut builder,
                                    types::I64,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                Ok(builder.ins().load(expected_type, MemFlags::new(), addr, 0))
                            }
                            Rvalue::Call(call_target, args) => emit_function_call_impl(
                                call_target,
                                args,
                                &mut builder,
                                &self.mir,
                                &self.clif_stack_slots,
                                &mut self.module,
                            ),
                            Rvalue::BinaryOp(op, left_operand, right_operand) => {
                                // For binary operations, we need to determine the correct types
                                // based on the operands themselves, not hardcode I32
                                let left_cranelift_type = get_operand_cranelift_type(left_operand, &self.mir)
                                    .map_err(|e| format!("Failed to get left operand type: {}", e))?;
                                let right_cranelift_type = get_operand_cranelift_type(right_operand, &self.mir)
                                    .map_err(|e| format!("Failed to get right operand type: {}", e))?;

                                // For Add/Sub operations, check if we have pointer arithmetic
                                // If one operand is a pointer and the other is an integer constant,
                                // ensure the constant is pointer-sized (i64)
                                let (final_left_type, final_right_type) = match op {
                                    BinaryOp::Add | BinaryOp::Sub => {
                                        if left_cranelift_type == types::I64 && right_cranelift_type == types::I32 {
                                            // Pointer + int constant
                                            (types::I64, types::I64)
                                        } else if left_cranelift_type == types::I32
                                            && right_cranelift_type == types::I64
                                        {
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
                                    &mut builder,
                                    final_left_type,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;

                                let right_val = resolve_operand_to_value(
                                    right_operand,
                                    &mut builder,
                                    final_right_type,
                                    &self.clif_stack_slots,
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
                                let from_type = match op {
                                    BinaryOp::Equal
                                    | BinaryOp::NotEqual
                                    | BinaryOp::Less
                                    | BinaryOp::LessEqual
                                    | BinaryOp::Greater
                                    | BinaryOp::GreaterEqual => types::I32,
                                    _ => final_left_type,
                                };

                                Ok(emit_type_conversion(
                                    result_val,
                                    from_type,
                                    expected_type,
                                    true,
                                    &mut builder,
                                ))
                            }
                            _ => Ok(builder.ins().iconst(expected_type, 0)),
                        };

                        // Now, assign the resolved value to the place
                        if let Ok(value) = rvalue_result {
                            match place {
                                Place::Local(local_id) => {
                                    // Check if this local has a stack slot (non-void types)
                                    if let Some(stack_slot) = self.clif_stack_slots.get(local_id) {
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
                                        &self.clif_stack_slots,
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
                        let cranelift_type =
                            convert_type(place_type).ok_or_else(|| "Cannot store to a void type".to_string())?;

                        let value = resolve_operand_to_value(
                            operand,
                            &mut builder,
                            cranelift_type,
                            &self.clif_stack_slots,
                            &self.mir,
                            &mut self.module,
                        )?;

                        // Now, store the value into the place
                        match place {
                            Place::Local(local_id) => {
                                let stack_slot = self
                                    .clif_stack_slots
                                    .get(local_id)
                                    .ok_or_else(|| format!("Stack slot not found for local {}", local_id.get()))?;
                                builder.ins().stack_store(value, *stack_slot, 0);
                            }
                            _ => {
                                // For other places, resolve to an address and store
                                let addr = resolve_place_to_addr(
                                    place,
                                    &mut builder,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                builder.ins().store(MemFlags::new(), value, addr, 0);
                            }
                        }
                    }

                    MirStmt::Call(call_target, args) => {
                        // Handle function calls that don't return values (side-effect only calls)
                        // This is used for void function calls or calls where the result is ignored
                        let _ = emit_function_call_impl(
                            call_target,
                            args,
                            &mut builder,
                            &self.mir,
                            &self.clif_stack_slots,
                            &mut self.module,
                        )?; // Ignore return value as this is a side-effect only call
                    }

                    MirStmt::Alloc(place, type_id) => {
                        // Get the size of the type to be allocated
                        let alloc_type = self.mir.get_type(*type_id);
                        let size = mir_type_size(alloc_type, &self.mir)?;

                        // Define the `malloc` function signature (size_t -> void*)
                        // In Cranelift, this would be (i64) -> i64 for a 64-bit target
                        let mut malloc_sig = Signature::new(builder.func.signature.call_conv);
                        malloc_sig.params.push(AbiParam::new(types::I64));
                        malloc_sig.returns.push(AbiParam::new(types::I64));

                        // Declare `malloc` if not already declared
                        let malloc_func = self
                            .module
                            .declare_function("malloc", Linkage::Import, &malloc_sig)
                            .map_err(|e| format!("Failed to declare malloc: {:?}", e))?;
                        let local_malloc = self.module.declare_func_in_func(malloc_func, builder.func);

                        // Call `malloc` with the calculated size
                        let size_val = builder.ins().iconst(types::I64, size as i64);
                        let call_inst = builder.ins().call(local_malloc, &[size_val]);
                        let alloc_ptr = builder.inst_results(call_inst)[0];

                        // Store the returned pointer into the destination place
                        match place {
                            Place::Local(local_id) => {
                                if let Some(stack_slot) = self.clif_stack_slots.get(local_id) {
                                    builder.ins().stack_store(alloc_ptr, *stack_slot, 0);
                                } else {
                                    eprintln!("Warning: Stack slot not found for local {}", local_id.get());
                                }
                            }
                            _ => {
                                let addr = resolve_place_to_addr(
                                    place,
                                    &mut builder,
                                    &self.clif_stack_slots,
                                    &self.mir,
                                    &mut self.module,
                                )?;
                                builder.ins().store(MemFlags::new(), alloc_ptr, addr, 0);
                            }
                        }
                    }

                    MirStmt::Dealloc(operand) => {
                        // Resolve the operand to get the pointer to be freed
                        let ptr_val = resolve_operand_to_value(
                            operand,
                            &mut builder,
                            types::I64, // Pointers are i64
                            &self.clif_stack_slots,
                            &self.mir,
                            &mut self.module,
                        )?;

                        // Define the `free` function signature (void* -> void)
                        let mut free_sig = Signature::new(builder.func.signature.call_conv);
                        free_sig.params.push(AbiParam::new(types::I64));

                        // Declare `free` if not already declared
                        let free_func = self
                            .module
                            .declare_function("free", Linkage::Import, &free_sig)
                            .map_err(|e| format!("Failed to declare free: {:?}", e))?;
                        let local_free = self.module.declare_func_in_func(free_func, builder.func);

                        // Call `free` with the pointer
                        builder.ins().call(local_free, &[ptr_val]);
                    }
                }
            }

            // ========================================================================
            // SECTION 2: Process terminator (control flow)
            // ========================================================================
            match &mir_block.terminator {
                Terminator::Goto(target) => {
                    let target_cl_block = clif_blocks
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
                        &self.clif_stack_slots,
                        &self.mir,
                        &mut self.module,
                    )?;

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
                            let return_value = resolve_operand_to_value(
                                operand,
                                &mut builder,
                                ret_type,
                                &self.clif_stack_slots,
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
            let cl_block = clif_blocks.get(&mir_block_id).expect("Block not found in mapping");
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
