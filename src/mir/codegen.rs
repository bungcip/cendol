//! MIR to Cranelift IR lowering module
//!
//! This module provides the mechanical translation from MIR to Cranelift IR.
//! The translation follows these rules:
//! - No C logic
//! - Assume MIR is valid

use crate::mir::MirProgram;
use crate::mir::{
    BinaryFloatOp, BinaryIntOp, CallTarget, ConstValueId, ConstValueKind, GlobalId, LocalId, MirBlockId, MirFunction,
    MirFunctionId, MirFunctionKind, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId, UnaryFloatOp,
    UnaryIntOp,
};
use cranelift::codegen::ir::{AtomicRmwOp, Inst, StackSlot, StackSlotData, StackSlotKind};
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
        MirType::F80 | MirType::F128 => Some(types::F128),
        MirType::Pointer { .. } => Some(types::I64), // Pointers are 64-bit on most modern systems

        MirType::Array { .. } | MirType::Record { .. } => None,
        MirType::Function { .. } => Some(types::I64), // Function pointers
    }
}

/// Helper function to convert MIR function kind to Cranelift linkage
fn convert_linkage(kind: MirFunctionKind) -> Linkage {
    match kind {
        MirFunctionKind::Extern => Linkage::Import,
        MirFunctionKind::Defined => Linkage::Export,
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
        MirType::F80 | MirType::F128 => Ok(16),

        MirType::Pointer { .. } => Ok(mir.pointer_width as u32),
        MirType::Array { layout, .. } => Ok(layout.size as u32),
        MirType::Record { layout, .. } => Ok(layout.size as u32),
        MirType::Bool => Ok(1),
        MirType::Void => Ok(0),
        // For other complex types, let's have a default, though this should be comprehensive.
        _ => Ok(4), // Default size for other types
    }
}

/// Context for constant emission
pub(crate) struct EmitContext<'a> {
    pub mir: &'a MirProgram,
    pub func_id_map: &'a HashMap<MirFunctionId, FuncId>,
    pub data_id_map: &'a HashMap<GlobalId, DataId>,
}

/// Context for emitting function bodies
pub(crate) struct BodyEmitContext<'a, 'b> {
    pub builder: &'a mut FunctionBuilder<'b>,
    pub mir: &'a MirProgram,
    pub stack_slots: &'a HashMap<LocalId, StackSlot>,
    pub module: &'a mut ObjectModule,
    pub clif_blocks: &'a HashMap<MirBlockId, Block>,
    pub worklist: &'a mut Vec<MirBlockId>,
    pub return_type: Option<Type>,
    pub va_spill_slot: Option<StackSlot>,
    pub func: &'a MirFunction,
    pub func_id_map: &'a HashMap<MirFunctionId, FuncId>,
    pub triple: &'a Triple,
    pub set_al_func: &'a mut Option<FuncId>,
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

fn f64_to_f128_bytes(val: f64) -> [u8; 16] {
    let bits = val.to_bits();
    let sign = (bits >> 63) & 1;
    let exp = (bits >> 52) & 0x7FF;
    let mant = bits & 0xFFFFFFFFFFFFF;

    let (new_exp, new_mant) = if exp == 0 {
        if mant == 0 {
            // Zero
            (0, 0)
        } else {
            // Subnormal f64 -> Normal f128
            // mant is 0.bbbb... (52 bits)
            let lz = mant.leading_zeros() - (64 - 52);
            let shift = lz + 1;
            let normalized_mant = mant << shift;
            let payload = normalized_mant & 0xFFFFFFFFFFFFF; // 52 bits

            let unbiased_exp = -1022 - (shift as i32);
            let biased_exp = unbiased_exp + 16383;

            (biased_exp as u64, (payload as u128) << (112 - 52))
        }
    } else if exp == 0x7FF {
        // Inf or NaN
        (0x7FFF, (mant as u128) << (112 - 52))
    } else {
        // Normal
        let unbiased_exp = (exp as i32) - 1023;
        let biased_exp = unbiased_exp + 16383;
        (biased_exp as u64, (mant as u128) << (112 - 52))
    };

    let sign_bit = (sign as u128) << 127;
    let exp_bits = (new_exp as u128) << 112;
    let mant_bits = new_mant;

    let result = sign_bit | exp_bits | mant_bits;
    result.to_le_bytes()
}

fn f64_to_x87_bytes(val: f64) -> [u8; 16] {
    let bits = val.to_bits();
    let sign = (bits >> 63) & 1;
    let exp = (bits >> 52) & 0x7FF;
    let mant = bits & 0xFFFFFFFFFFFFF;

    let mut out = [0u8; 16];

    if exp == 0 {
        if mant == 0 {
            // Zero
            if sign == 1 {
                out[9] = 0x80;
            }
            return out;
        }

        // Subnormal f64
        // Calculate leading zeros in the 52-bit mantissa
        // 12 zeros because u64 has 64 bits but mant only 52
        let lz = mant.leading_zeros() - 12;

        // Shift to make MSB 1 (integer bit for x87)
        // We want to put the first '1' at bit 63.
        // Currently it is at (51 - lz).
        // Shift left by 63 - (51 - lz) = 12 + lz.
        let new_mant = mant << (12 + lz);

        // Exponent calculation
        // Real exponent of f64 subnormal is -1022.
        // We effectively shifted left by (lz + 1) to normalize (because we moved 0.1... to 1.0...)
        // So we must subtract (lz + 1) from exponent.
        let real_exp = -1022 - (lz as i32 + 1);

        // x87 bias 16383
        let new_exp_biased = (real_exp + 16383) as u16;

        out[0..8].copy_from_slice(&new_mant.to_le_bytes());
        out[8..10].copy_from_slice(&new_exp_biased.to_le_bytes());
        if sign == 1 {
            out[9] |= 0x80;
        }
        return out;
    } else if exp == 0x7FF {
        // Inf or NaN
        out[8] = 0xFF;
        out[9] = 0x7F | ((sign as u8) << 7);

        if mant == 0 {
            // Infinity: Integer bit 1, mantissa 0
            out[7] = 0x80;
        } else {
            // NaN: Set integer bit 1
            // f64 mantissa is 52 bits. x87 is 63 bits.
            // Shift left by 11.
            let new_mant = (1u64 << 63) | (mant << 11);
            out[0..8].copy_from_slice(&new_mant.to_le_bytes());
        }
        return out;
    }

    // Normal f64
    let unbiased_exp = (exp as i32) - 1023;
    let new_exp = (unbiased_exp + 16383) as u16;

    // Explicit integer bit 1 for Normal numbers in x87
    let new_mant = (1u64 << 63) | (mant << 11);

    out[0..8].copy_from_slice(&new_mant.to_le_bytes());
    out[8..10].copy_from_slice(&new_exp.to_le_bytes());

    // Sign bit in byte 9, bit 7
    if sign == 1 {
        out[9] |= 0x80;
    }

    out
}

/// Helper to emit float constants
fn emit_const_float(val: f64, ty: &MirType, output: &mut Vec<u8>) -> Result<(), String> {
    match ty {
        MirType::F32 => {
            let bytes = (val as f32).to_bits().to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::F64 => {
            let bytes = val.to_bits().to_le_bytes();
            output.extend_from_slice(&bytes);
        }
        MirType::F80 => {
            let bytes = f64_to_x87_bytes(val);
            output.extend_from_slice(&bytes);
        }
        MirType::F128 => {
            let bytes = f64_to_f128_bytes(val);
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
    ty: &MirType,
    output: &mut Vec<u8>,
    ctx: &EmitContext,
    mut module: Option<&mut ObjectModule>,
    mut data_description: Option<&mut DataDescription>,
    base_offset: u32,
) -> Result<(), String> {
    match ty {
        MirType::Record {
            layout: record_layout,
            field_types: _,
            ..
        } => {
            // Initialize the entire struct with zeros
            let struct_size = record_layout.size as usize;
            let mut struct_bytes = vec![0u8; struct_size];

            // Emit each field at its proper offset
            for (field_index, field_const_id) in fields {
                if *field_index < record_layout.field_offsets.len() {
                    let field_offset = record_layout.field_offsets[*field_index] as usize;

                    let mut field_bytes = Vec::new();
                    emit_const(
                        *field_const_id,
                        &mut field_bytes,
                        ctx,
                        reborrow_module(&mut module),
                        reborrow_data_description(&mut data_description),
                        base_offset + field_offset as u32,
                    )?;

                    // Copy the field bytes into the struct buffer
                    let required_size = field_offset + field_bytes.len();
                    if required_size > struct_bytes.len() {
                        struct_bytes.resize(required_size, 0);
                    }
                    struct_bytes[field_offset..field_offset + field_bytes.len()].copy_from_slice(&field_bytes);
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
    ty: &MirType,
    output: &mut Vec<u8>,
    ctx: &EmitContext,
    mut module: Option<&mut ObjectModule>,
    mut data_description: Option<&mut DataDescription>,
    base_offset: u32,
) -> Result<(), String> {
    match ty {
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

    let ty = ctx.mir.get_type(const_value.ty);

    match &const_value.kind {
        ConstValueKind::Int(val) => emit_const_int(*val, ty, output),
        ConstValueKind::Float(val) => emit_const_float(*val, ty, output),
        ConstValueKind::Bool(val) => {
            let byte = if *val { 1u8 } else { 0u8 };
            output.push(byte);
            Ok(())
        }
        ConstValueKind::Null => {
            // Emit null as all zeros (pointer-sized)
            let null_bytes = 0i64.to_le_bytes();
            output.extend_from_slice(&null_bytes);
            Ok(())
        }
        ConstValueKind::Zero => {
            // Emit zeros for the entire type size
            let size = mir_type_size(ty, ctx.mir)? as usize;
            output.extend_from_slice(&vec![0u8; size]);
            Ok(())
        }
        ConstValueKind::GlobalAddress(global_id) => {
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
        ConstValueKind::FunctionAddress(func_id) => {
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
        ConstValueKind::StructLiteral(fields) => {
            emit_const_struct(fields, ty, output, ctx, module, data_description, offset)
        }
        ConstValueKind::ArrayLiteral(elements) => {
            emit_const_array(elements, ty, output, ctx, module, data_description, offset)
        }
    }
}

fn reborrow_module<'b>(m: &'b mut Option<&mut ObjectModule>) -> Option<&'b mut ObjectModule> {
    m.as_mut().map(|inner| &mut **inner)
}

fn reborrow_data_description<'b>(dd: &'b mut Option<&mut DataDescription>) -> Option<&'b mut DataDescription> {
    dd.as_mut().map(|inner| &mut **inner)
}

/// Helper to determine if a type consumes an XMM register (float/vector)
fn is_xmm_argument(mir_type: &MirType) -> bool {
    matches!(mir_type, MirType::F32 | MirType::F64 | MirType::F80 | MirType::F128)
}

/// Helper to prepare a function signature for a call
fn prepare_call_signature(
    call_conv: cranelift::codegen::isa::CallConv,
    return_type_id: TypeId,
    param_types: &[TypeId],
    args: &[Operand],
    mir: &MirProgram,
    is_variadic: bool,
    use_variadic_hack: bool,
    triple: &Triple,
) -> Signature {
    let mut sig = Signature::new(call_conv);
    // sig.set_is_variadic(is_variadic); // Try if this method exists

    // Return type
    let return_mir_type = mir.get_type(return_type_id);
    let return_type_opt = match convert_type(return_mir_type) {
        Some(t) => Some(t),
        None if return_mir_type.is_aggregate() => Some(types::I64),
        None => None,
    };
    if let Some(ret_type) = return_type_opt {
        sig.returns.push(AbiParam::new(ret_type));
    }

    // Use split ABI for internal functions (defined or indirect calls)
    let split_f128 = use_variadic_hack;

    // Track used XMM registers for SystemV ABI hack
    let mut xmm_used = 0;

    // Fixed parameters
    for &param_type_id in param_types {
        let mir_type = mir.get_type(param_type_id);

        if is_xmm_argument(mir_type) {
            xmm_used += 1;
        }

        if split_f128 && matches!(mir_type, MirType::F80 | MirType::F128) {
            sig.params.push(AbiParam::new(types::I64));
            sig.params.push(AbiParam::new(types::I64));
            continue;
        }

        let param_type = match convert_type(mir_type) {
            Some(t) => t,
            None if mir_type.is_aggregate() => types::I64,
            None => types::I32, // Should not happen for valid MIR
        };
        sig.params.push(AbiParam::new(param_type));
    }

    // Variadic arguments (if any) - structs are expanded to multiple I64 slots
    for arg in args.iter().skip(param_types.len()) {
        let arg_type_id = get_operand_type_id(arg, mir).ok();
        if let Some(type_id) = arg_type_id {
            let mir_type = mir.get_type(type_id);
            if mir_type.is_aggregate() {
                // For structs/arrays, calculate how many I64 slots we need
                let size = mir_type_size(mir_type, mir).unwrap_or(8);
                let num_slots = size.div_ceil(8) as usize; // Round up to nearest 8 bytes
                for _ in 0..num_slots {
                    sig.params.push(AbiParam::new(types::I64));
                }
                continue;
            }

            if split_f128 && matches!(mir_type, MirType::F80 | MirType::F128) {
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                continue;
            }

            // HACK: For x86_64 SystemV extern calls, force long double (F80/F128) to stack
            // by exhausting XMM registers if they are not already full.
            if !split_f128
                && triple.architecture == target_lexicon::Architecture::X86_64
                && matches!(mir_type, MirType::F80 | MirType::F128)
            {
                let needed_padding = 8usize.saturating_sub(xmm_used);
                for _ in 0..needed_padding {
                    sig.params.push(AbiParam::new(types::F64));
                }
                // We've effectively filled the registers
                xmm_used = 8;
            }

            if is_xmm_argument(mir_type) {
                xmm_used += 1;
            }
        }
        let mut arg_type = get_operand_clif_type(arg, mir).unwrap_or(types::I32);

        if use_variadic_hack {
            // Normalized Variadic Signature hack: promote variadic GPR args to i64
            if is_variadic && arg_type.is_int() && arg_type.bits() < 64 {
                arg_type = types::I64;
            }
        }

        sig.params.push(AbiParam::new(arg_type));
    }

    if use_variadic_hack {
        // Normalized Variadic Signature hack: Ensure at least 32 slots for variadic functions
        // This matches the 32-slot spill area in setup_signature
        if is_variadic {
            let current_gpr_count = sig.params.len();
            let total_variadic_slots = 32;
            if current_gpr_count < total_variadic_slots {
                for _ in 0..(total_variadic_slots - current_gpr_count) {
                    sig.params.push(AbiParam::new(types::I64));
                }
            }
        }
    }

    sig
}

/// Helper to resolve arguments for a call, handling variadic struct expansion if needed
fn resolve_call_args(
    args: &[Operand],
    fixed_param_count: usize,
    sig: &Signature,
    ctx: &mut BodyEmitContext,
    is_variadic: bool,
    split_f128: bool,
    triple: &Triple,
) -> Result<Vec<Value>, String> {
    let mut arg_values = Vec::new();
    let mut sig_idx = 0;
    let mut xmm_used = 0;

    // Count XMM usage from fixed parameters first (checking signatures from ctx.mir logic if needed)
    // But here we iterate all args. We need to distinguish fixed params.
    // We can assume first `fixed_param_count` args match `sig`'s first params,
    // but `sig` might have split params.
    // Simpler: iterate fixed_param_count args and check types.
    for i in 0..fixed_param_count {
        if let Some(arg) = args.get(i)
            && let Ok(type_id) = get_operand_type_id(arg, ctx.mir)
        {
            let mir_type = ctx.mir.get_type(type_id);
            if is_xmm_argument(mir_type) {
                xmm_used += 1;
            }
        }
    }

    for (arg_idx, arg) in args.iter().enumerate() {
        if sig_idx >= sig.params.len() {
            break;
        }

        // Check operand type
        let arg_type_id = get_operand_type_id(arg, ctx.mir).ok();

        // Check if F128 splitting is needed
        if split_f128
            && let Some(type_id) = arg_type_id
            && matches!(ctx.mir.get_type(type_id), MirType::F80 | MirType::F128)
        {
            let val = resolve_operand(arg, ctx, types::F128)?;
            // Split val into lo, hi by storing to stack and reloading
            let slot = ctx
                .builder
                .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 16, 0));
            ctx.builder.ins().stack_store(val, slot, 0);
            let lo = ctx.builder.ins().stack_load(types::I64, slot, 0);
            let hi = ctx.builder.ins().stack_load(types::I64, slot, 8);

            arg_values.push(lo);
            arg_values.push(hi);

            sig_idx += 2;
            continue;
        }

        // Check if this is a variadic struct argument that needs expansion
        if is_variadic
            && arg_idx >= fixed_param_count
            && let Some(type_id) = arg_type_id
        {
            let mir_type = ctx.mir.get_type(type_id);
            if mir_type.is_aggregate() {
                // Get the struct address
                let struct_addr = resolve_operand(arg, ctx, types::I64)?;

                // Calculate how many I64 slots this struct needs
                let size = mir_type_size(mir_type, ctx.mir).unwrap_or(8);
                let num_slots = size.div_ceil(8) as usize;

                // Load each I64 chunk from the struct
                for slot in 0..num_slots {
                    if sig_idx < sig.params.len() {
                        let offset = (slot * 8) as i32;

                        // Check if this is the last slot and if we need partial load
                        let current_offset = slot * 8;
                        let remaining_bytes = size as usize - current_offset;

                        let value = if remaining_bytes >= 8 {
                            ctx.builder.ins().load(types::I64, MemFlags::new(), struct_addr, offset)
                        } else {
                            // Partial load byte-by-byte to avoid OOB read
                            let mut current_val = ctx.builder.ins().iconst(types::I64, 0);
                            for i in 0..remaining_bytes {
                                let byte_val =
                                    ctx.builder
                                        .ins()
                                        .load(types::I8, MemFlags::new(), struct_addr, offset + i as i32);
                                let byte_ext = ctx.builder.ins().uextend(types::I64, byte_val);
                                let shift_amt = ctx.builder.ins().iconst(types::I64, (i * 8) as i64);
                                let shifted = ctx.builder.ins().ishl(byte_ext, shift_amt);
                                current_val = ctx.builder.ins().bor(current_val, shifted);
                            }
                            current_val
                        };

                        arg_values.push(value);
                        sig_idx += 1;
                    }
                }
                continue;
            }

            // HACK: Apply padding to force stack usage for long double
            if !split_f128
                && triple.architecture == target_lexicon::Architecture::X86_64
                && matches!(mir_type, MirType::F80 | MirType::F128)
            {
                let needed_padding = 8usize.saturating_sub(xmm_used);
                for _ in 0..needed_padding {
                    if sig_idx < sig.params.len() {
                        arg_values.push(ctx.builder.ins().f64const(0.0));
                        sig_idx += 1;
                    }
                }
                xmm_used = 8;
            }

            if is_xmm_argument(mir_type) {
                xmm_used += 1;
            }
        }

        // Update param_type as sig_idx might have changed due to padding
        if sig_idx >= sig.params.len() {
            break;
        }
        let param_type = sig.params[sig_idx].value_type;

        // Non-struct argument (or fixed param)
        match resolve_operand(arg, ctx, param_type) {
            Ok(value) => arg_values.push(value),
            Err(e) => return Err(format!("Failed to resolve function argument: {}", e)),
        }
        sig_idx += 1;
    }

    // Padding for remaining signature params (variadic slot padding SysV x86_64 hack)
    while sig_idx < sig.params.len() {
        let param_type = sig.params[sig_idx].value_type;
        arg_values.push(ctx.builder.ins().iconst(param_type, 0i64));
        sig_idx += 1;
    }

    Ok(arg_values)
}

/// Helper to get the result of a call, or a zero constant if it has no return value
fn get_call_result(builder: &mut FunctionBuilder, call_inst: Inst, expected_type: Type) -> Value {
    let results = builder.inst_results(call_inst);
    if results.is_empty() {
        builder.ins().iconst(expected_type, 0i64)
    } else {
        results[0]
    }
}

fn emit_function_call_impl(
    call_target: &CallTarget,
    args: &[Operand],
    expected_type: Type,
    ctx: &mut BodyEmitContext,
) -> Result<Value, String> {
    // 1. Determine function properties and callee address if indirect/variadic
    let (return_type_id, param_types, is_variadic, name_linkage, target_addr, use_variadic_hack) = match call_target {
        CallTarget::Direct(func_id) => {
            let func = ctx.mir.get_function(*func_id);
            let param_types: Vec<TypeId> = func.params.iter().map(|&p| ctx.mir.get_local(p).type_id).collect();
            let name_linkage = Some((func.name.as_str(), convert_linkage(func.kind)));
            let is_defined = matches!(func.kind, MirFunctionKind::Defined);
            (
                func.return_type,
                param_types,
                func.is_variadic,
                name_linkage,
                None,
                is_defined,
            )
        }
        CallTarget::Indirect(func_operand) => {
            let func_ptr_type_id = get_operand_type_id(func_operand, ctx.mir)
                .map_err(|e| format!("Failed to get function pointer type: {}", e))?;
            let func_ptr_type = ctx.mir.get_type(func_ptr_type_id);

            let ((return_type_id, param_types), is_function_type, is_variadic_call) = match func_ptr_type {
                MirType::Pointer { pointee } => match ctx.mir.get_type(*pointee) {
                    MirType::Function {
                        return_type,
                        params,
                        is_variadic,
                    } => ((*return_type, params.clone()), false, *is_variadic),
                    _ => return Err("Indirect call operand points to non-function type".to_string()),
                },
                MirType::Function {
                    return_type,
                    params,
                    is_variadic,
                } => ((*return_type, params.clone()), true, *is_variadic),
                _ => return Err("Indirect call operand is not a pointer".to_string()),
            };

            let callee_val = if is_function_type {
                match func_operand {
                    Operand::Copy(place) => resolve_place_to_addr(place, ctx)?,
                    _ => resolve_operand(func_operand, ctx, types::I64)?,
                }
            } else {
                resolve_operand(func_operand, ctx, types::I64)?
            };

            // Assuming function pointers point to internal functions requiring the hack.
            // TODO: Distinguish between internal and external function pointers if possible.
            (
                return_type_id,
                param_types,
                is_variadic_call,
                None,
                Some(callee_val),
                true,
            )
        }
    };

    // 2. Prepare call site signature and resolve arguments
    let sig = prepare_call_signature(
        ctx.builder.func.signature.call_conv,
        return_type_id,
        &param_types,
        args,
        ctx.mir,
        is_variadic,
        use_variadic_hack,
        ctx.triple,
    );

    let split_f128 = use_variadic_hack;
    let arg_values = resolve_call_args(args, param_types.len(), &sig, ctx, is_variadic, split_f128, ctx.triple)?;

    // 3. Emit the call
    let call_inst = if is_variadic {
        if let Some((name, linkage)) = name_linkage {
            // Variadic direct calls must be indirect to use the custom signature
            let canonical_sig = prepare_call_signature(
                ctx.builder.func.signature.call_conv,
                return_type_id,
                &param_types,
                &[],
                ctx.mir,
                is_variadic,
                use_variadic_hack,
                ctx.triple,
            );
            let decl = ctx
                .module
                .declare_function(name, linkage, &canonical_sig)
                .map_err(|e| format!("Failed to declare variadic function {}: {:?}", name, e))?;
            let func_ref = ctx.module.declare_func_in_func(decl, ctx.builder.func);
            let addr = ctx.builder.ins().func_addr(types::I64, func_ref);
            let sig_ref = ctx.builder.import_signature(sig);

            let addr = emit_al_count_and_pass_addr(args, &param_types, addr, ctx)?;

            ctx.builder.ins().call_indirect(sig_ref, addr, &arg_values)
        } else if let Some(addr) = target_addr {
            let sig_ref = ctx.builder.import_signature(sig);
            let addr = emit_al_count_and_pass_addr(args, &param_types, addr, ctx)?;
            ctx.builder.ins().call_indirect(sig_ref, addr, &arg_values)
        } else {
            return Err("Variadic call without target".to_string());
        }
    } else if let Some(addr) = target_addr {
        let sig_ref = ctx.builder.import_signature(sig);
        ctx.builder.ins().call_indirect(sig_ref, addr, &arg_values)
    } else {
        // Direct non-variadic call
        let (name, linkage) = name_linkage.unwrap();
        let decl = ctx
            .module
            .declare_function(name, linkage, &sig)
            .map_err(|e| format!("Failed to declare function {}: {:?}", name, e))?;
        let func_ref = ctx.module.declare_func_in_func(decl, ctx.builder.func);
        ctx.builder.ins().call(func_ref, &arg_values)
    };

    Ok(get_call_result(ctx.builder, call_inst, expected_type))
}

/// Helper function to convert boolean to integer (0 or 1)
fn emit_al_count_and_pass_addr(
    args: &[Operand],
    param_types: &[TypeId],
    addr: Value,
    ctx: &mut BodyEmitContext,
) -> Result<Value, String> {
    // x86_64 SysV ABI requires AL to be set to the number of floating point arguments for variadic calls.
    if ctx.triple.architecture == target_lexicon::Architecture::X86_64
        && ctx.builder.func.signature.call_conv == cranelift::codegen::isa::CallConv::SystemV
    {
        let mut fp_arg_count = 0;
        for (i, arg) in args.iter().enumerate() {
            // Only count arguments that are NOT fixed parameters
            if i >= param_types.len() {
                let arg_mir_type = ctx.mir.get_type(get_operand_type_id(arg, ctx.mir).unwrap());
                if matches!(arg_mir_type, MirType::F32 | MirType::F64) {
                    fp_arg_count += 1;
                }
            }
        }

        // Ensure fp_arg_count doesn't exceed 8 (number of XMM registers used for args)
        let fp_arg_count = fp_arg_count.min(8);

        // Define __cendol_set_al if not already defined
        if ctx.set_al_func.is_none() {
            *ctx.set_al_func = Some(emit_cendol_set_al(ctx.module)?);
        }

        let set_al_func = ctx.set_al_func.unwrap();
        let local_set_al = ctx.module.declare_func_in_func(set_al_func, ctx.builder.func);
        let count_val = ctx.builder.ins().iconst(types::I64, fp_arg_count as i64);
        let call_inst = ctx.builder.ins().call(local_set_al, &[count_val, addr]);
        Ok(ctx.builder.inst_results(call_inst)[1]) // Return the address (RDX)
    } else {
        Ok(addr)
    }
}

fn emit_bool_to_int(val: Value, target_type: Type, builder: &mut FunctionBuilder) -> Value {
    let one = builder.ins().iconst(target_type, 1);
    let zero = builder.ins().iconst(target_type, 0i64);
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
fn resolve_operand(operand: &Operand, ctx: &mut BodyEmitContext, expected_type: Type) -> Result<Value, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = ctx.mir.constants.get(const_id).expect("constant id not found");
            match &const_value.kind {
                ConstValueKind::Int(val) => Ok(ctx.builder.ins().iconst(expected_type, *val)),
                ConstValueKind::Float(val) => {
                    // Use the appropriate float constant based on expected type
                    if expected_type == types::F64 {
                        Ok(ctx.builder.ins().f64const(*val))
                    } else if expected_type == types::F32 {
                        Ok(ctx.builder.ins().f32const(*val as f32))
                    } else if expected_type == types::F128 {
                        // Use memory load for F128 to ensure precision and correct bit pattern (x87 or IEEE)
                        let bytes = if ctx.triple.architecture == target_lexicon::Architecture::X86_64 {
                            f64_to_x87_bytes(*val)
                        } else {
                            f64_to_f128_bytes(*val)
                        };

                        let data_id = ctx
                            .module
                            .declare_anonymous_data(false, false)
                            .map_err(|e| format!("Failed to declare anonymous data: {:?}", e))?;

                        let mut dd = DataDescription::new();
                        dd.define(bytes.to_vec().into_boxed_slice());
                        ctx.module
                            .define_data(data_id, &dd)
                            .map_err(|e| format!("Failed to define anonymous data: {:?}", e))?;

                        let global_val = ctx.module.declare_data_in_func(data_id, ctx.builder.func);
                        let addr = ctx.builder.ins().global_value(types::I64, global_val);
                        Ok(ctx
                            .builder
                            .ins()
                            .load(types::F128, MemFlags::new().with_readonly(), addr, 0))
                    } else {
                        Ok(ctx.builder.ins().f32const(*val as f32))
                    }
                }
                ConstValueKind::Bool(val) => {
                    let int_val = if *val { 1 } else { 0 };
                    Ok(ctx.builder.ins().iconst(expected_type, int_val))
                }
                ConstValueKind::Null => Ok(ctx.builder.ins().iconst(expected_type, 0i64)),
                ConstValueKind::GlobalAddress(global_id) => {
                    // Get the global variable and return its address
                    // This handles the array-to-pointer decay for string literals
                    let global = ctx.mir.get_global(*global_id);
                    let global_val = ctx
                        .module
                        .declare_data(global.name.as_str(), Linkage::Export, true, false)
                        .map_err(|e| format!("Failed to declare global data: {:?}", e))?;
                    let local_id = ctx.module.declare_data_in_func(global_val, ctx.builder.func);
                    // Global addresses are always pointer-sized (i64)
                    let addr = ctx.builder.ins().global_value(types::I64, local_id);
                    Ok(emit_type_conversion(
                        addr,
                        types::I64,
                        expected_type,
                        false,
                        ctx.builder,
                    ))
                }
                ConstValueKind::FunctionAddress(func_id) => {
                    if let Some(&clif_func_id) = ctx.func_id_map.get(func_id) {
                        let func_ref = ctx.module.declare_func_in_func(clif_func_id, ctx.builder.func);
                        let addr = ctx.builder.ins().func_addr(types::I64, func_ref);
                        Ok(emit_type_conversion(
                            addr,
                            types::I64,
                            expected_type,
                            false,
                            ctx.builder,
                        ))
                    } else {
                        Err(format!("Function ID {} not found in map", func_id.get()))
                    }
                }
                _ => Ok(ctx.builder.ins().iconst(expected_type, 0i64)),
            }
        }
        Operand::Copy(place) => {
            // Determine the correct type from the place itself
            let place_type_id = get_place_type_id(place, ctx.mir);
            let place_type = ctx.mir.get_type(place_type_id);

            if place_type.is_aggregate() {
                // For aggregate types, resolving the operand value means getting its address
                let addr = resolve_place_to_addr(place, ctx)?;
                return Ok(emit_type_conversion(
                    addr,
                    types::I64,
                    expected_type,
                    false,
                    ctx.builder,
                ));
            }

            let place_clif_type =
                convert_type(place_type).ok_or_else(|| format!("Unsupported place type: {:?}", place_type))?;

            let val = resolve_place(place, ctx, place_clif_type)?;
            Ok(emit_type_conversion(
                val,
                place_clif_type,
                expected_type,
                place_type.is_signed(),
                ctx.builder,
            ))
        }
        Operand::Cast(type_id, inner_operand) => {
            let inner_type = get_operand_clif_type(inner_operand, ctx.mir)?;
            let inner_val = resolve_operand(inner_operand, ctx, inner_type)?;

            let mir_type = ctx.mir.get_type(*type_id);
            let target_type = convert_type(mir_type).unwrap_or(types::I32);

            let converted = emit_type_conversion(
                inner_val,
                inner_type,
                target_type,
                is_operand_signed(inner_operand, ctx.mir),
                ctx.builder,
            );
            Ok(emit_type_conversion(
                converted,
                target_type,
                expected_type,
                mir_type.is_signed(),
                ctx.builder,
            ))
        }
        Operand::AddressOf(place) => {
            // The value of an AddressOf operand is the address of the place.
            let addr = resolve_place_to_addr(place, ctx)?;
            Ok(emit_type_conversion(
                addr,
                types::I64,
                expected_type,
                false,
                ctx.builder,
            ))
        }
    }
}

/// Helper function to resolve a MIR place to a Cranelift value
fn resolve_place(place: &Place, ctx: &mut BodyEmitContext, expected_type: Type) -> Result<Value, String> {
    match place {
        Place::Local(local_id) => {
            // A local place is resolved by loading from its stack slot
            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                Ok(ctx.builder.ins().stack_load(expected_type, *stack_slot, 0))
            } else {
                Err(format!("Stack slot not found for local {}", local_id.get()))
            }
        }
        Place::Global(_global_id) => {
            // First, get the memory address of the global.
            let addr = resolve_place_to_addr(place, ctx)?;

            // Then, load the value from that address.
            Ok(ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
        Place::Deref(operand) => {
            // The address is the value of the operand, so we load from that value
            let addr = resolve_operand(operand, ctx, types::I64)?;
            Ok(ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
        Place::StructField(base_place, field_index) => {
            // Get the address of the struct field
            let addr = resolve_place_to_addr(&Place::StructField(base_place.clone(), *field_index), ctx)?;
            Ok(ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
        Place::ArrayIndex(base_place, index_operand) => {
            // Get the address of the array element
            let addr = resolve_place_to_addr(&Place::ArrayIndex(base_place.clone(), index_operand.clone()), ctx)?;
            Ok(ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0))
        }
    }
}

/// Helper function to get the Cranelift Type of an operand
fn get_operand_clif_type(operand: &Operand, mir: &MirProgram) -> Result<Type, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = mir.constants.get(const_id).expect("constant id not found");
            let mir_type = mir.get_type(const_value.ty);

            // If we have a specific type for the constant, use that to determine the Cranelift type
            if let Some(clif_type) = convert_type(mir_type) {
                return Ok(clif_type);
            }

            // Fallback to kind-based determination if type is not convertible (e.g., struct/array)
            match &const_value.kind {
                // Integer literals in MIR are typically used in integer-sized contexts
                // Default to I32 so common small integer constants (like `4`) match i32
                // places instead of being treated as 64-bit immediates.
                ConstValueKind::Int(_) => Ok(types::I32),
                ConstValueKind::Float(_) => Ok(types::F64),
                ConstValueKind::Bool(_) => Ok(types::I32),
                // Null/Zero/Global addresses are pointer-sized
                ConstValueKind::Null | ConstValueKind::Zero | ConstValueKind::GlobalAddress(_) => Ok(types::I64),
                ConstValueKind::FunctionAddress(_) => Ok(types::I64),
                ConstValueKind::StructLiteral(_) => Ok(types::I32),
                ConstValueKind::ArrayLiteral(_) => Ok(types::I32),
            }
        }
        Operand::Copy(place) => {
            let place_type_id = get_place_type_id(place, mir);
            let place_type = mir.get_type(place_type_id);
            if place_type.is_aggregate() {
                return Ok(types::I64);
            }
            convert_type(place_type).ok_or_else(|| format!("Unsupported place type: {:?}", place_type))
        }
        Operand::Cast(type_id, _) => {
            let mir_type = mir.get_type(*type_id);
            if mir_type.is_aggregate() {
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
        Operand::Copy(place) => mir.get_type(get_place_type_id(place, mir)).is_signed(),
        Operand::Cast(type_id, _) => mir.get_type(*type_id).is_signed(),
        Operand::Constant(const_id) => {
            let const_val = mir.constants.get(const_id).expect("constant id not found");
            mir.get_type(const_val.ty).is_signed()
        }
        _ => false,
    }
}

/// Helper function to get the TypeId of an operand
fn get_operand_type_id(operand: &Operand, mir: &MirProgram) -> Result<TypeId, String> {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = mir.constants.get(const_id).expect("constant id not found");
            Ok(const_value.ty)
        }
        Operand::Copy(place) => Ok(get_place_type_id(place, mir)),
        Operand::Cast(type_id, _) => Ok(*type_id),
        Operand::AddressOf(place) => {
            // AddressOf returns a pointer to the place's type.
            // We need to find or create this pointer type in MIR.
            // Actually, for PtrAdd scaling, we only care about the base type of the pointer.
            let place_type_id = get_place_type_id(place, mir);
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
fn get_place_type_id(place: &Place, mir: &MirProgram) -> TypeId {
    match place {
        Place::Local(local_id) => mir.get_local(*local_id).type_id,
        Place::Global(global_id) => mir.get_global(*global_id).type_id,
        Place::Deref(operand) => {
            // To get the type of a dereference, we need the type of the operand,
            // which should be a pointer. The resulting type is the pointee.
            let operand_type_id = get_operand_type_id(operand, mir).unwrap();
            let operand_type = mir.get_type(operand_type_id);
            match operand_type {
                MirType::Pointer { pointee } => *pointee,
                _ => panic!("Cannot determine type for deref operand"),
            }
        }
        Place::StructField(base_place, field_index) => {
            let base_type_id = get_place_type_id(base_place, mir);
            let base_type = mir.get_type(base_type_id);
            match base_type {
                MirType::Record { field_types, .. } => field_types.get(*field_index).copied().unwrap(),
                MirType::Pointer { pointee } => {
                    let pointee_type = mir.get_type(*pointee);
                    if let MirType::Record { field_types, .. } = pointee_type {
                        field_types.get(*field_index).copied().unwrap()
                    } else {
                        panic!("Base of StructField is not a struct type")
                    }
                }
                _ => panic!("Base of StructField is not a struct type"),
            }
        }
        Place::ArrayIndex(base_place, _) => {
            let base_type_id = get_place_type_id(base_place, mir);
            let base_type = mir.get_type(base_type_id);
            match base_type {
                MirType::Array { element, .. } => *element,
                MirType::Pointer { pointee } => *pointee,
                _ => panic!("Base of ArrayIndex is not an array or pointer"),
            }
        }
    }
}

/// Helper function to resolve a MIR place to a memory address
fn resolve_place_to_addr(place: &Place, ctx: &mut BodyEmitContext) -> Result<Value, String> {
    match place {
        Place::Local(local_id) => {
            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                Ok(ctx.builder.ins().stack_addr(types::I64, *stack_slot, 0))
            } else {
                Err(format!("Stack slot not found for local {}", local_id.get()))
            }
        }
        Place::Global(global_id) => {
            let global = ctx.mir.get_global(*global_id);
            let linkage = if global.initial_value.is_some() {
                Linkage::Export
            } else {
                Linkage::Import
            };

            let global_val = ctx
                .module
                .declare_data(global.name.as_str(), linkage, true, false)
                .map_err(|e| format!("Failed to declare global data: {:?}", e))?;
            let local_id = ctx.module.declare_data_in_func(global_val, ctx.builder.func);
            // Use I64 for addresses
            Ok(ctx.builder.ins().global_value(types::I64, local_id))
        }
        Place::Deref(operand) => {
            // The address is the value of the operand itself (which should be a pointer).
            resolve_operand(operand, ctx, types::I64)
        }
        Place::StructField(base_place, field_index) => {
            // Get the base address of the struct
            let base_addr = resolve_place_to_addr(base_place, ctx)?;

            // We need to find the type of the base_place to get the pre-computed field offset
            let base_place_type_id = get_place_type_id(base_place, ctx.mir);
            let base_type = ctx.mir.get_type(base_place_type_id);

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
                    let pointee_type = ctx.mir.get_type(*pointee);
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
                ctx.builder.ins().load(types::I64, MemFlags::new(), base_addr, 0)
            } else {
                base_addr
            };

            let offset_val = ctx.builder.ins().iconst(types::I64, field_offset as i64);
            Ok(ctx.builder.ins().iadd(final_addr, offset_val))
        }
        Place::ArrayIndex(base_place, index_operand) => {
            // Get the base address of the array/pointer
            let base_addr = resolve_place_to_addr(base_place, ctx)?;

            // Resolve the index operand to a value
            let index_val = resolve_operand(index_operand, ctx, types::I64)?;

            // Determine the element size using pre-computed layout information
            let base_place_type_id = get_place_type_id(base_place, ctx.mir);
            let base_type = ctx.mir.get_type(base_place_type_id);

            // If the base is a pointer, we must load the pointer value from the base address
            // before adding the element offset. For arrays, the base address is already
            // the address of the first element.
            let (element_size, final_base_addr) = match base_type {
                MirType::Array { layout, .. } => (layout.stride as u32, base_addr),
                MirType::Pointer { pointee } => {
                    let pointee_type = ctx.mir.get_type(*pointee);
                    let size = mir_type_size(pointee_type, ctx.mir)?;
                    let loaded_ptr = ctx.builder.ins().load(types::I64, MemFlags::new(), base_addr, 0);
                    (size, loaded_ptr)
                }
                _ => return Err("Base of ArrayIndex is not an array or pointer".to_string()),
            };

            let element_size_val = ctx.builder.ins().iconst(types::I64, element_size as i64);
            let offset = ctx.builder.ins().imul(index_val, element_size_val);

            Ok(ctx.builder.ins().iadd(final_base_addr, offset))
        }
    }
}
/// Helper to lower a single MIR statement
fn lower_statement(stmt: &MirStmt, ctx: &mut BodyEmitContext) -> Result<(), String> {
    match stmt {
        MirStmt::Assign(place, rvalue) => {
            let place_type_id = get_place_type_id(place, ctx.mir);
            let place_mir_type = ctx.mir.get_type(place_type_id);
            let expected_type = match convert_type(place_mir_type) {
                Some(t) => t,
                None if place_mir_type.is_aggregate() => types::I64,
                None => return Err("Cannot assign to void type".to_string()),
            };

            // Process the rvalue to get a Cranelift value first
            let rvalue_result = match rvalue {
                Rvalue::Use(operand) => resolve_operand(operand, ctx, expected_type),
                Rvalue::Cast(type_id, operand) => {
                    let inner_clif_type = get_operand_clif_type(operand, ctx.mir)?;
                    let inner_val = resolve_operand(operand, ctx, inner_clif_type)?;

                    let target_mir_type = ctx.mir.get_type(*type_id);
                    let target_clif_type =
                        convert_type(target_mir_type).ok_or_else(|| "Cannot cast to void type".to_string())?;

                    let converted = emit_type_conversion(
                        inner_val,
                        inner_clif_type,
                        target_clif_type,
                        is_operand_signed(operand, ctx.mir),
                        ctx.builder,
                    );

                    Ok(emit_type_conversion(
                        converted,
                        target_clif_type,
                        expected_type,
                        target_mir_type.is_signed(),
                        ctx.builder,
                    ))
                }
                Rvalue::UnaryIntOp(op, operand) => {
                    let operand_clif_type = get_operand_clif_type(operand, ctx.mir)?;
                    let val = resolve_operand(operand, ctx, operand_clif_type)?;

                    match op {
                        UnaryIntOp::Neg => Ok(ctx.builder.ins().ineg(val)),
                        UnaryIntOp::BitwiseNot => Ok(ctx.builder.ins().bnot(val)),
                        UnaryIntOp::LogicalNot => {
                            let zero = ctx.builder.ins().iconst(operand_clif_type, 0i64);
                            let is_zero = ctx.builder.ins().icmp(IntCC::Equal, val, zero);
                            Ok(emit_bool_to_int(is_zero, expected_type, ctx.builder))
                        }
                    }
                }
                Rvalue::UnaryFloatOp(op, operand) => {
                    let operand_clif_type = get_operand_clif_type(operand, ctx.mir)?;
                    let val = resolve_operand(operand, ctx, operand_clif_type)?;

                    match op {
                        UnaryFloatOp::Neg => Ok(ctx.builder.ins().fneg(val)),
                    }
                }
                Rvalue::PtrAdd(base, offset) => {
                    let base_type_id = get_operand_type_id(base, ctx.mir)?;
                    let base_type = ctx.mir.get_type(base_type_id);
                    let MirType::Pointer { pointee } = base_type else {
                        return Err("PtrAdd base is not a pointer type".to_string());
                    };

                    let pointee_type = ctx.mir.get_type(*pointee);
                    let pointee_size = mir_type_size(pointee_type, ctx.mir)?;

                    let base_val = resolve_operand(base, ctx, types::I64)?;
                    let offset_val = resolve_operand(offset, ctx, types::I64)?;

                    let scaled_offset = if pointee_size > 1 {
                        let size_val = ctx.builder.ins().iconst(types::I64, pointee_size as i64);
                        ctx.builder.ins().imul(offset_val, size_val)
                    } else {
                        offset_val
                    };

                    Ok(ctx.builder.ins().iadd(base_val, scaled_offset))
                }
                Rvalue::PtrSub(base, offset) => {
                    let base_type_id = get_operand_type_id(base, ctx.mir)?;
                    let base_type = ctx.mir.get_type(base_type_id);
                    let MirType::Pointer { pointee } = base_type else {
                        return Err("PtrSub base is not a pointer type".to_string());
                    };

                    let pointee_type = ctx.mir.get_type(*pointee);
                    let pointee_size = mir_type_size(pointee_type, ctx.mir)?;

                    let base_val = resolve_operand(base, ctx, types::I64)?;
                    let offset_val = resolve_operand(offset, ctx, types::I64)?;

                    let scaled_offset = if pointee_size > 1 {
                        let size_val = ctx.builder.ins().iconst(types::I64, pointee_size as i64);
                        ctx.builder.ins().imul(offset_val, size_val)
                    } else {
                        offset_val
                    };

                    Ok(ctx.builder.ins().isub(base_val, scaled_offset))
                }
                Rvalue::PtrDiff(left, right) => {
                    let left_type_id = get_operand_type_id(left, ctx.mir)?;
                    let left_type = ctx.mir.get_type(left_type_id);
                    let pointee_size = if let MirType::Pointer { pointee } = left_type {
                        let pointee_type = ctx.mir.get_type(*pointee);
                        mir_type_size(pointee_type, ctx.mir)?
                    } else {
                        return Err("PtrDiff left operand is not a pointer type".to_string());
                    };

                    let left_val = resolve_operand(left, ctx, types::I64)?;
                    let right_val = resolve_operand(right, ctx, types::I64)?;

                    let diff = ctx.builder.ins().isub(left_val, right_val);
                    if pointee_size > 1 {
                        let size_val = ctx.builder.ins().iconst(types::I64, pointee_size as i64);
                        Ok(ctx.builder.ins().sdiv(diff, size_val))
                    } else {
                        Ok(diff)
                    }
                }
                Rvalue::Load(operand) => {
                    let addr = resolve_operand(operand, ctx, types::I64)?;
                    Ok(ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0))
                }

                Rvalue::BinaryIntOp(op, left_operand, right_operand) => {
                    let left_clif_type = get_operand_clif_type(left_operand, ctx.mir)
                        .map_err(|e| format!("Failed to get left operand type: {}", e))?;
                    let right_clif_type = get_operand_clif_type(right_operand, ctx.mir)
                        .map_err(|e| format!("Failed to get right operand type: {}", e))?;

                    // For Add/Sub operations on Pointers, we treat them as I64
                    let (final_left_type, final_right_type) = match op {
                        BinaryIntOp::Add | BinaryIntOp::Sub => {
                            if left_clif_type == types::I64 && right_clif_type == types::I32 {
                                // Pointer + int constant
                                (types::I64, types::I64)
                            } else if left_clif_type == types::I32 && right_clif_type == types::I64 {
                                // int constant + pointer
                                (types::I64, types::I64)
                            } else {
                                (left_clif_type, right_clif_type)
                            }
                        }
                        _ => (left_clif_type, right_clif_type),
                    };

                    let left_val = resolve_operand(left_operand, ctx, final_left_type)?;
                    let right_val = resolve_operand(right_operand, ctx, final_right_type)?;

                    let result_val = match op {
                        BinaryIntOp::Add => ctx.builder.ins().iadd(left_val, right_val),
                        BinaryIntOp::Sub => ctx.builder.ins().isub(left_val, right_val),
                        BinaryIntOp::Mul => ctx.builder.ins().imul(left_val, right_val),
                        BinaryIntOp::Div => {
                            if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder.ins().sdiv(left_val, right_val)
                            } else {
                                ctx.builder.ins().udiv(left_val, right_val)
                            }
                        }
                        BinaryIntOp::Mod => {
                            if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder.ins().srem(left_val, right_val)
                            } else {
                                ctx.builder.ins().urem(left_val, right_val)
                            }
                        }
                        BinaryIntOp::BitAnd => ctx.builder.ins().band(left_val, right_val),
                        BinaryIntOp::BitOr => ctx.builder.ins().bor(left_val, right_val),
                        BinaryIntOp::BitXor => ctx.builder.ins().bxor(left_val, right_val),
                        BinaryIntOp::LShift => ctx.builder.ins().ishl(left_val, right_val),
                        BinaryIntOp::RShift => {
                            if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder.ins().sshr(left_val, right_val)
                            } else {
                                ctx.builder.ins().ushr(left_val, right_val)
                            }
                        }
                        BinaryIntOp::Eq => {
                            let cond = ctx.builder.ins().icmp(IntCC::Equal, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Ne => {
                            let cond = ctx.builder.ins().icmp(IntCC::NotEqual, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Lt => {
                            let cond = if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder.ins().icmp(IntCC::SignedLessThan, left_val, right_val)
                            } else {
                                ctx.builder.ins().icmp(IntCC::UnsignedLessThan, left_val, right_val)
                            };
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Le => {
                            let cond = if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder
                                    .ins()
                                    .icmp(IntCC::SignedLessThanOrEqual, left_val, right_val)
                            } else {
                                ctx.builder
                                    .ins()
                                    .icmp(IntCC::UnsignedLessThanOrEqual, left_val, right_val)
                            };
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Gt => {
                            let cond = if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder.ins().icmp(IntCC::SignedGreaterThan, left_val, right_val)
                            } else {
                                ctx.builder.ins().icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
                            };
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Ge => {
                            let cond = if is_operand_signed(left_operand, ctx.mir) {
                                ctx.builder
                                    .ins()
                                    .icmp(IntCC::SignedGreaterThanOrEqual, left_val, right_val)
                            } else {
                                ctx.builder
                                    .ins()
                                    .icmp(IntCC::UnsignedGreaterThanOrEqual, left_val, right_val)
                            };
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                    };
                    Ok(result_val)
                }
                Rvalue::BinaryFloatOp(op, left_operand, right_operand) => {
                    let left_cranelift_type = get_operand_clif_type(left_operand, ctx.mir)
                        .map_err(|e| format!("Failed to get left operand type: {}", e))?;
                    let right_cranelift_type = get_operand_clif_type(right_operand, ctx.mir)
                        .map_err(|e| format!("Failed to get right operand type: {}", e))?;

                    let left_val = resolve_operand(left_operand, ctx, left_cranelift_type)?;
                    let right_val = resolve_operand(right_operand, ctx, right_cranelift_type)?;

                    let result_val = match op {
                        BinaryFloatOp::Add => ctx.builder.ins().fadd(left_val, right_val),
                        BinaryFloatOp::Sub => ctx.builder.ins().fsub(left_val, right_val),
                        BinaryFloatOp::Mul => ctx.builder.ins().fmul(left_val, right_val),
                        BinaryFloatOp::Div => ctx.builder.ins().fdiv(left_val, right_val),
                        BinaryFloatOp::Eq => {
                            let cond = ctx.builder.ins().fcmp(FloatCC::Equal, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryFloatOp::Ne => {
                            let cond = ctx.builder.ins().fcmp(FloatCC::NotEqual, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryFloatOp::Lt => {
                            let cond = ctx.builder.ins().fcmp(FloatCC::LessThan, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryFloatOp::Le => {
                            let cond = ctx.builder.ins().fcmp(FloatCC::LessThanOrEqual, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryFloatOp::Gt => {
                            let cond = ctx.builder.ins().fcmp(FloatCC::GreaterThan, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryFloatOp::Ge => {
                            let cond = ctx.builder.ins().fcmp(FloatCC::GreaterThanOrEqual, left_val, right_val);
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                    };
                    Ok(result_val)
                }
                Rvalue::BuiltinVaArg(ap, type_id) => {
                    // X86_64 SysV va_arg implementation
                    // va_list is struct { gp_offset, fp_offset, overflow_arg_area, reg_save_area }
                    // For GP types: if gp_offset < 48, fetch from reg_save_area + gp_offset
                    //               else fetch from overflow_arg_area

                    let ap_addr = resolve_place_to_addr(ap, ctx)?;

                    // Load fields from va_list
                    let gp_offset = ctx.builder.ins().load(types::I32, MemFlags::new(), ap_addr, 0);
                    let _fp_offset = ctx.builder.ins().load(types::I32, MemFlags::new(), ap_addr, 4);
                    let _overflow_area = ctx.builder.ins().load(types::I64, MemFlags::new(), ap_addr, 8);
                    let reg_save_area = ctx.builder.ins().load(types::I64, MemFlags::new(), ap_addr, 16);

                    let mir_type = ctx.mir.get_type(*type_id);
                    let cl_type = convert_type(mir_type).unwrap_or(types::I64);

                    // Unified va_arg implementation for "Cendol" ABI (all args in spill_slot/reg_save_area)
                    // We ignore is_float and standard SystemV ABI register separation because our
                    // implementation flattens everything into a sequential spill slot pointed to by reg_save_area.

                    let size = mir_type_size(mir_type, ctx.mir)? as u32;
                    let size = size.max(8);

                    let needed_slots = size.div_ceil(8);
                    let needed_gp = needed_slots * 8;

                    // Address is always reg_save_area + gp_offset
                    let offset_64 = ctx.builder.ins().uextend(types::I64, gp_offset);
                    let addr = ctx.builder.ins().iadd(reg_save_area, offset_64);

                    let result = if mir_type.is_aggregate() {
                        addr // Return address for aggregates
                    } else {
                        ctx.builder.ins().load(cl_type, MemFlags::new(), addr, 0)
                    };

                    // Increment gp_offset
                    let next_gp_increment = ctx.builder.ins().iconst(types::I32, needed_gp as i64);
                    let next_gp = ctx.builder.ins().iadd(gp_offset, next_gp_increment);
                    ctx.builder.ins().store(MemFlags::new(), next_gp, ap_addr, 0);

                    // Sync overflow_area to point to the next slot (needed if we pass ap to standard functions like vprintf)
                    // overflow_area = reg_save_area + next_gp
                    let next_gp_64 = ctx.builder.ins().uextend(types::I64, next_gp);
                    let next_overflow = ctx.builder.ins().iadd(reg_save_area, next_gp_64);
                    ctx.builder.ins().store(MemFlags::new(), next_overflow, ap_addr, 8);
                    Ok(result)
                }
                Rvalue::ArrayLiteral(elements) => {
                    let dest_addr = resolve_place_to_addr(place, ctx)?;
                    let MirType::Array { element, layout, .. } = place_mir_type else {
                        return Err("ArrayLiteral with non-array type".to_string());
                    };
                    let element_mir_type = ctx.mir.get_type(*element);
                    let element_clif_type = convert_type(element_mir_type);
                    let stride = layout.stride as i64;

                    for (i, element_op) in elements.iter().enumerate() {
                        let offset = i as i64 * stride;
                        let element_dest_addr = if offset == 0 {
                            dest_addr
                        } else {
                            ctx.builder.ins().iadd_imm(dest_addr, offset)
                        };

                        if element_mir_type.is_aggregate() {
                            let src_addr = resolve_operand(element_op, ctx, types::I64)?;
                            let size = mir_type_size(element_mir_type, ctx.mir)? as i64;
                            emit_memcpy(element_dest_addr, src_addr, size, ctx.builder, ctx.module)?;
                        } else {
                            let val = resolve_operand(element_op, ctx, element_clif_type.unwrap())?;
                            ctx.builder.ins().store(MemFlags::new(), val, element_dest_addr, 0);
                        }
                    }
                    return Ok(());
                }
                Rvalue::StructLiteral(fields) => {
                    let dest_addr = resolve_place_to_addr(place, ctx)?;
                    let MirType::Record {
                        layout, field_types, ..
                    } = place_mir_type
                    else {
                        return Err("StructLiteral with non-record type".to_string());
                    };

                    for (field_idx, element_op) in fields.iter() {
                        let offset = layout.field_offsets[*field_idx] as i64;
                        let field_dest_addr = if offset == 0 {
                            dest_addr
                        } else {
                            ctx.builder.ins().iadd_imm(dest_addr, offset)
                        };

                        let field_mir_type = ctx.mir.get_type(field_types[*field_idx]);
                        if field_mir_type.is_aggregate() {
                            let src_addr = resolve_operand(element_op, ctx, types::I64)?;
                            let size = mir_type_size(field_mir_type, ctx.mir)? as i64;
                            emit_memcpy(field_dest_addr, src_addr, size, ctx.builder, ctx.module)?;
                        } else {
                            let field_clif_type = convert_type(field_mir_type).unwrap();
                            let val = resolve_operand(element_op, ctx, field_clif_type)?;
                            ctx.builder.ins().store(MemFlags::new(), val, field_dest_addr, 0);
                        }
                    }
                    return Ok(());
                }
                Rvalue::AtomicLoad(ptr, _order) => {
                    let ptr_val = resolve_operand(ptr, ctx, types::I64)?;
                    Ok(ctx.builder.ins().atomic_load(expected_type, MemFlags::new(), ptr_val))
                }
                Rvalue::AtomicExchange(ptr, val, _order) => {
                    let ptr_val = resolve_operand(ptr, ctx, types::I64)?;
                    let val_type = get_operand_clif_type(val, ctx.mir)?;
                    let val_op = resolve_operand(val, ctx, val_type)?;
                    Ok(ctx
                        .builder
                        .ins()
                        .atomic_rmw(expected_type, MemFlags::new(), AtomicRmwOp::Xchg, ptr_val, val_op))
                }
                Rvalue::AtomicCompareExchange(ptr, expected, desired, _, _, _) => {
                    let ptr_val = resolve_operand(ptr, ctx, types::I64)?;
                    let expected_val = resolve_operand(expected, ctx, expected_type)?;
                    let desired_val = resolve_operand(desired, ctx, expected_type)?;

                    Ok(ctx
                        .builder
                        .ins()
                        .atomic_cas(MemFlags::new(), ptr_val, expected_val, desired_val))
                }
                Rvalue::AtomicFetchOp(op, ptr, val, _order) => {
                    let ptr_val = resolve_operand(ptr, ctx, types::I64)?;
                    let val_type = get_operand_clif_type(val, ctx.mir)?;
                    let val_op = resolve_operand(val, ctx, val_type)?;

                    let rmw_op = match op {
                        BinaryIntOp::Add => AtomicRmwOp::Add,
                        BinaryIntOp::Sub => AtomicRmwOp::Sub,
                        BinaryIntOp::BitAnd => AtomicRmwOp::And,
                        BinaryIntOp::BitOr => AtomicRmwOp::Or,
                        BinaryIntOp::BitXor => AtomicRmwOp::Xor,
                        _ => return Err(format!("Unsupported atomic fetch op: {:?}", op)),
                    };

                    Ok(ctx
                        .builder
                        .ins()
                        .atomic_rmw(expected_type, MemFlags::new(), rmw_op, ptr_val, val_op))
                }
            };

            // Now, assign the resolved value to the place
            if let Ok(value) = rvalue_result {
                let place_type_id = get_place_type_id(place, ctx.mir);
                let mir_type = ctx.mir.get_type(place_type_id);

                if mir_type.is_aggregate() {
                    let dest_addr = resolve_place_to_addr(place, ctx)?;
                    let size = mir_type_size(mir_type, ctx.mir)? as i64;
                    emit_memcpy(dest_addr, value, size, ctx.builder, ctx.module)?;
                } else {
                    match place {
                        Place::Local(local_id) => {
                            // Check if this local has a stack slot (non-void types)
                            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                                ctx.builder.ins().stack_store(value, *stack_slot, 0);
                            }
                            // Else: This local doesn't have a stack slot (likely a void type)
                            // or it's optimized out. In MIR, we assume it's valid to ignore.
                        }
                        _ => {
                            // This covers StructField, ArrayIndex, Deref, and Global assignments
                            match resolve_place_to_addr(place, ctx) {
                                Ok(addr) => {
                                    ctx.builder.ins().store(MemFlags::new(), value, addr, 0);
                                }
                                Err(e) => return Err(format!("Failed to resolve place address: {}", e)),
                            }
                        }
                    }
                }
            } else {
                return Err(format!("Failed to resolve rvalue: {:?}", rvalue_result.err()));
            }
            Ok(())
        }

        MirStmt::Store(operand, place) => {
            // We need to determine the correct type for the operand
            let place_type_id = get_place_type_id(place, ctx.mir);
            let place_type = ctx.mir.get_type(place_type_id);
            let cranelift_type = convert_type(place_type).ok_or_else(|| "Cannot store to a void type".to_string())?;

            let value = resolve_operand(operand, ctx, cranelift_type)?;

            // Now, store the value into the place
            match place {
                Place::Local(local_id) => {
                    let stack_slot = ctx
                        .stack_slots
                        .get(local_id)
                        .ok_or_else(|| format!("Stack slot not found for local {}", local_id.get()))?;
                    ctx.builder.ins().stack_store(value, *stack_slot, 0);
                }
                _ => {
                    // For other places, resolve to an address and store
                    let addr = resolve_place_to_addr(place, ctx)?;
                    ctx.builder.ins().store(MemFlags::new(), value, addr, 0);
                }
            }
            Ok(())
        }
        MirStmt::Call { target, args, dest } => {
            if let Some(dest_place) = dest {
                // Call with destination - need to store the result
                let dest_type_id = get_place_type_id(dest_place, ctx.mir);
                let dest_mir_type = ctx.mir.get_type(dest_type_id);
                let expected_type = match convert_type(dest_mir_type) {
                    Some(t) => t,
                    None if dest_mir_type.is_aggregate() => types::I64,
                    None => return Err("Cannot assign to void type".to_string()),
                };
                let result = emit_function_call_impl(target, args, expected_type, ctx)?;

                // Store the result in the destination place
                let dest_mir_type = ctx.mir.get_type(dest_type_id);
                if dest_mir_type.is_aggregate() {
                    // For aggregate types, result is an address, memcpy to dest
                    let dest_addr = resolve_place_to_addr(dest_place, ctx)?;
                    let size = mir_type_size(dest_mir_type, ctx.mir)? as i64;
                    emit_memcpy(dest_addr, result, size, ctx.builder, ctx.module)?;
                } else {
                    match dest_place {
                        Place::Local(local_id) => {
                            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                                ctx.builder.ins().stack_store(result, *stack_slot, 0);
                            }
                        }
                        _ => {
                            let addr = resolve_place_to_addr(dest_place, ctx)?;
                            ctx.builder.ins().store(MemFlags::new(), result, addr, 0);
                        }
                    }
                }
            } else {
                // Call without destination - ignore return value (side-effect only)
                let _ = emit_function_call_impl(target, args, types::I32, ctx)?;
            }
            Ok(())
        }

        MirStmt::Alloc(place, type_id) => {
            // Get the size of the type to be allocated
            let alloc_type = ctx.mir.get_type(*type_id);
            let size = mir_type_size(alloc_type, ctx.mir)?;

            // Define the `malloc` function signature (size_t -> void*)
            // In Cranelift, this would be (i64) -> i64 for a 64-bit target
            let mut malloc_sig = Signature::new(ctx.builder.func.signature.call_conv);
            malloc_sig.params.push(AbiParam::new(types::I64));
            malloc_sig.returns.push(AbiParam::new(types::I64));

            // Declare `malloc` if not already declared
            let malloc_func = ctx
                .module
                .declare_function("malloc", Linkage::Import, &malloc_sig)
                .map_err(|e| format!("Failed to declare malloc: {:?}", e))?;
            let local_malloc = ctx.module.declare_func_in_func(malloc_func, ctx.builder.func);

            // Call `malloc` with the calculated size
            let size_val = ctx.builder.ins().iconst(types::I64, size as i64);
            let call_inst = ctx.builder.ins().call(local_malloc, &[size_val]);
            let alloc_ptr = ctx.builder.inst_results(call_inst)[0];

            // Store the returned pointer into the destination place
            match place {
                Place::Local(local_id) => {
                    if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                        ctx.builder.ins().stack_store(alloc_ptr, *stack_slot, 0);
                    }
                }
                _ => {
                    let addr = resolve_place_to_addr(place, ctx)?;
                    ctx.builder.ins().store(MemFlags::new(), alloc_ptr, addr, 0);
                }
            }
            Ok(())
        }

        MirStmt::Dealloc(operand) => {
            // Resolve the operand to get the pointer to be freed
            let ptr_val = resolve_operand(operand, ctx, types::I64)?;

            // Define the `free` function signature (void* -> void)
            let mut free_sig = Signature::new(ctx.builder.func.signature.call_conv);
            free_sig.params.push(AbiParam::new(types::I64));

            // Declare `free` if not already declared
            let free_func = ctx
                .module
                .declare_function("free", Linkage::Import, &free_sig)
                .map_err(|e| format!("Failed to declare free: {:?}", e))?;
            let local_free = ctx.module.declare_func_in_func(free_func, ctx.builder.func);

            // Call `free` with the pointer
            ctx.builder.ins().call(local_free, &[ptr_val]);
            Ok(())
        }
        MirStmt::BuiltinVaStart(place, _operand) => {
            let ap_addr = resolve_place_to_addr(place, ctx)?;

            if let Some(spill_slot) = ctx.va_spill_slot {
                let spill_addr = ctx.builder.ins().stack_addr(types::I64, spill_slot, 0);

                // 1. gp_offset
                // Calculate how many bytes are consumed by fixed parameters
                let fixed_count = ctx.func.params.len();
                let gp_val = fixed_count * 8;

                // Clamp to 48 (max GPR registers)
                let effective_gp = std::cmp::min(gp_val, 48);
                let gp_const = ctx.builder.ins().iconst(types::I32, effective_gp as i64);
                ctx.builder.ins().store(MemFlags::new(), gp_const, ap_addr, 0);

                // 2. fp_offset = 176 (unused as we map everything to I64 GPRs in current hack)
                let fp_val = ctx.builder.ins().iconst(types::I32, 176);
                ctx.builder.ins().store(MemFlags::new(), fp_val, ap_addr, 4);

                // 3. overflow_arg_area
                // If gp < 48, overflow starts at 48.
                // If gp >= 48, overflow starts at gp.
                let overflow_offset = std::cmp::max(gp_val, 48) as i64;
                let overflow_ptr = ctx.builder.ins().iadd_imm(spill_addr, overflow_offset);
                ctx.builder.ins().store(MemFlags::new(), overflow_ptr, ap_addr, 8);

                // 4. reg_save_area
                // Points to the start of spill slot where we saved all params
                ctx.builder.ins().store(MemFlags::new(), spill_addr, ap_addr, 16);
            } else {
                // Fallback (should not happen for variadic functions)
                let zero = ctx.builder.ins().iconst(types::I64, 0);
                ctx.builder.ins().store(MemFlags::new(), zero, ap_addr, 8); // overflow
                ctx.builder.ins().store(MemFlags::new(), zero, ap_addr, 16); // reg_save
            }

            Ok(())
        }
        MirStmt::AtomicStore(ptr, val, _order) => {
            let ptr_val = resolve_operand(ptr, ctx, types::I64)?;
            let val_type = get_operand_clif_type(val, ctx.mir)?;
            let val_op = resolve_operand(val, ctx, val_type)?;

            ctx.builder.ins().atomic_store(MemFlags::new(), val_op, ptr_val);
            Ok(())
        }
        MirStmt::BuiltinVaEnd(_place) => {
            // No-op for x86_64
            Ok(())
        }
        MirStmt::BuiltinVaCopy(dest, src) => {
            let dest_addr = resolve_place_to_addr(dest, ctx)?;
            let src_addr = resolve_place_to_addr(src, ctx)?;
            // va_list is 24 bytes on x86_64
            emit_memcpy(dest_addr, src_addr, 24, ctx.builder, ctx.module)?;
            Ok(())
        }
    }
}

/// Helper to lower a terminator
fn lower_terminator(terminator: &Terminator, ctx: &mut BodyEmitContext) -> Result<(), String> {
    match terminator {
        Terminator::Goto(target) => {
            let target_cl_block = ctx
                .clif_blocks
                .get(target)
                .ok_or_else(|| format!("Target block {} not found", target.get()))?;
            ctx.builder.ins().jump(*target_cl_block, &[]);
            ctx.worklist.push(*target);
        }

        Terminator::If(cond, then_bb, else_bb) => {
            let cond_val = resolve_operand(cond, ctx, types::I32)?;

            let then_cl_block = ctx
                .clif_blocks
                .get(then_bb)
                .ok_or_else(|| format!("'Then' block {} not found", then_bb.get()))?;
            let else_cl_block = ctx
                .clif_blocks
                .get(else_bb)
                .ok_or_else(|| format!("'Else' block {} not found", else_bb.get()))?;

            ctx.builder
                .ins()
                .brif(cond_val, *then_cl_block, &[], *else_cl_block, &[]);

            ctx.worklist.push(*then_bb);
            ctx.worklist.push(*else_bb);
        }

        Terminator::Return(opt) => {
            if let Some(operand) = opt {
                if let Some(ret_type) = ctx.return_type {
                    let return_value = resolve_operand(operand, ctx, ret_type)?;
                    ctx.builder.ins().return_(&[return_value]);
                } else {
                    return Err("Returning a value from a void function".to_string());
                }
            } else {
                ctx.builder.ins().return_(&[]);
            }
        }

        Terminator::Unreachable => {
            // For unreachable, default to appropriate return based on function type
            if let Some(ret_type) = ctx.return_type {
                let return_value = ctx.builder.ins().iconst(ret_type, 0i64);
                ctx.builder.ins().return_(&[return_value]);
            } else {
                // Void function
                ctx.builder.ins().return_(&[]);
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
        None if return_mir_type.is_aggregate() => Some(types::I64),
        None => None, // Void
    };

    // Add parameters from MIR function signature
    let mut param_types = Vec::new();
    for &param_id in &func.params {
        let param_local = mir.get_local(param_id);
        let mir_type = mir.get_type(param_local.type_id);

        if matches!(mir_type, MirType::F80 | MirType::F128) {
            // Split F128/F80 into 2 I64s for internal ABI
            func_ctx.params.push(AbiParam::new(types::I64));
            func_ctx.params.push(AbiParam::new(types::I64));
            // Track them as F128 in param_types for lower_function to know,
            // OR track split types? lower_function iterates MIR params.
            // It needs to know it consumes 2 slots.
            // We push F128 to param_types so lower_function knows the logic type.
            // BUT setup_signature return type `Vec<Type>` is used by lower_function
            // to append_block_param.
            // So we must push I64, I64 to param_types.
            param_types.push(types::I64);
            param_types.push(types::I64);
            continue;
        }

        let param_type = match convert_type(mir_type) {
            Some(t) => t,
            None if mir_type.is_aggregate() => types::I64,
            None => return Err(format!("Unsupported parameter type for local {}", param_id.get())),
        };
        func_ctx.params.push(AbiParam::new(param_type));
        param_types.push(param_type);
    }

    if func.is_variadic && matches!(func.kind, MirFunctionKind::Defined) {
        // Add 32 total I64 parameters to capture variadic arguments (6 GPRs + 26 stack slots)
        // This allows variadic functions to receive many struct args that expand to multiple I64s
        let fixed_params_count = func.params.len();
        let total_variadic_slots = 32; // Support up to 32 I64 slots for variadic args
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
    let linkage = convert_linkage(func.kind);

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

    triple: Triple,
    set_al_func: Option<FuncId>,
}

/// NOTE: we use panic!() to ICE because codegen rely on correct MIR, so if we give invalid MIR, then problem is in previous phase
impl MirToCraneliftLowerer {
    pub(crate) fn new(mir: MirProgram) -> Self {
        let triple = Triple::host();
        let mut flag_builder = cranelift::prelude::settings::builder();
        flag_builder.set("is_pic", "true").unwrap();
        let builder = ObjectBuilder::new(
            cranelift::prelude::isa::lookup(triple.clone())
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
            triple,
            set_al_func: None,
        }
    }

    pub(crate) fn compile_module(mut self, emit_kind: EmitKind) -> Result<ClifOutput, String> {
        self.emit_kind = emit_kind;

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
            let linkage = convert_linkage(func.kind);

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
                let mut initial_value_bytes = Vec::new();
                // Enable relocations by passing data_description and maps
                let ctx = EmitContext {
                    mir: &self.mir,
                    func_id_map: &self.func_id_map,
                    data_id_map: &self.data_id_map,
                };
                emit_const(
                    const_id,
                    &mut initial_value_bytes,
                    &ctx,
                    Some(&mut self.module),
                    Some(&mut data_description),
                    0,
                )?;

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
                self.lower_function(func_id)?;
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
                    let total_variadic_slots = 32; // Must match setup_signature
                    if fixed_param_count < total_variadic_slots {
                        let extra_count = total_variadic_slots - fixed_param_count;
                        for _ in 0..extra_count {
                            builder.append_block_param(*clif_block, types::I64);
                        }
                    }
                }

                // Step 3: NOW emit instructions - store fixed params to stack slots
                let param_values: Vec<Value> = builder.block_params(*clif_block).to_vec();
                let mut param_iter = param_values.iter().copied();

                for &param_id in &func.params {
                    let local = self.mir.get_local(param_id);
                    let mir_type = self.mir.get_type(local.type_id);

                    if matches!(mir_type, MirType::F80 | MirType::F128) {
                        // Consumes 2 slots
                        let lo = param_iter.next().unwrap();
                        let hi = param_iter.next().unwrap();

                        if let Some(stack_slot) = self.clif_stack_slots.get(&param_id) {
                            builder.ins().stack_store(lo, *stack_slot, 0);
                            builder.ins().stack_store(hi, *stack_slot, 8);
                        }
                        continue;
                    }

                    let param_value = param_iter.next().unwrap();
                    if let Some(stack_slot) = self.clif_stack_slots.get(&param_id) {
                        if mir_type.is_aggregate() {
                            // Passed by pointer (I64), copy to stack slot
                            let dest_addr = builder.ins().stack_addr(types::I64, *stack_slot, 0);
                            let size = mir_type_size(mir_type, &self.mir)? as i64;
                            emit_memcpy(dest_addr, param_value, size, &mut builder, &mut self.module)?;
                        } else {
                            builder.ins().stack_store(param_value, *stack_slot, 0);
                        }
                    }
                }

                // Step 4: Handle variadic spill area - save all 32 slots
                if func.is_variadic {
                    let total_slots = 32;
                    let spill_size = total_slots * 8; // 256 bytes for 32 I64 slots
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

            let mut ctx = BodyEmitContext {
                builder: &mut builder,
                mir: &self.mir,
                stack_slots: &self.clif_stack_slots,
                module: &mut self.module,
                va_spill_slot,
                func,
                clif_blocks: &clif_blocks,
                worklist: &mut worklist,
                return_type: return_type_opt,
                func_id_map: &self.func_id_map,
                triple: &self.triple,
                set_al_func: &mut self.set_al_func,
            };

            // Process statements
            for stmt in &statements_to_process {
                lower_statement(stmt, &mut ctx)?;
            }

            // ========================================================================
            // SECTION 2: Process terminator (control flow)
            // ========================================================================
            lower_terminator(&mir_block.terminator, &mut ctx)?;

            va_spill_slot = ctx.va_spill_slot;
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

/// Internal helper for variadic calls on x86_64 SysV
fn emit_cendol_set_al(module: &mut ObjectModule) -> Result<FuncId, String> {
    let mut sig = Signature::new(cranelift::codegen::isa::CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // count
    sig.params.push(AbiParam::new(types::I64)); // addr
    sig.returns.push(AbiParam::new(types::I64)); // count (RAX)
    sig.returns.push(AbiParam::new(types::I64)); // addr (RDX)

    let func_id = module
        .declare_function("__cendol_set_al", Linkage::Export, &sig)
        .map_err(|e| format!("Failed to declare __cendol_set_al: {:?}", e))?;

    let mut ctx = cranelift::codegen::Context::new();
    ctx.func.signature = sig;

    let mut func_ctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut ctx.func, &mut func_ctx);

    let block = builder.create_block();
    builder.append_block_params_for_function_params(block);
    builder.switch_to_block(block);
    builder.seal_block(block);

    let count = builder.block_params(block)[0];
    let addr = builder.block_params(block)[1];
    builder.ins().return_(&[count, addr]);

    builder.finalize();

    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| format!("Failed to define __cendol_set_al: {:?}", e))?;

    Ok(func_id)
}
