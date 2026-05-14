//! MIR to Cranelift IR lowering module
//!
//! This module provides the mechanical translation from MIR to Cranelift IR.
//! The translation follows these rules:
//! - No C logic
//! - Assume MIR is valid

use crate::mir::MirProgram;
use crate::mir::{
    BinaryFloatOp, BinaryIntOp, CallTarget, ConstValueId, ConstValueKind, GlobalId, LocalId, MirBlockId, MirFunction,
    MirFunctionId, MirLinkage, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId, UnaryFloatOp, UnaryIntOp,
};
use cranelift::codegen::ir::{ArgumentPurpose, AtomicRmwOp, Inst, StackSlot, StackSlotData, StackSlotKind};
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
pub(crate) enum EmitKind {
    Object,
    Clif,
}

pub(crate) enum ClifOutput {
    ObjectFile(Vec<u8>),
    ClifDump(String),
}

/// Helper function to convert MIR type to Cranelift type
/// Returns None for void types, as they don't have a representation in Cranelift
fn lower_type(mir_type: &MirType) -> Option<Type> {
    match mir_type {
        MirType::Void => None,
        MirType::Bool => Some(types::I8), // Booleans as i8 (standard C)

        MirType::I8 | MirType::U8 => Some(types::I8),
        MirType::I16 | MirType::U16 => Some(types::I16),
        MirType::I32 | MirType::U32 => Some(types::I32),
        MirType::I64 | MirType::U64 => Some(types::I64),
        MirType::F32 => Some(types::F32),
        MirType::F64 => Some(types::F64),
        MirType::F80 | MirType::F128 => None, // Treat as aggregate for ABI/bits
        MirType::Pointer { .. } => Some(types::I64), // Pointers are 64-bit on most modern systems

        MirType::Array { .. } | MirType::Record { .. } => None,
        MirType::Function { .. } => Some(types::I64), // Function pointers
    }
}

/// Helper function to convert MIR linkage to Cranelift linkage
fn lower_mir_linkage(linkage: MirLinkage) -> Linkage {
    match linkage {
        MirLinkage::Internal => Linkage::Local,
        MirLinkage::External => Linkage::Export,
        MirLinkage::Import => Linkage::Import,
    }
}

/// Helper function to get the size of a MIR type in bytes
fn lower_type_size(mir_type: &MirType, mir: &MirProgram) -> u32 {
    match mir_type {
        MirType::I8 | MirType::U8 => 1,
        MirType::I16 | MirType::U16 => 2,
        MirType::I32 | MirType::U32 => 4,
        MirType::I64 | MirType::U64 => 8,
        MirType::F32 => 4,
        MirType::F64 => 8,
        MirType::F80 | MirType::F128 => 16,

        MirType::Pointer { .. } => mir.pointer_width as u32,
        MirType::Array { layout, .. } => layout.size as u32,
        MirType::Record { layout, .. } => layout.size as u32,
        MirType::Bool => 1,
        MirType::Void => 0,
        _ => 4, // Default size for other types
    }
}

/// Helper function to get the alignment of a MIR type in bytes
fn lower_type_alignment(mir_type: &MirType, _mir: &MirProgram) -> u64 {
    match mir_type {
        MirType::I8 | MirType::U8 | MirType::Bool => 1,
        MirType::I16 | MirType::U16 => 2,
        MirType::I32 | MirType::U32 | MirType::F32 => 4,
        MirType::I64 | MirType::U64 | MirType::F64 | MirType::Pointer { .. } | MirType::Function { .. } => 8,
        MirType::F80 | MirType::F128 => 16,
        MirType::Record { layout, .. } => layout.align as u64,
        MirType::Array { layout, .. } => layout.align as u64,
        MirType::Void => 1,
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
    pub return_types: Vec<Type>,
    pub return_ptr: Option<Value>,
    pub va_spill_slot: Option<StackSlot>,
    pub func: &'a MirFunction,
    pub func_id_map: &'a HashMap<MirFunctionId, FuncId>,
    pub data_id_map: &'a HashMap<GlobalId, DataId>,
    pub triple: &'a Triple,
    pub vararg_count_data: &'a mut Option<DataId>,
    pub vararg_target_data: &'a mut Option<DataId>,
    pub vararg_trampoline_func: &'a mut Option<FuncId>,
    pub pointee_to_pointer: &'a HashMap<TypeId, TypeId>,
    pub use_variadic_hack: bool,
    pub fixed_params_count: usize,
}

/// Context for lowering call signatures
pub(crate) struct SignatureLoweringContext<'a> {
    pub mir: &'a MirProgram,
    pub pointee_to_pointer: &'a HashMap<TypeId, TypeId>,
}

/// Helper to emit integer constants
fn emit_const_int(val: i64, layout: &MirType, output: &mut Vec<u8>) {
    match layout {
        MirType::I8 | MirType::U8 => output.extend_from_slice(&(val as u8).to_le_bytes()),
        MirType::I16 | MirType::U16 => output.extend_from_slice(&(val as u16).to_le_bytes()),
        MirType::I32 | MirType::U32 => output.extend_from_slice(&(val as u32).to_le_bytes()),
        MirType::I64 | MirType::U64 => output.extend_from_slice(&(val as u64).to_le_bytes()),
        MirType::Bool => output.push(if val != 0 { 1u8 } else { 0u8 }),
        MirType::Pointer { .. } => output.extend_from_slice(&(val as u64).to_le_bytes()),
        _ => output.extend_from_slice(&(val as u32).to_le_bytes()),
    }
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
fn emit_const_float(val: f64, ty: &MirType, output: &mut Vec<u8>) {
    match ty {
        MirType::F32 => output.extend_from_slice(&(val as f32).to_bits().to_le_bytes()),
        MirType::F64 => output.extend_from_slice(&val.to_bits().to_le_bytes()),
        MirType::F80 => output.extend_from_slice(&f64_to_x87_bytes(val)),
        MirType::F128 => output.extend_from_slice(&f64_to_f128_bytes(val)),
        _ => output.extend_from_slice(&val.to_bits().to_le_bytes()),
    }
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
) {
    let MirType::Record {
        layout: record_layout, ..
    } = ty
    else {
        panic!("StructLiteral with non-record type");
    };

    // Initialize the entire struct with zeros
    let mut struct_bytes = vec![0u8; record_layout.size as usize];

    // Emit each field at its proper offset
    for (field_index, field_const_id) in fields {
        if let Some(field_layout) = record_layout.fields.get(*field_index) {
            let field_offset = field_layout.offset as usize;

            let mut field_bytes = Vec::new();
            emit_const(
                *field_const_id,
                &mut field_bytes,
                ctx,
                reborrow_module(&mut module),
                reborrow_data_description(&mut data_description),
                base_offset + field_offset as u32,
            );

            // Copy the field bytes into the struct buffer, resizing if necessary
            let required_size = field_offset + field_bytes.len();
            if required_size > struct_bytes.len() {
                struct_bytes.resize(required_size, 0);
            }

            if let Some(bit_width) = field_layout.bit_width {
                let bit_offset = field_layout.bit_offset.unwrap_or(0);

                // Pack bitfield into the storage unit.
                let mut val = 0u64;
                for (i, &b) in field_bytes.iter().enumerate().take(8) {
                    val |= (b as u64) << (i * 8);
                }

                let mask = if bit_width == 64 { !0 } else { (1u64 << bit_width) - 1 };
                let packed_val = (val & mask) << bit_offset;
                let full_mask = mask << bit_offset;

                for (i, byte) in struct_bytes[field_offset..]
                    .iter_mut()
                    .enumerate()
                    .take(field_bytes.len())
                {
                    let byte_mask = (full_mask >> (i * 8)) as u8;
                    let byte_val = (packed_val >> (i * 8)) as u8;
                    *byte = (*byte & !byte_mask) | byte_val;
                }
            } else {
                struct_bytes[field_offset..field_offset + field_bytes.len()].copy_from_slice(&field_bytes);
            }
        }
    }
    output.extend_from_slice(&struct_bytes);
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
) {
    let MirType::Array {
        element,
        size,
        layout: array_layout,
    } = ty
    else {
        panic!("ArrayLiteral with non-array type");
    };

    let element_type = ctx.mir.get_type(*element);
    let element_size = lower_type_size(element_type, ctx.mir) as usize;
    let stride = array_layout.stride as usize;
    let padding = stride.saturating_sub(element_size);

    let limit = if *size == 0 { elements.len() } else { *size };

    for (i, element_const_id) in elements.iter().take(limit).enumerate() {
        let element_offset = (i * stride) as u32;

        emit_const(
            *element_const_id,
            output,
            ctx,
            reborrow_module(&mut module),
            reborrow_data_description(&mut data_description),
            base_offset + element_offset,
        );

        if padding > 0 {
            output.extend(std::iter::repeat_n(0, padding));
        }
    }

    // Fill remaining space with zeros if array is partially initialized
    let count = elements.len().min(limit);
    let emitted_size = count * stride;
    let total_size = (array_layout.size as usize).max(emitted_size);

    if emitted_size < total_size {
        let remaining = total_size - emitted_size;
        output.extend(std::iter::repeat_n(0, remaining));
    }
}

/// Emit a constant value to the output buffer based on its type layout
fn emit_const(
    const_id: ConstValueId,
    output: &mut Vec<u8>,
    ctx: &EmitContext,
    mut module: Option<&mut ObjectModule>,
    mut data_description: Option<&mut DataDescription>,
    offset: u32,
) {
    let const_value = ctx.mir.get_constant(const_id);
    let ty = ctx.mir.get_type(const_value.ty);

    match &const_value.kind {
        ConstValueKind::Int(val) => emit_const_int(*val, ty, output),
        ConstValueKind::Float(val) => emit_const_float(*val, ty, output),
        ConstValueKind::Bool(val) => output.push(if *val { 1u8 } else { 0u8 }),
        ConstValueKind::Null => output.extend_from_slice(&0u64.to_le_bytes()),
        ConstValueKind::Zero => output.extend(std::iter::repeat_n(0, lower_type_size(ty, ctx.mir) as usize)),
        ConstValueKind::GlobalAddress(global_id, addend) => {
            if let (Some(dd), Some(mod_obj)) = (&mut data_description, &mut module) {
                let data_id = *ctx
                    .data_id_map
                    .get(global_id)
                    .unwrap_or_else(|| panic!("Global ID {} not found in map during relocation", global_id.get()));
                let global_val = mod_obj.declare_data_in_data(data_id, dd);
                dd.write_data_addr(offset, global_val, *addend);
            }
            output.extend_from_slice(&0u64.to_le_bytes());
        }
        ConstValueKind::FunctionAddress(func_id) => {
            if let (Some(dd), Some(mod_obj)) = (&mut data_description, &mut module)
                && let Some(&clif_func_id) = ctx.func_id_map.get(func_id)
            {
                let func_ref = mod_obj.declare_func_in_data(clif_func_id, dd);
                dd.write_function_addr(offset, func_ref);
            }
            output.extend_from_slice(&0i64.to_le_bytes());
        }
        ConstValueKind::StructLiteral(fields) => {
            emit_const_struct(fields, ty, output, ctx, module, data_description, offset);
        }
        ConstValueKind::ArrayLiteral(elements) => {
            emit_const_array(elements, ty, output, ctx, module, data_description, offset);
        }
    }
}

fn reborrow_module<'b>(m: &'b mut Option<&mut ObjectModule>) -> Option<&'b mut ObjectModule> {
    m.as_mut().map(|inner| &mut **inner)
}

fn reborrow_data_description<'b>(dd: &'b mut Option<&mut DataDescription>) -> Option<&'b mut DataDescription> {
    dd.as_mut().map(|inner| &mut **inner)
}

/// Helper to determine if a type should be packed into registers (I64)
/// Returns Some(count) of I64 registers needed (max 2)
fn get_struct_packing(mir_type: &MirType, mir: &MirProgram) -> Option<Vec<Type>> {
    match mir_type {
        MirType::Record {
            layout, field_types, ..
        } if layout.size > 0 && layout.size <= 16 => {
            let count = layout.size.div_ceil(8);
            if field_types.iter().all(|&ft| {
                let ft_mir = mir.get_type(ft);
                matches!(ft_mir, MirType::F32 | MirType::F64)
            }) {
                Some(vec![types::F64; count as usize])
            } else {
                Some(vec![types::I64; count as usize])
            }
        }
        _ => None,
    }
}

fn lower_abi_param(
    mir_type: &MirType,
    mir: &MirProgram,
    sig: &mut Signature,
    param_types: &mut Vec<Type>,
    split_f128: bool,
) {
    if !split_f128 && let Some(types_list) = get_struct_packing(mir_type, mir) {
        for &t in &types_list {
            sig.params.push(AbiParam::new(t));
            param_types.push(t);
        }
        return;
    }

    // MEMORY class (stack) for large aggregates or long double
    // Only used for external calls (use_variadic_hack=false).
    // Internal calls pad the signature and expand into I64 registers.
    let size = lower_type_size(mir_type, mir);
    if !split_f128 && (size > 16 || matches!(mir_type, MirType::F80 | MirType::F128)) {
        let aligned_size = (size + 7) & !7;
        sig.params.push(AbiParam::special(
            types::I64,
            ArgumentPurpose::StructArgument(aligned_size),
        ));
        param_types.push(types::I64);
        return;
    }

    let t = match lower_type(mir_type) {
        Some(t) => t,
        None if mir_type.is_aggregate() => {
            // Expanding small struct into multiple I64 regs
            let size = lower_type_size(mir_type, mir);
            let num_slots = size.div_ceil(8);
            for _ in 0..num_slots {
                sig.params.push(AbiParam::new(types::I64));
                param_types.push(types::I64);
            }
            return;
        }
        None => types::I32,
    };

    // If using the variadic hack (padded signature), everything must be I64
    // to match the 128-parameter trampoline signature.
    let t = if split_f128 && !mir_type.is_aggregate() {
        types::I64
    } else {
        t
    };

    sig.params.push(AbiParam::new(t));
    param_types.push(t);
}

fn lower_abi_return(mir_type: &MirType, mir: &MirProgram, sig: &mut Signature, return_types: &mut Vec<Type>) -> bool {
    if let Some(types_list) = get_struct_packing(mir_type, mir) {
        for &t in &types_list {
            sig.returns.push(AbiParam::new(t));
            return_types.push(t);
        }
        return false;
    }

    if let Some(t) = lower_type(mir_type) {
        sig.returns.push(AbiParam::new(t));
        return_types.push(t);
        return false;
    }

    if mir_type.is_aggregate() {
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        return_types.push(types::I64);
        return true;
    }

    false
}

/// Helper to prepare a function signature for a call
fn lower_call_signature(
    call_conv: cranelift::codegen::isa::CallConv,
    return_type_id: TypeId,
    param_types: &[TypeId],
    args: &[Operand],
    is_variadic: bool,
    use_variadic_hack: bool,
    padded: bool,
    ctx: &SignatureLoweringContext,
) -> (Signature, bool) {
    let mut sig = Signature::new(call_conv);
    let mut return_types = Vec::new();
    let has_hidden_ptr = lower_abi_return(ctx.mir.get_type(return_type_id), ctx.mir, &mut sig, &mut return_types);

    let mut actual_param_types = Vec::new();
    if has_hidden_ptr {
        actual_param_types.push(types::I64);
    }

    for &param_type_id in param_types {
        lower_abi_param(
            ctx.mir.get_type(param_type_id),
            ctx.mir,
            &mut sig,
            &mut actual_param_types,
            use_variadic_hack,
        );
    }

    for arg in args.iter().skip(param_types.len()) {
        let arg_type_id = lower_operand_type_id(arg, ctx.mir, ctx.pointee_to_pointer);
        lower_abi_param(
            ctx.mir.get_type(arg_type_id),
            ctx.mir,
            &mut sig,
            &mut actual_param_types,
            use_variadic_hack,
        );
    }

    if is_variadic && padded {
        while sig.params.len() < 128 {
            sig.params.push(AbiParam::new(types::I64));
        }
    }

    (sig, has_hidden_ptr)
}

/// Helper to resolve arguments for a call, handling variadic struct expansion if needed
fn emit_call_args(
    args: &[Operand],
    fixed_param_count: usize,
    sig: &Signature,
    ctx: &mut BodyEmitContext,
    split_f128: bool,
    start_sig_idx: usize,
) -> Vec<Value> {
    let mut arg_values = Vec::new();
    let mut sig_idx = start_sig_idx;

    // Count usage (future expansion)

    for (arg_idx, arg) in args.iter().enumerate() {
        if sig_idx >= sig.params.len() {
            break;
        }

        // Check operand type
        let arg_type_id = Some(lower_operand_type_id(arg, ctx.mir, ctx.pointee_to_pointer));

        // Check for struct packing in fixed parameters
        if arg_idx < fixed_param_count
            && let Some(type_id) = arg_type_id
            && let Some(types_list) = get_struct_packing(ctx.mir.get_type(type_id), ctx.mir)
        {
            // Resolve struct to address
            let struct_addr = emit_operand(arg, ctx, types::I64);
            let size = lower_type_size(ctx.mir.get_type(type_id), ctx.mir);

            for (i, &t) in types_list.iter().enumerate() {
                // If it's the last chunk, we might need partial load
                let offset = (i * 8) as i32;
                let remaining = size.saturating_sub((i * 8) as u32);

                let val = if remaining >= 8 {
                    ctx.builder.ins().load(t, MemFlags::new(), struct_addr, offset)
                } else {
                    let current_val = emit_partial_load(ctx.builder, struct_addr, offset, remaining);
                    if t.is_float() {
                        ctx.builder.ins().bitcast(t, MemFlags::new(), current_val)
                    } else {
                        current_val
                    }
                };
                arg_values.push(val);
                sig_idx += 1;
            }
            continue;
        }

        let type_id = lower_operand_type_id(arg, ctx.mir, ctx.pointee_to_pointer);
        let mir_type = ctx.mir.get_type(type_id);

        // A. Handle aggregates (structs/unions/long-double)
        if mir_type.is_aggregate() {
            let struct_addr = emit_operand(arg, ctx, types::I64);
            let size = lower_type_size(mir_type, ctx.mir);

            // 1. Memory class (large aggregates or long double)
            // For external calls (split_f128=false), use StructArgument (stack).
            if !split_f128 && (size > 16 || matches!(mir_type, MirType::F80 | MirType::F128)) {
                arg_values.push(struct_addr);
                sig_idx += 1;
                continue;
            }

            // 2. Small aggregates in registers (Standard SysV or Internal hack)
            let num_slots = size.div_ceil(8) as usize;
            let types_list = if !split_f128 {
                get_struct_packing(mir_type, ctx.mir)
            } else {
                None
            };

            for slot in 0..num_slots {
                if sig_idx < sig.params.len() {
                    let offset = (slot * 8) as i32;
                    let remaining_bytes = size as usize - (slot * 8);
                    let cl_type = types_list
                        .as_ref()
                        .and_then(|l| l.get(slot).cloned())
                        .unwrap_or(types::I64);

                    let value = if remaining_bytes >= 8 {
                        ctx.builder.ins().load(cl_type, MemFlags::new(), struct_addr, offset)
                    } else {
                        let partial = emit_partial_load(ctx.builder, struct_addr, offset, remaining_bytes as u32);
                        if cl_type != types::I64 {
                            ctx.builder.ins().bitcast(cl_type, MemFlags::new(), partial)
                        } else {
                            partial
                        }
                    };
                    arg_values.push(value);
                    sig_idx += 1;
                }
            }
            continue;
        }

        // C. Handle variadic aggregates for hack (pass by pointer)
        if mir_type.is_aggregate() && split_f128 {
            let addr = emit_operand(arg, ctx, types::I64);
            arg_values.push(addr);
            sig_idx += 1;
            continue;
        }

        // Update param_type as sig_idx might have changed
        if sig_idx >= sig.params.len() {
            break;
        }
        let param_type = sig.params[sig_idx].value_type;

        // Non-struct argument (or fixed param)
        let value = emit_operand(arg, ctx, param_type);
        arg_values.push(value);
        sig_idx += 1;
    }

    // Padding for remaining signature params (variadic slot padding SysV x86_64 hack)
    while sig_idx < sig.params.len() {
        let param_type = sig.params[sig_idx].value_type;
        arg_values.push(ctx.builder.ins().iconst(param_type, 0i64));
        sig_idx += 1;
    }

    arg_values
}

/// Helper to get the result of a call, or a zero constant if it has no return value
fn get_call_result(ctx: &mut BodyEmitContext, call_inst: Inst, return_type_id: TypeId) -> Value {
    let results: Vec<Value> = ctx.builder.inst_results(call_inst).to_vec();
    let mir_type = ctx.mir.get_type(return_type_id);

    if let Some(types_list) = get_struct_packing(mir_type, ctx.mir) {
        // Results are packed into multiple registers. Store them to a temporary stack slot.
        let size = lower_type_size(mir_type, ctx.mir);
        let slot = ctx
            .builder
            .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, size, 3)); // 8-byte aligned

        for (i, _) in types_list.iter().enumerate() {
            let val = results[i];
            let offset = (i * 8) as i32;
            ctx.builder.ins().stack_store(val, slot, offset);
        }

        return ctx.builder.ins().stack_addr(types::I64, slot, 0);
    }

    if results.is_empty() {
        let clif_type = lower_type(mir_type).unwrap_or(types::I32);
        ctx.builder.ins().iconst(clif_type, 0i64)
    } else {
        // results[0] could be the hidden pointer for large aggregates,
        // or the direct result for small types.
        results[0]
    }
}

fn emit_function_call(call_target: &CallTarget, args: &[Operand], ctx: &mut BodyEmitContext) -> Value {
    // 1. Determine function properties and callee address if indirect/variadic
    let (return_type_id, param_types, is_variadic, name_linkage, target_addr, use_variadic_hack) = match call_target {
        CallTarget::Direct(func_id) => {
            let func = ctx.mir.get_function(*func_id);
            let param_types: Vec<TypeId> = func.params.iter().map(|&p| ctx.mir.get_local(p).type_id).collect();
            let name_linkage = Some((func.name, func.linkage));
            let is_defined = func.linkage != MirLinkage::Import;
            (
                func.return_type,
                param_types,
                func.is_variadic,
                name_linkage,
                None,
                func.is_variadic && is_defined && ctx.triple.architecture == target_lexicon::Architecture::X86_64,
            )
        }
        CallTarget::Indirect(func_operand) => {
            let func_ptr_type_id = lower_operand_type_id(func_operand, ctx.mir, ctx.pointee_to_pointer);
            let func_ptr_type = ctx.mir.get_type(func_ptr_type_id);

            let ((return_type_id, param_types), is_function_type, is_variadic_call) = match func_ptr_type {
                MirType::Pointer { pointee } => match ctx.mir.get_type(*pointee) {
                    MirType::Function {
                        return_type,
                        params,
                        is_variadic,
                    } => ((*return_type, params.clone()), false, *is_variadic),
                    _ => panic!("Indirect call operand points to non-function type"),
                },
                MirType::Function {
                    return_type,
                    params,
                    is_variadic,
                } => ((*return_type, params.clone()), true, *is_variadic),
                _ => panic!("Indirect call operand is not a pointer"),
            };

            let callee_val = if is_function_type {
                match func_operand {
                    Operand::Copy(place) => emit_place_addr(place, ctx),
                    _ => emit_operand(func_operand, ctx, types::I64),
                }
            } else {
                emit_operand(func_operand, ctx, types::I64)
            };

            (
                return_type_id,
                param_types,
                is_variadic_call,
                None,
                Some(callee_val),
                is_variadic_call && ctx.triple.architecture == target_lexicon::Architecture::X86_64,
            )
        }
    };

    // 2. Prepare call site signature and resolve arguments
    let lower_ctx = SignatureLoweringContext {
        mir: ctx.mir,
        pointee_to_pointer: ctx.pointee_to_pointer,
    };

    let (sig, has_hidden_ptr) = lower_call_signature(
        ctx.builder.func.signature.call_conv,
        return_type_id,
        &param_types,
        args,
        is_variadic,
        use_variadic_hack,
        use_variadic_hack, // padded if hack is used
        &lower_ctx,
    );

    let mut start_sig_idx = 0;
    let mut arg_values = Vec::new();

    if has_hidden_ptr {
        // Allocate space for the large return value
        let return_mir_type = ctx.mir.get_type(return_type_id);
        let size = lower_type_size(return_mir_type, ctx.mir);
        let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, size, 3); // 8-byte aligned
        let slot = ctx.builder.create_sized_stack_slot(slot_data);
        let addr = ctx.builder.ins().stack_addr(types::I64, slot, 0);
        arg_values.push(addr);
        start_sig_idx = 1;
    }

    let split_f128 = use_variadic_hack;
    let other_arg_values = emit_call_args(args, param_types.len(), &sig, ctx, split_f128, start_sig_idx);
    arg_values.extend(other_arg_values);

    // 3. Emit the call
    let call_inst = if is_variadic {
        if let Some((name, linkage)) = name_linkage {
            // Variadic direct calls must be indirect to use the custom signature
            let (canonical_sig, _) = lower_call_signature(
                ctx.builder.func.signature.call_conv,
                return_type_id,
                &param_types,
                &[],
                is_variadic,
                use_variadic_hack,
                linkage != MirLinkage::Import && ctx.triple.architecture == target_lexicon::Architecture::X86_64,
                &lower_ctx,
            );
            let decl = ctx
                .module
                .declare_function(name.as_str(), lower_mir_linkage(linkage), &canonical_sig)
                .expect("Failed to declare variadic function");
            let func_ref = ctx.module.declare_func_in_func(decl, ctx.builder.func);
            let addr = ctx.builder.ins().func_addr(types::I64, func_ref);
            let sig_ref = ctx.builder.import_signature(sig);

            let addr = emit_al_count_and_pass_addr(args, &param_types, addr, use_variadic_hack, ctx);

            ctx.builder.ins().call_indirect(sig_ref, addr, &arg_values)
        } else if let Some(addr) = target_addr {
            let sig_ref = ctx.builder.import_signature(sig);
            let addr = emit_al_count_and_pass_addr(args, &param_types, addr, use_variadic_hack, ctx);
            ctx.builder.ins().call_indirect(sig_ref, addr, &arg_values)
        } else {
            panic!("Variadic call without target");
        }
    } else if let Some(addr) = target_addr {
        let sig_ref = ctx.builder.import_signature(sig);
        ctx.builder.ins().call_indirect(sig_ref, addr, &arg_values)
    } else {
        // Direct non-variadic call
        let (name, linkage) = name_linkage.unwrap();
        let decl = ctx
            .module
            .declare_function(name.as_str(), lower_mir_linkage(linkage), &sig)
            .expect("Failed to declare function");
        let func_ref = ctx.module.declare_func_in_func(decl, ctx.builder.func);
        ctx.builder.ins().call(func_ref, &arg_values)
    };

    get_call_result(ctx, call_inst, return_type_id)
}

/// Helper function to convert boolean to integer (0 or 1)
fn emit_al_count_and_pass_addr(
    args: &[Operand],
    param_types: &[TypeId],
    addr: Value,
    use_variadic_hack: bool,
    ctx: &mut BodyEmitContext,
) -> Value {
    if ctx.triple.architecture == target_lexicon::Architecture::X86_64
        && ctx.builder.func.signature.call_conv == cranelift::codegen::isa::CallConv::SystemV
    {
        let mut fp_arg_count = 0;
        if !use_variadic_hack {
            for (i, arg) in args.iter().enumerate() {
                if i >= param_types.len() {
                    let arg_mir_type = ctx
                        .mir
                        .get_type(lower_operand_type_id(arg, ctx.mir, ctx.pointee_to_pointer));
                    if matches!(arg_mir_type, MirType::F32 | MirType::F64) {
                        fp_arg_count += 1;
                    }
                }
            }
        }

        let fp_arg_count = fp_arg_count.min(8);

        if ctx.vararg_count_data.is_none() {
            *ctx.vararg_count_data = Some(
                ctx.module
                    .declare_data("__cendol_vararg_al_count", Linkage::Import, true, false)
                    .unwrap(),
            );
            *ctx.vararg_target_data = Some(
                ctx.module
                    .declare_data("__cendol_vararg_target_addr", Linkage::Import, true, false)
                    .unwrap(),
            );
            let dummy_sig = Signature::new(cranelift::codegen::isa::CallConv::SystemV);
            *ctx.vararg_trampoline_func = Some(
                ctx.module
                    .declare_function("__cendol_vararg_trampoline", Linkage::Import, &dummy_sig)
                    .unwrap(),
            );
        }

        let count_data_id = ctx.vararg_count_data.unwrap();
        let target_data_id = ctx.vararg_target_data.unwrap();
        let tramp_func_id = ctx.vararg_trampoline_func.unwrap();

        let count_global = ctx.module.declare_data_in_func(count_data_id, ctx.builder.func);
        let count_addr = ctx.builder.ins().global_value(types::I64, count_global);
        let count_val = ctx.builder.ins().iconst(types::I64, fp_arg_count as i64);
        ctx.builder.ins().store(MemFlags::trusted(), count_val, count_addr, 0);

        let target_global = ctx.module.declare_data_in_func(target_data_id, ctx.builder.func);
        let target_addr_val = ctx.builder.ins().global_value(types::I64, target_global);
        ctx.builder.ins().store(MemFlags::trusted(), addr, target_addr_val, 0);

        let tramp_func_ref = ctx.module.declare_func_in_func(tramp_func_id, ctx.builder.func);
        ctx.builder.ins().func_addr(types::I64, tramp_func_ref)
    } else {
        addr
    }
}

fn emit_bool_to_int(val: Value, target_type: Type, builder: &mut FunctionBuilder) -> Value {
    let one = builder.ins().iconst(target_type, 1);
    let zero = builder.ins().iconst(target_type, 0i64);
    builder.ins().select(val, one, zero)
}

/// Helper function to emit a memcpy call
fn emit_memcpy(dest: Value, src: Value, size: i64, builder: &mut FunctionBuilder, module: &mut ObjectModule) {
    let mut sig = Signature::new(builder.func.signature.call_conv);
    sig.params.push(AbiParam::new(types::I64)); // dest
    sig.params.push(AbiParam::new(types::I64)); // src
    sig.params.push(AbiParam::new(types::I64)); // size
    sig.returns.push(AbiParam::new(types::I64)); // returns dest (ignored)

    let callee = module
        .declare_function("memcpy", Linkage::Import, &sig)
        .expect("Failed to declare memcpy");
    let local_callee = module.declare_func_in_func(callee, builder.func);

    let size_val = builder.ins().iconst(types::I64, size);
    builder.ins().call(local_callee, &[dest, src, size_val]);
}

/// Helper function to emit a memset call
fn emit_memset(dest: Value, val: i8, size: i64, builder: &mut FunctionBuilder, module: &mut ObjectModule) {
    let mut sig = Signature::new(builder.func.signature.call_conv);
    sig.params.push(AbiParam::new(types::I64)); // dest
    sig.params.push(AbiParam::new(types::I32)); // val
    sig.params.push(AbiParam::new(types::I64)); // size
    sig.returns.push(AbiParam::new(types::I64)); // returns dest (ignored)

    let callee = module
        .declare_function("memset", Linkage::Import, &sig)
        .expect("Failed to declare memset");
    let local_callee = module.declare_func_in_func(callee, builder.func);

    let val_val = builder.ins().iconst(types::I32, val as i64);
    let size_val = builder.ins().iconst(types::I64, size);
    builder.ins().call(local_callee, &[dest, val_val, size_val]);
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
                builder.ins().fcvt_to_sint_sat(types::I32, val)
            } else {
                builder.ins().fcvt_to_uint_sat(types::I32, val)
            };
            return builder.ins().ireduce(to, intermediate);
        }

        return if is_signed {
            builder.ins().fcvt_to_sint_sat(to, val)
        } else {
            builder.ins().fcvt_to_uint_sat(to, val)
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

/// Helper to convert a 16-byte x87 80-bit float (in memory) to a Cranelift F64 value.
/// This is used as a workaround since Cranelift x64 backend lacks native F128/F80 support.
fn emit_x87_to_f64(addr: Value, builder: &mut FunctionBuilder) -> Value {
    let lo = builder.ins().load(types::I64, MemFlags::new(), addr, 0);
    let hi = builder.ins().load(types::I64, MemFlags::new(), addr, 8);

    // x87 lo (8 bytes): Mantissa with explicit integer bit at 63
    // x87 hi (bits 0..14): Exponent (15-bit, 16383 bias)
    // x87 hi (bit 15): Sign

    let sign = builder.ins().ushr_imm(hi, 15);
    let sign = builder.ins().band_imm(sign, 1);
    let sign_f64 = builder.ins().ishl_imm(sign, 63);

    let exp_x87 = builder.ins().band_imm(hi, 0x7FFF);
    // f64_exp = exp_x87 - 16383 + 1023 = exp_x87 - 15360
    // Handle Special Values (NaN, Inf) where exp_x87 == 0x7FFF
    let is_special = builder.ins().icmp_imm(IntCC::Equal, exp_x87, 0x7FFF);
    let exp_f64_normal = builder.ins().iadd_imm(exp_x87, -15360);
    let exp_f64_special = builder.ins().iconst(types::I64, 0x7FF);
    let exp_f64 = builder.ins().select(is_special, exp_f64_special, exp_f64_normal);
    let exp_f64_clamped = builder.ins().ishl_imm(exp_f64, 52);

    // Mantissa: drop the explicit integer bit (bit 63) and shift to 52 bits
    let mant_x87_no_int = builder.ins().band_imm(lo, 0x7FFF_FFFF_FFFF_FFFF);
    let mant_f64 = builder.ins().ushr_imm(mant_x87_no_int, 11);
    let mant_f64_masked = builder.ins().band_imm(mant_f64, 0x000F_FFFF_FFFF_FFFF);

    let res_i64 = builder.ins().bor(sign_f64, exp_f64_clamped);
    let res_i64 = builder.ins().bor(res_i64, mant_f64_masked);

    builder.ins().bitcast(types::F64, MemFlags::new(), res_i64)
}

/// Helper to convert a Cranelift F64 value to a 16-byte x87 80-bit float format and store it.
fn emit_f64_to_x87(val: Value, addr: Value, builder: &mut FunctionBuilder) {
    // Zero the entire 16 bytes first to avoid garbage in padding (ABI requirement)
    let zero64 = builder.ins().iconst(types::I64, 0);
    builder.ins().store(MemFlags::new(), zero64, addr, 0);
    builder.ins().store(MemFlags::new(), zero64, addr, 8);

    let val_i64 = builder.ins().bitcast(types::I64, MemFlags::new(), val);

    let sign = builder.ins().ushr_imm(val_i64, 63);
    let exp_f64 = builder.ins().ushr_imm(val_i64, 52);
    let exp_f64 = builder.ins().band_imm(exp_f64, 0x7FF);
    let mant_f64 = builder.ins().band_imm(val_i64, 0x000F_FFFF_FFFF_FFFF);

    // x87_exp = exp_f64 - 1023 + 16383 = exp_f64 + 15360
    // Handle Special Values (NaN, Inf) where exp_f64 == 0x7FF
    let is_special = builder.ins().icmp_imm(IntCC::Equal, exp_f64, 0x7FF);
    let exp_x87_normal = builder.ins().iadd_imm(exp_f64, 15360);
    let exp_x87_special = builder.ins().iconst(types::I64, 0x7FFF);
    let exp_x87 = builder.ins().select(is_special, exp_x87_special, exp_x87_normal);
    let hi = builder.ins().ishl_imm(sign, 15);
    let hi = builder.ins().bor(hi, exp_x87);

    // x87_mant = (mant_f64 << 11) | explicit_integer_bit
    let mant_x87 = builder.ins().ishl_imm(mant_f64, 11);
    // Fixed: only set integer bit if exponent is not zero (simplified normal handling)
    let is_not_zero = builder.ins().icmp_imm(IntCC::NotEqual, exp_f64, 0);
    let iconst8 = builder.ins().iconst(types::I64, 1 << 63);
    let iconst0 = builder.ins().iconst(types::I64, 0);
    let integer_bit = builder.ins().select(is_not_zero, iconst8, iconst0);
    let mant_x87 = builder.ins().bor(mant_x87, integer_bit);

    builder.ins().store(MemFlags::new(), mant_x87, addr, 0);
    builder.ins().store(MemFlags::new(), hi, addr, 8);
    // Clear the rest of the 16-byte slot (padding to 16 bytes for ABI)
    let zero = builder.ins().iconst(types::I16, 0);
    builder.ins().store(MemFlags::new(), zero, addr, 10);
}

/// Helper to emit a constant to anonymous memory and return its address
fn emit_constant_to_memory(const_id: ConstValueId, ctx: &mut BodyEmitContext) -> Value {
    let const_value = ctx.mir.get_constant(const_id);
    let ty = ctx.mir.get_type(const_value.ty);
    let size = lower_type_size(ty, ctx.mir) as usize;

    let mut data_description = DataDescription::new();

    if let ConstValueKind::Zero = const_value.kind {
        data_description.define_zeroinit(size);
    } else {
        let mut bytes = Vec::with_capacity(size);
        let emit_ctx = EmitContext {
            mir: ctx.mir,
            func_id_map: ctx.func_id_map,
            data_id_map: ctx.data_id_map,
        };

        emit_const(
            const_id,
            &mut bytes,
            &emit_ctx,
            Some(&mut *ctx.module),
            Some(&mut data_description),
            0,
        );

        data_description.define(bytes.into_boxed_slice());
    }

    let data_id = ctx
        .module
        .declare_anonymous_data(false, false)
        .expect("Failed to declare anonymous data");

    ctx.module
        .define_data(data_id, &data_description)
        .expect("Failed to define anonymous data");

    let global_val = ctx.module.declare_data_in_func(data_id, ctx.builder.func);
    ctx.builder.ins().global_value(types::I64, global_val)
}

fn truncate_const(val: i64, ty: Type) -> i64 {
    match ty {
        types::I8 => (val as i8) as i64,
        types::I16 => (val as i16) as i64,
        types::I32 => (val as i32) as i64,
        types::I64 => val,
        _ => val,
    }
}

/// Helper function to resolve a MIR operand to a Cranelift value
fn emit_operand(operand: &Operand, ctx: &mut BodyEmitContext, expected_type: Type) -> Value {
    match operand {
        Operand::Constant(const_id) => {
            let const_value = ctx.mir.get_constant(*const_id);
            match &const_value.kind {
                ConstValueKind::Int(val) => {
                    let val = *val;
                    if expected_type.is_float() {
                        if expected_type == types::F64 {
                            ctx.builder.ins().f64const(val as f64)
                        } else if expected_type == types::F32 {
                            ctx.builder.ins().f32const(val as f32)
                        } else {
                            // F128 or other float types - might need better handling but for now fallback to f64 logic or panic
                            panic!("Implicit int-to-float constant conversion for type {:?}", expected_type);
                        }
                    } else {
                        let truncated = truncate_const(val, expected_type);
                        ctx.builder.ins().iconst(expected_type, truncated)
                    }
                }
                ConstValueKind::Float(val) => {
                    let val = *val;
                    let mir_type = ctx.mir.get_type(const_value.ty);
                    if mir_type.is_aggregate() {
                        let addr = emit_constant_to_memory(*const_id, ctx);
                        if expected_type == types::I64 {
                            return addr;
                        } else if matches!(mir_type, MirType::F80 | MirType::F128) && expected_type.is_float() {
                            return emit_x87_to_f64(addr, ctx.builder);
                        } else {
                            return ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0);
                        }
                    }

                    if expected_type == types::I64 {
                        let bits = val.to_bits();
                        ctx.builder.ins().iconst(types::I64, bits as i64)
                    } else if expected_type.is_int() {
                        let int_val = val as i64;
                        let truncated = truncate_const(int_val, expected_type);
                        ctx.builder.ins().iconst(expected_type, truncated)
                    } else if expected_type == types::F64 {
                        ctx.builder.ins().f64const(val)
                    } else if expected_type == types::F32 {
                        ctx.builder.ins().f32const(val as f32)
                    } else {
                        // Fallback/Default for float constants
                        ctx.builder.ins().f32const(val as f32)
                    }
                }
                ConstValueKind::Bool(val) => {
                    let int_val = if *val { 1 } else { 0 };
                    ctx.builder.ins().iconst(expected_type, int_val as i64)
                }
                ConstValueKind::Null => ctx.builder.ins().iconst(expected_type, 0i64),
                ConstValueKind::GlobalAddress(global_id, addend) => {
                    let global_id = *global_id;
                    let addend = *addend;
                    let global = ctx.mir.get_global(global_id);
                    let linkage = lower_mir_linkage(global.linkage);
                    let global_val = ctx
                        .module
                        .declare_data(global.name.as_str(), linkage, true, global.is_tls)
                        .expect("Failed to declare global data");
                    let local_id = ctx.module.declare_data_in_func(global_val, ctx.builder.func);
                    let addr = ctx.builder.ins().global_value(types::I64, local_id);
                    let addr = if addend != 0 {
                        let addend_val = ctx.builder.ins().iconst(types::I64, addend);
                        ctx.builder.ins().iadd(addr, addend_val)
                    } else {
                        addr
                    };
                    emit_type_conversion(addr, types::I64, expected_type, false, ctx.builder)
                }
                ConstValueKind::FunctionAddress(func_id) => {
                    let clif_func_id = *ctx
                        .func_id_map
                        .get(func_id)
                        .unwrap_or_else(|| panic!("Function ID {} not found in map", func_id.get()));
                    let func_ref = ctx.module.declare_func_in_func(clif_func_id, ctx.builder.func);
                    let addr = ctx.builder.ins().func_addr(types::I64, func_ref);
                    emit_type_conversion(addr, types::I64, expected_type, false, ctx.builder)
                }
                ConstValueKind::ArrayLiteral(_) | ConstValueKind::StructLiteral(_) => {
                    emit_constant_to_memory(*const_id, ctx)
                }
                _ => {
                    let mir_type = ctx.mir.get_type(const_value.ty);
                    if mir_type.is_aggregate() {
                        emit_constant_to_memory(*const_id, ctx)
                    } else {
                        ctx.builder.ins().iconst(expected_type, 0i64)
                    }
                }
            }
        }
        Operand::Copy(place) => {
            let place_type_id = lower_place_type_id(place, ctx.mir, ctx.pointee_to_pointer);
            let place_type = ctx.mir.get_type(place_type_id);

            if place_type.is_aggregate() {
                let addr = emit_place_addr(place, ctx);
                // For long double types (which are aggregates in MIR), if we expect a float value, load it
                if expected_type.is_float() && place_type.is_float() {
                    if matches!(place_type, MirType::F80 | MirType::F128) {
                        return emit_x87_to_f64(addr, ctx.builder);
                    }
                    return ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0);
                }
                return emit_type_conversion(addr, types::I64, expected_type, false, ctx.builder);
            }

            let place_clif_type =
                lower_type(place_type).unwrap_or_else(|| panic!("Unsupported place type: {:?}", place_type));

            let val = emit_place(place, ctx, place_clif_type);
            emit_type_conversion(val, place_clif_type, expected_type, place_type.is_signed(), ctx.builder)
        }
        Operand::Cast(type_id, inner_operand) => {
            let inner_mir_type =
                ctx.mir
                    .get_type(lower_operand_type_id(inner_operand, ctx.mir, ctx.pointee_to_pointer));
            let inner_type = if matches!(inner_mir_type, MirType::F80 | MirType::F128) {
                types::F64
            } else {
                lower_operand_type(inner_operand, ctx.mir, ctx.pointee_to_pointer)
            };
            let inner_val = emit_operand(inner_operand, ctx, inner_type);

            let mir_type = ctx.mir.get_type(*type_id);
            let target_type = if matches!(mir_type, MirType::F80 | MirType::F128) {
                types::F64
            } else if let Some(t) = lower_type(mir_type) {
                t
            } else {
                // If we can't lower the target type (e.g. void, array, record),
                // just return the inner value. This is safe for void casts because
                // the result is never used, and for other cases it avoids a panic.
                return inner_val;
            };

            let converted = if matches!(mir_type, MirType::Bool) && (inner_type.is_int() || inner_type.is_float()) {
                let zero = if inner_type.is_int() {
                    ctx.builder.ins().iconst(inner_type, 0i64)
                } else if inner_type == types::F32 {
                    ctx.builder.ins().f32const(0.0)
                } else if inner_type == types::F64 {
                    ctx.builder.ins().f64const(0.0)
                } else {
                    panic!("Unsupported float type");
                };
                let is_not_zero = if inner_type.is_int() {
                    ctx.builder.ins().icmp(IntCC::NotEqual, inner_val, zero)
                } else {
                    ctx.builder.ins().fcmp(FloatCC::NotEqual, inner_val, zero)
                };
                emit_bool_to_int(is_not_zero, target_type, ctx.builder)
            } else {
                emit_type_conversion(
                    inner_val,
                    inner_type,
                    target_type,
                    if inner_type.is_float() {
                        mir_type.is_signed()
                    } else {
                        is_operand_signed(inner_operand, ctx.mir, ctx.pointee_to_pointer)
                    },
                    ctx.builder,
                )
            };
            emit_type_conversion(converted, target_type, expected_type, mir_type.is_signed(), ctx.builder)
        }
        Operand::AddressOf(place) => {
            let addr = emit_place_addr(place, ctx);
            emit_type_conversion(addr, types::I64, expected_type, false, ctx.builder)
        }
    }
}

/// Helper function to resolve a MIR place to a Cranelift value
fn emit_place(place: &Place, ctx: &mut BodyEmitContext, expected_type: Type) -> Value {
    match place {
        Place::Local(local_id) => {
            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                ctx.builder.ins().stack_load(expected_type, *stack_slot, 0)
            } else {
                ctx.builder.ins().iconst(expected_type, 0)
            }
        }
        Place::Global(_global_id) => {
            let addr = emit_place_addr(place, ctx);
            ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0)
        }
        Place::Deref(operand) => {
            let addr = emit_operand(operand, ctx, types::I64);
            ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0)
        }
        Place::StructField(base_place, field_index, bit_info) => {
            let addr = emit_place_addr(&Place::StructField(base_place.clone(), *field_index, *bit_info), ctx);
            let raw_val = ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0);

            if let Some(info) = bit_info {
                let bits = expected_type.bits() as i64;
                let left_shift = bits - (info.offset + info.width) as i64;
                let right_shift = bits - info.width as i64;

                let mut val = raw_val;
                if left_shift > 0 {
                    val = ctx.builder.ins().ishl_imm(val, left_shift);
                }
                if right_shift > 0 {
                    if info.is_signed {
                        val = ctx.builder.ins().sshr_imm(val, right_shift);
                    } else {
                        val = ctx.builder.ins().ushr_imm(val, right_shift);
                    }
                }
                val
            } else {
                raw_val
            }
        }
        Place::ArrayIndex(base_place, index_operand) => {
            let addr = emit_place_addr(&Place::ArrayIndex(base_place.clone(), index_operand.clone()), ctx);
            ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0)
        }
    }
}

/// Helper function to get the Cranelift Type of an operand
fn lower_operand_type(operand: &Operand, mir: &MirProgram, pointee_to_pointer: &HashMap<TypeId, TypeId>) -> Type {
    if let Operand::AddressOf(_) = operand {
        return types::I64;
    }
    let type_id = lower_operand_type_id(operand, mir, pointee_to_pointer);
    let mir_type = mir.get_type(type_id);

    if let Some(clif_type) = lower_type(mir_type) {
        return clif_type;
    }

    if mir_type.is_aggregate() {
        return types::I64;
    }

    // Fallback for types that lower_type returns None for but aren't aggregates (shoudn't happen with valid MIR)
    types::I32
}

/// Helper function to check if a MIR type is signed
fn is_operand_signed(operand: &Operand, mir: &MirProgram, pointee_to_pointer: &HashMap<TypeId, TypeId>) -> bool {
    if let Operand::AddressOf(_) = operand {
        return false;
    }
    let type_id = lower_operand_type_id(operand, mir, pointee_to_pointer);
    mir.get_type(type_id).is_signed()
}

/// Helper function to resolve an operand to its TypeId
fn lower_operand_type_id(operand: &Operand, mir: &MirProgram, pointee_to_pointer: &HashMap<TypeId, TypeId>) -> TypeId {
    match operand {
        Operand::Constant(const_id) => mir.get_constant(*const_id).ty,
        Operand::Copy(place) => lower_place_type_id(place, mir, pointee_to_pointer),
        Operand::Cast(type_id, _) => *type_id,
        Operand::AddressOf(place) => {
            let place_type_id = lower_place_type_id(place, mir, pointee_to_pointer);
            pointee_to_pointer.get(&place_type_id).copied().unwrap_or_else(|| {
                // Fallback: If no specific pointer type exists, return the first available pointer type
                // or the pointee_type itself as a hack (since this is only for signature/ABI which treat all pointers as I64)
                pointee_to_pointer.values().next().copied().unwrap_or(place_type_id)
            })
        }
    }
}

/// Helper function to get the TypeId of a place
fn lower_place_type_id(place: &Place, mir: &MirProgram, pointee_to_pointer: &HashMap<TypeId, TypeId>) -> TypeId {
    match place {
        Place::Local(local_id) => mir.get_local(*local_id).type_id,
        Place::Global(global_id) => mir.get_global(*global_id).type_id,
        Place::Deref(operand) => {
            let operand_type_id = lower_operand_type_id(operand, mir, pointee_to_pointer);
            match mir.get_type(operand_type_id) {
                MirType::Pointer { pointee } => *pointee,
                _ => panic!("Cannot determine type for deref operand"),
            }
        }
        Place::StructField(base_place, field_index, _) => {
            let base_type_id = lower_place_type_id(base_place, mir, pointee_to_pointer);
            let base_type = mir.get_type(base_type_id);
            let record_type = if let MirType::Pointer { pointee } = base_type {
                mir.get_type(*pointee)
            } else {
                base_type
            };

            if let MirType::Record { field_types, .. } = record_type {
                return *field_types.get(*field_index).expect("Field index out of bounds");
            }
            panic!("Base of StructField is not a struct type");
        }
        Place::ArrayIndex(base_place, _) => {
            let base_type_id = lower_place_type_id(base_place, mir, pointee_to_pointer);
            match mir.get_type(base_type_id) {
                MirType::Array { element, .. } => *element,
                MirType::Pointer { pointee } => *pointee,
                _ => panic!("Base of ArrayIndex is not an array or pointer"),
            }
        }
    }
}

/// Helper function to resolve a MIR place to a memory address
fn emit_place_addr(place: &Place, ctx: &mut BodyEmitContext) -> Value {
    match place {
        Place::Local(local_id) => {
            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                ctx.builder.ins().stack_addr(types::I64, *stack_slot, 0)
            } else {
                ctx.builder.ins().iconst(types::I64, 0)
            }
        }
        Place::Global(global_id) => {
            let global = ctx.mir.get_global(*global_id);
            let linkage = lower_mir_linkage(global.linkage);
            let global_val = ctx
                .module
                .declare_data(global.name.as_str(), linkage, true, global.is_tls)
                .expect("Failed to declare global data");
            let local_id = ctx.module.declare_data_in_func(global_val, ctx.builder.func);
            ctx.builder.ins().global_value(types::I64, local_id)
        }
        Place::Deref(operand) => emit_operand(operand, ctx, types::I64),
        Place::StructField(base_place, field_index, _) => {
            let (final_base_addr, base_type_id) = lower_base_addr(base_place, ctx);
            let MirType::Record { layout, .. } = ctx.mir.get_type(base_type_id) else {
                panic!("Base of StructField is not a struct type");
            };
            let field_offset = layout.fields[*field_index].offset;
            ctx.builder.ins().iadd_imm(final_base_addr, field_offset as i64)
        }
        Place::ArrayIndex(base_place, index_operand) => {
            let (final_base_addr, base_type_id) = lower_base_addr(base_place, ctx);
            let index_val = emit_operand(index_operand, ctx, types::I64);

            let mir_type = ctx.mir.get_type(base_type_id);
            let element_size = match mir_type {
                MirType::Array { layout, .. } => layout.stride as u32,
                _ => lower_type_size(mir_type, ctx.mir),
            };

            let offset = if element_size > 1 {
                let element_size_val = ctx.builder.ins().iconst(types::I64, element_size as i64);
                ctx.builder.ins().imul(index_val, element_size_val)
            } else {
                index_val
            };
            ctx.builder.ins().iadd(final_base_addr, offset)
        }
    }
}

fn lower_base_addr(base_place: &Place, ctx: &mut BodyEmitContext) -> (Value, TypeId) {
    let base_addr = emit_place_addr(base_place, ctx);
    let base_type_id = lower_place_type_id(base_place, ctx.mir, ctx.pointee_to_pointer);
    let base_type = ctx.mir.get_type(base_type_id);

    if let MirType::Pointer { pointee } = base_type {
        let loaded_ptr = ctx.builder.ins().load(types::I64, MemFlags::new(), base_addr, 0);
        (loaded_ptr, *pointee)
    } else {
        (base_addr, base_type_id)
    }
}

fn emit_partial_load(builder: &mut FunctionBuilder, addr: Value, offset: i32, count: u32) -> Value {
    let mut current_val = builder.ins().iconst(types::I64, 0);
    for b in 0..count {
        let byte_val = builder.ins().load(types::I8, MemFlags::new(), addr, offset + b as i32);
        let byte_ext = builder.ins().uextend(types::I64, byte_val);
        let shift_amt = (b * 8) as i64;
        let shifted = builder.ins().ishl_imm(byte_ext, shift_amt);
        current_val = builder.ins().bor(current_val, shifted);
    }
    current_val
}

fn emit_partial_store(builder: &mut FunctionBuilder, val: Value, addr: Value, offset: i32, count: u32) {
    for b in 0..count {
        let shift_amt = (b * 8) as i64;
        let shifted = if shift_amt > 0 {
            builder.ins().ushr_imm(val, shift_amt)
        } else {
            val
        };
        let byte_val = builder.ins().ireduce(types::I8, shifted);
        builder.ins().store(MemFlags::new(), byte_val, addr, offset + b as i32);
    }
}

fn lower_atomic_rmw(
    ptr: &Operand,
    val: &Operand,
    op: AtomicRmwOp,
    expected_type: Type,
    ctx: &mut BodyEmitContext,
) -> Value {
    let ptr_val = emit_operand(ptr, ctx, types::I64);
    let val_type = lower_operand_type(val, ctx.mir, ctx.pointee_to_pointer);
    let val_op = emit_operand(val, ctx, val_type);
    ctx.builder
        .ins()
        .atomic_rmw(expected_type, MemFlags::new(), op, ptr_val, val_op)
}

fn emit_struct_literal(fields: &[(usize, Operand)], dest_addr: Value, type_id: TypeId, ctx: &mut BodyEmitContext) {
    let MirType::Record {
        layout, field_types, ..
    } = ctx.mir.get_type(type_id)
    else {
        panic!("StructLiteral type is not a record");
    };

    // Zero-initialize the entire struct first to ensure uninitialized members are zero
    let struct_size = layout.size as i64;
    emit_memset(dest_addr, 0, struct_size, ctx.builder, ctx.module);

    for (field_idx, element_op) in fields.iter() {
        let offset = layout.fields[*field_idx].offset as i64;
        let field_dest_addr = if offset == 0 {
            dest_addr
        } else {
            ctx.builder.ins().iadd_imm(dest_addr, offset)
        };

        let field_mir_type = ctx.mir.get_type(field_types[*field_idx]);
        if field_mir_type.is_aggregate() {
            let src_addr = emit_operand(element_op, ctx, types::I64);
            let size = lower_type_size(field_mir_type, ctx.mir) as i64;
            emit_memcpy(field_dest_addr, src_addr, size, ctx.builder, ctx.module);
        } else {
            let field_clif_type = lower_type(field_mir_type).unwrap();
            let val = emit_operand(element_op, ctx, field_clif_type);

            let field_layout = &layout.fields[*field_idx];
            if let Some(bit_width) = field_layout.bit_width {
                let bit_offset = field_layout.bit_offset.unwrap_or(0);
                // RMW for bitfield in struct literal initialization
                let original = ctx
                    .builder
                    .ins()
                    .load(field_clif_type, MemFlags::new(), field_dest_addr, 0);
                let mask = if bit_width == 64 {
                    !0u64
                } else {
                    (1u64 << bit_width) - 1
                };
                let bit_mask = mask << bit_offset;

                let masked_original = ctx.builder.ins().band_imm(original, !(bit_mask as i64));
                let masked_new = ctx.builder.ins().band_imm(val, mask as i64);
                let shifted_new = ctx.builder.ins().ishl_imm(masked_new, bit_offset as i64);
                let final_val = ctx.builder.ins().bor(masked_original, shifted_new);

                ctx.builder.ins().store(MemFlags::new(), final_val, field_dest_addr, 0);
            } else {
                ctx.builder.ins().store(MemFlags::new(), val, field_dest_addr, 0);
            }
        }
    }
}

fn emit_array_literal(elements: &[Operand], dest_addr: Value, type_id: TypeId, ctx: &mut BodyEmitContext) {
    let MirType::Array {
        element: element_type_id,
        layout,
        ..
    } = ctx.mir.get_type(type_id)
    else {
        panic!("ArrayLiteral type is not an array");
    };

    let element_mir_type = ctx.mir.get_type(*element_type_id);
    let element_clif_type = lower_type(element_mir_type);
    let stride = layout.stride as i64;

    for (i, element_op) in elements.iter().enumerate() {
        let offset = i as i64 * stride;
        let element_dest_addr = if offset == 0 {
            dest_addr
        } else {
            ctx.builder.ins().iadd_imm(dest_addr, offset)
        };

        if element_mir_type.is_aggregate() {
            let src_addr = emit_operand(element_op, ctx, types::I64);
            let size = lower_type_size(element_mir_type, ctx.mir) as i64;
            emit_memcpy(element_dest_addr, src_addr, size, ctx.builder, ctx.module);
        } else {
            let val = emit_operand(element_op, ctx, element_clif_type.unwrap());
            ctx.builder.ins().store(MemFlags::new(), val, element_dest_addr, 0);
        }
    }
}

fn lower_ptr_arith(base: &Operand, offset: &Operand, is_add: bool, ctx: &mut BodyEmitContext) -> Value {
    let base_type_id = lower_operand_type_id(base, ctx.mir, ctx.pointee_to_pointer);
    let MirType::Pointer { pointee } = ctx.mir.get_type(base_type_id) else {
        panic!("Pointer arithmetic base is not a pointer type");
    };

    let pointee_type = ctx.mir.get_type(*pointee);
    let pointee_size = lower_type_size(pointee_type, ctx.mir);

    let base_val = emit_operand(base, ctx, types::I64);
    let offset_val = emit_operand(offset, ctx, types::I64);

    let scaled_offset = if pointee_size > 1 {
        let size_val = ctx.builder.ins().iconst(types::I64, pointee_size as i64);
        ctx.builder.ins().imul(offset_val, size_val)
    } else {
        offset_val
    };

    if is_add {
        ctx.builder.ins().iadd(base_val, scaled_offset)
    } else {
        ctx.builder.ins().isub(base_val, scaled_offset)
    }
}
/// Helper function to store a value to a MIR place
fn emit_place_store(place: &Place, value: Value, expected_type: Type, ctx: &mut BodyEmitContext) {
    let place_type_id = lower_place_type_id(place, ctx.mir, ctx.pointee_to_pointer);
    let place_mir_type = ctx.mir.get_type(place_type_id);

    match place {
        Place::Local(local_id) => {
            if let Some(stack_slot) = ctx.stack_slots.get(local_id) {
                if matches!(place_mir_type, MirType::F80 | MirType::F128) && expected_type == types::F64 {
                    let addr = ctx.builder.ins().stack_addr(types::I64, *stack_slot, 0);
                    emit_f64_to_x87(value, addr, ctx.builder);
                } else {
                    ctx.builder.ins().stack_store(value, *stack_slot, 0);
                }
            }
        }
        Place::StructField(.., Some(bit_info)) => {
            let addr = emit_place_addr(place, ctx);
            let original = ctx.builder.ins().load(expected_type, MemFlags::new(), addr, 0);

            let mask = if bit_info.width == 64 {
                !0u64
            } else {
                (1u64 << bit_info.width) - 1
            };
            let bit_mask = mask << bit_info.offset;

            let masked_original = ctx.builder.ins().band_imm(original, !(bit_mask as i64));
            let masked_new = ctx.builder.ins().band_imm(value, mask as i64);
            let shifted_new = ctx.builder.ins().ishl_imm(masked_new, bit_info.offset as i64);
            let final_val = ctx.builder.ins().bor(masked_original, shifted_new);

            ctx.builder.ins().store(MemFlags::new(), final_val, addr, 0);
        }
        _ => {
            let addr = emit_place_addr(place, ctx);
            if matches!(place_mir_type, MirType::F80 | MirType::F128) && expected_type == types::F64 {
                emit_f64_to_x87(value, addr, ctx.builder);
            } else {
                ctx.builder.ins().store(MemFlags::new(), value, addr, 0);
            }
        }
    }
}

/// Helper to lower a single MIR statement
fn visit_statement(stmt: &MirStmt, ctx: &mut BodyEmitContext) {
    match stmt {
        MirStmt::Assign(place, rvalue) => {
            let place_type_id = lower_place_type_id(place, ctx.mir, ctx.pointee_to_pointer);
            let place_mir_type = ctx.mir.get_type(place_type_id);
            let expected_type = match lower_type(place_mir_type) {
                Some(t) => t,
                None if matches!(place_mir_type, MirType::F80 | MirType::F128) => types::F64,
                None => types::I64, // Pointers/addresses for aggregates
            };

            // Process the rvalue to get a Cranelift value first
            let rvalue_result = match rvalue {
                Rvalue::Use(operand) => emit_operand(operand, ctx, expected_type),
                Rvalue::UnaryIntOp(op, operand) => {
                    let operand_clif_type = lower_operand_type(operand, ctx.mir, ctx.pointee_to_pointer);
                    let val = emit_operand(operand, ctx, operand_clif_type);

                    match op {
                        UnaryIntOp::Neg => ctx.builder.ins().ineg(val),
                        UnaryIntOp::BitwiseNot => ctx.builder.ins().bnot(val),
                        UnaryIntOp::Popcount => {
                            let res = ctx.builder.ins().popcnt(val);
                            // popcnt returns the same type as input, but builtins return int (I32)
                            emit_type_conversion(res, operand_clif_type, expected_type, false, ctx.builder)
                        }
                        UnaryIntOp::Clz => {
                            let res = ctx.builder.ins().clz(val);
                            emit_type_conversion(res, operand_clif_type, expected_type, false, ctx.builder)
                        }
                        UnaryIntOp::Ctz => {
                            let res = ctx.builder.ins().ctz(val);
                            emit_type_conversion(res, operand_clif_type, expected_type, false, ctx.builder)
                        }
                        UnaryIntOp::Ffs => {
                            let ctz_val = ctx.builder.ins().ctz(val);
                            let ctz_plus_one = ctx.builder.ins().iadd_imm(ctz_val, 1);
                            let zero = ctx.builder.ins().iconst(operand_clif_type, 0);
                            let is_zero = ctx.builder.ins().icmp(IntCC::Equal, val, zero);
                            let res = ctx.builder.ins().select(is_zero, zero, ctz_plus_one);
                            emit_type_conversion(res, operand_clif_type, expected_type, false, ctx.builder)
                        }
                        UnaryIntOp::Bswap16 | UnaryIntOp::Bswap32 | UnaryIntOp::Bswap64 => {
                            let target_type = match op {
                                UnaryIntOp::Bswap16 => types::I16,
                                UnaryIntOp::Bswap32 => types::I32,
                                _ => types::I64,
                            };
                            let cast_val =
                                emit_type_conversion(val, operand_clif_type, target_type, false, ctx.builder);
                            let res = ctx.builder.ins().bswap(cast_val);
                            emit_type_conversion(res, target_type, expected_type, false, ctx.builder)
                        }
                        UnaryIntOp::LogicalNot => {
                            let zero = ctx.builder.ins().iconst(operand_clif_type, 0i64);
                            let is_zero = ctx.builder.ins().icmp(IntCC::Equal, val, zero);
                            emit_bool_to_int(is_zero, expected_type, ctx.builder)
                        }
                    }
                }
                Rvalue::UnaryFloatOp(op, operand) => {
                    let operand_mir_type =
                        ctx.mir
                            .get_type(lower_operand_type_id(operand, ctx.mir, ctx.pointee_to_pointer));
                    let operand_clif_type = if matches!(operand_mir_type, MirType::F80 | MirType::F128) {
                        types::F64
                    } else {
                        lower_operand_type(operand, ctx.mir, ctx.pointee_to_pointer)
                    };
                    let val = emit_operand(operand, ctx, operand_clif_type);

                    match op {
                        UnaryFloatOp::Neg => ctx.builder.ins().fneg(val),
                        UnaryFloatOp::Abs => ctx.builder.ins().fabs(val),
                        UnaryFloatOp::IsNegative => {
                            let width = operand_clif_type.bits();
                            let ity = match width {
                                32 => types::I32,
                                64 => types::I64,
                                _ => types::I64, // Fallback for F80/F128 which we treated as F64
                            };
                            let val_bits = ctx.builder.ins().bitcast(ity, MemFlags::new(), val);
                            let sign_bit = ctx.builder.ins().ushr_imm(val_bits, (width - 1) as i64);
                            emit_type_conversion(sign_bit, ity, expected_type, false, ctx.builder)
                        }
                    }
                }
                Rvalue::BuiltinFrameAddress(_) => {
                    // Create a dummy stack slot to get an address within the current frame.
                    // This is sufficient for stack overflow checks that compare addresses.
                    let slot =
                        ctx.builder
                            .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 8));
                    ctx.builder.ins().stack_addr(types::I64, slot, 0)
                }
                Rvalue::PtrAdd(base, offset) => lower_ptr_arith(base, offset, true, ctx),
                Rvalue::PtrSub(base, offset) => lower_ptr_arith(base, offset, false, ctx),
                Rvalue::PtrDiff(left, right) => {
                    let left_type_id = lower_operand_type_id(left, ctx.mir, ctx.pointee_to_pointer);
                    let left_type = ctx.mir.get_type(left_type_id);
                    let pointee_size = if let MirType::Pointer { pointee } = left_type {
                        let pointee_type = ctx.mir.get_type(*pointee);
                        lower_type_size(pointee_type, ctx.mir)
                    } else {
                        panic!("PtrDiff left operand is not a pointer type");
                    };

                    let left_val = emit_operand(left, ctx, types::I64);
                    let right_val = emit_operand(right, ctx, types::I64);

                    let diff = ctx.builder.ins().isub(left_val, right_val);
                    if pointee_size > 1 {
                        let size_val = ctx.builder.ins().iconst(types::I64, pointee_size as i64);
                        ctx.builder.ins().sdiv(diff, size_val)
                    } else {
                        diff
                    }
                }

                Rvalue::BinaryIntOp(op, left_operand, right_operand) => {
                    let left_clif_type = lower_operand_type(left_operand, ctx.mir, ctx.pointee_to_pointer);
                    let right_clif_type = lower_operand_type(right_operand, ctx.mir, ctx.pointee_to_pointer);

                    // Determine common type for the operation
                    // This handles mixing different integer widths (e.g. i8 + i32 literal)
                    // and pointer arithmetic (i64 + i32 literal)
                    let common_type = if left_clif_type.bits() > right_clif_type.bits() {
                        left_clif_type
                    } else {
                        right_clif_type
                    };

                    let left_val_raw = emit_operand(left_operand, ctx, left_clif_type);
                    let right_val_raw = emit_operand(right_operand, ctx, right_clif_type);

                    let left_val = emit_type_conversion(
                        left_val_raw,
                        left_clif_type,
                        common_type,
                        is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer),
                        ctx.builder,
                    );
                    let right_val = emit_type_conversion(
                        right_val_raw,
                        right_clif_type,
                        common_type,
                        is_operand_signed(right_operand, ctx.mir, ctx.pointee_to_pointer),
                        ctx.builder,
                    );

                    match op {
                        BinaryIntOp::Add => ctx.builder.ins().iadd(left_val, right_val),
                        BinaryIntOp::Sub => ctx.builder.ins().isub(left_val, right_val),
                        BinaryIntOp::Mul => ctx.builder.ins().imul(left_val, right_val),
                        BinaryIntOp::Div => {
                            if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
                                ctx.builder.ins().sdiv(left_val, right_val)
                            } else {
                                ctx.builder.ins().udiv(left_val, right_val)
                            }
                        }
                        BinaryIntOp::Mod => {
                            if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
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
                            if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
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
                            let cond = if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
                                ctx.builder.ins().icmp(IntCC::SignedLessThan, left_val, right_val)
                            } else {
                                ctx.builder.ins().icmp(IntCC::UnsignedLessThan, left_val, right_val)
                            };
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Le => {
                            let cond = if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
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
                            let cond = if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
                                ctx.builder.ins().icmp(IntCC::SignedGreaterThan, left_val, right_val)
                            } else {
                                ctx.builder.ins().icmp(IntCC::UnsignedGreaterThan, left_val, right_val)
                            };
                            emit_bool_to_int(cond, expected_type, ctx.builder)
                        }
                        BinaryIntOp::Ge => {
                            let cond = if is_operand_signed(left_operand, ctx.mir, ctx.pointee_to_pointer) {
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
                    }
                }
                Rvalue::BinaryFloatOp(op, left_operand, right_operand) => {
                    let left_type_id = lower_operand_type_id(left_operand, ctx.mir, ctx.pointee_to_pointer);
                    let left_mir_type = ctx.mir.get_type(left_type_id);
                    let left_clif_type = if matches!(left_mir_type, MirType::F80 | MirType::F128) {
                        types::F64
                    } else {
                        lower_operand_type(left_operand, ctx.mir, ctx.pointee_to_pointer)
                    };

                    let right_type_id = lower_operand_type_id(right_operand, ctx.mir, ctx.pointee_to_pointer);
                    let right_mir_type = ctx.mir.get_type(right_type_id);
                    let right_clif_type = if matches!(right_mir_type, MirType::F80 | MirType::F128) {
                        types::F64
                    } else {
                        lower_operand_type(right_operand, ctx.mir, ctx.pointee_to_pointer)
                    };

                    let left_val = emit_operand(left_operand, ctx, left_clif_type);
                    let right_val = emit_operand(right_operand, ctx, right_clif_type);

                    match op {
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
                    }
                }
                Rvalue::BuiltinVaArg(ap, type_id) => {
                    // X86_64 SysV va_arg implementation
                    // va_list is struct { gp_offset, fp_offset, overflow_arg_area, reg_save_area }
                    // For GP types: if gp_offset < 48, fetch from reg_save_area + gp_offset
                    //               else fetch from overflow_arg_area

                    let ap_addr = emit_place_addr(ap, ctx);

                    // Load fields from va_list
                    let gp_offset = ctx.builder.ins().load(types::I32, MemFlags::new(), ap_addr, 0);
                    let reg_save_area = ctx.builder.ins().load(types::I64, MemFlags::new(), ap_addr, 16);

                    let mir_type = ctx.mir.get_type(*type_id);
                    let cl_type = lower_type(mir_type).unwrap_or(types::I64);
                    let va_arg_type_size = lower_type_size(mir_type, ctx.mir);
                    let align = if ctx.use_variadic_hack {
                        8
                    } else {
                        lower_type_alignment(mir_type, ctx.mir)
                    };

                    // GP arg check: if gp_offset < 48, fetch from reg_save_area + gp_offset
                    //               else fetch from overflow_arg_area
                    let gp_block = ctx.builder.create_block();
                    let overflow_block = ctx.builder.create_block();
                    let join_block = ctx.builder.create_block();

                    // Temporary stack slot to store the resulting address (avoiding BlockArg issues)
                    let addr_slot =
                        ctx.builder
                            .create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 8));
                    // Check if the type can EVER be in the GP area (SysV rules)
                    // Memory class (large aggregates or long double) - MUST match lower_abi_param
                    // For internal hack, everything is in I64 slots (which we treat as GP area here)
                    let is_memory_class = !ctx.use_variadic_hack
                        && (va_arg_type_size > 16 || matches!(mir_type, MirType::F80 | MirType::F128));
                    let can_be_in_gp = ctx.use_variadic_hack
                        || (!is_memory_class && (!mir_type.is_aggregate() || va_arg_type_size <= 16));
                    let is_fp = matches!(mir_type, MirType::F32 | MirType::F64);

                    if can_be_in_gp && !is_fp {
                        let gp_threshold = ctx.builder.ins().iconst(types::I32, 48);
                        let is_overflow =
                            ctx.builder
                                .ins()
                                .icmp(IntCC::UnsignedGreaterThanOrEqual, gp_offset, gp_threshold);
                        ctx.builder.ins().brif(is_overflow, overflow_block, &[], gp_block, &[]);
                    } else {
                        ctx.builder.ins().jump(overflow_block, &[]);
                    }

                    // Path A: GP registers (through spill slot)
                    ctx.builder.switch_to_block(gp_block);
                    // Align GP offset if needed (though usually 8 is enough for GPRs)
                    let aligned_gp = if align > 8 {
                        let align_mask = ctx.builder.ins().iconst(types::I32, align as i64 - 1);
                        let added = ctx.builder.ins().iadd(gp_offset, align_mask);
                        let mask_not = ctx.builder.ins().iconst(types::I32, !(align as i64 - 1));
                        ctx.builder.ins().band(added, mask_not)
                    } else {
                        gp_offset
                    };

                    let offset_64 = ctx.builder.ins().uextend(types::I64, aligned_gp);
                    let gp_addr = ctx.builder.ins().iadd(reg_save_area, offset_64);
                    ctx.builder.ins().stack_store(gp_addr, addr_slot, 0);

                    let needed_gp = va_arg_type_size.max(8).div_ceil(8) * 8;
                    let next_gp_increment = ctx.builder.ins().iconst(types::I32, needed_gp as i64);
                    let next_gp = ctx.builder.ins().iadd(aligned_gp, next_gp_increment);
                    ctx.builder.ins().store(MemFlags::new(), next_gp, ap_addr, 0);

                    // Sync overflow_area to point to the next slot (just in case)
                    let next_gp_64 = ctx.builder.ins().uextend(types::I64, next_gp);
                    let overflow_ptr = ctx.builder.ins().iadd(reg_save_area, next_gp_64);
                    ctx.builder.ins().store(MemFlags::new(), overflow_ptr, ap_addr, 8);

                    ctx.builder.ins().jump(join_block, &[]);

                    // Path B: overflow area
                    ctx.builder.switch_to_block(overflow_block);
                    let overflow_addr = ctx.builder.ins().load(types::I64, MemFlags::new(), ap_addr, 8);

                    // Align overflow_addr if needed (CRITICAL for 16-byte types)
                    let aligned_overflow = if align > 8 {
                        let align_mask = ctx.builder.ins().iconst(types::I64, align as i64 - 1);
                        let added = ctx.builder.ins().iadd(overflow_addr, align_mask);
                        let mask_not = ctx.builder.ins().iconst(types::I64, !(align as i64 - 1));
                        ctx.builder.ins().band(added, mask_not)
                    } else {
                        overflow_addr
                    };

                    ctx.builder.ins().stack_store(aligned_overflow, addr_slot, 0);

                    let needed_overflow = va_arg_type_size.max(8).div_ceil(8) * 8;
                    let next_overflow_increment = ctx.builder.ins().iconst(types::I64, needed_overflow as i64);
                    let next_overflow = ctx.builder.ins().iadd(aligned_overflow, next_overflow_increment);
                    ctx.builder.ins().store(MemFlags::new(), next_overflow, ap_addr, 8);
                    ctx.builder.ins().jump(join_block, &[]);

                    ctx.builder.seal_block(gp_block);
                    ctx.builder.seal_block(overflow_block);
                    ctx.builder.switch_to_block(join_block);
                    ctx.builder.seal_block(join_block);
                    let addr = ctx.builder.ins().stack_load(types::I64, addr_slot, 0);

                    if mir_type.is_aggregate() {
                        // All aggregates (small or large) return the address
                        // small ones are in reg_save_area, large ones in overflow_arg_area
                        addr
                    } else {
                        ctx.builder.ins().load(cl_type, MemFlags::new(), addr, 0)
                    }
                }
                Rvalue::ArrayLiteral(elements) => {
                    let dest_addr = emit_place_addr(place, ctx);
                    emit_array_literal(elements, dest_addr, place_type_id, ctx);
                    // Array literals are stored directly into the place, so no value is returned
                    // This `rvalue_result` will be ignored by the subsequent `emit_place_store`
                    // because we return early.
                    return;
                }
                Rvalue::StructLiteral(fields) => {
                    let dest_addr = emit_place_addr(place, ctx);
                    emit_struct_literal(fields, dest_addr, place_type_id, ctx);
                    // Struct literals are stored directly into the place, so no value is returned
                    // This `rvalue_result` will be ignored by the subsequent `emit_place_store`
                    // because we return early.
                    return;
                }
                Rvalue::AtomicLoad(ptr, _order) => {
                    let ptr_val = emit_operand(ptr, ctx, types::I64);
                    ctx.builder.ins().atomic_load(expected_type, MemFlags::new(), ptr_val)
                }
                Rvalue::AtomicExchange(ptr, val, _order) => {
                    lower_atomic_rmw(ptr, val, AtomicRmwOp::Xchg, expected_type, ctx)
                }
                Rvalue::AtomicCompareExchange(ptr, expected, desired, ..) => {
                    let ptr_val = emit_operand(ptr, ctx, types::I64);
                    let expected_val = emit_operand(expected, ctx, expected_type);
                    let desired_val = emit_operand(desired, ctx, expected_type);

                    ctx.builder
                        .ins()
                        .atomic_cas(MemFlags::new(), ptr_val, expected_val, desired_val)
                }
                Rvalue::AtomicFetchOp(op, ptr, val, _order) => {
                    let rmw_op = match op {
                        BinaryIntOp::Add => AtomicRmwOp::Add,
                        BinaryIntOp::Sub => AtomicRmwOp::Sub,
                        BinaryIntOp::BitAnd => AtomicRmwOp::And,
                        BinaryIntOp::BitOr => AtomicRmwOp::Or,
                        BinaryIntOp::BitXor => AtomicRmwOp::Xor,
                        _ => panic!("Unsupported atomic fetch op: {:?}", op),
                    };
                    lower_atomic_rmw(ptr, val, rmw_op, expected_type, ctx)
                }
            };

            // Decide how to store the result based on whether the rvalue produced a value or an address
            let rvalue_type = ctx.builder.func.dfg.value_type(rvalue_result);
            let mir_type = ctx.mir.get_type(place_type_id);

            if mir_type.is_aggregate() && rvalue_type == types::I64 {
                // Address-to-address copy (memcpy)
                let dest_addr = emit_place_addr(place, ctx);
                let size = lower_type_size(mir_type, ctx.mir) as i64;
                emit_memcpy(dest_addr, rvalue_result, size, ctx.builder, ctx.module);
            } else {
                // Value-to-storage (store)
                // Ensure value matches expected type (truncating/casting if necessary)
                let mut value = emit_type_conversion(
                    rvalue_result,
                    rvalue_type,
                    expected_type,
                    place_mir_type.is_signed(),
                    ctx.builder,
                );

                // C11 6.3.1.2: Any non-zero scalar assigned to _Bool evaluates to 1
                if matches!(place_mir_type, MirType::Bool) {
                    let zero = ctx.builder.ins().iconst(expected_type, 0i64);
                    let is_not_zero = ctx.builder.ins().icmp(IntCC::NotEqual, value, zero);
                    value = emit_bool_to_int(is_not_zero, expected_type, ctx.builder);
                }

                emit_place_store(place, value, expected_type, ctx);
            }
        }

        MirStmt::Call { target, args, dest } => {
            if let Some(dest_place) = dest {
                // Call with destination - need to store the result
                let dest_type_id = lower_place_type_id(dest_place, ctx.mir, ctx.pointee_to_pointer);
                let dest_mir_type = ctx.mir.get_type(dest_type_id);
                let _expected_type = match lower_type(dest_mir_type) {
                    Some(t) => t,
                    None if dest_mir_type.is_aggregate() => types::I64,
                    None => panic!("Cannot assign to void type"),
                };
                let result = emit_function_call(target, args, ctx);

                // Store the result in the destination place
                let dest_mir_type = ctx.mir.get_type(dest_type_id);
                if dest_mir_type.is_aggregate() {
                    // For aggregate types, result is an address, memcpy to dest
                    let dest_addr = emit_place_addr(dest_place, ctx);
                    let size = lower_type_size(dest_mir_type, ctx.mir) as i64;
                    emit_memcpy(dest_addr, result, size, ctx.builder, ctx.module);
                } else {
                    let expected_type = lower_type(dest_mir_type).unwrap();
                    emit_place_store(dest_place, result, expected_type, ctx);
                }
            } else {
                // Call without destination - ignore return value (side-effect only)
                let _ = emit_function_call(target, args, ctx);
            }
        }

        MirStmt::BuiltinVaStart(place, _operand) => {
            let ap_addr = emit_place_addr(place, ctx);

            if let Some(spill_slot) = ctx.va_spill_slot {
                let spill_addr = ctx.builder.ins().stack_addr(types::I64, spill_slot, 0);

                // 1. gp_offset
                // Calculate how many bytes are consumed by fixed parameters
                let fixed_count = ctx.fixed_params_count;
                let gp_val = fixed_count * 8;

                // Clamp to 48 (max GPR registers)
                let effective_gp = std::cmp::min(gp_val, 48);
                let gp_const = ctx.builder.ins().iconst(types::I32, effective_gp as i64);
                ctx.builder.ins().store(MemFlags::new(), gp_const, ap_addr, 0);

                // 2. fp_offset = 176 (all FP args are passed in GPRs due to variadic hack)
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
        }
        MirStmt::AtomicStore(ptr, val, _order) => {
            let ptr_val = emit_operand(ptr, ctx, types::I64);
            let val_type = lower_operand_type(val, ctx.mir, ctx.pointee_to_pointer);
            let val_op = emit_operand(val, ctx, val_type);

            ctx.builder.ins().atomic_store(MemFlags::new(), val_op, ptr_val);
        }
        MirStmt::BuiltinVaEnd(_place) => {
            // No-op for x86_64
        }
        MirStmt::BuiltinVaCopy(dest, src) => {
            let dest_addr = emit_place_addr(dest, ctx);
            let src_addr = emit_place_addr(src, ctx);
            // va_list is 24 bytes on x86_64
            emit_memcpy(dest_addr, src_addr, 24, ctx.builder, ctx.module);
        }
        MirStmt::BuiltinPrefetch { addr, .. } => {
            let _ = emit_operand(addr, ctx, types::I64);
            // Cranelift doesn't have a stable prefetch intrinsic in InstBuilder yet.
        }
    }
}

/// Helper to lower a terminator
fn visit_terminator(terminator: &Terminator, ctx: &mut BodyEmitContext) {
    match terminator {
        Terminator::Goto(target) => {
            let target_cl_block = ctx.clif_blocks.get(target).unwrap_or_else(|| {
                panic!("Target block {:?} not found in function {}", target, ctx.func.name);
            });
            ctx.builder.ins().jump(*target_cl_block, &[]);
            ctx.worklist.push(*target);
        }

        Terminator::If(cond, then_bb, else_bb) => {
            let cond_val = emit_operand(cond, ctx, types::I32);

            let then_cl_block = ctx.clif_blocks.get(then_bb).unwrap_or_else(|| {
                panic!("Then block {:?} not found in function {}", then_bb, ctx.func.name);
            });
            let else_cl_block = ctx.clif_blocks.get(else_bb).unwrap_or_else(|| {
                panic!("Else block {:?} not found in function {}", else_bb, ctx.func.name);
            });

            ctx.builder
                .ins()
                .brif(cond_val, *then_cl_block, &[], *else_cl_block, &[]);

            ctx.worklist.push(*then_bb);
            ctx.worklist.push(*else_bb);
        }

        Terminator::Return(opt) => {
            if let Some(operand) = opt {
                if !ctx.return_types.is_empty() {
                    let mir_type = ctx.mir.get_type(ctx.func.return_type);
                    if let Some(return_ptr) = ctx.return_ptr {
                        // Large aggregate return via hidden pointer
                        let addr = emit_operand(operand, ctx, types::I64);
                        let size = lower_type_size(mir_type, ctx.mir) as i64;
                        emit_memcpy(return_ptr, addr, size, ctx.builder, ctx.module);
                        ctx.builder.ins().return_(&[return_ptr]);
                    } else if let Some(types_list) = get_struct_packing(mir_type, ctx.mir) {
                        // Pack return value into multiple registers
                        let addr = emit_operand(operand, ctx, types::I64);
                        let mut ret_values = Vec::new();
                        for (i, &t) in types_list.iter().enumerate() {
                            let offset = (i * 8) as i32;
                            let val = ctx.builder.ins().load(t, MemFlags::new(), addr, offset);
                            ret_values.push(val);
                        }
                        ctx.builder.ins().return_(&ret_values);
                    } else {
                        let ret_type = ctx.return_types[0];
                        let return_value = emit_operand(operand, ctx, ret_type);
                        ctx.builder.ins().return_(&[return_value]);
                    }
                } else {
                    panic!("Returning a value from a void function");
                }
            } else {
                ctx.builder.ins().return_(&[]);
            }
        }

        Terminator::Unreachable => {
            // For unreachable, default to appropriate return based on function type
            if !ctx.return_types.is_empty() {
                let mut ret_values = Vec::new();
                for &ret_type in &ctx.return_types {
                    let val = ctx.builder.ins().iconst(ret_type, 0i64);
                    ret_values.push(val);
                }
                ctx.builder.ins().return_(&ret_values);
            } else {
                // Void function
                ctx.builder.ins().return_(&[]);
            }
        }

        Terminator::Trap => {
            ctx.builder.ins().trap(cranelift::prelude::TrapCode::unwrap_user(1));
        }
    }
}

fn lower_function_signature(
    func: &MirFunction,
    mir: &MirProgram,
    sig: &mut Signature,
    use_variadic_hack: bool,
) -> (Vec<Type>, Vec<Type>, bool) {
    sig.params.clear();
    sig.returns.clear();

    let mut return_types = Vec::new();
    let has_hidden_return_ptr = lower_abi_return(mir.get_type(func.return_type), mir, sig, &mut return_types);

    let mut param_types = Vec::new();
    if has_hidden_return_ptr {
        param_types.push(types::I64);
    }

    for &param_id in &func.params {
        let param_local = mir.get_local(param_id);
        lower_abi_param(
            mir.get_type(param_local.type_id),
            mir,
            sig,
            &mut param_types,
            use_variadic_hack,
        );
    }

    if func.is_variadic && use_variadic_hack {
        while sig.params.len() < 128 {
            sig.params.push(AbiParam::new(types::I64));
        }
    }

    (param_types, return_types, has_hidden_return_ptr)
}

fn emit_stack_slots(
    func: &MirFunction,
    mir: &MirProgram,
    builder: &mut FunctionBuilder,
    clif_stack_slots: &mut HashMap<LocalId, StackSlot>,
) {
    clif_stack_slots.clear(); // Clear for each function

    // Combine locals and params for slot allocation
    let all_locals: Vec<LocalId> = func.locals.iter().chain(func.params.iter()).cloned().collect();

    for &local_id in &all_locals {
        let local = mir.get_local(local_id);
        let local_type = mir.get_type(local.type_id);
        let size = lower_type_size(local_type, mir);

        // Don't allocate space for zero-sized types
        if size > 0 {
            // Use explicit alignment if provided, otherwise default to natural alignment of the type
            let mir_type = mir.get_type(local.type_id);
            let natural_align = lower_type_alignment(mir_type, mir);

            let alignment = local.alignment.map(|a| a as u64).unwrap_or(natural_align);
            let align_shift = alignment.max(1).trailing_zeros() as u8;

            let slot_data = StackSlotData::new(StackSlotKind::ExplicitSlot, size, align_shift);
            let slot = builder.create_sized_stack_slot(slot_data);
            clif_stack_slots.insert(local_id, slot);
        }
    }
}

fn finalize_function_processing(
    func: &MirFunction,
    module: &mut ObjectModule,
    func_ctx: &mut cranelift::codegen::Context,
    emit_kind: EmitKind,
    compiled_functions: &mut HashMap<String, String>,
) {
    // Now declare and define the function
    let linkage = lower_mir_linkage(func.linkage);

    let id = module
        .declare_function(func.name.as_str(), linkage, &func_ctx.func.signature)
        .expect("module operation failed");

    // Only define the function body if it's a defined function (not extern)
    if func.linkage != MirLinkage::Import {
        module.define_function(id, func_ctx).expect("module operation failed");
    }

    if emit_kind == EmitKind::Clif {
        // Store the function IR string for dumping
        let func_ir = func_ctx.func.to_string();
        compiled_functions.insert(func.name.to_string(), func_ir);
    }
}

/// MIR to Cranelift IR Lowerer
pub struct ClifGen {
    pub(crate) builder_context: FunctionBuilderContext,
    pub(crate) module: ObjectModule,
    pub(crate) mir: MirProgram, // NOTE: need better nama
    pub(crate) clif_stack_slots: HashMap<LocalId, StackSlot>,
    // Store compiled functions for dumping
    pub(crate) compiled_functions: HashMap<String, String>,

    pub(crate) emit_kind: EmitKind,

    // Mappings for relocations
    pub(crate) func_id_map: HashMap<MirFunctionId, FuncId>,
    pub(crate) data_id_map: HashMap<GlobalId, DataId>,
    pub(crate) pointee_to_pointer: HashMap<TypeId, TypeId>,

    // Variadic spill area for the current function
    va_spill_slot: Option<StackSlot>,

    triple: Triple,
    vararg_count_data: Option<DataId>,
    vararg_target_data: Option<DataId>,
    vararg_trampoline_func: Option<FuncId>,
}

/// NOTE: we use panic!() to ICE because codegen rely on correct MIR, so if we give invalid MIR, then problem is in previous phase
impl ClifGen {
    pub(crate) fn new(mir: MirProgram) -> Self {
        let triple = Triple::host();
        let mut flag_builder = cranelift::prelude::settings::builder();
        flag_builder.set("is_pic", "true").unwrap();

        let tls_model = match triple.binary_format {
            target_lexicon::BinaryFormat::Elf => "elf_gd",
            target_lexicon::BinaryFormat::Macho => "macho",
            target_lexicon::BinaryFormat::Coff => "coff",
            _ => "none",
        };
        flag_builder.set("tls_model", tls_model).unwrap();

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
            clif_stack_slots: HashMap::new(),
            compiled_functions: HashMap::new(),
            emit_kind: EmitKind::Object,
            func_id_map: HashMap::new(),
            data_id_map: HashMap::new(),
            va_spill_slot: None,
            triple,
            vararg_count_data: None,
            vararg_target_data: None,
            vararg_trampoline_func: None,
            pointee_to_pointer: mir
                .types
                .iter()
                .enumerate()
                .filter_map(|(i, ty)| {
                    let id = TypeId::new((i + 1) as u32).unwrap();
                    if let MirType::Pointer { pointee } = ty {
                        Some((*pointee, id))
                    } else {
                        None
                    }
                })
                .collect(),
            mir,
        }
    }

    pub(crate) fn visit_module(mut self, emit_kind: EmitKind) -> ClifOutput {
        self.emit_kind = emit_kind;

        let (reachable_functions, reachable_globals) = self.analyze_reachability();

        // Pass 1: Declare reachable global variables
        for &global_id in &self.mir.module.globals {
            if !reachable_globals.contains(&global_id) {
                continue;
            }
            let global = self.mir.get_global(global_id);
            let linkage = lower_mir_linkage(global.linkage);

            let data_id = self
                .module
                .declare_data(global.name.as_str(), linkage, true, global.is_tls)
                .expect("module operation failed");

            self.data_id_map.insert(global_id, data_id);
        }

        // Pass 2: Declare reachable functions
        for &func_id in &self.mir.module.functions {
            if !reachable_functions.contains(&func_id) {
                continue;
            }
            let func = self.mir.get_function(func_id);
            let linkage = lower_mir_linkage(func.linkage);

            // Calculate signature for declaration
            let mut sig = self.module.make_signature();
            let use_hack = func.is_variadic
                && func.linkage != MirLinkage::Import
                && self.triple.architecture == target_lexicon::Architecture::X86_64;
            let (..) = lower_function_signature(func, &self.mir, &mut sig, use_hack);

            let clif_func_id = self
                .module
                .declare_function(func.name.as_str(), linkage, &sig)
                .expect("module operation failed");

            self.func_id_map.insert(func_id, clif_func_id);
        }

        // Pass 3: Define Global Variables (with relocations)
        for &global_id in &self.mir.module.globals {
            if !reachable_globals.contains(&global_id) {
                continue;
            }
            let global = self.mir.get_global(global_id);
            if let Some(const_id) = global.initial_value {
                let data_id = *self.data_id_map.get(&global_id).unwrap();
                let mut data_description = DataDescription::new();

                let const_val = self.mir.get_constant(const_id);
                if let ConstValueKind::Zero = const_val.kind {
                    let ty = self.mir.get_type(const_val.ty);
                    let size = lower_type_size(ty, &self.mir) as usize;
                    data_description.define_zeroinit(size);
                } else {
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
                    );

                    data_description.define(initial_value_bytes.into_boxed_slice());
                }

                self.module
                    .define_data(data_id, &data_description)
                    .expect("module operation failed");
            }
        }

        // Pass 4: Define Functions (Lower bodies)
        // We can't iterate on `&self.mir.module.functions` directly because `visit_function`
        // needs a mutable borrow of `self`. Instead, we iterate by index to avoid cloning the
        // function list, which would cause a heap allocation.
        for i in 0..self.mir.module.functions.len() {
            let func_id = self.mir.module.functions[i];
            if !reachable_functions.contains(&func_id) {
                continue;
            }
            // Only lower functions that are defined (have bodies)
            if self.mir.get_function(func_id).linkage != MirLinkage::Import {
                self.visit_function(func_id);
            }
        }

        // Finalize and return the compiled code
        let code = crate::codegen::ObjectGen::finalize(self.module).expect("Failed to finalize module");

        if emit_kind == EmitKind::Object {
            ClifOutput::ObjectFile(code)
        } else {
            // For Clif dump, concatenate all function IRs
            let mut clif_dump = String::new();
            let mut func_names: Vec<_> = self.compiled_functions.keys().collect();
            func_names.sort();

            for func_name in func_names {
                let func_ir = self.compiled_functions.get(func_name).unwrap();
                clif_dump.push_str(&format!("; Function: {}\n", func_name));
                clif_dump.push_str(func_ir);
                clif_dump.push_str("\n\n");
            }
            ClifOutput::ClifDump(clif_dump)
        }
    }

    /// Lower a MIR function to Cranelift IR using 3-phase algorithm
    fn visit_function(&mut self, func_id: MirFunctionId) {
        let func = self.mir.get_function(func_id);
        // Create a fresh context for this function
        let mut func_ctx = self.module.make_context();

        let (param_types, return_types, has_hidden_ptr) = lower_function_signature(
            func,
            &self.mir,
            &mut func_ctx.func.signature,
            func.is_variadic && self.triple.architecture == target_lexicon::Architecture::X86_64,
        );

        // Create a function builder with the fresh context
        let mut builder = FunctionBuilder::new(&mut func_ctx.func, &mut self.builder_context);

        emit_stack_slots(func, &self.mir, &mut builder, &mut self.clif_stack_slots);

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

            let clif_block = clif_blocks.get(&current_block_id).expect("Block not found in mapping");
            builder.switch_to_block(*clif_block);

            // Setup entry block parameters
            if Some(current_block_id) == func.entry_block {
                // Step 1: Add ALL block parameters first (fixed params)
                for &param_type in &param_types {
                    builder.append_block_param(*clif_block, param_type);
                }

                // Step 2: Add variadic block parameters if needed (still before any instructions)
                if func.is_variadic {
                    let total_variadic_slots = 128; // Must match lower_function_signature
                    if param_types.len() < total_variadic_slots {
                        let extra_count = total_variadic_slots - param_types.len();
                        for _ in 0..extra_count {
                            builder.append_block_param(*clif_block, types::I64);
                        }
                    }
                }

                // Step 3: NOW emit instructions - store fixed params to stack slots
                let param_values: Vec<Value> = builder.block_params(*clif_block).to_vec();
                let mut param_iter = param_values.iter().copied();

                if has_hidden_ptr {
                    // Skip hidden return pointer
                    param_iter.next();
                }

                for &param_id in &func.params {
                    let local = self.mir.get_local(param_id);
                    let mir_type = self.mir.get_type(local.type_id);

                    // Check for struct packing or variadic hack splitting
                    let use_hack = func.is_variadic && self.triple.architecture == target_lexicon::Architecture::X86_64;
                    if let Some(types_list) = get_struct_packing(mir_type, &self.mir).or_else(|| {
                        (use_hack && mir_type.is_aggregate()).then(|| {
                            let size = lower_type_size(mir_type, &self.mir);
                            vec![types::I64; size.div_ceil(8) as usize]
                        })
                    }) {
                        if let Some(stack_slot) = self.clif_stack_slots.get(&param_id) {
                            let size = lower_type_size(mir_type, &self.mir);
                            for (i, &t) in types_list.iter().enumerate() {
                                let val = param_iter.next().unwrap();
                                let offset = (i * 8) as i32;
                                let remaining = size.saturating_sub((i * 8) as u32);

                                if remaining >= 8 {
                                    builder.ins().stack_store(val, *stack_slot, offset);
                                } else {
                                    // Partial store
                                    let current_val_i64 = if t.is_float() {
                                        builder.ins().bitcast(types::I64, MemFlags::new(), val)
                                    } else {
                                        val
                                    };
                                    let slot_addr = builder.ins().stack_addr(types::I64, *stack_slot, 0);
                                    emit_partial_store(&mut builder, current_val_i64, slot_addr, offset, remaining);
                                }
                            }
                        } else {
                            // Consume even if no stack slot
                            for _ in 0..types_list.len() {
                                let _ = param_iter.next();
                            }
                        }
                        continue;
                    }

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
                            // Passed by pointer (I64) (only for non-variadic large structs)
                            let dest_addr = builder.ins().stack_addr(types::I64, *stack_slot, 0);
                            let size = lower_type_size(mir_type, &self.mir) as i64;
                            emit_memcpy(dest_addr, param_value, size, &mut builder, &mut self.module);
                        } else {
                            builder.ins().stack_store(param_value, *stack_slot, 0);
                        }
                    }
                }

                // Step 4: Handle variadic spill area - save all 32 slots
                if func.is_variadic {
                    let total_slots = 128;
                    let spill_size = total_slots * 8; // 256 bytes for 32 I64 slots
                    let spill_slot = builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        spill_size as u32,
                        4, // 16-byte aligned (2^4)
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
            let mir_block = self.mir.get_block(current_block_id);

            // ========================================================================
            // SECTION 1: Process statements within this block
            // ========================================================================
            let statements_to_process: Vec<MirStmt> = mir_block
                .statements
                .iter()
                .map(|&stmt_id| self.mir.get_statement(stmt_id).clone())
                .collect();

            let mut return_ptr = None;
            if has_hidden_ptr {
                // Return pointer is the first block parameter
                let clif_block = clif_blocks.get(&func.entry_block.unwrap()).unwrap();
                return_ptr = Some(builder.block_params(*clif_block)[0]);
            }

            let mut ctx = BodyEmitContext {
                builder: &mut builder,
                mir: &self.mir,
                stack_slots: &self.clif_stack_slots,
                module: &mut self.module,
                va_spill_slot,
                func,
                clif_blocks: &clif_blocks,
                worklist: &mut worklist,
                return_types: return_types.clone(),
                return_ptr,
                func_id_map: &self.func_id_map,
                data_id_map: &self.data_id_map,
                triple: &self.triple,
                vararg_count_data: &mut self.vararg_count_data,
                vararg_target_data: &mut self.vararg_target_data,
                vararg_trampoline_func: &mut self.vararg_trampoline_func,
                pointee_to_pointer: &self.pointee_to_pointer,
                use_variadic_hack: func.is_variadic && self.triple.architecture == target_lexicon::Architecture::X86_64,
                fixed_params_count: param_types.len(),
            };

            // Process statements
            for stmt in &statements_to_process {
                visit_statement(stmt, &mut ctx);
            }

            // ========================================================================
            // SECTION 2: Process terminator (control flow)
            // ========================================================================
            visit_terminator(&mir_block.terminator, &mut ctx);

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
        );
    }

    fn analyze_reachability(&self) -> (HashSet<MirFunctionId>, HashSet<GlobalId>) {
        let mut reachable_functions = HashSet::new();
        let mut reachable_globals = HashSet::new();
        let mut worklist_functions = Vec::new();
        let mut worklist_globals = Vec::new();

        // Initial roots: all non-import functions and all globals with initializers
        for (i, func) in self.mir.functions.iter().enumerate() {
            let id = MirFunctionId::new((i + 1) as u32).unwrap();
            if func.linkage != MirLinkage::Import && reachable_functions.insert(id) {
                worklist_functions.push(id);
            }
        }
        for (i, global) in self.mir.globals.iter().enumerate() {
            let id = GlobalId::new((i + 1) as u32).unwrap();
            if global.initial_value.is_some() && reachable_globals.insert(id) {
                worklist_globals.push(id);
            }
        }

        while !worklist_functions.is_empty() || !worklist_globals.is_empty() {
            while let Some(func_id) = worklist_functions.pop() {
                let func = self.mir.get_function(func_id);
                for block_id in &func.blocks {
                    let block = self.mir.get_block(*block_id);
                    for &stmt_id in &block.statements {
                        let stmt = self.mir.get_statement(stmt_id);
                        self.collect_stmt_reachability(
                            stmt,
                            &mut worklist_functions,
                            &mut reachable_functions,
                            &mut reachable_globals,
                            &mut worklist_globals,
                        );
                    }
                    self.collect_term_reachability(
                        &block.terminator,
                        &mut worklist_functions,
                        &mut reachable_functions,
                        &mut reachable_globals,
                        &mut worklist_globals,
                    );
                }
            }

            while let Some(global_id) = worklist_globals.pop() {
                let global = self.mir.get_global(global_id);
                if let Some(const_id) = global.initial_value {
                    self.collect_const_reachability(
                        const_id,
                        &mut worklist_functions,
                        &mut reachable_functions,
                        &mut reachable_globals,
                        &mut worklist_globals,
                    );
                }
            }
        }

        (reachable_functions, reachable_globals)
    }

    fn collect_stmt_reachability(
        &self,
        stmt: &MirStmt,
        wf: &mut Vec<MirFunctionId>,
        rf: &mut HashSet<MirFunctionId>,
        rg: &mut HashSet<GlobalId>,
        wg: &mut Vec<GlobalId>,
    ) {
        match stmt {
            MirStmt::Assign(place, rvalue) => {
                self.collect_place_reachability(place, wf, rf, rg, wg);
                self.collect_rvalue_reachability(rvalue, wf, rf, rg, wg);
            }
            MirStmt::Call { target, args, dest } => {
                match target {
                    CallTarget::Direct(id) => {
                        if rf.insert(*id) {
                            wf.push(*id);
                        }
                    }
                    CallTarget::Indirect(op) => self.collect_operand_reachability(op, wf, rf, rg, wg),
                }
                for arg in args {
                    self.collect_operand_reachability(arg, wf, rf, rg, wg);
                }
                if let Some(place) = dest {
                    self.collect_place_reachability(place, wf, rf, rg, wg);
                }
            }
            MirStmt::BuiltinVaStart(p, op) => {
                self.collect_place_reachability(p, wf, rf, rg, wg);
                self.collect_operand_reachability(op, wf, rf, rg, wg);
            }
            MirStmt::BuiltinVaEnd(p) => self.collect_place_reachability(p, wf, rf, rg, wg),
            MirStmt::BuiltinVaCopy(p1, p2) => {
                self.collect_place_reachability(p1, wf, rf, rg, wg);
                self.collect_place_reachability(p2, wf, rf, rg, wg);
            }
            MirStmt::AtomicStore(v1, v2, _) => {
                self.collect_operand_reachability(v1, wf, rf, rg, wg);
                self.collect_operand_reachability(v2, wf, rf, rg, wg);
            }
            MirStmt::BuiltinPrefetch { addr, .. } => {
                self.collect_operand_reachability(addr, wf, rf, rg, wg);
            }
        }
    }

    fn collect_term_reachability(
        &self,
        term: &Terminator,
        wf: &mut Vec<MirFunctionId>,
        rf: &mut HashSet<MirFunctionId>,
        rg: &mut HashSet<GlobalId>,
        wg: &mut Vec<GlobalId>,
    ) {
        match term {
            Terminator::Return(val) => {
                if let Some(op) = val {
                    self.collect_operand_reachability(op, wf, rf, rg, wg);
                }
            }
            Terminator::If(cond, _, _) => self.collect_operand_reachability(cond, wf, rf, rg, wg),
            Terminator::Goto(_) | Terminator::Unreachable | Terminator::Trap => {}
        }
    }

    fn collect_operand_reachability(
        &self,
        op: &Operand,
        wf: &mut Vec<MirFunctionId>,
        rf: &mut HashSet<MirFunctionId>,
        rg: &mut HashSet<GlobalId>,
        wg: &mut Vec<GlobalId>,
    ) {
        match op {
            Operand::Copy(place) | Operand::AddressOf(place) => self.collect_place_reachability(place, wf, rf, rg, wg),
            Operand::Constant(id) => self.collect_const_reachability(*id, wf, rf, rg, wg),
            Operand::Cast(_, inner) => self.collect_operand_reachability(inner, wf, rf, rg, wg),
        }
    }

    fn collect_place_reachability(
        &self,
        place: &Place,
        wf: &mut Vec<MirFunctionId>,
        rf: &mut HashSet<MirFunctionId>,
        rg: &mut HashSet<GlobalId>,
        wg: &mut Vec<GlobalId>,
    ) {
        match place {
            Place::Global(id) => {
                if rg.insert(*id) {
                    wg.push(*id);
                }
            }
            Place::Deref(op) => self.collect_operand_reachability(op, wf, rf, rg, wg),
            Place::StructField(base, _, _) | Place::ArrayIndex(base, _) => {
                self.collect_place_reachability(base, wf, rf, rg, wg);
                if let Place::ArrayIndex(_, idx) = place {
                    self.collect_operand_reachability(idx, wf, rf, rg, wg);
                }
            }
            Place::Local(_) => {}
        }
    }

    fn collect_rvalue_reachability(
        &self,
        rvalue: &Rvalue,
        wf: &mut Vec<MirFunctionId>,
        rf: &mut HashSet<MirFunctionId>,
        rg: &mut HashSet<GlobalId>,
        wg: &mut Vec<GlobalId>,
    ) {
        match rvalue {
            Rvalue::Use(op)
            | Rvalue::UnaryIntOp(_, op)
            | Rvalue::UnaryFloatOp(_, op)
            | Rvalue::PtrAdd(op, _)
            | Rvalue::PtrSub(op, _)
            | Rvalue::AtomicLoad(op, _) => self.collect_operand_reachability(op, wf, rf, rg, wg),

            Rvalue::BinaryIntOp(_, l, r)
            | Rvalue::BinaryFloatOp(_, l, r)
            | Rvalue::PtrDiff(l, r)
            | Rvalue::AtomicExchange(l, r, _)
            | Rvalue::AtomicFetchOp(_, l, r, _) => {
                self.collect_operand_reachability(l, wf, rf, rg, wg);
                self.collect_operand_reachability(r, wf, rf, rg, wg);
            }
            Rvalue::AtomicCompareExchange(p, e, d, ..) => {
                self.collect_operand_reachability(p, wf, rf, rg, wg);
                self.collect_operand_reachability(e, wf, rf, rg, wg);
                self.collect_operand_reachability(d, wf, rf, rg, wg);
            }
            Rvalue::StructLiteral(fields) => {
                for (_, op) in fields {
                    self.collect_operand_reachability(op, wf, rf, rg, wg);
                }
            }
            Rvalue::ArrayLiteral(elements) => {
                for op in elements {
                    self.collect_operand_reachability(op, wf, rf, rg, wg);
                }
            }
            Rvalue::BuiltinVaArg(place, _) => self.collect_place_reachability(place, wf, rf, rg, wg),
            Rvalue::BuiltinFrameAddress(_) => {}
        }
    }

    fn collect_const_reachability(
        &self,
        id: ConstValueId,
        wf: &mut Vec<MirFunctionId>,
        rf: &mut HashSet<MirFunctionId>,
        rg: &mut HashSet<GlobalId>,
        wg: &mut Vec<GlobalId>,
    ) {
        let cv = self.mir.get_constant(id);
        match &cv.kind {
            ConstValueKind::GlobalAddress(gid, _) if rg.insert(*gid) => {
                wg.push(*gid);
            }
            ConstValueKind::FunctionAddress(fid) if rf.insert(*fid) => {
                wf.push(*fid);
            }
            ConstValueKind::StructLiteral(fields) => {
                for (_, fid) in fields {
                    self.collect_const_reachability(*fid, wf, rf, rg, wg);
                }
            }
            ConstValueKind::ArrayLiteral(elements) => {
                for eid in elements {
                    self.collect_const_reachability(*eid, wf, rf, rg, wg);
                }
            }
            _ => {}
        }
    }
}
