use crate::codegen::error::{CodegenError, CodegenResult};
use crate::parser::ast::{
    AssignOp, BinOp, Type, TypedDesignator, TypedExpr, TypedForInit, TypedInitializer, TypedStmt,
};
use crate::parser::string_interner::StringId;
use cranelift::prelude::*;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{InstBuilder, Value};
use cranelift_codegen::ir::{StackSlot, StackSlotData, StackSlotKind};
use cranelift_frontend::{FunctionBuilder, Variable};
use cranelift_module::Module;
use std::collections::HashMap;

use super::SymbolTable;
use cranelift_module::DataId;
use cranelift_module::FuncId;
use cranelift_module::Linkage;
use cranelift_object::ObjectModule;

fn unescape(s: &str) -> Vec<u8> {
    let mut unescaped = Vec::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            if let Some(next) = chars.next() {
                match next {
                    'n' => unescaped.push(b'\n'),
                    't' => unescaped.push(b'\t'),
                    'r' => unescaped.push(b'\r'),
                    '\\' => unescaped.push(b'\\'),
                    '"' => unescaped.push(b'"'),
                    '\'' => unescaped.push(b'\''),
                    '0' => unescaped.push(b'\0'),
                    _ => {
                        // Not a valid escape sequence, treat as literal backslash and character
                        unescaped.push(b'\\');
                        unescaped.push(next as u8);
                    }
                }
            } else {
                // Trailing backslash
                unescaped.push(b'\\');
            }
        } else {
            unescaped.push(c as u8);
        }
    }
    unescaped
}

/// The state of the current block.
#[derive(PartialEq, PartialOrd)]
pub enum BlockState {
    /// The block is empty.
    Empty,
    /// The block is filled with instructions.
    Filled,
}
/// A function translator that translates statements and expressions into Cranelift IR.
pub(crate) struct FunctionTranslator<'a, 'b> {
    pub(crate) builder: FunctionBuilder<'a>,
    pub(crate) functions: &'b HashMap<StringId, (FuncId, Type, bool)>,
    pub(crate) variables:
        &'b mut SymbolTable<StringId, (Option<Variable>, Option<StackSlot>, Type)>,
    pub(crate) global_variables: &'b HashMap<StringId, (DataId, Type)>,
    pub(crate) static_local_variables: &'b mut HashMap<StringId, (DataId, Type)>,
    pub(crate) structs: &'b HashMap<StringId, Type>,
    pub(crate) unions: &'b HashMap<StringId, Type>,
    pub(crate) enum_constants: &'b HashMap<StringId, i64>,
    pub(crate) module: &'b mut ObjectModule,
    pub(crate) loop_context: Vec<(Block, Block)>,
    pub(crate) current_block_state: BlockState,
    pub(crate) signatures: &'b HashMap<StringId, Signature>,
    pub(crate) label_blocks: HashMap<StringId, Block>,
    pub(crate) current_function_name: StringId,
    pub(crate) anonymous_string_count: &'b mut usize,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
    pub fn get_type_size_from_type(
        ty: &Type,
        structs: &HashMap<StringId, Type>,
        unions: &HashMap<StringId, Type>,
    ) -> u32 {
        let real_ty = Self::get_real_type_from_type(ty, structs, unions).unwrap();
        match &real_ty {
            Type::Const(inner) => Self::get_type_size_from_type(inner, structs, unions),
            Type::Volatile(inner) => Self::get_type_size_from_type(inner, structs, unions),
            Type::Int | Type::UnsignedInt => 8,
            Type::Char | Type::UnsignedChar => 1,
            Type::Short | Type::UnsignedShort => 2,
            Type::Float => 4,
            Type::Double => 8,
            Type::Long | Type::UnsignedLong => 8,
            Type::LongLong | Type::UnsignedLongLong => 8,
            Type::Void => 0,
            Type::Bool => 1,
            Type::Pointer(_) => 8,
            Type::Struct(_, members) => {
                let mut size = 0;
                for member in members {
                    let member_size = Self::get_type_size_from_type(&member.ty, structs, unions);
                    let member_alignment =
                        Self::get_type_alignment_from_type(&member.ty, structs, unions);
                    size = (size + member_alignment - 1) & !(member_alignment - 1);
                    size += member_size;
                }
                let struct_alignment = Self::get_type_alignment_from_type(ty, structs, unions);
                (size + struct_alignment - 1) & !(struct_alignment - 1)
            }
            Type::Union(_, members) => {
                let size = members
                    .iter()
                    .map(|m| Self::get_type_size_from_type(&m.ty, structs, unions))
                    .max()
                    .unwrap_or(0);
                let union_alignment = Self::get_type_alignment_from_type(ty, structs, unions);
                (size + union_alignment - 1) & !(union_alignment - 1)
            }
            Type::Array(elem_ty, size) => {
                Self::get_type_size_from_type(elem_ty, structs, unions) * *size as u32
            }
            Type::Enum(_, _) => 8,
        }
    }

    fn get_type_alignment_from_type(
        ty: &Type,
        structs: &HashMap<StringId, Type>,
        unions: &HashMap<StringId, Type>,
    ) -> u32 {
        let real_ty = Self::get_real_type_from_type(ty, structs, unions).unwrap();
        match &real_ty {
            Type::Const(inner) => Self::get_type_alignment_from_type(inner, structs, unions),
            Type::Volatile(inner) => Self::get_type_alignment_from_type(inner, structs, unions),
            Type::Int | Type::UnsignedInt => 8,
            Type::Char | Type::UnsignedChar => 1,
            Type::Short | Type::UnsignedShort => 2,
            Type::Float => 4,
            Type::Double => 8,
            Type::Long | Type::UnsignedLong => 8,
            Type::LongLong | Type::UnsignedLongLong => 8,
            Type::Void => 1,
            Type::Bool => 1,
            Type::Pointer(_) => 8,
            Type::Struct(_, members) => members
                .iter()
                .map(|m| Self::get_type_alignment_from_type(&m.ty, structs, unions))
                .max()
                .unwrap_or(1),
            Type::Union(_, members) => members
                .iter()
                .map(|m| Self::get_type_alignment_from_type(&m.ty, structs, unions))
                .max()
                .unwrap_or(1),
            Type::Array(elem_ty, _) => Self::get_type_alignment_from_type(elem_ty, structs, unions),
            Type::Enum(_, _) => 8,
        }
    }

    fn get_real_type_from_type(
        ty: &Type,
        structs: &HashMap<StringId, Type>,
        unions: &HashMap<StringId, Type>,
    ) -> Result<Type, CodegenError> {
        if let Type::Struct(Some(name), members) = ty
            && members.is_empty()
        {
            return Ok(structs.get(name).unwrap().clone());
        } else if let Type::Union(Some(name), members) = ty
            && members.is_empty()
        {
            return Ok(unions.get(name).unwrap().clone());
        }
        Ok(ty.clone())
    }

    /// Switches to a new block.
    fn switch_to_block(&mut self, block: Block) {
        self.builder.switch_to_block(block);
        self.current_block_state = BlockState::Empty;
    }

    /// Jumps to a block if the current block is not filled.
    fn jump_to_block(&mut self, block: Block) {
        if self.current_block_state != BlockState::Filled {
            self.builder.ins().jump(block, &[]);
            self.current_block_state = BlockState::Filled;
        }
    }

    /// Returns the alignment of a given type in bytes.
    pub(crate) fn get_type_alignment(&self, ty: &Type) -> u32 {
        Self::get_type_alignment_from_type(ty, self.structs, self.unions)
    }

    /// Returns the size of a given type in bytes.
    pub(crate) fn get_type_size(&self, ty: &Type) -> u32 {
        Self::get_type_size_from_type(ty, self.structs, self.unions)
    }

    /// Translates a typed statement into Cranelift IR.
    pub(crate) fn translate_typed_stmt(&mut self, stmt: TypedStmt) -> Result<bool, CodegenError> {
        // If the current block is already terminated, only process labels to create their blocks
        if self.current_block_state == BlockState::Filled && !matches!(stmt, TypedStmt::Label(..)) {
            return Ok(true);
        }

        match stmt {
            TypedStmt::Return(expr) => {
                let (value, ty) = self.translate_typed_expr(expr)?;
                if ty.is_record() {
                    let dest = self
                        .builder
                        .block_params(self.builder.current_block().unwrap())[0];
                    let src = value;
                    let size = self.get_type_size(&ty);
                    self.builder.emit_small_memory_copy(
                        self.module.target_config(),
                        dest,
                        src,
                        size as u64,
                        1,
                        1,
                        true,
                        MemFlags::new(),
                    );
                    self.builder.ins().return_(&[dest]);
                } else {
                    self.builder.ins().return_(&[value]);
                }
                self.current_block_state = BlockState::Filled;
                Ok(true)
            }
            TypedStmt::Declaration(_, declarators, is_static) => {
                for declarator in declarators {
                    if is_static {
                        let mangled_name = format!(
                            "{}.{}",
                            self.current_function_name.as_str(),
                            declarator.name.as_str()
                        );
                        let id = self
                            .module
                            .declare_data(&mangled_name, Linkage::Local, true, false)
                            .unwrap();
                        self.static_local_variables
                            .insert(declarator.name, (id, declarator.ty.clone()));

                        let mut data_desc = cranelift_module::DataDescription::new();

                        let size = self.get_type_size(&declarator.ty);
                        let initial_value = if let Some(init) = &declarator.initializer {
                            if let TypedInitializer::Expr(expr) = init {
                                if let TypedExpr::Number(num, _) = **expr {
                                    num.to_le_bytes().to_vec()
                                } else {
                                    return Err(CodegenError::InvalidStaticInitializer);
                                }
                            } else {
                                return Err(CodegenError::InvalidStaticInitializer);
                            }
                        } else {
                            vec![0; size as usize]
                        };

                        data_desc.define(initial_value.into_boxed_slice());
                        self.module.define_data(id, &data_desc).unwrap();
                    } else {
                        let ty = &declarator.ty;
                        let size = self.get_type_size(ty);
                        let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                            StackSlotKind::ExplicitSlot,
                            size,
                            0,
                        ));
                        self.variables
                            .insert(declarator.name, (None, Some(slot), ty.clone()));
                        if let Some(initializer) = &declarator.initializer {
                            let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                            self.translate_initializer(addr, ty, initializer)?;
                        } else {
                            // Initialize to zero for scalars
                            if ty.is_aggregate() == false {
                                let zero = self.builder.ins().iconst(types::I64, 0);
                                self.builder.ins().stack_store(zero, slot, 0);
                            }
                        }
                    }
                }
                Ok(false)
            }
            TypedStmt::Block(stmts) => {
                self.variables.enter_scope();
                let mut terminated = false;
                for stmt in stmts {
                    let term = self.translate_typed_stmt(stmt)?;
                    terminated = term;
                }
                self.variables.exit_scope();
                Ok(terminated)
            }
            TypedStmt::If(cond, then, otherwise) => {
                let (condition_value, _) = self.translate_typed_expr(cond)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(condition_value, then_block, &[], else_block, &[]);

                self.switch_to_block(then_block);
                let then_terminated = self.translate_typed_stmt(*then)?;
                if !then_terminated {
                    self.jump_to_block(merge_block);
                }

                self.switch_to_block(else_block);
                let mut else_terminated = false;
                if let Some(otherwise) = otherwise {
                    else_terminated = self.translate_typed_stmt(*otherwise)?;
                }

                if !else_terminated {
                    self.jump_to_block(merge_block);
                }

                if !then_terminated || !else_terminated {
                    self.switch_to_block(merge_block);
                }

                Ok(then_terminated && else_terminated)
            }
            TypedStmt::While(cond, body) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                let (cond_val, _) = self.translate_typed_expr(cond)?;
                self.builder
                    .ins()
                    .brif(cond_val, body_block, &[], exit_block, &[]);

                self.switch_to_block(body_block);

                self.loop_context.push((header_block, exit_block));
                self.translate_typed_stmt(*body)?;
                self.loop_context.pop();

                self.jump_to_block(header_block);

                self.switch_to_block(exit_block);

                Ok(false)
            }
            TypedStmt::Break => {
                let (_, exit_block) = self.loop_context.last().unwrap();
                self.jump_to_block(*exit_block);
                Ok(true)
            }
            TypedStmt::Continue => {
                let (header_block, _) = self.loop_context.last().unwrap();
                self.jump_to_block(*header_block);
                Ok(true)
            }
            TypedStmt::For(init, cond, inc, body) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let inc_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.variables.enter_scope();
                if let Some(init) = *init {
                    match init {
                        TypedForInit::Declaration(ty, name, initializer) => {
                            let size = self.get_type_size(&ty);
                            let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                                StackSlotKind::ExplicitSlot,
                                size,
                                0,
                            ));
                            self.variables.insert(name, (None, Some(slot), ty.clone()));
                            if let Some(init) = initializer {
                                let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                                self.translate_initializer(addr, &ty, &init)?;
                            } else if ty.is_aggregate() {
                                let val = self.builder.ins().iconst(types::I64, 0);
                                self.builder.ins().stack_store(val, slot, 0);
                            };
                        }
                        TypedForInit::Expr(expr) => {
                            let _ = self.translate_typed_expr(expr);
                        }
                    }
                }

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                if let Some(cond) = *cond {
                    let (cond_val, _) = self.translate_typed_expr(cond)?;
                    self.builder
                        .ins()
                        .brif(cond_val, body_block, &[], exit_block, &[]);
                } else {
                    self.jump_to_block(body_block);
                }

                self.switch_to_block(body_block);
                self.loop_context.push((inc_block, exit_block));
                self.translate_typed_stmt(*body)?;
                self.loop_context.pop();

                self.jump_to_block(inc_block);
                self.switch_to_block(inc_block);

                if let Some(inc) = *inc {
                    self.translate_typed_expr(inc)?;
                }

                self.jump_to_block(header_block);

                self.switch_to_block(exit_block);

                self.variables.exit_scope();
                Ok(false)
            }
            TypedStmt::Expr(expr) => {
                self.translate_typed_expr(expr)?;
                Ok(false)
            }
            TypedStmt::Empty => Ok(false),
            TypedStmt::DoWhile(body, cond) => {
                let header_block = self.builder.create_block();
                let cond_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                self.loop_context.push((cond_block, exit_block));
                self.translate_typed_stmt(*body)?;
                self.loop_context.pop();

                self.jump_to_block(cond_block);

                self.switch_to_block(cond_block);

                let (cond_val, _) = self.translate_typed_expr(cond)?;
                self.builder
                    .ins()
                    .brif(cond_val, header_block, &[], exit_block, &[]);

                self.switch_to_block(exit_block);

                Ok(false)
            }
            TypedStmt::Switch(cond, body) => {
                let (cond_val, _) = self.translate_typed_expr(cond)?;
                let exit_block = self.builder.create_block();
                let mut case_blocks = HashMap::new();
                let mut default_block = None;

                // Pass 1: Collect cases and create blocks
                if let TypedStmt::Block(stmts) = &*body {
                    for stmt in stmts {
                        match stmt {
                            TypedStmt::Case(expr, _) => {
                                if let TypedExpr::Number(val, _) = expr {
                                    let block = self.builder.create_block();
                                    case_blocks.insert(*val, block);
                                }
                            }
                            TypedStmt::Default(_) => {
                                if default_block.is_none() {
                                    let block = self.builder.create_block();
                                    default_block = Some(block);
                                }
                            }
                            _ => {}
                        }
                    }
                }

                // Emit the switch instruction
                let mut switch = cranelift_frontend::Switch::new();
                for (val, block) in &case_blocks {
                    switch.set_entry(*val as u128, *block);
                }
                let final_default_block = default_block.unwrap_or(exit_block);
                switch.emit(&mut self.builder, cond_val, final_default_block);
                self.current_block_state = BlockState::Filled;

                // Pass 2: Translate the statement bodies
                if let TypedStmt::Block(stmts) = *body {
                    self.loop_context.push((exit_block, exit_block)); // for break
                                                                       // The block before the switch's inner statements is terminated by the switch instruction.
                    let mut current_block_is_terminated = true;

                    for stmt in stmts {
                        match stmt {
                            TypedStmt::Case(expr, inner_stmt) => {
                                let val = if let TypedExpr::Number(val, _) = expr {
                                    val
                                } else {
                                    // This should be caught by the semantic analyzer
                                    unreachable!("Case expression must be a constant integer")
                                };
                                let block = case_blocks[&val];

                                if !current_block_is_terminated {
                                    self.jump_to_block(block);
                                }

                                self.switch_to_block(block);
                                self.builder.seal_block(block);

                                current_block_is_terminated =
                                    self.translate_typed_stmt(*inner_stmt)?;
                            }
                            TypedStmt::Default(inner_stmt) => {
                                let block = default_block.unwrap();
                                if !current_block_is_terminated {
                                    self.jump_to_block(block);
                                }

                                self.switch_to_block(block);
                                self.builder.seal_block(block);

                                current_block_is_terminated =
                                    self.translate_typed_stmt(*inner_stmt)?;
                            }
                            _ => {
                                // This handles statements that are not directly inside a case/default
                                // but are inside the switch block.
                                if !current_block_is_terminated {
                                    current_block_is_terminated = self.translate_typed_stmt(stmt)?;
                                }
                            }
                        }
                    }

                    if !current_block_is_terminated {
                        self.jump_to_block(exit_block);
                    }
                    self.loop_context.pop();
                }

                self.switch_to_block(exit_block);
                self.builder.seal_block(exit_block);
                Ok(false)
            }
            TypedStmt::Case(_, _) => Ok(false),
            TypedStmt::Default(_) => Ok(false),
            TypedStmt::Label(name, body) => {
                let block = *self
                    .label_blocks
                    .entry(name)
                    .or_insert_with(|| self.builder.create_block());

                self.switch_to_block(block);

                // Handle consecutive labels by making them share the same block
                let mut current_body = body;
                let mut labels_to_update = vec![name];
                while let TypedStmt::Label(ref inner_name, ref inner_body) = *current_body {
                    labels_to_update.push(*inner_name);
                    current_body = inner_body.clone();
                }

                // Update all consecutive labels to point to the same block
                for label_name in labels_to_update {
                    self.label_blocks.insert(label_name, block);
                }

                let terminated = self.translate_typed_stmt(*current_body)?;
                Ok(terminated)
            }
            TypedStmt::Goto(name) => {
                let block = *self
                    .label_blocks
                    .entry(name)
                    .or_insert_with(|| self.builder.create_block());

                if self.current_block_state != BlockState::Filled {
                    self.builder.ins().jump(block, &[]);
                    self.current_block_state = BlockState::Filled;
                }

                Ok(true)
            }
            TypedStmt::FunctionDeclaration { .. } => Ok(false),
            TypedStmt::StaticAssert(_, _) => Ok(false),
        }
    }

    /// Resolves the real type of a struct.
    fn get_real_type(&self, ty: &Type) -> Result<Type, CodegenError> {
        Self::get_real_type_from_type(ty, self.structs, self.unions)
    }

    /// Translates an expression into a Cranelift `Value`.
    fn translate_lvalue(&mut self, expr: TypedExpr) -> Result<(Value, Type), CodegenError> {
        match expr {
            TypedExpr::Variable(name, _, ty) => {
                if let Some((_var_opt, slot_opt, _)) = self.variables.get(&name) {
                    if let Some(slot) = slot_opt {
                        let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                        Ok((addr, ty))
                    } else {
                        Err(CodegenError::InvalidLValue)
                    }
                } else if let Some((id, _)) = self.static_local_variables.get(&name) {
                    let local_id = self.module.declare_data_in_func(*id, self.builder.func);
                    let addr = self.builder.ins().global_value(types::I64, local_id);
                    Ok((addr, ty.clone()))
                } else {
                    let (id, _) = self.global_variables.get(&name).unwrap();
                    let local_id = self.module.declare_data_in_func(*id, self.builder.func);
                    let addr = self.builder.ins().global_value(types::I64, local_id);
                    Ok((addr, ty.clone()))
                }
            }
            TypedExpr::Deref(ptr, ty) => {
                let (ptr, _) = self.translate_typed_expr(*ptr)?;
                Ok((ptr, ty))
            }
            TypedExpr::Member(expr, member, _ty) => {
                let (ptr, expr_ty) = self.translate_typed_expr(*expr)?;
                let s = self.get_real_type(&expr_ty)?;
                if let Type::Struct(_, members) = s {
                    let mut offset = 0;
                    let mut member_ty = None;
                    for m in &members {
                        let member_alignment = self.get_type_alignment(&m.ty);
                        offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                        if m.name == member {
                            member_ty = Some(m.ty.clone());
                            break;
                        }
                        offset += self.get_type_size(&m.ty);
                    }
                    let member_ty = member_ty.unwrap();
                    let member_addr = self.builder.ins().iadd_imm(ptr, offset as i64);
                    Ok((member_addr, member_ty))
                } else if let Type::Union(_, members) = s {
                    let member_ty = members
                        .iter()
                        .find(|m| m.name == member)
                        .map(|m| m.ty.clone())
                        .unwrap();
                    Ok((ptr, member_ty))
                } else {
                    Err(CodegenError::NotAStruct)
                }
            }
            _ => Err(CodegenError::InvalidLValue),
        }
    }

    fn integer_promotion(&self, ty: &Type) -> Type {
        match ty {
            Type::Char | Type::Short | Type::Bool | Type::UnsignedChar | Type::UnsignedShort => {
                Type::Int
            }
            _ => ty.clone(),
        }
    }

    fn usual_arithmetic_conversions(&mut self, left_ty: &Type, right_ty: &Type) -> Type {
        let left_ty = self.integer_promotion(left_ty);
        let right_ty = self.integer_promotion(right_ty);

        if left_ty == right_ty {
            return left_ty;
        }

        if left_ty.is_unsigned() == right_ty.is_unsigned() {
            if left_ty.get_integer_rank() > right_ty.get_integer_rank() {
                return left_ty;
            } else {
                return right_ty;
            }
        }

        let (unsigned_ty, signed_ty) = if left_ty.is_unsigned() {
            (left_ty, right_ty)
        } else {
            (right_ty, left_ty)
        };

        if unsigned_ty.get_integer_rank() >= signed_ty.get_integer_rank() {
            return unsigned_ty;
        }

        if self.get_type_size(&signed_ty) >= self.get_type_size(&unsigned_ty) {
            return signed_ty;
        }

        match signed_ty {
            Type::Int => Type::UnsignedInt,
            Type::Long => Type::UnsignedLong,
            Type::LongLong => Type::UnsignedLongLong,
            _ => unsigned_ty,
        }
    }

    fn load_variable(&mut self, slot: StackSlot, ty: &Type) -> Value {
        let is_volatile = matches!(ty, Type::Volatile(_));
        if is_volatile {
            self.builder.ins().fence();
        }
        let value = match ty.unwrap_volatile() {
            Type::Char | Type::Bool => {
                let val = self.builder.ins().stack_load(types::I8, slot, 0);
                self.builder.ins().sextend(types::I64, val)
            }
            Type::UnsignedChar => {
                let val = self.builder.ins().stack_load(types::I8, slot, 0);
                self.builder.ins().uextend(types::I64, val)
            }
            Type::Short => {
                let val = self.builder.ins().stack_load(types::I16, slot, 0);
                self.builder.ins().sextend(types::I64, val)
            }
            Type::UnsignedShort => {
                let val = self.builder.ins().stack_load(types::I16, slot, 0);
                self.builder.ins().uextend(types::I64, val)
            }
            Type::Float => self.builder.ins().stack_load(types::F32, slot, 0),
            Type::Double => self.builder.ins().stack_load(types::F64, slot, 0),
            _ => self.builder.ins().stack_load(types::I64, slot, 0),
        };
        if is_volatile {
            self.builder.ins().fence();
        }
        value
    }

    fn load_lvalue(&mut self, addr: Value, ty: &Type) -> Value {
        let is_volatile = matches!(ty, Type::Volatile(_));
        if is_volatile {
            self.builder.ins().fence();
        }
        let flags = MemFlags::new();
        let value = match ty.unwrap_volatile() {
            Type::Char | Type::Bool => {
                let val = self.builder.ins().load(types::I8, flags, addr, 0);
                self.builder.ins().sextend(types::I64, val)
            }
            Type::UnsignedChar => {
                let val = self.builder.ins().load(types::I8, flags, addr, 0);
                self.builder.ins().uextend(types::I64, val)
            }
            Type::Short => {
                let val = self.builder.ins().load(types::I16, flags, addr, 0);
                self.builder.ins().sextend(types::I64, val)
            }
            Type::UnsignedShort => {
                let val = self.builder.ins().load(types::I16, flags, addr, 0);
                self.builder.ins().uextend(types::I64, val)
            }
            Type::Float => self.builder.ins().load(types::F32, flags, addr, 0),
            Type::Double => self.builder.ins().load(types::F64, flags, addr, 0),
            _ => self.builder.ins().load(types::I64, flags, addr, 0),
        };
        if is_volatile {
            self.builder.ins().fence();
        }
        value
    }

    fn translate_assign_expr(
        &mut self,
        op: AssignOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        ty: &Type,
    ) -> Result<(Value, Type), CodegenError> {
        let (addr, lhs_ty) = self.translate_lvalue(lhs.clone())?;
        let (rhs_val, _) = self.translate_typed_expr(rhs.clone())?;

        let lhs_val = self.load_lvalue(addr, &lhs_ty);
        let result_val = match op {
            AssignOp::Assign => rhs_val,
            AssignOp::Add => {
                if lhs_ty.is_floating() {
                    self.builder.ins().fadd(lhs_val, rhs_val)
                } else {
                    self.builder.ins().iadd(lhs_val, rhs_val)
                }
            }
            AssignOp::Sub => {
                if lhs_ty.is_floating() {
                    self.builder.ins().fsub(lhs_val, rhs_val)
                } else {
                    self.builder.ins().isub(lhs_val, rhs_val)
                }
            }
            AssignOp::Mul => {
                if lhs_ty.is_floating() {
                    self.builder.ins().fmul(lhs_val, rhs_val)
                } else {
                    self.builder.ins().imul(lhs_val, rhs_val)
                }
            }
            AssignOp::Div => {
                if lhs_ty.is_floating() {
                    self.builder.ins().fdiv(lhs_val, rhs_val)
                } else {
                    self.builder.ins().sdiv(lhs_val, rhs_val)
                }
            }
            AssignOp::Mod => self.builder.ins().srem(lhs_val, rhs_val),
            AssignOp::BitwiseAnd => self.builder.ins().band(lhs_val, rhs_val),
            AssignOp::BitwiseOr => self.builder.ins().bor(lhs_val, rhs_val),
            AssignOp::BitwiseXor => self.builder.ins().bxor(lhs_val, rhs_val),
            AssignOp::LeftShift => self.builder.ins().ishl(lhs_val, rhs_val),
            AssignOp::RightShift => self.builder.ins().sshr(lhs_val, rhs_val),
        };
        let is_volatile = matches!(lhs_ty, Type::Volatile(_));
        if is_volatile {
            self.builder.ins().fence();
        }
        self.builder
            .ins()
            .store(MemFlags::new(), result_val, addr, 0);
        if is_volatile {
            self.builder.ins().fence();
        }
        Ok((result_val, ty.clone()))
    }

    fn translate_binary_op(
        &mut self,
        op: BinOp,
        lhs: &TypedExpr,
        rhs: &TypedExpr,
        ty: &Type,
    ) -> Result<(Value, Type), CodegenError> {
        // Assignment operators are now handled by translate_assign_expr
        match op {
            BinOp::Add => {
                let (lhs_val, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs_val, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result_val = match (&lhs_ty, &rhs_ty) {
                    (Type::Pointer(base_ty), Type::Int) => {
                        let size = self.get_type_size(base_ty);
                        let offset = self.builder.ins().imul_imm(rhs_val, size as i64);
                        self.builder.ins().iadd(lhs_val, offset)
                    }
                    (Type::Int, Type::Pointer(base_ty)) => {
                        let size = self.get_type_size(base_ty);
                        let offset = self.builder.ins().imul_imm(lhs_val, size as i64);
                        self.builder.ins().iadd(rhs_val, offset)
                    }
                    (Type::Float, Type::Float) => self.builder.ins().fadd(lhs_val, rhs_val),
                    (Type::Double, Type::Double) => self.builder.ins().fadd(lhs_val, rhs_val),
                    _ => self.builder.ins().iadd(lhs_val, rhs_val),
                };
                let _result_ty = if lhs_ty.is_pointer() {
                    lhs_ty
                } else {
                    common_ty
                };
                Ok((result_val, ty.clone()))
            }
            BinOp::Sub => {
                let (lhs_val, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs_val, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result_val = match (&lhs_ty, &rhs_ty) {
                    (Type::Pointer(base_ty), Type::Int) => {
                        let size = self.get_type_size(base_ty);
                        let offset = self.builder.ins().imul_imm(rhs_val, size as i64);
                        self.builder.ins().isub(lhs_val, offset)
                    }
                    (Type::Pointer(lhs_base), Type::Pointer(rhs_base)) if lhs_base == rhs_base => {
                        let diff = self.builder.ins().isub(lhs_val, rhs_val);
                        let size = self.get_type_size(lhs_base);
                        self.builder.ins().sdiv_imm(diff, size as i64)
                    }
                    (Type::Float, Type::Float) => self.builder.ins().fsub(lhs_val, rhs_val),
                    (Type::Double, Type::Double) => self.builder.ins().fsub(lhs_val, rhs_val),
                    _ => self.builder.ins().isub(lhs_val, rhs_val),
                };
                let result_ty = match (&lhs_ty, &rhs_ty) {
                    (Type::Pointer(_), Type::Pointer(_)) => Type::Int,
                    (Type::Pointer(_), Type::Int) => lhs_ty,
                    _ => common_ty,
                };
                Ok((result_val, result_ty))
            }
            BinOp::Mul => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result = if common_ty.is_floating() {
                    self.builder.ins().fmul(lhs, rhs)
                } else {
                    self.builder.ins().imul(lhs, rhs)
                };
                Ok((result, ty.clone()))
            }
            BinOp::Div => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result = if common_ty.is_floating() {
                    self.builder.ins().fdiv(lhs, rhs)
                } else if common_ty.is_unsigned() {
                    self.builder.ins().udiv(lhs, rhs)
                } else {
                    self.builder.ins().sdiv(lhs, rhs)
                };
                Ok((result, ty.clone()))
            }
            BinOp::Mod => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result = if common_ty.is_unsigned() {
                    self.builder.ins().urem(lhs, rhs)
                } else {
                    self.builder.ins().srem(lhs, rhs)
                };
                Ok((result, ty.clone()))
            }
            BinOp::Equal => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let c = if common_ty.is_floating() {
                    self.builder.ins().fcmp(FloatCC::Equal, lhs, rhs)
                } else {
                    self.builder.ins().icmp(IntCC::Equal, lhs, rhs)
                };
                Ok((self.builder.ins().uextend(types::I64, c), ty.clone()))
            }
            BinOp::NotEqual => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let c = if common_ty.is_floating() {
                    self.builder.ins().fcmp(FloatCC::NotEqual, lhs, rhs)
                } else {
                    self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs)
                };
                Ok((self.builder.ins().uextend(types::I64, c), ty.clone()))
            }
            BinOp::LessThan => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let c = if common_ty.is_floating() {
                    self.builder.ins().fcmp(FloatCC::LessThan, lhs, rhs)
                } else {
                    let cc = if common_ty.is_unsigned() {
                        IntCC::UnsignedLessThan
                    } else {
                        IntCC::SignedLessThan
                    };
                    self.builder.ins().icmp(cc, lhs, rhs)
                };
                Ok((self.builder.ins().uextend(types::I64, c), ty.clone()))
            }
            BinOp::GreaterThan => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let c = if common_ty.is_floating() {
                    self.builder.ins().fcmp(FloatCC::GreaterThan, lhs, rhs)
                } else {
                    let cc = if common_ty.is_unsigned() {
                        IntCC::UnsignedGreaterThan
                    } else {
                        IntCC::SignedGreaterThan
                    };
                    self.builder.ins().icmp(cc, lhs, rhs)
                };
                Ok((self.builder.ins().uextend(types::I64, c), ty.clone()))
            }
            BinOp::LessThanOrEqual => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let c = if common_ty.is_floating() {
                    self.builder.ins().fcmp(FloatCC::LessThanOrEqual, lhs, rhs)
                } else {
                    let cc = if common_ty.is_unsigned() {
                        IntCC::UnsignedLessThanOrEqual
                    } else {
                        IntCC::SignedLessThanOrEqual
                    };
                    self.builder.ins().icmp(cc, lhs, rhs)
                };
                Ok((self.builder.ins().uextend(types::I64, c), ty.clone()))
            }
            BinOp::GreaterThanOrEqual => {
                let (lhs, lhs_ty) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, rhs_ty) = self.translate_typed_expr(rhs.clone())?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let c = if common_ty.is_floating() {
                    self.builder
                        .ins()
                        .fcmp(FloatCC::GreaterThanOrEqual, lhs, rhs)
                } else {
                    let cc = if common_ty.is_unsigned() {
                        IntCC::UnsignedGreaterThanOrEqual
                    } else {
                        IntCC::SignedGreaterThanOrEqual
                    };
                    self.builder.ins().icmp(cc, lhs, rhs)
                };
                Ok((self.builder.ins().uextend(types::I64, c), ty.clone()))
            }
            BinOp::LogicalAnd => {
                let (lhs_val, _) = self.translate_typed_expr(lhs.clone())?;
                let rhs_block = self.builder.create_block();
                let true_block = self.builder.create_block();
                let false_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                self.builder.append_block_param(merge_block, types::I64);
                self.builder
                    .ins()
                    .brif(lhs_val, rhs_block, &[], false_block, &[]);
                self.switch_to_block(rhs_block);
                self.builder.seal_block(rhs_block);
                let (rhs_val, _) = self.translate_typed_expr(rhs.clone())?;
                self.builder
                    .ins()
                    .brif(rhs_val, true_block, &[], false_block, &[]);
                self.switch_to_block(true_block);
                self.builder.seal_block(true_block);
                let one = self.builder.ins().iconst(types::I64, 1);
                self.builder.ins().jump(merge_block, &[one.into()]);
                self.switch_to_block(false_block);
                self.builder.seal_block(false_block);
                let zero = self.builder.ins().iconst(types::I64, 0);
                self.builder.ins().jump(merge_block, &[zero.into()]);
                self.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
                Ok((self.builder.block_params(merge_block)[0], ty.clone()))
            }
            BinOp::LogicalOr => {
                let (lhs_val, _) = self.translate_typed_expr(lhs.clone())?;
                let rhs_block = self.builder.create_block();
                let true_block = self.builder.create_block();
                let false_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                self.builder.append_block_param(merge_block, types::I64);
                self.builder
                    .ins()
                    .brif(lhs_val, true_block, &[], rhs_block, &[]);
                self.switch_to_block(rhs_block);
                self.builder.seal_block(rhs_block);
                let (rhs_val, _) = self.translate_typed_expr(rhs.clone())?;
                self.builder
                    .ins()
                    .brif(rhs_val, true_block, &[], false_block, &[]);
                self.switch_to_block(true_block);
                self.builder.seal_block(true_block);
                let one = self.builder.ins().iconst(types::I64, 1);
                self.builder.ins().jump(merge_block, &[one.into()]);
                self.switch_to_block(false_block);
                self.builder.seal_block(false_block);
                let zero = self.builder.ins().iconst(types::I64, 0);
                self.builder.ins().jump(merge_block, &[zero.into()]);
                self.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);
                Ok((self.builder.block_params(merge_block)[0], ty.clone()))
            }
            BinOp::BitwiseOr => {
                let (lhs, _) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, _) = self.translate_typed_expr(rhs.clone())?;
                Ok((self.builder.ins().bor(lhs, rhs), ty.clone()))
            }
            BinOp::BitwiseXor => {
                let (lhs, _) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, _) = self.translate_typed_expr(rhs.clone())?;
                Ok((self.builder.ins().bxor(lhs, rhs), ty.clone()))
            }
            BinOp::BitwiseAnd => {
                let (lhs, _) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, _) = self.translate_typed_expr(rhs.clone())?;
                Ok((self.builder.ins().band(lhs, rhs), ty.clone()))
            }
            BinOp::LeftShift => {
                let (lhs, _) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, _) = self.translate_typed_expr(rhs.clone())?;
                Ok((self.builder.ins().ishl(lhs, rhs), ty.clone()))
            }
            BinOp::RightShift => {
                let (lhs, _) = self.translate_typed_expr(lhs.clone())?;
                let (rhs, _) = self.translate_typed_expr(rhs.clone())?;
                Ok((self.builder.ins().sshr(lhs, rhs), ty.clone()))
            }
            BinOp::Comma => {
                self.translate_typed_expr(lhs.clone())?;
                self.translate_typed_expr(rhs.clone())
            }
        }
    }

    fn translate_typed_expr(&mut self, expr: TypedExpr) -> Result<(Value, Type), CodegenError> {
        if let Some((assign_op, lhs, rhs)) = expr.get_assign_expr() {
            return self.translate_assign_expr(assign_op, lhs, rhs, expr.ty());
        }

        if let Some((op, lhs, rhs)) = expr.get_binary_expr() {
            return self.translate_binary_op(op, lhs, rhs, expr.ty());
        }

        match expr {
            TypedExpr::Number(n, ty) => Ok((self.builder.ins().iconst(types::I64, n), ty)),
            TypedExpr::FloatNumber(n, ty) => Ok((self.builder.ins().f64const(n), ty)),
            TypedExpr::String(s, ty) => {
                let string_value = s.as_str();
                let unescaped = unescape(string_value);
                let mut data = Vec::with_capacity(unescaped.len() + 1);
                data.extend_from_slice(&unescaped);
                data.push(0); // Null terminator

                // Create a unique name for the string literal to avoid collisions
                let name = format!(".L.str{}", self.anonymous_string_count);
                *self.anonymous_string_count += 1;

                let id = self
                    .module
                    .declare_data(&name, Linkage::Local, false, false)
                    .unwrap();
                let mut data_desc = cranelift_module::DataDescription::new();
                data_desc.define(data.into_boxed_slice());
                self.module.define_data(id, &data_desc).unwrap();

                let local_id = self.module.declare_data_in_func(id, self.builder.func);
                Ok((self.builder.ins().global_value(types::I64, local_id), ty))
            }
            TypedExpr::Char(c, ty) => {
                let char_value = c.as_str();
                let character = char_value.chars().next().unwrap();
                let val = self.builder.ins().iconst(types::I64, character as i64);
                Ok((val, ty))
            }
            TypedExpr::PointerMember(expr, member, _ty) => {
                let (ptr, ptr_ty) = self.translate_typed_expr(*expr)?;
                if let Type::Pointer(base_ty) = ptr_ty {
                    let s = self.get_real_type(&base_ty)?;
                    if let Type::Struct(_, members) = s {
                        let mut offset = 0;
                        let mut member_ty = None;
                        for m in &members {
                            let member_alignment = self.get_type_alignment(&m.ty);
                            offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                            if m.name == member {
                                member_ty = Some(m.ty.clone());
                                break;
                            }
                            offset += self.get_type_size(&m.ty);
                        }
                        let member_ty = member_ty.unwrap();
                        let member_addr = self.builder.ins().iadd_imm(ptr, offset as i64);

                        if member_ty.is_aggregate() {
                            Ok((member_addr, member_ty))
                        } else {
                            Ok((
                                self.builder.ins().load(
                                    types::I64,
                                    MemFlags::new(),
                                    member_addr,
                                    0,
                                ),
                                member_ty,
                            ))
                        }
                    } else if let Type::Union(_, members) = s {
                        let member_ty = members
                            .iter()
                            .find(|m| m.name == member)
                            .map(|m| m.ty.clone())
                            .unwrap();
                        Ok((
                            self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0),
                            member_ty,
                        ))
                    } else {
                        Err(CodegenError::NotAStruct)
                    }
                } else {
                    Err(CodegenError::NotAPointer)
                }
            }
            TypedExpr::ImplicitCast(ty, expr, result_ty) => {
                let (val, expr_ty) = self.translate_typed_expr(*expr)?;
                if *ty == Type::Bool {
                    let zero = self.builder.ins().iconst(types::I64, 0);
                    let is_not_zero = self.builder.ins().icmp(IntCC::NotEqual, val, zero);
                    let bool_as_i64 = self.builder.ins().uextend(types::I64, is_not_zero);
                    return Ok((bool_as_i64, result_ty));
                }

                let cast_val = if ty.is_floating() && expr_ty.is_floating() {
                    // float <-> double
                    if *ty == Type::Double && expr_ty.unwrap_const() == &Type::Float {
                        self.builder.ins().fpromote(types::F64, val)
                    } else if *ty == Type::Float && expr_ty.unwrap_const() == &Type::Double {
                        self.builder.ins().fdemote(types::F32, val)
                    } else {
                        val
                    }
                } else if ty.is_floating() && !expr_ty.is_floating() {
                    // int -> float
                    let target_ty = if *ty == Type::Float {
                        types::F32
                    } else {
                        types::F64
                    };
                    if expr_ty.is_unsigned() {
                        self.builder.ins().fcvt_from_uint(target_ty, val)
                    } else {
                        self.builder.ins().fcvt_from_sint(target_ty, val)
                    }
                } else if !ty.is_floating() && expr_ty.is_floating() {
                    // float -> int
                    let target_ty = match ty.unwrap_const() {
                        Type::Char | Type::UnsignedChar | Type::Bool => types::I8,
                        Type::Short | Type::UnsignedShort => types::I16,
                        _ => types::I64,
                    };
                    let converted = if ty.is_unsigned() {
                        self.builder.ins().fcvt_to_uint_sat(target_ty, val)
                    } else {
                        self.builder.ins().fcvt_to_sint_sat(target_ty, val)
                    };

                    if target_ty != types::I64 {
                        if ty.is_unsigned() {
                            self.builder.ins().uextend(types::I64, converted)
                        } else {
                            self.builder.ins().sextend(types::I64, converted)
                        }
                    } else {
                        converted
                    }
                } else {
                    val
                };

                Ok((cast_val, result_ty))
            }
            TypedExpr::Member(expr, member, _ty) => {
                let (ptr, ty) = self.translate_typed_expr(*expr)?;
                let s = self.get_real_type(&ty)?;
                if let Type::Struct(_, members) = s {
                    let mut offset = 0;
                    let mut member_ty = None;
                    for m in &members {
                        let member_alignment = self.get_type_alignment(&m.ty);
                        offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                        if m.name == member {
                            member_ty = Some(m.ty.clone());
                            break;
                        }
                        offset += self.get_type_size(&m.ty);
                    }
                    let member_ty = member_ty.unwrap();
                    let member_addr = self.builder.ins().iadd_imm(ptr, offset as i64);

                    if member_ty.is_aggregate() {
                        Ok((member_addr, member_ty))
                    } else {
                        Ok((
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::new(), member_addr, 0),
                            member_ty,
                        ))
                    }
                } else if let Type::Union(_, members) = s {
                    let member_ty = members
                        .iter()
                        .find(|m| m.name == member)
                        .map(|m| m.ty.clone())
                        .unwrap();
                    Ok((
                        self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0),
                        member_ty,
                    ))
                } else {
                    Err(CodegenError::NotAStruct)
                }
            }
            TypedExpr::ExplicitCast(ty, expr, result_ty) => {
                let (val, _) = self.translate_typed_expr(*expr)?;
                if *ty == Type::Bool {
                    let zero = self.builder.ins().iconst(types::I64, 0);
                    let is_not_zero = self.builder.ins().icmp(IntCC::NotEqual, val, zero);
                    let bool_as_i64 = self.builder.ins().uextend(types::I64, is_not_zero);
                    return Ok((bool_as_i64, result_ty));
                }
                let cast_val = match *ty {
                    Type::Char | Type::UnsignedChar => self.builder.ins().ireduce(types::I8, val),
                    Type::Short | Type::UnsignedShort => {
                        self.builder.ins().ireduce(types::I16, val)
                    }
                    _ => val,
                };

                let extended_val = match *ty {
                    Type::Char | Type::Short => self.builder.ins().sextend(types::I64, cast_val),
                    Type::UnsignedChar | Type::UnsignedShort => {
                        self.builder.ins().uextend(types::I64, cast_val)
                    }
                    _ => cast_val,
                };

                Ok((extended_val, result_ty))
            }
            TypedExpr::CompoundLiteral(_ty, initializer, result_ty) => {
                let size = self.get_type_size(&result_ty);
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size,
                    0,
                ));
                let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                self.translate_initializer(addr, &result_ty, &initializer)?;
                Ok((addr, result_ty))
            }
            TypedExpr::PreIncrement(expr, ty) => {
                let (addr, _) = self.translate_lvalue(*expr)?;
                let val = self.load_lvalue(addr, &ty);
                let one = self.builder.ins().iconst(types::I64, 1);
                let new_val = self.builder.ins().iadd(val, one);
                self.builder.ins().store(MemFlags::new(), new_val, addr, 0);
                Ok((new_val, ty))
            }
            TypedExpr::PreDecrement(expr, ty) => {
                let (addr, _) = self.translate_lvalue(*expr)?;
                let val = self.load_lvalue(addr, &ty);
                let one = self.builder.ins().iconst(types::I64, 1);
                let new_val = self.builder.ins().isub(val, one);
                self.builder.ins().store(MemFlags::new(), new_val, addr, 0);
                Ok((new_val, ty))
            }
            TypedExpr::PostIncrement(expr, ty) => {
                let (addr, _) = self.translate_lvalue(*expr)?;
                let val = self.load_lvalue(addr, &ty);
                let one = self.builder.ins().iconst(types::I64, 1);
                let new_val = self.builder.ins().iadd(val, one);
                self.builder.ins().store(MemFlags::new(), new_val, addr, 0);
                Ok((val, ty))
            }
            TypedExpr::PostDecrement(expr, ty) => {
                let (addr, _) = self.translate_lvalue(*expr)?;
                let val = self.load_lvalue(addr, &ty);
                let one = self.builder.ins().iconst(types::I64, 1);
                let new_val = self.builder.ins().isub(val, one);
                self.builder.ins().store(MemFlags::new(), new_val, addr, 0);
                Ok((val, ty))
            }
            TypedExpr::Ternary(cond, then_expr, else_expr, _ty) => {
                let (condition_value, _) = self.translate_typed_expr(*cond)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(condition_value, then_block, &[], else_block, &[]);

                self.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                let (then_value, ty) = self.translate_typed_expr(*then_expr)?;
                self.builder.ins().jump(merge_block, &[then_value.into()]);
                self.current_block_state = BlockState::Filled;

                self.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let (else_value, _) = self.translate_typed_expr(*else_expr)?;
                self.builder.ins().jump(merge_block, &[else_value.into()]);
                self.current_block_state = BlockState::Filled;

                self.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                self.builder.append_block_param(merge_block, types::I64);

                self.switch_to_block(merge_block);

                Ok((self.builder.block_params(merge_block)[0], ty))
            }
            TypedExpr::AddressOf(expr, ty) => {
                if let TypedExpr::Variable(name, _, _var_ty) = *expr {
                    if let Some((var_opt, slot_opt, _)) = self.variables.get(&name) {
                        if let Some(slot) = slot_opt {
                            let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                            Ok((addr, ty))
                        } else if let Some(_var) = var_opt {
                            // Can't take address of SSA variable
                            Err(CodegenError::InvalidLValue)
                        } else {
                            Err(CodegenError::InvalidLValue)
                        }
                    } else {
                        Err(CodegenError::InvalidLValue)
                    }
                } else if let TypedExpr::Deref(ptr_expr, _) = *expr {
                    self.translate_typed_expr(*ptr_expr)
                } else if let TypedExpr::Member(struct_expr, member_name, _) = *expr {
                    let (base_ptr, base_ty) = self.translate_typed_expr(*struct_expr)?;
                    let real_ty = self.get_real_type(&base_ty)?;

                    match real_ty {
                        Type::Struct(_, members) => {
                            let mut offset = 0;
                            let mut member_ty = None;
                            for m in members {
                                let member_alignment = self.get_type_alignment(&m.ty);
                                offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                                if m.name == member_name {
                                    member_ty = Some(m.ty.clone());
                                    break;
                                }
                                offset += self.get_type_size(&m.ty);
                            }
                            let member_addr = self.builder.ins().iadd_imm(base_ptr, offset as i64);
                            Ok((member_addr, Type::Pointer(Box::new(member_ty.unwrap()))))
                        }
                        Type::Union(_, members) => {
                            let member_ty = members
                                .iter()
                                .find(|m| m.name == member_name)
                                .map(|m| m.ty.clone())
                                .unwrap();
                            Ok((base_ptr, Type::Pointer(Box::new(member_ty))))
                        }
                        _ => Err(CodegenError::NotAStruct),
                    }
                } else if let TypedExpr::CompoundLiteral(literal_ty, initializer, _) = *expr {
                    let size = self.get_type_size(&literal_ty);
                    let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size,
                        0,
                    ));
                    let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                    self.translate_initializer(addr, &literal_ty, &initializer)?;
                    Ok((addr, ty))
                } else {
                    Err(CodegenError::InvalidLValue)
                }
            }
            TypedExpr::Sizeof(expr, ty) => {
                let (_, expr_ty) = self.translate_typed_expr(*expr)?;
                let size = self.get_type_size(&expr_ty) as i64;
                Ok((self.builder.ins().iconst(types::I64, size), ty))
            }
            TypedExpr::SizeofType(ty, result_ty) => {
                let size = self.get_type_size(&ty) as i64;
                Ok((self.builder.ins().iconst(types::I64, size), result_ty))
            }
            TypedExpr::Alignof(expr, ty) => {
                let (_, expr_ty) = self.translate_typed_expr(*expr)?;
                let align = self.get_type_alignment(&expr_ty) as i64;
                Ok((self.builder.ins().iconst(types::I64, align), ty))
            }
            TypedExpr::AlignofType(ty, result_ty) => {
                let align = self.get_type_alignment(&ty) as i64;
                Ok((self.builder.ins().iconst(types::I64, align), result_ty))
            }
            TypedExpr::Deref(expr, ty) => {
                let (ptr, _) = self.translate_typed_expr(*expr)?;
                if ty.is_aggregate() {
                    Ok((ptr, ty))
                } else {
                    Ok((
                        self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0),
                        ty,
                    ))
                }
            }
            TypedExpr::InitializerList(list, ty) => {
                let size = self.get_type_size(&ty);
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size,
                    0,
                ));
                let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                self.translate_initializer(addr, &ty, &TypedInitializer::List(list.clone()))?;
                Ok((addr, ty))
            }
            TypedExpr::LogicalNot(expr, ty) => {
                let (val, _) = self.translate_typed_expr(*expr)?;
                let zero = self.builder.ins().iconst(types::I64, 0);
                let c = self.builder.ins().icmp(IntCC::Equal, val, zero);
                Ok((self.builder.ins().uextend(types::I64, c), ty))
            }
            TypedExpr::Neg(expr, ty) => {
                let (val, _) = self.translate_typed_expr(*expr)?;
                Ok((self.builder.ins().ineg(val), ty))
            }
            TypedExpr::BitwiseNot(expr, ty) => {
                let (val, _) = self.translate_typed_expr(*expr)?;
                Ok((self.builder.ins().bnot(val), ty))
            }
            TypedExpr::Variable(name, _, ty) => {
                if let Some(val) = self.enum_constants.get(&name) {
                    return Ok((self.builder.ins().iconst(types::I64, *val), Type::Int));
                }
                if let Some((_var_opt, slot_opt, _)) = self.variables.get(&name) {
                    if let Some(slot) = slot_opt {
                        if ty.is_record() {
                            return Ok((self.builder.ins().stack_addr(types::I64, slot, 0), ty));
                        }
                        if let Type::Array(elem_ty, _) = &ty {
                            let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                            return Ok((addr, Type::Pointer(elem_ty.clone())));
                        }
                        let loaded_val = self.load_variable(slot, &ty);
                        Ok((loaded_val, ty))
                    } else {
                        Err(CodegenError::InvalidLValue)
                    }
                } else if let Some((id, _)) = self.static_local_variables.get(&name) {
                    let local_id = self.module.declare_data_in_func(*id, self.builder.func);
                    let addr = self.builder.ins().global_value(types::I64, local_id);
                    Ok((
                        self.builder
                            .ins()
                            .load(types::I64, MemFlags::new(), addr, 0),
                        ty,
                    ))
                } else {
                    let (id, ty) = self.global_variables.get(&name).unwrap();
                    let local_id = self.module.declare_data_in_func(*id, self.builder.func);
                    let addr = self.builder.ins().global_value(types::I64, local_id);
                    if ty.is_aggregate() {
                        Ok((addr, ty.clone()))
                    } else {
                        Ok((
                            self.builder
                                .ins()
                                .load(types::I64, MemFlags::new(), addr, 0),
                            ty.clone(),
                        ))
                    }
                }
            }
            TypedExpr::Call(name, args, _, ty) => {
                let (callee, ret_ty, is_variadic) = self
                    .functions
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| panic!("Undefined function: {}", name.as_str()));

                let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

                let mut arg_values = Vec::new();
                if ret_ty.is_record() {
                    let size = self.get_type_size(&ret_ty);
                    let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size,
                        0,
                    ));
                    let ptr = self.builder.ins().stack_addr(types::I64, slot, 0);
                    arg_values.push(ptr);
                }

                for arg in &args {
                    let (val, _) = self.translate_typed_expr(arg.clone())?;
                    arg_values.push(val);
                }

                let call = if is_variadic {
                    let mut sig = self.signatures.get(&name).unwrap().clone();
                    for arg in &args[sig.params.len()..] {
                        let abi_param = match arg.ty() {
                            Type::Float => AbiParam::new(types::F32),
                            Type::Double => AbiParam::new(types::F64),
                            _ => AbiParam::new(types::I64),
                        };
                        sig.params.push(abi_param);
                    }
                    let sig_ref = self.builder.func.import_signature(sig);
                    let callee_addr = self.builder.ins().func_addr(types::I64, local_callee);
                    self.builder
                        .ins()
                        .call_indirect(sig_ref, callee_addr, &arg_values)
                } else {
                    self.builder.ins().call(local_callee, &arg_values)
                };

                if ret_ty.is_record() {
                    let addr = self.builder.inst_results(call)[0];
                    return Ok((addr, ret_ty));
                }
                Ok((self.builder.inst_results(call)[0], ty))
            }
            _ => todo!(),
        }
    }

    /// Translates an initializer into a series of memory writes.
    fn translate_initializer(
        &mut self,
        base_addr: Value,
        ty: &Type,
        initializer: &TypedInitializer,
    ) -> CodegenResult<()> {
        match initializer {
            TypedInitializer::Expr(expr) => {
                if let TypedExpr::Comma(lhs, rhs, _) = *expr.clone() {
                    self.translate_initializer(base_addr, ty, &TypedInitializer::Expr(lhs))?;
                    if let Type::Array(elem_ty, _) = ty {
                        let elem_size = self.get_type_size(elem_ty);
                        let next_addr = self.builder.ins().iadd_imm(base_addr, elem_size as i64);
                        self.translate_initializer(next_addr, ty, &TypedInitializer::Expr(rhs))?;
                    }
                } else {
                    let (val, val_ty) = self.translate_typed_expr(*expr.clone())?;
                    if val_ty.is_record() {
                        let size = self.get_type_size(&val_ty);
                        self.builder.emit_small_memory_copy(
                            self.module.target_config(),
                            base_addr,
                            val,
                            size as u64,
                            self.get_type_alignment(&val_ty) as u8,
                            self.get_type_alignment(&val_ty) as u8,
                            true,
                            MemFlags::new(),
                        );
                    } else {
                        self.builder.ins().store(MemFlags::new(), val, base_addr, 0);
                    }
                }
            }
            TypedInitializer::List(list) => {
                let ty = self.get_real_type(ty)?;
                match ty {
                    Type::Struct(_, ref members) => {
                        let mut member_index = 0;
                        for (designators, initializer) in list {
                            let (offset, member_ty) = if !designators.is_empty() {
                                let mut current_offset = 0;
                                let mut current_ty = ty.clone();
                                for designator in designators {
                                    match designator {
                                        TypedDesignator::Member(name) => {
                                            let s = self.get_real_type(&current_ty)?;
                                            if let Type::Struct(_, members) = s {
                                                let mut found = false;
                                                for (i, member) in members.iter().enumerate() {
                                                    let member_alignment =
                                                        self.get_type_alignment(&member.ty);
                                                    current_offset =
                                                        (current_offset + member_alignment - 1)
                                                            & !(member_alignment - 1);
                                                    if member.name == *name {
                                                        member_index = i;
                                                        current_ty = member.ty.clone();
                                                        found = true;
                                                        break;
                                                    }
                                                    current_offset +=
                                                        self.get_type_size(&member.ty);
                                                }
                                                if !found {
                                                    return Err(CodegenError::UnknownField(
                                                        name.to_string(),
                                                    ));
                                                }
                                            } else {
                                                return Err(CodegenError::NotAStruct);
                                            }
                                        }
                                        TypedDesignator::Index(expr) => {
                                            let s = self.get_real_type(&current_ty)?;
                                            if let Type::Array(elem_ty, _) = s {
                                                let elem_size = self.get_type_size(&elem_ty);
                                                if let TypedExpr::Number(n, _) = **expr {
                                                    current_offset += n as u32 * elem_size;
                                                    current_ty = *elem_ty.clone();
                                                } else {
                                                    return Err(
                                                        CodegenError::NonConstantArrayIndex,
                                                    );
                                                }
                                            } else {
                                                return Err(CodegenError::NotAnArray);
                                            }
                                        }
                                    }
                                }
                                (current_offset, current_ty)
                            } else {
                                if member_index >= members.len() {
                                    return Err(CodegenError::InitializerTooLong);
                                }
                                let mut offset = 0;
                                for member in members.iter().take(member_index) {
                                    let member_alignment = self.get_type_alignment(&member.ty);
                                    offset =
                                        (offset + member_alignment - 1) & !(member_alignment - 1);
                                    offset += self.get_type_size(&member.ty);
                                }
                                (offset, members[member_index].ty.clone())
                            };
                            let member_addr = self.builder.ins().iadd_imm(base_addr, offset as i64);
                            self.translate_initializer(member_addr, &member_ty, initializer)?;
                            member_index += 1;
                        }
                    }
                    Type::Array(elem_ty, _) => {
                        let elem_size = self.get_type_size(&elem_ty);
                        let mut index = 0;
                        for (designators, initializer) in list {
                            let current_index = if !designators.is_empty() {
                                if let TypedDesignator::Index(expr) = &designators[0] {
                                    if let TypedExpr::Number(n, _) = **expr {
                                        n as u32
                                    } else {
                                        return Err(CodegenError::NonConstantArrayIndex);
                                    }
                                } else {
                                    return Err(CodegenError::NotAnArray);
                                }
                            } else {
                                index
                            };
                            let offset = current_index * elem_size;
                            let elem_addr = self.builder.ins().iadd_imm(base_addr, offset as i64);
                            self.translate_initializer(elem_addr, &elem_ty, initializer)?;
                            index = current_index + 1;
                        }
                    }
                    _ => return Err(CodegenError::NotAStructOrArray),
                }
            }
        }
        Ok(())
    }
}
