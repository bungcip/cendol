use crate::codegen::error::CodegenError;
use crate::parser::ast::{Expr, ForInit, Program, Stmt, Type};
use cranelift::prelude::*;
use cranelift_codegen::Context;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, Value};
use cranelift_codegen::ir::{StackSlot, StackSlotData, StackSlotKind};
use cranelift_codegen::settings;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;

pub mod error;

struct SymbolTable<K, V> {
    scopes: Vec<HashMap<K, V>>,
}

impl<K: std::hash::Hash + Eq + Clone, V: Clone> SymbolTable<K, V> {
    fn new() -> Self {
        Self {
            scopes: vec![HashMap::new()],
        }
    }

    fn enter_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn exit_scope(&mut self) {
        self.scopes.pop();
    }

    fn insert(&mut self, key: K, value: V) {
        self.scopes.last_mut().unwrap().insert(key, value);
    }

    fn get(&self, key: &K) -> Option<V> {
        for scope in self.scopes.iter().rev() {
            if let Some(value) = scope.get(key) {
                return Some(value.clone());
            }
        }
        None
    }
}

/// A code generator that translates an AST into machine code.
use cranelift_module::FuncId;

pub struct CodeGen {
    builder_context: FunctionBuilderContext,
    ctx: Context,
    module: ObjectModule,
    variables: SymbolTable<String, (StackSlot, Type)>,
    functions: HashMap<String, (FuncId, Type)>,
    signatures: HashMap<String, cranelift::prelude::Signature>,
    structs: HashMap<String, Type>,
}

impl Default for CodeGen {
    /// Creates a new `CodeGen` with default settings.
    fn default() -> Self {
        Self::new()
    }
}

impl CodeGen {
    /// Creates a new `CodeGen`.
    pub fn new() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .unwrap();
        let builder =
            ObjectBuilder::new(isa, "cendol", cranelift_module::default_libcall_names()).unwrap();
        let module = ObjectModule::new(builder);
        let ctx = module.make_context();
        let builder_context = FunctionBuilderContext::new();

        Self {
            builder_context,
            ctx,
            module,
            variables: SymbolTable::new(),
            functions: HashMap::new(),
            signatures: HashMap::new(),
            structs: HashMap::new(),
        }
    }

    /// Compiles a program into a byte vector.
    ///
    /// # Arguments
    ///
    /// * `program` - The program to compile.
    ///
    /// # Returns
    ///
    /// A `Result` containing the compiled byte vector, or a `CodegenError` if compilation fails.
    pub fn compile(mut self, program: Program) -> Result<Vec<u8>, CodegenError> {
        for global in &program.globals {
            match global {
                Stmt::FunctionDeclaration(ty, name, params) => {
                    let mut sig = self.module.make_signature();
                    for _ in params {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    sig.returns.push(AbiParam::new(types::I64));
                    let id = self
                        .module
                        .declare_function(name, Linkage::Import, &sig)
                        .unwrap();
                    self.functions.insert(name.clone(), (id, ty.clone()));
                }
                Stmt::Declaration(ty, _, _) => {
                    if let Type::Struct(Some(name), _) = &ty {
                        self.structs.insert(name.clone(), ty.clone());
                    }
                }
                _ => {}
            }
        }

        // First, declare all functions
        for function in &program.functions {
            let mut sig = self.module.make_signature();
            if let Type::Struct(_, _) = function.return_type {
                sig.params.push(AbiParam::new(types::I64));
            }
            for _ in &function.params {
                sig.params.push(AbiParam::new(types::I64));
            }
            sig.returns.push(AbiParam::new(types::I64));

            let id = self
                .module
                .declare_function(
                    &function.name,
                    if function.name == "main" {
                        Linkage::Export
                    } else {
                        Linkage::Local
                    },
                    &sig,
                )
                .unwrap();
            self.functions
                .insert(function.name.clone(), (id, function.return_type.clone()));
            self.signatures.insert(function.name.clone(), sig);
        }

        // Then, define all functions
        for function_name in program.functions.iter().map(|f| &f.name) {
            let (id, _) = self.functions.get(function_name).unwrap();
            let sig = self.signatures.get(function_name).unwrap().clone();

            self.ctx.clear();
            self.ctx.func.signature = sig;

            let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let mut translator = FunctionTranslator {
                builder,
                functions: &self.functions,
                variables: &mut self.variables,
                structs: &self.structs,
                module: &mut self.module,
                loop_context: Vec::new(),
                current_block_state: BlockState::Empty,
            };
            // Find the function body
            let function = program
                .functions
                .iter()
                .find(|f| &f.name == function_name)
                .unwrap();
            // Add parameters to variables and store block params
            let block_params = translator.builder.block_params(entry_block).to_vec();
            for (i, param) in function.params.iter().enumerate() {
                let size = translator.get_type_size(&param.ty);
                let slot = translator
                    .builder
                    .create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size,
                        0,
                    ));
                translator
                    .variables
                    .insert(param.name.clone(), (slot, param.ty.clone()));
                // Store the block parameter into the stack slot
                translator
                    .builder
                    .ins()
                    .stack_store(block_params[i], slot, 0);
            }
            let mut terminated = false;
            for stmt in &function.body {
                if terminated {
                    break;
                }
                let term = translator.translate_stmt(stmt.clone())?;
                terminated = term;
            }
            if !terminated {
                let zero = translator.builder.ins().iconst(types::I64, 0);
                translator.builder.ins().return_(&[zero]);
            }
            translator.builder.seal_all_blocks();
            translator.builder.finalize();
            self.module.define_function(*id, &mut self.ctx).unwrap();
        }

        let product = self.module.finish();
        let object_bytes = product.emit().unwrap();
        Ok(object_bytes)
    }
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
struct FunctionTranslator<'a, 'b> {
    builder: FunctionBuilder<'a>,
    functions: &'b HashMap<String, (FuncId, Type)>,
    variables: &'b mut SymbolTable<String, (StackSlot, Type)>,
    structs: &'b HashMap<String, Type>,
    module: &'b mut ObjectModule,
    loop_context: Vec<(Block, Block)>,
    current_block_state: BlockState,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
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
    fn get_type_alignment(&self, ty: &Type) -> u32 {
        let real_ty = self.get_real_type(ty).unwrap();
        match &real_ty {
            Type::Int => 8,
            Type::Char => 1,
            Type::Float => 4,
            Type::Double => 8,
            Type::Long => 8,
            Type::LongLong => 8,
            Type::Void => 1,
            Type::Bool => 1,
            Type::Pointer(_) => 8,
            Type::Struct(_, members) => members
                .iter()
                .map(|m| self.get_type_alignment(&m.ty))
                .max()
                .unwrap_or(1),
            Type::Array(elem_ty, _) => self.get_type_alignment(elem_ty),
            _ => unimplemented!(),
        }
    }

    /// Returns the size of a given type in bytes.
    fn get_type_size(&self, ty: &Type) -> u32 {
        let real_ty = self.get_real_type(ty).unwrap();
        match &real_ty {
            Type::Int => 8,
            Type::Char => 1,
            Type::Float => 4,
            Type::Double => 8,
            Type::Long => 8,
            Type::LongLong => 8,
            Type::Void => 0,
            Type::Bool => 1,
            Type::Pointer(_) => 8,
            Type::Struct(_, members) => {
                let mut size = 0;
                for member in members {
                    let member_size = self.get_type_size(&member.ty);
                    let member_alignment = self.get_type_alignment(&member.ty);
                    size = (size + member_alignment - 1) & !(member_alignment - 1);
                    size += member_size;
                }
                let struct_alignment = self.get_type_alignment(ty);
                (size + struct_alignment - 1) & !(struct_alignment - 1)
            }
            Type::Array(elem_ty, size) => self.get_type_size(elem_ty) * *size as u32,
            _ => unimplemented!(),
        }
    }

    /// Translates a statement into Cranelift IR.
    fn translate_stmt(&mut self, stmt: Stmt) -> Result<bool, CodegenError> {
        match stmt {
            Stmt::Return(expr) => {
                let (value, ty) = self.translate_expr(expr)?;
                if let Type::Struct(_, _) = ty {
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
            Stmt::Declaration(ty, name, initializer) => {
                let size = self.get_type_size(&ty);
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size,
                    0,
                ));
                self.variables.insert(name, (slot, ty.clone()));
                if let Some(init) = initializer {
                    if let Expr::StructInitializer(initializers) = *init {
                        let s = self.get_real_type(&ty)?;
                        if let Type::Struct(_, members) = s {
                            let mut offset = 0;
                            for member in &members {
                                let val = self.builder.ins().iconst(types::I64, 0);
                                self.builder.ins().stack_store(val, slot, offset as i32);
                                offset += self.get_type_size(&member.ty);
                            }

                            let mut member_index = 0;
                            for initializer in initializers {
                                if let Expr::DesignatedInitializer(name, expr) = initializer {
                                    let mut offset = 0;
                                    let mut found = false;
                                    for (i, member) in members.iter().enumerate() {
                                        let member_alignment = self.get_type_alignment(&member.ty);
                                        offset = (offset + member_alignment - 1)
                                            & !(member_alignment - 1);
                                        if member.name == name {
                                            member_index = i;
                                            found = true;
                                            break;
                                        }
                                        offset += self.get_type_size(&member.ty);
                                    }
                                    if !found {
                                        return Err(CodegenError::UnknownField(name));
                                    }
                                    let (val, _) = self.translate_expr(*expr)?;
                                    self.builder.ins().stack_store(val, slot, offset as i32);
                                } else {
                                    if member_index >= members.len() {
                                        return Err(CodegenError::InitializerTooLong);
                                    }
                                    let mut offset = 0;
                                    for member in members.iter().take(member_index) {
                                        let member_alignment = self.get_type_alignment(&member.ty);
                                        offset = (offset + member_alignment - 1)
                                            & !(member_alignment - 1);
                                        offset += self.get_type_size(&member.ty);
                                    }
                                    let (val, _) = self.translate_expr(initializer)?;
                                    self.builder.ins().stack_store(val, slot, offset as i32);
                                }
                                member_index += 1;
                            }
                        } else {
                            return Err(CodegenError::NotAStruct);
                        }
                    } else {
                        let (val, val_ty) = self.translate_expr(*init)?;
                        if let Type::Struct(_, _) = val_ty {
                            let dest = self.builder.ins().stack_addr(types::I64, slot, 0);
                            let src = val;
                            let size = self.get_type_size(&val_ty);
                            self.builder.emit_small_memory_copy(
                                self.module.target_config(),
                                dest,
                                src,
                                size as u64,
                                self.get_type_alignment(&val_ty) as u8,
                                self.get_type_alignment(&val_ty) as u8,
                                true,
                                MemFlags::new(),
                            );
                        } else {
                            self.builder.ins().stack_store(val, slot, 0);
                        }
                    }
                } else {
                    let val = self.builder.ins().iconst(types::I64, 0);
                    self.builder.ins().stack_store(val, slot, 0);
                };
                Ok(false)
            }
            Stmt::Block(stmts) => {
                self.variables.enter_scope();
                let mut terminated = false;
                for stmt in stmts {
                    if terminated {
                        break;
                    }
                    let term = self.translate_stmt(stmt)?;
                    terminated = term;
                }
                self.variables.exit_scope();
                Ok(terminated)
            }
            Stmt::If(cond, then, otherwise) => {
                let (condition_value, _) = self.translate_expr(*cond)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(condition_value, then_block, &[], else_block, &[]);

                self.switch_to_block(then_block);
                let then_terminated = self.translate_stmt(*then)?;
                if !then_terminated {
                    self.jump_to_block(merge_block);
                }

                self.switch_to_block(else_block);
                let mut else_terminated = false;
                if let Some(otherwise) = otherwise {
                    else_terminated = self.translate_stmt(*otherwise)?;
                }

                if !else_terminated {
                    self.jump_to_block(merge_block);
                }

                if !then_terminated || !else_terminated {
                    self.switch_to_block(merge_block);
                }

                Ok(then_terminated && else_terminated)
            }
            Stmt::While(cond, body) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                let (cond_val, _) = self.translate_expr(*cond)?;
                self.builder
                    .ins()
                    .brif(cond_val, body_block, &[], exit_block, &[]);

                self.switch_to_block(body_block);

                self.loop_context.push((header_block, exit_block));
                self.translate_stmt(*body)?;
                self.loop_context.pop();

                self.jump_to_block(header_block);

                self.switch_to_block(exit_block);

                Ok(false)
            }
            Stmt::Break => {
                let (_, exit_block) = self.loop_context.last().unwrap();
                self.jump_to_block(*exit_block);
                Ok(true)
            }
            Stmt::Continue => {
                let (header_block, _) = self.loop_context.last().unwrap();
                self.jump_to_block(*header_block);
                Ok(true)
            }
            Stmt::For(init, cond, inc, body) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.variables.enter_scope();
                if let Some(init) = init {
                    match init {
                        ForInit::Declaration(ty, name, initializer) => {
                            let size = self.get_type_size(&ty);
                            let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                                StackSlotKind::ExplicitSlot,
                                size,
                                0,
                            ));
                            self.variables.insert(name, (slot, ty));
                            if let Some(init) = initializer {
                                let (val, _) = self.translate_expr(*init)?;
                                self.builder.ins().stack_store(val, slot, 0);
                            } else {
                                let val = self.builder.ins().iconst(types::I64, 0);
                                self.builder.ins().stack_store(val, slot, 0);
                            };
                        }
                        ForInit::Expr(expr) => {
                            self.translate_expr(expr)?;
                        }
                    }
                }

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                if let Some(cond) = cond {
                    let (cond_val, _) = self.translate_expr(*cond)?;
                    self.builder
                        .ins()
                        .brif(cond_val, body_block, &[], exit_block, &[]);
                } else {
                    self.jump_to_block(body_block);
                }

                self.switch_to_block(body_block);
                self.loop_context.push((header_block, exit_block));
                self.translate_stmt(*body)?;
                self.loop_context.pop();

                if let Some(inc) = inc {
                    self.translate_expr(*inc)?;
                }

                self.jump_to_block(header_block);

                self.switch_to_block(exit_block);

                self.variables.exit_scope();
                Ok(false)
            }
            Stmt::Expr(expr) => {
                self.translate_expr(expr)?;
                Ok(false)
            }
            Stmt::Empty => Ok(false),
            Stmt::DoWhile(body, cond) => {
                let header_block = self.builder.create_block();
                let cond_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                self.translate_stmt(*body)?;
                self.jump_to_block(cond_block);

                self.switch_to_block(cond_block);

                let (cond_val, _) = self.translate_expr(*cond)?;
                self.builder
                    .ins()
                    .brif(cond_val, header_block, &[], exit_block, &[]);

                self.switch_to_block(exit_block);

                Ok(false)
            }
            _ => unimplemented!(),
        }
    }

    /// Resolves the real type of a struct.
    fn get_real_type(&self, ty: &Type) -> Result<Type, CodegenError> {
        if let Type::Struct(Some(name), members) = ty
            && members.is_empty()
        {
            return Ok(self.structs.get(name).unwrap().clone());
        }
        Ok(ty.clone())
    }

    /// Translates an expression into a Cranelift `Value`.
    fn translate_expr(&mut self, expr: Expr) -> Result<(Value, Type), CodegenError> {
        match expr {
            Expr::Number(n) => Ok((self.builder.ins().iconst(types::I64, n), Type::Int)),
            Expr::String(s) => {
                let mut data = Vec::with_capacity(s.len() + 1);
                data.extend_from_slice(s.as_bytes());
                data.push(0);
                let id = self
                    .module
                    .declare_data(&s, Linkage::Local, false, false)
                    .unwrap();
                let mut data_desc = cranelift_module::DataDescription::new();
                data_desc.define(data.into_boxed_slice());
                self.module.define_data(id, &data_desc).unwrap();
                let local_id = self.module.declare_data_in_func(id, self.builder.func);
                Ok((
                    self.builder.ins().global_value(types::I64, local_id),
                    Type::Pointer(Box::new(Type::Char)),
                ))
            }
            Expr::Variable(name, _) => {
                let (slot, ty) = self.variables.get(&name).unwrap();
                if let Type::Struct(_, _) = &ty {
                    return Ok((
                        self.builder.ins().stack_addr(types::I64, slot, 0),
                        ty.clone(),
                    ));
                }
                if let Type::Array(elem_ty, _) = &ty {
                    // Array decays to a pointer to its first element
                    let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                    return Ok((addr, Type::Pointer(elem_ty.clone())));
                }
                let loaded_val = match ty {
                    Type::Char | Type::Bool => {
                        let val = self.builder.ins().stack_load(types::I8, slot, 0);
                        self.builder.ins().sextend(types::I64, val)
                    }
                    _ => self.builder.ins().stack_load(types::I64, slot, 0),
                };
                Ok((loaded_val, ty))
            }
            Expr::Assign(lhs, rhs) => {
                let (value, ty) = self.translate_expr(*rhs)?;
                if let Expr::Variable(name, _) = *lhs {
                    let (slot, _) = self.variables.get(&name).unwrap();
                    self.builder.ins().stack_store(value, slot, 0);
                } else if let Expr::Deref(ptr) = *lhs {
                    let (ptr, _) = self.translate_expr(*ptr)?;
                    self.builder.ins().store(MemFlags::new(), value, ptr, 0);
                } else if let Expr::Member(expr, member) = *lhs {
                    let (ptr, ty) = self.translate_expr(*expr)?;
                    let s = self.get_real_type(&ty)?;
                    if let Type::Struct(_, members) = s {
                        let mut offset = 0;
                        for m in &members {
                            let member_alignment = self.get_type_alignment(&m.ty);
                            offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                            if m.name == *member {
                                break;
                            }
                            offset += self.get_type_size(&m.ty);
                        }
                        self.builder
                            .ins()
                            .store(MemFlags::new(), value, ptr, offset as i32);
                    } else {
                        return Err(CodegenError::NotAStruct);
                    }
                } else {
                    unimplemented!()
                }
                Ok((value, ty))
            }
            Expr::AssignAdd(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().iadd(lhs_val, rhs_val);
                match &*lhs {
                    Expr::Variable(name, _) => {
                        let (slot, _) = self.variables.get(&name).unwrap();
                        self.builder.ins().stack_store(result_val, slot, 0);
                    }
                    Expr::Deref(ptr) => {
                        let (ptr, _) = self.translate_expr(*ptr.clone())?;
                        self.builder.ins().store(MemFlags::new(), result_val, ptr, 0);
                    }
                    Expr::Member(expr, member) => {
                        let (ptr, ty) = self.translate_expr(*expr.clone())?;
                        let s = self.get_real_type(&ty)?;
                        if let Type::Struct(_, members) = s {
                            let mut offset = 0;
                            for m in &members {
                                let member_alignment = self.get_type_alignment(&m.ty);
                                offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                                if m.name == *member {
                                    break;
                                }
                                offset += self.get_type_size(&m.ty);
                            }
                            self.builder
                                .ins()
                                .store(MemFlags::new(), result_val, ptr, offset as i32);
                        } else {
                            return Err(CodegenError::NotAStruct);
                        }
                    }
                    _ => unimplemented!(),
                }
                Ok((result_val, lhs_ty))
            }
            Expr::AssignSub(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().isub(lhs_val, rhs_val);
                match *lhs {
                    Expr::Variable(name, _) => {
                        let (slot, _) = self.variables.get(&name).unwrap();
                        self.builder.ins().stack_store(result_val, slot, 0);
                    }
                    Expr::Deref(ptr) => {
                        let (ptr, _) = self.translate_expr(*ptr)?;
                        self.builder.ins().store(MemFlags::new(), result_val, ptr, 0);
                    }
                    Expr::Member(expr, member) => {
                        let (ptr, ty) = self.translate_expr(*expr.clone())?;
                        let s = self.get_real_type(&ty)?;
                        if let Type::Struct(_, members) = s {
                            let mut offset = 0;
                            for m in &members {
                                let member_alignment = self.get_type_alignment(&m.ty);
                                offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                                if m.name == *member {
                                    break;
                                }
                                offset += self.get_type_size(&m.ty);
                            }
                            self.builder
                                .ins()
                                .store(MemFlags::new(), result_val, ptr, offset as i32);
                        } else {
                            return Err(CodegenError::NotAStruct);
                        }
                    }
                    _ => unimplemented!(),
                }
                Ok((result_val, lhs_ty))
            }
            Expr::AssignMul(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().imul(lhs_val, rhs_val);
                match *lhs {
                    Expr::Variable(name, _) => {
                        let (slot, _) = self.variables.get(&name).unwrap();
                        self.builder.ins().stack_store(result_val, slot, 0);
                    }
                    Expr::Deref(ptr) => {
                        let (ptr, _) = self.translate_expr(*ptr)?;
                        self.builder.ins().store(MemFlags::new(), result_val, ptr, 0);
                    }
                    Expr::Member(expr, member) => {
                        let (ptr, ty) = self.translate_expr(*expr.clone())?;
                        let s = self.get_real_type(&ty)?;
                        if let Type::Struct(_, members) = s {
                            let mut offset = 0;
                            for m in &members {
                                let member_alignment = self.get_type_alignment(&m.ty);
                                offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                                if m.name == *member {
                                    break;
                                }
                                offset += self.get_type_size(&m.ty);
                            }
                            self.builder
                                .ins()
                                .store(MemFlags::new(), result_val, ptr, offset as i32);
                        } else {
                            return Err(CodegenError::NotAStruct);
                        }
                    }
                    _ => unimplemented!(),
                }
                Ok((result_val, lhs_ty))
            }
            Expr::AssignDiv(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().sdiv(lhs_val, rhs_val);
                match *lhs {
                    Expr::Variable(name, _) => {
                        let (slot, _) = self.variables.get(&name).unwrap();
                        self.builder.ins().stack_store(result_val, slot, 0);
                    }
                    Expr::Deref(ptr) => {
                        let (ptr, _) = self.translate_expr(*ptr)?;
                        self.builder.ins().store(MemFlags::new(), result_val, ptr, 0);
                    }
                    Expr::Member(expr, member) => {
                        let (ptr, ty) = self.translate_expr(*expr.clone())?;
                        let s = self.get_real_type(&ty)?;
                        if let Type::Struct(_, members) = s {
                            let mut offset = 0;
                            for m in &members {
                                let member_alignment = self.get_type_alignment(&m.ty);
                                offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                                if m.name == *member {
                                    break;
                                }
                                offset += self.get_type_size(&m.ty);
                            }
                            self.builder
                                .ins()
                                .store(MemFlags::new(), result_val, ptr, offset as i32);
                        } else {
                            return Err(CodegenError::NotAStruct);
                        }
                    }
                    _ => unimplemented!(),
                }
                Ok((result_val, lhs_ty))
            }
            Expr::AssignMod(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().srem(lhs_val, rhs_val);
                match *lhs {
                    Expr::Variable(name, _) => {
                        let (slot, _) = self.variables.get(&name).unwrap();
                        self.builder.ins().stack_store(result_val, slot, 0);
                    }
                    Expr::Deref(ptr) => {
                        let (ptr, _) = self.translate_expr(*ptr)?;
                        self.builder.ins().store(MemFlags::new(), result_val, ptr, 0);
                    }
                    Expr::Member(expr, member) => {
                        let (ptr, ty) = self.translate_expr(*expr.clone())?;
                        let s = self.get_real_type(&ty)?;
                        if let Type::Struct(_, members) = s {
                            let mut offset = 0;
                            for m in &members {
                                let member_alignment = self.get_type_alignment(&m.ty);
                                offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                                if m.name == *member {
                                    break;
                                }
                                offset += self.get_type_size(&m.ty);
                            }
                            self.builder
                                .ins()
                                .store(MemFlags::new(), result_val, ptr, offset as i32);
                        } else {
                            return Err(CodegenError::NotAStruct);
                        }
                    }
                    _ => unimplemented!(),
                }
                Ok((result_val, lhs_ty))
            }
            Expr::Add(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs_val, rhs_ty) = self.translate_expr(*rhs)?;
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
                    _ => self.builder.ins().iadd(lhs_val, rhs_val),
                };
                let result_ty = if lhs_ty.is_pointer() { lhs_ty } else { rhs_ty };
                Ok((result_val, result_ty))
            }
            Expr::Sub(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs_val, rhs_ty) = self.translate_expr(*rhs)?;
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
                    _ => self.builder.ins().isub(lhs_val, rhs_val),
                };
                let result_ty = match (&lhs_ty, &rhs_ty) {
                    (Type::Pointer(_), Type::Pointer(_)) => Type::Int,
                    (Type::Pointer(_), Type::Int) => lhs_ty,
                    _ => lhs_ty,
                };
                Ok((result_val, result_ty))
            }
            Expr::Mul(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().imul(lhs, rhs), Type::Int))
            }
            Expr::Div(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().sdiv(lhs, rhs), Type::Int))
            }
            Expr::Mod(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().srem(lhs, rhs), Type::Int))
            }
            Expr::Equal(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self.builder.ins().icmp(IntCC::Equal, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::NotEqual(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::LessThan(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::GreaterThan(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::LessThanOrEqual(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::GreaterThanOrEqual(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::Neg(expr) => {
                let (val, ty) = self.translate_expr(*expr)?;
                Ok((self.builder.ins().ineg(val), ty))
            }
            Expr::BitwiseNot(expr) => {
                let (val, ty) = self.translate_expr(*expr)?;
                Ok((self.builder.ins().bnot(val), ty))
            }
            Expr::Sizeof(expr) => {
                let (_, ty) = self.translate_expr(*expr)?;
                let size = self.get_type_size(&ty) as i64;
                Ok((self.builder.ins().iconst(types::I64, size), Type::Int))
            }
            Expr::SizeofType(ty) => {
                let size = self.get_type_size(&ty) as i64;
                Ok((self.builder.ins().iconst(types::I64, size), Type::Int))
            }
            Expr::Deref(expr) => {
                let (ptr, ty) = self.translate_expr(*expr)?;
                if let Type::Pointer(base_ty) = ty {
                    Ok((
                        self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0),
                        *base_ty,
                    ))
                } else {
                    unimplemented!()
                }
            }
            Expr::AddressOf(expr) => {
                if let Expr::Variable(name, _) = *expr {
                    let (slot, ty) = self.variables.get(&name).unwrap();
                    let addr = self.builder.ins().stack_addr(types::I64, slot, 0);
                    Ok((addr, Type::Pointer(Box::new(ty))))
                } else if let Expr::Deref(ptr_expr) = *expr {
                    // Taking the address of a dereference is a no-op
                    self.translate_expr(*ptr_expr)
                } else {
                    unimplemented!()
                }
            }
            Expr::PointerMember(expr, member) => {
                let (ptr, ty) = self.translate_expr(*expr)?;
                if let Type::Pointer(base_ty) = ty {
                    let s = self.get_real_type(&base_ty)?;
                    if let Type::Struct(_, members) = s {
                        let mut offset = 0;
                        let mut member_ty = None;
                        for m in members {
                            let member_alignment = self.get_type_alignment(&m.ty);
                            offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                            if m.name == member {
                                member_ty = Some(m.ty);
                                break;
                            }
                            offset += self.get_type_size(&m.ty);
                        }
                        Ok((
                            self.builder.ins().load(
                                types::I64,
                                MemFlags::new(),
                                ptr,
                                offset as i32,
                            ),
                            member_ty.unwrap(),
                        ))
                    } else {
                        Err(CodegenError::NotAStruct)
                    }
                } else {
                    Err(CodegenError::NotAPointer)
                }
            }
            Expr::Call(name, args, _location) => {
                let (callee, ret_ty) = self
                    .functions
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| panic!("Undefined function: {}", name));
                let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

                let mut arg_values = Vec::new();
                if let Type::Struct(_, _) = ret_ty {
                    let size = self.get_type_size(&ret_ty);
                    let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size,
                        0,
                    ));
                    let ptr = self.builder.ins().stack_addr(types::I64, slot, 0);
                    arg_values.push(ptr);
                }

                for arg in args {
                    let (val, _) = self.translate_expr(arg)?;
                    arg_values.push(val);
                }

                let call = self.builder.ins().call(local_callee, &arg_values);
                if let Type::Struct(_, _) = ret_ty {
                    let addr = self.builder.inst_results(call)[0];
                    return Ok((addr, ret_ty));
                }
                Ok((self.builder.inst_results(call)[0], ret_ty))
            }
            Expr::Ternary(cond, then_expr, else_expr) => {
                let (condition_value, _) = self.translate_expr(*cond)?;

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(condition_value, then_block, &[], else_block, &[]);

                self.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                let (then_value, ty) = self.translate_expr(*then_expr)?;
                self.builder.ins().jump(merge_block, &[then_value.into()]);
                self.current_block_state = BlockState::Filled;

                self.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let (else_value, _) = self.translate_expr(*else_expr)?;
                self.builder.ins().jump(merge_block, &[else_value.into()]);
                self.current_block_state = BlockState::Filled;

                self.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                self.builder.append_block_param(merge_block, types::I64);

                self.switch_to_block(merge_block);

                Ok((self.builder.block_params(merge_block)[0], ty))
            }
            Expr::Member(expr, member) => {
                let (ptr, ty) = self.translate_expr(*expr.clone())?;
                let s = self.get_real_type(&ty)?;
                if let Type::Struct(_, members) = s {
                    let mut offset = 0;
                    let mut member_ty = None;
                    for m in members {
                        let member_alignment = self.get_type_alignment(&m.ty);
                        offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                        if m.name == member {
                            member_ty = Some(m.ty);
                            break;
                        }
                        offset += self.get_type_size(&m.ty);
                    }
                    Ok((
                        self.builder
                            .ins()
                            .load(types::I64, MemFlags::new(), ptr, offset as i32),
                        member_ty.unwrap(),
                    ))
                } else {
                    Err(CodegenError::NotAStruct)
                }
            }
            Expr::Cast(ty, expr) => {
                let (val, _) = self.translate_expr(*expr)?;
                let cast_val = match *ty {
                    Type::Char => self.builder.ins().ireduce(types::I8, val),
                    Type::Bool => self.builder.ins().ireduce(types::I8, val),
                    _ => val, // Other types are already I64
                };

                // The ABI requires function arguments and return values to be I64,
                // so we extend smaller types back to I64 after casting.
                let extended_val = match *ty {
                    Type::Char | Type::Bool => self.builder.ins().sextend(types::I64, cast_val),
                    _ => cast_val,
                };

                Ok((extended_val, *ty))
            }
            Expr::CompoundLiteral(mut ty, initializers) => {
                // If the type is an array with an unspecified size, update it
                if let Type::Array(_, ref mut size @ 0) = *ty {
                    *size = initializers.len();
                }

                let size = self.get_type_size(&ty);
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    size,
                    0,
                ));
                let s = self.get_real_type(&ty)?;

                match s {
                    Type::Struct(_, members) => {
                        let mut member_index = 0;
                        for initializer in initializers {
                            if let Expr::DesignatedInitializer(name, expr) = initializer {
                                let mut offset = 0;
                                let mut found = false;
                                for (i, member) in members.iter().enumerate() {
                                    let member_alignment = self.get_type_alignment(&member.ty);
                                    offset =
                                        (offset + member_alignment - 1) & !(member_alignment - 1);
                                    if member.name == name {
                                        member_index = i;
                                        found = true;
                                        break;
                                    }
                                    offset += self.get_type_size(&member.ty);
                                }
                                if !found {
                                    return Err(CodegenError::UnknownField(name));
                                }
                                let (val, _) = self.translate_expr(*expr)?;
                                self.builder.ins().stack_store(val, slot, offset as i32);
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
                                let (val, _) = self.translate_expr(initializer)?;
                                self.builder.ins().stack_store(val, slot, offset as i32);
                            }
                            member_index += 1;
                        }
                    }
                    Type::Array(elem_ty, _) => {
                        let elem_size = self.get_type_size(&elem_ty);
                        for (i, initializer) in initializers.into_iter().enumerate() {
                            let (val, _) = self.translate_expr(initializer)?;
                            let offset = (i as u32 * elem_size) as i32;
                            self.builder.ins().stack_store(val, slot, offset);
                        }
                    }
                    _ => return Err(CodegenError::NotAStructOrArray),
                }

                Ok((self.builder.ins().stack_addr(types::I64, slot, 0), *ty))
            }
            Expr::Increment(expr) => {
                if let Expr::Variable(name, _) = *expr {
                    let (slot, ty) = self.variables.get(&name).unwrap();
                    let loaded_val = match ty {
                        Type::Char | Type::Bool => {
                            let val = self.builder.ins().stack_load(types::I8, slot, 0);
                            self.builder.ins().sextend(types::I64, val)
                        }
                        _ => self.builder.ins().stack_load(types::I64, slot, 0),
                    };
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let new_val = self.builder.ins().iadd(loaded_val, one);
                    self.builder.ins().stack_store(new_val, slot, 0);
                    Ok((loaded_val, ty))
                } else {
                    unimplemented!()
                }
            }
            Expr::Decrement(expr) => {
                if let Expr::Variable(name, _) = *expr {
                    let (slot, ty) = self.variables.get(&name).unwrap();
                    let loaded_val = match ty {
                        Type::Char | Type::Bool => {
                            let val = self.builder.ins().stack_load(types::I8, slot, 0);
                            self.builder.ins().sextend(types::I64, val)
                        }
                        _ => self.builder.ins().stack_load(types::I64, slot, 0),
                    };
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let new_val = self.builder.ins().isub(loaded_val, one);
                    self.builder.ins().stack_store(new_val, slot, 0);
                    Ok((loaded_val, ty))
                } else {
                    unimplemented!()
                }
            }
            Expr::Char(_) => {
                // Literals are handled directly by the `translate_expr` function
                unreachable!()
            }
            Expr::LogicalAnd(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self.builder.ins().band(lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::LogicalOr(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let c = self.builder.ins().bor(lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::LogicalNot(expr) => {
                let (val, _) = self.translate_expr(*expr)?;
                let zero = self.builder.ins().iconst(types::I64, 0);
                let c = self.builder.ins().icmp(IntCC::Equal, val, zero);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::StructInitializer(_) | Expr::DesignatedInitializer(_, _) => unimplemented!(),
        }
    }
}
