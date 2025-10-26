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
    functions: HashMap<String, (FuncId, Type, bool)>,
    signatures: HashMap<String, cranelift::prelude::Signature>,
    structs: HashMap<String, Type>,
    unions: HashMap<String, Type>,
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
            unions: HashMap::new(),
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
                Stmt::FunctionDeclaration(ty, name, params, is_variadic) => {
                    let mut sig = self.module.make_signature();
                    for _ in params {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    sig.returns.push(AbiParam::new(types::I64));
                    let id = self
                        .module
                        .declare_function(name, Linkage::Import, &sig)
                        .unwrap();
                    self.functions
                        .insert(name.clone(), (id, ty.clone(), *is_variadic));
                    self.signatures.insert(name.clone(), sig);
                }
                Stmt::Declaration(base_ty, declarators) => {
                    if let Type::Struct(Some(name), _) = &base_ty {
                        self.structs.insert(name.clone(), base_ty.clone());
                    } else if let Type::Union(Some(name), _) = &base_ty {
                        self.unions.insert(name.clone(), base_ty.clone());
                    }
                    for declarator in declarators {
                        if let Type::Struct(Some(name), _) = &declarator.ty {
                            self.structs.insert(name.clone(), declarator.ty.clone());
                        } else if let Type::Union(Some(name), _) = &declarator.ty {
                            self.unions.insert(name.clone(), declarator.ty.clone());
                        }
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
            self.functions.insert(
                function.name.clone(),
                (id, function.return_type.clone(), function.is_variadic),
            );
            self.signatures.insert(function.name.clone(), sig);
        }

        // Then, define all functions
        for function_name in program.functions.iter().map(|f| &f.name) {
            let (id, _, _) = self.functions.get(function_name).unwrap();
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
                unions: &self.unions,
                module: &mut self.module,
                loop_context: Vec::new(),
                current_block_state: BlockState::Empty,
                signatures: &self.signatures,
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
            let mut text = String::new();
            cranelift::codegen::write_function(&mut text, &self.ctx.func).unwrap();
            println!("{}", text);
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
    functions: &'b HashMap<String, (FuncId, Type, bool)>,
    variables: &'b mut SymbolTable<String, (StackSlot, Type)>,
    structs: &'b HashMap<String, Type>,
    unions: &'b HashMap<String, Type>,
    module: &'b mut ObjectModule,
    loop_context: Vec<(Block, Block)>,
    current_block_state: BlockState,
    signatures: &'b HashMap<String, Signature>,
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
                .map(|m| self.get_type_alignment(&m.ty))
                .max()
                .unwrap_or(1),
            Type::Union(_, members) => members
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
                    let member_size = self.get_type_size(&member.ty);
                    let member_alignment = self.get_type_alignment(&member.ty);
                    size = (size + member_alignment - 1) & !(member_alignment - 1);
                    size += member_size;
                }
                let struct_alignment = self.get_type_alignment(ty);
                (size + struct_alignment - 1) & !(struct_alignment - 1)
            }
            Type::Union(_, members) => {
                let size = members
                    .iter()
                    .map(|m| self.get_type_size(&m.ty))
                    .max()
                    .unwrap_or(0);
                let union_alignment = self.get_type_alignment(ty);
                (size + union_alignment - 1) & !(union_alignment - 1)
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
                if let Type::Struct(_, _) | Type::Union(_, _) = ty {
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
            Stmt::Declaration(_, declarators) => {
                for declarator in declarators {
                    let size = self.get_type_size(&declarator.ty);
                    let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                        StackSlotKind::ExplicitSlot,
                        size,
                        0,
                    ));
                    self.variables
                        .insert(declarator.name, (slot, declarator.ty.clone()));
                    if let Some(init) = declarator.initializer {
                        if let Expr::StructInitializer(initializers) = *init {
                            let s = self.get_real_type(&declarator.ty)?;
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
                                            let member_alignment =
                                                self.get_type_alignment(&member.ty);
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
                                            let member_alignment =
                                                self.get_type_alignment(&member.ty);
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
                            if let Type::Struct(_, _) | Type::Union(_, _) = val_ty {
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
                }
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
                let inc_block = self.builder.create_block();
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
                self.loop_context.push((inc_block, exit_block));
                self.translate_stmt(*body)?;
                self.loop_context.pop();

                self.jump_to_block(inc_block);
                self.switch_to_block(inc_block);

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
        } else if let Type::Union(Some(name), members) = ty
            && members.is_empty()
        {
            return Ok(self.unions.get(name).unwrap().clone());
        }
        Ok(ty.clone())
    }

    /// Translates an expression into a Cranelift `Value`.
    fn translate_assignment(&mut self, lhs: Expr, rhs_val: Value) -> Result<(), CodegenError> {
        match lhs {
            Expr::Variable(name, _) => {
                let (slot, _) = self.variables.get(&name).unwrap();
                self.builder.ins().stack_store(rhs_val, slot, 0);
            }
            Expr::Deref(ptr) => {
                let (ptr, _) = self.translate_expr(*ptr)?;
                self.builder.ins().store(MemFlags::new(), rhs_val, ptr, 0);
            }
            Expr::Member(expr, member) => {
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
                        .store(MemFlags::new(), rhs_val, ptr, offset as i32);
                } else if let Type::Union(_, _) = s {
                    self.builder.ins().store(MemFlags::new(), rhs_val, ptr, 0);
                } else {
                    return Err(CodegenError::NotAStruct);
                }
            }
            _ => unimplemented!(),
        }
        Ok(())
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

        let unsigned_ty;
        let signed_ty;
        if left_ty.is_unsigned() {
            unsigned_ty = left_ty;
            signed_ty = right_ty;
        } else {
            unsigned_ty = right_ty;
            signed_ty = left_ty;
        }

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
        match ty {
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
            _ => self.builder.ins().stack_load(types::I64, slot, 0),
        }
    }

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
                if let Type::Struct(_, _) | Type::Union(_, _) = &ty {
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
                let loaded_val = self.load_variable(slot, &ty);
                Ok((loaded_val, ty))
            }
            Expr::Assign(lhs, rhs) => {
                let (rhs_val, ty) = self.translate_expr(*rhs)?;
                self.translate_assignment(*lhs, rhs_val)?;
                Ok((rhs_val, ty))
            }
            Expr::AssignAdd(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().iadd(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignSub(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().isub(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignMul(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().imul(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignDiv(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().sdiv(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignMod(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().srem(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignBitwiseAnd(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().band(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignBitwiseOr(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().bor(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignBitwiseXor(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().bxor(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignLeftShift(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().ishl(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::AssignRightShift(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs.clone())?;
                let (rhs_val, _) = self.translate_expr(*rhs)?;
                let result_val = self.builder.ins().sshr(lhs_val, rhs_val);
                self.translate_assignment(*lhs, result_val)?;
                Ok((result_val, lhs_ty))
            }
            Expr::Add(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs_val, rhs_ty) = self.translate_expr(*rhs)?;
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
                    _ => self.builder.ins().iadd(lhs_val, rhs_val),
                };
                let result_ty = if lhs_ty.is_pointer() {
                    lhs_ty
                } else {
                    common_ty
                };
                Ok((result_val, result_ty))
            }
            Expr::Sub(lhs, rhs) => {
                let (lhs_val, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs_val, rhs_ty) = self.translate_expr(*rhs)?;
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
                    _ => self.builder.ins().isub(lhs_val, rhs_val),
                };
                let result_ty = match (&lhs_ty, &rhs_ty) {
                    (Type::Pointer(_), Type::Pointer(_)) => Type::Int,
                    (Type::Pointer(_), Type::Int) => lhs_ty,
                    _ => common_ty,
                };
                Ok((result_val, result_ty))
            }
            Expr::Mul(lhs, rhs) => {
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                Ok((self.builder.ins().imul(lhs, rhs), common_ty))
            }
            Expr::Div(lhs, rhs) => {
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result = if common_ty.is_unsigned() {
                    self.builder.ins().udiv(lhs, rhs)
                } else {
                    self.builder.ins().sdiv(lhs, rhs)
                };
                Ok((result, common_ty))
            }
            Expr::Mod(lhs, rhs) => {
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let result = if common_ty.is_unsigned() {
                    self.builder.ins().urem(lhs, rhs)
                } else {
                    self.builder.ins().srem(lhs, rhs)
                };
                Ok((result, common_ty))
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
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let cc = if common_ty.is_unsigned() {
                    IntCC::UnsignedLessThan
                } else {
                    IntCC::SignedLessThan
                };
                let c = self.builder.ins().icmp(cc, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::GreaterThan(lhs, rhs) => {
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let cc = if common_ty.is_unsigned() {
                    IntCC::UnsignedGreaterThan
                } else {
                    IntCC::SignedGreaterThan
                };
                let c = self.builder.ins().icmp(cc, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::LessThanOrEqual(lhs, rhs) => {
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let cc = if common_ty.is_unsigned() {
                    IntCC::UnsignedLessThanOrEqual
                } else {
                    IntCC::SignedLessThanOrEqual
                };
                let c = self.builder.ins().icmp(cc, lhs, rhs);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::GreaterThanOrEqual(lhs, rhs) => {
                let (lhs, lhs_ty) = self.translate_expr(*lhs)?;
                let (rhs, rhs_ty) = self.translate_expr(*rhs)?;
                let common_ty = self.usual_arithmetic_conversions(&lhs_ty, &rhs_ty);
                let cc = if common_ty.is_unsigned() {
                    IntCC::UnsignedGreaterThanOrEqual
                } else {
                    IntCC::SignedGreaterThanOrEqual
                };
                let c = self.builder.ins().icmp(cc, lhs, rhs);
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
                } else if let Expr::Member(struct_expr, member_name) = *expr {
                    let (base_ptr, base_ty) = self.translate_expr(*struct_expr)?;
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
                            // Offset is always 0 for unions
                            Ok((base_ptr, Type::Pointer(Box::new(member_ty))))
                        }
                        _ => Err(CodegenError::NotAStruct),
                    }
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

                        if let Type::Struct(_, _) | Type::Union(_, _) | Type::Array(_, _) =
                            member_ty
                        {
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
            Expr::Call(name, args, _location) => {
                let (callee, ret_ty, is_variadic) = self
                    .functions
                    .get(&name)
                    .cloned()
                    .unwrap_or_else(|| panic!("Undefined function: {}", name));

                let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

                let mut arg_values = Vec::new();
                if let Type::Struct(_, _) | Type::Union(_, _) = ret_ty {
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

                let call = if is_variadic {
                    let mut sig = self.signatures.get(&name).unwrap().clone();
                    // `arg_values` has the real number of arguments to pass, including any hidden pointers.
                    // `sig.params` has the number of fixed parameters.
                    // The difference is the number of variadic arguments.
                    for _ in 0..(arg_values.len() - sig.params.len()) {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    let sig_ref = self.builder.func.import_signature(sig);
                    let callee_addr = self.builder.ins().func_addr(types::I64, local_callee);
                    self.builder
                        .ins()
                        .call_indirect(sig_ref, callee_addr, &arg_values)
                } else {
                    self.builder.ins().call(local_callee, &arg_values)
                };

                if let Type::Struct(_, _) | Type::Union(_, _) = ret_ty {
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
                let (ptr, ty) = self.translate_expr(*expr)?;
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

                    if let Type::Struct(_, _) | Type::Union(_, _) | Type::Array(_, _) = member_ty {
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
            Expr::Cast(ty, expr) => {
                let (val, _) = self.translate_expr(*expr)?;
                let cast_val = match *ty {
                    Type::Char | Type::UnsignedChar => self.builder.ins().ireduce(types::I8, val),
                    Type::Short | Type::UnsignedShort => {
                        self.builder.ins().ireduce(types::I16, val)
                    }
                    Type::Bool => self.builder.ins().ireduce(types::I8, val),
                    _ => val, // Other types are already I64
                };

                // The ABI requires function arguments and return values to be I64,
                // so we extend smaller types back to I64 after casting.
                let extended_val = match *ty {
                    Type::Char | Type::Bool | Type::Short => {
                        self.builder.ins().sextend(types::I64, cast_val)
                    }
                    Type::UnsignedChar | Type::UnsignedShort => {
                        self.builder.ins().uextend(types::I64, cast_val)
                    }
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
                    let loaded_val = self.load_variable(slot, &ty);
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let new_val = self.builder.ins().iadd(loaded_val, one);
                    self.builder.ins().stack_store(new_val, slot, 0);
                    Ok((new_val, ty))
                } else {
                    unimplemented!()
                }
            }
            Expr::Decrement(expr) => {
                if let Expr::Variable(name, _) = *expr {
                    let (slot, ty) = self.variables.get(&name).unwrap();
                    let loaded_val = self.load_variable(slot, &ty);
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let new_val = self.builder.ins().isub(loaded_val, one);
                    self.builder.ins().stack_store(new_val, slot, 0);
                    Ok((new_val, ty))
                } else {
                    unimplemented!()
                }
            }
            Expr::PostIncrement(expr) => {
                if let Expr::Variable(name, _) = *expr {
                    let (slot, ty) = self.variables.get(&name).unwrap();
                    let loaded_val = self.load_variable(slot, &ty);
                    let one = self.builder.ins().iconst(types::I64, 1);
                    let new_val = self.builder.ins().iadd(loaded_val, one);
                    self.builder.ins().stack_store(new_val, slot, 0);
                    Ok((loaded_val, ty))
                } else {
                    unimplemented!()
                }
            }
            Expr::PostDecrement(expr) => {
                if let Expr::Variable(name, _) = *expr {
                    let (slot, ty) = self.variables.get(&name).unwrap();
                    let loaded_val = self.load_variable(slot, &ty);
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
                let val = self.builder.ins().band(lhs, rhs);
                Ok((val, Type::Int))
            }
            Expr::LogicalOr(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                let val = self.builder.ins().bor(lhs, rhs);
                Ok((val, Type::Int))
            }
            Expr::BitwiseOr(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().bor(lhs, rhs), Type::Int))
            }
            Expr::BitwiseXor(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().bxor(lhs, rhs), Type::Int))
            }
            Expr::BitwiseAnd(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().band(lhs, rhs), Type::Int))
            }
            Expr::LeftShift(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().ishl(lhs, rhs), Type::Int))
            }
            Expr::RightShift(lhs, rhs) => {
                let (lhs, _) = self.translate_expr(*lhs)?;
                let (rhs, _) = self.translate_expr(*rhs)?;
                Ok((self.builder.ins().sshr(lhs, rhs), Type::Int))
            }
            Expr::LogicalNot(expr) => {
                let (val, _) = self.translate_expr(*expr)?;
                let zero = self.builder.ins().iconst(types::I64, 0);
                let c = self.builder.ins().icmp(IntCC::Equal, val, zero);
                Ok((self.builder.ins().uextend(types::I64, c), Type::Int))
            }
            Expr::StructInitializer(_) | Expr::DesignatedInitializer(_, _) | Expr::Comma(..) => {
                Ok((self.builder.ins().iconst(types::I64, 0), Type::Int))
            }
        }
    }
}
