use crate::codegen::error::CodegenError;
use crate::parser::ast::{Expr, Program, Stmt};
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

/// A code generator that translates an AST into machine code.
use cranelift_module::FuncId;

pub struct CodeGen {
    builder_context: FunctionBuilderContext,
    ctx: Context,
    module: ObjectModule,
    variables: HashMap<String, StackSlot>,
    functions: HashMap<String, FuncId>,
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
            variables: HashMap::new(),
            functions: HashMap::new(),
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
        for global in program.globals {
            match global {
                Stmt::FunctionDeclaration(_, _, _) => {}
                _ => unimplemented!(),
            }
        }

        self.ctx
            .func
            .signature
            .returns
            .push(AbiParam::new(types::I64));

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let pointer_type = self.module.isa().pointer_type();
        let mut translator = FunctionTranslator {
            builder,
            functions: &mut self.functions,
            variables: &mut self.variables,
            module: &mut self.module,
            loop_context: Vec::new(),
            current_block_state: BlockState::Empty,
            pointer_type,
        };
        for stmt in program.function.body {
            let _ = translator.translate_stmt(stmt);
        }
        translator.builder.finalize();

        let id = self
            .module
            .declare_function("main", Linkage::Export, &self.ctx.func.signature)
            .unwrap();
        self.module.define_function(id, &mut self.ctx).unwrap();
        self.module.clear_context(&mut self.ctx);

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
    functions: &'b mut HashMap<String, FuncId>,
    variables: &'b mut HashMap<String, StackSlot>,
    module: &'b mut ObjectModule,
    loop_context: Vec<(Block, Block)>,
    current_block_state: BlockState,
    pointer_type: types::Type,
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

    /// Translates a statement into Cranelift IR.
    fn translate_stmt(&mut self, stmt: Stmt) -> bool {
        match stmt {
            Stmt::Return(expr) => {
                let value = self.translate_expr(expr);
                self.builder.ins().return_(&[value]);
                self.current_block_state = BlockState::Filled;
                true
            }
            Stmt::Declaration(_ty, name, initializer) => {
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(
                    StackSlotKind::ExplicitSlot,
                    8,
                    0,
                ));
                self.variables.insert(name, slot);
                if let Some(init) = initializer {
                    let val = self.translate_expr(*init);
                    self.builder.ins().stack_store(val, slot, 0);
                } else {
                    let val = self.builder.ins().iconst(types::I64, 0);
                    self.builder.ins().stack_store(val, slot, 0);
                };
                false
            }
            Stmt::Block(stmts) => {
                let mut terminated = false;
                for stmt in stmts {
                    if terminated {
                        break;
                    }
                    let term = self.translate_stmt(stmt);
                    terminated = term;
                }
                terminated
            }
            Stmt::If(cond, then, otherwise) => {
                let condition_value = self.translate_expr(*cond);

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(condition_value, then_block, &[], else_block, &[]);

                self.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                let then_terminated = self.translate_stmt(*then);
                let if_has_return = self.current_block_state == BlockState::Filled;
                self.jump_to_block(merge_block);

                self.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                if let Some(otherwise) = otherwise {
                    self.translate_stmt(*otherwise);
                }
                if self.current_block_state != BlockState::Filled {
                    self.jump_to_block(merge_block);
                    self.switch_to_block(merge_block);
                } else if !if_has_return {
                    self.switch_to_block(merge_block);
                }

                then_terminated
            }
            Stmt::While(cond, body) => {
                let header_block = self.builder.create_block();
                let body_block = self.builder.create_block();
                let exit_block = self.builder.create_block();

                self.jump_to_block(header_block);
                self.switch_to_block(header_block);

                let cond_val = self.translate_expr(*cond);
                self.builder
                    .ins()
                    .brif(cond_val, body_block, &[], exit_block, &[]);

                self.switch_to_block(body_block);
                self.builder.seal_block(body_block);

                self.loop_context.push((header_block, exit_block));
                self.translate_stmt(*body);
                self.loop_context.pop();

                self.jump_to_block(header_block);

                self.switch_to_block(exit_block);
                self.builder.seal_block(header_block);
                self.builder.seal_block(exit_block);

                false
            }
            Stmt::Break => {
                let (_, exit_block) = self.loop_context.last().unwrap();
                self.jump_to_block(*exit_block);
                true
            }
            Stmt::Continue => {
                let (header_block, _) = self.loop_context.last().unwrap();
                self.jump_to_block(*header_block);
                true
            }
            Stmt::Expr(expr) => {
                self.translate_expr(expr);
                false
            }
            _ => unimplemented!(),
        }
    }

    /// Translates an expression into a Cranelift `Value`.
    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
            Expr::Number(n) => self.builder.ins().iconst(types::I64, n),
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
                self.builder.ins().global_value(types::I64, local_id)
            }
            Expr::Variable(name) => {
                let slot = self.variables.get(&name).unwrap();
                self.builder.ins().stack_load(types::I64, *slot, 0)
            }
            Expr::Assign(lhs, rhs) => {
                let value = self.translate_expr(*rhs);
                if let Expr::Variable(name) = *lhs {
                    let slot = self.variables.get(&name).unwrap();
                    self.builder.ins().stack_store(value, *slot, 0);
                } else if let Expr::Deref(ptr) = *lhs {
                    let ptr = self.translate_expr(*ptr);
                    self.builder.ins().store(MemFlags::new(), value, ptr, 0);
                } else {
                    unimplemented!()
                }
                value
            }
            Expr::Add(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().iadd(lhs, rhs)
            }
            Expr::Sub(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().isub(lhs, rhs)
            }
            Expr::Mul(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().imul(lhs, rhs)
            }
            Expr::Div(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                self.builder.ins().sdiv(lhs, rhs)
            }
            Expr::Equal(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                let c = self.builder.ins().icmp(IntCC::Equal, lhs, rhs);
                self.builder.ins().uextend(types::I64, c)
            }
            Expr::NotEqual(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                let c = self.builder.ins().icmp(IntCC::NotEqual, lhs, rhs);
                self.builder.ins().uextend(types::I64, c)
            }
            Expr::LessThan(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                let c = self.builder.ins().icmp(IntCC::SignedLessThan, lhs, rhs);
                self.builder.ins().uextend(types::I64, c)
            }
            Expr::GreaterThan(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                let c = self.builder.ins().icmp(IntCC::SignedGreaterThan, lhs, rhs);
                self.builder.ins().uextend(types::I64, c)
            }
            Expr::LessThanOrEqual(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                let c = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, lhs, rhs);
                self.builder.ins().uextend(types::I64, c)
            }
            Expr::GreaterThanOrEqual(lhs, rhs) => {
                let lhs = self.translate_expr(*lhs);
                let rhs = self.translate_expr(*rhs);
                let c = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, lhs, rhs);
                self.builder.ins().uextend(types::I64, c)
            }
            Expr::Neg(expr) => {
                let val = self.translate_expr(*expr);
                self.builder.ins().ineg(val)
            }
            Expr::Deref(expr) => {
                let ptr = self.translate_expr(*expr);
                self.builder.ins().load(types::I64, MemFlags::new(), ptr, 0)
            }
            Expr::AddressOf(expr) => {
                if let Expr::Variable(name) = *expr {
                    let slot = self.variables.get(&name).unwrap();
                    self.builder.ins().stack_addr(types::I64, *slot, 0)
                } else {
                    unimplemented!()
                }
            }
            Expr::Call(name, args) => {
                let mut sig = self.module.make_signature();
                sig.returns.push(AbiParam::new(types::I32)); // puts returns int (i32)
                for arg in &args {
                    match arg {
                        Expr::String(_) => sig.params.push(AbiParam::new(self.pointer_type)), // string literal is char*
                        _ => sig.params.push(AbiParam::new(types::I64)), // default to i64 for other types
                    }
                }

                let callee = match self.functions.get(&name) {
                    Some(callee) => *callee,
                    None => {
                        let callee = self
                            .module
                            .declare_function(&name, Linkage::Import, &sig)
                            .unwrap();
                        self.functions.insert(name.clone(), callee);
                        callee
                    }
                };
                let local_callee = self.module.declare_func_in_func(callee, self.builder.func);

                let mut arg_values = Vec::new();
                for arg in args {
                    arg_values.push(self.translate_expr(arg));
                }

                let call = self.builder.ins().call(local_callee, &arg_values);
                self.builder.inst_results(call)[0]
            }
            Expr::Ternary(cond, then_expr, else_expr) => {
                let condition_value = self.translate_expr(*cond);

                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();

                self.builder
                    .ins()
                    .brif(condition_value, then_block, &[], else_block, &[]);

                self.switch_to_block(then_block);
                self.builder.seal_block(then_block);
                let then_value = self.translate_expr(*then_expr);
                self.builder.ins().jump(merge_block, &[then_value.into()]);
                self.current_block_state = BlockState::Filled;

                self.switch_to_block(else_block);
                self.builder.seal_block(else_block);
                let else_value = self.translate_expr(*else_expr);
                self.builder.ins().jump(merge_block, &[else_value.into()]);
                self.current_block_state = BlockState::Filled;

                self.switch_to_block(merge_block);
                self.builder.seal_block(merge_block);

                self.builder.append_block_param(merge_block, types::I64);

                self.switch_to_block(merge_block);

                let phi_value = self.builder.block_params(merge_block)[0];
                phi_value
            }
            _ => unimplemented!(),
        }
    }
}
