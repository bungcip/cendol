use crate::codegen::error::CodegenError;
use crate::parser::ast::{Expr, Program, Stmt};
use cranelift::prelude::*;
use cranelift_codegen::ir::{StackSlot, StackSlotData, StackSlotKind};
use cranelift_codegen::Context;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, Value};
use cranelift_codegen::settings;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;

pub struct CodeGen {
    builder_context: FunctionBuilderContext,
    ctx: Context,
    module: ObjectModule,
    variables: HashMap<String, StackSlot>,
}

impl CodeGen {
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
        }
    }

    pub fn compile(mut self, program: Program) -> Result<Vec<u8>, CodegenError> {
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

        let mut translator = FunctionTranslator {
            builder,
            variables: &mut self.variables,
        };
        for stmt in program.function.body {
            translator.translate_stmt(stmt);
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

struct FunctionTranslator<'a, 'b> {
    builder: FunctionBuilder<'a>,
    variables: &'b mut HashMap<String, StackSlot>,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
    fn translate_stmt(&mut self, stmt: Stmt) -> Value {
        match stmt {
            Stmt::Return(expr) => {
                let value = self.translate_expr(expr);
                self.builder.ins().return_(&[value]);
                value
            }
            Stmt::Declaration(_ty, name) => {
                let slot = self.builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, 8, 0));
                self.variables.insert(name, slot);
                let val = self.builder.ins().iconst(types::I64, 0);
                self.builder.ins().stack_store(val, slot, 0);
                val
            }
            Stmt::Block(stmts) => {
                let mut last = self.builder.ins().iconst(types::I64, 0);
                for stmt in stmts {
                    last = self.translate_stmt(stmt);
                }
                last
            }
            _ => unimplemented!(),
        }
    }

    fn translate_expr(&mut self, expr: Expr) -> Value {
        match expr {
            Expr::Number(n) => self.builder.ins().iconst(types::I64, n),
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
            _ => unimplemented!(),
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
        }
    }
}
