use crate::codegen::error::CodegenError;
use crate::parser::ast::{Expr, Program, Stmt};
use cranelift::prelude::*;
use cranelift_codegen::Context;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, Value};
use cranelift_codegen::settings;
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};

pub struct CodeGen {
    builder_context: FunctionBuilderContext,
    ctx: Context,
    module: ObjectModule,
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

        translate_stmt(&mut builder, *program.function.body);
        builder.finalize();

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

fn translate_stmt(builder: &mut FunctionBuilder, stmt: Stmt) -> Value {
    match stmt {
        Stmt::Return(expr) => {
            let value = translate_expr(builder, expr);
            builder.ins().return_(&[value]);
            value
        }
        _ => unimplemented!(),
    }
}

fn translate_expr(builder: &mut FunctionBuilder, expr: Expr) -> Value {
    match expr {
        Expr::Number(n) => builder.ins().iconst(types::I64, n),
        Expr::Add(lhs, rhs) => {
            let lhs = translate_expr(builder, *lhs);
            let rhs = translate_expr(builder, *rhs);
            builder.ins().iadd(lhs, rhs)
        }
        Expr::Sub(lhs, rhs) => {
            let lhs = translate_expr(builder, *lhs);
            let rhs = translate_expr(builder, *rhs);
            builder.ins().isub(lhs, rhs)
        }
        Expr::Mul(lhs, rhs) => {
            let lhs = translate_expr(builder, *lhs);
            let rhs = translate_expr(builder, *rhs);
            builder.ins().imul(lhs, rhs)
        }
        Expr::Div(lhs, rhs) => {
            let lhs = translate_expr(builder, *lhs);
            let rhs = translate_expr(builder, *rhs);
            builder.ins().sdiv(lhs, rhs)
        }
        _ => unimplemented!(),
    }
}
