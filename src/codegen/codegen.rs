use crate::parser::ast::Expr;
use crate::codegen::error::CodegenError;
use cranelift::prelude::*;
use cranelift_codegen::Context;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{Linkage, Module, DataDescription};
use cranelift_codegen::settings;
use cranelift_codegen::ir::types;
use cranelift_codegen::ir::{AbiParam, InstBuilder, Value};

pub struct CodeGen {
    builder_context: FunctionBuilderContext,
    ctx: Context,
    data_ctx: DataDescription,
    module: JITModule,
}

impl CodeGen {
    pub fn new() -> Self {
        let mut flag_builder = settings::builder();
        flag_builder.set("use_colocated_libcalls", "false").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa_builder = cranelift_native::builder().unwrap_or_else(|msg| {
            panic!("host machine is not supported: {}", msg);
        });
        let isa = isa_builder.finish(settings::Flags::new(flag_builder)).unwrap();
        let module = JITModule::new(JITBuilder::with_isa(isa, cranelift_module::default_libcall_names()));
        let ctx = module.make_context();
        let builder_context = FunctionBuilderContext::new();
        let data_ctx = DataDescription::new();

        Self {
            builder_context,
            ctx,
            data_ctx,
            module,
        }
    }

    pub fn compile(&mut self, expr: Expr) -> Result<*const u8, CodegenError> {
        self.ctx.func.signature.params.push(AbiParam::new(types::I64));
        self.ctx.func.signature.returns.push(AbiParam::new(types::I64));

        let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        let result = translate_expr(&mut builder, expr);
        builder.ins().return_(&[result]);
        builder.finalize();

        let id = self.module.declare_function("main", Linkage::Local, &self.ctx.func.signature).unwrap();
        self.module.define_function(id, &mut self.ctx).unwrap();
        self.module.clear_context(&mut self.ctx);
        self.module.finalize_definitions().unwrap();

        let code = self.module.get_finalized_function(id);
        Ok(code)
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
    }
}
