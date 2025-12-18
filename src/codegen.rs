//! Code generation module
//!
//! This module is responsible for translating the AST into machine code.

use crate::ast::{Ast, BinaryOp, Declarator, Node, NodeKind};
use cranelift::prelude::*;
use cranelift_module::Module;
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use target_lexicon::Triple;

pub struct CodeGenerator<'a> {
    builder_context: FunctionBuilderContext,
    ctx: cranelift::codegen::Context,
    module: ObjectModule,
    ast: &'a Ast,
}

impl<'a> CodeGenerator<'a> {
    pub fn new(ast: &'a Ast) -> Self {
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
            ctx: module.make_context(),
            module,
            ast,
        }
    }

    pub fn compile(mut self) -> Result<Vec<u8>, String> {
        self.translate();
        let id = self
            .module
            .declare_function("main", cranelift_module::Linkage::Export, &self.ctx.func.signature)
            .unwrap();
        self.module.define_function(id, &mut self.ctx).unwrap();
        self.module.clear_context(&mut self.ctx);
        let product = self.module.finish();
        let code = product.object.write().unwrap();
        Ok(code)
    }

    fn translate(&mut self) {
        let root_node = self.ast.get_root_node().unwrap();
        if let NodeKind::TranslationUnit(nodes) = &root_node.kind {
            for node_ref in nodes {
                let node = self.ast.get_node(*node_ref);
                if let NodeKind::FunctionDef(_) = &node.kind {
                    self.gen_function(node);
                }
            }
        }
    }

    fn gen_function(&mut self, node: &Node) {
        if let NodeKind::FunctionDef(data) = &node.kind {
            let declarator = &data.declarator;
            if let Declarator::Function(direct_declarator, ..) = declarator
                && let Declarator::Identifier(_name, ..) = &**direct_declarator
            {
                let int = self.module.target_config().pointer_type();
                self.ctx.func.signature.params.clear();
                self.ctx.func.signature.returns.push(AbiParam::new(int));
                let mut builder = FunctionBuilder::new(&mut self.ctx.func, &mut self.builder_context);
                let entry_block = builder.create_block();
                builder.switch_to_block(entry_block);
                builder.seal_block(entry_block);
                let mut vars = HashMap::new();
                let mut func_translator = FunctionTranslator {
                    builder,
                    module: &mut self.module,
                    vars: &mut vars,
                    ast: self.ast,
                };
                let body = self.ast.get_node(data.body);
                func_translator.gen_statement(body);
                func_translator.builder.finalize();
            }
        }
    }
}

struct FunctionTranslator<'a, 'b> {
    builder: FunctionBuilder<'a>,
    module: &'b mut ObjectModule,
    vars: &'b mut HashMap<String, Variable>,
    ast: &'a Ast,
}

impl<'a, 'b> FunctionTranslator<'a, 'b> {
    fn gen_statement(&mut self, node: &Node) {
        match &node.kind {
            NodeKind::CompoundStatement(nodes) => {
                for node_ref in nodes {
                    self.gen_statement(self.ast.get_node(*node_ref));
                }
            }
            NodeKind::Declaration(decl) => {
                for init_declarator in &decl.init_declarators {
                    if let Declarator::Identifier(name, ..) = &init_declarator.declarator {
                        let int = self.module.target_config().pointer_type();
                        let var = self.builder.declare_var(int);
                        if let Some(initializer) = &init_declarator.initializer {
                            let value = self.gen_expr(self.ast.get_node(initializer.get_expression()));
                            self.builder.def_var(var, value);
                        }
                        self.vars.insert(name.to_string(), var);
                    }
                }
            }
            NodeKind::Return(expr) => {
                let value = self.gen_expr(self.ast.get_node(*expr.as_ref().unwrap()));
                self.builder.ins().return_(&[value]);
            }
            _ => unimplemented!(),
        }
    }

    fn gen_expr(&mut self, node: &Node) -> Value {
        match &node.kind {
            NodeKind::LiteralInt(val) => {
                let int = self.module.target_config().pointer_type();
                self.builder.ins().iconst(int, *val)
            }
            NodeKind::BinaryOp(op, left, right) => {
                let left = self.gen_expr(self.ast.get_node(*left));
                let right = self.gen_expr(self.ast.get_node(*right));
                match op {
                    BinaryOp::Add => self.builder.ins().iadd(left, right),
                    _ => unimplemented!(),
                }
            }
            NodeKind::Ident(name, _) => {
                let var = self.vars.get(&name.to_string()).unwrap();
                self.builder.use_var(*var)
            }
            _ => unimplemented!(),
        }
    }
}

#[cfg(test)]
mod tests;
