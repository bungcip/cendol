use crate::codegen::error::CodegenError;
use crate::parser::ast::{Expr, Type, TypedExpr, TypedInitializer, TypedStmt, TypedTranslationUnit};
use cranelift::prelude::*;
use cranelift_codegen::ir::Function;
use cranelift_codegen::ir::{types, AbiParam};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use translator::{BlockState, FunctionTranslator};

pub mod error;
mod translator;
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

use cranelift_codegen::ir::StackSlot;
use cranelift_module::DataId;

pub struct CodeGen {
    ctx: FunctionBuilderContext,
    module: ObjectModule,
    variables: SymbolTable<String, (Option<Variable>, Option<StackSlot>, Type)>,
    global_variables: HashMap<String, (DataId, Type)>,
    static_local_variables: HashMap<String, (DataId, Type)>,
    functions: HashMap<String, (FuncId, Type, bool)>,
    signatures: HashMap<String, cranelift::prelude::Signature>,
    structs: HashMap<String, Type>,
    unions: HashMap<String, Type>,
    pub enum_constants: HashMap<String, i64>,
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
        let ctx = FunctionBuilderContext::new();

        Self {
            ctx,
            module,
            variables: SymbolTable::new(),
            global_variables: HashMap::new(),
            static_local_variables: HashMap::new(),
            functions: HashMap::new(),
            signatures: HashMap::new(),
            structs: HashMap::new(),
            unions: HashMap::new(),
            enum_constants: HashMap::new(),
        }
    }

    /// Compiles a typed translation unit into a byte vector.
    ///
    /// # Arguments
    ///
    /// * `typed_unit` - The typed translation unit to compile.
    ///
    /// # Returns
    ///
    /// A `Result` containing the compiled byte vector, or a `CodegenError` if compilation fails.
    pub fn compile(mut self, typed_unit: TypedTranslationUnit) -> Result<Vec<u8>, CodegenError> {
        for global in &typed_unit.globals {
            match global {
                TypedStmt::FunctionDeclaration(ty, name, params, is_variadic) => {
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
                TypedStmt::Declaration(base_ty, declarators, _is_static) => {
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
                        } else {
                            // This is a global variable declaration.
                            let id = self
                                .module
                                .declare_data(&declarator.name, Linkage::Export, true, false)
                                .unwrap();

                            self.global_variables
                                .insert(declarator.name.clone(), (id, declarator.ty.clone()));

                            let mut data_desc = cranelift_module::DataDescription::new();

                            let size = FunctionTranslator::get_type_size_from_type(
                                &declarator.ty,
                                &self.structs,
                                &self.unions,
                            );

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
                        }
                    }
                }
                _ => {}
            }
        }

        // First, declare all functions
        for function in &typed_unit.functions {
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

        // Collect enum constants from global declarations
        for global in &typed_unit.globals {
            if let TypedStmt::Declaration(ty, _, _) = global
                && let Type::Enum(_name, members) = ty
                && !members.is_empty()
            {
                let mut next_value = 0;
                for (name, value, _span) in members {
                    let val = if let Some(expr) = value {
                        if let Expr::Number(num) = **expr {
                            num
                        } else {
                            -1 // Dummy value
                        }
                    } else {
                        next_value
                    };
                    self.enum_constants.insert(name.clone(), val);
                    next_value = val + 1;
                }
            }
        }

        // Collect enum constants from function bodies
        for function in &typed_unit.functions {
            self.collect_enum_constants_from_stmts(&function.body)?;
        }

        // Then, define all functions
        for function_def in typed_unit.functions {
            let (id, _, _) = self.functions.get(&function_def.name).unwrap();
            let sig = self.signatures.get(&function_def.name).unwrap().clone();
            let mut func = Function::new();
            func.signature = sig;

            let mut builder = FunctionBuilder::new(&mut func, &mut self.ctx);
            let entry_block = builder.create_block();
            builder.append_block_params_for_function_params(entry_block);
            builder.switch_to_block(entry_block);

            let mut translator = FunctionTranslator {
                builder,
                functions: &self.functions,
                variables: &mut self.variables,
                global_variables: &self.global_variables,
                static_local_variables: &mut self.static_local_variables,
                structs: &self.structs,
                unions: &self.unions,
                enum_constants: &self.enum_constants,
                module: &mut self.module,
                loop_context: Vec::new(),
                current_block_state: BlockState::Empty,
                signatures: &self.signatures,
                label_blocks: HashMap::new(),
                current_function_name: &function_def.name,
            };

            // Add parameters to variables and store block params
            let block_params = translator.builder.block_params(entry_block).to_vec();
            for (i, param) in function_def.params.iter().enumerate() {
                let size = translator.get_type_size(&param.ty);
                let slot = translator
                    .builder
                    .create_sized_stack_slot(cranelift::prelude::StackSlotData::new(
                        cranelift::prelude::StackSlotKind::ExplicitSlot,
                        size,
                        0,
                    ));
                translator
                    .variables
                    .insert(param.name.clone(), (None, Some(slot), param.ty.clone()));
                // Store the block parameter into the stack slot
                translator
                    .builder
                    .ins()
                    .stack_store(block_params[i], slot, 0);
            }

            let mut terminated = false;
            for stmt in function_def.body {
                if terminated {
                    break;
                }
                let term = translator.translate_typed_stmt(stmt)?;
                terminated = term;
            }

            if !terminated {
                let zero = translator.builder.ins().iconst(types::I64, 0);
                translator.builder.ins().return_(&[zero]);
            }
            translator.builder.seal_all_blocks();
            translator.builder.finalize();
            let mut context = self.module.make_context();
            context.func = func;
            self.module.define_function(*id, &mut context).unwrap();
        }

        let product = self.module.finish();
        let object_bytes = product.emit().unwrap();
        Ok(object_bytes)
    }

    fn collect_enum_constants_from_stmts(
        &mut self,
        stmts: &[TypedStmt],
    ) -> Result<(), CodegenError> {
        for stmt in stmts {
            match stmt {
                TypedStmt::Declaration(ty, _, _) => {
                    if let Type::Enum(_name, members) = ty
                        && !members.is_empty()
                    {
                        let mut next_value = 0;
                        for (name, value, _span) in members {
                            let val = if let Some(expr) = value {
                                if let Expr::Number(num) = **expr {
                                    num
                                } else {
                                    -1 // Dummy value
                                }
                            } else {
                                next_value
                            };
                            self.enum_constants.insert(name.clone(), val);
                            next_value = val + 1;
                        }
                    }
                }
                TypedStmt::Block(stmts) => {
                    self.collect_enum_constants_from_stmts(stmts)?;
                }
                TypedStmt::If(_, then, otherwise) => {
                    self.collect_enum_constants_from_stmts(&[*then.clone()])?;
                    if let Some(otherwise) = otherwise {
                        self.collect_enum_constants_from_stmts(&[*otherwise.clone()])?;
                    }
                }
                TypedStmt::While(_, body) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                TypedStmt::For(_, _, _, body) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                TypedStmt::DoWhile(body, _) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                TypedStmt::Switch(_, body) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                TypedStmt::Case(_, body) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                TypedStmt::Default(body) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                TypedStmt::Label(_, body) => {
                    self.collect_enum_constants_from_stmts(&[*body.clone()])?;
                }
                _ => {}
            }
        }
        Ok(())
    }
}
