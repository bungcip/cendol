use crate::codegen::error::CodegenError;
use crate::parser::ast::Expr;
use crate::semantic::typed_ast::{
    TypedExpr, TypedFunctionDecl, TypedInitializer, TypedLValue, TypedStmt, TypedTranslationUnit,
};
use crate::parser::string_interner::StringId;
use crate::types::{TypeId, TypeKind};
use cranelift::prelude::*;
use cranelift_codegen::binemit::Reloc;
use cranelift_codegen::ir::Function;
use cranelift_codegen::ir::{AbiParam, types};
use cranelift_codegen::settings;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::{DataDescription, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use std::collections::HashSet;
use translator::{BlockState, FunctionTranslator};

pub mod error;
mod translator;
mod util;
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
    variables: SymbolTable<StringId, (Option<Variable>, Option<StackSlot>, TypeId)>,
    global_variables: HashMap<StringId, (DataId, TypeId)>,
    static_local_variables: HashMap<StringId, (DataId, TypeId)>,
    functions: HashMap<StringId, (FuncId, TypeId, bool)>,
    signatures: HashMap<StringId, cranelift::prelude::Signature>,
    structs: HashMap<StringId, TypeId>,
    unions: HashMap<StringId, TypeId>,
    pub enum_constants: HashMap<StringId, i64>,
    anonymous_string_count: usize,
}

impl Default for CodeGen {
    /// Creates a new `CodeGen` with default settings.
    fn default() -> Self {
        Self::new()
    }
}

fn collect_label_names(stmt: &TypedStmt, set: &mut HashSet<StringId>) {
    match stmt {
        TypedStmt::Label(name, body) => {
            set.insert(*name);
            collect_label_names(body, set);
        }
        TypedStmt::Block(stmts) => {
            for s in stmts {
                collect_label_names(s, set);
            }
        }
        TypedStmt::If(_, then_blk, else_opt) => {
            collect_label_names(then_blk, set);
            if let Some(e) = else_opt {
                collect_label_names(e, set);
            }
        }
        TypedStmt::While(_, body) => collect_label_names(body, set),
        TypedStmt::DoWhile(body, _) => collect_label_names(body, set),
        TypedStmt::For(_init, _, _, body) => {
            // If init contains nested stmts, handle accordingly. For now traverse body.
            collect_label_names(body, set);
        }
        TypedStmt::Switch(_, body) => collect_label_names(body, set),
        TypedStmt::Case(_, body) => collect_label_names(body, set),
        TypedStmt::Default(body) => collect_label_names(body, set),
        // Leaves that cannot contain nested stmt labels: Return, Goto, Declaration, Expr, Empty, Break, Continue
        _ => {}
    }
}

impl CodeGen {
    fn translate_function(
        &mut self,
        function_def: TypedFunctionDecl,
    ) -> Result<(), CodegenError> {
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
            current_function_name: function_def.name,
            anonymous_string_count: &mut self.anonymous_string_count,
        };

        // Add parameters to variables and store block params
        let block_params = translator.builder.block_params(entry_block).to_vec();
        for (i, param) in function_def.params.iter().enumerate() {
            let size = translator.get_type_size(param.ty);
            let slot = translator
                .builder
                .create_sized_stack_slot(cranelift::prelude::StackSlotData::new(
                    cranelift::prelude::StackSlotKind::ExplicitSlot,
                    size,
                    0,
                ));
            translator
                .variables
                .insert(param.name, (None, Some(slot), param.ty));
            // Store the block parameter into the stack slot
            translator
                .builder
                .ins()
                .stack_store(block_params[i], slot, 0);
        }

        // Predeclare label blocks
        let mut label_names = HashSet::new();
        for s in &function_def.body {
            collect_label_names(s, &mut label_names);
        }

        for name in label_names {
            let b = translator.builder.create_block();
            translator.label_blocks.insert(name, b);
            // eprintln!("predeclared label: {} -> {:?}", name, b);
        }

        let mut terminated = false;
        for stmt in function_def.body {
            if terminated {
                // Only process labels after termination
                if let TypedStmt::Label(..) = stmt {
                    let _ = translator.translate_typed_stmt(stmt)?;
                }
                continue;
            }
            let term = translator.translate_typed_stmt(stmt)?;
            terminated = term;
        }

        // Seal all label blocks that were created but not yet sealed
        // Note: seal_all_blocks() will handle sealing all blocks, including labels
        // So we don't need to manually seal them here

        // Seal the entry block as well
        translator.builder.seal_block(entry_block);

        if !terminated {
            let zero = translator.builder.ins().iconst(types::I64, 0);
            translator.builder.ins().return_(&[zero]);
        }
        translator.builder.seal_all_blocks();
        translator.builder.finalize();

        let mut context = self.module.make_context();
        context.func = func;
        self.module.define_function(*id, &mut context).unwrap();

        Ok(())
    }
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
            anonymous_string_count: 0,
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
        // First, declare all functions
        for global in &typed_unit.globals {
            if let crate::semantic::typed_ast::TypedGlobalDecl::Function(function) = global {
                let mut sig = self.module.make_signature();
                if function.return_type.is_record() {
                    sig.params.push(AbiParam::new(types::I64));
                }
                for param in &function.params {
                    let abi_param = match param.ty.kind() {
                        crate::types::TypeKind::Float => AbiParam::new(types::F32),
                        crate::types::TypeKind::Double => AbiParam::new(types::F64),
                        _ => AbiParam::new(types::I64),
                    };
                    sig.params.push(abi_param);
                }
                sig.returns.push(AbiParam::new(types::I64));

                let id = self.module.declare_function(
                    function.name.as_str(),
                    if function.name.as_str() == "main" {
                        Linkage::Export
                    } else {
                        Linkage::Local
                    },
                    &sig,
                )?;
                self.functions.insert(
                    function.name,
                    (id, function.return_type.clone(), function.is_variadic),
                );
                self.signatures.insert(function.name, sig);
            }
        }

        // Then, define all functions and global variables
        for global in typed_unit.globals {
            match global {
                crate::semantic::typed_ast::TypedGlobalDecl::Function(function) => {
                    self.translate_function(function)?;
                }
                crate::semantic::typed_ast::TypedGlobalDecl::Variable(variables) => {
                    for variable in variables {
                        let name = variable.name;
                        let ty = variable.ty;
                        let initializer = variable.initializer;

                        let data_id = self.module.declare_data(
                            &name.to_string(),
                            cranelift_module::Linkage::Local,
                            true,
                            false,
                        )?;
                        self.global_variables.insert(name, (data_id, ty));
                    }
                }
            }
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
                TypedStmt::Declaration(declarators) => {
                    for declarator in declarators {
                        if let TypeKind::Enum{name: _, underlying_type: _, variants} = declarator.ty.kind()
                            && !variants.is_empty() {
                                let mut next_value = 0;
                                for variant in variants {
                                    let val = variant.value;
                                    self.enum_constants.insert(variant.name, val);
                                    next_value = val + 1;
                                }
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
