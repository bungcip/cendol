use crate::ast::BinaryOp;
use crate::ast::nodes;
use crate::ast::*;
use crate::driver::compiler::SemaOutput;
use crate::mir::{
    self, BinaryOp as MirBinaryOp, CallTarget, ConstValue, ConstValueId, LocalId, MirBlockId, MirBuilder,
    MirFunctionId, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId,
};
use crate::semantic::ArraySizeType;
use crate::semantic::QualType;
use crate::semantic::StructMember;
use crate::semantic::SymbolKind;
use crate::semantic::SymbolRef;
use crate::semantic::SymbolTable;
use crate::semantic::TypeKind;
use crate::semantic::{DefinitionState, TypeRef, TypeRegistry};
use crate::semantic::{Namespace, ScopeId};
use crate::source_manager::SourceSpan;
use hashbrown::HashMap;
use log::debug;

use crate::mir::GlobalId;

pub struct AstToMirLowerer<'a> {
    ast: &'a Ast,
    symbol_table: &'a mut SymbolTable,
    mir_builder: MirBuilder,
    current_function: Option<MirFunctionId>,
    current_block: Option<MirBlockId>,
    registry: &'a TypeRegistry,
    local_map: HashMap<SymbolRef, LocalId>,
    global_map: HashMap<SymbolRef, GlobalId>,
    #[allow(unused)]
    label_map: HashMap<NameId, MirBlockId>,
    type_cache: HashMap<TypeRef, TypeId>,
}

impl<'a> AstToMirLowerer<'a> {
    pub fn new(ast: &'a Ast, symbol_table: &'a mut SymbolTable, registry: &'a TypeRegistry) -> Self {
        let mir_builder = MirBuilder::new(mir::MirModuleId::new(1).unwrap());
        Self {
            ast,
            symbol_table,
            mir_builder,
            current_function: None,
            current_block: None,
            local_map: HashMap::new(),
            global_map: HashMap::new(),
            label_map: HashMap::new(),
            registry,
            type_cache: HashMap::new(),
        }
    }

    pub fn lower_module_complete(&mut self) -> SemaOutput {
        debug!("Starting semantic analysis and MIR construction (complete)");
        let root = self.ast.get_root();
        self.lower_node_ref(root, ScopeId::GLOBAL);
        debug!("Semantic analysis complete");
        self.finalize_globals();

        let module = self.mir_builder.finalize_module();
        let functions = self.mir_builder.get_functions().clone();
        let blocks = self.mir_builder.get_blocks().clone();
        let locals = self.mir_builder.get_locals().clone();
        let globals = self.mir_builder.get_globals().clone();
        let types = self.mir_builder.get_types().clone();
        let constants = self.mir_builder.get_constants().clone();
        let statements = self.mir_builder.get_statements().clone();

        SemaOutput {
            module,
            functions,
            blocks,
            locals,
            globals,
            types,
            constants,
            statements,
        }
    }

    fn finalize_globals(&mut self) {
        let tentative_entries: Vec<(NameId, SymbolRef)> = self
            .symbol_table
            .get_scope(ScopeId::GLOBAL)
            .symbols
            .values()
            .filter_map(|entry_ref| {
                let entry = self.symbol_table.get_symbol(*entry_ref);
                if matches!(entry.kind, SymbolKind::Variable { .. }) && entry.def_state == DefinitionState::Tentative {
                    Some((entry.name, *entry_ref))
                } else {
                    None
                }
            })
            .collect();

        for (_, entry_ref) in &tentative_entries {
            let entry = self.symbol_table.get_symbol_mut(*entry_ref);
            if let SymbolKind::Variable { .. } = &mut entry.kind
                && entry.def_state == DefinitionState::Tentative
            {
                entry.def_state = DefinitionState::Defined;
            }
        }
    }

    fn lower_node_ref(&mut self, node_ref: NodeRef, scope_id: ScopeId) {
        let node_kind = self.ast.get_node(node_ref).kind.clone();
        let node_span = self.ast.get_node(node_ref).span;

        match node_kind {
            NodeKind::TranslationUnit(nodes) => {
                // Ensure all global functions (including declarations) have a MIR representation.
                // This is done before traversing the AST to ensure that function calls
                // can be resolved even if the function is defined later in the file or is external.
                let global_scope = self.symbol_table.get_scope(ScopeId::GLOBAL);
                let mut global_symbols: Vec<_> = global_scope.symbols.values().copied().collect();

                // Sort by symbol name to ensure deterministic order for snapshot tests
                global_symbols.sort_by_key(|s| self.symbol_table.get_symbol(*s).name);

                for sym_ref in global_symbols {
                    let (symbol_name, symbol_type_info, is_function) = {
                        let symbol = self.symbol_table.get_symbol(sym_ref);
                        (
                            symbol.name,
                            symbol.type_info,
                            matches!(symbol.kind, SymbolKind::Function { .. }),
                        )
                    };

                    if is_function {
                        if self
                            .mir_builder
                            .get_functions()
                            .iter()
                            .any(|(_, f)| f.name == symbol_name)
                        {
                            continue;
                        }

                        let func_type = self.registry.get(symbol_type_info).clone();
                        if let TypeKind::Function {
                            return_type,
                            parameters,
                            ..
                        } = &func_type.kind
                        {
                            let return_mir_type = self.lower_type_to_mir(*return_type);
                            let param_mir_types = parameters
                                .iter()
                                .map(|p| self.lower_type_to_mir(p.param_type.ty))
                                .collect();
                            self.mir_builder
                                .create_function(symbol_name, param_mir_types, return_mir_type);
                        } else {
                            // This case should ideally not be reached for a SymbolKind::Function
                            let return_mir_type = self.get_int_type();
                            self.mir_builder.create_function(symbol_name, vec![], return_mir_type);
                        }
                    }
                }
                for child_ref in nodes {
                    self.lower_node_ref(child_ref, ScopeId::GLOBAL);
                }
            }
            NodeKind::Function(function_data) => self.lower_function(node_ref, &function_data),
            NodeKind::VarDecl(var_decl) => self.lower_var_declaration(scope_id, &var_decl, node_span),
            NodeKind::CompoundStatement(nodes) => self.lower_compound_statement(node_ref, &nodes),
            NodeKind::DeclarationList(nodes) => {
                for child_ref in nodes {
                    self.lower_node_ref(child_ref, scope_id);
                }
            }
            _ => self.try_lower_as_statement(scope_id, node_ref),
        }
    }

    fn try_lower_as_statement(&mut self, scope_id: ScopeId, node_ref: NodeRef) {
        let node = self.ast.get_node(node_ref);
        match node.kind.clone() {
            NodeKind::Return(expr) => self.lower_return_statement(scope_id, &expr),
            NodeKind::If(if_stmt) => self.lower_if_statement(scope_id, &if_stmt),
            NodeKind::While(while_stmt) => self.lower_while_statement(scope_id, &while_stmt),
            NodeKind::For(for_stmt) => self.lower_for_statement(scope_id, &for_stmt),
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                self.lower_expression(scope_id, expr_ref);
            }
            _ => {}
        }
    }

    fn lower_initializer_list(
        &mut self,
        scope_id: ScopeId,
        inits: &[nodes::DesignatedInitializer],
        members: &[StructMember],
        target_ty: QualType,
    ) -> Operand {
        let mut field_operands = Vec::new();
        let mut current_field_idx = 0;

        for init in inits {
            let field_idx = if let Some(designator) = init.designation.first() {
                if let Designator::FieldName(name) = designator {
                    members.iter().position(|m| m.name == *name).unwrap()
                } else {
                    panic!("Array designator for struct initializer");
                }
            } else {
                let idx = current_field_idx;
                current_field_idx += 1;
                idx
            };

            let member_ty = members[field_idx].member_type;
            let operand = self.lower_initializer(scope_id, init.initializer, member_ty);
            field_operands.push((field_idx, operand));
        }

        let is_global = self.current_function.is_none();
        if is_global {
            let const_fields = field_operands
                .into_iter()
                .map(|(idx, op)| {
                    if let Operand::Constant(const_id) = op {
                        (idx, const_id)
                    } else if let Operand::AddressOf(place) = op {
                        if let Place::Global(global_id) = *place {
                            (idx, self.create_constant(ConstValue::GlobalAddress(global_id)))
                        } else {
                            panic!("Global initializer address is not a global variable");
                        }
                    } else {
                        panic!("Global initializer is not a constant expression");
                    }
                })
                .collect();
            let const_val = ConstValue::StructLiteral(const_fields);
            Operand::Constant(self.create_constant(const_val))
        } else {
            let rval = Rvalue::StructLiteral(field_operands);
            let mir_ty = self.lower_type_to_mir(target_ty.ty);
            let (_, place) = self.create_temp_local_with_assignment(rval, mir_ty);
            Operand::Copy(Box::new(place))
        }
    }

    fn lower_initializer(&mut self, scope_id: ScopeId, init_ref: NodeRef, target_ty: QualType) -> Operand {
        let init_node_kind = self.ast.get_node(init_ref).kind.clone();
        let target_ty_kind = &self.registry.get(target_ty.ty).kind.clone();

        match (init_node_kind, target_ty_kind) {
            (NodeKind::InitializerList(inits), TypeKind::Record { members, .. }) => {
                self.lower_initializer_list(scope_id, &inits, members, target_ty)
            }
            _ => {
                // It's a simple expression initializer.
                self.lower_expression(scope_id, init_ref)
            }
        }
    }

    fn lower_compound_statement(&mut self, node_ref: NodeRef, nodes: &[NodeRef]) {
        let scope_id = self.ast.scope_of(node_ref);
        for &stmt_ref in nodes {
            self.lower_node_ref(stmt_ref, scope_id);
        }
    }

    fn lower_function(&mut self, node_ref: NodeRef, function_data: &FunctionData) {
        let symbol_entry = self.symbol_table.get_symbol(function_data.symbol);
        let func_name = symbol_entry.name;

        // Find the existing function in the MIR builder. It should have been created by the pre-pass.
        let func_id = self
            .mir_builder
            .get_functions()
            .iter()
            .find(|(_, f)| f.name == func_name)
            .map(|(id, _)| *id)
            .expect("Function not found in MIR builder, pre-pass failed?");

        self.current_function = Some(func_id);
        self.mir_builder.set_current_function(func_id);

        // Only create blocks and lower body if there is a body.
        // Declarations without bodies are handled by the pre-pass.
        if !matches!(&self.ast.get_node(function_data.body).kind, NodeKind::CompoundStatement(nodes) if nodes.is_empty())
        {
            let entry_block_id = self.mir_builder.create_block();
            self.mir_builder.set_function_entry_block(func_id, entry_block_id);
            self.current_block = Some(entry_block_id);
            self.mir_builder.set_current_block(entry_block_id);

            // Parameter locals are now created in `create_function`. We just need to
            // map the SymbolRef to the LocalId.
            let scope_id = self.ast.scope_of(node_ref);
            let mir_function = self.mir_builder.get_functions().get(&func_id).unwrap().clone();
            for (param_decl, local_id) in function_data.params.iter().zip(mir_function.params.iter()) {
                self.local_map.insert(param_decl.symbol, *local_id);
            }

            self.lower_node_ref(function_data.body, scope_id);
        }
    }

    fn lower_var_declaration(&mut self, scope_id: ScopeId, var_decl: &VarDeclData, _span: SourceSpan) {
        let mir_type_id = self.lower_type_to_mir(var_decl.ty.ty);
        let (entry_ref, _) = self
            .symbol_table
            .lookup(var_decl.name, scope_id, Namespace::Ordinary)
            .unwrap();

        let is_global = self.current_function.is_none();

        if is_global {
            let initial_value_id = var_decl.init.and_then(|init_ref| {
                let operand = self.lower_initializer(scope_id, init_ref, var_decl.ty);
                if let Operand::Constant(const_id) = operand {
                    Some(const_id)
                } else {
                    None
                }
            });

            if let Some(global_id) = self.global_map.get(&entry_ref) {
                if let Some(init_id) = initial_value_id {
                    self.mir_builder.set_global_initializer(*global_id, init_id);
                }
            } else {
                let symbol = self.symbol_table.get_symbol(entry_ref);
                let final_init = if initial_value_id.is_some() {
                    initial_value_id
                } else if symbol.def_state == DefinitionState::Tentative {
                    Some(self.create_constant(ConstValue::Zero))
                } else {
                    None
                };

                let global_id = self
                    .mir_builder
                    .create_global_with_init(var_decl.name, mir_type_id, false, final_init);
                self.global_map.insert(entry_ref, global_id);
            }
        } else {
            let local_id = self.mir_builder.create_local(Some(var_decl.name), mir_type_id, false);
            self.local_map.insert(entry_ref, local_id);

            if let Some(initializer) = var_decl.init {
                let init_operand = self.lower_initializer(scope_id, initializer, var_decl.ty);
                self.emit_assignment(Place::Local(local_id), init_operand);
            }
        }
    }

    fn lower_expression(&mut self, scope_id: ScopeId, expr_ref: NodeRef) -> Operand {
        let ty = self
            .ast
            .get_node(expr_ref)
            .resolved_type
            .get()
            .expect("Type not resolved");
        let node_kind = self.ast.get_node(expr_ref).kind.clone();

        let mir_ty = self.lower_type_to_mir(ty.ty);

        match &node_kind {
            NodeKind::LiteralInt(val) => Operand::Constant(self.create_constant(ConstValue::Int(*val))),
            NodeKind::LiteralFloat(val) => Operand::Constant(self.create_constant(ConstValue::Float(*val))),
            NodeKind::LiteralChar(val) => Operand::Constant(self.create_constant(ConstValue::Int(*val as i64))),
            NodeKind::LiteralString(val) => {
                let string_type = self.lower_type_to_mir(ty.ty);
                let const_val = ConstValue::String(val.to_string());
                let const_id = self.create_constant(const_val);
                let global_name = self.mir_builder.get_next_anonymous_global_name();
                let global_id =
                    self.mir_builder
                        .create_global_with_init(global_name, string_type, true, Some(const_id));

                let addr_const_val = ConstValue::GlobalAddress(global_id);
                Operand::Constant(self.create_constant(addr_const_val))
            }
            NodeKind::Ident(_, symbol_ref) => {
                let resolved_ref = symbol_ref.get().unwrap();
                let entry = self.symbol_table.get_symbol(resolved_ref);

                match &entry.kind {
                    SymbolKind::Variable { is_global, .. } => {
                        if *is_global {
                            let global_id = self.global_map.get(&resolved_ref).unwrap();
                            Operand::Copy(Box::new(Place::Global(*global_id)))
                        } else {
                            let local_id = self.local_map.get(&resolved_ref).unwrap();
                            Operand::Copy(Box::new(Place::Local(*local_id)))
                        }
                    }
                    SymbolKind::Function { .. } => {
                        let func_id = self
                            .mir_builder
                            .get_functions()
                            .iter()
                            .find(|(_, f)| f.name == entry.name)
                            .map(|(id, _)| *id)
                            .unwrap();
                        let const_val = ConstValue::FunctionAddress(func_id);
                        Operand::Constant(self.create_constant(const_val))
                    }
                    SymbolKind::EnumConstant { value } => {
                        Operand::Constant(self.create_constant(ConstValue::Int(*value)))
                    }
                    _ => panic!("Unexpected symbol kind"),
                }
            }
            NodeKind::UnaryOp(op, operand_ref) => match *op {
                UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                    self.lower_compound_assignment(scope_id, op, *operand_ref, *operand_ref)
                }
                UnaryOp::AddrOf => {
                    let operand = self.lower_expression(scope_id, *operand_ref);
                    if let Operand::Copy(place) = operand {
                        Operand::AddressOf(place)
                    } else {
                        panic!("Cannot take address of a non-lvalue");
                    }
                }
                _ => {
                    let operand = self.lower_expression(scope_id, *operand_ref);
                    let mir_op = self.map_ast_unary_op_to_mir(op);
                    let rval = Rvalue::UnaryOp(mir_op, operand);
                    let (_, place) = self.create_temp_local_with_assignment(rval, mir_ty);
                    Operand::Copy(Box::new(place))
                }
            },
            NodeKind::BinaryOp(op, left_ref, right_ref) => {
                let lhs = self.lower_expression(scope_id, *left_ref);
                let rhs = self.lower_expression(scope_id, *right_ref);
                let mir_op = self.map_ast_binary_op_to_mir(op);
                let rval = Rvalue::BinaryOp(mir_op, lhs, rhs);
                let (_, place) = self.create_temp_local_with_assignment(rval, mir_ty);
                Operand::Copy(Box::new(place))
            }
            NodeKind::Assignment(_, left_ref, right_ref) => {
                let lhs_op = self.lower_expression(scope_id, *left_ref);
                let rhs_op = self.lower_expression(scope_id, *right_ref);

                if let Operand::Copy(place) = lhs_op {
                    self.emit_assignment(*place, rhs_op.clone());
                    rhs_op
                } else {
                    panic!("LHS of assignment is not a place");
                }
            }
            NodeKind::FunctionCall(func_ref, args) => {
                let callee = self.lower_expression(scope_id, *func_ref);

                let mut arg_operands = Vec::new();
                for arg in args {
                    arg_operands.push(self.lower_expression(scope_id, *arg));
                }

                let call_target = if let Operand::Constant(const_id) = callee {
                    if let ConstValue::FunctionAddress(func_id) =
                        self.mir_builder.get_constants().get(&const_id).unwrap()
                    {
                        CallTarget::Direct(*func_id)
                    } else {
                        panic!("Expected function address");
                    }
                } else {
                    CallTarget::Indirect(callee)
                };

                let rval = Rvalue::Call(call_target, arg_operands);
                let (_, place) = self.create_temp_local_with_assignment(rval, mir_ty);
                Operand::Copy(Box::new(place))
            }
            NodeKind::MemberAccess(obj_ref, field_name, is_arrow) => {
                let obj_operand = self.lower_expression(scope_id, *obj_ref);
                let obj_ty = self.ast.get_node(*obj_ref).resolved_type.get().unwrap();
                let record_ty = if *is_arrow {
                    if let TypeKind::Pointer { pointee } = &self.registry.get(obj_ty.ty).kind {
                        *pointee
                    } else {
                        panic!("Arrow access on non-pointer type");
                    }
                } else {
                    obj_ty.ty
                };

                let record_kind = &self.registry.get(record_ty).kind;
                if let TypeKind::Record { members, .. } = record_kind {
                    let field_idx = members.iter().position(|m| m.name == *field_name).unwrap();
                    let place = if let Operand::Copy(place) = obj_operand {
                        Place::StructField(place, field_idx)
                    } else {
                        let mir_type = self.lower_type_to_mir(obj_ty.ty);
                        let (_, temp_place) =
                            self.create_temp_local_with_assignment(Rvalue::Use(obj_operand), mir_type);
                        Place::StructField(Box::new(temp_place), field_idx)
                    };
                    Operand::Copy(Box::new(place))
                } else {
                    panic!("Member access on non-record type");
                }
            }
            NodeKind::IndexAccess(arr_ref, idx_ref) => {
                let arr_operand = self.lower_expression(scope_id, *arr_ref);
                let idx_operand = self.lower_expression(scope_id, *idx_ref);

                let arr_place = if let Operand::Copy(place) = arr_operand {
                    *place
                } else {
                    let arr_ty = self.ast.get_node(*arr_ref).resolved_type.get().unwrap();
                    let mir_type = self.lower_type_to_mir(arr_ty.ty);
                    let (_, temp_place) = self.create_temp_local_with_assignment(Rvalue::Use(arr_operand), mir_type);
                    temp_place
                };

                Operand::Copy(Box::new(Place::ArrayIndex(Box::new(arr_place), Box::new(idx_operand))))
            }
            _ => Operand::Constant(self.create_constant(ConstValue::Int(0))),
        }
    }

    fn lower_return_statement(&mut self, scope_id: ScopeId, expr: &Option<NodeRef>) {
        let operand = expr.map(|expr_ref| self.lower_expression(scope_id, expr_ref));
        self.mir_builder.set_terminator(Terminator::Return(operand));
    }

    fn lower_if_statement(&mut self, scope_id: ScopeId, if_stmt: &IfStmt) {
        let then_block = self.mir_builder.create_block();
        let else_block = self.mir_builder.create_block();
        let merge_block = self.mir_builder.create_block();

        let cond_operand = self.lower_expression(scope_id, if_stmt.condition);
        self.mir_builder
            .set_terminator(Terminator::If(cond_operand, then_block, else_block));

        self.mir_builder.set_current_block(then_block);
        self.lower_node_ref(if_stmt.then_branch, scope_id);
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(merge_block));
        }

        self.mir_builder.set_current_block(else_block);
        if let Some(else_branch) = &if_stmt.else_branch {
            self.lower_node_ref(*else_branch, scope_id);
        }
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(merge_block));
        }

        self.mir_builder.set_current_block(merge_block);
        self.current_block = Some(merge_block);
    }

    fn lower_while_statement(&mut self, scope_id: ScopeId, while_stmt: &WhileStmt) {
        let cond_block = self.mir_builder.create_block();
        let body_block = self.mir_builder.create_block();
        let exit_block = self.mir_builder.create_block();

        self.mir_builder.set_terminator(Terminator::Goto(cond_block));
        self.mir_builder.set_current_block(cond_block);

        let cond_operand = self.lower_expression(scope_id, while_stmt.condition);
        self.mir_builder
            .set_terminator(Terminator::If(cond_operand, body_block, exit_block));

        self.mir_builder.set_current_block(body_block);
        self.lower_node_ref(while_stmt.body, scope_id);
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(cond_block));
        }

        self.mir_builder.set_current_block(exit_block);
        self.current_block = Some(exit_block);
    }

    fn lower_for_statement(&mut self, scope_id: ScopeId, for_stmt: &ForStmt) {
        let cond_block = self.mir_builder.create_block();
        let body_block = self.mir_builder.create_block();
        let increment_block = self.mir_builder.create_block();
        let exit_block = self.mir_builder.create_block();

        if let Some(init_ref) = for_stmt.init {
            self.lower_node_ref(init_ref, scope_id);
        }
        self.mir_builder.set_terminator(Terminator::Goto(cond_block));
        self.mir_builder.set_current_block(cond_block);

        if let Some(cond_ref) = for_stmt.condition {
            let cond_operand = self.lower_expression(scope_id, cond_ref);
            self.mir_builder
                .set_terminator(Terminator::If(cond_operand, body_block, exit_block));
        } else {
            self.mir_builder.set_terminator(Terminator::Goto(body_block));
        }

        self.mir_builder.set_current_block(body_block);
        self.lower_node_ref(for_stmt.body, scope_id);
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(increment_block));
        }

        self.mir_builder.set_current_block(increment_block);
        if let Some(inc_ref) = for_stmt.increment {
            self.lower_expression(scope_id, inc_ref);
        }
        self.mir_builder.set_terminator(Terminator::Goto(cond_block));

        self.mir_builder.set_current_block(exit_block);
        self.current_block = Some(exit_block);
    }

    fn emit_assignment(&mut self, place: Place, operand: Operand) {
        if self.mir_builder.current_block_has_terminator() {
            return;
        }
        let rvalue = Rvalue::Use(operand);
        let stmt = MirStmt::Assign(place, rvalue);
        self.mir_builder.add_statement(stmt);
    }

    fn lower_type_to_mir(&mut self, type_ref: TypeRef) -> TypeId {
        if let Some(type_id) = self.type_cache.get(&type_ref) {
            return *type_id;
        }

        let ast_type_kind = self.registry.get(type_ref).kind.clone();
        let mir_type = match &ast_type_kind {
            TypeKind::Void => MirType::Void,
            TypeKind::Bool => MirType::Bool,
            TypeKind::Char { is_signed } => MirType::Int {
                is_signed: *is_signed,
                width: 8,
            },
            TypeKind::Short { is_signed } => MirType::Int {
                is_signed: *is_signed,
                width: 16,
            },
            TypeKind::Int { is_signed } => MirType::Int {
                is_signed: *is_signed,
                width: 32,
            },
            TypeKind::Long {
                is_signed,
                is_long_long,
            } => MirType::Int {
                is_signed: *is_signed,
                width: if *is_long_long { 64 } else { 32 },
            },
            TypeKind::Float => MirType::Float { width: 32 },
            TypeKind::Double { is_long_double } => MirType::Float {
                width: if *is_long_double { 80 } else { 64 },
            },
            TypeKind::Pointer { pointee } => MirType::Pointer {
                pointee: self.lower_type_to_mir(*pointee),
            },
            TypeKind::Array { element_type, size } => {
                let element = self.lower_type_to_mir(*element_type);
                let size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };
                MirType::Array { element, size }
            }
            TypeKind::Function {
                return_type,
                parameters,
                ..
            } => {
                let return_type = self.lower_type_to_mir(*return_type);
                let mut params = Vec::new();
                for p in parameters {
                    params.push(self.lower_type_to_mir(p.param_type.ty));
                }
                MirType::Function { return_type, params }
            }
            TypeKind::Record {
                tag, members, is_union, ..
            } => {
                let name = tag.unwrap_or_else(|| NameId::new("anonymous"));
                if *is_union {
                    let placeholder = MirType::Union {
                        name,
                        fields: Vec::new(),
                    };
                    let type_id = self.mir_builder.add_type(placeholder);
                    self.type_cache.insert(type_ref, type_id);

                    let mut fields = Vec::new();
                    for m in members {
                        fields.push((m.name, self.lower_type_to_mir(m.member_type.ty)));
                    }
                    self.mir_builder.update_union_fields(type_id, fields);

                    return type_id;
                } else {
                    let placeholder = MirType::Struct {
                        name,
                        fields: Vec::new(),
                    };
                    let type_id = self.mir_builder.add_type(placeholder);
                    self.type_cache.insert(type_ref, type_id);

                    let mut fields = Vec::new();
                    for m in members {
                        fields.push((m.name, self.lower_type_to_mir(m.member_type.ty)));
                    }
                    self.mir_builder.update_struct_fields(type_id, fields);

                    return type_id;
                }
            }
            _ => MirType::Int {
                is_signed: true,
                width: 32,
            },
        };
        self.mir_builder.add_type(mir_type)
    }

    fn create_constant(&mut self, value: ConstValue) -> ConstValueId {
        self.mir_builder.create_constant(value)
    }

    fn get_int_type(&mut self) -> TypeId {
        self.mir_builder.add_type(MirType::Int {
            is_signed: true,
            width: 32,
        })
    }

    fn create_temp_local(&mut self, type_id: TypeId) -> (LocalId, Place) {
        let local_id = self.mir_builder.create_local(None, type_id, false);
        let place = Place::Local(local_id);
        (local_id, place)
    }

    fn create_temp_local_with_assignment(&mut self, rvalue: Rvalue, type_id: TypeId) -> (LocalId, Place) {
        let (local_id, place) = self.create_temp_local(type_id);
        let assign_stmt = MirStmt::Assign(place.clone(), rvalue);
        self.mir_builder.add_statement(assign_stmt);
        (local_id, place)
    }

    fn map_ast_binary_op_to_mir(&self, ast_op: &BinaryOp) -> MirBinaryOp {
        match ast_op {
            BinaryOp::Add => MirBinaryOp::Add,
            BinaryOp::Sub => MirBinaryOp::Sub,
            BinaryOp::Mul => MirBinaryOp::Mul,
            BinaryOp::Div => MirBinaryOp::Div,
            BinaryOp::Mod => MirBinaryOp::Mod,
            BinaryOp::BitAnd => MirBinaryOp::BitAnd,
            BinaryOp::BitOr => MirBinaryOp::BitOr,
            BinaryOp::BitXor => MirBinaryOp::BitXor,
            BinaryOp::LShift => MirBinaryOp::LShift,
            BinaryOp::RShift => MirBinaryOp::RShift,
            BinaryOp::Equal => MirBinaryOp::Equal,
            BinaryOp::NotEqual => MirBinaryOp::NotEqual,
            BinaryOp::Less => MirBinaryOp::Less,
            BinaryOp::LessEqual => MirBinaryOp::LessEqual,
            BinaryOp::Greater => MirBinaryOp::Greater,
            BinaryOp::GreaterEqual => MirBinaryOp::GreaterEqual,
            BinaryOp::LogicAnd => MirBinaryOp::LogicAnd,
            BinaryOp::LogicOr => MirBinaryOp::LogicOr,
            BinaryOp::Comma => MirBinaryOp::Comma,
            other => panic!("Unsupported binary operator: {:?}", other),
        }
    }

    fn map_ast_unary_op_to_mir(&self, ast_op: &UnaryOp) -> mir::UnaryOp {
        match ast_op {
            UnaryOp::AddrOf => mir::UnaryOp::AddrOf,
            UnaryOp::Deref => mir::UnaryOp::Deref,
            UnaryOp::Plus => panic!("Unary plus should be handled by type resolver"),
            UnaryOp::Minus => mir::UnaryOp::Neg,
            UnaryOp::BitNot => mir::UnaryOp::Not,
            UnaryOp::LogicNot => mir::UnaryOp::Not,
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => {
                panic!("Pre-increment/decrement should be desugared in lower_expression")
            }
        }
    }

    fn lower_compound_assignment(
        &mut self,
        scope_id: ScopeId,
        op: &UnaryOp,
        lhs_ref: NodeRef,
        _rhs_ref: NodeRef,
    ) -> Operand {
        let lhs = self.lower_expression(scope_id, lhs_ref);
        let rhs = Operand::Constant(self.create_constant(ConstValue::Int(1))); // For inc/dec, RHS is 1

        let mir_op = match op {
            UnaryOp::PreIncrement => MirBinaryOp::Add,
            UnaryOp::PreDecrement => MirBinaryOp::Sub,
            _ => unreachable!(),
        };

        let rval = Rvalue::BinaryOp(mir_op, lhs.clone(), rhs);
        let mir_ty = self.lower_type_to_mir(self.ast.get_node(lhs_ref).resolved_type.get().unwrap().ty);
        let (_, place) = self.create_temp_local_with_assignment(rval, mir_ty);

        if let Operand::Copy(lhs_place) = lhs {
            self.emit_assignment(*lhs_place, Operand::Copy(Box::new(place.clone())));
        } else {
            panic!("LHS of assignment is not a place");
        }

        Operand::Copy(Box::new(place))
    }
}
