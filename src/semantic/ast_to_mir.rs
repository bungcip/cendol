use crate::ast::BinaryOp;
use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::driver::compiler::SemaOutput;
use crate::mir::{
    self, BinaryOp as MirBinaryOp, CallTarget, ConstValue, ConstValueId, LocalId, MirBlockId, MirBuilder,
    MirFunctionId, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId,
};
use crate::semantic::SymbolKind;
use crate::semantic::SymbolRef;
use crate::semantic::SymbolTable;
use crate::semantic::{DefinitionState, TypeContext, TypeRef};
use crate::semantic::{Namespace, ScopeId};
use crate::source_manager::SourceSpan;
use hashbrown::HashMap;
use log::debug;

pub struct AstToMirLowerer<'a, 'src> {
    ast: &'a mut Ast,
    diag: &'src mut DiagnosticEngine,
    symbol_table: &'a mut SymbolTable,
    mir_builder: MirBuilder,
    current_function: Option<MirFunctionId>,
    current_block: Option<MirBlockId>,
    type_ctx: &'a mut TypeContext,
    local_map: HashMap<SymbolRef, LocalId>,
    label_map: HashMap<NameId, MirBlockId>,
    has_errors: bool,
}

impl<'a, 'src> AstToMirLowerer<'a, 'src> {
    pub fn new(
        ast: &'a mut Ast,
        diag: &'src mut DiagnosticEngine,
        symbol_table: &'a mut SymbolTable,
        type_ctx: &'a mut TypeContext,
    ) -> Self {
        let mir_builder = MirBuilder::new(mir::MirModuleId::new(1).unwrap());
        Self {
            ast,
            diag,
            symbol_table,
            mir_builder,
            current_function: None,
            current_block: None,
            local_map: HashMap::new(),
            label_map: HashMap::new(),
            has_errors: false,
            type_ctx,
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
            if let SymbolKind::Variable { .. } = &mut entry.kind {
                if entry.def_state == DefinitionState::Tentative {
                    entry.def_state = DefinitionState::Defined;
                }
            }
        }
    }

    fn lower_node_ref(&mut self, node_ref: NodeRef, scope_id: ScopeId) {
        let node_kind = self.ast.get_node(node_ref).kind.clone();
        let node_span = self.ast.get_node(node_ref).span;

        match node_kind {
            NodeKind::TranslationUnit(nodes) => {
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
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                self.lower_expression(scope_id, expr_ref);
            }
            _ => {}
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

        let func_type = self.type_ctx.get(function_data.ty);
        let return_mir_type = if let TypeKind::Function { return_type, .. } = &func_type.kind {
            self.lower_type_to_mir(*return_type)
        } else {
            self.get_int_type()
        };

        let func_id = self.mir_builder.create_function(func_name, return_mir_type);
        self.current_function = Some(func_id);
        self.mir_builder.set_current_function(func_id);

        let entry_block_id = self.mir_builder.create_block();
        self.mir_builder.set_function_entry_block(func_id, entry_block_id);
        self.current_block = Some(entry_block_id);
        self.mir_builder.set_current_block(entry_block_id);

        let scope_id = self.ast.scope_of(node_ref);
        for param in &function_data.params {
            self.lower_function_parameter(scope_id, param);
        }
        self.lower_node_ref(function_data.body, scope_id);
    }

    fn lower_function_parameter(&mut self, scope_id: ScopeId, param: &ParamDecl) {
        let param_name = self.symbol_table.get_symbol(param.symbol).name;
        let mir_type_id = self.lower_type_to_mir(param.ty.ty);
        let local_id = self.mir_builder.create_local(Some(param_name), mir_type_id, true);

        let (existing_entry, _) = self
            .symbol_table
            .lookup(param_name, scope_id, Namespace::Ordinary)
            .unwrap();
        self.local_map.insert(existing_entry, local_id);
    }

    fn lower_var_declaration(&mut self, scope_id: ScopeId, var_decl: &VarDeclData, _span: SourceSpan) {
        let mir_type_id = self.lower_type_to_mir(var_decl.ty.ty);
        let is_global = self.current_function.is_none();

        if is_global {
            let initial_value_id = var_decl.init.and_then(|init| {
                if let Operand::Constant(const_id) = self.lower_expression(scope_id, init) {
                    Some(const_id)
                } else {
                    None
                }
            });
            self.mir_builder
                .create_global_with_init(var_decl.name, mir_type_id, false, initial_value_id);
        } else {
            let (entry_ref, _) = self
                .symbol_table
                .lookup(var_decl.name, scope_id, Namespace::Ordinary)
                .unwrap();
            let local_id = self.mir_builder.create_local(Some(var_decl.name), mir_type_id, false);
            self.local_map.insert(entry_ref, local_id);

            if let Some(initializer) = var_decl.init {
                let init_operand = self.lower_expression(scope_id, initializer);
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
                Operand::Constant(self.create_constant(ConstValue::String(val.to_string())))
            }
            NodeKind::Ident(_, symbol_ref) => {
                let resolved_ref = symbol_ref.get().unwrap();
                let entry = self.symbol_table.get_symbol(resolved_ref);

                match &entry.kind {
                    SymbolKind::Variable { is_global, .. } => {
                        if *is_global {
                            let global_id = self
                                .mir_builder
                                .get_globals()
                                .iter()
                                .find(|(_, g)| g.name == entry.name)
                                .map(|(id, _)| *id)
                                .unwrap();
                            Operand::Copy(Box::new(Place::Global(global_id)))
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
                    _ => panic!("Unexpected symbol kind"),
                }
            }
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

    fn emit_assignment(&mut self, place: Place, operand: Operand) {
        if self.mir_builder.current_block_has_terminator() {
            return;
        }
        let rvalue = Rvalue::Use(operand);
        let stmt = MirStmt::Assign(place, rvalue);
        self.mir_builder.add_statement(stmt);
    }

    fn lower_type_to_mir(&mut self, type_ref: TypeRef) -> TypeId {
        let ast_type_kind = self.type_ctx.get(type_ref).kind.clone();
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
                let mut fields = Vec::new();
                for m in members {
                    fields.push((m.name, self.lower_type_to_mir(m.member_type.ty)));
                }

                if *is_union {
                    MirType::Union { name, fields }
                } else {
                    MirType::Struct { name, fields }
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
            _ => panic!("Unsupported binary operator"),
        }
    }
}
