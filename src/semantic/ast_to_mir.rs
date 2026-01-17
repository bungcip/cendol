use crate::ast::BinaryOp;
use crate::ast::nodes;
use crate::ast::*;
use crate::mir::MirArrayLayout;
use crate::mir::MirProgram;
use crate::mir::MirRecordLayout;
use crate::mir::{
    self, BinaryFloatOp, BinaryIntOp, CallTarget, ConstValue, ConstValueId, LocalId, MirBlockId, MirBuilder,
    MirFunctionId, MirStmt, MirType, Operand, Place, Rvalue, Terminator, TypeId, UnaryFloatOp, UnaryIntOp,
};
use crate::semantic::ArraySizeType;
use crate::semantic::BuiltinType;
use crate::semantic::QualType;
use crate::semantic::StructMember;
use crate::semantic::SymbolKind;
use crate::semantic::SymbolRef;
use crate::semantic::SymbolTable;
use crate::semantic::TypeKind;
use crate::semantic::ValueCategory;
use crate::semantic::const_eval::{ConstEvalCtx, eval_const_expr};
use crate::semantic::{DefinitionState, TypeRef, TypeRegistry};
use crate::semantic::{ImplicitConversion, Namespace, ScopeId};
use crate::source_manager::SourceSpan;
use hashbrown::{HashMap, HashSet};
use log::debug;

use crate::mir::GlobalId;

pub(crate) struct AstToMirLowerer<'a> {
    ast: &'a Ast,
    symbol_table: &'a SymbolTable, // Now immutable
    mir_builder: MirBuilder,
    current_function: Option<MirFunctionId>,
    current_block: Option<MirBlockId>,
    registry: &'a TypeRegistry,
    local_map: HashMap<SymbolRef, LocalId>,
    global_map: HashMap<SymbolRef, GlobalId>,
    label_map: HashMap<NameId, MirBlockId>,
    type_cache: HashMap<TypeRef, TypeId>,
    type_conversion_in_progress: HashSet<TypeRef>,
    break_target: Option<MirBlockId>,
    continue_target: Option<MirBlockId>,
}

impl<'a> AstToMirLowerer<'a> {
    pub(crate) fn new(ast: &'a Ast, symbol_table: &'a SymbolTable, registry: &'a TypeRegistry) -> Self {
        let mir_builder = MirBuilder::new(mir::MirModuleId::new(1).unwrap(), 8);
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
            type_conversion_in_progress: HashSet::new(),
            break_target: None,
            continue_target: None,
        }
    }

    pub(crate) fn lower_module_complete(&mut self) -> MirProgram {
        debug!("Starting semantic analysis and MIR construction (complete)");
        let root = self.ast.get_root();
        self.lower_node_ref(root, ScopeId::GLOBAL);
        debug!("Semantic analysis complete");

        // Take ownership of the builder to consume it, replacing it with a dummy.
        let builder = std::mem::replace(
            &mut self.mir_builder,
            MirBuilder::new(mir::MirModuleId::new(1).unwrap(), 8),
        );
        let output = builder.consume();

        MirProgram {
            module: output.module,
            functions: output.functions,
            blocks: output.blocks,
            locals: output.locals,
            globals: output.globals,
            types: output.types,
            constants: output.constants,
            statements: output.statements,
            pointer_width: 8,
        }
    }

    fn lower_node_ref(&mut self, node_ref: NodeRef, scope_id: ScopeId) {
        let node_kind = self.ast.get_kind(node_ref).clone();
        let node_span = self.ast.get_span(node_ref);

        match node_kind {
            NodeKind::TranslationUnit(tu_data) => self.lower_translation_unit(&tu_data),
            NodeKind::Function(function_data) => self.lower_function(node_ref, &function_data),
            NodeKind::VarDecl(var_decl) => self.lower_var_declaration(scope_id, &var_decl, node_span),
            NodeKind::CompoundStatement(cs) => self.lower_compound_statement(node_ref, &cs),

            _ => self.try_lower_as_statement(scope_id, node_ref),
        }
    }

    fn lower_translation_unit(&mut self, tu_data: &nodes::TranslationUnitData) {
        self.predeclare_global_functions();
        for child_ref in tu_data.decl_start.range(tu_data.decl_len) {
            self.lower_node_ref(child_ref, ScopeId::GLOBAL);
        }
    }

    fn predeclare_global_functions(&mut self) {
        // Ensure all global functions (including declarations) have a MIR representation.
        // This is done before traversing the AST to ensure that function calls
        // can be resolved even if the function is defined later in the file or is external.
        let global_scope = self.symbol_table.get_scope(ScopeId::GLOBAL);
        let mut global_symbols: Vec<_> = global_scope.symbols.values().copied().collect();

        // Sort by symbol name to ensure deterministic order for snapshot tests
        global_symbols.sort_by_key(|s| self.symbol_table.get_symbol(*s).name);

        for sym_ref in global_symbols {
            let (symbol_name, symbol_type_info, is_function, has_definition) = {
                let symbol = self.symbol_table.get_symbol(sym_ref);
                (
                    symbol.name,
                    symbol.type_info,
                    matches!(symbol.kind, SymbolKind::Function { .. }),
                    symbol.def_state == DefinitionState::Defined,
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

                let func_type = self.registry.get(symbol_type_info.ty()).clone();
                if let TypeKind::Function {
                    return_type,
                    parameters,
                    is_variadic,
                    ..
                } = &func_type.kind
                {
                    let return_mir_type = self.lower_type(*return_type);
                    let param_mir_types = parameters.iter().map(|p| self.lower_qual_type(p.param_type)).collect();

                    self.define_or_declare_function(
                        symbol_name,
                        param_mir_types,
                        return_mir_type,
                        *is_variadic,
                        has_definition,
                    );
                } else {
                    // This case should ideally not be reached for a SymbolKind::Function
                    let return_mir_type = self.get_int_type();
                    self.define_or_declare_function(symbol_name, vec![], return_mir_type, false, has_definition);
                }
            }
        }
    }

    fn operand_to_const_id_strict(&mut self, op: Operand, msg: &str) -> ConstValueId {
        self.operand_to_const_id(op).expect(msg)
    }

    fn try_lower_as_statement(&mut self, scope_id: ScopeId, node_ref: NodeRef) {
        let node_kind = self.ast.get_kind(node_ref);
        match node_kind.clone() {
            NodeKind::Return(expr) => self.lower_return_statement(scope_id, &expr),
            NodeKind::If(if_stmt) => self.lower_if_statement(scope_id, &if_stmt),
            NodeKind::While(while_stmt) => self.lower_while_statement(scope_id, &while_stmt),
            NodeKind::DoWhile(body, condition) => self.lower_do_while_statement(scope_id, body, condition),
            NodeKind::For(for_stmt) => self.lower_for_statement(scope_id, &for_stmt),
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                // Expression statement: value not needed, only side-effects
                self.lower_expression(scope_id, expr_ref, false);
            }
            NodeKind::Break => {
                let target = self.break_target.unwrap();
                self.mir_builder.set_terminator(Terminator::Goto(target));
            }
            NodeKind::Continue => {
                let target = self.continue_target.unwrap();
                self.mir_builder.set_terminator(Terminator::Goto(target));
            }
            NodeKind::Goto(label_name, _) => self.lower_goto_statement(&label_name),
            NodeKind::Label(label_name, statement, _) => self.lower_label_statement(scope_id, &label_name, statement),
            _ => {}
        }
    }

    fn lower_initializer_list(
        &mut self,
        scope_id: ScopeId,
        list_data: &nodes::InitializerListData,
        members: &[StructMember],
        target_ty: QualType,
    ) -> Operand {
        let mut field_operands = Vec::new();
        let mut current_field_idx = 0;
        // Get record layout to detect anonymous-union-like members that share the
        // same offset. If multiple consecutive members have the same offset,
        // they form an (anonymous) union and should be initialized by a single
        // initializer.
        let (_rec_size, _rec_align, field_layouts, _) = self.registry.get_record_layout(target_ty.ty());

        for item_ref in list_data.init_start.range(list_data.init_len) {
            let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                continue;
            };
            let init = *init;
            let field_idx = if init.designator_len > 0 {
                let designator_ref = init.designator_start;
                if let NodeKind::Designator(Designator::FieldName(name)) = self.ast.get_kind(designator_ref) {
                    members.iter().position(|m| m.name == Some(*name)).unwrap()
                } else {
                    panic!("Array designator for struct initializer");
                }
            } else {
                // Heuristic: if the initializer is itself an initializer list (a subaggregate),
                // and the current member is not a record but a later member is a record,
                // prefer assigning this initializer to that later record member. This handles
                // cases with anonymous unions where members are flattened in the member list.
                let mut idx = current_field_idx;
                let init_node_kind = self.ast.get_kind(init.initializer);
                if let NodeKind::InitializerList(_) = init_node_kind {
                    if idx < members.len() {
                        let mut found = None;
                        for (j, item) in members.iter().enumerate().skip(idx) {
                            let mty = item.member_type;
                            if let TypeKind::Record { .. } = &self.registry.get(mty.ty()).kind {
                                found = Some(j);
                                break;
                            }
                        }
                        if let Some(j) = found {
                            // assign to the record member
                            idx = j;
                            current_field_idx = j + 1;
                            idx
                        } else {
                            current_field_idx += 1;
                            idx
                        }
                    } else {
                        current_field_idx += 1;
                        idx
                    }
                } else {
                    let tmp = idx;
                    current_field_idx += 1;
                    tmp
                }
            };

            let member_ty = members[field_idx].member_type;

            let operand = self.lower_initializer(scope_id, init.initializer, member_ty);
            field_operands.push((field_idx, operand));
            // If subsequent members share the same offset, they are part of a union
            // and should not consume additional initializers. Advance current_field_idx
            // past all members that share this field's offset.
            if field_idx < field_layouts.len() {
                let base_offset = field_layouts[field_idx].offset;
                let mut next_idx = field_idx + 1;
                while next_idx < field_layouts.len() && field_layouts[next_idx].offset == base_offset {
                    next_idx += 1;
                }
                current_field_idx = next_idx;
            }
        }

        self.finalize_struct_initializer(field_operands, target_ty)
    }

    fn lower_array_initializer(
        &mut self,
        scope_id: ScopeId,
        list_data: &nodes::InitializerListData,
        element_ty: QualType,
        _size: usize,
        target_ty: QualType,
    ) -> Operand {
        let mut elements = Vec::new();
        for item_ref in list_data.init_start.range(list_data.init_len) {
            let NodeKind::InitializerItem(init) = self.ast.get_kind(item_ref) else {
                continue;
            };
            let operand = self.lower_initializer(scope_id, init.initializer, element_ty);
            elements.push(operand);
        }

        self.finalize_array_initializer(elements, target_ty)
    }

    fn finalize_initializer_generic<T, C, R>(
        &mut self,
        target_ty: QualType,
        data: T,
        create_const: C,
        create_rvalue: R,
    ) -> Operand
    where
        C: FnOnce(&mut Self, T) -> ConstValue,
        R: FnOnce(T) -> Rvalue,
    {
        if self.current_function.is_none() {
            let const_val = create_const(self, data);
            Operand::Constant(self.create_constant(const_val))
        } else {
            let rval = create_rvalue(data);
            let mir_ty = self.lower_qual_type(target_ty);
            self.emit_rvalue_to_operand(rval, mir_ty)
        }
    }

    fn finalize_struct_initializer(&mut self, field_operands: Vec<(usize, Operand)>, target_ty: QualType) -> Operand {
        self.finalize_initializer_generic(
            target_ty,
            field_operands,
            |this, ops| {
                let const_fields = ops
                    .into_iter()
                    .map(|(idx, op)| {
                        let const_id =
                            this.operand_to_const_id_strict(op, "Global initializer is not a constant expression");
                        (idx, const_id)
                    })
                    .collect();
                ConstValue::StructLiteral(const_fields)
            },
            Rvalue::StructLiteral,
        )
    }

    fn finalize_array_initializer(&mut self, elements: Vec<Operand>, target_ty: QualType) -> Operand {
        self.finalize_initializer_generic(
            target_ty,
            elements,
            |this, elems| {
                let const_elements = elems
                    .into_iter()
                    .map(|op| {
                        this.operand_to_const_id_strict(op, "Global array initializer must be a constant expression")
                    })
                    .collect();
                ConstValue::ArrayLiteral(const_elements)
            },
            Rvalue::ArrayLiteral,
        )
    }

    fn lower_condition(&mut self, scope_id: ScopeId, condition: NodeRef) -> Operand {
        let cond_operand = self.lower_expression(scope_id, condition, true);
        // Apply conversions for condition (should be boolean)
        let cond_ty = self.ast.get_resolved_type(condition).unwrap();
        let cond_mir_ty = self.lower_qual_type(cond_ty);
        self.apply_conversions(cond_operand, condition, cond_mir_ty)
    }

    fn lower_initializer_to_const(
        &mut self,
        scope_id: ScopeId,
        init_ref: NodeRef,
        ty: QualType,
    ) -> Option<ConstValueId> {
        let operand = self.lower_initializer(scope_id, init_ref, ty);
        self.operand_to_const_id(operand)
    }

    fn lower_initializer(&mut self, scope_id: ScopeId, init_ref: NodeRef, target_ty: QualType) -> Operand {
        let init_node_kind = self.ast.get_kind(init_ref).clone();
        let target_ty_kind = self.registry.get(target_ty.ty()).kind.clone();

        match (init_node_kind, target_ty_kind) {
            (NodeKind::InitializerList(list), TypeKind::Record { members, .. }) => {
                self.lower_initializer_list(scope_id, &list, &members, target_ty)
            }
            (NodeKind::InitializerList(list), TypeKind::Array { element_type, size }) => {
                let element_ty = QualType::unqualified(element_type);
                let array_size = if let ArraySizeType::Constant(s) = size { s } else { 0 };
                self.lower_array_initializer(scope_id, &list, element_ty, array_size, target_ty)
            }
            (NodeKind::LiteralString(val), TypeKind::Array { element_type, size }) => {
                let element_ty_kind = &self.registry.get(element_type).kind;
                if matches!(element_ty_kind, TypeKind::Builtin(BuiltinType::Char)) {
                    let fixed_size = if let ArraySizeType::Constant(s) = size {
                        Some(s)
                    } else {
                        None
                    };
                    let array_const_id = self.create_string_array_const(&val, fixed_size);
                    Operand::Constant(array_const_id)
                } else {
                    let operand = self.lower_expression(scope_id, init_ref, true);
                    let mir_target_ty = self.lower_qual_type(target_ty);
                    self.apply_conversions(operand, init_ref, mir_target_ty)
                }
            }
            _ => {
                // It's a simple expression initializer.
                let operand = self.lower_expression(scope_id, init_ref, true);
                let mir_target_ty = self.lower_qual_type(target_ty);
                self.apply_conversions(operand, init_ref, mir_target_ty)
            }
        }
    }

    fn lower_compound_statement(&mut self, node_ref: NodeRef, cs: &nodes::CompoundStmtData) {
        let scope_id = self.ast.scope_of(node_ref);
        for stmt_ref in cs.stmt_start.range(cs.stmt_len) {
            let node_kind = self.ast.get_kind(stmt_ref);
            if self.mir_builder.current_block_has_terminator() {
                if let NodeKind::Label(..) = node_kind {
                    // This is a label, which is a valid entry point.
                    // Let lower_node_ref handle it, it will switch to a new block.
                } else {
                    // This statement is unreachable. Skip it.
                    continue;
                }
            }
            self.lower_node_ref(stmt_ref, scope_id)
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

        // Since we use define_function for functions with bodies, we should always have a body here
        let entry_block_id = self.mir_builder.create_block();
        self.mir_builder.set_function_entry_block(func_id, entry_block_id);
        self.current_block = Some(entry_block_id);
        self.mir_builder.set_current_block(entry_block_id);

        // Pre-scan for all labels in the function body to create their MIR blocks upfront.
        self.label_map.clear();
        self.scan_for_labels(function_data.body);

        // Parameter locals are now created in `define_function`. We just need to
        // map the SymbolRef to the LocalId.
        self.local_map.clear();
        let scope_id = self.ast.scope_of(node_ref);
        let mir_function = self.mir_builder.get_functions().get(&func_id).unwrap().clone();

        for (i, param_ref) in function_data.param_start.range(function_data.param_len).enumerate() {
            if let NodeKind::Param(param_data) = self.ast.get_kind(param_ref) {
                let local_id = mir_function.params[i];
                self.local_map.insert(param_data.symbol, local_id);
            }
        }

        self.lower_node_ref(function_data.body, scope_id);

        self.current_function = None;
        self.current_block = None;
    }

    fn lower_var_declaration(&mut self, scope_id: ScopeId, var_decl: &VarDeclData, _span: SourceSpan) {
        let mir_type_id = self.lower_qual_type(var_decl.ty);
        let (entry_ref, _) = self
            .symbol_table
            .lookup(var_decl.name, scope_id, Namespace::Ordinary)
            .unwrap();

        let is_global = self.current_function.is_none();

        if is_global {
            self.lower_global_var_declaration(scope_id, var_decl, entry_ref, mir_type_id);
        } else {
            self.lower_local_var_declaration(scope_id, var_decl, entry_ref, mir_type_id);
        }
    }

    fn lower_global_var_declaration(
        &mut self,
        scope_id: ScopeId,
        var_decl: &VarDeclData,
        entry_ref: SymbolRef,
        mir_type_id: TypeId,
    ) {
        let initial_value_id = var_decl
            .init
            .and_then(|init_ref| self.lower_initializer_to_const(scope_id, init_ref, var_decl.ty));

        let symbol = self.symbol_table.get_symbol(entry_ref);
        let final_init = initial_value_id.or_else(|| {
            if symbol.def_state == DefinitionState::Tentative {
                Some(self.create_constant(ConstValue::Zero))
            } else {
                None
            }
        });

        if let Some(global_id) = self.global_map.get(&entry_ref).copied() {
            if let Some(init_id) = final_init {
                self.mir_builder.set_global_initializer(global_id, init_id);
            }
        } else {
            let global_id = self
                .mir_builder
                .create_global_with_init(var_decl.name, mir_type_id, false, final_init);

            if let Some(alignment) = var_decl.alignment {
                self.mir_builder.set_global_alignment(global_id, alignment as u32);
            }

            self.global_map.insert(entry_ref, global_id);
        }
    }

    fn lower_local_var_declaration(
        &mut self,
        scope_id: ScopeId,
        var_decl: &VarDeclData,
        entry_ref: SymbolRef,
        mir_type_id: TypeId,
    ) {
        let local_id = self.mir_builder.create_local(Some(var_decl.name), mir_type_id, false);

        if let Some(alignment) = var_decl.alignment {
            self.mir_builder.set_local_alignment(local_id, alignment as u32);
        }

        self.local_map.insert(entry_ref, local_id);

        if let Some(initializer) = var_decl.init {
            let init_operand = self.lower_initializer(scope_id, initializer, var_decl.ty);
            self.emit_assignment(Place::Local(local_id), init_operand);
        }
    }

    fn lower_expression(&mut self, scope_id: ScopeId, expr_ref: NodeRef, need_value: bool) -> Operand {
        let ty = self.ast.get_resolved_type(expr_ref).unwrap_or_else(|| {
            let node_kind = self.ast.get_kind(expr_ref);
            let node_span = self.ast.get_span(expr_ref);
            panic!("Type not resolved for node {:?} at {:?}", node_kind, node_span);
        });
        let node_kind = self.ast.get_kind(expr_ref).clone();

        let mir_ty = self.lower_qual_type(ty);

        // Attempt constant folding for arithmetic/logical operations that are not simple literals
        if matches!(
            node_kind,
            NodeKind::BinaryOp(..) | NodeKind::UnaryOp(..) | NodeKind::TernaryOp(..)
        ) {
            let ctx = ConstEvalCtx {
                ast: self.ast,
                symbol_table: self.symbol_table,
            };
            if let Some(val) = eval_const_expr(&ctx, expr_ref) {
                return Operand::Constant(self.create_constant(ConstValue::Int(val)));
            }
        }

        match &node_kind {
            NodeKind::LiteralInt(_)
            | NodeKind::LiteralFloat(_)
            | NodeKind::LiteralChar(_)
            | NodeKind::LiteralString(_) => self.lower_literal(&node_kind, ty).expect("Failed to lower literal"),
            NodeKind::Ident(_, symbol_ref) => self.lower_ident(*symbol_ref),
            NodeKind::UnaryOp(op, operand_ref) => self.lower_unary_op_expr(scope_id, op, *operand_ref, mir_ty),
            NodeKind::PostIncrement(operand_ref) => self.lower_post_incdec(scope_id, *operand_ref, true, need_value),
            NodeKind::PostDecrement(operand_ref) => self.lower_post_incdec(scope_id, *operand_ref, false, need_value),
            NodeKind::BinaryOp(op, left_ref, right_ref) => {
                self.lower_binary_op_expr(scope_id, op, *left_ref, *right_ref, mir_ty)
            }
            NodeKind::Assignment(op, left_ref, right_ref) => {
                self.lower_assignment_expr(scope_id, expr_ref, op, *left_ref, *right_ref, mir_ty)
            }
            NodeKind::FunctionCall(call_expr) => self.lower_function_call(scope_id, call_expr, mir_ty),
            NodeKind::MemberAccess(obj_ref, field_name, is_arrow) => {
                self.lower_member_access(scope_id, *obj_ref, field_name, *is_arrow)
            }
            NodeKind::IndexAccess(arr_ref, idx_ref) => self.lower_index_access(scope_id, *arr_ref, *idx_ref),
            NodeKind::TernaryOp(cond, then, else_expr) => {
                self.lower_ternary_op(scope_id, *cond, *then, *else_expr, mir_ty)
            }
            NodeKind::SizeOfExpr(expr) => self.lower_sizeof_expr(*expr),
            NodeKind::SizeOfType(ty) => self.lower_sizeof_type(ty),
            NodeKind::AlignOf(ty) => self.lower_alignof_type(ty),
            NodeKind::GenericSelection(gs) => self.lower_generic_selection(scope_id, gs, need_value),
            NodeKind::GnuStatementExpression(_stmt, _) => {
                panic!("GnuStatementExpression not implemented");
            }
            NodeKind::Cast(_ty, operand_ref) => self.lower_cast(scope_id, *operand_ref, mir_ty),
            NodeKind::CompoundLiteral(ty, init_ref) => self.lower_compound_literal(scope_id, *ty, *init_ref),
            NodeKind::InitializerList(_) | NodeKind::InitializerItem(_) => {
                // Should be lowered in context of assignment usually.
                panic!("InitializerList or InitializerItem not implemented");
            }
            _ => unreachable!(),
        }
    }

    fn lower_ternary_op(
        &mut self,
        scope_id: ScopeId,
        cond: NodeRef,
        then_expr: NodeRef,
        else_expr: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        let cond_op = self.lower_expression(scope_id, cond, true);

        let then_block = self.mir_builder.create_block();
        let else_block = self.mir_builder.create_block();
        let exit_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(cond_op, then_block, else_block));

        // Result local
        let result_local = self.mir_builder.create_local(None, mir_ty, false);

        // Then
        self.mir_builder.set_current_block(then_block);
        let then_val = self.lower_expression(scope_id, then_expr, true);
        let then_val_conv = self.apply_conversions(then_val, then_expr, mir_ty);
        self.emit_assignment(Place::Local(result_local), then_val_conv);
        self.mir_builder.set_terminator(Terminator::Goto(exit_block));

        // Else
        self.mir_builder.set_current_block(else_block);
        let else_val = self.lower_expression(scope_id, else_expr, true);
        let else_val_conv = self.apply_conversions(else_val, else_expr, mir_ty);
        self.emit_assignment(Place::Local(result_local), else_val_conv);
        self.mir_builder.set_terminator(Terminator::Goto(exit_block));

        self.mir_builder.set_current_block(exit_block);

        Operand::Copy(Box::new(Place::Local(result_local)))
    }

    fn lower_sizeof_expr(&mut self, expr: NodeRef) -> Operand {
        let operand_ty = self
            .ast
            .get_resolved_type(expr)
            .expect("SizeOf operand type missing")
            .ty();
        self.lower_type_query(operand_ty, true)
    }

    fn lower_sizeof_type(&mut self, ty: &QualType) -> Operand {
        self.lower_type_query(ty.ty(), true)
    }

    fn lower_alignof_type(&mut self, ty: &QualType) -> Operand {
        self.lower_type_query(ty.ty(), false)
    }

    fn lower_type_query(&mut self, ty: TypeRef, is_size: bool) -> Operand {
        let layout = self.registry.get_layout(ty);
        let val = if is_size { layout.size } else { layout.alignment };
        self.create_int_operand(val as i64)
    }

    fn lower_generic_selection(
        &mut self,
        scope_id: ScopeId,
        gs: &nodes::GenericSelectionData,
        need_value: bool,
    ) -> Operand {
        let ctrl_ty = self
            .ast
            .get_resolved_type(gs.control)
            .expect("Controlling expr type missing")
            .ty();
        let unqualified_ctrl = self.registry.strip_all(QualType::unqualified(ctrl_ty));

        let mut selected_expr = None;
        let mut default_expr = None;

        for assoc_node_ref in gs.assoc_start.range(gs.assoc_len) {
            if let NodeKind::GenericAssociation(ga) = self.ast.get_kind(assoc_node_ref) {
                if let Some(ty) = ga.ty {
                    if self.registry.is_compatible(unqualified_ctrl, ty) {
                        selected_expr = Some(ga.result_expr);
                        break;
                    }
                } else {
                    default_expr = Some(ga.result_expr);
                }
            }
        }

        let expr_to_lower = selected_expr
            .or(default_expr)
            .expect("Generic selection failed (should be caught by Analyzer)");
        self.lower_expression(scope_id, expr_to_lower, need_value)
    }

    fn lower_cast(&mut self, scope_id: ScopeId, operand_ref: NodeRef, mir_ty: TypeId) -> Operand {
        let operand = self.lower_expression(scope_id, operand_ref, true);
        Operand::Cast(mir_ty, Box::new(operand))
    }

    fn lower_literal(&mut self, node_kind: &NodeKind, ty: QualType) -> Option<Operand> {
        match node_kind {
            NodeKind::LiteralInt(val) => Some(self.create_int_operand(*val)),
            NodeKind::LiteralFloat(val) => Some(self.create_float_operand(*val)),
            NodeKind::LiteralChar(val) => Some(self.create_int_operand(*val as i64)),
            NodeKind::LiteralString(val) => Some(self.lower_literal_string(val, ty)),
            _ => None,
        }
    }

    fn lower_compound_literal(&mut self, scope_id: ScopeId, ty: QualType, init_ref: NodeRef) -> Operand {
        let mir_ty = self.lower_qual_type(ty);

        // Check if we are at global scope
        if self.current_function.is_none() {
            // Global compound literal
            let global_name = self.mir_builder.get_next_anonymous_global_name();

            // Lower initializer (must be constant)
            let init_const_id = self
                .lower_initializer_to_const(scope_id, init_ref, ty)
                .expect("Global compound literal initializer must be constant");

            let global_id = self.mir_builder.create_global_with_init(
                global_name,
                mir_ty,
                false, // not constant (it's an lvalue)
                Some(init_const_id),
            );

            Operand::Copy(Box::new(Place::Global(global_id)))
        } else {
            // Local compound literal
            let (_, place) = self.create_temp_local(mir_ty);

            // Lower initializer
            let init_operand = self.lower_initializer(scope_id, init_ref, ty);
            self.emit_assignment(place.clone(), init_operand);

            Operand::Copy(Box::new(place))
        }
    }

    fn create_string_array_const(&mut self, val: &NameId, fixed_size: Option<usize>) -> ConstValueId {
        let string_content = val.as_str();
        let bytes = string_content.as_bytes();
        let size = fixed_size.unwrap_or(bytes.len() + 1);

        let char_constants = (0..size)
            .map(|i| {
                let byte_val = if i < bytes.len() { bytes[i] } else { 0 };
                let char_const = ConstValue::Int(byte_val as i64);
                self.create_constant(char_const)
            })
            .collect();

        let array_const = ConstValue::ArrayLiteral(char_constants);
        self.create_constant(array_const)
    }

    fn lower_literal_string(&mut self, val: &NameId, ty: QualType) -> Operand {
        let string_type = self.lower_qual_type(ty);

        let array_const_id = self.create_string_array_const(val, None);

        let global_name = self.mir_builder.get_next_anonymous_global_name();
        let global_id = self
            .mir_builder
            .create_global_with_init(global_name, string_type, true, Some(array_const_id));

        let addr_const_val = ConstValue::GlobalAddress(global_id);
        Operand::Constant(self.create_constant(addr_const_val))
    }

    fn lower_unary_op_expr(
        &mut self,
        scope_id: ScopeId,
        op: &UnaryOp,
        operand_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        match op {
            UnaryOp::PreIncrement | UnaryOp::PreDecrement => self.lower_pre_incdec(scope_id, op, operand_ref),
            UnaryOp::AddrOf => self.lower_unary_addrof(scope_id, operand_ref),
            UnaryOp::Deref => self.lower_unary_deref(scope_id, operand_ref),
            UnaryOp::Plus => self.lower_expression(scope_id, operand_ref, true),
            _ => {
                let operand = self.lower_expression(scope_id, operand_ref, true);
                let operand_ty = self.get_operand_type(&operand);
                let mir_type_info = self.mir_builder.get_type(operand_ty);

                let rval = self.emit_unary_rvalue(op, operand, mir_type_info.is_float());
                self.emit_rvalue_to_operand(rval, mir_ty)
            }
        }
    }

    fn lower_unary_addrof(&mut self, scope_id: ScopeId, operand_ref: NodeRef) -> Operand {
        let operand = self.lower_expression(scope_id, operand_ref, true);
        if let Operand::Copy(place) = operand {
            Operand::AddressOf(place)
        } else if let Operand::Constant(const_id) = operand
            && self.ast.get_value_category(operand_ref) == Some(ValueCategory::LValue)
            && matches!(
                self.mir_builder.get_constants().get(&const_id),
                Some(ConstValue::FunctionAddress(_))
            )
        {
            Operand::Constant(const_id)
        } else {
            panic!("Cannot take address of a non-lvalue");
        }
    }

    fn lower_unary_deref(&mut self, scope_id: ScopeId, operand_ref: NodeRef) -> Operand {
        let operand = self.lower_expression(scope_id, operand_ref, true);
        let operand_ty = self.ast.get_resolved_type(operand_ref).unwrap();
        let target_mir_ty = self.lower_qual_type(operand_ty);
        let operand_converted = self.apply_conversions(operand, operand_ref, target_mir_ty);

        let place = Place::Deref(Box::new(operand_converted));
        Operand::Copy(Box::new(place))
    }

    fn lower_ident(&mut self, resolved_ref: SymbolRef) -> Operand {
        let entry = self.symbol_table.get_symbol(resolved_ref);

        match &entry.kind {
            SymbolKind::Variable { is_global, .. } => {
                if *is_global {
                    // Global variables should have been lowered already if we are visiting in order.
                    // However, if we are in an initializer of a global variable that refers to itself (or forward ref),
                    // or if there is a bug in ordering, this might fail.
                    // For now, let's assume valid C code where globals are defined before use (or tentatively defined).
                    let global_id = match self.global_map.get(&resolved_ref) {
                        Some(id) => id,
                        None => {
                            // Fallback: If not yet in map, it might be a forward reference or we missed it.
                            // But in this specific crash case, 's' is defined before 'anon'.
                            // Let's print debug info to diagnose.
                            panic!(
                                "Global variable '{}' not found in MIR map. Visited? {:?}",
                                entry.name,
                                self.global_map.keys()
                            );
                        }
                    };
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
            SymbolKind::EnumConstant { value } => Operand::Constant(self.create_constant(ConstValue::Int(*value))),
            _ => panic!("Unexpected symbol kind"),
        }
    }

    fn unify_binary_operands(
        &mut self,
        mut lhs: Operand,
        mut rhs: Operand,
        lhs_mir_ty: TypeId,
        rhs_mir_ty: TypeId,
    ) -> (Operand, Operand) {
        if lhs_mir_ty != rhs_mir_ty {
            // Unify to the larger type or just handle common cases.
            // For now, if one is i64 and other is i32, promote i32 to i64.
            let lhs_mir = self.mir_builder.get_type(lhs_mir_ty);
            let rhs_mir = self.mir_builder.get_type(rhs_mir_ty);

            if lhs_mir.is_int() && rhs_mir.is_int() {
                let w1 = lhs_mir.width();
                let w2 = rhs_mir.width();
                if w1 > w2 {
                    rhs = Operand::Cast(lhs_mir_ty, Box::new(rhs));
                } else if w2 > w1 {
                    lhs = Operand::Cast(rhs_mir_ty, Box::new(lhs));
                }
            } else if lhs_mir.is_pointer() && rhs_mir.is_int() {
                rhs = Operand::Cast(lhs_mir_ty, Box::new(rhs));
            } else if lhs_mir.is_int() && rhs_mir.is_pointer() {
                lhs = Operand::Cast(rhs_mir_ty, Box::new(lhs));
            }
        }
        (lhs, rhs)
    }

    fn lower_binary_op_expr(
        &mut self,
        scope_id: ScopeId,
        op: &BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        debug_assert!(
            !op.is_assignment(),
            "lower_binary_op_expr called with assignment operator: {:?}",
            op
        );
        if matches!(op, BinaryOp::LogicAnd | BinaryOp::LogicOr) {
            return self.lower_logical_op(scope_id, op, left_ref, right_ref, mir_ty);
        }

        let lhs = self.lower_expression(scope_id, left_ref, true);
        let rhs = self.lower_expression(scope_id, right_ref, true);

        // Handle pointer arithmetic

        if let Some(rval) = self.lower_pointer_arithmetic(op, lhs.clone(), rhs.clone(), left_ref, right_ref) {
            return self.emit_rvalue_to_operand(rval, mir_ty);
        }

        // Apply implicit conversions from semantic info first to match AST
        let lhs_converted = self.apply_conversions(lhs, left_ref, mir_ty);
        let rhs_converted = self.apply_conversions(rhs, right_ref, mir_ty);

        // Ensure both operands have the same type for MIR operations.
        // Some operations like comparisons have mir_ty as i32 (the result),
        // but operands might be i64. We should use a common type.
        let lhs_mir_ty = self.get_operand_type(&lhs_converted);
        let rhs_mir_ty = self.get_operand_type(&rhs_converted);

        let (lhs_converted, rhs_converted) =
            self.unify_binary_operands(lhs_converted, rhs_converted, lhs_mir_ty, rhs_mir_ty);

        let lhs_final = self.ensure_explicit_cast(lhs_converted, left_ref);
        let rhs_final = self.ensure_explicit_cast(rhs_converted, right_ref);

        // Check types for correct MIR op
        let lhs_mir = self.mir_builder.get_type(lhs_mir_ty);

        if matches!(op, BinaryOp::Comma) {
            // Comma operator: LHS evaluated (lhs_final), result discarded. Result is RHS.
            return rhs_final;
        }

        let rval = self.emit_binary_rvalue(op, lhs_final, rhs_final, lhs_mir.is_float());
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    /// Helper to ensure constants are explicitly cast if they are not the default i32
    fn ensure_explicit_cast(&mut self, operand: Operand, node_ref: NodeRef) -> Operand {
        match operand {
            Operand::Constant(_) => {
                if let Some(ty) = self.ast.get_resolved_type(node_ref) {
                    let mir_type_id = self.lower_qual_type(ty);
                    Operand::Cast(mir_type_id, Box::new(operand))
                } else {
                    operand
                }
            }
            _ => operand,
        }
    }

    fn lower_logical_op(
        &mut self,
        scope_id: ScopeId,
        op: &BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        // Short-circuiting logic for && and ||
        // result = lhs ? (op == LogicOr ? 1 : rhs) : (op == LogicOr ? rhs : 0)

        // Create temporary for result
        let (_res_local, res_place) = self.create_temp_local(mir_ty);

        let eval_rhs_block = self.mir_builder.create_block();
        let merge_block = self.mir_builder.create_block();
        let short_circuit_block = self.mir_builder.create_block();

        // 1. Evaluate LHS
        let lhs_op = self.lower_condition(scope_id, left_ref);

        // Pre-create constants to avoid double borrow
        let zero_const = self.create_constant(ConstValue::Int(0));
        let one_const = self.create_constant(ConstValue::Int(1));

        let (short_circuit_val, true_target, false_target) = match op {
            BinaryOp::LogicAnd => (zero_const, eval_rhs_block, short_circuit_block),
            BinaryOp::LogicOr => (one_const, short_circuit_block, eval_rhs_block),
            _ => unreachable!(),
        };

        // if lhs { goto true_target } else { goto false_target }
        self.mir_builder
            .set_terminator(Terminator::If(lhs_op, true_target, false_target));

        // Short circuit case
        self.mir_builder.set_current_block(short_circuit_block);
        self.mir_builder.add_statement(MirStmt::Assign(
            res_place.clone(),
            Rvalue::Use(Operand::Constant(short_circuit_val)),
        ));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        // 2. Evaluate RHS
        self.mir_builder.set_current_block(eval_rhs_block);
        let rhs_val = self.lower_condition(scope_id, right_ref);

        // Convert boolean condition result to 0 or 1 integer
        // If rhs_val is true -> 1, else -> 0
        let rhs_true_block = self.mir_builder.create_block();
        let rhs_false_block = self.mir_builder.create_block();

        self.mir_builder
            .set_terminator(Terminator::If(rhs_val, rhs_true_block, rhs_false_block));

        self.mir_builder.set_current_block(rhs_true_block);
        self.mir_builder.add_statement(MirStmt::Assign(
            res_place.clone(),
            Rvalue::Use(Operand::Constant(one_const)),
        ));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        self.mir_builder.set_current_block(rhs_false_block);
        self.mir_builder.add_statement(MirStmt::Assign(
            res_place.clone(),
            Rvalue::Use(Operand::Constant(zero_const)),
        ));
        self.mir_builder.set_terminator(Terminator::Goto(merge_block));

        // Merge
        self.mir_builder.set_current_block(merge_block);
        self.current_block = Some(merge_block);

        Operand::Copy(Box::new(res_place))
    }

    fn lower_pointer_arithmetic(
        &mut self,
        op: &BinaryOp,
        lhs: Operand,
        rhs: Operand,
        left_ref: NodeRef,
        right_ref: NodeRef,
    ) -> Option<Rvalue> {
        let lhs_type = self.ast.get_resolved_type(left_ref).unwrap();
        let rhs_type = self.ast.get_resolved_type(right_ref).unwrap();

        match op {
            BinaryOp::Add => {
                if lhs_type.is_pointer() {
                    let rhs_mir_ty = self.lower_qual_type(rhs_type);
                    let rhs_converted = self.apply_conversions(rhs, right_ref, rhs_mir_ty);
                    Some(Rvalue::PtrAdd(lhs, rhs_converted))
                } else if rhs_type.is_pointer() {
                    let lhs_mir_ty = self.lower_qual_type(lhs_type);
                    let lhs_converted = self.apply_conversions(lhs, left_ref, lhs_mir_ty);
                    Some(Rvalue::PtrAdd(rhs, lhs_converted))
                } else {
                    None
                }
            }
            BinaryOp::Sub => {
                if lhs_type.is_pointer() {
                    if rhs_type.is_pointer() {
                        Some(Rvalue::PtrDiff(lhs, rhs))
                    } else if rhs_type.is_integer() {
                        let rhs_mir_ty = self.lower_qual_type(rhs_type);
                        let rhs_converted = self.apply_conversions(rhs, right_ref, rhs_mir_ty);
                        Some(Rvalue::PtrSub(lhs, rhs_converted))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn lower_assignment_expr(
        &mut self,
        scope_id: ScopeId,
        node_ref: NodeRef,
        op: &BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        mir_ty: TypeId,
    ) -> Operand {
        debug_assert!(
            op.is_assignment(),
            "lower_assignment_expr called with non-assignment operator: {:?}",
            op
        );
        let lhs_op = self.lower_expression(scope_id, left_ref, true);

        // Ensure the LHS is a place. If not, this is a semantic error.
        if self.ast.get_value_category(left_ref) != Some(ValueCategory::LValue) {
            panic!("LHS of assignment must be an lvalue");
        }

        let place = if let Operand::Copy(place) = lhs_op {
            *place
        } else {
            panic!("LHS of assignment lowered to non-place operand despite being LValue");
        };

        let rhs_op = self.lower_expression(scope_id, right_ref, true);

        let final_rhs = if let Some(compound_op) = op.without_assignment() {
            // This is a compound assignment, e.g., a += b
            // Use the already-evaluated place to read the current value.
            let lhs_copy = Operand::Copy(Box::new(place.clone()));

            if let Some(rval) =
                self.lower_pointer_arithmetic(&compound_op, lhs_copy.clone(), rhs_op.clone(), left_ref, right_ref)
            {
                self.emit_rvalue_to_operand(rval, mir_ty)
            } else {
                let lhs_converted_for_op = self.apply_conversions(lhs_copy, left_ref, mir_ty);
                let rhs_converted_for_op = self.apply_conversions(rhs_op, right_ref, mir_ty);

                let lhs_ty_for_op = self.get_operand_type(&lhs_converted_for_op);
                let mir_type_info = self.mir_builder.get_type(lhs_ty_for_op);

                let rval = self.emit_binary_rvalue(
                    &compound_op,
                    lhs_converted_for_op,
                    rhs_converted_for_op,
                    mir_type_info.is_float(),
                );
                let result_of_op = self.emit_rvalue_to_operand(rval, lhs_ty_for_op);
                self.apply_conversions(result_of_op, node_ref, mir_ty)
            }
        } else {
            // Simple assignment, just use the RHS
            self.apply_conversions(rhs_op, right_ref, mir_ty)
        };

        self.emit_assignment(place, final_rhs.clone());
        final_rhs // C assignment expressions evaluate to the assigned value
    }

    fn lower_function_call(&mut self, scope_id: ScopeId, call_expr: &nodes::CallExpr, mir_ty: TypeId) -> Operand {
        let callee = self.lower_expression(scope_id, call_expr.callee, true);

        let mut arg_operands = Vec::new();

        // Get the function type to determine parameter types for conversions
        let func_node_kind = self.ast.get_kind(call_expr.callee);
        let func_type = if let NodeKind::Ident(_, symbol_ref) = func_node_kind {
            let resolved_symbol = *symbol_ref;
            let func_entry = self.symbol_table.get_symbol(resolved_symbol);
            Some(self.registry.get(func_entry.type_info.ty()))
        } else {
            None
        };

        let param_types = if let Some(func_type) = func_type {
            if let TypeKind::Function { parameters, .. } = &func_type.kind {
                Some(
                    parameters
                        .iter()
                        .map(|param| self.lower_qual_type(param.param_type))
                        .collect::<Vec<_>>(),
                )
            } else {
                None
            }
        } else {
            None
        };

        for (i, arg_ref) in call_expr.arg_start.range(call_expr.arg_len).enumerate() {
            // Note: lower_expression(CallArg) will just lower the inner expression.
            // But we use arg_ref (the CallArg node) for implicit conversion lookup.
            let arg_operand = self.lower_expression(scope_id, arg_ref, true);

            // Apply conversions for function arguments if needed
            // The resolved type of CallArg is same as inner expr.
            let arg_ty = self.ast.get_resolved_type(arg_ref).unwrap();
            let arg_mir_ty = self.lower_qual_type(arg_ty);

            // Use the parameter type as the target type for conversions, if available
            let target_mir_ty = if let Some(ref param_types_vec) = param_types {
                if i < param_types_vec.len() {
                    param_types_vec[i]
                } else {
                    // Variadic argument: Logic handled by implicit conversions (Promotion/Decay) calculated in analyzer.rs
                    // We just need a placeholder type, or the promoted type if we could calculate it.
                    // Since semantic analysis has inserted promoted type casts/conversions, we can start with the argument's own type.
                    arg_mir_ty
                }
            } else {
                // Unprototyped function: Logic handled by implicit conversions
                arg_mir_ty
            };

            let converted_arg = self.apply_conversions(arg_operand, arg_ref, target_mir_ty);

            arg_operands.push(converted_arg);
        }

        let call_target = if let Operand::Constant(const_id) = callee {
            if let ConstValue::FunctionAddress(func_id) = self.mir_builder.get_constants().get(&const_id).unwrap() {
                CallTarget::Direct(*func_id)
            } else {
                panic!("Expected function address");
            }
        } else {
            CallTarget::Indirect(callee)
        };

        // Check if this is a void function call - if so, we use MirStmt::Call
        // Otherwise, we use Rvalue::Call and create a temporary local
        let is_void = matches!(self.mir_builder.get_type(mir_ty), MirType::Void);
        if is_void {
            // Void function call - use MirStmt::Call for side effects only
            let stmt = MirStmt::Call(call_target, arg_operands);
            self.mir_builder.add_statement(stmt);
            // Return a dummy operand for void functions
            return Operand::Constant(self.create_constant(ConstValue::Int(0)));
        }

        // Non-void function call - use Rvalue::Call and store result
        let rval = Rvalue::Call(call_target, arg_operands);
        self.emit_rvalue_to_operand(rval, mir_ty)
    }

    fn find_member_path(&self, record_ty: TypeRef, field_name: NameId) -> Option<Vec<usize>> {
        let ty = self.registry.get(record_ty);
        if let TypeKind::Record { members, .. } = &ty.kind {
            // 1. Check direct members
            if let Some(idx) = members.iter().position(|m| m.name == Some(field_name)) {
                return Some(vec![idx]);
            }

            // 2. Check anonymous members
            for (idx, member) in members.iter().enumerate() {
                if member.name.is_none() {
                    let member_ty = member.member_type.ty();
                    // Only recurse if it's a record
                    if matches!(self.registry.get(member_ty).kind, TypeKind::Record { .. })
                        && let Some(mut sub_path) = self.find_member_path(member_ty, field_name)
                    {
                        let mut full_path = vec![idx];
                        full_path.append(&mut sub_path);
                        return Some(full_path);
                    }
                }
            }
        }
        None
    }

    fn lower_member_access(
        &mut self,
        scope_id: ScopeId,
        obj_ref: NodeRef,
        field_name: &NameId,
        is_arrow: bool,
    ) -> Operand {
        let obj_operand = self.lower_expression(scope_id, obj_ref, true);
        let obj_ty = self.ast.get_resolved_type(obj_ref).unwrap();
        let record_ty = if is_arrow {
            self.registry
                .get_pointee(obj_ty.ty())
                .expect("Arrow access on non-pointer type")
                .ty()
        } else {
            obj_ty.ty()
        };

        if record_ty.is_record() {
            // Validate that the field exists and get its layout information
            let path = self
                .find_member_path(record_ty, *field_name)
                .expect("Field not found - should be caught by semantic analysis");

            // Apply the chain of field accesses

            // Resolve base place
            let mir_type = self.lower_qual_type(obj_ty);
            let mut current_place = self.ensure_place(obj_operand, mir_type);

            if is_arrow {
                // Dereference: *ptr
                let deref_op = Operand::Copy(Box::new(current_place));
                current_place = Place::Deref(Box::new(deref_op));
            }

            for field_idx in path {
                current_place = Place::StructField(Box::new(current_place), field_idx);
            }

            Operand::Copy(Box::new(current_place))
        } else {
            panic!("Member access on non-record type");
        }
    }

    fn lower_index_access(&mut self, scope_id: ScopeId, arr_ref: NodeRef, idx_ref: NodeRef) -> Operand {
        let arr_operand = self.lower_expression(scope_id, arr_ref, true);
        let idx_operand = self.lower_expression(scope_id, idx_ref, true);
        let arr_ty = self.ast.get_resolved_type(arr_ref).unwrap();

        // Handle both array and pointer types for index access
        // In C, arr[idx] is equivalent to *(arr + idx)
        if arr_ty.is_array() {
            // Array indexing - use ArrayIndex place
            // We can skip the explicit layout check as we trust the type system
            let mir_type = self.lower_qual_type(arr_ty);
            let arr_place = self.ensure_place(arr_operand, mir_type);

            Operand::Copy(Box::new(Place::ArrayIndex(Box::new(arr_place), Box::new(idx_operand))))
        } else if arr_ty.is_pointer() {
            // For pointer indexing, we can use the ArrayIndex place directly
            // since pointer indexing follows the same rules as array indexing
            // p[idx] is equivalent to *(p + idx) which is what ArrayIndex does

            // Create an ArrayIndex place with the pointer as base and index
            let mir_type = self.lower_qual_type(arr_ty);
            let pointer_place = self.ensure_place(arr_operand, mir_type);

            Operand::Copy(Box::new(Place::ArrayIndex(
                Box::new(pointer_place),
                Box::new(idx_operand),
            )))
        } else {
            panic!("Index access on non-array, non-pointer type");
        }
    }

    fn lower_return_statement(&mut self, scope_id: ScopeId, expr: &Option<NodeRef>) {
        let operand = expr.map(|expr_ref| {
            let expr_operand = self.lower_expression(scope_id, expr_ref, true);
            // Apply conversions for return value if needed
            if let Some(func_id) = self.current_function {
                let func = self.mir_builder.get_functions().get(&func_id).unwrap();
                let return_mir_ty = func.return_type;
                self.apply_conversions(expr_operand, expr_ref, return_mir_ty)
            } else {
                expr_operand
            }
        });
        self.mir_builder.set_terminator(Terminator::Return(operand));
    }

    fn lower_if_statement(&mut self, scope_id: ScopeId, if_stmt: &IfStmt) {
        let then_block = self.mir_builder.create_block();
        let else_block = self.mir_builder.create_block();
        let merge_block = self.mir_builder.create_block();

        let cond_converted = self.lower_condition(scope_id, if_stmt.condition);
        self.mir_builder
            .set_terminator(Terminator::If(cond_converted, then_block, else_block));

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

    fn lower_loop_generic<I, C, B, Inc>(
        &mut self,
        init_fn: Option<I>,
        cond_fn: Option<C>,
        body_fn: B,
        inc_fn: Option<Inc>,
        is_do_while: bool,
    ) where
        I: FnOnce(&mut Self),
        C: FnOnce(&mut Self) -> Operand,
        B: FnOnce(&mut Self),
        Inc: FnOnce(&mut Self),
    {
        let cond_block = self.mir_builder.create_block();
        let body_block = self.mir_builder.create_block();
        let increment_block = if inc_fn.is_some() {
            self.mir_builder.create_block()
        } else {
            // If there's no increment block (e.g. while/do-while), "continue" goes to condition
            cond_block
        };
        let exit_block = self.mir_builder.create_block();

        // Continue target depends on whether we have an increment step
        let continue_target = increment_block;

        self.with_loop_targets(exit_block, continue_target, |this| {
            if let Some(init) = init_fn {
                init(this);
            }

            if is_do_while {
                // do-while: jump straight to body
                this.mir_builder.set_terminator(Terminator::Goto(body_block));
            } else {
                // for/while: jump to condition
                this.mir_builder.set_terminator(Terminator::Goto(cond_block));
            }

            // Condition block
            this.mir_builder.set_current_block(cond_block);
            if let Some(cond) = cond_fn {
                let cond_val = cond(this);
                this.mir_builder
                    .set_terminator(Terminator::If(cond_val, body_block, exit_block));
            } else {
                // No condition (e.g. for(;;)) -> infinite loop
                this.mir_builder.set_terminator(Terminator::Goto(body_block));
            }

            // Body block
            this.mir_builder.set_current_block(body_block);
            body_fn(this);

            // After body, jump to increment (or condition if no increment)
            if !this.mir_builder.current_block_has_terminator() {
                this.mir_builder.set_terminator(Terminator::Goto(increment_block));
            }

            // Increment block (only if it exists and is distinct from cond_block)
            if let Some(inc) = inc_fn {
                this.mir_builder.set_current_block(increment_block);
                inc(this);
                this.mir_builder.set_terminator(Terminator::Goto(cond_block));
            }
        });

        self.mir_builder.set_current_block(exit_block);
        self.current_block = Some(exit_block);
    }

    fn lower_while_statement(&mut self, scope_id: ScopeId, while_stmt: &WhileStmt) {
        self.lower_loop_generic(
            None::<fn(&mut Self)>,
            Some(|this: &mut Self| this.lower_condition(scope_id, while_stmt.condition)),
            |this| this.lower_node_ref(while_stmt.body, scope_id),
            None::<fn(&mut Self)>,
            false,
        );
    }

    fn lower_do_while_statement(&mut self, scope_id: ScopeId, body: NodeRef, condition: NodeRef) {
        self.lower_loop_generic(
            None::<fn(&mut Self)>,
            Some(|this: &mut Self| this.lower_condition(scope_id, condition)),
            |this| this.lower_node_ref(body, scope_id),
            None::<fn(&mut Self)>,
            true,
        );
    }

    fn lower_for_statement(&mut self, scope_id: ScopeId, for_stmt: &ForStmt) {
        let init_fn = for_stmt
            .init
            .map(|init| move |this: &mut Self| this.lower_node_ref(init, scope_id));

        let cond_fn = for_stmt
            .condition
            .map(|cond| move |this: &mut Self| this.lower_condition(scope_id, cond));

        let inc_fn = for_stmt.increment.map(|inc| {
            move |this: &mut Self| {
                this.lower_expression(scope_id, inc, false);
            }
        });

        self.lower_loop_generic(
            init_fn,
            cond_fn,
            |this| this.lower_node_ref(for_stmt.body, scope_id),
            inc_fn,
            false,
        );
    }

    fn emit_assignment(&mut self, place: Place, operand: Operand) {
        if self.mir_builder.current_block_has_terminator() {
            return;
        }
        let rvalue = Rvalue::Use(operand);
        let stmt = MirStmt::Assign(place, rvalue);
        self.mir_builder.add_statement(stmt);
    }

    fn lower_qual_type(&mut self, ty: QualType) -> TypeId {
        self.lower_type(ty.ty())
    }

    fn lower_type(&mut self, type_ref: TypeRef) -> TypeId {
        if let Some(type_id) = self.type_cache.get(&type_ref) {
            return *type_id;
        }

        // If this type is already being converted, return the placeholder we've inserted earlier
        if self.type_conversion_in_progress.contains(&type_ref) {
            return *self
                .type_cache
                .get(&type_ref)
                .expect("Placeholder must exist for recursive type");
        }

        // Begin conversion: reserve a placeholder TypeId so recursive references can point to it.
        self.type_conversion_in_progress.insert(type_ref);
        let placeholder_name = NameId::new(format!("__recursive_placeholder_{}", type_ref.get()));
        let placeholder_type = MirType::Record {
            name: placeholder_name,
            field_types: Vec::new(),
            field_names: Vec::new(),
            is_union: false,
            layout: MirRecordLayout {
                size: 0,
                alignment: 0,
                field_offsets: Vec::new(),
            },
        };
        let placeholder_id = self.mir_builder.add_type(placeholder_type);
        self.type_cache.insert(type_ref, placeholder_id);

        let ast_type = self.registry.get(type_ref).clone();
        let ast_type_kind = ast_type.kind.clone();

        let mir_type = match &ast_type_kind {
            TypeKind::Builtin(b) => self.lower_builtin_type(b),
            TypeKind::Pointer { pointee } => self.lower_pointer_type(*pointee),
            TypeKind::Array { element_type, size } => self.lower_array_type(type_ref, *element_type, size),
            TypeKind::Function {
                return_type,
                parameters,
                ..
            } => self.lower_function_type(return_type, parameters),
            TypeKind::Record {
                tag,
                members,
                is_union,
                is_complete,
            } => self.lower_record_type(type_ref, tag, members, *is_union, *is_complete),
            _ => MirType::I32,
        };

        // Remove from in-progress set
        self.type_conversion_in_progress.remove(&type_ref);

        // Replace the placeholder entry with the real type
        self.mir_builder.update_type(placeholder_id, mir_type.clone());
        self.type_cache.insert(type_ref, placeholder_id);
        placeholder_id
    }

    fn lower_builtin_type(&self, b: &BuiltinType) -> MirType {
        match b {
            BuiltinType::Void => MirType::Void,
            BuiltinType::Bool => MirType::Bool,
            BuiltinType::Char | BuiltinType::SChar => MirType::I8,
            BuiltinType::UChar => MirType::U8,
            BuiltinType::Short => MirType::I16,
            BuiltinType::UShort => MirType::U16,
            BuiltinType::Int => MirType::I32,
            BuiltinType::UInt => MirType::U32,
            BuiltinType::Long | BuiltinType::LongLong => MirType::I64,
            BuiltinType::ULong | BuiltinType::ULongLong => MirType::U64,
            BuiltinType::Float => MirType::F32,
            BuiltinType::Double | BuiltinType::LongDouble => MirType::F64,
            BuiltinType::Signed => MirType::I32,
        }
    }

    fn lower_pointer_type(&mut self, pointee: QualType) -> MirType {
        MirType::Pointer {
            pointee: self.lower_type(pointee.ty()),
        }
    }

    fn lower_array_type(&mut self, type_ref: TypeRef, element_type: TypeRef, size: &ArraySizeType) -> MirType {
        let element = self.lower_type(element_type);
        let size = if let ArraySizeType::Constant(s) = size { *s } else { 0 };

        let (layout_size, layout_align, element_ref, _) = self.registry.get_array_layout(type_ref);
        let element_layout = self.registry.get_layout(element_ref);

        MirType::Array {
            element,
            size,
            layout: MirArrayLayout {
                size: layout_size,
                align: layout_align,
                stride: element_layout.size,
            },
        }
    }

    fn lower_function_type(
        &mut self,
        return_type: &TypeRef,
        parameters: &[crate::semantic::FunctionParameter],
    ) -> MirType {
        let return_type = self.lower_type(*return_type);
        let mut params = Vec::new();
        for p in parameters {
            params.push(self.lower_qual_type(p.param_type));
        }
        MirType::Function { return_type, params }
    }

    fn lower_record_type(
        &mut self,
        type_ref: TypeRef,
        tag: &Option<NameId>,
        members: &[StructMember],
        is_union: bool,
        is_complete: bool,
    ) -> MirType {
        let name = tag.unwrap_or_else(|| NameId::new("anonymous"));

        let (size, alignment, field_offsets, field_names, field_types) = if is_complete {
            let (size, alignment, field_layouts, _) = self.registry.get_record_layout(type_ref);
            let field_offsets = field_layouts.iter().map(|f| f.offset).collect();

            let mut field_names = Vec::new();
            let mut field_types = Vec::new();

            for (idx, m) in members.iter().enumerate() {
                let name = m.name.unwrap_or_else(|| NameId::new(format!("__anon_{}", idx)));
                field_names.push(name);
                field_types.push(self.lower_qual_type(m.member_type));
            }
            (size, alignment, field_offsets, field_names, field_types)
        } else {
            (0, 1, Vec::new(), Vec::new(), Vec::new())
        };

        MirType::Record {
            name,
            field_types,
            field_names,
            is_union,
            layout: MirRecordLayout {
                size,
                alignment,
                field_offsets,
            },
        }
    }

    fn create_constant(&mut self, value: ConstValue) -> ConstValueId {
        self.mir_builder.create_constant(value)
    }

    fn create_int_operand(&mut self, val: i64) -> Operand {
        Operand::Constant(self.create_constant(ConstValue::Int(val)))
    }

    fn create_float_operand(&mut self, val: f64) -> Operand {
        Operand::Constant(self.create_constant(ConstValue::Float(val)))
    }

    fn emit_conversion(&mut self, operand: Operand, conv: &ImplicitConversion, target_type_id: TypeId) -> Operand {
        let to_mir_type = match conv {
            ImplicitConversion::IntegerCast { to, .. }
            | ImplicitConversion::IntegerPromotion { to, .. }
            | ImplicitConversion::PointerCast { to, .. } => self.lower_type(*to),
            ImplicitConversion::NullPointerConstant => {
                // Null pointer constant usually converts to void* first.
                // However, we can use target_type_id if it's already a pointer.
                let void_ptr_mir = self.lower_type(self.registry.type_void_ptr);
                if self.mir_builder.get_type(target_type_id).is_pointer() {
                    target_type_id
                } else {
                    void_ptr_mir
                }
            }
            ImplicitConversion::PointerDecay { to } => self.lower_type(*to),
            ImplicitConversion::LValueToRValue => target_type_id,
            ImplicitConversion::QualifierAdjust { .. } => target_type_id,
        };

        // Optimization: skip if already same type
        let current_ty = self.get_operand_type(&operand);
        if current_ty == to_mir_type && !matches!(conv, ImplicitConversion::PointerDecay { .. }) {
            return operand;
        }

        match conv {
            ImplicitConversion::IntegerCast { .. }
            | ImplicitConversion::IntegerPromotion { .. }
            | ImplicitConversion::PointerCast { .. } => Operand::Cast(to_mir_type, Box::new(operand)),
            ImplicitConversion::NullPointerConstant => Operand::Cast(
                to_mir_type,
                Box::new(Operand::Constant(self.create_constant(ConstValue::Int(0)))),
            ),
            ImplicitConversion::PointerDecay { .. } => {
                if let Operand::Copy(place) = &operand {
                    let addr_of_array = Operand::AddressOf(place.clone());
                    Operand::Cast(to_mir_type, Box::new(addr_of_array))
                } else {
                    // If it's not a place (e.g. String Literal might be lowered to Constant directly?)
                    // String literals usually LValue, so Copy(Place::Global/Local).
                    Operand::Cast(to_mir_type, Box::new(operand))
                }
            }
            _ => Operand::Cast(target_type_id, Box::new(operand)),
        }
    }

    fn get_operand_type(&mut self, operand: &Operand) -> TypeId {
        match operand {
            Operand::Copy(place) => self.get_place_type(place),
            Operand::Constant(const_id) => {
                let const_val = self.mir_builder.get_constants().get(const_id).unwrap().clone();
                match const_val {
                    ConstValue::Int(_) => self.lower_type(self.registry.type_int),
                    ConstValue::Float(_) => self.lower_type(self.registry.type_double),
                    ConstValue::Bool(_) => self.lower_type(self.registry.type_bool),
                    ConstValue::Null => self.lower_type(self.registry.type_void_ptr),
                    ConstValue::Zero => self.lower_type(self.registry.type_void),
                    ConstValue::Cast(ty, _) => ty,
                    ConstValue::GlobalAddress(global_id) => self.get_global_type(global_id),
                    ConstValue::FunctionAddress(func_id) => self.get_function_type(func_id),
                    ConstValue::StructLiteral(_) | ConstValue::ArrayLiteral(_) => {
                        panic!("Unexpected aggregate constant in get_operand_type")
                    }
                }
            }
            Operand::AddressOf(place) => {
                let pointee = self.get_place_type(place);
                self.mir_builder.add_type(MirType::Pointer { pointee })
            }
            Operand::Cast(ty, _) => *ty,
        }
    }

    fn get_place_type(&mut self, place: &Place) -> TypeId {
        match place {
            Place::Local(local_id) => self.mir_builder.get_locals().get(local_id).unwrap().type_id,
            Place::Global(global_id) => self.get_global_type(*global_id),
            Place::Deref(operand) => {
                let ptr_ty = self.get_operand_type(operand);
                match self.mir_builder.get_type(ptr_ty) {
                    MirType::Pointer { pointee } => *pointee,
                    _ => panic!("Deref of non-pointer type"),
                }
            }
            Place::StructField(base, field_idx) => {
                let struct_ty = self.get_place_type(base);
                match self.mir_builder.get_type(struct_ty) {
                    MirType::Record { field_types, .. } => field_types[*field_idx],
                    _ => panic!("StructField access on non-struct type"),
                }
            }
            Place::ArrayIndex(base, _) => {
                let base_ty = self.get_place_type(base);
                match self.mir_builder.get_type(base_ty) {
                    MirType::Array { element, .. } => *element,
                    MirType::Pointer { pointee, .. } => *pointee,
                    _ => panic!("ArrayIndex access on non-array, non-pointer type"),
                }
            }
        }
    }

    fn get_global_type(&self, global_id: GlobalId) -> TypeId {
        self.mir_builder.get_globals().get(&global_id).unwrap().type_id
    }

    fn get_function_type(&mut self, func_id: MirFunctionId) -> TypeId {
        let func = self.mir_builder.get_functions().get(&func_id).unwrap();
        let ret_ty = func.return_type;
        let mut param_types = Vec::new();
        for &param_id in &func.params {
            param_types.push(self.mir_builder.get_locals().get(&param_id).unwrap().type_id);
        }
        self.mir_builder.add_type(MirType::Function {
            return_type: ret_ty,
            params: param_types,
        })
    }

    fn apply_conversions(&mut self, operand: Operand, node_ref: NodeRef, target_type_id: TypeId) -> Operand {
        // Look up conversions for this node in semantic_info
        if let Some(semantic_info) = &self.ast.semantic_info {
            let idx = node_ref.index();
            if idx < semantic_info.conversions.len() {
                let mut result = operand;
                for conv in &semantic_info.conversions[idx] {
                    result = self.emit_conversion(result, conv, target_type_id);
                }
                return result;
            }
        }
        operand
    }

    fn get_int_type(&mut self) -> TypeId {
        self.mir_builder.add_type(MirType::I32)
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

    fn ensure_place(&mut self, operand: Operand, type_id: TypeId) -> Place {
        if let Operand::Copy(place) = operand {
            *place
        } else {
            let (_, temp_place) = self.create_temp_local_with_assignment(Rvalue::Use(operand), type_id);
            temp_place
        }
    }

    fn emit_rvalue_to_operand(&mut self, rvalue: Rvalue, type_id: TypeId) -> Operand {
        let (_, place) = self.create_temp_local_with_assignment(rvalue, type_id);
        Operand::Copy(Box::new(place))
    }

    fn emit_binary_rvalue(&self, op: &BinaryOp, lhs: Operand, rhs: Operand, is_float: bool) -> Rvalue {
        if is_float {
            let mir_op = self.map_ast_binary_op_to_mir_float(op);
            Rvalue::BinaryFloatOp(mir_op, lhs, rhs)
        } else {
            let mir_op = self.map_ast_binary_op_to_mir_int(op);
            Rvalue::BinaryIntOp(mir_op, lhs, rhs)
        }
    }

    fn emit_unary_rvalue(&self, op: &UnaryOp, operand: Operand, is_float: bool) -> Rvalue {
        if is_float {
            let mir_op = self.map_ast_unary_op_to_mir_float(op);
            Rvalue::UnaryFloatOp(mir_op, operand)
        } else {
            let mir_op = self.map_ast_unary_op_to_mir_int(op);
            Rvalue::UnaryIntOp(mir_op, operand)
        }
    }

    fn operand_to_const_id(&mut self, operand: Operand) -> Option<ConstValueId> {
        match operand {
            Operand::Constant(id) => Some(id),
            Operand::Cast(ty, inner) => {
                let inner_id = self.operand_to_const_id(*inner)?;
                Some(self.create_constant(ConstValue::Cast(ty, inner_id)))
            }
            Operand::AddressOf(place) => {
                if let Place::Global(global_id) = *place {
                    Some(self.create_constant(ConstValue::GlobalAddress(global_id)))
                } else {
                    None
                }
            }
            Operand::Copy(place) => {
                if let Place::Global(global_id) = *place {
                    // In some contexts, a global might be referred to by copy (like array-to-pointer decay)
                    // but for initializers we usually expect AddressOf or Constant.
                    // However, let's be safe.
                    Some(self.create_constant(ConstValue::GlobalAddress(global_id)))
                } else {
                    None
                }
            }
        }
    }

    fn map_ast_binary_op_to_mir_int(&self, ast_op: &BinaryOp) -> BinaryIntOp {
        let op = ast_op.without_assignment().unwrap_or(*ast_op);
        match op {
            BinaryOp::Add => BinaryIntOp::Add,
            BinaryOp::Sub => BinaryIntOp::Sub,
            BinaryOp::Mul => BinaryIntOp::Mul,
            BinaryOp::Div => BinaryIntOp::Div,
            BinaryOp::Mod => BinaryIntOp::Mod,
            BinaryOp::BitAnd => BinaryIntOp::BitAnd,
            BinaryOp::BitOr => BinaryIntOp::BitOr,
            BinaryOp::BitXor => BinaryIntOp::BitXor,
            BinaryOp::LShift => BinaryIntOp::LShift,
            BinaryOp::RShift => BinaryIntOp::RShift,
            BinaryOp::Equal => BinaryIntOp::Eq,
            BinaryOp::NotEqual => BinaryIntOp::Ne,
            BinaryOp::Less => BinaryIntOp::Lt,
            BinaryOp::LessEqual => BinaryIntOp::Le,
            BinaryOp::Greater => BinaryIntOp::Gt,
            BinaryOp::GreaterEqual => BinaryIntOp::Ge,
            // Logic ops are handled separately (short-circuit)
            BinaryOp::LogicAnd | BinaryOp::LogicOr => panic!("Logic ops should be handled separately"),
            BinaryOp::Comma => panic!("Comma op should be handled separately"), // Comma usually handled in expression lowering
            _ => panic!("Unsupported integer binary operator: {:?}", ast_op),
        }
    }

    fn map_ast_binary_op_to_mir_float(&self, ast_op: &BinaryOp) -> BinaryFloatOp {
        let op = ast_op.without_assignment().unwrap_or(*ast_op);
        match op {
            BinaryOp::Add => BinaryFloatOp::Add,
            BinaryOp::Sub => BinaryFloatOp::Sub,
            BinaryOp::Mul => BinaryFloatOp::Mul,
            BinaryOp::Div => BinaryFloatOp::Div,
            BinaryOp::Equal => BinaryFloatOp::Eq,
            BinaryOp::NotEqual => BinaryFloatOp::Ne,
            BinaryOp::Less => BinaryFloatOp::Lt,
            BinaryOp::LessEqual => BinaryFloatOp::Le,
            BinaryOp::Greater => BinaryFloatOp::Gt,
            BinaryOp::GreaterEqual => BinaryFloatOp::Ge,
            _ => panic!("Unsupported float binary operator: {:?}", ast_op),
        }
    }

    fn map_ast_unary_op_to_mir_int(&self, ast_op: &UnaryOp) -> UnaryIntOp {
        match ast_op {
            UnaryOp::Minus => UnaryIntOp::Neg,
            UnaryOp::BitNot => UnaryIntOp::BitwiseNot,
            UnaryOp::LogicNot => UnaryIntOp::LogicalNot,
            _ => panic!("Unsupported integer unary operator: {:?}", ast_op),
        }
    }

    fn map_ast_unary_op_to_mir_float(&self, ast_op: &UnaryOp) -> UnaryFloatOp {
        match ast_op {
            UnaryOp::Minus => UnaryFloatOp::Neg,
            _ => panic!("Unsupported float unary operator: {:?}", ast_op),
        }
    }

    fn with_loop_targets<F>(&mut self, break_target: MirBlockId, continue_target: MirBlockId, f: F)
    where
        F: FnOnce(&mut Self),
    {
        let old_break = self.break_target.replace(break_target);
        let old_continue = self.continue_target.replace(continue_target);

        f(self);

        self.break_target = old_break;
        self.continue_target = old_continue;
    }

    fn lower_inc_dec_common(
        &mut self,
        scope_id: ScopeId,
        operand_ref: NodeRef,
        is_inc: bool,
        is_post: bool,
        need_value: bool,
    ) -> Operand {
        let operand = self.lower_expression(scope_id, operand_ref, true);
        let operand_ty = self.ast.get_resolved_type(operand_ref).unwrap();
        let mir_ty = self.lower_qual_type(operand_ty);

        if self.ast.get_value_category(operand_ref) != Some(ValueCategory::LValue) {
            panic!("Inc/Dec operand must be an lvalue");
        }

        if let Operand::Copy(place) = operand.clone() {
            // If it's post-inc/dec and we need the value, save the old value
            let old_value = if is_post && need_value {
                let rval = Rvalue::Use(operand.clone());
                let (_, temp_place) = self.create_temp_local_with_assignment(rval, mir_ty);
                Some(Operand::Copy(Box::new(temp_place)))
            } else {
                None
            };

            // Determine MIR operation and Rvalue
            let rval = self.create_inc_dec_rvalue(operand.clone(), operand_ty, is_inc);

            // Perform the assignment
            if is_post && !need_value {
                // Optimization: assign directly to place if old value not needed
                self.mir_builder.add_statement(MirStmt::Assign(*place.clone(), rval));
            } else {
                // If we needed old value (is_post), or if it is pre-inc (need new value),
                // we compute to a temp first to ensure correctness and return the right value.
                let (_, new_place) = self.create_temp_local_with_assignment(rval, mir_ty);
                self.emit_assignment(*place.clone(), Operand::Copy(Box::new(new_place.clone())));

                if !is_post {
                    // Pre-inc: return the new value
                    return Operand::Copy(Box::new(new_place));
                }
            }

            if is_post {
                if need_value {
                    old_value.unwrap()
                } else {
                    Operand::Constant(self.create_constant(ConstValue::Int(0)))
                }
            } else {
                // Pre-inc: we already returned inside the block above.
                // RE-FETCH from place as a fallback (should not be reached)
                Operand::Copy(place)
            }
        } else {
            panic!("Inc/Dec operand is not a place");
        }
    }

    fn create_inc_dec_rvalue(&mut self, operand: Operand, operand_ty: QualType, is_inc: bool) -> Rvalue {
        let one_const = Operand::Constant(self.create_constant(ConstValue::Int(1)));
        let minus_one_const = Operand::Constant(self.create_constant(ConstValue::Int(-1)));

        if operand_ty.is_pointer() {
            if is_inc {
                Rvalue::PtrAdd(operand, one_const)
            } else {
                Rvalue::PtrSub(operand, one_const)
            }
        } else {
            // For Integers: Add(delta) (Note: we use Add with negative delta for decrement
            // to support proper wrapping arithmetic and fix previous bugs)
            let rhs = if is_inc { one_const } else { minus_one_const };
            Rvalue::BinaryIntOp(BinaryIntOp::Add, operand, rhs)
        }
    }

    fn lower_pre_incdec(&mut self, scope_id: ScopeId, op: &UnaryOp, lhs_ref: NodeRef) -> Operand {
        let is_inc = matches!(op, UnaryOp::PreIncrement);
        self.lower_inc_dec_common(scope_id, lhs_ref, is_inc, false, true)
    }

    fn lower_post_incdec(
        &mut self,
        scope_id: ScopeId,
        operand_ref: NodeRef,
        is_inc: bool,
        need_value: bool,
    ) -> Operand {
        self.lower_inc_dec_common(scope_id, operand_ref, is_inc, true, need_value)
    }

    fn scan_for_labels(&mut self, node_ref: NodeRef) {
        let node_kind = self.ast.get_kind(node_ref).clone();
        match node_kind {
            NodeKind::Label(name, inner_stmt, _) => {
                if !self.label_map.contains_key(&name) {
                    let block_id = self.mir_builder.create_block();
                    self.label_map.insert(name, block_id);
                }
                self.scan_for_labels(inner_stmt);
            }
            NodeKind::CompoundStatement(cs) => {
                for stmt_ref in cs.stmt_start.range(cs.stmt_len) {
                    self.scan_for_labels(stmt_ref);
                }
            }
            // Add other statement types that can contain labels, like loops and conditionals
            NodeKind::If(if_stmt) => {
                self.scan_for_labels(if_stmt.then_branch);
                if let Some(else_branch) = if_stmt.else_branch {
                    self.scan_for_labels(else_branch);
                }
            }
            NodeKind::While(while_stmt) => self.scan_for_labels(while_stmt.body),
            NodeKind::DoWhile(body, _) => self.scan_for_labels(body),
            NodeKind::For(for_stmt) => self.scan_for_labels(for_stmt.body),
            NodeKind::Switch(_, body) => self.scan_for_labels(body),
            NodeKind::Case(_, stmt) => self.scan_for_labels(stmt),
            NodeKind::CaseRange(_, _, stmt) => self.scan_for_labels(stmt),
            NodeKind::Default(stmt) => self.scan_for_labels(stmt),
            _ => {
                // No labels in expressions or simple statements
            }
        }
    }

    fn lower_goto_statement(&mut self, label_name: &NameId) {
        if let Some(target_block) = self.label_map.get(label_name).copied() {
            self.mir_builder.set_terminator(Terminator::Goto(target_block));
        } else {
            // This should be caught by semantic analysis, but we panic as a safeguard
            panic!("Goto to undefined label '{}'", label_name.as_str());
        }
    }

    fn lower_label_statement(&mut self, scope_id: ScopeId, label_name: &NameId, statement: NodeRef) {
        if let Some(label_block) = self.label_map.get(label_name).copied() {
            // Make sure the current block is terminated before switching
            if !self.mir_builder.current_block_has_terminator() {
                self.mir_builder.set_terminator(Terminator::Goto(label_block));
            }

            self.mir_builder.set_current_block(label_block);
            self.current_block = Some(label_block);

            // Now, lower the statement that follows the label
            self.lower_node_ref(statement, scope_id);
        } else {
            panic!("Label '{}' was not pre-scanned", label_name.as_str());
        }
    }

    fn define_or_declare_function(
        &mut self,
        name: NameId,
        params: Vec<TypeId>,
        ret: TypeId,
        variadic: bool,
        is_def: bool,
    ) {
        if is_def {
            self.mir_builder.define_function(name, params, ret, variadic);
        } else {
            self.mir_builder.declare_function(name, params, ret, variadic);
        }
    }
}
