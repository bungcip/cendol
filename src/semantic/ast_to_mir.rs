use crate::ast::nodes;
use crate::ast::*;
use crate::mir::MirArrayLayout;
use crate::mir::MirProgram;
use crate::mir::MirRecordLayout;
use crate::mir::{
    self, BinaryIntOp, ConstValueId, ConstValueKind, LocalId, MirBlockId, MirBuilder, MirFunctionId, MirStmt, MirType,
    Operand, Place, Rvalue, Terminator, TypeId,
};
use crate::semantic::ArraySizeType;
use crate::semantic::BuiltinType;
use crate::semantic::QualType;
use crate::semantic::StructMember;
use crate::semantic::SymbolKind;
use crate::semantic::SymbolRef;
use crate::semantic::SymbolTable;
use crate::semantic::TypeKind;

use crate::semantic::{DefinitionState, TypeRef, TypeRegistry};
use crate::semantic::{ImplicitConversion, Namespace, ScopeId};
use hashbrown::{HashMap, HashSet};
use log::debug;

use crate::mir::GlobalId;

pub(crate) struct AstToMirLowerer<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: &'a SymbolTable, // Now immutable
    pub(crate) mir_builder: MirBuilder,
    pub(crate) current_function: Option<MirFunctionId>,
    pub(crate) current_block: Option<MirBlockId>,
    pub(crate) current_scope_id: ScopeId,
    pub(crate) registry: &'a mut TypeRegistry,
    pub(crate) local_map: HashMap<SymbolRef, LocalId>,
    pub(crate) global_map: HashMap<SymbolRef, GlobalId>,
    pub(crate) label_map: HashMap<NameId, MirBlockId>,
    pub(crate) type_cache: HashMap<TypeRef, TypeId>,
    pub(crate) type_conversion_in_progress: HashSet<TypeRef>,
    pub(crate) break_target: Option<MirBlockId>,
    pub(crate) continue_target: Option<MirBlockId>,
    pub(crate) switch_case_map: HashMap<NodeRef, MirBlockId>,
    pub(crate) valist_mir_id: Option<TypeId>,
}

impl<'a> AstToMirLowerer<'a> {
    pub(crate) fn new(ast: &'a Ast, symbol_table: &'a SymbolTable, registry: &'a mut TypeRegistry) -> Self {
        let mir_builder = MirBuilder::new(mir::MirModuleId::new(1).unwrap(), 8);
        Self {
            ast,
            symbol_table,
            mir_builder,
            current_function: None,
            current_block: None,
            current_scope_id: ScopeId::GLOBAL,
            local_map: HashMap::new(),
            global_map: HashMap::new(),
            label_map: HashMap::new(),
            registry,
            type_cache: HashMap::new(),
            type_conversion_in_progress: HashSet::new(),
            break_target: None,
            continue_target: None,
            switch_case_map: HashMap::new(),
            valist_mir_id: None,
        }
    }

    // create dummy operand
    pub(crate) fn create_dummy_operand(&mut self) -> Operand {
        self.create_int_operand(9999)
    }

    pub(crate) fn lower_module_complete(&mut self) -> MirProgram {
        debug!("Starting semantic analysis and MIR construction (complete)");
        let root = self.ast.get_root();
        self.lower_node_ref(root);
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

    pub(crate) fn lower_node_ref(&mut self, node_ref: NodeRef) {
        let old_scope = self.current_scope_id;
        let node_kind = self.ast.get_kind(node_ref).clone();

        match node_kind {
            NodeKind::TranslationUnit(tu_data) => {
                self.current_scope_id = self.ast.scope_of(node_ref);
                self.lower_translation_unit(&tu_data)
            }
            NodeKind::Function(function_data) => {
                self.current_scope_id = self.ast.scope_of(node_ref);
                self.lower_function(&function_data)
            }
            NodeKind::For(for_stmt) => {
                self.current_scope_id = self.ast.scope_of(node_ref);
                self.lower_for_statement(&for_stmt)
            }
            NodeKind::CompoundStatement(cs) => {
                self.current_scope_id = self.ast.scope_of(node_ref);
                self.lower_compound_statement(&cs)
            }
            NodeKind::VarDecl(var_decl) => self.lower_var(&var_decl),

            NodeKind::Return(expr) => self.lower_return_statement(&expr),
            NodeKind::If(if_stmt) => self.lower_if_statement(&if_stmt),
            NodeKind::While(while_stmt) => self.lower_while_statement(&while_stmt),
            NodeKind::DoWhile(body, condition) => self.lower_do_while_statement(body, condition),
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                // Expression statement: value not needed, only side-effects
                self.lower_expression(expr_ref, false);
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
            NodeKind::Label(label_name, statement, _) => self.lower_label_statement(&label_name, statement),
            NodeKind::Switch(cond, body) => self.lower_switch_statement(cond, body),
            NodeKind::Case(_, stmt) => self.lower_case_default_statement(node_ref, stmt),
            NodeKind::Default(stmt) => self.lower_case_default_statement(node_ref, stmt),

            // Expressions used as statements (without ExpressionStatement wrapper)
            // This happens in For loop initializers/increments and potentially GnuStatementExpression results.
            NodeKind::Literal(_)
            | NodeKind::Ident(..)
            | NodeKind::UnaryOp(..)
            | NodeKind::BinaryOp(..)
            | NodeKind::TernaryOp(..)
            | NodeKind::PostIncrement(..)
            | NodeKind::PostDecrement(..)
            | NodeKind::Assignment(..)
            | NodeKind::FunctionCall(..)
            | NodeKind::MemberAccess(..)
            | NodeKind::IndexAccess(..)
            | NodeKind::Cast(..)
            | NodeKind::SizeOfExpr(..)
            | NodeKind::SizeOfType(..)
            | NodeKind::AlignOf(..)
            | NodeKind::CompoundLiteral(..)
            | NodeKind::BuiltinVaArg(..)
            | NodeKind::BuiltinExpect(..)
            | NodeKind::BuiltinVaStart(..)
            | NodeKind::BuiltinVaEnd(..)
            | NodeKind::BuiltinVaCopy(..)
            | NodeKind::GenericSelection(..)
            | NodeKind::GnuStatementExpression(..) => {
                self.lower_expression(node_ref, false);
            }

            _ => {}
        }

        self.current_scope_id = old_scope;
    }

    fn lower_translation_unit(&mut self, tu_data: &nodes::TranslationUnitData) {
        self.predeclare_global_functions();
        for child_ref in tu_data.decl_start.range(tu_data.decl_len) {
            self.lower_node_ref(child_ref);
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

                let func_type_kind = self.registry.get(symbol_type_info.ty()).kind.clone();
                if let TypeKind::Function {
                    return_type,
                    parameters,
                    is_variadic,
                    ..
                } = &func_type_kind
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

    pub(crate) fn operand_to_const_id_strict(&mut self, op: Operand, msg: &str) -> ConstValueId {
        if let Some(id) = self.operand_to_const_id(op.clone()) {
            id
        } else {
            panic!("{} - Operand: {:?}", msg, op);
        }
    }

    pub(crate) fn lower_condition(&mut self, condition: NodeRef) -> Operand {
        let cond_operand = self.lower_expression(condition, true);
        // Apply conversions for condition (should be boolean)
        let cond_ty = self.ast.get_resolved_type(condition).unwrap();
        let cond_mir_ty = self.lower_qual_type(cond_ty);
        self.apply_conversions(cond_operand, condition, cond_mir_ty)
    }

    fn lower_compound_statement(&mut self, cs: &nodes::CompoundStmtData) {
        for stmt_ref in cs.stmt_start.range(cs.stmt_len) {
            // We visit all statements regardless of whether the current block is terminated.
            // MirBuilder will suppress statement addition to terminated blocks, but we need
            // to traverse to find nested labels/cases which start new reachable blocks.
            self.lower_node_ref(stmt_ref)
        }
    }

    fn lower_function(&mut self, function_data: &FunctionData) {
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
        let mir_function = self.mir_builder.get_functions().get(&func_id).unwrap().clone();

        for (i, param_ref) in function_data.param_start.range(function_data.param_len).enumerate() {
            if let NodeKind::Param(param_data) = self.ast.get_kind(param_ref) {
                let local_id = mir_function.params[i];
                self.local_map.insert(param_data.symbol, local_id);
            }
        }

        self.lower_node_ref(function_data.body);

        // Handle implicit return if control falls off the end
        if !self.mir_builder.current_block_has_terminator() {
            let func_def = self.mir_builder.get_functions().get(&func_id).unwrap();
            let ret_ty_id = func_def.return_type;
            let ret_ty = self.mir_builder.get_type(ret_ty_id);

            if matches!(ret_ty, crate::mir::MirType::Void) {
                self.mir_builder.set_terminator(crate::mir::Terminator::Return(None));
            } else if func_name.to_string() == "main" && ret_ty.is_int() {
                // main() implicitly returns 0
                let zero = self.create_int_operand(0);
                self.mir_builder
                    .set_terminator(crate::mir::Terminator::Return(Some(zero)));
            } else {
                // Falling off the end of a non-void function is undefined behavior.
                // We leave it as Unreachable (default) or explicitly set it.
                self.mir_builder.set_terminator(crate::mir::Terminator::Unreachable);
            }
        }

        self.current_function = None;
        self.current_block = None;
    }

    fn lower_var(&mut self, var_decl: &VarDeclData) {
        let mir_type_id = self.lower_qual_type(var_decl.ty);
        let (entry_ref, _) = self
            .symbol_table
            .lookup(var_decl.name, self.current_scope_id, Namespace::Ordinary)
            .unwrap();

        self.lower_variable_symbol(entry_ref, mir_type_id);
    }

    pub(crate) fn lower_variable_symbol(&mut self, entry_ref: SymbolRef, mir_type_id: TypeId) {
        let symbol = self.symbol_table.get_symbol(entry_ref);
        let (is_global_sym, storage) = if let SymbolKind::Variable { is_global, storage, .. } = symbol.kind {
            (is_global, storage)
        } else {
            panic!("lower_variable_symbol called on non-variable");
        };

        // Treat static locals as globals for MIR generation purposes (lifetime/storage)
        let is_global = self.current_function.is_none() || is_global_sym || storage == Some(StorageClass::Static);

        if is_global {
            self.lower_global(entry_ref, mir_type_id);
        } else {
            self.lower_local(entry_ref, mir_type_id);
        }
    }

    fn lower_global(&mut self, entry_ref: SymbolRef, mir_type_id: TypeId) {
        let symbol = self.symbol_table.get_symbol(entry_ref);
        let (init, alignment, name, ty) = if let SymbolKind::Variable {
            initializer, alignment, ..
        } = &symbol.kind
        {
            (*initializer, *alignment, symbol.name, symbol.type_info)
        } else {
            unreachable!()
        };

        let initial_value_id = init.and_then(|init_ref| self.lower_initializer_to_const(init_ref, ty));

        let final_init = initial_value_id.or_else(|| {
            if symbol.def_state == DefinitionState::Tentative {
                Some(self.create_constant(mir_type_id, ConstValueKind::Zero))
            } else {
                None
            }
        });

        if let Some(global_id) = self.global_map.get(&entry_ref).copied() {
            if let Some(init_id) = final_init {
                self.mir_builder.set_global_initializer(global_id, init_id);
            }
        } else {
            let global_name = if symbol.scope_id == ScopeId::GLOBAL {
                name
            } else {
                // Mangle name for static local to avoid collision
                crate::ast::NameId::new(format!("{}.{}", name, entry_ref.get()))
            };

            let global_id = self
                .mir_builder
                .create_global_with_init(global_name, mir_type_id, false, final_init);

            if let Some(align) = alignment {
                self.mir_builder.set_global_alignment(global_id, align);
            }

            self.global_map.insert(entry_ref, global_id);
        }
    }

    fn lower_local(&mut self, entry_ref: SymbolRef, mir_type_id: TypeId) {
        let symbol = self.symbol_table.get_symbol(entry_ref);
        let (init, alignment, name, ty) = if let SymbolKind::Variable {
            initializer, alignment, ..
        } = &symbol.kind
        {
            (*initializer, *alignment, symbol.name, symbol.type_info)
        } else {
            unreachable!()
        };

        let local_id = self.mir_builder.create_local(Some(name), mir_type_id, false);

        if let Some(align) = alignment {
            self.mir_builder.set_local_alignment(local_id, align);
        }

        self.local_map.insert(entry_ref, local_id);

        if let Some(initializer) = init {
            let init_operand = self.lower_initializer(initializer, ty, Some(Place::Local(local_id)));
            // If lower_initializer used the destination, it returns Operand::Copy(destination)
            // emit_assignment will then emit Place::Local(local_id) = Place::Local(local_id), which is fine or can be skipped.
            self.emit_assignment(Place::Local(local_id), init_operand);
        }
    }

    fn lower_return_statement(&mut self, expr: &Option<NodeRef>) {
        let operand = expr.map(|expr_ref| {
            let expr_operand = self.lower_expression(expr_ref, true);
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

    fn lower_if_statement(&mut self, if_stmt: &IfStmt) {
        let then_block = self.mir_builder.create_block();
        let else_block = self.mir_builder.create_block();
        let merge_block = self.mir_builder.create_block();

        let cond_converted = self.lower_condition(if_stmt.condition);
        self.mir_builder
            .set_terminator(Terminator::If(cond_converted, then_block, else_block));

        self.mir_builder.set_current_block(then_block);
        self.lower_node_ref(if_stmt.then_branch);
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(merge_block));
        }

        self.mir_builder.set_current_block(else_block);
        if let Some(else_branch) = &if_stmt.else_branch {
            self.lower_node_ref(*else_branch);
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

    fn lower_while_statement(&mut self, while_stmt: &WhileStmt) {
        self.lower_loop_generic(
            None::<fn(&mut Self)>,
            Some(|this: &mut Self| this.lower_condition(while_stmt.condition)),
            |this| this.lower_node_ref(while_stmt.body),
            None::<fn(&mut Self)>,
            false,
        );
    }

    fn lower_do_while_statement(&mut self, body: NodeRef, condition: NodeRef) {
        self.lower_loop_generic(
            None::<fn(&mut Self)>,
            Some(|this: &mut Self| this.lower_condition(condition)),
            |this| this.lower_node_ref(body),
            None::<fn(&mut Self)>,
            true,
        );
    }

    fn lower_for_statement(&mut self, for_stmt: &ForStmt) {
        let init_fn = for_stmt
            .init
            .map(|init| move |this: &mut Self| this.lower_node_ref(init));

        let cond_fn = for_stmt
            .condition
            .map(|cond| move |this: &mut Self| this.lower_condition(cond));

        let inc_fn = for_stmt.increment.map(|inc| {
            move |this: &mut Self| {
                this.lower_expression(inc, false);
            }
        });

        self.lower_loop_generic(
            init_fn,
            cond_fn,
            |this| this.lower_node_ref(for_stmt.body),
            inc_fn,
            false,
        );
    }

    fn lower_switch_statement(&mut self, cond: NodeRef, body: NodeRef) {
        let cond_op = self.lower_expression(cond, true);

        // Integer promotions on controlling expression are handled by lower_expression if sema did it?
        // Semantic analysis should have inserted implicit conversions.
        // But we might need to cast case values to this type.
        let cond_ty_id = self.get_operand_type(&cond_op);

        let merge_block = self.mir_builder.create_block();

        let saved_break = self.break_target;
        self.break_target = Some(merge_block);

        // Collect cases
        let cases = self.collect_switch_cases(body);

        // Create blocks for cases
        let mut case_blocks = Vec::new();
        let mut default_block = None;

        for (node, val_opt) in cases {
            let block = self.mir_builder.create_block();
            self.switch_case_map.insert(node, block);

            if let Some(val) = val_opt {
                case_blocks.push((val, block));
            } else {
                default_block = Some(block);
            }
        }

        // Generate dispatch
        let fallback_block = default_block.unwrap_or(merge_block);

        for (val_id, target_block) in case_blocks {
            let next_test_block = self.mir_builder.create_block();
            let val_const = self.mir_builder.get_constants().get(&val_id).unwrap().clone();

            // Re-create constant with the same type as condition to ensure safe comparison
            // This assumes the values are compatible (integral).
            // Sema should ensure they are compatible.
            // We just cast the constant value to the condition type for the comparison operand.
            // Note: `val_const` is already lowered to some type.

            let val_op = Operand::Constant(val_id);
            let cast_val_op = if val_const.ty != cond_ty_id {
                Operand::Cast(cond_ty_id, Box::new(val_op))
            } else {
                val_op
            };

            // Use Eq comparison
            // If condition is float (illegal in C switch), we panic?
            // Switch only works on integers.
            let cmp_rvalue = Rvalue::BinaryIntOp(BinaryIntOp::Eq, cond_op.clone(), cast_val_op);
            let bool_type_id = self.lower_type(self.registry.type_bool);
            let (_cmp_local, cmp_place) = self.create_temp_local_with_assignment(cmp_rvalue, bool_type_id);
            let cmp_op = Operand::Copy(Box::new(cmp_place));

            self.mir_builder
                .set_terminator(Terminator::If(cmp_op, target_block, next_test_block));

            self.mir_builder.set_current_block(next_test_block);
            self.current_block = Some(next_test_block);
        }

        // Final jump to default or merge
        self.mir_builder.set_terminator(Terminator::Goto(fallback_block));

        // Lower body
        // Start a dummy unreachable block for the body entry (to catch unreachable statements)
        let body_entry_dummy = self.mir_builder.create_block();
        // Do not jump to it. It is unreachable.

        self.mir_builder.set_current_block(body_entry_dummy);
        self.current_block = Some(body_entry_dummy);

        self.lower_node_ref(body);

        // If body falls through, go to merge
        if self.mir_builder.current_block_has_terminator() == false {
            // Check if terminator is Unreachable (default) - if so, we can replace it or just leave it?
            // `current_block_has_terminator` returns false if it is Unreachable.
            // But if we are in body_entry_dummy and it's empty, we shouldn't jump to merge.
            // Actually, if execution falls through the body, it should hit merge.
            // But valid C code falling through end of switch goes to next stmt (merge).
            self.mir_builder.set_terminator(Terminator::Goto(merge_block));
        }

        self.break_target = saved_break;
        self.mir_builder.set_current_block(merge_block);
        self.current_block = Some(merge_block);
    }

    fn lower_case_default_statement(&mut self, node: NodeRef, stmt: NodeRef) {
        let target_block = *self.switch_case_map.get(&node).expect("Case/Default not mapped");

        // Fallthrough from previous block
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(target_block));
        }

        self.mir_builder.set_current_block(target_block);
        self.current_block = Some(target_block);

        self.lower_node_ref(stmt);
    }

    fn collect_switch_cases(&mut self, node: NodeRef) -> Vec<(NodeRef, Option<ConstValueId>)> {
        let mut cases = Vec::new();
        self.collect_switch_cases_recursive(node, &mut cases);
        cases
    }

    fn collect_switch_cases_recursive(&mut self, node: NodeRef, cases: &mut Vec<(NodeRef, Option<ConstValueId>)>) {
        let kind = self.ast.get_kind(node).clone();
        match kind {
            NodeKind::Case(expr, stmt) => {
                let op = self.lower_expression(expr, true);
                let val = self.operand_to_const_id_strict(op, "Case label must be constant");
                cases.push((node, Some(val)));
                self.collect_switch_cases_recursive(stmt, cases);
            }
            NodeKind::Default(stmt) => {
                cases.push((node, None));
                self.collect_switch_cases_recursive(stmt, cases);
            }
            NodeKind::Switch(..) => {
                // Do not recurse into nested switch
            }
            _ => {
                kind.visit_children(|child| self.collect_switch_cases_recursive(child, cases));
            }
        }
    }

    pub(crate) fn emit_assignment(&mut self, place: Place, operand: Operand) {
        if self.mir_builder.current_block_has_terminator() {
            return;
        }

        // Avoid identity assignments like %x = %x
        if let Operand::Copy(box_place) = &operand
            && **box_place == place
        {
            return;
        }

        let rvalue = Rvalue::Use(operand);
        let stmt = MirStmt::Assign(place, rvalue);
        self.mir_builder.add_statement(stmt);
    }

    pub(crate) fn lower_qual_type(&mut self, ty: QualType) -> TypeId {
        self.lower_type(ty.ty())
    }

    pub(crate) fn lower_type(&mut self, type_ref: TypeRef) -> TypeId {
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

        let ast_type_kind = self.registry.get(type_ref).kind.clone();

        if let TypeKind::Record { .. } = &ast_type_kind {
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

            let mir_type = if let TypeKind::Record {
                tag,
                members,
                is_union,
                is_complete,
            } = &ast_type_kind
            {
                self.lower_record_type(type_ref, tag, members, *is_union, *is_complete)
            } else {
                unreachable!()
            };

            // Remove from in-progress set
            self.type_conversion_in_progress.remove(&type_ref);

            // Replace the placeholder entry with the real type
            self.mir_builder.update_type(placeholder_id, mir_type);
            placeholder_id
        } else {
            let mir_type = match &ast_type_kind {
                TypeKind::Builtin(b) => {
                    if matches!(b, BuiltinType::VaList) {
                        self.lower_valist_type()
                    } else {
                        self.lower_builtin_type(b)
                    }
                }
                TypeKind::Pointer { pointee } => self.lower_pointer_type(*pointee),
                TypeKind::Array { element_type, size } => self.lower_array_type(type_ref, *element_type, size),
                TypeKind::Function {
                    return_type,
                    parameters,
                    is_variadic,
                    ..
                } => self.lower_function_type(return_type, parameters, *is_variadic),
                TypeKind::Record { .. } => unreachable!(),
                _ => MirType::I32,
            };

            let type_id = self.mir_builder.add_type(mir_type);
            self.type_cache.insert(type_ref, type_id);
            type_id
        }
    }

    fn lower_valist_type(&mut self) -> MirType {
        let u32_id = self.lower_type(self.registry.type_int_unsigned);
        let u64_id = self.lower_type(self.registry.type_long_long_unsigned);

        let record_layout = MirRecordLayout {
            size: 24,
            alignment: 8,
            field_offsets: vec![0, 4, 8, 16],
        };

        // Cache the __va_list_tag record type to ensure canonical type usage
        let record_id = if let Some(id) = self.valist_mir_id {
            id
        } else {
            let record_type = MirType::Record {
                name: NameId::new("__va_list_tag"),
                field_types: vec![u32_id, u32_id, u64_id, u64_id],
                field_names: Vec::new(),
                is_union: false,
                layout: record_layout,
            };
            let id = self.mir_builder.add_type(record_type);
            self.valist_mir_id = Some(id);
            id
        };

        let array_layout = MirArrayLayout {
            size: 24,
            align: 8,
            stride: 24,
        };

        MirType::Array {
            element: record_id,
            size: 1,
            layout: array_layout,
        }
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
            BuiltinType::Double => MirType::F64,
            BuiltinType::LongDouble => MirType::F128,
            BuiltinType::Signed => MirType::I32,
            BuiltinType::VaList => MirType::U64, // Opaque handle
        }
    }

    fn lower_pointer_type(&mut self, pointee: QualType) -> MirType {
        MirType::Pointer {
            pointee: self.lower_type(pointee.ty()),
        }
    }

    fn lower_array_type(&mut self, type_ref: TypeRef, element_type: TypeRef, size: &ArraySizeType) -> MirType {
        let element = self.lower_type(element_type);

        match size {
            ArraySizeType::Constant(s) => {
                let (layout_size, layout_align, element_ref, _) = self.registry.get_array_layout(type_ref);
                let element_layout = self.registry.get_layout(element_ref);

                MirType::Array {
                    element,
                    size: *s,
                    layout: MirArrayLayout {
                        size: layout_size,
                        align: layout_align,
                        stride: element_layout.size,
                    },
                }
            }
            _ => {
                // For VLA or incomplete array, layout is not computed in registry.
                // We use dummy layout (size 0) but try to preserve alignment/stride from element type.
                let (align, stride) = if element_type.is_inline_array()
                    || element_type.is_inline_pointer()
                    || self.registry.types[element_type.index()].layout.is_some()
                {
                    let layout = self.registry.get_layout(element_type);
                    (layout.alignment, layout.size)
                } else {
                    // Element layout also unknown (e.g. nested VLA or incomplete)
                    (1, 0)
                };

                MirType::Array {
                    element,
                    size: 0,
                    layout: MirArrayLayout { size: 0, align, stride },
                }
            }
        }
    }

    fn lower_function_type(
        &mut self,
        return_type: &TypeRef,
        parameters: &[crate::semantic::FunctionParameter],
        is_variadic: bool,
    ) -> MirType {
        let return_type = self.lower_type(*return_type);
        let mut params = Vec::new();
        for p in parameters {
            let param_ty_id = self.lower_qual_type(p.param_type);
            // Adjust array parameters to pointers (C standard).
            // This is especially important for VaList which treats itself as an array but is passed as a pointer.
            // Sema handles explicit arrays, but BuiltinType::VaList is lowered to Array here.
            let param_ty = self.mir_builder.get_type(param_ty_id);
            let adjusted_ty_id = if let MirType::Array { element, .. } = param_ty {
                self.mir_builder.add_type(MirType::Pointer { pointee: *element })
            } else {
                param_ty_id
            };
            params.push(adjusted_ty_id);
        }
        MirType::Function {
            return_type,
            params,
            is_variadic,
        }
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

    pub(crate) fn create_constant(&mut self, ty: TypeId, kind: ConstValueKind) -> ConstValueId {
        self.mir_builder.create_constant(ty, kind)
    }

    pub(crate) fn create_int_operand(&mut self, val: i64) -> Operand {
        let ty_id = self.get_int_type();
        Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(val)))
    }

    pub(crate) fn create_float_operand(&mut self, val: f64) -> Operand {
        let ty_id = self.lower_type(self.registry.type_double);
        Operand::Constant(self.create_constant(ty_id, ConstValueKind::Float(val)))
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
            ImplicitConversion::NullPointerConstant => {
                let ty_id = self.lower_type(self.registry.type_int);
                Operand::Cast(
                    to_mir_type,
                    Box::new(Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(0)))),
                )
            }
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

    pub(crate) fn get_operand_type(&mut self, operand: &Operand) -> TypeId {
        match operand {
            Operand::Copy(place) => self.get_place_type(place),
            Operand::Constant(const_id) => {
                let const_val = self.mir_builder.get_constants().get(const_id).unwrap();
                const_val.ty
            }
            Operand::AddressOf(place) => {
                let pointee = self.get_place_type(place);
                self.mir_builder.add_type(MirType::Pointer { pointee })
            }
            Operand::Cast(ty, _) => *ty,
        }
    }

    pub(crate) fn get_place_type(&mut self, place: &Place) -> TypeId {
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

    pub(crate) fn get_function_type(&mut self, func_id: MirFunctionId) -> TypeId {
        let func = self.mir_builder.get_functions().get(&func_id).unwrap();
        let ret_ty = func.return_type;
        let mut param_types = Vec::new();
        for &param_id in &func.params {
            param_types.push(self.mir_builder.get_locals().get(&param_id).unwrap().type_id);
        }
        self.mir_builder.add_type(MirType::Function {
            return_type: ret_ty,
            params: param_types,
            is_variadic: func.is_variadic,
        })
    }

    pub(crate) fn apply_conversions(&mut self, operand: Operand, node_ref: NodeRef, target_type_id: TypeId) -> Operand {
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

    pub(crate) fn get_int_type(&mut self) -> TypeId {
        self.lower_type(self.registry.type_int)
    }

    pub(crate) fn create_temp_local(&mut self, type_id: TypeId) -> (LocalId, Place) {
        let local_id = self.mir_builder.create_local(None, type_id, false);
        let place = Place::Local(local_id);
        (local_id, place)
    }

    pub(crate) fn create_temp_local_with_assignment(&mut self, rvalue: Rvalue, type_id: TypeId) -> (LocalId, Place) {
        let (local_id, place) = self.create_temp_local(type_id);
        let assign_stmt = MirStmt::Assign(place.clone(), rvalue);
        self.mir_builder.add_statement(assign_stmt);
        (local_id, place)
    }

    pub(crate) fn ensure_place(&mut self, operand: Operand, type_id: TypeId) -> Place {
        if let Operand::Copy(place) = operand {
            *place
        } else {
            let (_, temp_place) = self.create_temp_local_with_assignment(Rvalue::Use(operand), type_id);
            temp_place
        }
    }

    pub(crate) fn emit_rvalue_to_operand(&mut self, rvalue: Rvalue, type_id: TypeId) -> Operand {
        let (_, place) = self.create_temp_local_with_assignment(rvalue, type_id);
        Operand::Copy(Box::new(place))
    }

    pub(crate) fn operand_to_const_id(&mut self, operand: Operand) -> Option<ConstValueId> {
        match operand {
            Operand::Constant(id) => Some(id),
            Operand::Cast(ty, inner) => {
                // Recursively try to get constant from inner operand
                if let Some(inner_const_id) = self.operand_to_const_id(*inner) {
                    let inner_const = self.mir_builder.get_constants().get(&inner_const_id).unwrap();
                    // Create a new constant with the target type but same kind
                    Some(self.create_constant(ty, inner_const.kind.clone()))
                } else {
                    None
                }
            }
            Operand::AddressOf(place) => {
                if let Place::Global(global_id) = *place {
                    let global_type = self.get_global_type(global_id);
                    let ptr_ty = self.mir_builder.add_type(MirType::Pointer { pointee: global_type });
                    Some(self.create_constant(ptr_ty, ConstValueKind::GlobalAddress(global_id)))
                } else {
                    None
                }
            }
            Operand::Copy(place) => {
                if let Place::Global(global_id) = *place {
                    // If it is an array, using it in an expression decays to a pointer (GlobalAddress)
                    let global_ty_id = self.get_global_type(global_id);
                    let global_mir_ty = self.mir_builder.get_type(global_ty_id);
                    if matches!(global_mir_ty, MirType::Array { .. }) {
                        let ptr_ty = self.mir_builder.add_type(MirType::Pointer { pointee: global_ty_id });
                        return Some(self.create_constant(ptr_ty, ConstValueKind::GlobalAddress(global_id)));
                    }

                    // If we are copying a global, and it has a constant initializer, return that value.
                    // This handles compound literals which are lowered to globals.
                    let global = self.mir_builder.get_globals().get(&global_id).unwrap();
                    global.initial_value
                } else {
                    None
                }
            }
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

    fn scan_for_labels(&mut self, node_ref: NodeRef) {
        let node_kind = self.ast.get_kind(node_ref).clone();
        if let NodeKind::Label(name, _, _) = node_kind
            && !self.label_map.contains_key(&name)
        {
            let block_id = self.mir_builder.create_block();
            self.label_map.insert(name, block_id);
        }
        node_kind.visit_children(|child| self.scan_for_labels(child));
    }

    fn lower_goto_statement(&mut self, label_name: &NameId) {
        if let Some(target_block) = self.label_map.get(label_name).copied() {
            self.mir_builder.set_terminator(Terminator::Goto(target_block));
        } else {
            // This should be caught by semantic analysis, but we panic as a safeguard
            panic!("Goto to undefined label '{}'", label_name.as_str());
        }
    }

    fn lower_label_statement(&mut self, label_name: &NameId, statement: NodeRef) {
        if let Some(label_block) = self.label_map.get(label_name).copied() {
            // Make sure the current block is terminated before switching
            if !self.mir_builder.current_block_has_terminator() {
                self.mir_builder.set_terminator(Terminator::Goto(label_block));
            }

            self.mir_builder.set_current_block(label_block);
            self.current_block = Some(label_block);

            // Now, lower the statement that follows the label
            self.lower_node_ref(statement);
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
