use crate::ast::nodes;
use crate::ast::*;
use crate::mir::MirArrayLayout;
use crate::mir::MirProgram;
use crate::mir::{
    AtomicMemOrder, BinaryIntOp, CallTarget, ConstValueId, ConstValueKind, GlobalDecl, LocalId, MirBlockId, MirBuilder,
    MirFieldLayout, MirFunctionId, MirLinkage, MirRecordLayout, MirStmt, MirType, Operand, Place, Rvalue, Terminator,
    TypeId,
};
use crate::semantic::ArraySizeType;
use crate::semantic::BuiltinType;
use crate::semantic::FunctionParameter;
use crate::semantic::QualType;
use crate::semantic::SymbolKind;
use crate::semantic::SymbolRef;
use crate::semantic::SymbolTable;
use crate::semantic::TypeKind;

use crate::semantic::const_eval::ConstEvalCtx;
use crate::semantic::{Conversion, ScopeId};
use crate::semantic::{DefinitionState, TypeRef, TypeRegistry};
use hashbrown::{HashMap, HashSet};
use target_lexicon::Architecture;

use crate::mir::GlobalId;

pub(crate) struct FunctionState {
    pub(crate) func_id: MirFunctionId,
    pub(crate) current_block: Option<MirBlockId>,
    pub(crate) local_map: HashMap<SymbolRef, LocalId>,
    pub(crate) vla_map: HashMap<SymbolRef, (LocalId, LocalId)>,
    pub(crate) label_map: HashMap<NameId, MirBlockId>,
    pub(crate) break_target: Option<MirBlockId>,
    pub(crate) continue_target: Option<MirBlockId>,
    pub(crate) switch_case_map: HashMap<NodeRef, MirBlockId>,
    pub(crate) scope_cleanup: Vec<Vec<LocalId>>,
}

impl FunctionState {
    fn new(func_id: MirFunctionId, entry_block: MirBlockId) -> Self {
        Self {
            func_id,
            current_block: Some(entry_block),
            local_map: HashMap::new(),
            vla_map: HashMap::new(),
            label_map: HashMap::new(),
            break_target: None,
            continue_target: None,
            switch_case_map: HashMap::new(),
            scope_cleanup: Vec::new(),
        }
    }
}

pub(crate) struct MirGen<'a> {
    pub(crate) ast: &'a Ast,
    pub(crate) symbol_table: &'a SymbolTable, // Now immutable
    pub(crate) mb: MirBuilder,
    pub(crate) registry: &'a mut TypeRegistry,
    pub(crate) global_map: HashMap<SymbolRef, GlobalId>,
    pub(crate) type_cache: HashMap<TypeRef, TypeId>,
    pub(crate) type_conversion_in_progress: HashSet<TypeRef>,
    pub(crate) valist_mir_id: Option<TypeId>,
    pub(crate) current_scope_id: ScopeId,
    pub(crate) func_state: Option<FunctionState>,
    pub(crate) keywords: MirGenKeywords,
}

pub(crate) struct MirGenKeywords {
    pub(crate) main: NameId,
    pub(crate) builtin_nanf: NameId,
    pub(crate) builtin_nan: NameId,
    pub(crate) builtin_inff: NameId,
    pub(crate) builtin_inf: NameId,
    pub(crate) builtin_huge_valf: NameId,
    pub(crate) builtin_huge_val: NameId,
}

impl MirGenKeywords {
    fn new() -> Self {
        Self {
            main: NameId::new("main"),
            builtin_nanf: NameId::new("__builtin_nanf"),
            builtin_nan: NameId::new("__builtin_nan"),
            builtin_inff: NameId::new("__builtin_inff"),
            builtin_inf: NameId::new("__builtin_inf"),
            builtin_huge_valf: NameId::new("__builtin_huge_valf"),
            builtin_huge_val: NameId::new("__builtin_huge_val"),
        }
    }
}

impl<'a> MirGen<'a> {
    pub(crate) fn create_block(&mut self) -> MirBlockId {
        let (func_id, current_block) = self.get_func_info();
        let mut fb = self.mb.build_function(func_id, current_block);
        fb.create_block()
    }

    pub(crate) fn set_current_block(&mut self, block_id: MirBlockId) {
        let state = self.func_state_mut();
        state.current_block = Some(block_id);
    }

    pub(crate) fn add_stmt(&mut self, stmt: MirStmt) -> crate::mir::MirStmtId {
        let (func_id, current_block) = self.get_func_info();
        let mut fb = self.mb.build_function(func_id, current_block);
        fb.add_stmt(stmt)
    }

    pub(crate) fn set_terminator(&mut self, terminator: crate::mir::Terminator) {
        let (func_id, current_block) = self.get_func_info();
        let mut fb = self.mb.build_function(func_id, current_block);
        fb.set_terminator(terminator)
    }

    pub(crate) fn current_block_has_terminator(&mut self) -> bool {
        let (func_id, current_block) = self.get_func_info();
        let fb = self.mb.build_function(func_id, current_block);
        fb.current_block_has_terminator()
    }

    pub(crate) fn create_local(&mut self, name: Option<NameId>, type_id: TypeId, is_param: bool) -> LocalId {
        let (func_id, current_block) = self.get_func_info();
        let mut fb = self.mb.build_function(func_id, current_block);
        fb.create_local(name, type_id, is_param)
    }

    pub(crate) fn set_local_alignment(&mut self, local_id: LocalId, alignment: u16) {
        let (func_id, current_block) = self.get_func_info();
        let mut fb = self.mb.build_function(func_id, current_block);
        fb.set_local_alignment(local_id, alignment)
    }

    pub(super) fn func_state_mut(&mut self) -> &mut FunctionState {
        self.func_state.as_mut().expect("Not in a function")
    }

    fn get_func_info(&self) -> (MirFunctionId, Option<MirBlockId>) {
        let state = self.func_state.as_ref().expect("Not in a function");
        (state.func_id, state.current_block)
    }

    pub(super) fn get_or_lower_global(&mut self, sym: SymbolRef) -> GlobalId {
        if let Some(id) = self.global_map.get(&sym) {
            return *id;
        }

        let entry = self.symbol_table.get_symbol(sym);
        let qt = entry.type_info;
        let mir_ty = self.lower_qual_type(qt);
        self.visit_variable(sym, mir_ty);

        *self
            .global_map
            .get(&sym)
            .expect("Global should be lowered by visit_variable")
    }

    pub(super) fn get_or_declare_function(&mut self, sym: SymbolRef) -> MirFunctionId {
        let entry = self.symbol_table.get_symbol(sym);
        if let Some(id) = self.mb.find_function_by_name(entry.name) {
            return id;
        }

        let storage = if let SymbolKind::Function { storage, .. } = &entry.kind {
            *storage
        } else {
            None
        };

        let linkage = self.calculate_linkage(storage, entry.def_state);
        let has_definition = entry.def_state == DefinitionState::Defined;

        let mut fn_data = None;
        {
            let type_info = self.registry.get(entry.type_info.ty());
            if let TypeKind::Function {
                return_type,
                parameters,
                is_variadic,
                ..
            } = &type_info.kind
            {
                fn_data = Some((
                    *return_type,
                    parameters.iter().map(|p| p.param_type).collect::<Vec<_>>(),
                    *is_variadic,
                ));
            }
        }

        if let Some((return_type, parameters, is_variadic)) = fn_data {
            let return_mir_type = self.lower_type(return_type);
            let param_mir_types = parameters.into_iter().map(|p| self.lower_qual_type(p)).collect();

            self.define_or_declare_function(
                entry.name,
                param_mir_types,
                return_mir_type,
                is_variadic,
                has_definition,
                linkage,
            )
        } else {
            let return_mir_type = self.get_int_type();
            self.define_or_declare_function(entry.name, vec![], return_mir_type, false, has_definition, linkage)
        }
    }
    pub(crate) fn new(ast: &'a Ast, symbol_table: &'a SymbolTable, registry: &'a mut TypeRegistry) -> Self {
        Self {
            ast,
            symbol_table,
            mb: MirBuilder::new(8),
            registry,
            global_map: HashMap::new(),
            type_cache: HashMap::new(),
            type_conversion_in_progress: HashSet::new(),
            valist_mir_id: None,
            keywords: MirGenKeywords::new(),
            current_scope_id: ScopeId::GLOBAL,
            func_state: None,
        }
    }

    pub(crate) fn const_ctx(&self) -> ConstEvalCtx<'_> {
        ConstEvalCtx {
            ast: self.ast,
            symbol_table: self.symbol_table,
            registry: self.registry,
            semantic_info: &self.ast.semantic_info,
        }
    }

    // create dummy operand
    pub(super) fn create_dummy_operand(&mut self) -> Operand {
        self.create_int_operand(9999)
    }

    pub(crate) fn create_anon_global(&mut self, mir_ty: TypeId, init_const: ConstValueId) -> GlobalId {
        let name = self.mb.get_next_anon_global_name();
        self.mb.create_global(GlobalDecl::anonymous(name, mir_ty, init_const))
    }

    pub(crate) fn visit_module(&mut self) -> MirProgram {
        let root = self.ast.get_root();
        self.visit_node(root);

        // Take ownership of the builder to consume it, replacing it with a dummy.
        let builder = std::mem::replace(&mut self.mb, MirBuilder::new(8));
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

    pub(crate) fn visit_node(&mut self, node: NodeRef) {
        let old_scope = self.current_scope_id;
        let node_kind = *self.ast.get_kind(node);

        match node_kind {
            NodeKind::TranslationUnit(tu) => {
                self.current_scope_id = self.ast.scope_of(node);
                self.visit_translation_unit(&tu)
            }
            NodeKind::Function(function) => {
                self.current_scope_id = self.ast.scope_of(node);
                self.visit_function(&function)
            }
            NodeKind::For(for_stmt) => {
                self.current_scope_id = self.ast.scope_of(node);
                self.visit_for_stmt(&for_stmt)
            }
            NodeKind::CompoundStmt(cs) => {
                self.current_scope_id = self.ast.scope_of(node);
                self.visit_compound_statement(&cs)
            }
            NodeKind::VarDecl(var_decl) => self.visit_var_decl(&var_decl),

            NodeKind::Return(expr) => self.visit_return_stmt(&expr),
            NodeKind::If(if_stmt) => self.visit_if_stmt(&if_stmt),
            NodeKind::While(while_stmt) => self.visit_while_stmt(&while_stmt),
            NodeKind::DoWhile(body, condition) => self.visit_do_while_stmt(body, condition),
            NodeKind::ExpressionStmt(Some(expr)) => {
                // Expression statement: value not needed, only side-effects
                self.visit_expression(expr, false);
            }
            NodeKind::AsmStmt(_) => {
                // Ignore inline assembly in Cranelift backend for now
            }
            NodeKind::Break => {
                let target = self.func_state_mut().break_target.unwrap();
                self.set_terminator(Terminator::Goto(target));
            }
            NodeKind::Continue => {
                let target = self.func_state_mut().continue_target.unwrap();
                self.set_terminator(Terminator::Goto(target));
            }
            NodeKind::Goto(label_name, _) => self.visit_goto_stmt(label_name),
            NodeKind::Label(label_name, stmt, _) => self.visit_label_stmt(label_name, stmt),
            NodeKind::Switch(cond, body) => self.visit_switch_stmt(cond, body),
            NodeKind::Case(_, stmt) => self.visit_case_default_stmt(node, stmt),
            NodeKind::CaseRange(.., stmt) => self.visit_case_default_stmt(node, stmt),
            NodeKind::Default(stmt) => self.visit_case_default_stmt(node, stmt),

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
            | NodeKind::AlignOfType(..)
            | NodeKind::AlignOfExpr(..)
            | NodeKind::CompoundLiteral(..)
            | NodeKind::BuiltinVaArg(..)
            | NodeKind::BuiltinExpect(..)
            | NodeKind::BuiltinVaStart(..)
            | NodeKind::BuiltinVaEnd(..)
            | NodeKind::BuiltinVaCopy(..)
            | NodeKind::GenericSelection(..)
            | NodeKind::StatementExpr(..) => {
                self.visit_expression(node, false);
            }

            _ => {}
        }

        self.current_scope_id = old_scope;
    }

    fn visit_translation_unit(&mut self, tu: &nodes::TranslationUnit) {
        self.predeclare_global_functions();
        for child in tu.decl_start.range(tu.decl_len) {
            self.visit_node(child);
        }
    }

    fn predeclare_global_functions(&mut self) {
        let global_scope = self.symbol_table.get_scope(ScopeId::GLOBAL);
        let mut global_symbols: Vec<_> = global_scope.symbols.values().copied().collect();

        // Sort by symbol name to ensure deterministic order for snapshot tests
        global_symbols.sort_by_key(|s| self.symbol_table.get_symbol(*s).name);

        for sym in global_symbols {
            if let SymbolKind::Function { .. } = self.symbol_table.get_symbol(sym).kind {
                self.get_or_declare_function(sym);
            }
        }
    }

    pub(super) fn operand_to_const_id_strict(&mut self, op: Operand, msg: &str) -> ConstValueId {
        if let Some(id) = self.operand_to_const_id(&op) {
            id
        } else {
            panic!("{} - Operand: {:?}", msg, op);
        }
    }

    pub(super) fn evaluate_constant_usize(&mut self, expr: NodeRef, error_msg: &str) -> usize {
        let operand = self.visit_expression(expr, true);
        if let Some(const_id) = self.operand_to_const_id(&operand) {
            let const_val = self.mb.get_constants().get(const_id.index()).unwrap();
            if let ConstValueKind::Int(val) = const_val.kind {
                val as usize
            } else {
                panic!("{}", error_msg);
            }
        } else {
            panic!("{}", error_msg);
        }
    }

    pub(super) fn lower_condition(&mut self, condition: NodeRef) -> Operand {
        let cond_operand = self.visit_expression(condition, true);
        // Apply conversions for condition (should be boolean)
        let cond_ty = self.ast.qual_type_of(condition);
        let cond_mir_ty = self.lower_qual_type(cond_ty);
        let converted = self.apply_conversions(cond_operand, condition, cond_mir_ty);
        self.cast_operand_to_bool(converted)
    }

    fn visit_compound_statement(&mut self, cs: &nodes::CompoundStmt) {
        self.func_state_mut().scope_cleanup.push(Vec::new());
        for stmt in cs.stmt_start.range(cs.stmt_len) {
            // We visit all statements regardless of whether the current block is terminated.
            // MirBuilder will suppress statement addition to terminated blocks, but we need
            // to traverse to find nested labels/cases which start new reachable blocks.
            self.visit_node(stmt)
        }
        let cleanup = self.func_state_mut().scope_cleanup.pop().unwrap();
        for ptr_local_id in cleanup {
            let ptr_op = Operand::Copy(Box::new(Place::Local(ptr_local_id)));
            self.emit_free_call(ptr_op);
        }
    }

    fn visit_function(&mut self, function: &Function) {
        let symbol_entry = self.symbol_table.get_symbol(function.symbol);
        let func_name = symbol_entry.name;

        let func_id = self
            .mb
            .find_function_by_name(func_name)
            .expect("Function not found in MIR builder");

        let entry_block_id = {
            let mut fb = self.mb.build_function(func_id, None);
            let entry_block_id = fb.create_block();
            fb.builder.set_function_entry_block(func_id, entry_block_id);
            entry_block_id
        };

        self.func_state = Some(FunctionState::new(func_id, entry_block_id));

        let param_len = if let SymbolKind::Function { param_len, .. } = &symbol_entry.kind {
            *param_len
        } else {
            0
        };

        self.map_parameters(func_id, function, param_len);

        let body_node = function.child_start.add_offset(param_len);
        self.scan_for_labels(body_node);
        self.visit_node(body_node);

        self.emit_implicit_return(func_id, func_name);

        self.func_state = None;
    }

    fn map_parameters(&mut self, func_id: MirFunctionId, function: &Function, param_len: u16) {
        let mir_params = self.mb.get_functions().get(func_id.index()).unwrap().params.clone();
        for (i, param) in function.child_start.range(param_len).enumerate() {
            if let NodeKind::Param(param) = self.ast.get_kind(param) {
                let local_id = mir_params[i];
                self.func_state_mut().local_map.insert(param.symbol, local_id);
            }
        }
    }

    fn emit_implicit_return(&mut self, func_id: MirFunctionId, func_name: NameId) {
        if self.current_block_has_terminator() {
            return;
        }

        let func_def = self.mb.get_functions().get(func_id.index()).unwrap();
        let ret_ty_id = func_def.return_type;
        let ret_ty = self.mb.get_type(ret_ty_id).clone();

        if matches!(ret_ty, crate::mir::MirType::Void) {
            self.set_terminator(Terminator::Return(None));
        } else if func_name == self.keywords.main && ret_ty.is_int() {
            let zero = self.create_int_operand(0);
            self.set_terminator(Terminator::Return(Some(zero)));
        } else {
            self.set_terminator(Terminator::Unreachable);
        }
    }

    fn visit_var_decl(&mut self, var_decl: &VarDecl) {
        let sym = var_decl.symbol;
        let symbol = self.symbol_table.get_symbol(sym);
        let qt = symbol.type_info;
        let mir_type_id = self.lower_qual_type(qt);

        self.visit_variable(sym, mir_type_id);
    }

    fn visit_variable(&mut self, sym: SymbolRef, mir_type_id: TypeId) {
        let symbol = self.symbol_table.get_symbol(sym);
        let (is_global_sym, storage) = if let SymbolKind::Variable { is_global, storage, .. } = symbol.kind {
            (is_global, storage)
        } else {
            panic!("visit_variable called on non-variable");
        };

        // Treat static locals as globals for MIR generation purposes (lifetime/storage)
        let is_global = self.func_state.is_none() || is_global_sym || storage == Some(StorageClass::Static);

        if is_global {
            self.visit_global_symbol(sym, mir_type_id);
        } else {
            self.visit_local_symbol(sym, mir_type_id);
        }
    }

    fn visit_global_symbol(&mut self, sym: SymbolRef, mir_type_id: TypeId) {
        if self.global_map.contains_key(&sym) {
            return;
        }

        let symbol = self.symbol_table.get_symbol(sym);
        let SymbolKind::Variable {
            initializer: init,
            alignment,
            storage,
            is_thread_local: is_tls,
            ..
        } = symbol.kind
        else {
            unreachable!()
        };

        let global_name = if symbol.scope_id == ScopeId::GLOBAL {
            symbol.name
        } else {
            // Mangle name for static local to avoid collision
            crate::ast::NameId::new(format!("{}.{}", symbol.name, sym.get()))
        };

        let linkage = self.calculate_linkage(storage, symbol.def_state);

        let global_id = self.mb.create_global(GlobalDecl {
            name: global_name,
            type_id: mir_type_id,
            is_constant: symbol.is_const(),
            is_tls,
            linkage,
            initial_value: None,
        });

        if let Some(align) = alignment {
            self.mb.set_global_alignment(global_id, align);
        }

        self.global_map.insert(sym, global_id);

        // Static locals must be evaluated as constants, even if we are inside a function.
        // We temporarily unset current_function to force constant evaluation mode.
        let saved_state = self.func_state.take();
        let initial_value_id = init.and_then(|init| self.eval_init_to_const(init, symbol.type_info));
        self.func_state = saved_state;

        let final_init = initial_value_id.or_else(|| {
            if symbol.def_state == DefinitionState::Tentative {
                Some(self.create_constant(mir_type_id, ConstValueKind::Zero))
            } else {
                None
            }
        });

        if let Some(init_id) = final_init {
            self.mb.set_global_initializer(global_id, init_id);
        }
    }

    fn visit_local_symbol(&mut self, sym: SymbolRef, mir_type_id: TypeId) {
        let symbol = self.symbol_table.get_symbol(sym);
        let SymbolKind::Variable {
            initializer: init,
            alignment,
            ..
        } = symbol.kind
        else {
            unreachable!()
        };
        let name = symbol.name;
        let qt = symbol.type_info;

        // 1. Handle VLA type
        if let Some((size_expr, element_type)) = self.get_vla_info(qt.ty()) {
            self.visit_vla_local(sym, name, size_expr, element_type, alignment);
            return;
        }

        // 2. Handle highly aligned locals (fallback to heap to ensure alignment)
        if let Some(align) = alignment
            && align > 16
        {
            self.visit_aligned_local(sym, name, mir_type_id, qt, init, align);
            return;
        }

        // 3. Standard local variable
        let local_id = self.create_local(Some(name), mir_type_id, false);
        if let Some(align) = alignment {
            self.set_local_alignment(local_id, align);
        }

        self.func_state_mut().local_map.insert(sym, local_id);

        if let Some(initializer) = init {
            let init_operand = self.visit_init(initializer, qt, Some(Place::Local(local_id)));
            self.emit_assignment(Place::Local(local_id), init_operand);
        }
    }

    fn visit_aligned_local(
        &mut self,
        sym: SymbolRef,
        name: NameId,
        mir_type_id: TypeId,
        qt: QualType,
        init: Option<NodeRef>,
        alignment: u16,
    ) {
        let mir_type = self.mb.get_type(mir_type_id);
        let size = self.get_type_size(mir_type);
        let size_op = self.create_size_t_operand(size as u64);
        let ptr_local_id = self.emit_heap_alloc(Some(name), mir_type_id, Some(alignment), size_op);

        // We need a dummy size local for the vla_map entry, although it won't be used for sizeof.
        let size_t_ty = self.get_size_t_type();
        let dummy_size_local = self.create_local(None, size_t_ty, false);
        self.func_state_mut()
            .vla_map
            .insert(sym, (ptr_local_id, dummy_size_local));

        // Initialize if needed
        if let Some(initializer) = init {
            let deref_place = Place::Deref(Box::new(Operand::Copy(Box::new(Place::Local(ptr_local_id)))));
            let init_operand = self.visit_init(initializer, qt, Some(deref_place.clone()));
            self.emit_assignment(deref_place, init_operand);
        }
    }

    /// Extract VLA info from a type: returns (size_expression_node, element_type) if VLA.
    fn get_vla_info(&self, ty: TypeRef) -> Option<(NodeRef, TypeRef)> {
        let type_info = self.registry.get(ty);
        if let TypeKind::Array {
            element_type,
            size: ArraySizeType::Variable(size_expr),
        } = &type_info.kind
        {
            Some((*size_expr, *element_type))
        } else {
            None
        }
    }
    /// Handle VLA local variable declaration.
    /// Creates a pointer-typed local for the data and a size_t local for sizeof.
    /// Emits runtime allocation using posix_memalign/malloc.
    fn visit_vla_local(
        &mut self,
        sym: SymbolRef,
        name: NameId,
        size_expr: NodeRef,
        element_type: TypeRef,
        alignment: Option<u16>,
    ) {
        let size_t_ty = self.get_size_t_type();

        // 1. Get count and element size (dynamically, as the element type might itself be a VLA)
        let count_op = self.visit_expression(size_expr, true);
        let count_op = self.apply_conversions(count_op, size_expr, size_t_ty);
        let count_op = if self.get_operand_type(&count_op) != size_t_ty {
            Operand::Cast(size_t_ty, Box::new(count_op))
        } else {
            count_op
        };

        let elem_size_op = self.visit_type_query(element_type, true);
        let elem_mir_ty = self.lower_type(element_type);

        // 2. Compute total byte size: total_size = count * element_size
        let total_size_op = self.emit_rvalue_to_operand(
            Rvalue::BinaryIntOp(crate::mir::BinaryIntOp::Mul, count_op, elem_size_op),
            size_t_ty,
        );

        // 3. Allocate and map locals
        let size_local_id = self.create_local(None, size_t_ty, false);
        self.emit_assignment(Place::Local(size_local_id), total_size_op.clone());

        let ptr_local_id = self.emit_heap_alloc(Some(name), elem_mir_ty, alignment, total_size_op);

        let func_state = self.func_state_mut();
        func_state.local_map.insert(sym, ptr_local_id);
        func_state.vla_map.insert(sym, (ptr_local_id, size_local_id));
    }

    /// Helper to emit heap allocation for a local (VLA or highly-aligned).
    /// Returns the LocalId of the pointer.
    fn emit_heap_alloc(
        &mut self,
        name: Option<NameId>,
        mir_type_id: TypeId,
        alignment: Option<u16>,
        size_operand: Operand,
    ) -> LocalId {
        let ptr_mir_ty = self.mb.add_type(MirType::Pointer { pointee: mir_type_id });

        // Create pointer local (holds the allocated memory address)
        let ptr_local_id = self.create_local(name, ptr_mir_ty, false);
        if let Some(align) = alignment {
            self.set_local_alignment(ptr_local_id, align);
        }

        // Allocate memory: use posix_memalign if alignment is specified and > 8, otherwise malloc.
        if let Some(align) = alignment
            && align > 8
        {
            self.emit_posix_memalign_call(ptr_local_id, align, size_operand);
        } else {
            self.emit_malloc_call(ptr_local_id, size_operand);
        }

        // Register for cleanup at end of current scope
        if let Some(current_scope_cleanup) = self.func_state_mut().scope_cleanup.last_mut() {
            current_scope_cleanup.push(ptr_local_id);
        }

        ptr_local_id
    }

    /// Emit a malloc call and store the result in the given local.
    pub(super) fn emit_malloc_call(&mut self, dest_local: LocalId, size_operand: Operand) {
        // Declare malloc as an extern function if not already declared
        let malloc_name = NameId::new("malloc");
        let size_t_ty = self.get_size_t_type();
        let void_ty = self.mb.add_type(MirType::Void);
        let ptr_ty = self.mb.add_type(MirType::Pointer { pointee: void_ty });

        // Find or create the malloc function declaration
        let malloc_func_id = self.find_or_declare_extern_function(malloc_name, vec![size_t_ty], ptr_ty, false);

        // Call malloc(size) and store result in dest_local
        self.add_stmt(MirStmt::Call {
            target: CallTarget::Direct(malloc_func_id),
            args: vec![size_operand],
            dest: Some(Place::Local(dest_local)),
        });
    }

    /// Emit a posix_memalign call and store the result in the given local.
    fn emit_posix_memalign_call(&mut self, dest_local: LocalId, alignment: u16, size_operand: Operand) {
        let name = NameId::new("posix_memalign");
        let size_t_ty = self.get_size_t_type();
        let void_ty = self.mb.add_type(MirType::Void);
        let ptr_ty = self.mb.add_type(MirType::Pointer { pointee: void_ty });
        let ptr_ptr_ty = self.mb.add_type(MirType::Pointer { pointee: ptr_ty });
        let int_ty = self.get_int_type();

        // Declare int posix_memalign(void **memptr, size_t alignment, size_t size);
        let func_id = self.find_or_declare_extern_function(name, vec![ptr_ptr_ty, size_t_ty, size_t_ty], int_ty, false);

        let align_operand = self.create_size_t_operand(alignment as u64);
        let dest_addr = Operand::AddressOf(Box::new(Place::Local(dest_local)));
        let dest_addr_casted = Operand::Cast(ptr_ptr_ty, Box::new(dest_addr));

        // Call posix_memalign(&dest_local, alignment, size)
        self.add_stmt(MirStmt::Call {
            target: CallTarget::Direct(func_id),
            args: vec![dest_addr_casted, align_operand, size_operand],
            dest: None, // Ignore return value (should ideally check for ENOMEM/EINVAL)
        });
    }

    /// Emit a free call for the given pointer operand.
    fn emit_free_call(&mut self, ptr_operand: Operand) {
        let name = NameId::new("free");
        let void_ty = self.mb.add_type(MirType::Void);
        let ptr_ty = self.mb.add_type(MirType::Pointer { pointee: void_ty });

        // Declare void free(void *ptr);
        let func_id = self.find_or_declare_extern_function(name, vec![ptr_ty], void_ty, false);

        // MIR requires strict type matching for call arguments.
        let ptr_casted = if self.get_operand_type(&ptr_operand) != ptr_ty {
            Operand::Cast(ptr_ty, Box::new(ptr_operand))
        } else {
            ptr_operand
        };

        // Call free(ptr)
        self.add_stmt(MirStmt::Call {
            target: CallTarget::Direct(func_id),
            args: vec![ptr_casted],
            dest: None,
        });
    }

    /// Find or declare an external function by name.
    pub(super) fn find_or_declare_extern_function(
        &mut self,
        name: NameId,
        param_types: Vec<TypeId>,
        return_type: TypeId,
        is_variadic: bool,
    ) -> MirFunctionId {
        // Check if already declared
        for (i, func) in self.mb.get_functions().iter().enumerate() {
            if func.name == name {
                return MirFunctionId::new((i + 1) as u32).unwrap();
            }
        }
        // Declare it
        self.mb.declare_function(name, param_types, return_type, is_variadic)
    }

    fn visit_return_stmt(&mut self, expr: &Option<NodeRef>) {
        let operand = expr.map(|expr| self.visit_expression(expr, true));
        self.set_terminator(Terminator::Return(operand));
    }

    fn visit_if_stmt(&mut self, if_stmt: &IfStmt) {
        let then_block = self.create_block();
        let else_block = self.create_block();
        let merge_block = self.create_block();

        let mut cond_op = self.visit_expression(if_stmt.condition, true);
        let bool_ty = self.lower_type(self.registry.type_bool);
        if self.get_operand_type(&cond_op) != bool_ty {
            cond_op = self.emit_cast(cond_op, bool_ty);
        }

        self.set_terminator(Terminator::If(cond_op, then_block, else_block));

        self.set_current_block(then_block);
        self.visit_node(if_stmt.then_branch);
        if !self.current_block_has_terminator() {
            self.set_terminator(Terminator::Goto(merge_block));
        }

        self.set_current_block(else_block);
        if let Some(else_branch) = &if_stmt.else_branch {
            self.visit_node(*else_branch);
        }
        if !self.current_block_has_terminator() {
            self.set_terminator(Terminator::Goto(merge_block));
        }

        self.set_current_block(merge_block);
    }

    fn emit_loop_generic<I, C, B, Inc>(
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
        let cond_block = self.create_block();
        let body_block = self.create_block();
        let increment_block = if inc_fn.is_some() {
            self.create_block()
        } else {
            // If there's no increment block (e.g. while/do-while), "continue" goes to condition
            cond_block
        };
        let exit_block = self.create_block();

        // Continue target depends on whether we have an increment step
        let continue_target = increment_block;

        self.with_loop_targets(exit_block, continue_target, |this| {
            if let Some(init) = init_fn {
                init(this);
            }

            if is_do_while {
                // do-while: jump straight to body
                this.set_terminator(Terminator::Goto(body_block));
            } else {
                // for/while: jump to condition
                this.set_terminator(Terminator::Goto(cond_block));
            }

            // Condition block
            this.set_current_block(cond_block);
            if let Some(cond) = cond_fn {
                let cond_val = cond(this);
                this.set_terminator(Terminator::If(cond_val, body_block, exit_block));
            } else {
                // No condition (e.g. for(;;)) -> infinite loop
                this.set_terminator(Terminator::Goto(body_block));
            }

            // Body block
            this.set_current_block(body_block);
            body_fn(this);

            // After body, jump to increment (or condition if no increment)
            if !this.current_block_has_terminator() {
                this.set_terminator(Terminator::Goto(increment_block));
            }

            // Increment block (only if it exists and is distinct from cond_block)
            if let Some(inc) = inc_fn {
                this.set_current_block(increment_block);
                inc(this);
                this.set_terminator(Terminator::Goto(cond_block));
            }
        });

        self.set_current_block(exit_block);
    }

    fn visit_while_stmt(&mut self, while_stmt: &WhileStmt) {
        self.emit_loop_generic(
            None::<fn(&mut Self)>,
            Some(|this: &mut Self| {
                let mut op = this.visit_expression(while_stmt.condition, true);
                let bool_ty = this.lower_type(this.registry.type_bool);
                if this.get_operand_type(&op) != bool_ty {
                    op = this.emit_cast(op, bool_ty);
                }
                op
            }),
            |this| this.visit_node(while_stmt.body),
            None::<fn(&mut Self)>,
            false,
        );
    }

    fn visit_do_while_stmt(&mut self, body: NodeRef, condition: NodeRef) {
        self.emit_loop_generic(
            None::<fn(&mut Self)>,
            Some(|this: &mut Self| {
                let mut op = this.visit_expression(condition, true);
                let bool_ty = this.lower_type(this.registry.type_bool);
                if this.get_operand_type(&op) != bool_ty {
                    op = this.emit_cast(op, bool_ty);
                }
                op
            }),
            |this| this.visit_node(body),
            None::<fn(&mut Self)>,
            true,
        );
    }

    fn visit_for_stmt(&mut self, for_stmt: &ForStmt) {
        let init_node = for_stmt.child_start;
        let cond_node = for_stmt.child_start.add_offset(1);
        let inc_node = for_stmt.child_start.add_offset(2);

        let has_init = !matches!(self.ast.get_kind(init_node), NodeKind::Dummy);
        let has_cond = !matches!(self.ast.get_kind(cond_node), NodeKind::Dummy);
        let has_inc = !matches!(self.ast.get_kind(inc_node), NodeKind::Dummy);

        let init_fn = if has_init {
            Some(move |this: &mut Self| this.visit_node(init_node))
        } else {
            None
        };

        let cond_fn = if has_cond {
            Some(move |this: &mut Self| {
                let mut op = this.visit_expression(cond_node, true);
                let bool_ty = this.lower_type(this.registry.type_bool);
                if this.get_operand_type(&op) != bool_ty {
                    op = this.emit_cast(op, bool_ty);
                }
                op
            })
        } else {
            None
        };

        let inc_fn = if has_inc {
            Some(move |this: &mut Self| {
                this.visit_expression(inc_node, false);
            })
        } else {
            None
        };

        self.emit_loop_generic(init_fn, cond_fn, |this| this.visit_node(for_stmt.body), inc_fn, false);
    }

    fn visit_switch_stmt(&mut self, cond: NodeRef, body: NodeRef) {
        let cond_op = self.visit_expression(cond, true);
        let cond_ty_id = self.get_operand_type(&cond_op);

        let merge_block = self.create_block();

        let saved_break = self.func_state_mut().break_target;
        self.func_state_mut().break_target = Some(merge_block);

        // Collect cases
        let cases = self.collect_switch_cases(body);

        // Create blocks for cases
        let mut case_blocks = Vec::new();
        let mut default_block = None;

        for (node, start_val, end_val) in cases {
            let block = self.create_block();
            self.func_state_mut().switch_case_map.insert(node, block);

            if let Some(start) = start_val {
                case_blocks.push((start, end_val, block));
            } else {
                default_block = Some(block);
            }
        }

        // Generate dispatch
        let fallback_block = default_block.unwrap_or(merge_block);
        let bool_type_id = self.lower_type(self.registry.type_bool);

        for (start_id, end_id_opt, target_block) in case_blocks {
            let next_test_block = self.create_block();
            let start_const = self.mb.get_constants().get(start_id.index()).unwrap().clone();

            // Re-create constant with the same type as condition to ensure safe comparison
            let start_op = Operand::Constant(start_id);
            let cast_start_op = if start_const.ty != cond_ty_id {
                Operand::Cast(cond_ty_id, Box::new(start_op))
            } else {
                start_op
            };

            let cmp_op = if let Some(end_id) = end_id_opt {
                // Range check: x >= start && x <= end
                let end_const = self.mb.get_constants().get(end_id.index()).unwrap().clone();
                let end_op = Operand::Constant(end_id);
                let cast_end_op = if end_const.ty != cond_ty_id {
                    Operand::Cast(cond_ty_id, Box::new(end_op))
                } else {
                    end_op
                };

                // GE: x >= start
                let ge_rvalue = Rvalue::BinaryIntOp(BinaryIntOp::Ge, cond_op.clone(), cast_start_op);
                let ge_op = self.emit_rvalue_to_operand(ge_rvalue, bool_type_id);

                // LE: x <= end
                let le_rvalue = Rvalue::BinaryIntOp(BinaryIntOp::Le, cond_op.clone(), cast_end_op);
                let le_op = self.emit_rvalue_to_operand(le_rvalue, bool_type_id);

                // AND: (x >= start) && (x <= end)
                let and_rvalue = Rvalue::BinaryIntOp(BinaryIntOp::BitAnd, ge_op, le_op);
                self.emit_rvalue_to_operand(and_rvalue, bool_type_id)
            } else {
                // Single value check: x == val
                let eq_rvalue = Rvalue::BinaryIntOp(BinaryIntOp::Eq, cond_op.clone(), cast_start_op);
                self.emit_rvalue_to_operand(eq_rvalue, bool_type_id)
            };

            self.set_terminator(Terminator::If(cmp_op, target_block, next_test_block));

            self.set_current_block(next_test_block);
        }

        // Final jump to default or merge
        self.set_terminator(Terminator::Goto(fallback_block));

        // Lower body
        // Start a dummy unreachable block for the body entry (to catch unreachable statements)
        let body_entry_dummy = self.create_block();
        // Do not jump to it. It is unreachable.

        self.set_current_block(body_entry_dummy);

        self.visit_node(body);

        // If body falls through, go to merge
        if !self.current_block_has_terminator() {
            // Check if terminator is Unreachable (default) - if so, we can replace it or just leave it?
            // `current_block_has_terminator` returns false if it is Unreachable.
            // But if we are in body_entry_dummy and it's empty, we shouldn't jump to merge.
            // Actually, if execution falls through the body, it should hit merge.
            // But valid C code falling through end of switch goes to next stmt (merge).
            self.set_terminator(Terminator::Goto(merge_block));
        }

        self.func_state_mut().break_target = saved_break;
        self.set_current_block(merge_block);
    }

    fn visit_case_default_stmt(&mut self, node: NodeRef, stmt: NodeRef) {
        let target_block = *self
            .func_state_mut()
            .switch_case_map
            .get(&node)
            .expect("Case/Default not mapped");

        // Fallthrough from previous block
        if !self.current_block_has_terminator() {
            self.set_terminator(Terminator::Goto(target_block));
        }

        self.set_current_block(target_block);
        self.visit_node(stmt);
    }

    fn collect_switch_cases(&mut self, node: NodeRef) -> Vec<(NodeRef, Option<ConstValueId>, Option<ConstValueId>)> {
        let mut cases = Vec::new();
        self.collect_switch_cases_recursive(node, &mut cases);
        cases
    }

    fn collect_switch_cases_recursive(
        &mut self,
        node: NodeRef,
        cases: &mut Vec<(NodeRef, Option<ConstValueId>, Option<ConstValueId>)>,
    ) {
        let kind = *self.ast.get_kind(node);
        match kind {
            NodeKind::Case(expr, stmt) => {
                let op = self.visit_expression(expr, true);
                let val = self.operand_to_const_id_strict(op, "Case label must be constant");
                cases.push((node, Some(val), None));
                self.collect_switch_cases_recursive(stmt, cases);
            }
            NodeKind::CaseRange(start, end, stmt) => {
                let start_op = self.visit_expression(start, true);
                let start_val = self.operand_to_const_id_strict(start_op, "Case range start must be constant");

                let end_op = self.visit_expression(end, true);
                let end_val = self.operand_to_const_id_strict(end_op, "Case range end must be constant");

                cases.push((node, Some(start_val), Some(end_val)));
                self.collect_switch_cases_recursive(stmt, cases);
            }
            NodeKind::Default(stmt) => {
                cases.push((node, None, None));
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

    pub(super) fn emit_assignment(&mut self, place: Place, operand: Operand) {
        if self.current_block_has_terminator() {
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
        self.add_stmt(stmt);
    }

    pub(super) fn lower_qual_type(&mut self, qt: QualType) -> TypeId {
        self.lower_type(qt.ty())
    }

    pub(super) fn lower_type(&mut self, ty: TypeRef) -> TypeId {
        if let Some(type_id) = self.type_cache.get(&ty) {
            return *type_id;
        }

        let _ = self.registry.ensure_layout(ty);

        // Return placeholder if already converting this type (recursion loop)
        if self.type_conversion_in_progress.contains(&ty) {
            return *self
                .type_cache
                .get(&ty)
                .expect("Placeholder must exist for recursive type");
        }

        // Bolt ⚡: Avoid cloning the entire TypeKind.
        // We use matching on a reference and scoped extraction where needed.
        enum Task {
            Record(Option<NameId>, bool, bool),
            Builtin(BuiltinType),
            Pointer(QualType),
            Array(TypeRef, ArraySizeType),
            Function(TypeRef, Vec<FunctionParameter>, bool),
            Complex(TypeRef),
            Default,
        }

        let task = {
            let type_info = self.registry.get(ty);
            match &type_info.kind {
                TypeKind::Record {
                    tag,
                    is_union,
                    is_complete,
                    ..
                } => Task::Record(*tag, *is_union, *is_complete),
                TypeKind::Builtin(b) => Task::Builtin(*b),
                TypeKind::Pointer { pointee } => Task::Pointer(*pointee),
                TypeKind::Array { element_type, size } => Task::Array(*element_type, *size),
                TypeKind::Function {
                    return_type,
                    parameters,
                    is_variadic,
                    ..
                } => Task::Function(*return_type, parameters.to_vec(), *is_variadic),
                TypeKind::Complex { base_type } => Task::Complex(*base_type),
                _ => Task::Default,
            }
        };

        match task {
            Task::Record(tag, is_union, is_complete) => {
                self.lower_recursive_record_pattern(ty, tag, is_union, is_complete)
            }
            Task::Builtin(b) => {
                let mir_type = if matches!(b, BuiltinType::VaList) {
                    self.lower_valist_type()
                } else {
                    self.lower_builtin_type(&b)
                };
                self.cache_type(ty, mir_type)
            }
            Task::Pointer(pointee) => {
                let mir_type = self.lower_pointer_type(pointee);
                self.cache_type(ty, mir_type)
            }
            Task::Array(element_type, size) => {
                let mir_type = self.lower_array_type(ty, element_type, &size);
                self.cache_type(ty, mir_type)
            }
            Task::Function(return_type, parameters, is_variadic) => {
                let mir_type = self.lower_function_type(return_type, &parameters, is_variadic);
                self.cache_type(ty, mir_type)
            }
            Task::Complex(base_type) => {
                let mir_type = self.lower_complex_type(base_type);
                self.cache_type(ty, mir_type)
            }
            _ => {
                let mir_type = MirType::I32;
                self.cache_type(ty, mir_type)
            }
        }
    }

    fn lower_recursive_record_pattern(
        &mut self,
        ty: TypeRef,
        tag: Option<NameId>,
        is_union: bool,
        is_complete: bool,
    ) -> TypeId {
        // Begin conversion: reserve a placeholder TypeId so recursive references can point to it.
        self.type_conversion_in_progress.insert(ty);
        let placeholder_name = NameId::new(format!("__recursive_placeholder_{}", ty.get()));
        let placeholder_type = MirType::Record {
            name: placeholder_name,
            field_types: Vec::new(),
            field_names: Vec::new(),
            is_union: false,
            layout: MirRecordLayout {
                size: 0,
                align: 0,
                fields: Vec::new(),
            },
        };
        let placeholder_id = self.mb.add_type(placeholder_type);
        self.type_cache.insert(ty, placeholder_id);

        let mir_type = self.lower_record_type(ty, &tag, is_union, is_complete);

        // Remove from in-progress set
        self.type_conversion_in_progress.remove(&ty);

        // Replace the placeholder entry with the real type
        self.mb.update_type(placeholder_id, mir_type);
        placeholder_id
    }

    fn cache_type(&mut self, ty: TypeRef, mir_type: MirType) -> TypeId {
        let type_id = self.mb.add_type(mir_type);
        self.type_cache.insert(ty, type_id);
        type_id
    }

    fn lower_valist_type(&mut self) -> MirType {
        let u32_id = self.lower_type(self.registry.type_int_unsigned);
        let u64_id = self.lower_type(self.registry.type_long_long_unsigned);

        let record_layout = MirRecordLayout {
            size: 24,
            align: 8,
            fields: vec![
                MirFieldLayout::new(0),
                MirFieldLayout::new(4),
                MirFieldLayout::new(8),
                MirFieldLayout::new(16),
            ],
        };

        // Cache the __va_list_tag record type to ensure canonical type usage
        let record_id = if let Some(id) = self.valist_mir_id {
            id
        } else {
            let record_type = MirType::Record {
                name: NameId::new("__va_list_tag"),
                field_types: vec![u32_id, u32_id, u64_id, u64_id],
                field_names: vec![
                    NameId::new("gp_offset"),
                    NameId::new("fp_offset"),
                    NameId::new("overflow_arg_area"),
                    NameId::new("reg_save_area"),
                ],
                is_union: false,
                layout: record_layout,
            };
            let id = self.mb.add_type(record_type);
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
            BuiltinType::LongDouble => {
                if self.registry.target_triple.architecture == Architecture::X86_64 {
                    MirType::F80
                } else {
                    MirType::F128
                }
            }
            BuiltinType::Signed => MirType::I32,
            BuiltinType::VaList => MirType::U64,   // Opaque handle
            BuiltinType::Complex => MirType::Void, // Should not happen in MIR
        }
    }

    fn lower_pointer_type(&mut self, pointee: QualType) -> MirType {
        MirType::Pointer {
            pointee: self.lower_qual_type(pointee),
        }
    }

    fn lower_array_type(&mut self, ty: TypeRef, element_type: TypeRef, size: &ArraySizeType) -> MirType {
        let element = self.lower_type(element_type);

        match size {
            ArraySizeType::Constant(s) if !self.registry.is_vla_type(ty) => {
                let _ = self.registry.ensure_layout(ty);
                let (layout_size, layout_align, element_ty, _) = self.registry.get_array_layout(ty);
                let element_layout = self.registry.get_layout(element_ty);

                MirType::Array {
                    element,
                    size: *s,
                    layout: MirArrayLayout {
                        size: layout_size,
                        align: layout_align as u16,
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
        return_type: TypeRef,
        parameters: &[FunctionParameter],
        is_variadic: bool,
    ) -> MirType {
        let return_type = self.lower_type(return_type);
        let mut params = Vec::new();
        for p in parameters {
            let param_ty_id = self.lower_qual_type(p.param_type);
            // Adjust array parameters to pointers (C standard).
            // This is especially important for VaList which treats itself as an array but is passed as a pointer.
            // Sema handles explicit arrays, but BuiltinType::VaList is lowered to Array here.
            let param_ty = self.mb.get_type(param_ty_id);
            let adjusted_ty_id = if let MirType::Array { element, .. } = param_ty {
                self.mb.add_type(MirType::Pointer { pointee: *element })
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

    fn lower_complex_type(&mut self, base_type: TypeRef) -> MirType {
        let element_id = self.lower_type(base_type);
        let element_layout = self
            .registry
            .ensure_layout(base_type)
            .expect("Layout computation failed");
        let element_size = element_layout.size;
        let element_align = element_layout.alignment;

        let name = NameId::new(format!("_Complex_{}", self.registry.display_type(base_type)));

        MirType::Record {
            name,
            field_types: vec![element_id, element_id],
            field_names: vec![NameId::new("real"), NameId::new("imag")],
            is_union: false,
            layout: MirRecordLayout {
                size: element_size * 2,
                align: element_align,
                fields: vec![
                    MirFieldLayout::new(0).signed(true),
                    MirFieldLayout::new(element_size).signed(true),
                ],
            },
        }
    }

    fn lower_record_type(&mut self, ty: TypeRef, tag: &Option<NameId>, is_union: bool, is_complete: bool) -> MirType {
        let name = tag.unwrap_or_else(|| {
            self.ast
                .semantic_info
                .anonymous_tags
                .get(&ty)
                .copied()
                .unwrap_or_else(|| NameId::new("anonymous"))
        });

        let (size, alignment, field_layouts, field_names, field_types) = if is_complete {
            let mut flat_members = Vec::new();
            let mut flat_fields = Vec::new();
            let ty = self.registry.get(ty).into_owned();
            ty.flatten_members_with_layouts(self.registry, &mut flat_members, &mut flat_fields, 0);

            let mut field_names = Vec::new();
            let mut field_types = Vec::new();
            let mut field_layouts = Vec::new();

            for (idx, m) in flat_members.iter().enumerate() {
                let name = m.name.unwrap_or_else(|| NameId::new(format!("__anon_{}", idx)));
                field_names.push(name);
                field_types.push(self.lower_qual_type(m.member_type));

                let fl = &flat_fields[idx];
                field_layouts.push(MirFieldLayout::from(fl).signed(self.registry.get(m.member_type.ty()).is_signed()));
            }
            let layout = ty.layout.as_ref().unwrap();
            (layout.size, layout.alignment, field_layouts, field_names, field_types)
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
                align: alignment,
                fields: field_layouts,
            },
        }
    }

    pub(crate) fn create_constant(&mut self, ty: TypeId, kind: ConstValueKind) -> ConstValueId {
        self.mb.create_constant(ty, kind)
    }

    pub(super) fn create_int_operand(&mut self, val: i64) -> Operand {
        let ty_id = self.get_int_type();
        Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(val)))
    }

    pub(super) fn create_float_operand(&mut self, val: f64, ty_id: TypeId) -> Operand {
        Operand::Constant(self.create_constant(ty_id, ConstValueKind::Float(val)))
    }

    pub(super) fn create_size_t_operand(&mut self, val: u64) -> Operand {
        let ty_id = self.get_size_t_type();
        Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(val as i64)))
    }

    pub(super) fn get_size_t_type(&mut self) -> TypeId {
        self.lower_type(self.registry.type_long_unsigned)
    }

    fn emit_conversion(
        &mut self,
        operand: Operand,
        conv: &Conversion,
        target_type_id: TypeId,
        node: NodeRef,
    ) -> Operand {
        let to_ty = match conv {
            Conversion::IntegerCast { to, .. }
            | Conversion::FloatingCast { to, .. }
            | Conversion::ComplexCast { to, .. }
            | Conversion::IntegerPromotion { to, .. }
            | Conversion::PointerCast { to, .. } => Some(*to),
            Conversion::PointerDecay { to } => Some(*to),
            _ => None,
        };

        let from_ty = match conv {
            Conversion::IntegerCast { from, .. }
            | Conversion::FloatingCast { from, .. }
            | Conversion::ComplexCast { from, .. }
            | Conversion::IntegerPromotion { from, .. }
            | Conversion::PointerCast { from, .. } => Some(*from),
            _ => None,
        };

        if let Some(to) = to_ty
            && (to.is_complex() || from_ty.is_some_and(|f| f.is_complex()))
        {
            return self.emit_complex_conversion(operand, from_ty, to);
        }

        let to_mir_type = match conv {
            Conversion::IntegerCast { to, .. }
            | Conversion::FloatingCast { to, .. }
            | Conversion::ComplexCast { to, .. }
            | Conversion::IntegerPromotion { to, .. }
            | Conversion::PointerCast { to, .. } => self.lower_type(*to),
            Conversion::NullPointerConstant => {
                // Null pointer constant usually converts to void* first.
                // However, we can use target_type_id if it's already a pointer.
                let void_ptr_mir = self.lower_type(self.registry.type_void_ptr);
                if self.mb.get_type(target_type_id).is_pointer() {
                    target_type_id
                } else {
                    void_ptr_mir
                }
            }
            Conversion::PointerDecay { to } => self.lower_type(*to),
            Conversion::LValueToRValue | Conversion::QualifierAdjust { .. } => {
                let qt = self.ast.qual_type_of(node);
                self.lower_qual_type(qt.strip_all())
            }
        };

        if matches!(conv, Conversion::LValueToRValue) {
            let qt = self.ast.qual_type_of(node);
            if qt.is_atomic() {
                // Perform atomic load
                let ptr_operand = match operand {
                    Operand::Copy(ref p) => Operand::AddressOf(p.clone()),
                    _ => operand.clone(),
                };
                let rval = Rvalue::AtomicLoad(ptr_operand, AtomicMemOrder::SeqCst);
                return self.emit_rvalue_to_operand(rval, target_type_id);
            }
        }

        // Optimization: skip if already same type
        let current_mty = self.get_operand_type(&operand);
        if current_mty == to_mir_type {
            return operand;
        }

        match conv {
            Conversion::IntegerCast { .. }
            | Conversion::IntegerPromotion { .. }
            | Conversion::PointerCast { .. }
            | Conversion::FloatingCast { .. } => {
                // Fold constant casts if types are compatible
                if let Some(const_id) = self.operand_to_const_id(&operand) {
                    let const_val = self.mb.get_constants()[const_id.index()].clone();
                    let mir_type = self.mb.get_type(to_mir_type);

                    let is_compatible = match (&const_val.kind, mir_type) {
                        (ConstValueKind::Int(_), t) => t.is_int() || t.is_pointer(),
                        (ConstValueKind::Float(_), t) => t.is_float(),
                        (ConstValueKind::GlobalAddress(_, _), t) => t.is_pointer() || t.is_int(),
                        (ConstValueKind::FunctionAddress(_), t) => t.is_pointer() || t.is_int(),
                        _ => false,
                    };

                    if is_compatible {
                        let truncated_kind = match const_val.kind {
                            ConstValueKind::Int(val) => {
                                // C11 6.3.1.2-3: When converting to _Bool, the result is 0 if the value is 0, otherwise 1
                                if matches!(mir_type, MirType::Bool) {
                                    ConstValueKind::Int(if val != 0 { 1 } else { 0 })
                                } else {
                                    ConstValueKind::Int(mir_type.truncate_int(val))
                                }
                            }
                            kind => kind,
                        };
                        Operand::Constant(self.create_constant(to_mir_type, truncated_kind))
                    } else {
                        Operand::Cast(to_mir_type, Box::new(operand))
                    }
                } else {
                    Operand::Cast(to_mir_type, Box::new(operand))
                }
            }
            Conversion::ComplexCast { from, to } => self.emit_complex_conversion(operand, Some(*from), *to),
            Conversion::NullPointerConstant => {
                let ty_id = self.lower_type(self.registry.type_int);
                Operand::Cast(
                    to_mir_type,
                    Box::new(Operand::Constant(self.create_constant(ty_id, ConstValueKind::Int(0)))),
                )
            }
            Conversion::PointerDecay { .. } => {
                if let Operand::Copy(place) = &operand {
                    let addr_of_array = Operand::AddressOf(place.clone());
                    Operand::Cast(to_mir_type, Box::new(addr_of_array))
                } else {
                    // If it's not a place (e.g. String Literal might be lowered to Constant directly?)
                    // String literals usually LValue, so Copy(Place::Global/Local).
                    Operand::Cast(to_mir_type, Box::new(operand))
                }
            }
            _ => {
                let target_mty = self.mb.get_type(target_type_id);
                if target_mty.is_void() || matches!(target_mty, MirType::Array { .. } | MirType::Record { .. }) {
                    operand
                } else {
                    Operand::Cast(target_type_id, Box::new(operand))
                }
            }
        }
    }

    pub(super) fn get_operand_type(&mut self, operand: &Operand) -> TypeId {
        match operand {
            Operand::Copy(place) => self.get_place_type(place),
            Operand::Constant(const_id) => {
                let const_val = self.mb.get_constant(*const_id);
                const_val.ty
            }
            Operand::AddressOf(place) => {
                let pointee = self.get_place_type(place);
                self.mb.add_type(MirType::Pointer { pointee })
            }
            Operand::Cast(ty, _) => *ty,
        }
    }

    pub(super) fn get_place_type(&mut self, place: &Place) -> TypeId {
        match place {
            Place::Local(local_id) => self.mb.get_local(*local_id).type_id,
            Place::Global(global_id) => self.get_global_type(*global_id),
            Place::Deref(operand) => {
                let ptr_ty = self.get_operand_type(operand);
                match self.mb.get_type(ptr_ty) {
                    MirType::Pointer { pointee } => *pointee,
                    _ => panic!("Deref of non-pointer type"),
                }
            }
            Place::StructField(base, field_idx, _) => {
                let struct_ty = self.get_place_type(base);
                match self.mb.get_type(struct_ty) {
                    MirType::Record { field_types, .. } => field_types[*field_idx],
                    _ => panic!("StructField access on non-struct type"),
                }
            }
            Place::ArrayIndex(base, _) => {
                let base_ty = self.get_place_type(base);
                match self.mb.get_type(base_ty) {
                    MirType::Array { element, .. } => *element,
                    MirType::Pointer { pointee, .. } => *pointee,
                    _ => panic!("ArrayIndex access on non-array, non-pointer type"),
                }
            }
        }
    }

    fn get_type_size(&self, mir_type: &MirType) -> u32 {
        match mir_type {
            MirType::I8 | MirType::U8 => 1,
            MirType::I16 | MirType::U16 => 2,
            MirType::I32 | MirType::U32 => 4,
            MirType::I64 | MirType::U64 => 8,
            MirType::F32 => 4,
            MirType::F64 => 8,
            MirType::F80 | MirType::F128 => 16,
            MirType::Pointer { .. } => 8, // Assuming 64-bit pointers
            MirType::Array { layout, .. } => layout.size as u32,
            MirType::Record { layout, .. } => layout.size as u32,
            MirType::Bool => 1,
            MirType::Void => 0,
            _ => 4,
        }
    }

    fn place_to_global_offset(&mut self, place: &Place) -> Option<(GlobalId, i64)> {
        match place {
            Place::Global(id) => Some((*id, 0)),
            Place::StructField(base, field_index, _) => {
                let (base_id, base_offset) = self.place_to_global_offset(base)?;
                let base_ty = self.get_place_type(base);
                let mir_type = self.mb.get_type(base_ty);
                match mir_type {
                    MirType::Record { layout, .. } => {
                        let field_offset = layout.fields[*field_index].offset as i64;
                        Some((base_id, base_offset + field_offset))
                    }
                    _ => None,
                }
            }
            Place::ArrayIndex(base, index_operand) => {
                let (base_id, base_offset) = self.place_to_global_offset(base)?;
                let element_size = {
                    let base_ty = self.get_place_type(base);
                    let mir_type = self.mb.get_type(base_ty);
                    match mir_type {
                        MirType::Array { layout, .. } => layout.stride as i64,
                        MirType::Pointer { pointee, .. } => {
                            let pointee_type = self.mb.get_type(*pointee);
                            self.get_type_size(pointee_type) as i64
                        }
                        _ => return None,
                    }
                };

                let index_val = match &**index_operand {
                    Operand::Constant(const_id) => {
                        let const_val = self.mb.get_constant(*const_id);
                        match const_val.kind {
                            ConstValueKind::Int(v) => v,
                            _ => return None,
                        }
                    }
                    _ => return None,
                };

                Some((base_id, base_offset + element_size * index_val))
            }
            Place::Deref(_) | Place::Local(_) => None,
        }
    }

    fn get_global_type(&self, global_id: GlobalId) -> TypeId {
        self.mb.get_global(global_id).type_id
    }

    pub(super) fn get_function_type(&mut self, func_id: MirFunctionId) -> TypeId {
        let func = self.mb.get_function(func_id);
        let ret_ty = func.return_type;
        let mut param_types = Vec::new();
        for &param_id in &func.params {
            param_types.push(self.mb.get_local(param_id).type_id);
        }
        self.mb.add_type(MirType::Function {
            return_type: ret_ty,
            params: param_types,
            is_variadic: func.is_variadic,
        })
    }

    pub(super) fn apply_conversions(&mut self, operand: Operand, node: NodeRef, target: TypeId) -> Operand {
        // Look up conversions for this node in semantic_info
        let semantic_info = &self.ast.semantic_info;
        let idx = node.index();
        if idx < semantic_info.conversions.len() {
            let mut result = operand;
            for conv in &semantic_info.conversions[idx] {
                result = self.emit_conversion(result, conv, target, node);
            }
            return result;
        }
        operand
    }

    pub(super) fn get_int_type(&mut self) -> TypeId {
        self.lower_type(self.registry.type_int)
    }

    fn emit_complex_conversion(&mut self, operand: Operand, from_ty: Option<TypeRef>, to_ty: TypeRef) -> Operand {
        let to_mir_ty = self.lower_type(to_ty);
        let from_mir_ty = self.get_operand_type(&operand);

        if to_ty.is_complex() {
            let to_element_ty = match &self.registry.get(to_ty).kind {
                TypeKind::Complex { base_type } => *base_type,
                _ => unreachable!(),
            };
            let to_element_mir_ty = self.lower_type(to_element_ty);

            if from_ty.is_some_and(|f| f.is_complex()) {
                // Complex to Complex
                let (real, imag) = self.get_complex_components(operand, from_mir_ty);

                let res_real = self.emit_cast(real, to_element_mir_ty);
                let res_imag = self.emit_cast(imag, to_element_mir_ty);

                self.emit_complex_struct(res_real, res_imag, to_mir_ty)
            } else {
                // Real to Complex
                let res_real = self.emit_cast(operand, to_element_mir_ty);
                let zero_const = self.create_constant(to_element_mir_ty, ConstValueKind::Float(0.0));
                let res_imag =
                    self.emit_rvalue_to_operand(Rvalue::Use(Operand::Constant(zero_const)), to_element_mir_ty);

                self.emit_complex_struct(res_real, res_imag, to_mir_ty)
            }
        } else {
            // Complex to Real
            let (real, _) = self.get_complex_components(operand, from_mir_ty);
            self.emit_cast(real, to_mir_ty)
        }
    }

    pub(super) fn create_temp_local(&mut self, type_id: TypeId) -> (LocalId, Place) {
        let local_id = self.create_local(None, type_id, false);
        let place = Place::Local(local_id);
        (local_id, place)
    }

    pub(super) fn deref_operand(&self, operand: Operand) -> Place {
        Place::Deref(Box::new(operand))
    }

    pub(super) fn create_temp_local_with_assignment(&mut self, rvalue: Rvalue, type_id: TypeId) -> (LocalId, Place) {
        let (local_id, place) = self.create_temp_local(type_id);
        let assign_stmt = MirStmt::Assign(place.clone(), rvalue);
        self.add_stmt(assign_stmt);
        (local_id, place)
    }

    pub(super) fn ensure_place(&mut self, operand: Operand, type_id: TypeId) -> Place {
        if let Operand::Copy(place) = operand {
            *place
        } else {
            if self.mb.get_type(type_id).is_void() {
                // This shouldn't normally happen if the rest of the lowerer handles void correctly.
                panic!("ICE: Cannot ensure_place for void type");
            }
            let (_, temp_place) = self.create_temp_local_with_assignment(Rvalue::Use(operand), type_id);
            temp_place
        }
    }

    pub(super) fn emit_rvalue_to_operand(&mut self, rvalue: Rvalue, type_id: TypeId) -> Operand {
        if self.mb.get_type(type_id).is_void() {
            // For void expressions, just return a dummy operand.
            // Any side effects in the Rvalue's operands were already emitted.
            return self.create_dummy_operand();
        }

        if let Some(const_id) = self.try_fold_rvalue_to_const(&rvalue, type_id) {
            return Operand::Constant(const_id);
        }

        let (_, place) = self.create_temp_local_with_assignment(rvalue, type_id);
        Operand::Copy(Box::new(place))
    }

    fn try_fold_rvalue_to_const(&mut self, rvalue: &Rvalue, type_id: TypeId) -> Option<ConstValueId> {
        match rvalue {
            Rvalue::Use(op) => self.operand_to_const_id(op),
            Rvalue::StructLiteral(fields) => {
                let mut const_fields = Vec::with_capacity(fields.len());
                for (idx, op) in fields {
                    let const_id = self.operand_to_const_id(op)?;
                    const_fields.push((*idx, const_id));
                }
                Some(self.create_constant(type_id, ConstValueKind::StructLiteral(const_fields)))
            }
            Rvalue::ArrayLiteral(elements) => {
                let mut const_elements = Vec::with_capacity(elements.len());
                for op in elements {
                    let const_id = self.operand_to_const_id(op)?;
                    const_elements.push(const_id);
                }
                Some(self.create_constant(type_id, ConstValueKind::ArrayLiteral(const_elements)))
            }
            _ => None,
        }
    }

    pub(super) fn get_complex_components(&mut self, operand: Operand, ty: TypeId) -> (Operand, Operand) {
        let mir_ty = self.mb.get_type(ty);
        if let MirType::Record { .. } = mir_ty {
            let place = self.ensure_place(operand, ty);
            let real = Operand::Copy(Box::new(Place::StructField(Box::new(place.clone()), 0, None)));
            let imag = Operand::Copy(Box::new(Place::StructField(Box::new(place), 1, None)));
            (real, imag)
        } else {
            // Real to complex components
            let zero = if mir_ty.is_float() {
                ConstValueKind::Float(0.0)
            } else {
                ConstValueKind::Int(0)
            };
            let imag = Operand::Constant(self.create_constant(ty, zero));
            (operand, imag)
        }
    }

    pub(super) fn emit_float_binop(
        &mut self,
        op: crate::mir::BinaryFloatOp,
        lhs: Operand,
        rhs: Operand,
        ty: TypeId,
    ) -> Operand {
        self.emit_rvalue_to_operand(Rvalue::BinaryFloatOp(op, lhs, rhs), ty)
    }

    pub(super) fn emit_float_unop(&mut self, op: crate::mir::UnaryFloatOp, operand: Operand, ty: TypeId) -> Operand {
        self.emit_rvalue_to_operand(Rvalue::UnaryFloatOp(op, operand), ty)
    }

    pub(super) fn emit_complex_struct(&mut self, real: Operand, imag: Operand, ty: TypeId) -> Operand {
        self.emit_rvalue_to_operand(Rvalue::StructLiteral(vec![(0, real), (1, imag)]), ty)
    }

    pub(super) fn operand_to_const_id(&mut self, operand: &Operand) -> Option<ConstValueId> {
        match operand {
            Operand::Constant(id) => Some(*id),
            Operand::Cast(ty, inner) => {
                // Recursively try to get constant from inner operand
                if let Some(inner_const_id) = self.operand_to_const_id(inner) {
                    let inner_const = self.mb.get_constant(inner_const_id).clone();
                    let mir_type = self.mb.get_type(*ty);
                    let truncated_kind = match inner_const.kind {
                        ConstValueKind::Int(val) => {
                            if mir_type.is_float() {
                                ConstValueKind::Float(val as f64)
                            } else {
                                ConstValueKind::Int(mir_type.truncate_int(val))
                            }
                        }
                        ConstValueKind::Float(val) => {
                            if mir_type.is_int() {
                                ConstValueKind::Int(mir_type.truncate_int(val as i64))
                            } else {
                                ConstValueKind::Float(val)
                            }
                        }
                        ConstValueKind::Bool(val) => {
                            if mir_type.is_float() {
                                ConstValueKind::Float(if val { 1.0 } else { 0.0 })
                            } else {
                                ConstValueKind::Int(if val { 1 } else { 0 })
                            }
                        }
                        ConstValueKind::Zero => {
                            if mir_type.is_float() {
                                ConstValueKind::Float(0.0)
                            } else {
                                ConstValueKind::Int(0)
                            }
                        }
                        ConstValueKind::GlobalAddress(_, _) | ConstValueKind::FunctionAddress(_) => {
                            if mir_type.is_int() || mir_type.is_bool() {
                                ConstValueKind::Int(1)
                            } else if mir_type.is_float() {
                                ConstValueKind::Float(1.0)
                            } else {
                                inner_const.kind
                            }
                        }
                        kind => kind,
                    };
                    // Create a new constant with the target type but same kind
                    Some(self.create_constant(*ty, truncated_kind))
                } else {
                    None
                }
            }
            Operand::AddressOf(place) => {
                if let Some((global_id, offset)) = self.place_to_global_offset(place) {
                    let global_type = self.get_global_type(global_id);
                    let ptr_ty = self.mb.add_type(MirType::Pointer { pointee: global_type });
                    Some(self.create_constant(ptr_ty, ConstValueKind::GlobalAddress(global_id, offset)))
                } else {
                    None
                }
            }
            Operand::Copy(place) => {
                if let Some((global_id, offset)) = self.place_to_global_offset(place) {
                    // If it is an array, using it in an expression decays to a pointer (GlobalAddress).
                    // We must check if the *place* itself is an array, not just if the base global is an array.
                    let place_ty_id = self.get_place_type(place);
                    let place_mir_ty = self.mb.get_type(place_ty_id);
                    if matches!(place_mir_ty, MirType::Array { .. }) {
                        let ptr_ty = self.mb.add_type(MirType::Pointer { pointee: place_ty_id });
                        return Some(self.create_constant(ptr_ty, ConstValueKind::GlobalAddress(global_id, offset)));
                    }

                    // If we are copying a global, and it has a constant initializer, return that value.
                    // This handles compound literals which are lowered to globals.
                    // However, if there's an offset and it's not an array decaying, we can't easily extract the sub-value right now.
                    // For now, only return initial_value if offset is 0 and the place is the exact global base.
                    if offset == 0 && matches!(&**place, Place::Global(_)) {
                        let global = self.mb.get_global(global_id);
                        if self.func_state.is_none() || global.is_constant {
                            return global.initial_value;
                        }
                    }

                    None
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
        let old_break = self.func_state_mut().break_target.replace(break_target);
        let old_continue = self.func_state_mut().continue_target.replace(continue_target);

        f(self);

        let state = self.func_state_mut();
        state.break_target = old_break;
        state.continue_target = old_continue;
    }

    fn scan_for_labels(&mut self, node: NodeRef) {
        let node_kind = *self.ast.get_kind(node);
        if let NodeKind::Label(name, _, _) = node_kind
            && !self.func_state_mut().label_map.contains_key(&name)
        {
            let block_id = self.create_block();
            self.func_state_mut().label_map.insert(name, block_id);
        }
        node_kind.visit_children(|child| self.scan_for_labels(child));
    }

    fn visit_goto_stmt(&mut self, label_name: NameId) {
        if let Some(target_block) = self.func_state_mut().label_map.get(&label_name).copied() {
            self.set_terminator(Terminator::Goto(target_block));
        } else {
            // This should be caught by semantic analysis, but we panic as a safeguard
            panic!("Goto to undefined label '{}'", label_name.as_str());
        }
    }

    fn visit_label_stmt(&mut self, label_name: NameId, statement: NodeRef) {
        let label_block = *self
            .func_state_mut()
            .label_map
            .get(&label_name)
            .expect("Label was not pre-scanned");

        // Make sure the current block is terminated before switching (fallthrough)
        if !self.current_block_has_terminator() {
            self.set_terminator(Terminator::Goto(label_block));
        }

        self.set_current_block(label_block);
        self.visit_node(statement);
    }

    fn define_or_declare_function(
        &mut self,
        name: NameId,
        params: Vec<TypeId>,
        ret: TypeId,
        variadic: bool,
        is_def: bool,
        linkage: MirLinkage,
    ) -> MirFunctionId {
        if is_def {
            self.mb.define_function(name, params, ret, variadic, linkage)
        } else {
            self.mb
                .declare_function_with_linkage(name, params, ret, variadic, linkage)
        }
    }

    fn calculate_linkage(&self, storage: Option<StorageClass>, def_state: DefinitionState) -> MirLinkage {
        if def_state == DefinitionState::DeclaredOnly {
            return MirLinkage::Import;
        }
        match storage {
            Some(StorageClass::Static) => MirLinkage::Internal,
            _ => MirLinkage::External,
        }
    }
}
