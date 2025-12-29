use crate::{
    ast::{
        Ast, FunctionData, NodeKind, NodeRef, VarDeclData,
    },
    diagnostic::{DiagnosticEngine},
    mir::{
        self, CallTarget, ConstValue, ConstValueId, GlobalId, MirBuilder,
        MirFunctionId, MirModule, MirType, Operand, Terminator,
        TypeId, MirBlockId, Place as Lvalue,
    },
    semantic::{
        symbol_table::{Namespace, Symbol, SymbolKind, SymbolTable},
        ScopeId, SymbolRef,
    },
};
use std::collections::HashMap;

pub struct AstToMirLowerer<'ast, 'diag> {
    ast: &'ast Ast,
    diag: &'diag mut DiagnosticEngine,
    symbol_table: &'ast mut SymbolTable,
    builder: MirBuilder,
    current_fn: Option<MirFunctionId>,
    break_target: Option<MirBlockId>,
    continue_target: Option<MirBlockId>,
    lvalue_map: HashMap<SymbolRef, Lvalue>,
    constant_map: HashMap<NodeRef, ConstValueId>,
}

impl<'ast, 'diag> AstToMirLowerer<'ast, 'diag> {
    pub fn new(
        ast: &'ast Ast,
        diag: &'diag mut DiagnosticEngine,
        symbol_table: &'ast mut SymbolTable,
    ) -> Self {
        Self {
            ast,
            diag,
            symbol_table,
            builder: MirBuilder::new(crate::mir::MirModuleId::new(1).unwrap()),
            current_fn: None,
            break_target: None,
            continue_target: None,
            lvalue_map: HashMap::new(),
            constant_map: HashMap::new(),
        }
    }

    pub fn lower_module_complete(mut self) -> crate::driver::compiler::SemaOutput {
        let root = self.ast.get_root();
        self.lower_node(root);
        self.builder.finalize_module()
    }

    fn lower_node(&mut self, node_ref: NodeRef) {
        let node = self.ast.get_node(node_ref);
        match &node.kind {
            NodeKind::TranslationUnit(decls) => {
                for decl in decls {
                    self.lower_node(*decl);
                }
            }
            NodeKind::Function(data) => self.lower_function(data),
            NodeKind::VarDecl(data) => self.lower_global_variable(data),
            _ => {}
        }
    }

    fn lower_function(&mut self, data: &FunctionData) {
        let return_type: TypeId = data.ty.into();
        let func_id = self.builder.create_function(
            self.symbol_table.get_symbol(data.symbol).name,
            return_type,
        );
        self.current_fn = Some(func_id);
        let entry_block = self.builder.create_block();
        self.builder.set_function_entry_block(func_id, entry_block);
        self.builder.set_current_block(entry_block);

        for param in &data.params {
            let lvalue = self.builder.create_local(
                Some(self.symbol_table.get_symbol(param.symbol).name),
                param.ty.into(),
                true,
            );
            self.lvalue_map.insert(param.symbol, Lvalue::Local(lvalue));
        }

        self.lower_statement(data.body);

        if !self.builder.current_block_has_terminator() {
            if return_type == self.builder.add_type(MirType::Void) {
                self.builder.set_terminator(Terminator::Return(None));
            }
        }

        self.current_fn = None;
    }

    fn lower_global_variable(&mut self, data: &VarDeclData) {
        let symbol = self
            .symbol_table
            .lookup(data.name, ScopeId::GLOBAL, Namespace::Ordinary);
        let symbol = self.symbol_table.get_symbol(symbol.unwrap().0);

        if let SymbolKind::Variable { is_global, .. } = symbol.kind {
            if is_global {
                let ty: TypeId = data.ty.into();
                let init = data.init.map(|i| self.lower_constant(i));
                self.builder
                    .create_global_with_init(data.name, ty, false, init);
            }
        }
    }

    fn lower_statement(&mut self, node_ref: NodeRef) {
        let node = self.ast.get_node(node_ref);
        match &node.kind {
            NodeKind::CompoundStatement(items) => {
                for item in items {
                    self.lower_statement(*item);
                }
            }
            NodeKind::If(stmt) => {
                let then_block = self.builder.create_block();
                let else_block = self.builder.create_block();
                let merge_block = self.builder.create_block();
                let cond = self.lower_expression(stmt.condition);
                self.builder
                    .set_terminator(Terminator::If(cond, then_block, else_block));
                self.builder.set_current_block(then_block);
                self.lower_statement(stmt.then_branch);
                self.builder.set_terminator(Terminator::Goto(merge_block));
                self.builder.set_current_block(else_block);
                if let Some(else_branch) = stmt.else_branch {
                    self.lower_statement(else_branch);
                }
                self.builder.set_terminator(Terminator::Goto(merge_block));
                self.builder.set_current_block(merge_block);
            }
            _ => {}
        }
    }

    fn lower_expression(&mut self, node_ref: NodeRef) -> Operand {
        let node = self.ast.get_node(node_ref);
        let _ty: TypeId = node.resolved_type.get().unwrap().into();
        match &node.kind {
            NodeKind::LiteralInt(val) => {
                let const_id = self.builder.create_constant(ConstValue::Int(*val));
                Operand::Constant(const_id)
            }
            _ => Operand::Constant(self.builder.create_constant(ConstValue::Int(0))),
        }
    }

    fn lower_lvalue(&mut self, node_ref: NodeRef) -> Lvalue {
        let node = self.ast.get_node(node_ref);
        match &node.kind {
            NodeKind::Ident(name, symbol) => {
                let symbol = symbol.get().unwrap();
                if let Some(lvalue) = self.lvalue_map.get(&symbol) {
                    *lvalue
                } else {
                    let globals = self.builder.finalize_module().globals;
                    let global = globals
                        .iter()
                        .find(|(_, g)| g.name == *name)
                        .unwrap()
                        .0;
                    Lvalue::Global(*global)
                }
            }
            // FIXME: unimplemented
            _ => unimplemented!(),
        }
    }

    fn lower_constant(&mut self, node_ref: NodeRef) -> ConstValueId {
        if let Some(const_id) = self.constant_map.get(&node_ref) {
            return *const_id;
        }

        let node = self.ast.get_node(node_ref);
        let _ty: TypeId = node.resolved_type.get().unwrap().into();

        let const_val = match &node.kind {
            NodeKind::LiteralInt(val) => ConstValue::Int(*val),
            NodeKind::LiteralFloat(val) => ConstValue::Float(*val),
            NodeKind::LiteralString(val) => ConstValue::String(val.to_string()),
            NodeKind::LiteralChar(val) => ConstValue::Int(*val as i64),
            NodeKind::CompoundLiteral(type_ref, init_list) => {
                let _ty: TypeId = (*type_ref).into();
                let _inits = self.lower_initializer_list(*init_list);
                //ConstValue::Aggregate(inits, ty)
                todo!()
            }
            NodeKind::Ident(name, symbol) => {
                let symbol_ref = symbol.get().unwrap();
                let symbol = self.symbol_table.get_symbol(symbol_ref);
                match symbol.kind {
                    SymbolKind::Variable { is_global, .. } => {
                        if is_global {
                            let globals = self.builder.finalize_module().globals;
                            let global = globals
                                .iter()
                                .find(|(_, g)| g.name == *name)
                                .unwrap()
                                .0;
                            ConstValue::GlobalAddress(*global)
                        } else {
                            panic!("not a global")
                        }
                    }
                    SymbolKind::EnumConstant { value, .. } => ConstValue::Int(value),
                    _ => panic!("not a constant"),
                }
            }
            _ => panic!("not a constant"),
        };
        let const_id = self.builder.create_constant(const_val);
        self.constant_map.insert(node_ref, const_id);
        const_id
    }

    fn lower_initializer_list(&mut self, node_ref: NodeRef) -> Vec<ConstValueId> {
        let node = self.ast.get_node(node_ref);
        match &node.kind {
            NodeKind::ListInitializer(inits) => inits
                .iter()
                .map(|i| self.lower_constant(i.initializer))
                .collect(),
            _ => panic!("not an initializer list"),
        }
    }
}
