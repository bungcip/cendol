//! Semantic Analysis Phase - Complete semantic checking and MIR construction.
//!
//! This module implements the full semantic analysis phase that bridges the gap
//! between parser AST and MIR, with comprehensive validation and proper multi-declarator
//! handling through a two-pass approach.

use crate::ast::BinaryOp;
use crate::ast::SymbolEntryRef;
use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::driver::compiler::SemaOutput;
use crate::mir::{
    self, BinaryOp as MirBinaryOp, CallTarget, ConstValue, ConstValueId, Local, LocalId, MirBlock, MirBlockId,
    MirBuilder, MirFunction, MirFunctionId, MirModule, MirStmt, Operand, Place, Rvalue, Terminator, TypeId,
};
use crate::semantic::symbol_table::SymbolTable;
use crate::source_manager::SourceSpan;
use hashbrown::HashMap;
use log::debug;

/// Main entry point for semantic analysis that produces MIR
pub struct SemanticAnalyzer<'a, 'src> {
    ast: &'a mut Ast,
    diag: &'src mut DiagnosticEngine,
    symbol_table: &'a mut SymbolTable,
    mir_builder: MirBuilder,
    current_function: Option<MirFunctionId>,
    current_block: Option<MirBlockId>,
    /// Maps variable names to their MIR Local IDs
    /// Maps symbol entry references to their MIR Local IDs.
    /// Using SymbolEntryRef instead of name ensures scope awareness and handles shadowing correctly.
    local_map: HashMap<SymbolEntryRef, LocalId>,
    /// Maps label names to their MIR Block IDs
    label_map: HashMap<Symbol, MirBlockId>,
    /// Track errors during analysis for early termination
    has_errors: bool,
}

impl<'a, 'src> SemanticAnalyzer<'a, 'src> {
    /// Create a new semantic analyzer
    pub fn new(ast: &'a mut Ast, diag: &'src mut DiagnosticEngine, symbol_table: &'a mut SymbolTable) -> Self {
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
        }
    }

    /// Main entry point - analyze AST and produce MIR module
    pub fn lower_module(&mut self) -> MirModule {
        debug!("Starting semantic analysis and MIR construction");

        // Check if we have a root node to start traversal from
        let Some(root_node_ref) = self.ast.root else {
            debug!("No root node found, skipping semantic analysis");
            return self.mir_builder.finalize_module();
        };

        // Reset symbol table traversal to re-enter scopes in the same order
        self.symbol_table.reset_traversal();

        // Process the entire AST starting from root
        self.lower_node_ref(root_node_ref);

        debug!("Semantic analysis complete");

        // Finalize global variables - convert tentative definitions to defined with implicit zero-initialization
        self.finalize_globals();

        self.mir_builder.finalize_module()
    }

    /// Lower module and return complete MIR data for testing
    pub fn lower_module_complete(&mut self) -> SemaOutput {
        debug!("Starting semantic analysis and MIR construction (complete)");

        // Check if we have a root node to start traversal from
        let Some(root_node_ref) = self.ast.root else {
            debug!("No root node found, skipping semantic analysis");
            let module = self.mir_builder.finalize_module();
            let functions = self.mir_builder.get_functions().clone();
            let blocks = self.mir_builder.get_blocks().clone();
            let locals = self.mir_builder.get_locals().clone();
            let globals = self.mir_builder.get_globals().clone();
            let types = self.mir_builder.get_types().clone();
            let constants = self.mir_builder.get_constants().clone();
            let statements = self.mir_builder.get_statements().clone();
            return SemaOutput {
                module,
                functions,
                blocks,
                locals,
                globals,
                types,
                constants,
                statements,
            };
        };

        // Reset symbol table traversal to re-enter scopes in the same order
        self.symbol_table.reset_traversal();

        // Process the entire AST starting from root
        self.lower_node_ref(root_node_ref);

        debug!("Semantic analysis complete");

        // Finalize global variables - convert tentative definitions to defined with implicit zero-initialization
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

    /// Report a semantic error and mark analyzer as having errors
    fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report(error);
    }

    /// Finalize global variables after the entire translation unit has been analyzed.
    /// This function converts tentative definitions to defined ones with implicit zero-initialization.
    fn finalize_globals(&mut self) {
        debug!("Finalizing global variables - converting tentative definitions to defined");

        let global_scope_id = crate::semantic::symbol_table::ScopeId::GLOBAL;
        let global_scope = self.symbol_table.get_scope(global_scope_id);

        // First pass: collect tentative global variable names and their entry refs
        let tentative_entries: Vec<(Symbol, SymbolEntryRef)> = global_scope
            .symbols
            .values()
            .filter_map(|entry_ref| {
                let entry = self.symbol_table.get_symbol_entry(*entry_ref);
                if matches!(entry.kind, SymbolKind::Variable { .. }) && entry.def_state == DefinitionState::Tentative {
                    Some((entry.name, *entry_ref))
                } else {
                    None
                }
            })
            .collect();

        // Second pass: update symbol table entries
        for (_, entry_ref) in &tentative_entries {
            let entry = self.symbol_table.get_symbol_entry_mut(*entry_ref);

            if let SymbolKind::Variable { .. } = &mut entry.kind
                && entry.def_state == DefinitionState::Tentative
            {
                debug!(
                    "Converting tentative definition to defined for global variable '{}'",
                    entry.name
                );
                entry.def_state = DefinitionState::Defined;
            }
        }

        // Third pass: add zero initialization to MIR globals
        for (var_name, _) in tentative_entries {
            self.add_zero_initialization_to_global(var_name);
        }

        debug!("Global variable finalization complete");
    }

    /// Add zero initialization to a MIR global variable
    fn add_zero_initialization_to_global(&mut self, var_name: Symbol) {
        debug!("Adding zero initialization to global variable '{}'", var_name);

        // Get immutable access to globals to find the target
        let target_global_id = {
            let globals = self.mir_builder.get_globals();
            globals
                .iter()
                .find(|(_, global)| global.name == var_name && global.initial_value.is_none())
                .map(|(global_id, _)| *global_id)
        };

        if let Some(global_id) = target_global_id {
            debug!("Found global '{}' that needs zero initialization", var_name);

            // Get the global's type to determine what zero value to create
            let global_type = {
                let global = self.mir_builder.get_globals().get(&global_id).unwrap();
                self.get_types().get(&global.type_id).cloned()
            };

            if let Some(mir_type) = global_type {
                // Create an appropriate zero constant based on the type
                let zero_const = match mir_type {
                    crate::mir::MirType::Int { is_signed: _, width: _ } => ConstValue::Int(0),
                    crate::mir::MirType::Float { width: _ } => ConstValue::Float(0.0),
                    crate::mir::MirType::Bool => ConstValue::Bool(false),
                    crate::mir::MirType::Pointer { .. } => ConstValue::Null,
                    _ => {
                        // For complex types like structs, we can't easily create zero
                        // For now, just skip complex types
                        debug!("Skipping zero initialization for complex type: {:?}", mir_type);
                        return;
                    }
                };

                // Create the zero constant
                let const_id = self.create_constant(zero_const);

                // Update the global to have the zero initial value
                let globals_mut = self.mir_builder.get_globals_mut();
                if let Some(global_mut) = globals_mut.get_mut(&global_id) {
                    global_mut.initial_value = Some(const_id);
                    debug!("Added zero initialization to global '{}'", var_name);
                }
            }
        }
    }

    /// Lower a single AST node reference
    fn lower_node_ref(&mut self, node_ref: NodeRef) {
        // Get the node data first to avoid borrowing issues
        let node_kind = self.ast.get_node(node_ref).kind.clone();
        let node_span = self.ast.get_node(node_ref).span;

        match node_kind {
            NodeKind::TranslationUnit(nodes) => {
                for child_ref in nodes {
                    self.lower_node_ref(child_ref);
                }
            }

            NodeKind::FunctionDef(func_def) => {
                self.lower_function_def(&func_def, node_span);
            }

            NodeKind::Declaration(_) => {
                // This should have been converted to VarDecl or TypedefDecl in earlier phases
                panic!("NodeKind::Declaration still exists in AST during semantic analysis");
            }

            NodeKind::TypedefDecl(typedef_decl) => {
                self.lower_typedef_declaration(&typedef_decl, node_span);
            }

            NodeKind::RecordDecl(record_decl) => {
                self.lower_record_declaration(&record_decl, node_span);
            }

            NodeKind::VarDecl(var_decl) => {
                self.lower_var_declaration(&var_decl, node_span);
            }

            NodeKind::While(while_stmt) => {
                self.lower_while_statement(&while_stmt, node_span);
            }

            NodeKind::DoWhile(body_ref, condition_ref) => {
                self.lower_do_while_statement(body_ref, condition_ref, node_span);
            }

            // Handle compound statements by processing their statements
            NodeKind::CompoundStatement(nodes) => {
                self.lower_compound_statement(&nodes);
            }

            // Handle declaration lists by processing each declaration
            NodeKind::DeclarationList(nodes) => {
                for child_ref in nodes {
                    self.lower_node_ref(child_ref);
                }
            }

            // For other node types, try to lower as statement
            _ => {
                self.try_lower_as_statement(node_ref);
            }
        }
    }

    /// Try to lower a node as a statement
    fn try_lower_as_statement(&mut self, node_ref: NodeRef) {
        // Get the node data first to avoid borrowing issues
        let node = self.ast.get_node(node_ref);

        match node.kind {
            NodeKind::Return(expr) => {
                self.lower_return_statement(&expr, node.span);
            }
            NodeKind::Goto(label) => {
                self.lower_goto_statement(label, node.span);
            }
            NodeKind::Label(label, statement) => {
                self.lower_label_statement(label, statement, node.span);
            }
            NodeKind::If(if_stmt) => {
                self.lower_if_statement(&if_stmt, node.span);
            }
            NodeKind::ExpressionStatement(Some(expr_ref)) => {
                self.lower_expression(expr_ref);
            }
            _ => {
                // For unsupported statement types, just continue
            }
        }
    }

    /// Two-pass approach for compound statements to handle goto/label resolution
    fn lower_compound_statement(&mut self, nodes: &[NodeRef]) {
        debug!(
            "Processing compound statement with {} items using two-pass approach",
            nodes.len()
        );

        // First pass: collect all labels (including nested ones)
        // Note: Label collection doesn't need scope management as labels are function-scoped
        for &stmt_ref in nodes {
            self.collect_labels_recursive(stmt_ref);
        }

        // Second pass: process all statements with proper scope management
        self.symbol_table
            .push_scope(crate::semantic::symbol_table::ScopeKind::Block);

        for &stmt_ref in nodes {
            self.lower_node_ref(stmt_ref);
        }

        self.symbol_table.pop_scope();
    }

    /// Recursively collect all labels from a statement and its nested statements
    fn collect_labels_recursive(&mut self, stmt_ref: NodeRef) {
        // Clone the node kind to avoid borrow conflicts
        let node_kind = self.ast.get_node(stmt_ref).kind.clone();

        match node_kind {
            NodeKind::Label(label, _) => {
                // If the label is already mapped, it means we've processed it as part of a
                // preceding chain of labels. We can skip it to avoid redundant work and errors.
                if self.label_map.contains_key(&label) {
                    return;
                }

                // This is the first unprocessed label in a chain. Create a single block for the entire chain.
                let target_block_id = self.mir_builder.create_block();
                let mut current_stmt = stmt_ref;

                // Traverse the chain of consecutive labels, mapping each to the same block.
                while let NodeKind::Label(current_label, next_stmt) = self.ast.get_node(current_stmt).kind.clone() {
                    if self.label_map.contains_key(&current_label) {
                        let node_span = self.ast.get_node(current_stmt).span;
                        self.report_error(SemanticError::Redefinition {
                            name: current_label,
                            first_def: node_span, // Note: This is not the ideal span for first_def
                            second_def: node_span,
                        });
                    } else {
                        self.label_map.insert(current_label, target_block_id);
                    }
                    current_stmt = next_stmt;
                }

                // After the loop, current_stmt is the first non-label statement.
                // Recursively process it for any nested labels.
                self.collect_labels_recursive(current_stmt);
            }
            NodeKind::CompoundStatement(nodes) => {
                // For compound statements, recursively collect labels from all items
                for &nested_stmt_ref in nodes.iter() {
                    self.collect_labels_recursive(nested_stmt_ref);
                }
            }
            NodeKind::DeclarationList(nodes) => {
                // For declaration lists, recursively collect labels from all items
                for &nested_stmt_ref in nodes.iter() {
                    self.collect_labels_recursive(nested_stmt_ref);
                }
            }
            NodeKind::If(if_stmt) => {
                self.collect_labels_recursive(if_stmt.then_branch);
                if let Some(else_branch) = if_stmt.else_branch {
                    self.collect_labels_recursive(else_branch);
                }
            }
            NodeKind::While(while_stmt) => {
                self.collect_labels_recursive(while_stmt.body);
            }
            NodeKind::DoWhile(body, _) => {
                self.collect_labels_recursive(body);
            }
            NodeKind::For(for_stmt) => {
                self.collect_labels_recursive(for_stmt.body);
            }
            NodeKind::Switch(_, body) => {
                self.collect_labels_recursive(body);
            }
            NodeKind::Case(_, stmt) => {
                self.collect_labels_recursive(stmt);
            }
            NodeKind::CaseRange(_, _, stmt) => {
                self.collect_labels_recursive(stmt);
            }
            NodeKind::Default(stmt) => {
                self.collect_labels_recursive(stmt);
            }
            _ => {
                // Leaves or nodes that definitely don't contain statements (e.g. VarDecl)
            }
        }
    }

    /// Extract the return type from a function declarator
    fn extract_function_return_type(
        &mut self,
        declarator: &Declarator,
        _specifiers: &[DeclSpecifier],
        _location: SourceSpan,
    ) -> TypeId {
        // Start with a default return type (int)
        let base_type_ref = self.ast.push_type(Type::new(TypeKind::Int { is_signed: true }));

        // The function declarator should be a Function type
        if let Declarator::Function(base_declarator, _) = declarator {
            // The base declarator contains the return type information
            // We need to resolve what the base type is

            // For now, we'll look at the function definition's specifiers
            // In a more complete implementation, we would track the function's
            // return type through the semantic lowering phase

            // Check if we can find the function in the symbol table to get its type
            if let Some(func_name) = extract_identifier(declarator) {
                debug!("Looking for function '{}' in symbol table", func_name);
                if let Some((entry_ref, _)) = self.symbol_table.lookup_symbol(func_name) {
                    let entry = self.symbol_table.get_symbol_entry(entry_ref);
                    debug!(
                        "Found function '{}' in symbol table, type_info: {:?}",
                        func_name, entry.type_info
                    );
                    // The function's return type is stored in the type_info field
                    // which points to a function type that contains the return type
                    if matches!(&entry.kind, SymbolKind::Function { .. }) {
                        // Get the function type from type_info
                        let func_type = self.ast.get_type(entry.type_info);
                        debug!("Function type: {:?}", func_type.kind);
                        if let TypeKind::Function { return_type, .. } = &func_type.kind {
                            debug!("Found return type: {:?}", return_type);
                            // Use the function's return type from the symbol table
                            return self.lower_type_to_mir(*return_type);
                        }
                    }
                } else {
                    debug!("Function '{}' not found in symbol table", func_name);
                }
            }

            // If we couldn't find the function in the symbol table, try to extract
            // the return type from the base declarator
            // For simple cases like "void" or "int", the base declarator is just an identifier
            // We need to look at the function's specifiers to determine the return type
            // This is a simplified approach - in a full implementation, we would
            // have the return type properly tracked through semantic analysis
            let _base = base_declarator; // Keep for potential future use
        }

        // Default to int if we couldn't determine the return type
        debug!("Using default return type (int)");
        self.lower_type_to_mir(base_type_ref)
    }

    /// Lower a function definition
    fn lower_function_def(&mut self, func_def: &FunctionDefData, location: SourceSpan) {
        debug!("Lowering function definition");

        // Extract function name from declarator
        let func_name = match extract_identifier(&func_def.declarator) {
            Some(symbol) => {
                debug!("Found function identifier directly: {}", symbol);
                symbol
            }
            None => {
                self.report_error(SemanticError::TypeMismatch {
                    expected: "a named function declarator".to_string(),
                    found: "an unnamed declarator".to_string(),
                    location,
                });
                Symbol::new("unknown_function")
            }
        };

        // Extract the return type from the function declarator
        let return_type = self.extract_function_return_type(&func_def.declarator, &func_def.specifiers, location);

        // Create MIR function
        let func_id = self.mir_builder.create_function(func_name, return_type);
        debug!(
            "Created function '{}' with ID {:?} (ID as integer: {})",
            func_name,
            func_id,
            func_id.get()
        );

        // Set current function
        self.mir_builder.set_current_function(func_id);
        self.current_function = Some(func_id);

        // Create entry block explicitly
        let entry_block_id = self.mir_builder.create_block();
        self.mir_builder.set_function_entry_block(func_id, entry_block_id);
        self.mir_builder.set_current_block(entry_block_id);
        self.current_block = Some(entry_block_id);

        // Push function scope for parameters and locals
        let func_scope = self
            .symbol_table
            .push_scope(crate::semantic::symbol_table::ScopeKind::Function);
        debug!("Pushed function scope: {:?}", func_scope);

        // Process function parameters and create locals for them
        // Skip parameters for main function
        if func_name.as_str() != "main" {
            self.lower_function_parameters(&func_def.declarator, location);
        } else {
            debug!("Skipping parameters for main function");
        }

        // Process function body
        self.lower_node_ref(func_def.body);

        // Pop function scope
        self.symbol_table.pop_scope();

        debug!("Completed function definition: {}", func_name);
    }

    /// Lower function parameters and create local variables for them
    fn lower_function_parameters(&mut self, declarator: &Declarator, location: SourceSpan) {
        debug!("Lowering function parameters");

        // Extract parameters from the function declarator
        if let Declarator::Function(_, parameters) = declarator {
            debug!("Found {} function parameters", parameters.len());

            for param in parameters {
                self.lower_function_parameter(param, location);
            }
        } else {
            debug!("Declarator is not a function, skipping parameters");
        }
    }

    /// Lower a single function parameter
    fn lower_function_parameter(&mut self, param: &ParamData, location: SourceSpan) {
        debug!("Lowering function parameter");

        // Extract parameter name from declarator if present
        let param_name = if let Some(declarator) = &param.declarator {
            if let Some(symbol) = extract_identifier(declarator) {
                symbol
            } else {
                // Abstract parameter (no name) - skip for now
                debug!("Skipping abstract parameter without name");
                return;
            }
        } else {
            // No declarator - skip for now
            debug!("Skipping parameter without declarator");
            return;
        };

        debug!("Processing parameter: {}", param_name);

        // Check for redeclaration in current scope
        if let Some((existing_entry, scope_id)) = self.symbol_table.lookup_symbol(param_name)
            && scope_id == self.symbol_table.current_scope()
        {
            // If we've already created a MIR local for this entry in this pass, it's a real redefinition
            if self.local_map.contains_key(&existing_entry) {
                let existing = self.symbol_table.get_symbol_entry(existing_entry);
                self.report_error(SemanticError::Redefinition {
                    name: param_name,
                    first_def: existing.def_span,
                    second_def: location,
                });
                return;
            }

            // Symbol already exists from previous pass (lowering). Re-use it and create MIR local.
            let type_id = self.get_int_type(); // Default to int for now
            let local_id = self.mir_builder.create_local(Some(param_name), type_id, true);
            self.local_map.insert(existing_entry, local_id);
            debug!(
                "Re-using symbol entry from lowering pass for parameter '{}'",
                param_name
            );
            return;
        }

        // Create MIR local for the parameter
        let type_id = self.get_int_type(); // Default to int for now
        let local_id = self.mir_builder.create_local(Some(param_name), type_id, true);

        // Add to symbol table and store in local map
        let symbol_entry = SymbolEntry {
            name: param_name,
            kind: SymbolKind::Variable {
                is_global: false,
                is_static: false,
                initializer: None,
            },
            type_info: self.ast.push_type(Type {
                kind: TypeKind::Int { is_signed: true },
                qualifiers: TypeQualifiers::empty(),
                size: None,
                alignment: None,
            }),
            storage_class: None,
            scope_id: self.symbol_table.current_scope().get(),
            def_span: location,
            def_state: DefinitionState::Defined,
            is_referenced: false,
            is_completed: true,
        };

        let entry_ref = self.symbol_table.add_symbol(param_name, symbol_entry);
        self.local_map.insert(entry_ref, local_id);
    }

    /// Second pass: Process an initializer and emit assignment
    fn process_initializer(
        &mut self,
        initializer: &Initializer,
        local_id: LocalId,
        var_name: &str,
        location: SourceSpan,
    ) {
        debug!("Processing initializer for variable '{}'", var_name);

        match initializer {
            Initializer::Expression(expr_ref) => {
                // Lower the initializer expression to an operand
                let init_operand = self.lower_expression(*expr_ref);

                // Emit assignment: local = initializer
                self.emit_assignment(Place::Local(local_id), init_operand, location);
            }
            Initializer::List(designated_initializers) => {
                // Process designated initializers (both positional and named)
                self.process_designated_initializers(designated_initializers, local_id, var_name, location);
            }
        }
    }

    /// Process designated initializers for struct/array initialization
    fn process_designated_initializers(
        &mut self,
        designated_initializers: &[DesignatedInitializer],
        local_id: LocalId,
        var_name: &str,
        location: SourceSpan,
    ) {
        debug!(
            "Processing {} designated initializers for variable '{}'",
            designated_initializers.len(),
            var_name
        );

        // For now, handle the simple case of positional initializers
        // This covers cases like: struct { int a; int b; int c; } s = {1, 2, 3};

        let mut current_index = 0;

        for designated_init in designated_initializers {
            if designated_init.designation.is_empty() {
                // This is a positional initializer
                self.process_positional_initializer(
                    &designated_init.initializer,
                    local_id,
                    var_name,
                    current_index,
                    location,
                );
                current_index += 1;
            } else {
                // This is a designated initializer with explicit field/index
                // Process named designated initializer
                self.process_named_designated_initializer(designated_init, local_id, var_name, location);
            }
        }
    }

    /// Process a named designated initializer (with field names or array indices)
    fn process_named_designated_initializer(
        &mut self,
        designated_init: &DesignatedInitializer,
        local_id: LocalId,
        var_name: &str,
        location: SourceSpan,
    ) {
        debug!("Processing named designated initializer for variable '{}'", var_name);

        // Get the variable's type information
        let var_type_id = {
            let local = self.get_locals().get(&local_id).expect("Local should exist");
            // The local already has the canonicalized type from lower_var_declaration
            local.type_id
        };

        // Process each designator in sequence (for nested field access)
        let mut current_place = Place::Local(local_id);
        let mut current_type_id = var_type_id;

        for designator in &designated_init.designation {
            match designator {
                Designator::FieldName(field_name) => {
                    // Look up the field in the struct/union type
                    if let Some(field_index) = self.find_struct_field(current_type_id, *field_name) {
                        debug!("Found field '{}' at index {}", field_name, field_index);
                        // Create a place representing the struct field
                        current_place = Place::StructField(Box::new(current_place), field_index);

                        // Update current type to the field's type for potential nested access
                        if let Some(field_type_id) = self.get_struct_field_type(current_type_id, field_index) {
                            current_type_id = field_type_id;
                        }
                    } else {
                        // Field not found - report error
                        debug!(
                            "Field '{}' not found in type {:?}",
                            field_name,
                            self.get_types().get(&current_type_id)
                        );
                        self.report_error(SemanticError::UndeclaredIdentifier {
                            name: *field_name,
                            location,
                        });
                        return;
                    }
                }
                Designator::ArrayIndex(index_expr) => {
                    // Handle array index designator
                    let index_operand = self.lower_expression(*index_expr);
                    current_place = Place::ArrayIndex(Box::new(current_place), Box::new(index_operand));

                    // Update current type to the element type
                    if let Some(element_type_id) = self.get_array_element_type(current_type_id) {
                        current_type_id = element_type_id;
                    }
                }
                Designator::GnuArrayRange(_start_expr, _end_expr) => {
                    // GNU extension: range designator [start ... end]
                    self.report_error(SemanticError::UnsupportedFeature {
                        feature: "GNU array range designator".to_string(),
                        location,
                    });
                    return;
                }
            }
        }

        // Process the initializer for this designated field
        match &designated_init.initializer {
            Initializer::Expression(expr_ref) => {
                // Lower the initializer expression to an operand
                let init_operand = self.lower_expression(*expr_ref);

                // Emit assignment to the designated field: field = initializer
                self.emit_assignment(current_place, init_operand, location);
            }
            Initializer::List(_nested_inits) => {
                // Nested compound initializer - for now, just report as unsupported
                self.report_error(SemanticError::NonConstantInitializer { location });
            }
        }
    }

    /// Process a positional initializer (no designation)
    fn process_positional_initializer(
        &mut self,
        initializer: &Initializer,
        local_id: LocalId,
        var_name: &str,
        index: usize,
        location: SourceSpan,
    ) {
        debug!(
            "Processing positional initializer {} for variable '{}'",
            index, var_name
        );

        match initializer {
            Initializer::Expression(expr_ref) => {
                // For simple positional initializers, we can use the existing logic
                // but we need to handle struct/array member access
                let init_operand = self.lower_expression(*expr_ref);

                // Get the type for the temporary local
                let temp_type_id = self.get_int_type(); // For now, assume int type

                // Create a temporary local for the initializer
                let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);

                // Emit assignment to temporary: temp = initializer
                self.emit_assignment(Place::Local(temp_local_id), init_operand, location);

                // TODO: Emit assignment to the appropriate struct member or array element
                // For now, just assign to the main local
                self.emit_assignment(
                    Place::Local(local_id),
                    Operand::Copy(Box::new(Place::Local(temp_local_id))),
                    location,
                );
            }
            Initializer::List(_) => {
                // Nested compound initializer - for now, just report as unsupported
                self.report_error(SemanticError::NonConstantInitializer { location });
            }
        }
    }

    /// Process compound initializers for global variables
    fn process_global_compound_initializer(
        &mut self,
        initializer: &Initializer,
        var_name: Symbol,
        _var_type_id: TypeId,
        location: SourceSpan,
    ) -> Option<ConstValueId> {
        debug!("Processing global compound initializer for variable '{}'", var_name);

        match initializer {
            Initializer::List(designated_initializers) => {
                // Collect constant values for fields
                // We use a map to handle out-of-order and designated initializers
                // Key is the field index
                let mut field_values_map: HashMap<usize, ConstValueId> = HashMap::new();

                // Track current index for positional initializers
                let mut current_index = 0;

                // Process each initializer in the compound initializer
                for designated_init in designated_initializers {
                    // Determine the target field index
                    let target_index = if designated_init.designation.is_empty() {
                        // Positional initializer
                        let index = current_index;
                        current_index += 1;
                        index
                    } else {
                        // Designated initializer
                        // We only support single-level designation for now (e.g., .a = 1)
                        // Nested designation (e.g., .a.b = 1) is not supported for globals yet

                        if designated_init.designation.len() > 1 {
                            self.report_error(SemanticError::NonConstantInitializer { location });
                            return None;
                        }

                        match &designated_init.designation[0] {
                            Designator::FieldName(name) => {
                                if let Some(index) = self.find_struct_field(_var_type_id, *name) {
                                    // Update current index to the next field after this one
                                    current_index = index + 1;
                                    index
                                } else {
                                    self.report_error(SemanticError::UndeclaredIdentifier { name: *name, location });
                                    return None;
                                }
                            }
                            Designator::ArrayIndex(_) => {
                                self.report_error(SemanticError::NonConstantInitializer { location });
                                return None;
                            }
                            Designator::GnuArrayRange(_, _) => {
                                self.report_error(SemanticError::NonConstantInitializer { location });
                                return None;
                            }
                        }
                    };

                    // Process the initializer value
                    if let Initializer::Expression(expr_ref) = &designated_init.initializer {
                        // Lower the initializer expression to get the constant value
                        let init_operand = self.lower_expression(*expr_ref);

                        match init_operand {
                            Operand::Constant(const_id) => {
                                debug!(
                                    "Global compound initializer: field {} = constant {:?}",
                                    target_index, const_id
                                );
                                field_values_map.insert(target_index, const_id);
                            }
                            Operand::AddressOf(place_box) => {
                                if let Place::Global(global_id) = *place_box {
                                    debug!(
                                        "Global compound initializer: field {} = address of global {:?}",
                                        target_index, global_id
                                    );
                                    let const_val = ConstValue::GlobalAddress(global_id);
                                    let const_id = self.create_constant(const_val);
                                    field_values_map.insert(target_index, const_id);
                                } else {
                                    self.report_error(SemanticError::NonConstantInitializer { location });
                                    return None;
                                }
                            }
                            _ => {
                                // Non-constant expression in global initializer - report error
                                self.report_error(SemanticError::NonConstantInitializer { location });
                                return None;
                            }
                        }
                    } else {
                        // Nested compound literal
                        // Get the type of the field we are initializing
                        // Try to get struct field type first
                        let field_type_id =
                            if let Some(type_id) = self.get_struct_field_type(_var_type_id, target_index) {
                                type_id
                            } else if let Some(element_type_id) = self.get_array_element_type(_var_type_id) {
                                // If it's an array, use the element type
                                element_type_id
                            } else {
                                self.report_error(SemanticError::NonConstantInitializer { location });
                                return None;
                            };

                        if let Some(nested_const_id) = self.process_global_compound_initializer(
                            &designated_init.initializer,
                            var_name,
                            field_type_id,
                            location,
                        ) {
                            debug!(
                                "Global compound initializer: field {} = nested constant {:?}",
                                target_index, nested_const_id
                            );
                            field_values_map.insert(target_index, nested_const_id);
                        } else {
                            return None;
                        }
                    }
                }

                // Convert map to vector of (index, value) pairs, sorted by index
                let mut field_values: Vec<(usize, ConstValueId)> = field_values_map.into_iter().collect();
                field_values.sort_by_key(|(idx, _)| *idx);

                // Create a struct literal constant value
                let struct_literal = ConstValue::StructLiteral(field_values);
                let struct_const_id = self.create_constant(struct_literal);

                debug!(
                    "Created struct literal constant {:?} for global variable '{}'",
                    struct_const_id, var_name
                );

                Some(struct_const_id)
            }
            _ => {
                // This should not happen as we only call this for compound initializers
                debug!("Unexpected initializer type in process_global_compound_initializer");
                None
            }
        }
    }

    /// Lower a variable declaration (from semantic AST)
    fn lower_var_declaration(&mut self, var_decl: &VarDeclData, location: SourceSpan) {
        debug!("Lowering semantic var declaration for '{}'", var_decl.name);

        // Check for redeclaration
        if let Some((existing_entry, scope_id)) = self.symbol_table.lookup_symbol(var_decl.name)
            && scope_id == self.symbol_table.current_scope()
        {
            // If we've already handled this in THIS pass (it has a MIR local or is a global we've seen),
            // it might be a real redefinition.
            // For locals, we check local_map.
            if self.local_map.contains_key(&existing_entry) {
                let existing = self.symbol_table.get_symbol_entry(existing_entry);
                self.report_error(SemanticError::Redefinition {
                    name: var_decl.name,
                    first_def: existing.def_span,
                    second_def: location,
                });
                return;
            }

            // If it's a global, we can check if it already has a MIR global.
            // ... (global redefinition check could be here, but let's focus on fixing the bug first)
        }

        // Canonicalize the variable's type (like Clang does)
        let canonical_type_id = self.canonicalize_type(var_decl.ty);
        debug!(
            "Canonicalized type for variable '{}': {} -> {}",
            var_decl.name,
            var_decl.ty.get(),
            canonical_type_id.get()
        );

        // Convert AST type to MIR type
        let mir_type_id = self.lower_type_to_mir(canonical_type_id);

        let is_global = self.current_function.is_none();
        let initializer_node_ref = var_decl.init.as_ref().and_then(|init| match init {
            Initializer::Expression(expr_ref) => Some(*expr_ref),
            _ => None,
        });

        if is_global {
            // Check if a global with this name already exists
            let mut existing_global_id = None;
            for (global_id, global) in self.mir_builder.get_globals() {
                if global.name == var_decl.name {
                    existing_global_id = Some(*global_id);
                    break;
                }
            }

            let global_id = if let Some(existing_id) = existing_global_id {
                debug!("Reusing existing global '{}' with id {:?}", var_decl.name, existing_id);
                existing_id
            } else {
                // Create MIR global variable
                let is_constant =
                    var_decl.storage == Some(StorageClass::Static) || var_decl.storage == Some(StorageClass::Extern);

                // Process initializer to get constant value
                let mut initial_value_id = None;
                if let Some(init) = &var_decl.init {
                    match init {
                        Initializer::Expression(expr_ref) => {
                            // Try to evaluate the initializer as a constant
                            let init_operand = self.lower_expression(*expr_ref);
                            if let Operand::Constant(const_id) = init_operand {
                                initial_value_id = Some(const_id);
                            }
                        }
                        _ => {
                            // For compound initializers in global variables, we need to process them properly
                            if let Some(struct_const_id) =
                                self.process_global_compound_initializer(init, var_decl.name, mir_type_id, location)
                            {
                                initial_value_id = Some(struct_const_id);
                            }
                        }
                    }
                }

                let new_global_id =
                    self.mir_builder
                        .create_global_with_init(var_decl.name, mir_type_id, is_constant, initial_value_id);
                debug!("Created new global '{}' with id {:?}", var_decl.name, new_global_id);
                new_global_id
            };

            // Handle global variable symbol table entry with proper redefinition checking
            let def_state = if initializer_node_ref.is_some() {
                DefinitionState::Defined
            } else if var_decl.storage == Some(StorageClass::Extern) {
                DefinitionState::DeclaredOnly
            } else {
                DefinitionState::Tentative
            };

            let symbol_entry = SymbolEntry {
                name: var_decl.name,
                kind: SymbolKind::Variable {
                    is_global: true,
                    is_static: var_decl.storage == Some(StorageClass::Static),
                    initializer: initializer_node_ref,
                },
                type_info: var_decl.ty,
                storage_class: var_decl.storage,
                scope_id: self.symbol_table.current_scope().get(),
                def_span: location,
                def_state,
                is_referenced: false,
                is_completed: true,
            };

            // Use merge_global_symbol to handle C11 6.9.2 merging rules and detect redefinitions
            match self.symbol_table.merge_global_symbol(var_decl.name, symbol_entry) {
                Ok(entry_ref) => {
                    // Symbol was successfully added or merged
                    debug!("Global variable '{}' processed successfully", var_decl.name);

                    // If this is a new symbol (not merged), we may need to add it to MIR globals
                    // Check if this symbol already exists in the symbol table
                    if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(var_decl.name)
                        && existing_entry != entry_ref
                    {
                        // This is a new symbol, ensure it's in MIR globals
                        // (This case shouldn't happen with merge_global_symbol, but keeping for safety)
                    }
                }
                Err(_error) => {
                    // merge_global_symbol detected a redefinition error
                    // The error already contains the symbol name, but we need source spans for proper error reporting
                    // Find the existing symbol to get its definition span for error reporting
                    if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(var_decl.name) {
                        let existing = self.symbol_table.get_symbol_entry(existing_entry);
                        self.report_error(SemanticError::Redefinition {
                            name: var_decl.name,
                            first_def: existing.def_span,
                            second_def: location,
                        });
                    } else {
                        // This shouldn't happen, but provide a fallback error
                        self.report_error(SemanticError::Redefinition {
                            name: var_decl.name,
                            first_def: location,
                            second_def: location,
                        });
                    }
                    return;
                }
            }
            debug!("Created semantic global '{}' with id {:?}", var_decl.name, global_id);
        } else {
            // Check if symbol entry already exists from previous pass
            let existing_entry = self.symbol_table.lookup_symbol(var_decl.name).and_then(|(e, s)| {
                if s == self.symbol_table.current_scope() {
                    Some(e)
                } else {
                    None
                }
            });

            // Create MIR local variable (inside function)
            let local_id = self.mir_builder.create_local(Some(var_decl.name), mir_type_id, false);

            let entry_ref = if let Some(e) = existing_entry {
                e
            } else {
                // Add to symbol table as local
                let def_state = if initializer_node_ref.is_some() {
                    DefinitionState::Defined
                } else if var_decl.storage == Some(StorageClass::Extern) {
                    DefinitionState::DeclaredOnly
                } else {
                    DefinitionState::Tentative
                };

                let symbol_entry = SymbolEntry {
                    name: var_decl.name,
                    kind: SymbolKind::Variable {
                        is_global: false,
                        is_static: var_decl.storage == Some(StorageClass::Static),
                        initializer: initializer_node_ref,
                    },
                    type_info: var_decl.ty,
                    storage_class: var_decl.storage,
                    scope_id: self.symbol_table.current_scope().get(),
                    def_span: location,
                    def_state,
                    is_referenced: false,
                    is_completed: true,
                };
                self.symbol_table.add_symbol(var_decl.name, symbol_entry)
            };

            // Store in local map
            self.local_map.insert(entry_ref, local_id);

            // Process initializer if present
            if let Some(initializer) = &var_decl.init {
                self.process_initializer(initializer, local_id, &var_decl.name.to_string(), location);
            }

            debug!("Created semantic local '{}' with id {:?}", var_decl.name, local_id);
        }
    }

    /// Lower a typedef declaration
    fn lower_typedef_declaration(&mut self, typedef_decl: &TypedefDeclData, location: SourceSpan) {
        // Check if typedef is already in symbol table (added during semantic lowering)
        if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(typedef_decl.name) {
            let existing = self.symbol_table.get_symbol_entry(existing_entry);
            // If it's already a typedef with the same type, skip the redefinition error
            if matches!(existing.kind, SymbolKind::Typedef { .. }) {
                debug!(
                    "Typedef '{}' already exists in symbol table, skipping duplicate",
                    typedef_decl.name
                );
                return;
            } else {
                // Different symbol with same name - this is a real redefinition error
                self.report_error(SemanticError::Redefinition {
                    name: typedef_decl.name,
                    first_def: existing.def_span,
                    second_def: location,
                });
                return;
            }
        }

        // Add typedef to symbol table (only if not already present)
        let symbol_entry = SymbolEntry {
            name: typedef_decl.name,
            kind: SymbolKind::Typedef {
                aliased_type: typedef_decl.ty,
            },
            type_info: typedef_decl.ty, // Typedef points to the aliased type
            storage_class: Some(StorageClass::Typedef),
            scope_id: self.symbol_table.current_scope().get(),
            def_span: location,
            def_state: DefinitionState::Defined,
            is_referenced: false,
            is_completed: true,
        };

        self.symbol_table.add_symbol(typedef_decl.name, symbol_entry);
    }

    /// Lower a record declaration (struct/union)
    fn lower_record_declaration(&mut self, record_decl: &RecordDeclData, _location: SourceSpan) {
        debug!(
            "Lowering record declaration for '{}'",
            record_decl.name.map_or("<anonymous>".to_string(), |n| n.to_string())
        );

        // Check if we already have a MIR type for this record
        // The semantic lowering phase should have already created the proper type
        // with member information, so we just need to ensure it's in the MIR types
        let mir_type_id = self.lower_type_to_mir(record_decl.ty);

        debug!("Created/verified MIR type for record: {:?}", mir_type_id);

        // Verify that the type has the expected members
        if let Some(mir_type) = self.get_types().get(&mir_type_id) {
            debug!("Record type info: {:?}", mir_type);
        }
    }

    /// Lower an expression to an operand
    fn lower_expression(&mut self, expr_ref: NodeRef) -> Operand {
        match self.ast.get_node(expr_ref).kind.clone() {
            NodeKind::LiteralInt(val) => {
                let const_id = self.create_constant(ConstValue::Int(val));
                Operand::Constant(const_id)
            }

            NodeKind::LiteralFloat(val) => {
                let const_id = self.create_constant(ConstValue::Float(val));
                Operand::Constant(const_id)
            }

            NodeKind::LiteralChar(val) => {
                // Character literals in C are essentially integer constants representing the character code
                let const_id = self.create_constant(ConstValue::Int(val as i64));
                Operand::Constant(const_id)
            }

            NodeKind::LiteralString(val) => {
                // String literals are represented as string constants
                let const_id = self.create_constant(ConstValue::String(val.to_string()));
                Operand::Constant(const_id)
            }

            NodeKind::Ident(name, symbol_ref) => {
                debug!("Resolving identifier '{}'", name);
                // First try to resolve through semantic analysis
                if let Some(resolved_ref) = symbol_ref.get() {
                    let entry = self.symbol_table.get_symbol_entry(resolved_ref);

                    match &entry.kind {
                        SymbolKind::Variable { is_global, .. } => {
                            if *is_global {
                                // This is a global variable - find its MIR global ID
                                for (global_id, global) in self.mir_builder.get_globals() {
                                    if global.name == entry.name {
                                        let current_node = self.ast.get_node(expr_ref);
                                        current_node.resolved_type.set(Some(entry.type_info));
                                        return Operand::Copy(Box::new(Place::Global(*global_id)));
                                    }
                                }
                            } else {
                                // This is a local variable - look up the local in our local map
                                if let Some(local_id) = self.local_map.get(&resolved_ref) {
                                    let current_node = self.ast.get_node(expr_ref);
                                    current_node.resolved_type.set(Some(entry.type_info));
                                    return Operand::Copy(Box::new(Place::Local(*local_id)));
                                }
                            }
                        }
                        SymbolKind::EnumConstant { value } => {
                            let val = *value;
                            let type_info = entry.type_info;
                            let const_id = self.create_constant(ConstValue::Int(val));
                            let current_node = self.ast.get_node(expr_ref);
                            current_node.resolved_type.set(Some(type_info));
                            return Operand::Constant(const_id);
                        }
                        SymbolKind::Function { .. } => {
                            // Function identifier - resolve to function address
                            debug!("Resolving function identifier '{}' to function address", name);

                            // Look up the function in MIR functions by name
                            if let Some(func_id) = self.find_mir_function_by_name(name) {
                                let current_node = self.ast.get_node(expr_ref);
                                current_node.resolved_type.set(Some(entry.type_info));
                                // Create a function address constant
                                let func_addr_const = ConstValue::FunctionAddress(func_id);
                                let const_id = self.create_constant(func_addr_const);
                                return Operand::Constant(const_id);
                            } else {
                                // Function not found in MIR, might be a forward declaration
                                debug!("Function '{}' found in symbol table but not in MIR functions", name);
                                // For now, return a dummy operand to allow compilation to continue
                                let error_const = self.create_constant(ConstValue::Int(0));
                                return Operand::Constant(error_const);
                            }
                        }
                        _ => {}
                    }
                }

                // Fallback: Check if it's a global variable by name
                for (global_id, global) in self.mir_builder.get_globals() {
                    if global.name == name {
                        // Try to find the type info from symbol table
                        if let Some((entry_ref, _)) = self.symbol_table.lookup_symbol(name) {
                            let entry = self.symbol_table.get_symbol_entry(entry_ref);
                            let current_node = self.ast.get_node(expr_ref);
                            current_node.resolved_type.set(Some(entry.type_info));
                        }
                        return Operand::Copy(Box::new(Place::Global(*global_id)));
                    }
                }

                // Fallback to searching all symbol entries and local map if needed
                debug!("Fallback lookup for identifier '{}'", name);
                if let Some((entry_ref, scope_id)) = self.symbol_table.lookup_symbol(name) {
                    let entry = self.symbol_table.get_symbol_entry(entry_ref);
                    debug!(
                        "Found identifier '{}' in scope {} with kind {:?}",
                        name,
                        scope_id.get(),
                        entry.kind
                    );
                    if let Some(local_id) = self.local_map.get(&entry_ref) {
                        let current_node = self.ast.get_node(expr_ref);
                        current_node.resolved_type.set(Some(entry.type_info));
                        return Operand::Copy(Box::new(Place::Local(*local_id)));
                    } else if let SymbolKind::EnumConstant { value } = &entry.kind {
                        let val = *value;
                        let type_info = entry.type_info;
                        let const_id = self.create_constant(ConstValue::Int(val));
                        let current_node = self.ast.get_node(expr_ref);
                        current_node.resolved_type.set(Some(type_info));
                        return Operand::Constant(const_id);
                    } else if let SymbolKind::Function { .. } = &entry.kind {
                        // Function identifier - resolve to function address
                        debug!(
                            "Resolving function identifier '{}' to function address (fallback case)",
                            name
                        );

                        // Look up the function in MIR functions by name
                        if let Some(func_id) = self.find_mir_function_by_name(name) {
                            let current_node = self.ast.get_node(expr_ref);
                            current_node.resolved_type.set(Some(entry.type_info));
                            // Create a function address constant
                            let func_addr_const = ConstValue::FunctionAddress(func_id);
                            let const_id = self.create_constant(func_addr_const);
                            return Operand::Constant(const_id);
                        } else {
                            // Function not found in MIR, might be a forward declaration
                            debug!("Function '{}' found in symbol table but not in MIR functions", name);
                            // For now, return a dummy operand to allow compilation to continue
                            let error_const = self.create_constant(ConstValue::Int(0));
                            return Operand::Constant(error_const);
                        }
                    }
                }

                self.report_error(SemanticError::UndeclaredIdentifier {
                    name,
                    location: self.ast.get_node(expr_ref).span,
                });

                // Return a dummy operand to allow compilation to continue
                let error_const = self.create_constant(ConstValue::Int(0));
                Operand::Constant(error_const)
            }

            NodeKind::BinaryOp(op, left_ref, right_ref) => {
                debug!("Lowering binary operation: {:?}", op);

                // Special handling for assignment operations
                if matches!(
                    op,
                    BinaryOp::Assign
                        | BinaryOp::AssignAdd
                        | BinaryOp::AssignSub
                        | BinaryOp::AssignMul
                        | BinaryOp::AssignDiv
                        | BinaryOp::AssignMod
                        | BinaryOp::AssignBitAnd
                        | BinaryOp::AssignBitOr
                        | BinaryOp::AssignBitXor
                        | BinaryOp::AssignLShift
                        | BinaryOp::AssignRShift
                ) {
                    // This is an assignment operation, handle it specially
                    return self.lower_assignment_operation(op, left_ref, right_ref, expr_ref);
                }

                // Lower left and right operands
                let left_operand = self.lower_expression(left_ref);
                let right_operand = self.lower_expression(right_ref);

                // Get the source location for error reporting
                let node_span = self.ast.get_node(expr_ref).span;

                // For now, create dummy types for the operands
                // In a complete implementation, we would track operand types
                let left_type = self.get_int_type();
                let right_type = self.get_int_type();

                // Apply binary operand conversion
                match self.apply_binary_operand_conversion(
                    left_operand,
                    left_type,
                    right_operand,
                    right_type,
                    node_span,
                ) {
                    Ok((converted_left, converted_right, common_type)) => {
                        debug!(
                            "Applied binary operand conversion: {:?} -> {:?}, {:?} -> {:?}, common type: {:?}",
                            converted_left, left_type, converted_right, right_type, common_type
                        );

                        // Map AST BinaryOp to MIR BinaryOp
                        match self.map_ast_binary_op_to_mir(&op, node_span) {
                            Ok(mir_binary_op) => {
                                // Create a temporary local to store the result
                                let temp_local_id = self.mir_builder.create_local(None, common_type, false);

                                // Generate proper binary operation using Rvalue
                                let binary_rvalue = Rvalue::BinaryOp(mir_binary_op, converted_left, converted_right);
                                let assign_stmt = MirStmt::Assign(Place::Local(temp_local_id), binary_rvalue);
                                self.mir_builder.add_statement(assign_stmt);

                                // Return the local that contains the result
                                Operand::Copy(Box::new(Place::Local(temp_local_id)))
                            }
                            Err(error) => {
                                debug!("Binary operation mapping failed: {:?}", error);
                                self.report_error(error);
                                let error_const = self.create_constant(ConstValue::Int(0));
                                Operand::Constant(error_const)
                            }
                        }
                    }
                    Err(error) => {
                        debug!("Binary operand conversion failed: {:?}", error);

                        // Report error but continue with dummy operand
                        self.report_error(error);
                        let error_const = self.create_constant(ConstValue::Int(0));
                        Operand::Constant(error_const)
                    }
                }
            }

            NodeKind::UnaryOp(op, operand_ref) => {
                debug!("Lowering unary operation: {:?}", op);

                // Lower the operand first
                let operand = self.lower_expression(operand_ref);
                let node_span = self.ast.get_node(expr_ref).span;

                match op {
                    crate::ast::UnaryOp::Deref => {
                        // Pointer dereferencing: *operand
                        // The operand should be a pointer type, and we want to return
                        // a place that represents the dereferenced location

                        // Create a temporary local to store the result
                        let temp_type_id = self.get_int_type(); // For now, assume int type
                        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                        let temp_place = Place::Local(temp_local_id);

                        // Create a dereference operation: temp = *operand
                        let deref_rvalue = Rvalue::UnaryOp(crate::mir::UnaryOp::Deref, operand);
                        let assign_stmt = MirStmt::Assign(temp_place.clone(), deref_rvalue);
                        self.mir_builder.add_statement(assign_stmt);

                        // Return the local that contains the dereferenced value
                        Operand::Copy(Box::new(temp_place))
                    }
                    crate::ast::UnaryOp::AddrOf => {
                        // Address-of operation: &operand
                        // This should return a pointer to the operand

                        // For now, we'll handle the simple case where operand is a local variable
                        if let Operand::Copy(place_box) = operand {
                            let place = *place_box;
                            // Return the address of the place
                            Operand::AddressOf(Box::new(place))
                        } else {
                            // For other cases, return a dummy operand
                            self.report_error(SemanticError::NotAnLvalue { location: node_span });
                            let error_const = self.create_constant(ConstValue::Int(0));
                            Operand::Constant(error_const)
                        }
                    }
                    crate::ast::UnaryOp::Plus | crate::ast::UnaryOp::Minus => {
                        // Unary plus/minus operations
                        let unary_op = match op {
                            crate::ast::UnaryOp::Plus => crate::mir::UnaryOp::Neg, // Unary plus is like no-op
                            crate::ast::UnaryOp::Minus => crate::mir::UnaryOp::Neg,
                            _ => unreachable!(),
                        };

                        // Create a temporary local to store the result
                        let temp_type_id = self.get_int_type();
                        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                        let temp_place = Place::Local(temp_local_id);

                        // Create the unary operation: temp = op operand
                        let unary_rvalue = Rvalue::UnaryOp(unary_op, operand);
                        let assign_stmt = MirStmt::Assign(temp_place.clone(), unary_rvalue);
                        self.mir_builder.add_statement(assign_stmt);

                        // Return the local that contains the result
                        Operand::Copy(Box::new(temp_place))
                    }
                    crate::ast::UnaryOp::BitNot | crate::ast::UnaryOp::LogicNot => {
                        // Bitwise and logical NOT operations
                        let unary_op = match op {
                            crate::ast::UnaryOp::BitNot => crate::mir::UnaryOp::Not,
                            crate::ast::UnaryOp::LogicNot => crate::mir::UnaryOp::Not,
                            _ => unreachable!(),
                        };

                        // Create a temporary local to store the result
                        let temp_type_id = self.get_int_type();
                        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                        let temp_place = Place::Local(temp_local_id);

                        // Create the unary operation: temp = op operand
                        let unary_rvalue = Rvalue::UnaryOp(unary_op, operand);
                        let assign_stmt = MirStmt::Assign(temp_place.clone(), unary_rvalue);
                        self.mir_builder.add_statement(assign_stmt);

                        // Return the local that contains the result
                        Operand::Copy(Box::new(temp_place))
                    }
                    crate::ast::UnaryOp::PreIncrement | crate::ast::UnaryOp::PreDecrement => {
                        // Pre-increment and pre-decrement operations
                        // These operations:
                        // 1. Load the current value
                        // 2. Perform increment/decrement
                        // 3. Store result back to operand
                        // 4. Return the new value

                        // For pre-increment/decrement, the operand must be a place (lvalue)
                        let operand_place = match &operand {
                            Operand::Copy(place_box) => *place_box.clone(),
                            _ => {
                                // Operand is not a valid lvalue - report error
                                self.report_error(SemanticError::NotAnLvalue { location: node_span });
                                let error_const = self.create_constant(ConstValue::Int(0));
                                return Operand::Constant(error_const);
                            }
                        };

                        // Create a temporary local to store the result
                        let temp_type_id = self.get_int_type(); // For now, assume int type
                        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                        let temp_place = Place::Local(temp_local_id);

                        // Step 1: Load current value into temp: temp = operand
                        let load_rvalue = Rvalue::Use(operand.clone());
                        let load_stmt = MirStmt::Assign(temp_place.clone(), load_rvalue);
                        self.mir_builder.add_statement(load_stmt);

                        // Step 2: Perform increment/decrement on temp
                        let binary_op = match op {
                            crate::ast::UnaryOp::PreIncrement => MirBinaryOp::Add,
                            crate::ast::UnaryOp::PreDecrement => MirBinaryOp::Sub,
                            _ => unreachable!(),
                        };

                        // Create constant 1 for the operation
                        let one_const = self.create_constant(ConstValue::Int(1));
                        let one_operand = Operand::Constant(one_const);

                        // temp = temp +/- 1
                        let increment_rvalue =
                            Rvalue::BinaryOp(binary_op, Operand::Copy(Box::new(temp_place.clone())), one_operand);
                        let increment_stmt = MirStmt::Assign(temp_place.clone(), increment_rvalue);
                        self.mir_builder.add_statement(increment_stmt);

                        // Step 3: Store result back to operand: operand = temp
                        self.emit_assignment(operand_place, Operand::Copy(Box::new(temp_place.clone())), node_span);

                        // Step 4: Return the temp (which contains the new value)
                        Operand::Copy(Box::new(temp_place))
                    }
                }
            }

            NodeKind::FunctionCall(func_ref, args) => {
                debug!("Lowering function call expression with {} arguments", args.len());

                // Evaluate function arguments first
                let mut arg_operands = Vec::new();
                for arg_ref in args {
                    let arg_operand = self.lower_expression(arg_ref);
                    arg_operands.push(arg_operand);
                }

                // Handle different types of function call targets
                let func_node = self.ast.get_node(func_ref);

                match &func_node.kind {
                    NodeKind::Ident(name, _) => {
                        // Direct function call: foo()
                        debug!("Direct function call target: {}", name);
                        self.handle_direct_function_call(*name, arg_operands)
                    }
                    NodeKind::MemberAccess(object_ref, field_name, is_arrow) => {
                        // Function pointer call through member access: v.fptr() or v->fptr()
                        debug!(
                            "Function pointer call through member access: {}.{}() (is_arrow: {})",
                            field_name, field_name, is_arrow
                        );
                        self.handle_function_pointer_call(*object_ref, *field_name, *is_arrow, arg_operands)
                    }
                    _ => {
                        debug!("Unsupported function call target: {:?}", func_node.kind);
                        let dummy_const = self.create_constant(ConstValue::Int(0));
                        Operand::Constant(dummy_const)
                    }
                }
            }

            NodeKind::IndexAccess(array_ref, index_ref) => {
                debug!("Lowering array index access expression");

                // Lower the array expression
                let array_operand = self.lower_expression(array_ref);

                // Lower the index expression
                let index_operand = self.lower_expression(index_ref);

                // For array subscripting (a[b]), this is semantically equivalent to *(a + b)
                // We need to create a proper Place that represents the array element access
                // The result should be a Place that can be used as an lvalue

                // Create a Place::ArrayIndex to represent the array element access
                // This will be handled properly by the MIR code generation
                let array_place = match array_operand {
                    Operand::Copy(place_box) => *place_box,
                    _ => {
                        // If array is not a place, create a temporary to hold the computed address
                        let temp_type_id = self.get_int_type();
                        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                        let temp_place = Place::Local(temp_local_id);

                        // Store the array value in the temporary
                        let assign_stmt = MirStmt::Assign(temp_place.clone(), Rvalue::Use(array_operand));
                        self.mir_builder.add_statement(assign_stmt);

                        temp_place
                    }
                };

                // Create the array index place
                let index_place = Place::ArrayIndex(Box::new(array_place), Box::new(index_operand));

                // Return this as an operand that can be used as an lvalue
                Operand::Copy(Box::new(index_place))
            }

            NodeKind::Cast(type_ref, expr_ref) => {
                debug!("Lowering cast expression to type {:?}", type_ref);

                // Lower the expression being cast
                let expr_operand = self.lower_expression(expr_ref);

                // Convert the target type to MIR type
                let target_type_id = self.lower_type_to_mir(type_ref);

                // Create a cast operation
                // For now, we'll create a temporary local and assign the cast result to it
                let temp_local_id = self.mir_builder.create_local(None, target_type_id, false);
                let temp_place = Place::Local(temp_local_id);

                // Create the cast rvalue
                let cast_rvalue = Rvalue::Cast(target_type_id, expr_operand);
                let assign_stmt = MirStmt::Assign(temp_place.clone(), cast_rvalue);
                self.mir_builder.add_statement(assign_stmt);

                // Return the local that contains the cast result
                Operand::Copy(Box::new(temp_place))
            }

            NodeKind::MemberAccess(object_ref, field_name, is_arrow) => {
                debug!(
                    "Lowering member access expression for field: {} (is_arrow: {})",
                    field_name, is_arrow
                );

                // Lower the object expression to get the base place
                let object_operand = self.lower_expression(object_ref);

                // For member access (object.field or object->field), we need to create a proper Place
                // that represents the struct field access. The result should be a Place that can be used as an lvalue.

                let mut object_place = match object_operand {
                    Operand::Copy(place_box) => *place_box,
                    _ => {
                        // If object is not a place, create a temporary to hold the computed address
                        let temp_type_id = self.get_int_type();
                        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                        let temp_place = Place::Local(temp_local_id);

                        // Store the object value in the temporary
                        let assign_stmt = MirStmt::Assign(temp_place.clone(), Rvalue::Use(object_operand));
                        self.mir_builder.add_statement(assign_stmt);

                        temp_place
                    }
                };

                // Handle arrow access (object->field) by dereferencing the pointer first
                if is_arrow {
                    debug!("Handling arrow access, dereferencing pointer first");

                    // For arrow access, we need to dereference the pointer to get the struct
                    // Create a temporary to hold the dereferenced struct
                    let temp_type_id = self.get_int_type(); // For now, assume int type
                    let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                    let temp_place = Place::Local(temp_local_id);

                    // Dereference the pointer: temp = *object_place
                    let deref_operand = Operand::Copy(Box::new(object_place));
                    let deref_rvalue = Rvalue::UnaryOp(crate::mir::UnaryOp::Deref, deref_operand);
                    let assign_stmt = MirStmt::Assign(temp_place.clone(), deref_rvalue);
                    self.mir_builder.add_statement(assign_stmt);

                    // Update object_place to be the dereferenced struct
                    object_place = temp_place;
                }

                // Get the type of the object being accessed
                let object_node = self.ast.get_node(object_ref);
                let mut object_type_ref = object_node.resolved_type.get().or_else(|| {
                    // If type is not resolved, try to resolve it from the symbol table
                    debug!("Type not pre-resolved for object, attempting to resolve from symbol table");

                    // For identifiers, look up the symbol in the symbol table
                    if let NodeKind::Ident(name, _) = &object_node.kind {
                        debug!("Looking up symbol '{}' in symbol table", name);
                        if let Some((entry_ref, scope_id)) = self.symbol_table.lookup_symbol(*name) {
                            let entry = self.symbol_table.get_symbol_entry(entry_ref);
                            debug!(
                                "Found symbol '{}' in scope {} with type {:?}",
                                name,
                                scope_id.get(),
                                entry.type_info
                            );
                            debug!("Symbol kind: {:?}", entry.kind);
                            Some(entry.type_info)
                        } else {
                            debug!("Symbol '{}' not found in symbol table", name);
                            debug!("Current scope: {}", self.symbol_table.current_scope().get());
                            // List all symbols in current scope for debugging
                            let current_scope = self.symbol_table.get_scope(self.symbol_table.current_scope());
                            debug!(
                                "Symbols in current scope: {:?}",
                                current_scope.symbols.keys().collect::<Vec<_>>()
                            );
                            None
                        }
                    } else {
                        // For complex expressions like nested MemberAccess, we need to resolve the type
                        // by examining the structure of the expression
                        debug!("Object is a complex expression, attempting to resolve type from expression structure");
                        self.resolve_type_from_expression(object_ref)
                    }
                });

                // For arrow access, if the object type is a pointer, we need to dereference it
                // to get the actual struct type for field lookup
                if is_arrow && let Some(type_ref) = object_type_ref {
                    let object_ast_type = self.ast.get_type(type_ref);
                    if let crate::ast::TypeKind::Pointer { pointee } = &object_ast_type.kind {
                        // Canonicalize the pointee type to ensure it points to the complete struct definition
                        let canonical_pointee = self.canonicalize_type(*pointee);
                        object_type_ref = Some(canonical_pointee);
                    }
                }

                let Some(object_type_ref) = object_type_ref else {
                    // Cannot resolve object type - report error
                    let node_span = self.ast.get_node(expr_ref).span;
                    self.report_error(SemanticError::UndeclaredIdentifier {
                        name: field_name,
                        location: node_span,
                    });

                    let error_const = self.create_constant(ConstValue::Int(0));
                    return Operand::Constant(error_const);
                };

                debug!(
                    "Looking for field '{}' in object type {:?}",
                    field_name, object_type_ref
                );

                // Look for the field in the specific object type
                let field_index = {
                    let object_ast_type = self.ast.get_type(object_type_ref);

                    // Handle both struct and union types
                    match &object_ast_type.kind {
                        crate::ast::TypeKind::Record { members, is_union, .. } => {
                            debug!(
                                "Searching for field '{}' in {} with {} members",
                                field_name,
                                if *is_union { "union" } else { "struct" },
                                members.len()
                            );

                            // Debug: Print all member names for inspection
                            for (i, member) in members.iter().enumerate() {
                                debug!("Member {}: '{}'", i, member.name);
                            }

                            // Search for the field in the struct/union members
                            members.iter().position(|member| member.name == field_name)
                        }
                        _ => {
                            debug!("Object type is not a struct/union: {:?}", object_ast_type.kind);
                            None
                        }
                    }
                };

                if let Some(field_idx) = field_index {
                    // Create the struct field place
                    let field_place = Place::StructField(Box::new(object_place), field_idx);

                    // Set the resolved type for this MemberAccess node
                    let field_type = {
                        let object_ast_type = self.ast.get_type(object_type_ref);
                        if let crate::ast::TypeKind::Record { members, .. } = &object_ast_type.kind {
                            members[field_idx].member_type
                        } else {
                            self.get_int_type() // fallback
                        }
                    };

                    // Update the resolved_type field of the current node
                    let current_node = self.ast.get_node(expr_ref);
                    current_node.resolved_type.set(Some(field_type));

                    // Return this as an operand that can be used as an lvalue
                    Operand::Copy(Box::new(field_place))
                } else {
                    // Field not found - report error but continue with dummy operand
                    let node_span = self.ast.get_node(expr_ref).span;
                    self.report_error(SemanticError::UndeclaredIdentifier {
                        name: field_name,
                        location: node_span,
                    });

                    let error_const = self.create_constant(ConstValue::Int(0));
                    Operand::Constant(error_const)
                }
            }

            _ => {
                // For unsupported expressions, return a dummy operand
                let node = self.ast.get_node(expr_ref);
                debug!("Unsupported expression type: {:?}", node.kind);
                let error_const = self.create_constant(ConstValue::Int(0));
                Operand::Constant(error_const)
            }
        }
    }

    /// Lower a return statement
    fn lower_return_statement(&mut self, expr: &Option<NodeRef>, _location: SourceSpan) {
        // Check if we're in a void function
        if let Some(current_func_id) = self.current_function
            && let Some(func) = self.mir_builder.get_functions().get(&current_func_id)
            && let Some(return_type_id) = self.get_types().get(&func.return_type)
            && matches!(return_type_id, crate::mir::MirType::Void)
        {
            // We're in a void function - return statement should not have any operand
            self.mir_builder.set_terminator(Terminator::Return(None));
            return;
        }

        // For non-void functions, handle the return expression normally
        if let Some(expr_ref) = expr {
            let operand = self.lower_expression(*expr_ref);
            self.mir_builder.set_terminator(Terminator::Return(Some(operand)));
        } else {
            self.mir_builder.set_terminator(Terminator::Return(None));
        }
    }

    /// Lower an if statement
    fn lower_if_statement(&mut self, if_stmt: &IfStmt, _location: SourceSpan) {
        debug!("Lowering if statement");

        // Create blocks for then and else branches
        let then_block = self.mir_builder.create_block();
        let else_block_id = if if_stmt.else_branch.is_some() {
            Some(self.mir_builder.create_block())
        } else {
            None
        };

        // Lower the condition expression to an operand
        let cond_operand = self.lower_expression(if_stmt.condition);

        // Determine the block for the false case
        let false_block = if let Some(else_id) = else_block_id {
            else_id
        } else {
            self.mir_builder.create_block()
        };

        // Set the terminator for the current block
        self.mir_builder
            .set_terminator(Terminator::If(cond_operand, then_block, false_block));

        // Process the then branch
        self.mir_builder.set_current_block(then_block);
        self.lower_node_ref(if_stmt.then_branch);
        let then_block_has_terminator = self.mir_builder.current_block_has_terminator();

        // Process the else branch if it exists
        let else_block_has_terminator = if let Some(else_id) = else_block_id {
            self.mir_builder.set_current_block(else_id);
            if let Some(else_branch) = &if_stmt.else_branch {
                self.lower_node_ref(*else_branch);
            }
            self.mir_builder.current_block_has_terminator()
        } else {
            false
        };

        // Determine if we need a merge block and setup continuation
        if let Some(else_id) = else_block_id {
            if then_block_has_terminator && else_block_has_terminator {
                // Both branches terminate, no merge block needed for continuation
                // But we should probably invalidate the current block to avoid accidental spill
                self.current_block = None;
            } else {
                // At least one branch falls through, create merge block
                let merge_block = self.mir_builder.create_block();

                // Ensure both branches have terminators going to merge
                if !then_block_has_terminator {
                    self.mir_builder.set_current_block(then_block);
                    self.mir_builder.set_terminator(Terminator::Goto(merge_block));
                }

                if !else_block_has_terminator {
                    self.mir_builder.set_current_block(else_id);
                    self.mir_builder.set_terminator(Terminator::Goto(merge_block));
                }

                // Set current block to merge block for continuation
                self.mir_builder.set_current_block(merge_block);
                self.current_block = Some(merge_block);
            }
        } else {
            // No else branch. false_block serves as the skip/merge block.
            if !then_block_has_terminator {
                // Then branch falls through, link it to the false/merge block
                self.mir_builder.set_current_block(then_block);
                self.mir_builder.set_terminator(Terminator::Goto(false_block));
            }

            // Always continue from the false_block (which is the skip/merge point)
            self.mir_builder.set_current_block(false_block);
            self.current_block = Some(false_block);
        }
    }

    /// Lower a while statement
    fn lower_while_statement(&mut self, while_stmt: &WhileStmt, _location: SourceSpan) {
        debug!("Lowering while statement");

        // Create blocks for condition check, body, and continuation
        let condition_block = self.mir_builder.create_block();
        let body_block = self.mir_builder.create_block();
        let continue_block = self.mir_builder.create_block();

        // Jump from current block to condition check
        self.mir_builder.set_terminator(Terminator::Goto(condition_block));

        // Set up condition block
        self.mir_builder.set_current_block(condition_block);
        self.current_block = Some(condition_block);

        // Lower the condition expression to an operand
        let cond_operand = self.lower_expression(while_stmt.condition);

        // Set terminator for condition block: if condition is true, go to body; else go to continue
        self.mir_builder
            .set_terminator(Terminator::If(cond_operand, body_block, continue_block));

        // Set up body block
        self.mir_builder.set_current_block(body_block);
        self.current_block = Some(body_block);

        // Process the body of the while loop
        self.lower_node_ref(while_stmt.body);

        // After body execution, jump back to condition check
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(condition_block));
        }

        // Set current block to continue block for code after the loop
        self.mir_builder.set_current_block(continue_block);
        self.current_block = Some(continue_block);
    }

    /// Lower a do-while statement
    fn lower_do_while_statement(&mut self, body_ref: NodeRef, condition_ref: NodeRef, _location: SourceSpan) {
        debug!("Lowering do-while statement");

        // Create blocks for body, condition check, and continuation
        let body_block = self.mir_builder.create_block();
        let condition_block = self.mir_builder.create_block();
        let continue_block = self.mir_builder.create_block();

        // Jump from current block to body (do-while executes body first)
        self.mir_builder.set_terminator(Terminator::Goto(body_block));

        // Set up body block
        self.mir_builder.set_current_block(body_block);
        self.current_block = Some(body_block);

        // Process the body of the do-while loop
        self.lower_node_ref(body_ref);

        // After body execution, jump to condition check
        if !self.mir_builder.current_block_has_terminator() {
            self.mir_builder.set_terminator(Terminator::Goto(condition_block));
        }

        // Set up condition block
        self.mir_builder.set_current_block(condition_block);
        self.current_block = Some(condition_block);

        // Lower the condition expression to an operand
        let cond_operand = self.lower_expression(condition_ref);

        // Set terminator for condition block: if condition is true, go back to body; else go to continue
        self.mir_builder
            .set_terminator(Terminator::If(cond_operand, body_block, continue_block));

        // Set current block to continue block for code after the loop
        self.mir_builder.set_current_block(continue_block);
        self.current_block = Some(continue_block);
    }

    /// Lower an assignment operation
    fn lower_assignment_operation(
        &mut self,
        op: BinaryOp,
        left_ref: NodeRef,
        right_ref: NodeRef,
        expr_ref: NodeRef,
    ) -> Operand {
        debug!("Lowering assignment operation: {:?}", op);

        // Lower the left-hand side to get the place to assign to
        let left_operand = self.lower_expression(left_ref);

        // For assignment operations, the left operand should be a place (variable, field access, etc.)
        // that we can assign to. We need to extract the Place from the Operand.
        let place = match left_operand {
            Operand::Copy(place_box) => *place_box,
            _ => {
                // Left operand is not a valid lvalue - report error
                let node_span = self.ast.get_node(expr_ref).span;
                self.report_error(SemanticError::NotAnLvalue { location: node_span });
                // Return a dummy operand to allow compilation to continue
                let error_const = self.create_constant(ConstValue::Int(0));
                return Operand::Constant(error_const);
            }
        };

        // Lower the right-hand side
        let right_operand = self.lower_expression(right_ref);

        // Get the source location for error reporting
        let node_span = self.ast.get_node(expr_ref).span;

        // For assignment operations, we need to handle the different types:
        // - Simple assignment (=)
        // - Compound assignments (+=, -=, etc.)
        match op {
            BinaryOp::Assign => {
                // Simple assignment: left = right
                self.emit_assignment(place, right_operand.clone(), node_span);
                // Return the assigned value (for chained assignments like a = b = c)
                right_operand
            }
            BinaryOp::AssignAdd => {
                // Compound assignment: left += right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::Add, node_span)
            }
            BinaryOp::AssignSub => {
                // Compound assignment: left -= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::Sub, node_span)
            }
            BinaryOp::AssignMul => {
                // Compound assignment: left *= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::Mul, node_span)
            }
            BinaryOp::AssignDiv => {
                // Compound assignment: left /= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::Div, node_span)
            }
            BinaryOp::AssignMod => {
                // Compound assignment: left %= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::Mod, node_span)
            }
            BinaryOp::AssignBitAnd => {
                // Compound assignment: left &= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::BitAnd, node_span)
            }
            BinaryOp::AssignBitOr => {
                // Compound assignment: left |= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::BitOr, node_span)
            }
            BinaryOp::AssignBitXor => {
                // Compound assignment: left ^= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::BitXor, node_span)
            }
            BinaryOp::AssignLShift => {
                // Compound assignment: left <<= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::LShift, node_span)
            }
            BinaryOp::AssignRShift => {
                // Compound assignment: left >>= right

                self.lower_compound_assignment(place, right_operand, MirBinaryOp::RShift, node_span)
            }
            _ => {
                unreachable!("This should not happen as we already matched assignment operations");
            }
        }
    }

    /// Lower a compound assignment operation (like +=, -=, etc.)
    fn lower_compound_assignment(
        &mut self,
        place: Place,
        right_operand: Operand,
        binary_op: MirBinaryOp,
        location: SourceSpan,
    ) -> Operand {
        debug!("Lowering compound assignment with operation: {:?}", binary_op);

        // First, load the current value from the place
        let current_value = Operand::Copy(Box::new(place.clone()));

        // Create a temporary local to store the result
        let temp_type_id = self.get_int_type(); // For now, assume int type
        let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
        let temp_place = Place::Local(temp_local_id);

        // Perform the binary operation: temp = current_value OP right_operand
        let binary_rvalue = Rvalue::BinaryOp(binary_op, current_value, right_operand);
        let assign_stmt = MirStmt::Assign(temp_place.clone(), binary_rvalue);
        self.mir_builder.add_statement(assign_stmt);

        // Assign the result back to the original place: left = temp
        self.emit_assignment(place, Operand::Copy(Box::new(temp_place.clone())), location);

        // Return the assigned value (for chained assignments)
        Operand::Copy(Box::new(temp_place))
    }

    /// Emit an assignment statement
    fn emit_assignment(&mut self, place: Place, operand: Operand, _location: SourceSpan) {
        // Check if current block is already terminated (unreachable code)
        if self.mir_builder.current_block_has_terminator() {
            debug!("Skipping unreachable assignment statement");
            return;
        }

        let rvalue = Rvalue::Use(operand);
        let stmt = MirStmt::Assign(place, rvalue);

        // Use the public add_statement method
        let _stmt_id = self.mir_builder.add_statement(stmt);
        debug!("Emitted assignment statement");
    }

    /// Lower a type reference to MIR type
    fn lower_type_to_mir(&mut self, type_ref: TypeRef) -> TypeId {
        // Clone the AST type to avoid borrow conflicts
        let ast_type = self.ast.get_type(type_ref).clone();

        debug!("Converting AST type to MIR: {:?}", ast_type.kind);

        match ast_type.kind {
            crate::ast::TypeKind::Int { is_signed } => {
                let mir_type = crate::mir::MirType::Int { is_signed, width: 32 };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Void => {
                let mir_type = crate::mir::MirType::Void;
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Char { is_signed } => {
                let mir_type = crate::mir::MirType::Int { is_signed, width: 8 };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Short { is_signed } => {
                let mir_type = crate::mir::MirType::Int { is_signed, width: 16 };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Long {
                is_signed,
                is_long_long,
            } => {
                // Handle both long and long long
                let width = if is_long_long { 64 } else { 32 };
                let mir_type = crate::mir::MirType::Int { is_signed, width };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Float => {
                let mir_type = crate::mir::MirType::Float { width: 32 };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Double { is_long_double } => {
                // Handle both double and long double
                let width = if is_long_double { 80 } else { 64 };
                let mir_type = crate::mir::MirType::Float { width };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Pointer { pointee } => {
                // Convert the pointee type first
                let pointee_type_id = self.lower_type_to_mir(pointee);
                let mir_type = crate::mir::MirType::Pointer {
                    pointee: pointee_type_id,
                };
                self.add_type(mir_type)
            }
            crate::ast::TypeKind::Record {
                tag, members, is_union, ..
            } => {
                debug!("Converting Record type with {} members to MIR", members.len());
                // Convert struct/union members to MIR format
                let mut mir_fields = Vec::new();
                for member in members {
                    let field_type_id = self.lower_type_to_mir(member.member_type);
                    mir_fields.push((member.name, field_type_id));
                }

                let type_name =
                    tag.unwrap_or_else(|| Symbol::new(format!("anon_{}", if is_union { "union" } else { "struct" })));
                debug!(
                    "Created MIR type for struct '{}' with {} fields",
                    type_name,
                    mir_fields.len()
                );

                let mir_type = if is_union {
                    crate::mir::MirType::Union {
                        name: type_name,
                        fields: mir_fields,
                    }
                } else {
                    crate::mir::MirType::Struct {
                        name: type_name,
                        fields: mir_fields,
                    }
                };

                self.add_type(mir_type)
            }
            _ => {
                // Default to int for unsupported types
                self.get_int_type()
            }
        }
    }

    /// Create a constant value
    fn create_constant(&mut self, value: ConstValue) -> ConstValueId {
        self.mir_builder.create_constant(value)
    }

    /// Add a type to the MIR module
    fn add_type(&mut self, mir_type: crate::mir::MirType) -> TypeId {
        self.mir_builder.add_type(mir_type)
    }

    /// Get the default int type
    fn get_int_type(&mut self) -> TypeId {
        let mir_type = crate::mir::MirType::Int {
            is_signed: true,
            width: 32,
        };
        self.add_type(mir_type)
    }

    /// Get functions for validation
    pub fn get_functions(&self) -> &HashMap<MirFunctionId, MirFunction> {
        self.mir_builder.get_functions()
    }

    /// Get blocks for validation
    pub fn get_blocks(&self) -> &HashMap<MirBlockId, MirBlock> {
        self.mir_builder.get_blocks()
    }

    /// Get locals for validation
    pub fn get_locals(&self) -> &HashMap<LocalId, Local> {
        self.mir_builder.get_locals()
    }

    /// Get globals for validation
    pub fn get_globals(&self) -> &HashMap<mir::GlobalId, mir::Global> {
        self.mir_builder.get_globals()
    }

    /// Get types for validation
    pub fn get_types(&self) -> &HashMap<TypeId, crate::mir::MirType> {
        self.mir_builder.get_types()
    }

    /// Get statements for validation
    pub fn get_statements(&self) -> &HashMap<crate::mir::MirStmtId, crate::mir::MirStmt> {
        self.mir_builder.get_statements()
    }

    /// Get constants for validation
    pub fn get_constants(&self) -> &HashMap<crate::mir::ConstValueId, crate::mir::ConstValue> {
        self.mir_builder.get_constants()
    }

    /// Lower a goto statement
    fn lower_goto_statement(&mut self, label: Symbol, location: SourceSpan) {
        debug!("Lowering goto statement to label: {}", label);

        // For goto statements, we need to set up a jump to the target label
        // However, we might not know the target block ID yet if labels come after
        // For now, create a temporary placeholder and resolve later

        // Look up the label in our label map
        if let Some(target_block_id) = self.label_map.get(&label) {
            // Check if current block is already terminated
            if self.mir_builder.current_block_has_terminator() {
                // Current block is already terminated, create a new block for this goto
                debug!("Current block already terminated, creating new block for goto");
                let new_block_id = self.mir_builder.create_block();
                self.mir_builder.set_current_block(new_block_id);
                self.current_block = Some(new_block_id);
            }

            // Set terminator to jump to the target block
            self.mir_builder.set_terminator(Terminator::Goto(*target_block_id));
            debug!("Goto resolved to block {:?}", target_block_id);
        } else {
            // Label not found - this is an error
            debug!("Label '{}' not found in label map during goto resolution", label);
            self.report_error(SemanticError::UndeclaredIdentifier { name: label, location });
            // Set a dummy terminator to allow compilation to continue
            self.mir_builder.set_terminator(Terminator::Unreachable);
        }
    }

    /// Lower a label statement
    fn lower_label_statement(&mut self, label: Symbol, statement: NodeRef, _location: SourceSpan) {
        // Get the existing block for this label (created in first pass)
        if let Some(&target_block_id) = self.label_map.get(&label) {
            // Switch to the existing block for the label's statement
            self.mir_builder.set_current_block(target_block_id);
            self.current_block = Some(target_block_id);

            // Process the statement that follows the label
            self.lower_node_ref(statement);
        } else {
            // This path should be unreachable. After the refactoring of `collect_labels_recursive`,
            // all labels, including consecutive ones, are mapped to a block in the first pass.
            // If we hit this else, it indicates a bug in the label collection logic.
            panic!("Unmapped label '{}' found during lowering", label);
        }
    }

    /// Find a struct/union field by name and return its index
    fn find_struct_field(&self, type_id: TypeId, field_name: Symbol) -> Option<usize> {
        let mir_type = self.get_types().get(&type_id)?;

        debug!("Looking for field '{}' in type {:?}", field_name, mir_type);

        match mir_type {
            crate::mir::MirType::Struct { fields, .. } | crate::mir::MirType::Union { fields, .. } => {
                let field_index = fields.iter().position(|(name, _)| *name == field_name);
                debug!("Field '{}' found at index {:?}", field_name, field_index);
                field_index
            }
            _ => {
                debug!("Type {:?} is not a struct/union", mir_type);
                None
            }
        }
    }

    /// Get the type ID of a struct/union field by index
    fn get_struct_field_type(&self, type_id: TypeId, field_index: usize) -> Option<TypeId> {
        let mir_type = self.get_types().get(&type_id)?;

        match mir_type {
            crate::mir::MirType::Struct { fields, .. } | crate::mir::MirType::Union { fields, .. } => {
                fields.get(field_index).map(|(_, field_type)| *field_type)
            }
            _ => None,
        }
    }

    /// Get the element type of an array
    fn get_array_element_type(&self, type_id: TypeId) -> Option<TypeId> {
        let mir_type = self.get_types().get(&type_id)?;

        match mir_type {
            crate::mir::MirType::Array { element, .. } => Some(*element),
            _ => None,
        }
    }

    /// Canonicalize a type reference - resolve incomplete types to their complete definitions
    /// This is similar to how Clang handles type canonicalization
    fn canonicalize_type(&mut self, type_ref: TypeRef) -> TypeRef {
        // Clone the type to avoid borrow issues
        let ast_type = self.ast.get_type(type_ref).clone();

        match ast_type.kind {
            crate::ast::TypeKind::Record {
                tag,
                members: _,
                is_complete,
                ..
            } => {
                // If the record is already complete, return the original type
                if is_complete {
                    return type_ref;
                }

                // If incomplete, try to find the complete definition in the current scope hierarchy
                if let Some(tag_name) = tag
                    && let Some((entry_ref, _)) = self.symbol_table.lookup_tag(tag_name)
                {
                    let entry = self.symbol_table.get_symbol_entry(entry_ref);
                    if entry.is_completed {
                        debug!(
                            "Found complete definition for {:?} via symbol table, canonicalizing {} to {}",
                            tag_name,
                            type_ref.get(),
                            entry.type_info.get()
                        );
                        return entry.type_info;
                    }
                }

                // If no complete definition found, return the original type
                debug!("No complete definition found for type, returning original");
                type_ref
            }
            crate::ast::TypeKind::Pointer { pointee } => {
                // For pointer types, canonicalize the pointee type
                let canonical_pointee = self.canonicalize_type(pointee);
                if canonical_pointee != pointee {
                    // Create a new pointer type with the canonical pointee
                    let canonical_pointer_type = crate::ast::Type::new(crate::ast::TypeKind::Pointer {
                        pointee: canonical_pointee,
                    });
                    self.ast.push_type(canonical_pointer_type)
                } else {
                    // Even if pointee didn't change, we need to check if this pointer type
                    // should be updated to point to a complete struct definition
                    let pointee_ast_type = self.ast.get_type(pointee);
                    if let crate::ast::TypeKind::Record { tag, .. } = &pointee_ast_type.kind
                        && let Some(tag_name) = tag
                    {
                        // Look for a complete struct with the same tag
                        for (i, complete_type_candidate) in self.ast.types.iter().enumerate() {
                            if let crate::ast::TypeKind::Record {
                                tag: candidate_tag,
                                members: candidate_members,
                                is_complete: candidate_is_complete,
                                ..
                            } = &complete_type_candidate.kind
                                && Some(*tag_name) == *candidate_tag
                                && *candidate_is_complete
                                && !candidate_members.is_empty()
                                && pointee.get() != (i + 1) as u32
                            {
                                let complete_struct_ref = crate::ast::TypeRef::new((i + 1) as u32).unwrap();
                                let updated_pointer_type = crate::ast::Type::new(crate::ast::TypeKind::Pointer {
                                    pointee: complete_struct_ref,
                                });
                                return self.ast.push_type(updated_pointer_type);
                            }
                        }
                    }
                    type_ref
                }
            }
            _ => {
                // For non-record types, return as-is
                type_ref
            }
        }
    }

    /// Check if a type is arithmetic (integer or floating-point)
    fn is_arithmetic_type(&self, type_id: TypeId) -> bool {
        if let Some(mir_type) = self.get_types().get(&type_id) {
            matches!(
                mir_type,
                crate::mir::MirType::Int { .. } | crate::mir::MirType::Float { .. }
            )
        } else {
            false
        }
    }

    /// Check if a type is integer
    fn is_integer_type(&self, type_id: TypeId) -> bool {
        if let Some(mir_type) = self.get_types().get(&type_id) {
            matches!(mir_type, crate::mir::MirType::Int { .. })
        } else {
            false
        }
    }

    /// Apply binary operand type conversion following C11 standard rules.
    ///
    /// This function implements:
    /// - Integer promotions (C11 6.3.1.1)
    /// - Usual arithmetic conversions (C11 6.3.1.8)
    /// - Pointer arithmetic conversions
    /// - Comprehensive error handling
    ///
    /// # Arguments
    /// * `left` - Left operand
    /// * `left_type` - Type of left operand
    /// * `right` - Right operand  
    /// * `right_type` - Type of right operand
    /// * `location` - Source location for error reporting
    ///
    /// # Returns
    /// Returns a tuple of (converted_left, converted_right, common_type) or an error
    fn apply_binary_operand_conversion(
        &mut self,
        left: Operand,
        left_type: TypeId,
        right: Operand,
        right_type: TypeId,
        location: SourceSpan,
    ) -> Result<(Operand, Operand, TypeId), SemanticError> {
        debug!(
            "Applying binary operand conversion: {:?} : {:?} and {:?} : {:?}",
            left, left_type, right, right_type
        );

        // Input validation
        if let Some(left_mir_type) = self.get_types().get(&left_type)
            && matches!(left_mir_type, crate::mir::MirType::Void)
        {
            return Err(SemanticError::InvalidUseOfVoid { location });
        }

        if let Some(right_mir_type) = self.get_types().get(&right_type)
            && matches!(right_mir_type, crate::mir::MirType::Void)
        {
            return Err(SemanticError::InvalidUseOfVoid { location });
        }

        // Get MIR types for both operands
        let (left_mir_type, right_mir_type) =
            match (self.get_types().get(&left_type), self.get_types().get(&right_type)) {
                (Some(left_type), Some(right_type)) => (left_type.clone(), right_type.clone()),
                _ => {
                    // This case should ideally not be reached if types are well-formed.
                    // Fallback to a generic error message if types are not found.
                    return Err(SemanticError::InvalidBinaryOperands {
                        left_ty: "unknown".to_string(),
                        right_ty: "unknown".to_string(),
                        location,
                    });
                }
            };

        // Handle arithmetic type conversions
        if self.is_arithmetic_type(left_type) && self.is_arithmetic_type(right_type) {
            let (converted_left, converted_right, common_type) = self.apply_arithmetic_conversions(
                left,
                left_type,
                right,
                right_type,
                &left_mir_type,
                &right_mir_type,
                location,
            )?;

            Ok((converted_left, converted_right, common_type))
        } else if self.is_pointer_type(left_type) && self.is_pointer_type(right_type) {
            // Pointer equality comparisons
            let (converted_left, converted_right, common_type) = self.apply_pointer_conversions(
                left,
                left_type,
                right,
                right_type,
                &left_mir_type,
                &right_mir_type,
                location,
            )?;

            Ok((converted_left, converted_right, common_type))
        } else if self.is_pointer_type(left_type) && self.is_integer_type(right_type) {
            // Pointer + integer operations
            let (converted_left, converted_right, common_type) = self.apply_pointer_integer_conversions(
                left,
                left_type,
                right,
                right_type,
                &left_mir_type,
                &right_mir_type,
                location,
            )?;

            Ok((converted_left, converted_right, common_type))
        } else if self.is_integer_type(left_type) && self.is_pointer_type(right_type) {
            // Integer + pointer operations
            let (converted_left, converted_right, common_type) = self.apply_integer_pointer_conversions(
                left,
                left_type,
                right,
                right_type,
                &left_mir_type,
                &right_mir_type,
                location,
            )?;

            Ok((converted_left, converted_right, common_type))
        } else {
            // Invalid combination
            Err(SemanticError::InvalidBinaryOperands {
                left_ty: format!("{:?}", left_mir_type),
                right_ty: format!("{:?}", right_mir_type),
                location,
            })
        }
    }

    /// Helper function to check if a type is a pointer type
    fn is_pointer_type(&self, type_id: TypeId) -> bool {
        if let Some(mir_type) = self.get_types().get(&type_id) {
            matches!(mir_type, crate::mir::MirType::Pointer { .. })
        } else {
            false
        }
    }

    /// Apply arithmetic type conversions (C11 6.3.1.8)
    fn apply_arithmetic_conversions(
        &mut self,
        left: Operand,
        left_type: TypeId,
        right: Operand,
        right_type: TypeId,
        left_mir_type: &crate::mir::MirType,
        right_mir_type: &crate::mir::MirType,
        location: SourceSpan,
    ) -> Result<(Operand, Operand, TypeId), SemanticError> {
        debug!(
            "Applying arithmetic conversions: {:?} : {:?} and {:?} : {:?}",
            left, left_mir_type, right, right_mir_type
        );

        // Apply integer promotions first (C11 6.3.1.1)
        let (promoted_left, promoted_left_type) = self.apply_integer_promotions(left, left_type, location)?;
        let (promoted_right, promoted_right_type) = self.apply_integer_promotions(right, right_type, location)?;

        // Get promoted types
        let (promoted_left_mir_type, promoted_right_mir_type) = match (
            self.get_types().get(&promoted_left_type),
            self.get_types().get(&promoted_right_type),
        ) {
            (Some(left_type), Some(right_type)) => (left_type.clone(), right_type.clone()),
            _ => unreachable!(), // Should not happen as we just created these types
        };

        // Check if both are the same type
        if promoted_left_type == promoted_right_type {
            return Ok((promoted_left, promoted_right, promoted_left_type));
        }

        // Apply usual arithmetic conversions
        let common_type =
            self.find_common_arithmetic_type(&promoted_left_mir_type, &promoted_right_mir_type, location)?;

        // Convert operands to common type
        let converted_left = if promoted_left_type == common_type {
            promoted_left
        } else {
            Operand::Cast(common_type, Box::new(promoted_left))
        };

        let converted_right = if promoted_right_type == common_type {
            promoted_right
        } else {
            Operand::Cast(common_type, Box::new(promoted_right))
        };

        debug!(
            "Arithmetic conversion result: common_type = {:?}",
            self.get_types().get(&common_type)
        );

        Ok((converted_left, converted_right, common_type))
    }

    /// Apply integer promotions (C11 6.3.1.1)
    fn apply_integer_promotions(
        &mut self,
        operand: Operand,
        operand_type: TypeId,
        location: SourceSpan,
    ) -> Result<(Operand, TypeId), SemanticError> {
        let mir_type = self.get_types().get(&operand_type).cloned();
        if let Some(mir_type) = mir_type {
            match mir_type {
                crate::mir::MirType::Int { is_signed, width } => {
                    // Integer promotions: if int can represent all values of the original type,
                    // convert to int; otherwise convert to unsigned int
                    if width < 32 {
                        let promoted_type = if is_signed {
                            self.get_int_type_with_width(32, true)
                        } else {
                            self.get_int_type_with_width(32, false)
                        };

                        debug!(
                            "Integer promotion: {:?} -> {:?}",
                            &mir_type,
                            self.get_types().get(&promoted_type)
                        );

                        Ok((Operand::Cast(promoted_type, Box::new(operand)), promoted_type))
                    } else {
                        // Already large enough, no promotion needed
                        Ok((operand, operand_type))
                    }
                }
                _ => {
                    // Non-integer arithmetic types, no promotion
                    Ok((operand, operand_type))
                }
            }
        } else {
            Err(SemanticError::TypeMismatch {
                expected: "integer type".to_string(),
                found: "unknown".to_string(),
                location,
            })
        }
    }

    /// Find common arithmetic type using C11 usual arithmetic conversions
    fn find_common_arithmetic_type(
        &mut self,
        left_type: &crate::mir::MirType,
        right_type: &crate::mir::MirType,
        location: SourceSpan,
    ) -> Result<TypeId, SemanticError> {
        debug!(
            "Finding common arithmetic type for {:?} and {:?}",
            left_type, right_type
        );

        // Handle floating point types
        match (left_type, right_type) {
            (crate::mir::MirType::Float { .. }, crate::mir::MirType::Float { .. }) => {
                // Both float -> result is float
                Ok(self.get_float_type(32))
            }
            (crate::mir::MirType::Float { .. }, _) | (_, crate::mir::MirType::Float { .. }) => {
                // Any float with other type -> result is double
                Ok(self.get_float_type(64))
            }
            _ => {
                // Both are integer types, apply integer conversion rules
                self.find_common_integer_type(left_type, right_type, location)
            }
        }
    }

    /// Find common integer type for integer conversion rules
    fn find_common_integer_type(
        &mut self,
        left_type: &crate::mir::MirType,
        right_type: &crate::mir::MirType,
        location: SourceSpan,
    ) -> Result<TypeId, SemanticError> {
        let (left_is_signed, left_width) = match left_type {
            crate::mir::MirType::Int { is_signed, width } => (*is_signed, *width),
            _ => unreachable!(), // Should only be called with integer types
        };

        let (right_is_signed, right_width) = match right_type {
            crate::mir::MirType::Int { is_signed, width } => (*is_signed, *width),
            _ => unreachable!(),
        };

        // C11 usual arithmetic conversions for integers:
        // 1. If both have same signedness and width -> that type
        // 2. If one is wider than the other -> wider type
        // 3. If both signed and same width -> that type
        // 4. If unsigned is at least as wide as signed -> unsigned type
        // 5. If signed is wider than unsigned -> signed type
        // 6. Otherwise -> unsigned type with width of signed type

        if left_width == right_width && left_is_signed == right_is_signed {
            // Same signedness and width -> that type
            Ok(self.get_int_type_with_width(left_width, left_is_signed))
        } else if left_width > right_width {
            // Left is wider
            Ok(self.get_int_type_with_width(left_width, left_is_signed))
        } else if right_width > left_width {
            // Right is wider
            Ok(self.get_int_type_with_width(right_width, right_is_signed))
        } else {
            // Same width, different signedness
            if left_is_signed && !right_is_signed {
                // Left signed, right unsigned
                // If unsigned >= signed in range -> unsigned
                // Otherwise -> signed
                if self.is_unsigned_at_least_as_wide_as_signed(left_width) {
                    Ok(self.get_int_type_with_width(left_width, false))
                } else {
                    Ok(self.get_int_type_with_width(left_width, true))
                }
            } else if !left_is_signed && right_is_signed {
                // Left unsigned, right signed
                if self.is_unsigned_at_least_as_wide_as_signed(left_width) {
                    Ok(self.get_int_type_with_width(left_width, false))
                } else {
                    Ok(self.get_int_type_with_width(left_width, true))
                }
            } else {
                // Shouldn't happen due to earlier checks
                Err(SemanticError::InvalidBinaryOperands {
                    left_ty: format!("{:?}", left_type),
                    right_ty: format!("{:?}", right_type),
                    location,
                })
            }
        }
    }

    /// Check if unsigned type of given width can represent all values of signed type
    fn is_unsigned_at_least_as_wide_as_signed(&self, width: u8) -> bool {
        // For a given width, unsigned can represent [0, 2^width - 1]
        // Signed can represent [-2^(width-1), 2^(width-1) - 1]
        // Unsigned is at least as wide if 2^width - 1 >= 2^(width-1) - 1
        // This simplifies to: width >= 1 (which is always true for our purposes)
        // But we need to be more conservative for smaller widths
        width >= 16 // Conservative threshold
    }

    /// Apply pointer type conversions
    fn apply_pointer_conversions(
        &mut self,
        left: Operand,
        left_type: TypeId,
        right: Operand,
        right_type: TypeId,
        _left_mir_type: &crate::mir::MirType,
        _right_mir_type: &crate::mir::MirType,
        _location: SourceSpan,
    ) -> Result<(Operand, Operand, TypeId), SemanticError> {
        // For pointer equality comparisons, we can use either type
        // but prefer void* for compatibility
        let common_type = self.get_void_pointer_type();

        let converted_left = if left_type == common_type {
            left
        } else {
            Operand::Cast(common_type, Box::new(left))
        };

        let converted_right = if right_type == common_type {
            right
        } else {
            Operand::Cast(common_type, Box::new(right))
        };

        Ok((converted_left, converted_right, common_type))
    }

    /// Apply pointer-integer conversions
    fn apply_pointer_integer_conversions(
        &mut self,
        left: Operand,
        left_type: TypeId,
        right: Operand,
        right_type: TypeId,
        _left_mir_type: &crate::mir::MirType,
        _right_mir_type: &crate::mir::MirType,
        _location: SourceSpan,
    ) -> Result<(Operand, Operand, TypeId), SemanticError> {
        // Pointer + integer -> pointer type (with integer promoted if needed)
        let (promoted_right, _promoted_right_type) = self.apply_integer_promotions(right, right_type, _location)?;

        Ok((left, promoted_right, left_type))
    }

    /// Apply integer-pointer conversions
    fn apply_integer_pointer_conversions(
        &mut self,
        left: Operand,
        left_type: TypeId,
        right: Operand,
        right_type: TypeId,
        _left_mir_type: &crate::mir::MirType,
        _right_mir_type: &crate::mir::MirType,
        _location: SourceSpan,
    ) -> Result<(Operand, Operand, TypeId), SemanticError> {
        // Integer + pointer -> pointer type (with integer promoted if needed)
        let (promoted_left, _promoted_left_type) = self.apply_integer_promotions(left, left_type, _location)?;

        Ok((promoted_left, right, right_type))
    }

    /// Get integer type with specific width and signedness
    fn get_int_type_with_width(&mut self, width: u8, is_signed: bool) -> TypeId {
        let mir_type = crate::mir::MirType::Int { is_signed, width };
        self.add_type(mir_type)
    }

    /// Get float type with specific width
    fn get_float_type(&mut self, width: u8) -> TypeId {
        let mir_type = crate::mir::MirType::Float { width };
        self.add_type(mir_type)
    }

    /// Get void pointer type
    fn get_void_pointer_type(&mut self) -> TypeId {
        // Create void type first
        let void_type = self.add_type(crate::mir::MirType::Void);
        // Create pointer to void
        let mir_type = crate::mir::MirType::Pointer { pointee: void_type };
        self.add_type(mir_type)
    }

    /// Resolve the type of a complex expression by examining its structure
    fn resolve_type_from_expression(&self, expr_ref: NodeRef) -> Option<TypeRef> {
        let node = self.ast.get_node(expr_ref);

        match &node.kind {
            NodeKind::MemberAccess(object_ref, field_name, is_arrow) => {
                debug!(
                    "Resolving type for MemberAccess expression: {} (is_arrow: {})",
                    field_name, is_arrow
                );

                // First, resolve the type of the object
                let object_type_ref = self.resolve_type_from_expression(*object_ref)?;

                // For arrow access, we need to dereference the pointer to get the struct type
                let dereferenced_type_ref = if *is_arrow {
                    let object_ast_type = self.ast.get_type(object_type_ref);
                    if let crate::ast::TypeKind::Pointer { pointee } = &object_ast_type.kind {
                        debug!("Dereferencing pointer type to get struct type");
                        *pointee
                    } else {
                        debug!("Arrow access on non-pointer type: {:?}", object_ast_type.kind);
                        return None;
                    }
                } else {
                    object_type_ref
                };

                // Look for the field in the struct/union type
                let struct_ast_type = self.ast.get_type(dereferenced_type_ref);
                if let crate::ast::TypeKind::Record { members, .. } = &struct_ast_type.kind {
                    if let Some(field_index) = members.iter().position(|member| member.name == *field_name) {
                        debug!("Found field '{}' at index {}", field_name, field_index);
                        let field_type = members[field_index].member_type;

                        // If this is arrow access, the result should be the field type directly
                        // If this is dot access, the result should also be the field type directly
                        Some(field_type)
                    } else {
                        debug!("Field '{}' not found in struct", field_name);
                        None
                    }
                } else {
                    debug!("Type is not a struct/union: {:?}", struct_ast_type.kind);
                    None
                }
            }
            NodeKind::Ident(name, symbol_ref) => {
                // For simple identifiers, use the existing symbol table lookup
                if let Some(resolved_ref) = symbol_ref.get() {
                    let entry = self.symbol_table.get_symbol_entry(resolved_ref);
                    debug!("Resolved identifier '{}' to type {:?}", name, entry.type_info);
                    Some(entry.type_info)
                } else {
                    None
                }
            }
            _ => {
                debug!("Cannot resolve type for expression: {:?}", node.kind);
                None
            }
        }
    }

    /// Map AST BinaryOp to MIR BinaryOp
    fn map_ast_binary_op_to_mir(&self, ast_op: &BinaryOp, location: SourceSpan) -> Result<MirBinaryOp, SemanticError> {
        use crate::ast::BinaryOp::*;
        use crate::mir::BinaryOp as MirBinaryOp;

        let mir_op = match ast_op {
            // Arithmetic operations
            Add => MirBinaryOp::Add,
            Sub => MirBinaryOp::Sub,
            Mul => MirBinaryOp::Mul,
            Div => MirBinaryOp::Div,
            Mod => MirBinaryOp::Mod,

            // Bitwise operations
            BitAnd => MirBinaryOp::BitAnd,
            BitOr => MirBinaryOp::BitOr,
            BitXor => MirBinaryOp::BitXor,
            LShift => MirBinaryOp::LShift,
            RShift => MirBinaryOp::RShift,

            // Comparison operations
            Equal => MirBinaryOp::Equal,
            NotEqual => MirBinaryOp::NotEqual,
            Less => MirBinaryOp::Less,
            LessEqual => MirBinaryOp::LessEqual,
            Greater => MirBinaryOp::Greater,
            GreaterEqual => MirBinaryOp::GreaterEqual,

            // Logical operations
            LogicAnd => MirBinaryOp::LogicAnd,
            LogicOr => MirBinaryOp::LogicOr,

            // Comma operator
            Comma => MirBinaryOp::Comma,

            // Assignment operations are not supported in simple binary expressions
            // These should be handled separately as assignment statements
            Assign | AssignAdd | AssignSub | AssignMul | AssignDiv | AssignMod | AssignBitAnd | AssignBitOr
            | AssignBitXor | AssignLShift | AssignRShift => {
                // This is an internal compiler error, as assignment operations should be handled
                // separately in `lower_expression` and not passed to this function.
                panic!(
                    "ICE: Assignment operation unexpectedly passed to map_ast_binary_op_to_mir at {:?}",
                    location
                );
            }
        };

        Ok(mir_op)
    }

    /// Handle direct function calls (e.g., foo())
    fn handle_direct_function_call(&mut self, func_name: Symbol, arg_operands: Vec<Operand>) -> Operand {
        debug!("Handling direct function call: {}", func_name);

        // Look up the function in the MIR functions
        let target_func_id = self.find_mir_function_by_name(func_name);

        if let Some(func_id) = target_func_id {
            debug!(
                "Found function '{}' with ID {:?} (ID as integer: {})",
                func_name,
                func_id,
                func_id.get()
            );

            // Get the function information
            let func = self
                .mir_builder
                .get_functions()
                .get(&func_id)
                .expect("Function should exist");

            // Check if function returns void
            let return_type = self.get_types().get(&func.return_type);
            let is_void_function = return_type.is_some_and(|t| matches!(t, crate::mir::MirType::Void));

            if is_void_function {
                // For void functions, just emit the call without creating a local
                let call_target = CallTarget::Direct(func_id);
                let call_rvalue = Rvalue::Call(call_target, arg_operands);
                // Create a dummy assignment target that won't be used
                let dummy_type_id = self.get_int_type();
                let dummy_local_id = self.mir_builder.create_local(None, dummy_type_id, false);
                let assign_stmt = MirStmt::Assign(Place::Local(dummy_local_id), call_rvalue);
                self.mir_builder.add_statement(assign_stmt);

                // Return a dummy constant since void functions don't return values
                let dummy_const = self.create_constant(ConstValue::Int(0));
                Operand::Constant(dummy_const)
            } else {
                // For non-void functions, create a temporary local to store the return value
                // Use the function's actual return type instead of defaulting to int
                let temp_type_id = func.return_type;
                let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);

                // Generate a proper call using Rvalue
                let call_target = CallTarget::Direct(func_id);
                let call_rvalue = Rvalue::Call(call_target, arg_operands);
                let assign_stmt = MirStmt::Assign(Place::Local(temp_local_id), call_rvalue);
                self.mir_builder.add_statement(assign_stmt);

                // Return the local that will contain the call result
                Operand::Copy(Box::new(Place::Local(temp_local_id)))
            }
        } else {
            debug!("Function {} not found in MIR functions", func_name);
            // Return a dummy operand to allow compilation to continue
            let dummy_const = self.create_constant(ConstValue::Int(0));
            Operand::Constant(dummy_const)
        }
    }

    /// Handle function pointer calls (e.g., v.fptr() or v->fptr())
    fn handle_function_pointer_call(
        &mut self,
        object_ref: NodeRef,
        field_name: Symbol,
        is_arrow: bool,
        arg_operands: Vec<Operand>,
    ) -> Operand {
        debug!(
            "Handling function pointer call through field: {} (is_arrow: {})",
            field_name, is_arrow
        );

        // Lower the object expression to get the base place
        let object_operand = self.lower_expression(object_ref);

        // Create a place representing the function pointer field access
        let mut object_place = match object_operand {
            Operand::Copy(place_box) => *place_box,
            _ => {
                // If object is not a place, create a temporary to hold the computed address
                let temp_type_id = self.get_int_type();
                let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
                let temp_place = Place::Local(temp_local_id);

                // Store the object value in the temporary
                let assign_stmt = MirStmt::Assign(temp_place.clone(), Rvalue::Use(object_operand));
                self.mir_builder.add_statement(assign_stmt);

                temp_place
            }
        };

        // Handle arrow access (object->field) by dereferencing the pointer first
        if is_arrow {
            debug!("Handling arrow access, dereferencing pointer first");

            // For arrow access, we need to dereference the pointer to get the struct
            // Create a temporary to hold the dereferenced struct
            let temp_type_id = self.get_int_type(); // For now, assume int type
            let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
            let temp_place = Place::Local(temp_local_id);

            // Dereference the pointer: temp = *object_place
            let deref_operand = Operand::Copy(Box::new(object_place));
            let deref_rvalue = Rvalue::UnaryOp(crate::mir::UnaryOp::Deref, deref_operand);
            let assign_stmt = MirStmt::Assign(temp_place.clone(), deref_rvalue);
            self.mir_builder.add_statement(assign_stmt);

            // Update object_place to be the dereferenced struct
            object_place = temp_place;
        }

        // Get the type of the object being accessed (similar to member access logic)
        let object_node = self.ast.get_node(object_ref);
        let mut object_type_ref = object_node.resolved_type.get().or_else(|| {
            // If type is not resolved, try to resolve it from the symbol table
            debug!("Type not pre-resolved for object, attempting to resolve from symbol table");

            // For identifiers, look up the symbol in the symbol table
            if let NodeKind::Ident(name, _) = &object_node.kind {
                debug!("Looking up symbol '{}' in symbol table", name);
                if let Some((entry_ref, scope_id)) = self.symbol_table.lookup_symbol(*name) {
                    let entry = self.symbol_table.get_symbol_entry(entry_ref);
                    debug!(
                        "Found symbol '{}' in scope {} with type {:?}",
                        name,
                        scope_id.get(),
                        entry.type_info
                    );
                    debug!("Symbol kind: {:?}", entry.kind);
                    Some(entry.type_info)
                } else {
                    debug!("Symbol '{}' not found in symbol table", name);
                    None
                }
            } else {
                // For complex expressions like nested MemberAccess, we need to resolve the type
                // by examining the structure of the expression
                debug!("Object is a complex expression, attempting to resolve type from expression structure");
                self.resolve_type_from_expression(object_ref)
            }
        });

        // For arrow access, if the object type is a pointer, we need to dereference it
        // to get the actual struct type for field lookup
        if is_arrow && let Some(type_ref) = object_type_ref {
            let object_ast_type = self.ast.get_type(type_ref);
            if let crate::ast::TypeKind::Pointer { pointee } = &object_ast_type.kind {
                // Canonicalize the pointee type to ensure it points to the complete struct definition
                let canonical_pointee = self.canonicalize_type(*pointee);
                object_type_ref = Some(canonical_pointee);
            }
        }

        let Some(object_type_ref) = object_type_ref else {
            // Cannot resolve object type - report error and return dummy operand
            debug!("Cannot resolve object type for function pointer call");
            let error_const = self.create_constant(ConstValue::Int(0));
            return Operand::Constant(error_const);
        };

        debug!(
            "Looking for field '{}' in object type {:?} for function pointer call",
            field_name, object_type_ref
        );

        // Look for the field in the struct and get its index
        let field_index = {
            let object_ast_type = self.ast.get_type(object_type_ref);

            // Handle both struct and union types
            match &object_ast_type.kind {
                crate::ast::TypeKind::Record { members, is_union, .. } => {
                    debug!(
                        "Searching for field '{}' in {} with {} members",
                        field_name,
                        if *is_union { "union" } else { "struct" },
                        members.len()
                    );

                    // Debug: Print all member names for inspection
                    for (i, member) in members.iter().enumerate() {
                        debug!("Member {}: '{}'", i, member.name);
                    }

                    // Search for the field in the struct/union members
                    members.iter().position(|member| member.name == field_name)
                }
                _ => {
                    debug!("Object type is not a struct/union: {:?}", object_ast_type.kind);
                    None
                }
            }
        };

        if let Some(field_idx) = field_index {
            // Create the struct field place for the function pointer
            let func_ptr_place = Place::StructField(Box::new(object_place), field_idx);

            // Load the function pointer from the struct field
            let temp_type_id = self.get_int_type(); // Function pointer type
            let temp_local_id = self.mir_builder.create_local(None, temp_type_id, false);
            let temp_place = Place::Local(temp_local_id);

            // Load the function pointer: temp = object.field
            let load_rvalue = Rvalue::Use(Operand::Copy(Box::new(func_ptr_place)));
            let assign_stmt = MirStmt::Assign(temp_place.clone(), load_rvalue);
            self.mir_builder.add_statement(assign_stmt);

            // Create the indirect call through the function pointer
            debug!("Creating indirect function pointer call");
            let call_target = CallTarget::Indirect(Operand::Copy(Box::new(temp_place)));
            let call_rvalue = Rvalue::Call(call_target, arg_operands);

            // Create a temporary local for the call result
            let result_type_id = self.get_int_type(); // For now, assume int return type
            let result_local_id = self.mir_builder.create_local(None, result_type_id, false);
            let result_place = Place::Local(result_local_id);

            let call_assign_stmt = MirStmt::Assign(result_place.clone(), call_rvalue);
            self.mir_builder.add_statement(call_assign_stmt);

            // Return the local that will contain the call result
            Operand::Copy(Box::new(result_place))
        } else {
            // Field not found - report error and return dummy operand
            debug!("Field '{}' not found for function pointer call", field_name);
            let error_const = self.create_constant(ConstValue::Int(0));
            Operand::Constant(error_const)
        }
    }

    /// Find a MIR function by name
    fn find_mir_function_by_name(&self, func_name: Symbol) -> Option<MirFunctionId> {
        for (func_id, func) in self.mir_builder.get_functions() {
            if func.name == func_name {
                return Some(*func_id);
            }
        }
        None
    }
}
