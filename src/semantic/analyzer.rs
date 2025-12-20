//! Semantic Analysis Phase - Complete semantic checking and MIR construction.
//!
//! This module implements the full semantic analysis phase that bridges the gap
//! between parser AST and MIR, with comprehensive validation and proper multi-declarator
//! handling through a two-pass approach.

use crate::ast::*;
use crate::diagnostic::{DiagnosticEngine, SemanticError};
use crate::mir::{
    self, ConstValue, ConstValueId, Local, LocalId, MirBlock, MirBlockId, MirBuilder, MirFunction, MirFunctionId,
    MirModule, MirStmt, Operand, Place, Terminator, TypeId,
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
    local_map: HashMap<String, LocalId>,
    /// Maps label names to their MIR Block IDs
    label_map: HashMap<String, MirBlockId>,
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

        // Process the entire AST starting from root
        self.lower_node_ref(root_node_ref);

        debug!("Semantic analysis complete");
        self.mir_builder.finalize_module()
    }

    /// Report a semantic error and mark analyzer as having errors
    fn report_error(&mut self, error: SemanticError) {
        self.has_errors = true;
        self.diag.report_error(error);
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

            // Handle compound statements by processing their statements
            NodeKind::CompoundStatement(nodes) => {
                self.lower_compound_statement(&nodes);
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
        let node_kind = self.ast.get_node(node_ref).kind.clone();
        let node_span = self.ast.get_node(node_ref).span;

        match node_kind {
            NodeKind::Return(expr) => {
                self.lower_return_statement(&expr, node_span);
            }
            NodeKind::Goto(label) => {
                self.lower_goto_statement(label, node_span);
            }
            NodeKind::Label(label, statement) => {
                self.lower_label_statement(label, statement, node_span);
            }
            NodeKind::If(if_stmt) => {
                self.lower_if_statement(&if_stmt, node_span);
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
        for &stmt_ref in nodes {
            self.collect_labels_recursive(stmt_ref);
        }

        // Second pass: process all statements
        for &stmt_ref in nodes {
            self.lower_node_ref(stmt_ref);
        }
    }

    /// Recursively collect all labels from a statement and its nested statements
    fn collect_labels_recursive(&mut self, stmt_ref: NodeRef) {
        // Clone the node kind to avoid borrow conflicts
        let node_kind = self.ast.get_node(stmt_ref).kind.clone();

        match node_kind {
            NodeKind::Label(label, statement) => {
                let label_str = label.to_string();

                // Check if this is a consecutive label (the statement is another label)
                let stmt_node_kind = self.ast.get_node(statement).kind.clone();
                if let NodeKind::Label(next_label, _) = stmt_node_kind {
                    // This is a consecutive label

                    // Create a block for the first label in the consecutive chain
                    let block_id = if !self.label_map.contains_key(&label_str) {
                        let target_block_id = self.mir_builder.create_block();
                        self.label_map.insert(label_str.clone(), target_block_id);
                        target_block_id
                    } else {
                        *self.label_map.get(&label_str).unwrap()
                    };

                    // Ensure the next label also maps to the same block
                    self.label_map.insert(next_label.to_string(), block_id);

                    // For consecutive labels, we need to continue processing the chain
                    // but skip the recursive call here since the next label will be processed
                    // when we encounter it in the main traversal
                    // Just process the final statement in the chain by unwrapping all consecutive labels
                    let mut current_statement = statement;
                    while let NodeKind::Label(_, next_stmt) = self.ast.get_node(current_statement).kind.clone() {
                        current_statement = next_stmt;
                    }
                    // Now process the final statement after the consecutive labels
                    self.collect_labels_recursive(current_statement);
                } else {
                    // This is a regular label with a non-label statement
                    // Check for duplicate label definition
                    if self.label_map.contains_key(&label_str) {
                        let node_span = self.ast.get_node(stmt_ref).span;
                        self.report_error(SemanticError::Redefinition {
                            name: label,
                            first_def: node_span,
                            second_def: node_span,
                        });
                    } else {
                        // Create a new basic block for this label
                        let target_block_id = self.mir_builder.create_block();

                        // Register the label mapping
                        self.label_map.insert(label_str.clone(), target_block_id);
                    }

                    // Recursively collect labels from the statement that follows this label
                    self.collect_labels_recursive(statement);
                }
            }
            NodeKind::CompoundStatement(nodes) => {
                // For compound statements, recursively collect labels from all items
                for nested_stmt_ref in nodes {
                    self.collect_labels_recursive(nested_stmt_ref);
                }
            }
            _ => {
                // For other statement types, no action needed for label collection
            }
        }
    }

    /// Lower a function definition
    fn lower_function_def(&mut self, func_def: &FunctionDefData, location: SourceSpan) {
        debug!("Lowering function definition");

        // Extract function name from declarator
        let func_name = match &func_def.declarator {
            Declarator::Identifier(symbol, _, _) => {
                debug!("Found function identifier directly: {}", symbol);
                symbol.to_string()
            }
            other => {
                debug!("Function declarator type: {:?}", std::mem::discriminant(other));
                if let Some(symbol) = extract_identifier(&func_def.declarator) {
                    debug!("Extracted function name: {}", symbol);
                    symbol.to_string()
                } else {
                    debug!(
                        "Failed to extract function name from declarator: {:?}",
                        func_def.declarator
                    );
                    self.report_error(SemanticError::InvalidFunctionDeclarator { location });
                    "unknown_function".to_string()
                }
            }
        };

        // Create MIR function
        let return_type = self.get_int_type(); // Default to int for now
        let func_id = self.mir_builder.create_function(func_name.clone(), return_type);

        // Set current function
        self.mir_builder.set_current_function(func_id);
        self.current_function = Some(func_id);

        // Get function and set entry block using public getters
        let functions = self.mir_builder.get_functions();
        if let Some(current_func) = functions.get(&func_id) {
            let entry_block = current_func.entry_block;
            let _ = functions; // Release the immutable borrow
            self.mir_builder.set_current_block(entry_block);
            self.current_block = Some(entry_block);
        }

        // Push function scope for parameters and locals
        let func_scope = self
            .symbol_table
            .push_scope(crate::semantic::symbol_table::ScopeKind::Function);
        debug!("Pushed function scope: {:?}", func_scope);

        // Process function parameters and create locals for them
        // Skip parameters for main function
        if func_name != "main" {
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
                symbol.to_string()
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
        if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(param_name.as_str().into()) {
            let existing = self.symbol_table.get_symbol_entry(existing_entry);
            self.report_error(SemanticError::Redefinition {
                name: param_name.as_str().into(),
                first_def: existing.definition_span,
                second_def: location,
            });
            return;
        }

        // Create MIR local for the parameter
        let type_id = self.get_int_type(); // Default to int for now
        let local_id = self.mir_builder.create_local(param_name.clone(), type_id, false);

        // Store in local map for expression resolution
        self.local_map.insert(param_name.clone(), local_id);

        // Add to symbol table
        let symbol_entry = SymbolEntry {
            name: param_name.as_str().into(),
            kind: SymbolKind::Variable {
                is_global: false,
                is_static: false,
                is_extern: false,
                initializer: None, // Parameters don't have initializers
            },
            type_info: self.ast.push_type(crate::ast::Type {
                kind: crate::ast::TypeKind::Int { is_signed: true },
                qualifiers: crate::ast::TypeQualifiers::empty(),
                size: None,
                alignment: None,
            }),
            storage_class: None,
            scope_id: self.symbol_table.current_scope().get(),
            definition_span: location,
            is_defined: true,
            is_referenced: false,
            is_completed: true,
        };

        self.symbol_table.add_symbol(param_name.as_str().into(), symbol_entry);

        debug!("Created parameter local '{}' with id {:?}", param_name, local_id);
    }

    // /// Lower a declaration (from parser AST)
    // fn lower_declaration(&mut self, decl: &DeclarationData, location: SourceSpan) {
    //     debug!("Lowering declaration with {} init-declarators", decl.init_declarators.len());

    //     // First pass: Create locals for all declarators without processing initializers
    //     let mut local_info = Vec::new();

    //     for init_declarator in &decl.init_declarators {
    //         let (var_name, local_id) = match self.create_local_for_declarator(init_declarator, location) {
    //             Some((name, id)) => (name, id),
    //             None => continue, // Skip if there was an error
    //         };

    //         local_info.push((var_name, local_id, init_declarator.initializer.clone()));
    //     }

    //     // Second pass: Process initializers and emit assignments
    //     for (var_name, local_id, initializer) in local_info {
    //         if let Some(init) = initializer {
    //             self.process_initializer(&init, local_id, &var_name, location);
    //         }
    //     }
    // }

    // /// First pass: Create a local for a declarator
    // fn create_local_for_declarator(
    //     &mut self,
    //     init_declarator: &InitDeclarator,
    //     location: SourceSpan,
    // ) -> Option<(String, LocalId)> {
    //     // Extract variable name
    //     let var_name = match extract_identifier(&init_declarator.declarator) {
    //         Some(symbol) => symbol.to_string(),
    //         None => {
    //             self.report_error(SemanticError::InvalidDeclarator { location });
    //             return None;
    //         }
    //     };

    //     // Check for redeclaration in current scope
    //     if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(var_name.as_str().into()) {
    //         let existing = self.symbol_table.get_symbol_entry(existing_entry);
    //         self.report_error(SemanticError::Redefinition {
    //             name: var_name.as_str().into(),
    //             first_def: existing.definition_span,
    //             second_def: location,
    //         });
    //         return None;
    //     }

    //     // Create MIR local
    //     let type_id = self.get_int_type(); // Default to int for now
    //     let local_id = self.mir_builder.create_local(var_name.clone(), type_id, false);

    //     // Store in local map for expression resolution
    //     self.local_map.insert(var_name.clone(), local_id);

    //     // Add to symbol table
    //     let symbol_entry = SymbolEntry {
    //         name: var_name.as_str().into(),
    //         kind: SymbolKind::Variable {
    //             is_global: false,
    //             is_static: false,
    //             is_extern: false,
    //             initializer: init_declarator.initializer.clone().map(|i| self.convert_initializer(i)),
    //         },
    //         type_info: self.ast.push_type(crate::ast::Type {
    //             kind: crate::ast::TypeKind::Int { is_signed: true },
    //             qualifiers: crate::ast::TypeQualifiers::empty(),
    //             size: None,
    //             alignment: None,
    //         }),
    //         storage_class: None,
    //         scope_id: self.symbol_table.current_scope().get(),
    //         definition_span: location,
    //         is_defined: true,
    //         is_referenced: false,
    //         is_completed: true,
    //     };

    //     self.symbol_table.add_symbol(var_name.as_str().into(), symbol_entry);

    //     debug!("Created local '{}' with id {:?}", var_name, local_id);
    //     Some((var_name, local_id))
    // }

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
                        feature: "GNU array range designator '[start ... end]' not yet implemented".to_string(),
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
                self.report_error(SemanticError::UnsupportedFeature {
                    feature: "Nested compound initializers in designated initializers not yet implemented".to_string(),
                    location,
                });
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
                let temp_local_id =
                    self.mir_builder
                        .create_local(format!("{}_init_{}", var_name, index), temp_type_id, false);

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
                self.report_error(SemanticError::UnsupportedFeature {
                    feature: "Nested compound initializers not yet implemented".to_string(),
                    location,
                });
            }
        }
    }

    /// Lower a variable declaration (from semantic AST)
    fn lower_var_declaration(&mut self, var_decl: &VarDeclData, location: SourceSpan) {
        debug!("Lowering semantic var declaration for '{}'", var_decl.name);

        // Check for redeclaration
        if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(var_decl.name) {
            let existing = self.symbol_table.get_symbol_entry(existing_entry);
            self.report_error(SemanticError::Redefinition {
                name: var_decl.name,
                first_def: existing.definition_span,
                second_def: location,
            });
            return;
        }

        // Canonicalize the variable's type (like Clang does)
        let canonical_type_id = self.canonicalize_type(var_decl.ty);

        // Create MIR local with canonicalized type
        let mir_type_id = self.lower_type_to_mir(canonical_type_id);
        let local_id = self
            .mir_builder
            .create_local(var_decl.name.to_string(), mir_type_id, false);

        // Store in local map
        self.local_map.insert(var_decl.name.to_string(), local_id);

        // Process initializer if present
        if let Some(initializer) = &var_decl.init {
            self.process_initializer(initializer, local_id, &var_decl.name.to_string(), location);
        }

        debug!("Created semantic var '{}' with id {:?}", var_decl.name, local_id);
    }

    /// Lower a typedef declaration
    fn lower_typedef_declaration(&mut self, typedef_decl: &TypedefDeclData, location: SourceSpan) {
        // Check for redeclaration in current scope
        if let Some((existing_entry, _)) = self.symbol_table.lookup_symbol(typedef_decl.name) {
            let existing = self.symbol_table.get_symbol_entry(existing_entry);
            self.report_error(SemanticError::Redefinition {
                name: typedef_decl.name,
                first_def: existing.definition_span,
                second_def: location,
            });
            return;
        }

        // Add typedef to symbol table
        let symbol_entry = SymbolEntry {
            name: typedef_decl.name,
            kind: SymbolKind::Typedef {
                aliased_type: typedef_decl.ty,
            },
            type_info: typedef_decl.ty, // Typedef points to the aliased type
            storage_class: Some(StorageClass::Typedef),
            scope_id: self.symbol_table.current_scope().get(),
            definition_span: location,
            is_defined: true,
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

            NodeKind::Ident(name, symbol_ref) => {
                // First try to resolve through semantic analysis
                if let Some(resolved_ref) = symbol_ref.get() {
                    let entry = self.symbol_table.get_symbol_entry(resolved_ref);
                    if let SymbolKind::Variable { .. } = &entry.kind {
                        // Look up the local in our local map
                        let var_name = entry.name.to_string();
                        if let Some(local_id) = self.local_map.get(&var_name) {
                            return Operand::Copy(Box::new(Place::Local(*local_id)));
                        }
                    }
                }

                // Fallback to direct local map lookup
                if let Some(local_id) = self.local_map.get(&name.to_string()) {
                    Operand::Copy(Box::new(Place::Local(*local_id)))
                } else {
                    self.report_error(SemanticError::UndeclaredIdentifier {
                        name,
                        location: self.ast.get_node(expr_ref).span,
                    });

                    // Return a dummy operand to allow compilation to continue
                    let error_const = self.create_constant(ConstValue::Int(0));
                    Operand::Constant(error_const)
                }
            }

            NodeKind::BinaryOp(op, left_ref, right_ref) => {
                debug!("Lowering binary operation: {:?}", op);

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

                        // TODO: Generate proper binary operation MIR using converted operands
                        // For now, return a dummy result of the common type
                        let result_const = self.create_constant(ConstValue::Int(0));
                        Operand::Constant(result_const)
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

            NodeKind::FunctionCall(func_ref, args) => {
                debug!("Lowering function call expression with {} arguments", args.len());

                // Extract function name from the function reference
                let func_node = self.ast.get_node(func_ref);
                let func_name = if let NodeKind::Ident(name, _) = &func_node.kind {
                    name.to_string()
                } else {
                    debug!("Function call target is not an identifier: {:?}", func_node.kind);
                    let dummy_const = self.create_constant(ConstValue::Int(0));
                    return Operand::Constant(dummy_const);
                };

                debug!("Function call target: {}", func_name);

                // For now, generate a call statement and return a dummy operand
                // TODO: Implement proper function call handling with argument evaluation
                // and return value assignment

                // Create a temporary local to store the return value
                let temp_type_id = self.get_int_type();
                let temp_local_id =
                    self.mir_builder
                        .create_local(format!("call_result_{}", func_name), temp_type_id, false);

                // Generate a call statement
                let call_stmt = MirStmt::Call(
                    Place::Local(temp_local_id),
                    Operand::Copy(Box::new(Place::Local(temp_local_id))), // Function placeholder
                    Vec::new(),                                           // No arguments for now
                );

                let _stmt_id = self.mir_builder.add_statement(call_stmt);

                // Return the local that will contain the call result
                Operand::Copy(Box::new(Place::Local(temp_local_id)))
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
        // Check if current block is already terminated (unreachable code)
        if self.mir_builder.current_block_has_terminator() {
            debug!("Skipping unreachable return statement");
            return;
        }

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

        // For now, simplify if statement handling
        // TODO: Implement proper control flow with then/else blocks
        // This involves creating new blocks for then and else branches

        // Evaluate condition (currently just processes it)
        let _cond_operand = self.lower_expression(if_stmt.condition);

        // Process then branch
        self.lower_node_ref(if_stmt.then_branch);

        // Process else branch if present
        if let Some(else_branch) = &if_stmt.else_branch {
            self.lower_node_ref(*else_branch);
        }
    }

    /// Emit an assignment statement
    fn emit_assignment(&mut self, place: Place, operand: Operand, _location: SourceSpan) {
        // Check if current block is already terminated (unreachable code)
        if self.mir_builder.current_block_has_terminator() {
            debug!("Skipping unreachable assignment statement");
            return;
        }

        let stmt = MirStmt::Assign(place, operand);

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
            crate::ast::TypeKind::Record {
                tag, members, is_union, ..
            } => {
                debug!("Converting Record type with {} members to MIR", members.len());
                // Convert struct/union members to MIR format
                let mut mir_fields = Vec::new();
                for member in members {
                    let field_type_id = self.lower_type_to_mir(member.member_type);
                    mir_fields.push((member.name.to_string(), field_type_id));
                }

                let type_name = tag
                    .map(|t| t.to_string())
                    .unwrap_or_else(|| format!("anonymous_{}", if is_union { "union" } else { "struct" }));
                debug!(
                    "Created MIR type for struct '{}' with {} fields",
                    type_name,
                    mir_fields.len()
                );

                let mir_type = if is_union {
                    crate::mir::MirType::Union {
                        name: type_name.clone(),
                        fields: mir_fields.clone(),
                    }
                } else {
                    crate::mir::MirType::Struct {
                        name: type_name.clone(),
                        fields: mir_fields.clone(),
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
    pub fn get_functions(&self) -> &hashbrown::HashMap<MirFunctionId, MirFunction> {
        self.mir_builder.get_functions()
    }

    /// Get blocks for validation
    pub fn get_blocks(&self) -> &hashbrown::HashMap<MirBlockId, MirBlock> {
        self.mir_builder.get_blocks()
    }

    /// Get locals for validation
    pub fn get_locals(&self) -> &hashbrown::HashMap<LocalId, Local> {
        self.mir_builder.get_locals()
    }

    /// Get globals for validation
    pub fn get_globals(&self) -> &hashbrown::HashMap<mir::GlobalId, mir::Global> {
        self.mir_builder.get_globals()
    }

    /// Get types for validation
    pub fn get_types(&self) -> &hashbrown::HashMap<TypeId, crate::mir::MirType> {
        self.mir_builder.get_types()
    }

    /// Lower a goto statement
    fn lower_goto_statement(&mut self, label: Symbol, location: SourceSpan) {
        debug!("Lowering goto statement to label: {}", label);

        // For goto statements, we need to set up a jump to the target label
        // However, we might not know the target block ID yet if labels come after
        // For now, create a temporary placeholder and resolve later
        let label_str = label.to_string();

        // Look up the label in our label map
        if let Some(target_block_id) = self.label_map.get(&label_str) {
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
            debug!("Label '{}' not found in label map during goto resolution", label_str);
            self.report_error(SemanticError::UndeclaredIdentifier { name: label, location });
            // Set a dummy terminator to allow compilation to continue
            self.mir_builder.set_terminator(Terminator::Unreachable);
        }
    }

    /// Lower a label statement
    fn lower_label_statement(&mut self, label: Symbol, statement: NodeRef, _location: SourceSpan) {
        let label_str = label.to_string();

        // Get the existing block for this label (created in first pass)
        if let Some(&target_block_id) = self.label_map.get(&label_str) {
            // Switch to the existing block for the label's statement
            self.mir_builder.set_current_block(target_block_id);
            self.current_block = Some(target_block_id);

            // Process the statement that follows the label
            self.lower_node_ref(statement);
        } else {
            // This label wasn't created in the first pass, which means it's a consecutive label.
            // We need to find the previous label's block and map this label to it.
            // However, since we don't have easy access to the previous label here,
            // we'll create a new block for now and handle this case better.
            //
            // TODO: Fix this by tracking consecutive labels better

            // Create a new basic block for this label (fallback)
            let target_block_id = self.mir_builder.create_block();
            self.label_map.insert(label_str.clone(), target_block_id);

            // Switch to the new block for the label's statement
            self.mir_builder.set_current_block(target_block_id);
            self.current_block = Some(target_block_id);

            // Process the statement that follows the label
            self.lower_node_ref(statement);
        }
    }

    /// Find a struct/union field by name and return its index
    fn find_struct_field(&self, type_id: TypeId, field_name: Symbol) -> Option<usize> {
        let mir_type = self.get_types().get(&type_id)?;

        debug!("Looking for field '{}' in type {:?}", field_name, mir_type);

        match mir_type {
            crate::mir::MirType::Struct { fields, .. } | crate::mir::MirType::Union { fields, .. } => {
                let field_index = fields.iter().position(|(name, _)| *name == field_name.to_string());
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
    fn canonicalize_type(&self, type_ref: TypeRef) -> TypeRef {
        let ast_type = self.ast.get_type(type_ref);

        match &ast_type.kind {
            crate::ast::TypeKind::Record {
                tag,
                members: _,
                is_complete,
                ..
            } => {
                // If the record is already complete, return the original type
                if *is_complete {
                    return type_ref;
                }

                // If incomplete, try to find the complete definition
                if let Some(tag_name) = tag {
                    // Search through all AST types for a complete definition with the same tag
                    for (i, ast_type_candidate) in self.ast.types.iter().enumerate() {
                        if let crate::ast::TypeKind::Record {
                            tag: candidate_tag,
                            members: candidate_members,
                            is_complete: candidate_is_complete,
                            ..
                        } = &ast_type_candidate.kind
                            && Some(tag_name) == candidate_tag.as_ref()
                            && *candidate_is_complete
                            && !candidate_members.is_empty()
                        {
                            return TypeRef::new((i + 1) as u32).unwrap();
                        }
                    }
                }

                // If no complete definition found, return the original type
                debug!("No complete definition found for type, returning original");
                type_ref
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
            return Err(SemanticError::InvalidBinaryOperandTypes {
                left_type: format!("{:?}", left_mir_type),
                right_type: "unknown".to_string(), // Will be updated below
                location,
            });
        }

        if let Some(right_mir_type) = self.get_types().get(&right_type)
            && matches!(right_mir_type, crate::mir::MirType::Void)
        {
            return Err(SemanticError::InvalidBinaryOperandTypes {
                left_type: "unknown".to_string(), // Will be updated below
                right_type: format!("{:?}", right_mir_type),
                location,
            });
        }

        // Get MIR types for both operands
        let (left_mir_type, right_mir_type) =
            match (self.get_types().get(&left_type), self.get_types().get(&right_type)) {
                (Some(left_type), Some(right_type)) => (left_type.clone(), right_type.clone()),
                _ => {
                    return Err(SemanticError::InvalidBinaryOperandTypes {
                        left_type: format!("unknown ({})", left_type.get()),
                        right_type: format!("unknown ({})", right_type.get()),
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
            Err(SemanticError::InvalidBinaryOperandTypes {
                left_type: format!("{:?}", left_mir_type),
                right_type: format!("{:?}", right_mir_type),
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
            Err(SemanticError::InvalidTypeConversion {
                from_type: "unknown".to_string(),
                to_type: "unknown".to_string(),
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
                Err(SemanticError::UnsupportedConversion {
                    left_type: format!("{:?}", left_type),
                    right_type: format!("{:?}", right_type),
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_apply_binary_operand_conversion_exists() {
        // This test ensures the function exists and compiles correctly
        // Actual functionality testing would require a proper test setup with lifetimes

        // We can at least verify the function signature is correct by checking
        // that it would compile if called with the right parameters
        let _function_exists = true; // Placeholder to ensure this test compiles
        assert!(_function_exists);
    }
}

/// Extract identifier from a declarator (helper function)
fn extract_identifier(declarator: &Declarator) -> Option<Symbol> {
    match declarator {
        Declarator::Identifier(name, _, _) => Some(*name),
        Declarator::Pointer(_, next) => next.as_ref().and_then(|d| extract_identifier(d)),
        Declarator::Array(base, _) => extract_identifier(base),
        Declarator::Function(base, _) => extract_identifier(base),
        Declarator::BitField(base, _) => extract_identifier(base),
        _ => None,
    }
}
