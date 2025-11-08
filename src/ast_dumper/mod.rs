use std::fmt::Write;
use std::path::PathBuf;

use crate::ast::*;
use crate::diagnostic::*;
use crate::semantic::*;

/// Configuration for AST dump output
#[derive(Debug, Clone)]
pub struct DumpConfig {
    pub pretty_print: bool,
    pub include_source: bool,
    pub max_depth: Option<usize>,
    pub output_path: PathBuf,
}

impl Default for DumpConfig {
    fn default() -> Self {
        DumpConfig {
            pretty_print: true,
            include_source: false,
            max_depth: None,
            output_path: PathBuf::from("ast_dump.html"),
        }
    }
}

/// Main AST dumper that generates HTML visualization
pub struct AstDumper<'src> {
    ast: &'src Ast,
    symbol_table: &'src SymbolTable,
    diag: &'src DiagnosticEngine,
    config: DumpConfig,
}

impl<'src> AstDumper<'src> {
    /// Create a new AST dumper
    pub fn new(
        ast: &'src Ast,
        symbol_table: &'src SymbolTable,
        diag: &'src DiagnosticEngine,
        config: DumpConfig,
    ) -> Self {
        AstDumper {
            ast,
            symbol_table,
            diag,
            config,
        }
    }

    /// Generate the complete HTML dump
    pub fn generate_html(&self) -> Result<String, std::fmt::Error> {
        let mut html = String::new();

        // HTML header
        self.write_html_header(&mut html)?;

        // Body start
        writeln!(html, "<body>")?;
        writeln!(html, "<h1>Cendol Compiler AST Dump</h1>")?;

        // Generate sections
        self.generate_ast_section(&mut html)?;
        self.generate_symbol_table_section(&mut html)?;
        self.generate_scope_table_section(&mut html)?;
        self.generate_type_table_section(&mut html)?;

        // Body end
        writeln!(html, "</body>")?;
        writeln!(html, "</html>")?;

        Ok(html)
    }

    fn write_html_header(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<!DOCTYPE html>")?;
        writeln!(html, "<html>")?;
        writeln!(html, "<head>")?;
        writeln!(html, "<title>Cendol AST Dump</title>")?;
        writeln!(html, "<style>")?;
        self.write_css_styles(html)?;
        writeln!(html, "</style>")?;
        writeln!(html, "<script>")?;
        self.write_javascript(html)?;
        writeln!(html, "</script>")?;
        writeln!(html, "</head>")?;
        Ok(())
    }

    fn write_css_styles(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, r#"
            body {{
                font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
                margin: 20px;
                background-color: #f8f9fa;
            }}

            h1, h2 {{
                color: #2c3e50;
            }}

            .ast-node {{
                margin: 5px 0;
                padding: 5px;
                border-left: 3px solid #3498db;
                background-color: white;
            }}

            .node-type {{
                font-weight: bold;
                color: #2e86ab;
            }}

            .span-info {{
                color: #7f8c8d;
                font-size: 0.9em;
            }}

            .semantic-info {{
                background: #ecf0f1;
                padding: 5px;
                margin: 5px 0;
                border-radius: 3px;
                font-size: 0.9em;
            }}

            .ast-tree {{
                margin-left: 20px;
            }}

            .ast-tree ul {{
                list-style-type: none;
                padding-left: 20px;
            }}

            .ast-tree li {{
                position: relative;
            }}

            .ast-tree li:before {{
                content: '';
                position: absolute;
                left: -15px;
                top: 8px;
                width: 10px;
                height: 1px;
                background: #bdc3c7;
            }}

            .ast-tree li:only-child:before {{
                display: none;
            }}

            table {{
                border-collapse: collapse;
                width: 100%;
                margin: 20px 0;
                background-color: white;
                box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            }}

            th, td {{
                border: 1px solid #ddd;
                padding: 12px;
                text-align: left;
            }}

            th {{
                background-color: #34495e;
                color: white;
                font-weight: bold;
            }}

            tr:nth-child(even) {{
                background-color: #f2f2f2;
            }}

            tr:hover {{
                background-color: #e8f4fd;
            }}

            .collapsible {{
                cursor: pointer;
                user-select: none;
            }}

            .collapsible:before {{
                content: '▶ ';
                display: inline-block;
                transition: transform 0.2s;
            }}

            .collapsible.collapsed:before {{
                transform: rotate(0deg);
            }}

            .collapsible.expanded:before {{
                transform: rotate(90deg);
            }}

            .content {{
                display: block;
            }}

            .content.collapsed {{
                display: none;
            }}

            .search-container {{
                margin: 20px 0;
            }}

            #search-input {{
                padding: 8px;
                width: 300px;
                border: 1px solid #ddd;
                border-radius: 4px;
            }}

            .error {{
                color: #e74c3c;
                font-weight: bold;
            }}

            .warning {{
                color: #f39c12;
            }}

            a {{
                color: #3498db;
                text-decoration: none;
            }}

            a:hover {{
                text-decoration: underline;
            }}
        "#)?;
        Ok(())
    }

    fn write_javascript(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, r#"
            function toggleCollapse(element) {{
                const content = element.nextElementSibling;
                const isCollapsed = content.classList.contains('collapsed');

                if (isCollapsed) {{
                    content.classList.remove('collapsed');
                    element.classList.remove('collapsed');
                    element.classList.add('expanded');
                }} else {{
                    content.classList.add('collapsed');
                    element.classList.remove('expanded');
                    element.classList.add('collapsed');
                }}
            }}

            function searchTable(tableId, query) {{
                const table = document.getElementById(tableId);
                const rows = table.getElementsByTagName('tbody')[0].getElementsByTagName('tr');
                const lowerQuery = query.toLowerCase();

                for (let i = 0; i < rows.length; i++) {{
                    const cells = rows[i].getElementsByTagName('td');
                    let found = false;

                    for (let j = 0; j < cells.length; j++) {{
                        if (cells[j].textContent.toLowerCase().includes(lowerQuery)) {{
                            found = true;
                            break;
                        }}
                    }}

                    rows[i].style.display = found ? '' : 'none';
                }}
            }}

            function setupSearch() {{
                const searchInput = document.getElementById('search-input');
                const tableSelect = document.getElementById('table-select');

                function performSearch() {{
                    const query = searchInput.value;
                    const tableId = tableSelect.value;
                    searchTable(tableId, query);
                }}

                searchInput.addEventListener('input', performSearch);
                tableSelect.addEventListener('change', performSearch);
            }}

            document.addEventListener('DOMContentLoaded', function() {{
                setupSearch();

                // Make collapsible elements work
                const collapsibles = document.getElementsByClassName('collapsible');
                for (let i = 0; i < collapsibles.length; i++) {{
                    collapsibles[i].addEventListener('click', function() {{
                        toggleCollapse(this);
                    }});
                }}
            }});
        "#)?;
        Ok(())
    }

    fn generate_ast_section(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<section id=\"ast-section\">")?;
        writeln!(html, "<h2>Abstract Syntax Tree</h2>")?;
        writeln!(html, "<div id=\"ast-tree\">")?;

        // Find the root node (TranslationUnit)
        if let Some(root_node) = self.ast.nodes.first() {
            self.generate_ast_tree(html, root_node, 0)?;
        } else {
            writeln!(html, "<p class=\"error\">No AST nodes found</p>")?;
        }

        writeln!(html, "</div>")?;
        writeln!(html, "</section>")?;
        Ok(())
    }

    fn generate_ast_tree(&self, html: &mut String, node: &Node, depth: usize) -> Result<(), std::fmt::Error> {
        if let Some(max_depth) = self.config.max_depth {
            if depth > max_depth {
                writeln!(html, "<li class=\"ast-node\">... (truncated)</li>")?;
                return Ok(());
            }
        }

        let node_type = self.get_node_type_name(&node.kind);
        let span_info = format!("[0:{}-0:{}]",
            node.span.start.offset(),
            node.span.end.offset()
        );

        writeln!(html, "<ul class=\"ast-tree\">")?;
        writeln!(html, "<li class=\"ast-node\">")?;
        writeln!(html, "<span class=\"node-type\">{}</span>", self.escape_html(&node_type))?;
        writeln!(html, "<span class=\"span-info\">{}</span>", self.escape_html(&span_info))?;

        // Add semantic information
        self.generate_semantic_info(html, node)?;

        // Generate child nodes
        self.generate_child_nodes(html, node, depth)?;

        writeln!(html, "</li>")?;
        writeln!(html, "</ul>")?;
        Ok(())
    }

    fn get_node_type_name(&self, kind: &NodeKind) -> String {
        match kind {
            NodeKind::TranslationUnit(_) => "TranslationUnit".to_string(),
            NodeKind::FunctionDef(_) => "FunctionDef".to_string(),
            NodeKind::Declaration(_) => "Declaration".to_string(),
            NodeKind::Ident(_, _) => "Ident".to_string(),
            NodeKind::LiteralInt(_) => "LiteralInt".to_string(),
            NodeKind::LiteralFloat(_) => "LiteralFloat".to_string(),
            NodeKind::LiteralString(_) => "LiteralString".to_string(),
            NodeKind::LiteralChar(_) => "LiteralChar".to_string(),
            NodeKind::BinaryOp(op, _, _) => format!("BinaryOp({:?})", op),
            NodeKind::UnaryOp(op, _) => format!("UnaryOp({:?})", op),
            NodeKind::Assignment(op, _, _) => format!("Assignment({:?})", op),
            NodeKind::FunctionCall(_, _) => "FunctionCall".to_string(),
            NodeKind::CompoundStatement(_) => "CompoundStatement".to_string(),
            NodeKind::If(_) => "If".to_string(),
            NodeKind::While(_) => "While".to_string(),
            NodeKind::For(_) => "For".to_string(),
            NodeKind::Return(_) => "Return".to_string(),
            NodeKind::Break => "Break".to_string(),
            NodeKind::Continue => "Continue".to_string(),
            NodeKind::ExpressionStatement(_) => "ExpressionStatement".to_string(),
            NodeKind::EmptyStatement => "EmptyStatement".to_string(),
            _ => format!("{:?}", kind).split('(').next().unwrap_or("Unknown").to_string(),
        }
    }

    fn generate_semantic_info(&self, html: &mut String, node: &Node) -> Result<(), std::fmt::Error> {
        let mut info_parts = Vec::new();

        if let Some(type_ref) = node.resolved_type.get() {
            info_parts.push(format!("Type: <a href=\"#type_{}\">{}</a>",
                type_ref.get(),
                self.get_type_display_name(type_ref)
            ));
        }

        if let Some(symbol_ref) = node.resolved_symbol.get() {
            let symbol = self.symbol_table.get_symbol_entry(symbol_ref);
            info_parts.push(format!("Symbol: <a href=\"#sym_{}\">{}</a>",
                symbol_ref.get(),
                self.escape_html(&symbol.name.to_string())
            ));
        }

        if !info_parts.is_empty() {
            writeln!(html, "<div class=\"semantic-info\">")?;
            writeln!(html, "{}", info_parts.join(", "))?;
            writeln!(html, "</div>")?;
        }

        Ok(())
    }

    fn generate_child_nodes(&self, html: &mut String, node: &Node, depth: usize) -> Result<(), std::fmt::Error> {
        match &node.kind {
            NodeKind::TranslationUnit(nodes) => {
                for &node_ref in nodes {
                    let child = self.ast.get_node(node_ref);
                    self.generate_ast_tree(html, child, depth + 1)?;
                }
            }
            NodeKind::FunctionDef(func_def) => {
                // Generate function body
                let body_node = self.ast.get_node(func_def.body);
                self.generate_ast_tree(html, body_node, depth + 1)?;
            }
            NodeKind::CompoundStatement(nodes) => {
                for &node_ref in nodes {
                    let child = self.ast.get_node(node_ref);
                    self.generate_ast_tree(html, child, depth + 1)?;
                }
            }
            NodeKind::BinaryOp(_, left, right) => {
                let left_node = self.ast.get_node(*left);
                let right_node = self.ast.get_node(*right);
                self.generate_ast_tree(html, left_node, depth + 1)?;
                self.generate_ast_tree(html, right_node, depth + 1)?;
            }
            NodeKind::UnaryOp(_, operand) => {
                let operand_node = self.ast.get_node(*operand);
                self.generate_ast_tree(html, operand_node, depth + 1)?;
            }
            NodeKind::Assignment(_, lhs, rhs) => {
                let lhs_node = self.ast.get_node(*lhs);
                let rhs_node = self.ast.get_node(*rhs);
                self.generate_ast_tree(html, lhs_node, depth + 1)?;
                self.generate_ast_tree(html, rhs_node, depth + 1)?;
            }
            NodeKind::FunctionCall(func, args) => {
                let func_node = self.ast.get_node(*func);
                self.generate_ast_tree(html, func_node, depth + 1)?;
                for &arg_ref in args {
                    let arg_node = self.ast.get_node(arg_ref);
                    self.generate_ast_tree(html, arg_node, depth + 1)?;
                }
            }
            NodeKind::If(if_stmt) => {
                let condition = self.ast.get_node(if_stmt.condition);
                let then_branch = self.ast.get_node(if_stmt.then_branch);
                self.generate_ast_tree(html, condition, depth + 1)?;
                self.generate_ast_tree(html, then_branch, depth + 1)?;
                if let Some(else_branch) = if_stmt.else_branch {
                    let else_node = self.ast.get_node(else_branch);
                    self.generate_ast_tree(html, else_node, depth + 1)?;
                }
            }
            NodeKind::While(while_stmt) => {
                let condition = self.ast.get_node(while_stmt.condition);
                let body = self.ast.get_node(while_stmt.body);
                self.generate_ast_tree(html, condition, depth + 1)?;
                self.generate_ast_tree(html, body, depth + 1)?;
            }
            NodeKind::For(for_stmt) => {
                if let Some(init) = for_stmt.init {
                    let init_node = self.ast.get_node(init);
                    self.generate_ast_tree(html, init_node, depth + 1)?;
                }
                if let Some(condition) = for_stmt.condition {
                    let cond_node = self.ast.get_node(condition);
                    self.generate_ast_tree(html, cond_node, depth + 1)?;
                }
                if let Some(increment) = for_stmt.increment {
                    let inc_node = self.ast.get_node(increment);
                    self.generate_ast_tree(html, inc_node, depth + 1)?;
                }
                let body = self.ast.get_node(for_stmt.body);
                self.generate_ast_tree(html, body, depth + 1)?;
            }
            NodeKind::Return(Some(expr)) => {
                let expr_node = self.ast.get_node(*expr);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
            }
            NodeKind::ExpressionStatement(Some(expr)) => {
                let expr_node = self.ast.get_node(*expr);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
            }
            // Add more cases as needed
            _ => {} // Leaf nodes or unhandled cases
        }
        Ok(())
    }

    fn generate_symbol_table_section(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<section id=\"symbols-section\">")?;
        writeln!(html, "<h2>Symbol Table</h2>")?;
        writeln!(html, "<table id=\"symbol-table\">")?;
        writeln!(html, "<thead>")?;
        writeln!(html, "<tr>")?;
        writeln!(html, "<th>ID</th>")?;
        writeln!(html, "<th>Name</th>")?;
        writeln!(html, "<th>Kind</th>")?;
        writeln!(html, "<th>Type</th>")?;
        writeln!(html, "<th>Scope</th>")?;
        writeln!(html, "<th>Location</th>")?;
        writeln!(html, "</tr>")?;
        writeln!(html, "</thead>")?;
        writeln!(html, "<tbody>")?;

        // Generate symbol entries
        for (i, entry) in self.symbol_table.entries.iter().enumerate() {
            let id = i + 1;
            let name = self.escape_html(&entry.name.to_string());
            let kind = self.get_symbol_kind_display(&entry.kind);
            let type_link = format!("<a href=\"#type_{}\">{}</a>",
                entry.type_info.get(),
                self.get_type_display_name(entry.type_info)
            );
            let scope_link = format!("<a href=\"#scope_{}\">{}</a>", entry.scope_id, entry.scope_id);
            let location = format!("[{}:{}-{}:{}]",
                entry.definition_span.start.source_id(),
                entry.definition_span.start.offset(),
                entry.definition_span.end.source_id(),
                entry.definition_span.end.offset()
            );

            writeln!(html, "<tr id=\"sym_{}\">", id)?;
            writeln!(html, "<td>{}</td>", id)?;
            writeln!(html, "<td>{}</td>", name)?;
            writeln!(html, "<td>{}</td>", kind)?;
            writeln!(html, "<td>{}</td>", type_link)?;
            writeln!(html, "<td>{}</td>", scope_link)?;
            writeln!(html, "<td>{}</td>", location)?;
            writeln!(html, "</tr>")?;
        }

        writeln!(html, "</tbody>")?;
        writeln!(html, "</table>")?;
        writeln!(html, "</section>")?;
        Ok(())
    }

    fn generate_scope_table_section(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<section id=\"scopes-section\">")?;
        writeln!(html, "<h2>Scope Table</h2>")?;
        writeln!(html, "<table id=\"scope-table\">")?;
        writeln!(html, "<thead>")?;
        writeln!(html, "<tr>")?;
        writeln!(html, "<th>ID</th>")?;
        writeln!(html, "<th>Parent</th>")?;
        writeln!(html, "<th>Kind</th>")?;
        writeln!(html, "<th>Level</th>")?;
        writeln!(html, "<th>Symbols</th>")?;
        writeln!(html, "</tr>")?;
        writeln!(html, "</thead>")?;
        writeln!(html, "<tbody>")?;

        for (i, scope) in self.symbol_table.scopes.iter().enumerate() {
            let id = i + 1;
            let parent = scope.parent.map(|p| p.get().to_string()).unwrap_or_else(|| "None".to_string());
            let kind = format!("{:?}", scope.kind);
            let level = scope.level;
            let symbols: Vec<String> = scope.symbols.values()
                .map(|&ref_| format!("<a href=\"#sym_{}\">{}</a>",
                    ref_.get(),
                    self.escape_html(&self.symbol_table.get_symbol_entry(ref_).name.to_string())
                ))
                .collect();
            let symbols_str = symbols.join(", ");

            writeln!(html, "<tr id=\"scope_{}\">", id)?;
            writeln!(html, "<td>{}</td>", id)?;
            writeln!(html, "<td>{}</td>", parent)?;
            writeln!(html, "<td>{}</td>", kind)?;
            writeln!(html, "<td>{}</td>", level)?;
            writeln!(html, "<td>{}</td>", symbols_str)?;
            writeln!(html, "</tr>")?;
        }

        writeln!(html, "</tbody>")?;
        writeln!(html, "</table>")?;
        writeln!(html, "</section>")?;
        Ok(())
    }

    fn generate_type_table_section(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<section id=\"types-section\">")?;
        writeln!(html, "<h2>Type Table</h2>")?;
        writeln!(html, "<table id=\"type-table\">")?;
        writeln!(html, "<thead>")?;
        writeln!(html, "<tr>")?;
        writeln!(html, "<th>ID</th>")?;
        writeln!(html, "<th>Kind</th>")?;
        writeln!(html, "<th>Base</th>")?;
        writeln!(html, "<th>Qualifiers</th>")?;
        writeln!(html, "<th>Size</th>")?;
        writeln!(html, "<th>Details</th>")?;
        writeln!(html, "</tr>")?;
        writeln!(html, "</thead>")?;
        writeln!(html, "<tbody>")?;

        for (i, ty) in self.ast.types.iter().enumerate() {
            let id = i + 1;
            let kind = self.get_type_kind_display(&ty.kind);
            let base = self.get_type_base_display(&ty.kind);
            let qualifiers = format!("{:?}", ty.qualifiers);
            let size = ty.size.map(|s| s.to_string()).unwrap_or_else(|| "Unknown".to_string());
            let details = self.get_type_details(&ty.kind);

            writeln!(html, "<tr id=\"type_{}\">", id)?;
            writeln!(html, "<td>{}</td>", id)?;
            writeln!(html, "<td>{}</td>", kind)?;
            writeln!(html, "<td>{}</td>", base)?;
            writeln!(html, "<td>{}</td>", qualifiers)?;
            writeln!(html, "<td>{}</td>", size)?;
            writeln!(html, "<td>{}</td>", details)?;
            writeln!(html, "</tr>")?;
        }

        writeln!(html, "</tbody>")?;
        writeln!(html, "</table>")?;
        writeln!(html, "</section>")?;
        Ok(())
    }

    fn get_symbol_kind_display(&self, kind: &SymbolKind) -> String {
        match kind {
            SymbolKind::Variable { is_global, is_static, is_extern, .. } => {
                let mut parts = vec!["Variable"];
                if *is_global { parts.push("global"); }
                if *is_static { parts.push("static"); }
                if *is_extern { parts.push("extern"); }
                parts.join(" ")
            }
            SymbolKind::Function { is_definition, is_inline, is_variadic, .. } => {
                let mut parts = vec!["Function"];
                if *is_definition { parts.push("definition"); }
                if *is_inline { parts.push("inline"); }
                if *is_variadic { parts.push("variadic"); }
                parts.join(" ")
            }
            SymbolKind::Typedef { .. } => "Typedef".to_string(),
            SymbolKind::EnumConstant { .. } => "EnumConstant".to_string(),
            SymbolKind::Label { .. } => "Label".to_string(),
            SymbolKind::Record { .. } => "Record".to_string(),
        }
    }

    fn get_type_display_name(&self, type_ref: TypeRef) -> String {
        let ty = self.ast.get_type(type_ref);
        match &ty.kind {
            TypeKind::Void => "void".to_string(),
            TypeKind::Bool => "_Bool".to_string(),
            TypeKind::Char { is_signed: true } => "char".to_string(),
            TypeKind::Char { is_signed: false } => "unsigned char".to_string(),
            TypeKind::Short { is_signed: true } => "short".to_string(),
            TypeKind::Short { is_signed: false } => "unsigned short".to_string(),
            TypeKind::Int { is_signed: true } => "int".to_string(),
            TypeKind::Int { is_signed: false } => "unsigned int".to_string(),
            TypeKind::Long { is_signed: true, is_long_long: false } => "long".to_string(),
            TypeKind::Long { is_signed: true, is_long_long: true } => "long long".to_string(),
            TypeKind::Long { is_signed: false, is_long_long: false } => "unsigned long".to_string(),
            TypeKind::Long { is_signed: false, is_long_long: true } => "unsigned long long".to_string(),
            TypeKind::Float => "float".to_string(),
            TypeKind::Double { is_long_double: false } => "double".to_string(),
            TypeKind::Double { is_long_double: true } => "long double".to_string(),
            TypeKind::Pointer { .. } => format!("{}*", self.get_type_display_name(TypeRef::new(1).unwrap())), // Simplified
            TypeKind::Array { .. } => "array".to_string(),
            TypeKind::Function { .. } => "function".to_string(),
            TypeKind::Record { tag, is_union, .. } => {
                let kind = if *is_union { "union" } else { "struct" };
                tag.map(|t| format!("{} {}", kind, t)).unwrap_or_else(|| kind.to_string())
            }
            TypeKind::Enum { tag, .. } => {
                tag.map(|t| format!("enum {}", t)).unwrap_or_else(|| "enum".to_string())
            }
            TypeKind::Typedef { name, .. } => name.to_string(),
            TypeKind::Incomplete => "incomplete".to_string(),
            TypeKind::Error => "error".to_string(),
            _ => "unknown".to_string(),
        }
    }

    fn get_type_kind_display(&self, kind: &TypeKind) -> String {
        match kind {
            TypeKind::Void => "Void".to_string(),
            TypeKind::Bool => "Bool".to_string(),
            TypeKind::Char { .. } => "Char".to_string(),
            TypeKind::Short { .. } => "Short".to_string(),
            TypeKind::Int { .. } => "Int".to_string(),
            TypeKind::Long { .. } => "Long".to_string(),
            TypeKind::Float => "Float".to_string(),
            TypeKind::Double { .. } => "Double".to_string(),
            TypeKind::Complex { .. } => "Complex".to_string(),
            TypeKind::Atomic { .. } => "Atomic".to_string(),
            TypeKind::Pointer { .. } => "Pointer".to_string(),
            TypeKind::Array { .. } => "Array".to_string(),
            TypeKind::Function { .. } => "Function".to_string(),
            TypeKind::Record { is_union, .. } => {
                if *is_union { "Union" } else { "Struct" }.to_string()
            }
            TypeKind::Enum { .. } => "Enum".to_string(),
            TypeKind::Typedef { .. } => "Typedef".to_string(),
            TypeKind::Incomplete => "Incomplete".to_string(),
            TypeKind::Error => "Error".to_string(),
        }
    }

    fn get_type_base_display(&self, kind: &TypeKind) -> String {
        match kind {
            TypeKind::Pointer { pointee } => self.get_type_display_name(*pointee),
            TypeKind::Array { element_type, .. } => self.get_type_display_name(*element_type),
            TypeKind::Function { return_type, .. } => self.get_type_display_name(*return_type),
            TypeKind::Complex { base_type } => self.get_type_display_name(*base_type),
            TypeKind::Atomic { base_type } => self.get_type_display_name(*base_type),
            _ => "-".to_string(),
        }
    }

    fn get_type_details(&self, kind: &TypeKind) -> String {
        match kind {
            TypeKind::Array { size, .. } => {
                match size {
                    ArraySizeType::Constant(size) => format!("size: {}", size),
                    ArraySizeType::Variable(_) => "variable size".to_string(),
                    ArraySizeType::Incomplete => "incomplete".to_string(),
                    ArraySizeType::Star => "*".to_string(),
                }
            }
            TypeKind::Function { parameters, is_variadic, .. } => {
                let param_count = parameters.len();
                let variadic = if *is_variadic { ", ..." } else { "" };
                format!("{} parameters{}", param_count, variadic)
            }
            TypeKind::Record { members, is_complete, .. } => {
                let complete = if *is_complete { "complete" } else { "incomplete" };
                format!("{} members, {}", members.len(), complete)
            }
            TypeKind::Enum { enumerators, is_complete, .. } => {
                let complete = if *is_complete { "complete" } else { "incomplete" };
                format!("{} enumerators, {}", enumerators.len(), complete)
            }
            _ => "-".to_string(),
        }
    }

    fn escape_html(&self, text: &str) -> String {
        text.replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace("\"", "&quot;")
            .replace("'", "&#x27;")
    }
}