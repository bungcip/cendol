use std::fmt::Write;
use std::path::PathBuf;

use crate::ast::*;
use crate::diagnostic::*;
use crate::lang_options::LangOptions;
use crate::lexer::{Lexer, TokenKind};
use crate::pp::{PPConfig, Preprocessor};
use crate::semantic::*;
use crate::source_manager::*;
use target_lexicon::Triple as TargetTriple;

/// Configuration for AST dump output
#[derive(Debug, Clone)]
pub struct DumpConfig {
    pub pretty_print: bool,
    pub include_source: bool,
    pub max_depth: Option<usize>,
    pub max_source_lines: Option<usize>,
    pub output_path: PathBuf,
}

impl Default for DumpConfig {
    fn default() -> Self {
        DumpConfig {
            pretty_print: true,
            include_source: false,
            max_depth: None,
            max_source_lines: None,
            output_path: PathBuf::from("ast_dump.html"),
        }
    }
}

/// Main AST dumper that generates HTML visualization
pub struct AstDumper<'src> {
    ast: &'src Ast,
    symbol_table: &'src SymbolTable,
    diag: &'src mut DiagnosticEngine,
    source_manager: &'src mut SourceManager,
    lang_opts: &'src LangOptions,
    target_info: &'src TargetTriple,
    config: DumpConfig,
}

impl<'src> AstDumper<'src> {
    /// Create a new AST dumper
    pub fn new(
        ast: &'src Ast,
        symbol_table: &'src SymbolTable,
        diag: &'src mut DiagnosticEngine,
        source_manager: &'src mut SourceManager,
        lang_opts: &'src LangOptions,
        target_info: &'src TargetTriple,
        config: DumpConfig,
    ) -> Self {
        AstDumper {
            ast,
            symbol_table,
            diag,
            source_manager,
            lang_opts,
            target_info,
            config,
        }
    }

    /// Generate the complete HTML dump
    pub fn generate_html(&mut self) -> Result<String, std::fmt::Error> {
        let mut html = String::new();

        // HTML header
        self.write_html_header(&mut html)?;

        // Body start
        writeln!(html, "<body>")?;
        writeln!(html, "<h1>Cendol Compiler AST Dump</h1>")?;

        // Generate table of contents
        self.generate_table_of_contents(&mut html)?;

        // Generate sections
        self.generate_ast_section(&mut html)?;
        self.generate_symbol_table_section(&mut html)?;
        self.generate_scope_table_section(&mut html)?;
        self.generate_type_table_section(&mut html)?;
        self.generate_diagnostics_section(&mut html)?;

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
        writeln!(
            html,
            r#"
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
                padding: 8px;
                margin: 5px 0;
                border-radius: 4px;
                font-size: 0.85em;
                border-left: 3px solid #3498db;
                line-height: 1.4;
            }}

            .semantic-info a {{
                color: #2980b9;
                text-decoration: none;
                font-weight: bold;
            }}

            .semantic-info a:hover {{
                text-decoration: underline;
            }}

            .source-code {{
                background-color: #f8f9fa;
                border: 1px solid #e9ecef;
                border-radius: 4px;
                padding: 8px;
                margin: 5px 0;
                font-family: 'Courier New', monospace;
                font-size: 0.85em;
                color: #495057;
                white-space: pre-wrap;
                line-height: 1.4;
            }}

            /* Syntax highlighting classes */
            .c-keyword {{
                color: #0000ff;
                font-weight: bold;
            }}

            .c-type {{
                color: #267f99;
                font-weight: bold;
            }}

            .c-operator {{
                color: #000000;
                font-weight: bold;
            }}

            .c-literal {{
                color: #09885a;
            }}

            .c-string {{
                color: #a31515;
            }}

            .c-comment {{
                color: #008000;
                font-style: italic;
            }}

            .c-preprocessor {{
                color: #af00db;
            }}

            .c-identifier {{
                color: #001080;
            }}

            .c-number {{
                color: #09885a;
            }}

            .c-punctuation {{
                color: #000000;
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

            .ast-controls {{
                display: flex;
                gap: 20px;
                margin-bottom: 20px;
                align-items: center;
            }}

            .tree-controls {{
                display: flex;
                gap: 10px;
            }}

            .tree-controls button {{
                padding: 8px 16px;
                background-color: #3498db;
                color: white;
                border: none;
                border-radius: 4px;
                cursor: pointer;
                font-size: 14px;
            }}

            .tree-controls button:hover {{
                background-color: #2980b9;
            }}

            .ast-tree li.collapsed > ul {{
                display: none;
            }}

            .ast-tree li.expanded > ul {{
                display: block;
            }}

            .ast-tree .node-content {{
                display: flex;
                align-items: center;
                cursor: pointer;
                padding: 2px 0;
            }}

            .ast-tree .node-content:hover {{
                background-color: #f0f8ff;
            }}

            .ast-tree .toggle-icon {{
                margin-right: 5px;
                font-size: 12px;
                color: #666;
                transition: transform 0.2s;
            }}

            .ast-tree li.collapsed .toggle-icon {{
                transform: rotate(0deg);
            }}

            .ast-tree li.expanded .toggle-icon {{
                transform: rotate(90deg);
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

            #table-of-contents {{
                position: fixed;
                top: 20px;
                right: 20px;
                width: 200px;
                background-color: white;
                border: 1px solid #ddd;
                border-radius: 4px;
                padding: 15px;
                box-shadow: 0 2px 4px rgba(0,0,0,0.1);
                max-height: 80vh;
                overflow-y: auto;
                z-index: 1000;
            }}

            #table-of-contents h2 {{
                font-size: 1.1em;
                margin-top: 0;
                margin-bottom: 10px;
                color: #2c3e50;
            }}

            #table-of-contents ul {{
                list-style-type: none;
                padding: 0;
                margin: 0;
            }}

            #table-of-contents li {{
                margin: 5px 0;
            }}

            #table-of-contents a {{
                color: #3498db;
                text-decoration: none;
                font-size: 0.9em;
            }}

            #table-of-contents a:hover {{
                text-decoration: underline;
            }}

            /* Node type filtering */
            .node-filter {{
                margin: 10px 0;
                padding: 10px;
                background-color: #f8f9fa;
                border-radius: 4px;
            }}

            .node-filter select {{
                padding: 5px;
                border: 1px solid #ddd;
                border-radius: 3px;
                margin-left: 5px;
            }}

            .node-filter label {{
                font-weight: bold;
                color: #2c3e50;
            }}
        "#
        )?;
        Ok(())
    }

    fn write_javascript(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(
            html,
            r#"
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
                const searchInput = document.getElementById('ast-search');

                function performSearch() {{
                    const query = searchInput.value;
                    searchAst(query);
                }}

                if (searchInput) {{
                    searchInput.addEventListener('input', performSearch);
                }}
            }}

            function toggleAstNode(element) {{
                const li = element.parentElement;
                const isCollapsed = li.classList.contains('collapsed');

                if (isCollapsed) {{
                    li.classList.remove('collapsed');
                    li.classList.add('expanded');
                }} else {{
                    li.classList.remove('expanded');
                    li.classList.add('collapsed');
                }}
            }}

            function expandAllAst() {{
                const collapsedNodes = document.querySelectorAll('#ast-tree li.collapsed');
                collapsedNodes.forEach(node => {{
                    node.classList.remove('collapsed');
                    node.classList.add('expanded');
                }});
            }}

            function collapseAllAst() {{
                const expandedNodes = document.querySelectorAll('#ast-tree li.expanded');
                expandedNodes.forEach(node => {{
                    node.classList.remove('expanded');
                    node.classList.add('collapsed');
                }});
            }}

            function searchAst(query) {{
                const lowerQuery = query.toLowerCase();
                const allNodes = document.querySelectorAll('#ast-tree li');

                allNodes.forEach(node => {{
                    const nodeType = node.querySelector('.node-type');
                    const spanInfo = node.querySelector('.span-info');
                    const text = (nodeType ? nodeType.textContent : '') + (spanInfo ? spanInfo.textContent : '');

                    if (text.toLowerCase().includes(lowerQuery)) {{
                        node.style.display = '';
                        // Expand parent nodes to show this result
                        let parent = node.parentElement;
                        while (parent && parent.id !== 'ast-tree') {{
                            if (parent.tagName === 'LI') {{
                                parent.classList.remove('collapsed');
                                parent.classList.add('expanded');
                            }}
                            parent = parent.parentElement;
                        }}
                    }} else {{
                        node.style.display = 'none';
                    }}
                }});
            }}

            function filterAstByType(nodeType) {{
                const allNodes = document.querySelectorAll('#ast-tree li');

                allNodes.forEach(node => {{
                    const nodeTypeSpan = node.querySelector('.node-type');
                    const nodeTypeText = nodeTypeSpan ? nodeTypeSpan.textContent : '';

                    if (!nodeType || nodeTypeText === nodeType) {{
                        node.style.display = '';
                    }} else {{
                        node.style.display = 'none';
                    }}
                }});
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

                // Setup AST search
                const astSearchInput = document.getElementById('ast-search');
                if (astSearchInput) {{
                    astSearchInput.addEventListener('input', function() {{
                        searchAst(this.value);
                    }});
                }}

                // Setup node type filtering
                const nodeTypeFilter = document.getElementById('node-type-filter');
                if (nodeTypeFilter) {{
                    nodeTypeFilter.addEventListener('change', function() {{
                        filterAstByType(this.value);
                    }});
                }}
            }});
        "#
        )?;
        Ok(())
    }

    fn generate_table_of_contents(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<nav id=\"table-of-contents\">")?;
        writeln!(html, "<h2>Table of Contents</h2>")?;
        writeln!(html, "<ul>")?;
        writeln!(html, "<li><a href=\"#ast-section\">Abstract Syntax Tree</a></li>")?;
        writeln!(html, "<li><a href=\"#symbols-section\">Symbol Table</a></li>")?;
        writeln!(html, "<li><a href=\"#scopes-section\">Scope Table</a></li>")?;
        writeln!(html, "<li><a href=\"#types-section\">Type Table</a></li>")?;
        writeln!(html, "<li><a href=\"#diagnostics-section\">Diagnostics</a></li>")?;
        writeln!(html, "</ul>")?;
        writeln!(html, "</nav>")?;
        Ok(())
    }

    fn generate_ast_section(&mut self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<section id=\"ast-section\">")?;
        writeln!(html, "<h2>Abstract Syntax Tree</h2>")?;

        // Add controls for AST tree
        writeln!(html, "<div class=\"ast-controls\">")?;
        writeln!(html, "<div class=\"search-container\">")?;
        writeln!(
            html,
            "<input type=\"text\" id=\"ast-search\" placeholder=\"Search AST nodes...\">"
        )?;
        writeln!(html, "</div>")?;
        writeln!(html, "<div class=\"tree-controls\">")?;
        writeln!(html, "<button onclick=\"expandAllAst()\">Expand All</button>")?;
        writeln!(html, "<button onclick=\"collapseAllAst()\">Collapse All</button>")?;
        writeln!(html, "</div>")?;
        writeln!(html, "<div class=\"node-filter\">")?;
        writeln!(html, "<label for=\"node-type-filter\">Filter by type:</label>")?;
        writeln!(html, "<select id=\"node-type-filter\">")?;
        writeln!(html, "<option value=\"\">All Types</option>")?;
        writeln!(html, "<option value=\"FunctionDef\">FunctionDef</option>")?;
        writeln!(html, "<option value=\"Declaration\">Declaration</option>")?;
        writeln!(html, "<option value=\"BinaryOp\">BinaryOp</option>")?;
        writeln!(html, "<option value=\"UnaryOp\">UnaryOp</option>")?;
        writeln!(html, "<option value=\"If\">If</option>")?;
        writeln!(html, "<option value=\"While\">While</option>")?;
        writeln!(html, "<option value=\"For\">For</option>")?;
        writeln!(html, "<option value=\"Return\">Return</option>")?;
        writeln!(html, "<option value=\"CompoundStatement\">CompoundStatement</option>")?;
        writeln!(html, "</select>")?;
        writeln!(html, "</div>")?;
        writeln!(html, "</div>")?;

        writeln!(html, "<div id=\"ast-tree\">")?;

        // Find the root node (TranslationUnit)
        if let Some(root_node) = self.ast.get_root_node() {
            self.generate_ast_tree(html, root_node, 0)?;
        } else {
            writeln!(html, "<p class=\"error\">No root AST node found</p>")?;
        }

        writeln!(html, "</div>")?;
        writeln!(html, "</section>")?;
        Ok(())
    }

    fn generate_ast_tree(&mut self, html: &mut String, node: &Node, depth: usize) -> Result<(), std::fmt::Error> {
        if let Some(max_depth) = self.config.max_depth
            && depth > max_depth
        {
            writeln!(html, "<li class=\"ast-node\">... (truncated)</li>")?;
            return Ok(());
        }

        let node_type = self.get_node_type_name(&node.kind);
        let span_info = format!("[0:{}-0:{}]", node.span.start.offset(), node.span.end.offset());

        let has_children = self.node_has_children(node);
        let collapsed_class = if depth > 0 { " collapsed" } else { "" };

        writeln!(html, "<ul class=\"ast-tree\">")?;
        writeln!(
            html,
            "<li class=\"ast-node{}\" id=\"node_{}\">",
            collapsed_class,
            node.span.start.offset()
        )?;
        if has_children {
            writeln!(html, "<div class=\"node-content\" onclick=\"toggleAstNode(this)\">")?;
            writeln!(html, "<span class=\"toggle-icon\">▶</span>")?;
        } else {
            writeln!(html, "<div class=\"node-content\">")?;
        }
        writeln!(
            html,
            "<span class=\"node-type\">{}</span>",
            self.escape_html(&node_type)
        )?;
        writeln!(
            html,
            "<span class=\"span-info\">{}</span>",
            self.escape_html(&span_info)
        )?;
        writeln!(html, "</div>")?;

        // Add source code snippet if enabled
        if self.config.include_source {
            let raw_text = self.source_manager.get_source_text(node.span);
            let escaped_text = self.escape_html(raw_text);
            let lines: Vec<&str> = escaped_text.split('\n').collect();
            let (start_line, _) = self.source_manager.get_line_column(node.span.start).unwrap_or((1, 1));
            let mut text_with_lines = String::new();

            // Apply truncation if max_source_lines is set
            if let Some(max_lines) = self.config.max_source_lines {
                if lines.len() > max_lines {
                    // Show first max_lines - 1 lines, then "..."
                    for (i, line) in lines.iter().enumerate().take(max_lines - 1) {
                        let line_num = start_line + i as u32;
                        text_with_lines.push_str(&format!("{}: {}\n", line_num, line));
                    }
                    text_with_lines.push_str("...\n");
                } else {
                    for (i, line) in lines.iter().enumerate() {
                        let line_num = start_line + i as u32;
                        text_with_lines.push_str(&format!("{}: {}\n", line_num, line));
                    }
                }
            } else {
                for (i, line) in lines.iter().enumerate() {
                    let line_num = start_line + i as u32;
                    text_with_lines.push_str(&format!("{}: {}\n", line_num, line));
                }
            }

            if text_with_lines.ends_with('\n') {
                text_with_lines.pop();
            }
            let highlighted_text = self.highlight_source_code(&text_with_lines, node.span);
            let html_text = highlighted_text.replace('\n', "<br>");
            writeln!(html, "<div class=\"source-code\">{}</div>", html_text)?;
        }

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
            NodeKind::TernaryOp(_, _, _) => "TernaryOp".to_string(),
            NodeKind::PostIncrement(_) => "PostIncrement".to_string(),
            NodeKind::PostDecrement(_) => "PostDecrement".to_string(),
            NodeKind::Assignment(op, _, _) => format!("Assignment({:?})", op),
            NodeKind::FunctionCall(_, _) => "FunctionCall".to_string(),
            NodeKind::MemberAccess(_, _, _) => "MemberAccess".to_string(),
            NodeKind::IndexAccess(_, _) => "IndexAccess".to_string(),
            NodeKind::Cast(_, _) => "Cast".to_string(),
            NodeKind::SizeOfExpr(_) => "SizeOfExpr".to_string(),
            NodeKind::SizeOfType(_) => "SizeOfType".to_string(),
            NodeKind::AlignOf(_) => "AlignOf".to_string(),
            NodeKind::CompoundLiteral(_, _) => "CompoundLiteral".to_string(),
            NodeKind::GenericSelection(_, _) => "GenericSelection".to_string(),
            NodeKind::VaArg(_, _) => "VaArg".to_string(),
            NodeKind::GnuStatementExpression(_, _) => "GnuStatementExpression".to_string(),
            NodeKind::CompoundStatement(_) => "CompoundStatement".to_string(),
            NodeKind::If(_) => "If".to_string(),
            NodeKind::While(_) => "While".to_string(),
            NodeKind::DoWhile(_, _) => "DoWhile".to_string(),
            NodeKind::For(_) => "For".to_string(),
            NodeKind::Return(_) => "Return".to_string(),
            NodeKind::Break => "Break".to_string(),
            NodeKind::Continue => "Continue".to_string(),
            NodeKind::Goto(_) => "Goto".to_string(),
            NodeKind::Label(_, _) => "Label".to_string(),
            NodeKind::Switch(_, _) => "Switch".to_string(),
            NodeKind::Case(_, _) => "Case".to_string(),
            NodeKind::CaseRange(_, _, _) => "CaseRange".to_string(),
            NodeKind::Default(_) => "Default".to_string(),
            NodeKind::ExpressionStatement(_) => "ExpressionStatement".to_string(),
            NodeKind::EmptyStatement => "EmptyStatement".to_string(),
            NodeKind::EnumConstant(_, _) => "EnumConstant".to_string(),
            NodeKind::StaticAssert(_, _) => "StaticAssert".to_string(),
            NodeKind::Dummy => "Dummy".to_string(),
            // Semantic nodes
            NodeKind::VarDecl(_) => "VarDecl".to_string(),
            NodeKind::FunctionDecl(_) => "FunctionDecl".to_string(),
            NodeKind::TypedefDecl(_) => "TypedefDecl".to_string(),
            NodeKind::RecordDecl(_) => "RecordDecl".to_string(),
        }
    }

    fn generate_semantic_info(&self, html: &mut String, node: &Node) -> Result<(), std::fmt::Error> {
        let mut info_parts = Vec::new();

        if let Some(type_ref) = node.resolved_type.get() {
            let type_display = self.get_enhanced_type_display_name(type_ref);
            info_parts.push(format!(
                "Type: <a href=\"#type_{}\">{}</a>",
                type_ref.get(),
                type_display
            ));
        }

        if let Some(symbol_ref) = node.resolved_symbol.get() {
            let symbol = self.symbol_table.get_symbol_entry(symbol_ref);
            let symbol_info = self.get_enhanced_symbol_info(symbol_ref, symbol);
            info_parts.push(format!(
                "Symbol: <a href=\"#sym_{}\">{}</a>{}",
                symbol_ref.get(),
                self.escape_html(&symbol.name.to_string()),
                self.escape_html(&symbol_info)
            ));
        }

        if !info_parts.is_empty() {
            writeln!(html, "<div class=\"semantic-info\">")?;
            for (i, part) in info_parts.iter().enumerate() {
                if i > 0 {
                    writeln!(html, "<br>")?;
                }
                writeln!(html, "{}", part)?;
            }
            writeln!(html, "</div>")?;
        }

        Ok(())
    }

    fn generate_child_nodes(&mut self, html: &mut String, node: &Node, depth: usize) -> Result<(), std::fmt::Error> {
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
            NodeKind::Declaration(decl) => {
                // Handle declarators and initializers
                for init_decl in &decl.init_declarators {
                    self.generate_declarator_children(html, &init_decl.declarator, depth + 1)?;
                    if let Some(initializer) = &init_decl.initializer {
                        self.generate_initializer_children(html, initializer, depth + 1)?;
                    }
                }
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
            NodeKind::TernaryOp(cond, then_expr, else_expr) => {
                let cond_node = self.ast.get_node(*cond);
                let then_node = self.ast.get_node(*then_expr);
                let else_node = self.ast.get_node(*else_expr);
                self.generate_ast_tree(html, cond_node, depth + 1)?;
                self.generate_ast_tree(html, then_node, depth + 1)?;
                self.generate_ast_tree(html, else_node, depth + 1)?;
            }
            NodeKind::PostIncrement(operand) | NodeKind::PostDecrement(operand) => {
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
            NodeKind::MemberAccess(object, _, _) => {
                let object_node = self.ast.get_node(*object);
                self.generate_ast_tree(html, object_node, depth + 1)?;
            }
            NodeKind::IndexAccess(array, index) => {
                let array_node = self.ast.get_node(*array);
                let index_node = self.ast.get_node(*index);
                self.generate_ast_tree(html, array_node, depth + 1)?;
                self.generate_ast_tree(html, index_node, depth + 1)?;
            }
            NodeKind::Cast(_, expr) => {
                let expr_node = self.ast.get_node(*expr);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
            }
            NodeKind::SizeOfExpr(expr) => {
                let expr_node = self.ast.get_node(*expr);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
            }
            NodeKind::CompoundLiteral(_, init_ref) => {
                let initializer = self.ast.get_initializer(*init_ref);
                self.generate_initializer_children(html, initializer, depth + 1)?;
            }
            NodeKind::GenericSelection(ctrl_expr, associations) => {
                let ctrl_node = self.ast.get_node(*ctrl_expr);
                self.generate_ast_tree(html, ctrl_node, depth + 1)?;
                for assoc in associations {
                    let result_node = self.ast.get_node(assoc.result_expr);
                    self.generate_ast_tree(html, result_node, depth + 1)?;
                }
            }
            NodeKind::VaArg(va_list_expr, _) => {
                let expr_node = self.ast.get_node(*va_list_expr);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
            }
            NodeKind::GnuStatementExpression(compound_stmt, result_expr) => {
                let compound_node = self.ast.get_node(*compound_stmt);
                let result_node = self.ast.get_node(*result_expr);
                self.generate_ast_tree(html, compound_node, depth + 1)?;
                self.generate_ast_tree(html, result_node, depth + 1)?;
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
            NodeKind::DoWhile(body, condition) => {
                let body_node = self.ast.get_node(*body);
                let cond_node = self.ast.get_node(*condition);
                self.generate_ast_tree(html, body_node, depth + 1)?;
                self.generate_ast_tree(html, cond_node, depth + 1)?;
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
            NodeKind::Goto(_) => {} // No children
            NodeKind::Label(_, stmt) => {
                let stmt_node = self.ast.get_node(*stmt);
                self.generate_ast_tree(html, stmt_node, depth + 1)?;
            }
            NodeKind::Switch(condition, body) => {
                let cond_node = self.ast.get_node(*condition);
                let body_node = self.ast.get_node(*body);
                self.generate_ast_tree(html, cond_node, depth + 1)?;
                self.generate_ast_tree(html, body_node, depth + 1)?;
            }
            NodeKind::Case(expr, stmt) => {
                let expr_node = self.ast.get_node(*expr);
                let stmt_node = self.ast.get_node(*stmt);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
                self.generate_ast_tree(html, stmt_node, depth + 1)?;
            }
            NodeKind::CaseRange(start, end, stmt) => {
                let start_node = self.ast.get_node(*start);
                let end_node = self.ast.get_node(*end);
                let stmt_node = self.ast.get_node(*stmt);
                self.generate_ast_tree(html, start_node, depth + 1)?;
                self.generate_ast_tree(html, end_node, depth + 1)?;
                self.generate_ast_tree(html, stmt_node, depth + 1)?;
            }
            NodeKind::Default(stmt) => {
                let stmt_node = self.ast.get_node(*stmt);
                self.generate_ast_tree(html, stmt_node, depth + 1)?;
            }
            NodeKind::ExpressionStatement(Some(expr)) => {
                let expr_node = self.ast.get_node(*expr);
                self.generate_ast_tree(html, expr_node, depth + 1)?;
            }
            NodeKind::EnumConstant(_, Some(value_expr)) => {
                let value_node = self.ast.get_node(*value_expr);
                self.generate_ast_tree(html, value_node, depth + 1)?;
            }
            NodeKind::StaticAssert(condition, _) => {
                let cond_node = self.ast.get_node(*condition);
                self.generate_ast_tree(html, cond_node, depth + 1)?;
            }
            // Leaf nodes or unhandled cases
            _ => {}
        }
        Ok(())
    }

    fn generate_declarator_children(
        &mut self,
        html: &mut String,
        declarator: &Declarator,
        depth: usize,
    ) -> Result<(), std::fmt::Error> {
        match declarator {
            Declarator::Identifier(_, _, next) => {
                if let Some(next_decl) = next {
                    self.generate_declarator_children(html, next_decl, depth)?;
                }
            }
            Declarator::Abstract => {
                // Abstract declarator has no children
            }
            Declarator::Pointer(_, next) => {
                if let Some(next_decl) = next {
                    self.generate_declarator_children(html, next_decl, depth)?;
                }
            }
            Declarator::Array(decl, size) => {
                match size {
                    ArraySize::Expression { .. } => {
                        // For now, don't generate children for expression arrays
                    }
                    ArraySize::VlaSpecifier { size: Some(expr), .. } => {
                        let expr_node = self.ast.get_node(*expr);
                        self.generate_ast_tree(html, expr_node, depth)?;
                    }
                    _ => {}
                }
                self.generate_declarator_children(html, decl, depth)?;
            }
            Declarator::Function(decl, params) => {
                for param in params {
                    if let Some(declarator) = &param.declarator {
                        self.generate_declarator_children(html, declarator, depth)?;
                    }
                }
                self.generate_declarator_children(html, decl, depth)?;
            }
            Declarator::BitField(decl, bit_width_expr) => {
                // Generate the bit width expression as a child
                let expr_node = self.ast.get_node(*bit_width_expr);
                self.generate_ast_tree(html, expr_node, depth)?;
                // Also generate children for the inner declarator
                self.generate_declarator_children(html, decl, depth)?;
            }
            Declarator::AnonymousRecord(_, members) => {
                for member in members {
                    for init_decl in &member.init_declarators {
                        self.generate_declarator_children(html, &init_decl.declarator, depth)?;
                        if let Some(initializer) = &init_decl.initializer {
                            self.generate_initializer_children(html, initializer, depth)?;
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn generate_initializer_children(
        &mut self,
        html: &mut String,
        initializer: &Initializer,
        depth: usize,
    ) -> Result<(), std::fmt::Error> {
        match initializer {
            Initializer::Expression(expr) => {
                let expr_node = self.ast.get_node(*expr);
                self.generate_ast_tree(html, expr_node, depth)?;
            }
            Initializer::List(designated_inits) => {
                for designated in designated_inits {
                    for designator in &designated.designation {
                        if let Designator::ArrayIndex(index_expr) = designator {
                            let index_node = self.ast.get_node(*index_expr);
                            self.generate_ast_tree(html, index_node, depth)?;
                        }
                    }
                    self.generate_initializer_children(html, &designated.initializer, depth)?;
                }
            }
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
            let type_link = format!(
                "<a href=\"#type_{}\">{}</a>",
                entry.type_info.get(),
                self.get_type_display_name(entry.type_info)
            );
            let scope_link = format!("<a href=\"#scope_{}\">{}</a>", entry.scope_id, entry.scope_id);
            let location = format!(
                "[{}:{}-{}:{}]",
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
            let parent = scope
                .parent
                .map(|p| p.get().to_string())
                .unwrap_or_else(|| "None".to_string());
            let kind = self.escape_html(&format!("{:?}", scope.kind));
            let level = scope.level;
            let symbols: Vec<String> = scope
                .symbols
                .values()
                .map(|&ref_| {
                    format!(
                        "<a href=\"#sym_{}\">{}</a>",
                        ref_.get(),
                        self.escape_html(&self.symbol_table.get_symbol_entry(ref_).name.to_string())
                    )
                })
                .collect();
            let _symbols_str = self.escape_html(&symbols.join(", "));
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
            let qualifiers = self.escape_html(&format!("{:?}", ty.qualifiers));
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

    fn generate_diagnostics_section(&self, html: &mut String) -> Result<(), std::fmt::Error> {
        writeln!(html, "<section id=\"diagnostics-section\">")?;
        writeln!(html, "<h2>Diagnostics</h2>")?;
        writeln!(html, "<table id=\"diagnostics-table\">")?;
        writeln!(html, "<thead>")?;
        writeln!(html, "<tr>")?;
        writeln!(html, "<th>Level</th>")?;
        writeln!(html, "<th>Message</th>")?;
        writeln!(html, "<th>Location</th>")?;
        writeln!(html, "<th>Code</th>")?;
        writeln!(html, "<th>Hints</th>")?;
        writeln!(html, "</tr>")?;
        writeln!(html, "</thead>")?;
        writeln!(html, "<tbody>")?;

        for (i, diag) in self.diag.diagnostics().iter().enumerate() {
            let id = i + 1;
            let level = match diag.level {
                crate::diagnostic::DiagnosticLevel::Error => "<span class=\"error\">Error</span>",
                crate::diagnostic::DiagnosticLevel::Warning => "<span class=\"warning\">Warning</span>",
                crate::diagnostic::DiagnosticLevel::Note => "Note",
            };
            let message = self.escape_html(&diag.message);
            let location = format!(
                "[{}:{}-{}:{}]",
                diag.location.start.source_id(),
                diag.location.start.offset(),
                diag.location.end.source_id(),
                diag.location.end.offset()
            );
            let code = diag
                .code
                .as_ref()
                .map(|c| self.escape_html(c))
                .unwrap_or_else(|| "-".to_string());
            let hints = if diag.hints.is_empty() {
                "-".to_string()
            } else {
                diag.hints
                    .iter()
                    .map(|h| self.escape_html(h))
                    .collect::<Vec<_>>()
                    .join("<br>")
            };

            writeln!(html, "<tr id=\"diag_{}\">", id)?;
            writeln!(html, "<td>{}</td>", level)?;
            writeln!(html, "<td>{}</td>", message)?;
            writeln!(html, "<td>{}</td>", location)?;
            writeln!(html, "<td>{}</td>", code)?;
            writeln!(html, "<td>{}</td>", hints)?;
            writeln!(html, "</tr>")?;
        }

        writeln!(html, "</tbody>")?;
        writeln!(html, "</table>")?;
        writeln!(html, "</section>")?;
        Ok(())
    }

    fn get_symbol_kind_display(&self, kind: &SymbolKind) -> String {
        match kind {
            SymbolKind::Variable {
                is_global,
                is_static,
                is_extern,
                ..
            } => {
                let mut parts = vec!["Variable"];
                if *is_global {
                    parts.push("global");
                }
                if *is_static {
                    parts.push("static");
                }
                if *is_extern {
                    parts.push("extern");
                }
                parts.join(" ")
            }
            SymbolKind::Function {
                is_definition,
                is_inline,
                is_variadic,
                ..
            } => {
                let mut parts = vec!["Function"];
                if *is_definition {
                    parts.push("definition");
                }
                if *is_inline {
                    parts.push("inline");
                }
                if *is_variadic {
                    parts.push("variadic");
                }
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
            TypeKind::Long {
                is_signed: true,
                is_long_long: false,
            } => "long".to_string(),
            TypeKind::Long {
                is_signed: true,
                is_long_long: true,
            } => "long long".to_string(),
            TypeKind::Long {
                is_signed: false,
                is_long_long: false,
            } => "unsigned long".to_string(),
            TypeKind::Long {
                is_signed: false,
                is_long_long: true,
            } => "unsigned long long".to_string(),
            TypeKind::Float => "float".to_string(),
            TypeKind::Double { is_long_double: false } => "double".to_string(),
            TypeKind::Double { is_long_double: true } => "long double".to_string(),
            TypeKind::Pointer { .. } => {
                format!("{}*", self.get_type_display_name(TypeRef::new(1).unwrap()))
            } // Simplified
            TypeKind::Array { .. } => "array".to_string(),
            TypeKind::Function { .. } => "function".to_string(),
            TypeKind::Record { tag, is_union, .. } => {
                let kind = if *is_union { "union" } else { "struct" };
                tag.map(|t| format!("{} {}", kind, t))
                    .unwrap_or_else(|| kind.to_string())
            }
            TypeKind::Enum { tag, .. } => tag.map(|t| format!("enum {}", t)).unwrap_or_else(|| "enum".to_string()),
            TypeKind::Typedef { name, .. } => name.to_string(),
            TypeKind::Incomplete => "incomplete".to_string(),
            TypeKind::Error => "error".to_string(),
            _ => "unknown".to_string(),
        }
    }

    fn get_enhanced_type_display_name(&self, type_ref: TypeRef) -> String {
        let ty = self.ast.get_type(type_ref);
        let mut display = self.get_type_display_name(type_ref);

        // Add qualifiers if present
        if !ty.qualifiers.is_empty() {
            let qual_str = format!("{:?}", ty.qualifiers).to_lowercase();
            display = format!("{} {}", qual_str, display);
        }

        // Add size information if available
        if let Some(size) = ty.size {
            display = format!("{} ({} bytes)", display, size);
        }

        display
    }

    fn get_enhanced_symbol_info(&self, _symbol_ref: SymbolEntryRef, symbol: &SymbolEntry) -> String {
        let mut info_parts = Vec::new();

        // Add definition/referenced status
        let def_status = if symbol.is_defined { "defined" } else { "declared" };
        let ref_status = if symbol.is_referenced { "referenced" } else { "unused" };
        info_parts.push(format!("({} {})", def_status, ref_status));

        // Add storage class if present
        if let Some(storage_class) = symbol.storage_class {
            info_parts.push(format!(
                "storage: {}",
                self.escape_html(&format!("{:?}", storage_class))
            ));
        }

        // Add symbol kind specific information
        match &symbol.kind {
            SymbolKind::Variable {
                is_global,
                is_static,
                is_extern,
                initializer,
            } => {
                let mut attrs = Vec::new();
                if *is_global {
                    attrs.push("global");
                }
                if *is_static {
                    attrs.push("static");
                }
                if *is_extern {
                    attrs.push("extern");
                }
                if !attrs.is_empty() {
                    info_parts.push(format!("attrs: {}", self.escape_html(&attrs.join(", "))));
                }
                if let Some(init_ref) = initializer {
                    info_parts.push(format!("initializer: node {}", init_ref.get()));
                }
            }
            SymbolKind::Function {
                is_definition,
                is_inline,
                is_variadic,
                parameters,
            } => {
                let mut attrs = Vec::new();
                if *is_definition {
                    attrs.push("definition");
                }
                if *is_inline {
                    attrs.push("inline");
                }
                if *is_variadic {
                    attrs.push("variadic");
                }
                if !attrs.is_empty() {
                    info_parts.push(format!("attrs: {}", self.escape_html(&attrs.join(", "))));
                }
                info_parts.push(format!("params: {}", parameters.len()));
            }
            SymbolKind::Typedef { aliased_type } => {
                let aliased_name = self.get_type_display_name(*aliased_type);
                info_parts.push(format!("aliased: {}", self.escape_html(&aliased_name)));
            }
            SymbolKind::EnumConstant { value } => {
                info_parts.push(format!("value: {}", value));
            }
            SymbolKind::Label { is_defined, is_used } => {
                let def_status = if *is_defined { "defined" } else { "undeclared" };
                let use_status = if *is_used { "used" } else { "unused" };
                info_parts.push(format!(
                    "label: {} {}",
                    self.escape_html(def_status),
                    self.escape_html(use_status)
                ));
            }
            SymbolKind::Record {
                is_complete,
                members,
                size,
                alignment,
            } => {
                let complete_status = if *is_complete { "complete" } else { "incomplete" };
                info_parts.push(format!(
                    "record: {} ({} members)",
                    self.escape_html(complete_status),
                    members.len()
                ));
                if let Some(size) = size {
                    info_parts.push(format!("size: {} bytes", size));
                }
                if let Some(align) = alignment {
                    info_parts.push(format!("align: {} bytes", align));
                }
            }
        }

        if !info_parts.is_empty() {
            format!(" {}", info_parts.join(", "))
        } else {
            String::new()
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
            TypeKind::Record { is_union, .. } => if *is_union { "Union" } else { "Struct" }.to_string(),
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
            TypeKind::Array { size, .. } => match size {
                ArraySizeType::Constant(size) => format!("size: {}", size),
                ArraySizeType::Variable(_) => "variable size".to_string(),
                ArraySizeType::Incomplete => "incomplete".to_string(),
                ArraySizeType::Star => "*".to_string(),
            },
            TypeKind::Function {
                parameters,
                is_variadic,
                ..
            } => {
                let param_count = parameters.len();
                let variadic = if *is_variadic { ", ..." } else { "" };
                format!("{} parameters{}", param_count, variadic)
            }
            TypeKind::Record {
                members, is_complete, ..
            } => {
                let complete = if *is_complete { "complete" } else { "incomplete" };
                format!("{} members, {}", members.len(), complete)
            }
            TypeKind::Enum {
                enumerators,
                is_complete,
                ..
            } => {
                let complete = if *is_complete { "complete" } else { "incomplete" };
                format!("{} enumerators, {}", enumerators.len(), complete)
            }
            _ => "-".to_string(),
        }
    }

    /// Apply syntax highlighting to source code using the lexer
    fn highlight_source_code(&mut self, text: &str, _span: SourceSpan) -> String {
        // Add the text as a temporary source for tokenization
        let temp_source_id = self.source_manager.add_buffer(text.as_bytes().to_vec(), "<highlight>");

        // Create preprocessor config
        let pp_config = PPConfig {
            max_include_depth: 10, // Small limit for highlighting
            ..Default::default()
        };

        // Preprocess the temporary source
        let mut preprocessor = Preprocessor::new(
            self.source_manager,
            self.diag,
            self.lang_opts.clone(),
            self.target_info.clone(),
            &pp_config,
        );

        let pp_tokens = match preprocessor.process(temp_source_id, &pp_config) {
            Ok(tokens) => tokens,
            Err(_) => return self.escape_html(text), // Fallback to plain text on error
        };

        // Create lexer and tokenize
        let mut lexer = Lexer::new(&pp_tokens);

        let tokens = lexer.tokenize_all();

        // Build highlighted text
        let mut highlighted = String::new();
        let mut last_end = 0;

        for token in tokens {
            if matches!(token.kind, TokenKind::EndOfFile) {
                break;
            }

            // Calculate relative positions in the text
            let token_start = token.location.start.offset() as usize;
            let token_end = token.location.end.offset() as usize;

            // Skip if token is outside the span (though it shouldn't be)
            if token_start < last_end || token_end > text.len() {
                continue;
            }

            // Add unhighlighted text before this token
            if token_start > last_end {
                highlighted.push_str(&self.escape_html(&text[last_end..token_start]));
            }

            // Add highlighted token
            let token_text = &text[token_start..token_end];
            let css_class = self.token_kind_to_css_class(&token.kind);
            highlighted.push_str(&format!(
                "<span class=\"{}\">{}</span>",
                css_class,
                self.escape_html(token_text)
            ));

            last_end = token_end;
        }

        // Add any remaining text
        if last_end < text.len() {
            highlighted.push_str(&self.escape_html(&text[last_end..]));
        }

        highlighted
    }

    /// Map TokenKind to CSS class for highlighting
    fn token_kind_to_css_class(&self, kind: &TokenKind) -> &'static str {
        match kind {
            TokenKind::Auto
            | TokenKind::Break
            | TokenKind::Case
            | TokenKind::Char
            | TokenKind::Const
            | TokenKind::Continue
            | TokenKind::Default
            | TokenKind::Do
            | TokenKind::Double
            | TokenKind::Else
            | TokenKind::Enum
            | TokenKind::Extern
            | TokenKind::Float
            | TokenKind::For
            | TokenKind::Goto
            | TokenKind::If
            | TokenKind::Inline
            | TokenKind::Int
            | TokenKind::Long
            | TokenKind::Register
            | TokenKind::Restrict
            | TokenKind::Return
            | TokenKind::Short
            | TokenKind::Signed
            | TokenKind::Sizeof
            | TokenKind::Static
            | TokenKind::Struct
            | TokenKind::Switch
            | TokenKind::Typedef
            | TokenKind::Union
            | TokenKind::Unsigned
            | TokenKind::Void
            | TokenKind::Volatile
            | TokenKind::While
            | TokenKind::Alignas
            | TokenKind::Alignof
            | TokenKind::Atomic
            | TokenKind::Bool
            | TokenKind::Complex
            | TokenKind::Generic
            | TokenKind::Noreturn
            | TokenKind::Pragma
            | TokenKind::StaticAssert
            | TokenKind::ThreadLocal
            | TokenKind::Attribute => "c-keyword",

            TokenKind::Identifier(_) => "c-identifier",

            TokenKind::IntegerConstant(_) | TokenKind::FloatConstant(_) => "c-number",

            TokenKind::CharacterConstant(_) => "c-literal",

            TokenKind::StringLiteral(_) => "c-string",

            TokenKind::Plus
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::Slash
            | TokenKind::Percent
            | TokenKind::And
            | TokenKind::Or
            | TokenKind::Xor
            | TokenKind::Not
            | TokenKind::Tilde
            | TokenKind::Less
            | TokenKind::Greater
            | TokenKind::LessEqual
            | TokenKind::GreaterEqual
            | TokenKind::Equal
            | TokenKind::NotEqual
            | TokenKind::LeftShift
            | TokenKind::RightShift
            | TokenKind::Assign
            | TokenKind::PlusAssign
            | TokenKind::MinusAssign
            | TokenKind::StarAssign
            | TokenKind::DivAssign
            | TokenKind::ModAssign
            | TokenKind::AndAssign
            | TokenKind::OrAssign
            | TokenKind::XorAssign
            | TokenKind::LeftShiftAssign
            | TokenKind::RightShiftAssign
            | TokenKind::Increment
            | TokenKind::Decrement
            | TokenKind::Arrow
            | TokenKind::Dot
            | TokenKind::Question
            | TokenKind::Colon
            | TokenKind::Comma
            | TokenKind::Semicolon
            | TokenKind::LeftParen
            | TokenKind::RightParen
            | TokenKind::LeftBracket
            | TokenKind::RightBracket
            | TokenKind::LeftBrace
            | TokenKind::RightBrace
            | TokenKind::Ellipsis
            | TokenKind::LogicAnd
            | TokenKind::LogicOr => "c-operator",

            TokenKind::Unknown => "c-unknown",
            TokenKind::EndOfFile => "",
        }
    }

    fn escape_html(&self, text: &str) -> String {
        text.replace("&", "&amp;")
            .replace("<", "&lt;")
            .replace(">", "&gt;")
            .replace("\"", "&quot;")
            .replace("'", "&#x27;")
    }

    fn node_has_children(&self, node: &Node) -> bool {
        match &node.kind {
            NodeKind::TranslationUnit(nodes) => !nodes.is_empty(),
            NodeKind::FunctionDef(_) => true, // Has body
            NodeKind::Declaration(decl) => !decl.init_declarators.is_empty(),
            NodeKind::CompoundStatement(nodes) => !nodes.is_empty(),
            NodeKind::BinaryOp(_, _, _) => true,
            NodeKind::UnaryOp(_, _) => true,
            NodeKind::TernaryOp(_, _, _) => true,
            NodeKind::PostIncrement(_) | NodeKind::PostDecrement(_) => true,
            NodeKind::Assignment(_, _, _) => true,
            NodeKind::FunctionCall(_, args) => !args.is_empty(),
            NodeKind::MemberAccess(_, _, _) => true,
            NodeKind::IndexAccess(_, _) => true,
            NodeKind::Cast(_, _) => true,
            NodeKind::SizeOfExpr(_) => true,
            NodeKind::CompoundLiteral(_, _) => true,
            NodeKind::GenericSelection(_, associations) => !associations.is_empty(),
            NodeKind::VaArg(_, _) => true,
            NodeKind::GnuStatementExpression(_, _) => true,
            NodeKind::If(_) => true,
            NodeKind::While(_) => true,
            NodeKind::DoWhile(_, _) => true,
            NodeKind::For(_) => true,
            NodeKind::Return(Some(_)) => true,
            NodeKind::Goto(_) => false, // No children
            NodeKind::Label(_, _) => true,
            NodeKind::Switch(_, _) => true,
            NodeKind::Case(_, _) => true,
            NodeKind::CaseRange(_, _, _) => true,
            NodeKind::Default(_) => true,
            NodeKind::ExpressionStatement(Some(_)) => true,
            NodeKind::EnumConstant(_, Some(_)) => true,
            NodeKind::StaticAssert(_, _) => true,
            // Semantic nodes - no children
            NodeKind::VarDecl(_) | NodeKind::FunctionDecl(_) | NodeKind::TypedefDecl(_) | NodeKind::RecordDecl(_) => {
                false
            }
            _ => false,
        }
    }
}
