use crate::ast::literal::CharPrefix;
use crate::ast::*;
use crate::driver::{CompileConfig, CompilePhase, CompilerDriver};
use crate::lang_options::CStandard;
use crate::parser::statements::parse_compound_statement;
use crate::parser::{BindingPower, Lexer, ParseDiag, Parser, declarations, statements};
use crate::pp::Preprocessor;
use crate::source_manager::FileKind;
use crate::tests::test_utils::setup_sm_and_de;
use serde::Serialize;

/// Resolved AST node kind for testing - replaces NodeRef with actual content
#[derive(Debug, Serialize)]
pub(crate) enum RNodeKind {
    LiteralInt(i64),
    LiteralFloat(f64),
    LiteralString(String),
    LiteralChar(u64, CharPrefix),
    LiteralNullptr,
    LiteralTrue,
    LiteralFalse,
    Ident(String),
    UnaryOp(UnaryOp, Box<RNodeKind>),
    BinaryOp(BinaryOp, Box<RNodeKind>, Box<RNodeKind>),
    TernaryOp(Box<RNodeKind>, Box<RNodeKind>, Box<RNodeKind>),
    PostIncrement(Box<RNodeKind>),
    PostDecrement(Box<RNodeKind>),
    Assignment(BinaryOp, Box<RNodeKind>, Box<RNodeKind>),
    FunctionCall(Box<RNodeKind>, Vec<RNodeKind>),
    MemberAccess(Box<RNodeKind>, String, bool),
    IndexAccess(Box<RNodeKind>, Box<RNodeKind>),
    Cast(String, Box<RNodeKind>), // Simplified: just type name
    SizeOfExpr(Box<RNodeKind>),
    SizeOfType(String),  // Simplified: just type name
    AlignOfType(String), // Simplified: just type name
    AlignOfExpr(Box<RNodeKind>),
    Declaration {
        specifiers: Vec<String>,
        init_declarators: Vec<RInitDeclarator>,
    }, // Simplified declaration
    EnumConstant(String, Option<Box<RNodeKind>>),
    InitializerList(Vec<RNodeKind>),             // For initializer lists like {1, 2, 3}
    ExpressionStatement(Option<Box<RNodeKind>>), // Expression statement
    CompoundStatement(Vec<RNodeKind>),           // Compound statement { ... }
    GnuStatementExpression(Box<RNodeKind>, Box<RNodeKind>), // GNU statement expression ({ ... })
    GenericSelection(Box<RNodeKind>, Vec<RGenericAssociation>), // _Generic selection
    Label(String, Box<RNodeKind>),               // Label statement (label: statement)
    Goto(String),                                // Goto statement
    Return(Option<Box<RNodeKind>>),              // Return statement
    Break,                                       // Break statement
    Continue,                                    // Continue statement
    Switch(Box<RNodeKind>, Box<RNodeKind>),
    Case(Box<RNodeKind>, Box<RNodeKind>),                       // Case statement
    CaseRange(Box<RNodeKind>, Box<RNodeKind>, Box<RNodeKind>),  // GNU Case range statement
    Default(Box<RNodeKind>),                                    // Default statement
    If(Box<RNodeKind>, Box<RNodeKind>, Option<Box<RNodeKind>>), // If statement
    While(Box<RNodeKind>, Box<RNodeKind>),                      // While statement
    DoWhile(Box<RNodeKind>, Box<RNodeKind>),                    // Do-while statement
    For(
        Option<Box<RNodeKind>>,
        Option<Box<RNodeKind>>,
        Option<Box<RNodeKind>>,
        Box<RNodeKind>,
    ), // For statement
    StaticAssert(Box<RNodeKind>, Option<String>),
    CompoundLiteral(String, Box<RNodeKind>),
    FunctionDef {
        specifiers: Vec<String>,
        declarator: Box<RInitDeclarator>,
        body: Box<RNodeKind>,
    },
    TranslationUnit(Vec<RNodeKind>),
    Empty, // Empty statement
    // Add more as needed for tests
    PragmaPackStmt(String),
}

/// Simplified resolved generic association for testing
#[derive(Debug, Serialize)]
pub(crate) struct RGenericAssociation {
    type_name: Option<String>, // None for 'default:'
    result_expr: RNodeKind,
}

/// Simplified resolved init declarator for testing
#[derive(Debug, Serialize)]
pub(crate) struct RInitDeclarator {
    name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    initializer: Option<RNodeKind>,
}

fn resolve_specs(ast: &PAst, specifiers: &[DeclSpec]) -> Vec<String> {
    specifiers
        .iter()
        .map(|s| match s {
            DeclSpec::TypeSpec(ts) => match ts {
                TypeSpec::Void => "void".to_string(),
                TypeSpec::Bool => "_Bool".to_string(),
                TypeSpec::Char => "char".to_string(),
                TypeSpec::Short => "short".to_string(),
                TypeSpec::Int => "int".to_string(),
                TypeSpec::Long => "long".to_string(),
                TypeSpec::Float => "float".to_string(),
                TypeSpec::Double => "double".to_string(),
                TypeSpec::Signed => "signed".to_string(),
                TypeSpec::Unsigned => "unsigned".to_string(),
                TypeSpec::Complex => "_Complex".to_string(),
                TypeSpec::TypedefName(name) => format!("TypedefName({:?})", name.to_string()),
                TypeSpec::Enum(tag, enumerators, underlying_type) => {
                    let tag_str = tag.map(|t| t.to_string()).unwrap_or_else(|| "".to_string());
                    let mut s = format!("enum {}", tag_str);
                    if let Some(ut) = underlying_type {
                        s.push_str(" : ");
                        s.push_str(&extract_type_kind(ast, ut));
                    }
                    if let Some(enums) = enumerators {
                        let enum_parts: Vec<String> = enums
                            .iter()
                            .map(|&node| match &ast.get_node(node).kind {
                                PNodeKind::EnumConstant(name, Some(value_expr)) => {
                                    let value = resolve_node(ast, *value_expr);
                                    match value {
                                        RNodeKind::LiteralInt(val) => format!("{} = {}", name, val),
                                        _ => format!("{} = <expr>", name),
                                    }
                                }
                                PNodeKind::EnumConstant(name, None) => name.to_string(),
                                _ => "<invalid>".to_string(),
                            })
                            .collect();
                        s.push_str(&format!(" {{ {} }}", enum_parts.join(", ")));
                    }
                    s
                }
                TypeSpec::Record(is_union, tag, def, _) => {
                    let record_kind = if *is_union { "union" } else { "struct" };
                    let has_body = def.is_some();

                    let mut s = record_kind.to_string();
                    if let Some(tag) = tag {
                        s.push(' ');
                        s.push_str(tag.as_str());
                    }
                    if has_body {
                        s.push_str(" { ... }");
                    }
                    s
                }
                _ => format!("{:?}", ts),
            },
            DeclSpec::StorageClass(sc) => format!("{:?}", sc),
            DeclSpec::ThreadLocal => "ThreadLocal".to_string(),
            DeclSpec::TypeQualifier(tq) => format!("TypeQualifier({:?})", tq),
            DeclSpec::FunctionSpec(fs) => format!("{:?}", fs),
            DeclSpec::AlignmentSpec(aspec, _) => format!("{:?}", aspec),
            DeclSpec::Attribute => "__attribute__".to_string(),
            DeclSpec::AttributePacked => "packed".to_string(),
            DeclSpec::AttributeCleanup(_) => "cleanup(...)".to_string(),
            DeclSpec::AttributeTransparentUnion => "transparent_union".to_string(),
            DeclSpec::AttributeVisibility(vis) => format!("visibility({:?})", vis),
            DeclSpec::AttributeAlias(lit) => {
                let (value, _) = lit.get_val();
                format!("alias(\"{}\")", String::from_utf8_lossy(&value))
            }
            DeclSpec::AttributeAsm(lit) => {
                let (value, _) = lit.get_val();
                format!("asm(\"{}\")", String::from_utf8_lossy(&value))
            }
            DeclSpec::AttributeMode(mode) => {
                format!("mode({})", mode.as_str())
            }
        })
        .collect()
}

/// Resolve a ParsedNodeRef to a ResolvedNodeKind by recursively following references
pub(crate) fn resolve_node(ast: &PAst, node: PNodeRef) -> RNodeKind {
    let node = ast.get_node(node);
    match &node.kind {
        PNodeKind::Literal(lit) => match lit.get_val() {
            LitVal::Int { value, .. } => RNodeKind::LiteralInt(value),
            lit @ LitVal::Float { .. } => RNodeKind::LiteralFloat(lit.as_f64()),
            LitVal::String { value, .. } => RNodeKind::LiteralString(String::from_utf8_lossy(&value).to_string()),
            LitVal::Char(c, prefix) => RNodeKind::LiteralChar(c as u64, prefix),
            LitVal::Nullptr => RNodeKind::LiteralNullptr,
            LitVal::True => RNodeKind::LiteralTrue,
            LitVal::False => RNodeKind::LiteralFalse,
        },
        PNodeKind::Ident(symbol) => RNodeKind::Ident(symbol.to_string()),
        PNodeKind::UnaryOp(op, operand) => RNodeKind::UnaryOp(*op, Box::new(resolve_node(ast, *operand))),
        PNodeKind::BinaryOp(op, left, right) => RNodeKind::BinaryOp(
            *op,
            Box::new(resolve_node(ast, *left)),
            Box::new(resolve_node(ast, *right)),
        ),
        PNodeKind::TernaryOp(cond, then_expr, else_expr) => RNodeKind::TernaryOp(
            Box::new(resolve_node(ast, *cond)),
            Box::new(resolve_node(ast, *then_expr)),
            Box::new(resolve_node(ast, *else_expr)),
        ),
        PNodeKind::PostIncrement(operand) => RNodeKind::PostIncrement(Box::new(resolve_node(ast, *operand))),
        PNodeKind::PostDecrement(operand) => RNodeKind::PostDecrement(Box::new(resolve_node(ast, *operand))),
        PNodeKind::Assignment(op, lhs, rhs) => RNodeKind::Assignment(
            *op,
            Box::new(resolve_node(ast, *lhs)),
            Box::new(resolve_node(ast, *rhs)),
        ),
        PNodeKind::FunctionCall(func, args) => RNodeKind::FunctionCall(
            Box::new(resolve_node(ast, *func)),
            args.iter().map(|&arg| resolve_node(ast, arg)).collect(),
        ),
        PNodeKind::BuiltinChooseExpr(c, t, f) => RNodeKind::FunctionCall(
            Box::new(RNodeKind::Ident("__builtin_choose_expr".to_string())),
            vec![resolve_node(ast, *c), resolve_node(ast, *t), resolve_node(ast, *f)],
        ),
        PNodeKind::BuiltinComplex(r, i) => RNodeKind::FunctionCall(
            Box::new(RNodeKind::Ident("__builtin_complex".to_string())),
            vec![resolve_node(ast, *r), resolve_node(ast, *i)],
        ),
        PNodeKind::BuiltinBitCast(ty, expr) => RNodeKind::FunctionCall(
            Box::new(RNodeKind::Ident("__builtin_bit_cast".to_string())),
            vec![
                RNodeKind::Ident(format!("ptype_{}", ty.base.get())),
                resolve_node(ast, *expr),
            ],
        ),
        PNodeKind::BuiltinTypesCompatibleP(boxed) => {
            let (t1, t2) = &**boxed;
            RNodeKind::FunctionCall(
                Box::new(RNodeKind::Ident("__builtin_types_compatible_p".to_string())),
                vec![
                    RNodeKind::Ident(format!("type_{}", t1.base.get())),
                    RNodeKind::Ident(format!("type_{}", t2.base.get())),
                ],
            )
        }
        PNodeKind::BuiltinConvertVector(expr, ty) => RNodeKind::FunctionCall(
            Box::new(RNodeKind::Ident("__builtin_convertvector".to_string())),
            vec![
                resolve_node(ast, *expr),
                RNodeKind::Ident(format!("type_{}", ty.base.get())),
            ],
        ),
        PNodeKind::BuiltinVaArg(ty, expr) => RNodeKind::FunctionCall(
            Box::new(RNodeKind::Ident("__builtin_va_arg".to_string())),
            vec![
                RNodeKind::Ident(format!("type_{}", ty.base.get())),
                resolve_node(ast, *expr),
            ],
        ),
        PNodeKind::MemberAccess(object, field, is_arrow) => {
            RNodeKind::MemberAccess(Box::new(resolve_node(ast, *object)), field.to_string(), *is_arrow)
        }
        PNodeKind::IndexAccess(array, index) => {
            RNodeKind::IndexAccess(Box::new(resolve_node(ast, *array)), Box::new(resolve_node(ast, *index)))
        }
        PNodeKind::Cast(ty, expr) => {
            // For simplicity, just show a placeholder type name
            RNodeKind::Cast(
                format!("parsed_type_{}_{}", ty.base.get(), ty.declarator.get()),
                Box::new(resolve_node(ast, *expr)),
            )
        }
        PNodeKind::SizeOfExpr(expr) => RNodeKind::SizeOfExpr(Box::new(resolve_node(ast, *expr))),
        PNodeKind::SizeOfType(ty) => RNodeKind::SizeOfType(format!("type_{}", ty.base.get())),
        PNodeKind::AlignOfType(ty) => RNodeKind::AlignOfType(format!("type_{}", ty.base.get())),
        PNodeKind::AlignOfExpr(expr) => RNodeKind::AlignOfExpr(Box::new(resolve_node(ast, *expr))),
        PNodeKind::Declaration(decl) => {
            let specifiers = resolve_specs(ast, &decl.specifiers);
            let init_declarators = decl
                .init_declarators
                .iter()
                .map(|init_decl| {
                    let name = extract_declarator_name(ast, init_decl.declarator);
                    let kind_str = extract_declarator_kind(ast, init_decl.declarator);
                    let kind = if kind_str == "identifier" { None } else { Some(kind_str) };
                    let initializer = init_decl
                        .initializer
                        .as_ref()
                        .map(|init| resolve_initializer(ast, *init));
                    RInitDeclarator {
                        name,
                        kind,
                        initializer,
                    }
                })
                .collect();
            RNodeKind::Declaration {
                specifiers,
                init_declarators,
            }
        }
        PNodeKind::EnumConstant(name, value_expr) => RNodeKind::EnumConstant(
            name.to_string(),
            value_expr.map(|expr| Box::new(resolve_node(ast, expr))),
        ),
        PNodeKind::ExpressionStmt(expr) => RNodeKind::ExpressionStatement(expr.map(|e| Box::new(resolve_node(ast, e)))),
        PNodeKind::CompoundStmt(statements, _) => {
            RNodeKind::CompoundStatement(statements.iter().map(|&stmt| resolve_node(ast, stmt)).collect())
        }
        PNodeKind::GnuStatementExpr(compound_stmt, result_expr) => RNodeKind::GnuStatementExpression(
            Box::new(resolve_node(ast, *compound_stmt)),
            Box::new(resolve_node(ast, *result_expr)),
        ),
        PNodeKind::GenericSelection(controlling_expr, associations) => {
            let resolved_controlling = Box::new(resolve_node(ast, *controlling_expr));
            let resolved_associations = associations
                .iter()
                .map(|assoc| {
                    let type_name = assoc.type_name.map(|ty| {
                        // For simplicity, just show a placeholder type name
                        // In a full implementation, we'd resolve the actual type
                        format!("type_{}", ty.base.get())
                    });
                    let result_expr = resolve_node(ast, assoc.result_expr);
                    RGenericAssociation { type_name, result_expr }
                })
                .collect();
            RNodeKind::GenericSelection(resolved_controlling, resolved_associations)
        }
        PNodeKind::Label(label, statement) => {
            RNodeKind::Label(label.to_string(), Box::new(resolve_node(ast, *statement)))
        }
        PNodeKind::Goto(label) => RNodeKind::Goto(label.to_string()),
        PNodeKind::Return(expr) => RNodeKind::Return(expr.map(|e| Box::new(resolve_node(ast, e)))),
        PNodeKind::Break => RNodeKind::Break,
        PNodeKind::Continue => RNodeKind::Continue,
        PNodeKind::Switch(condition, body) => RNodeKind::Switch(
            Box::new(resolve_node(ast, *condition)),
            Box::new(resolve_node(ast, *body)),
        ),
        PNodeKind::Case(expr, statement) => RNodeKind::Case(
            Box::new(resolve_node(ast, *expr)),
            Box::new(resolve_node(ast, *statement)),
        ),
        PNodeKind::CaseRange(start, end, statement) => RNodeKind::CaseRange(
            Box::new(resolve_node(ast, *start)),
            Box::new(resolve_node(ast, *end)),
            Box::new(resolve_node(ast, *statement)),
        ),
        PNodeKind::Default(statement) => RNodeKind::Default(Box::new(resolve_node(ast, *statement))),
        PNodeKind::If(if_stmt) => RNodeKind::If(
            Box::new(resolve_node(ast, if_stmt.condition)),
            Box::new(resolve_node(ast, if_stmt.then_branch)),
            if_stmt.else_branch.map(|br| Box::new(resolve_node(ast, br))),
        ),
        PNodeKind::While(while_stmt) => RNodeKind::While(
            Box::new(resolve_node(ast, while_stmt.condition)),
            Box::new(resolve_node(ast, while_stmt.body)),
        ),
        PNodeKind::DoWhile(body, condition) => RNodeKind::DoWhile(
            Box::new(resolve_node(ast, *body)),
            Box::new(resolve_node(ast, *condition)),
        ),
        PNodeKind::For(for_stmt) => RNodeKind::For(
            for_stmt.init.map(|i| Box::new(resolve_node(ast, i))),
            for_stmt.condition.map(|c| Box::new(resolve_node(ast, c))),
            for_stmt.increment.map(|inc| Box::new(resolve_node(ast, inc))),
            Box::new(resolve_node(ast, for_stmt.body)),
        ),
        PNodeKind::StaticAssert(expr, msg) => {
            let message = msg.map(|m| {
                if let PNodeKind::Literal(lit) = &ast.get_node(m).kind {
                    if let LitVal::String { value, .. } = lit.get_val() {
                        String::from_utf8_lossy(&value).to_string()
                    } else {
                        "<invalid>".to_string()
                    }
                } else {
                    "<invalid>".to_string()
                }
            });
            RNodeKind::StaticAssert(Box::new(resolve_node(ast, *expr)), message)
        }
        PNodeKind::CompoundLiteral(ty, init) => {
            // Check if init is an InitializerList, if so use resolve_initializer, otherwise resolve_node
            let init_node = ast.get_node(*init);
            let resolved_init = match init_node.kind {
                PNodeKind::InitializerList(_) => resolve_initializer(ast, *init),
                _ => resolve_node(ast, *init),
            };
            RNodeKind::CompoundLiteral(
                format!("parsed_type_{}", ty.base.get()), // Simplified type
                Box::new(resolved_init),
            )
        }
        PNodeKind::TranslationUnit(nodes) => {
            RNodeKind::TranslationUnit(nodes.iter().map(|&n| resolve_node(ast, n)).collect())
        }
        PNodeKind::FunctionDef(def) => {
            let specifiers = resolve_specs(ast, &def.specifiers);
            let name = extract_declarator_name(ast, def.declarator);
            let kind_str = extract_declarator_kind(ast, def.declarator);
            let kind = if kind_str == "identifier" { None } else { Some(kind_str) };

            let resolved_declarator = RInitDeclarator {
                name,
                kind,
                initializer: None,
            };

            RNodeKind::FunctionDef {
                specifiers,
                declarator: Box::new(resolved_declarator),
                body: Box::new(resolve_node(ast, def.body)),
            }
        }
        PNodeKind::EmptyStmt | PNodeKind::Dummy => RNodeKind::Empty,
        PNodeKind::PragmaPack(kind) => RNodeKind::PragmaPackStmt(format!("{:?}", kind)),
        // Add more cases as needed for other ParsedNodeKind variants used in tests
        _ => panic!("Unsupported ParsedNodeKind for resolution: {:?}", node.kind),
    }
}

fn extract_declarator_name(ast: &PAst, declarator: DeclaratorRef) -> String {
    let declarator = ast.arena.get_decl(declarator);
    match declarator {
        PDeclarator::Identifier(name) => name.map(|n| n.to_string()).unwrap_or_else(|| "<unnamed>".to_string()),
        PDeclarator::Pointer { inner, .. }
        | PDeclarator::Array { inner, .. }
        | PDeclarator::Function { inner, .. }
        | PDeclarator::BitField { inner, .. }
        | PDeclarator::Attribute { inner, .. } => extract_declarator_name(ast, *inner),
    }
}

fn extract_declarator_kind(ast: &PAst, declarator: DeclaratorRef) -> String {
    let declarator = ast.arena.get_decl(declarator);
    match declarator {
        PDeclarator::Identifier(name) => {
            if name.is_some() {
                "identifier".to_string()
            } else {
                "abstract".to_string()
            }
        }
        PDeclarator::Pointer { inner, .. } => {
            let inner_kind = extract_declarator_kind(ast, *inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "pointer".to_string()
            } else {
                format!("pointer to {}", inner_kind)
            }
        }
        PDeclarator::Array { inner, .. } => {
            let inner_kind = extract_declarator_kind(ast, *inner);
            if inner_kind == "identifier" || inner_kind == "abstract" {
                "array".to_string()
            } else {
                format!("array of {}", inner_kind)
            }
        }
        PDeclarator::Function {
            inner, params, flags, ..
        } => {
            let return_type = extract_declarator_kind(ast, *inner);
            let mut param_str = if params.len == 0 {
                "void".to_string()
            } else {
                ast.arena
                    .get_params(*params)
                    .iter()
                    .map(|param| extract_type_kind(ast, &param.ty))
                    .collect::<Vec<_>>()
                    .join(", ")
            };

            if flags.contains(crate::ast::FunctionFlags::IS_VARIADIC) {
                if params.len == 0 {
                    param_str = "...".to_string();
                } else {
                    param_str.push_str(", ...");
                }
            }

            let return_type_str = if return_type == "abstract" || return_type == "identifier" {
                "int".to_string()
            } else {
                return_type
            };
            format!("function({}) -> {}", param_str, return_type_str)
        }
        PDeclarator::BitField { inner, .. } => {
            let inner_kind = extract_declarator_kind(ast, *inner);
            format!("bitfield {}", inner_kind)
        }
        PDeclarator::Attribute { inner, .. } => extract_declarator_kind(ast, *inner),
    }
}

fn extract_base_kind(ast: &PAst, base: TypeSpecRef) -> String {
    let base = ast.arena.get_type_spec(base);
    match base {
        TypeSpec::Record(is_union, tag, _, _) => {
            let kind = if *is_union { "union" } else { "struct" };
            if let Some(tag) = tag {
                format!("{} {}", kind, tag)
            } else {
                "struct { ... }".to_string()
            }
        }
        TypeSpec::Enum(tag, _, underlying_type) => {
            let mut s = if let Some(tag) = tag {
                format!("enum {}", tag)
            } else {
                "enum { ... }".to_string()
            };
            if let Some(ut) = underlying_type {
                s.push_str(" : ");
                s.push_str(&extract_type_kind(ast, ut));
            }
            s
        }
        TypeSpec::TypedefName(name) => name.to_string(),
        TypeSpec::Typeof(..) => "typeof(...)".to_string(),
        TypeSpec::TypeofExpr(..) => "typeof(...)".to_string(),
        TypeSpec::TypeofUnqual(..) => "typeof_unqual(...)".to_string(),
        TypeSpec::TypeofUnqualExpr(..) => "typeof_unqual(...)".to_string(),
        spec => {
            let s = format!("{:?}", spec);
            let mut result = String::new();
            for (i, c) in s.chars().enumerate() {
                if i > 0 && c.is_uppercase() {
                    result.push(' ');
                }
                result.push(c.to_ascii_lowercase());
            }
            result
        }
    }
}

fn extract_type_kind(ast: &PAst, ty: &crate::ast::PType) -> String {
    let base_kind = extract_base_kind(ast, ty.base);
    let decl_kind = extract_declarator_kind(ast, ty.declarator);

    if decl_kind == "identifier" || decl_kind == "abstract" {
        base_kind
    } else if decl_kind == "pointer" {
        format!("{} pointer", base_kind)
    } else if decl_kind == "array" {
        format!("{} array", base_kind)
    } else if decl_kind.starts_with("function") {
        format!("{} {}", base_kind, decl_kind)
    } else {
        // Fallback for complex combinations like "pointer to array"
        format!("{} to {}", decl_kind, base_kind)
    }
}

fn resolve_initializer(ast: &PAst, initializer: PNodeRef) -> RNodeKind {
    let node = ast.get_node(initializer);
    match &node.kind {
        PNodeKind::InitializerList(designated_inits) => {
            let mut elements = Vec::new();
            for designated in designated_inits {
                // For now, ignore designations and just collect the initializer values
                // In a full implementation, we'd handle [index] and .field designators
                elements.push(resolve_initializer(ast, designated.initializer));
            }
            RNodeKind::InitializerList(elements)
        }
        _ => resolve_node(ast, initializer),
    }
}

pub(crate) fn setup_source<F, T>(source: &str, parse_fn: F) -> (PAst, T)
where
    F: FnOnce(&mut Parser<'_, '_, '_>) -> T,
{
    let config = CompileConfig::from_virtual_file(source.to_string(), CompilePhase::Parse);
    let (mut sm, mut de) = setup_sm_and_de();
    let source_id = sm.add_buffer(source.as_bytes().to_vec(), "test.c", None, FileKind::Real);

    let mut preprocessor = Preprocessor::new(&mut sm, &mut de, &config.preprocessor);
    preprocessor.start_processing(source_id);
    let mut lexer = Lexer::new(&mut preprocessor, config.lang_options.c_standard);

    let mut symbol_table = crate::semantic::SymbolTable::new();
    let (ast, result) = {
        let mut parser = Parser::new(&mut lexer, &mut symbol_table, &config.lang_options);
        let res = parse_fn(&mut parser);
        (parser.take_ast(), res)
    };

    assert!(
        de.diagnostics.is_empty(),
        "Expected no diagnostics, but found: {:?}",
        de.diagnostics
    );
    (ast, result)
}

pub(crate) fn setup_expr(source: &str) -> RNodeKind {
    let (ast, expr_result) = setup_source(source, |parser| parser.parse_expression(BindingPower::MIN));

    let node = expr_result.unwrap();
    resolve_node(&ast, node)
}

pub(crate) fn setup_declaration(source: &str) -> RNodeKind {
    setup_declaration_with_std(source, CStandard::C11)
}

pub(crate) fn setup_declaration_with_std(source: &str, std: CStandard) -> RNodeKind {
    match setup_translation_unit_with_std(source, std) {
        RNodeKind::TranslationUnit(nodes) => nodes
            .into_iter()
            .find(|n| !matches!(n, RNodeKind::Empty))
            .expect("No declaration found in translation unit"),
        _ => panic!("Expected translation unit"),
    }
}

pub(crate) fn setup_declaration_with_errors(source: &str) -> ParseDiag {
    setup_source(source, |p| declarations::parse_decl(p, false))
        .1
        .unwrap_err()
}

pub(crate) fn setup_statement(source: &str) -> RNodeKind {
    let (ast, stmt_result) = setup_source(source, statements::parse_statement);
    resolve_node(&ast, stmt_result.expect("Expected statement"))
}

/// Setup a compound statement, useful for testing multi-statement blocks
pub(crate) fn setup_compound(source: &str) -> RNodeKind {
    let source = format!("{{ {} }}", source);
    let (ast, stmt_result) = setup_source(&source, parse_compound_statement);
    resolve_node(&ast, stmt_result.expect("Expected multi statement block").0)
}

pub(crate) fn setup_translation_unit(source: &str) -> RNodeKind {
    setup_translation_unit_with_std(source, CStandard::C11)
}

pub(crate) fn setup_translation_unit_with_std(source: &str, std: CStandard) -> RNodeKind {
    let phase = CompilePhase::Parse;
    let mut config = CompileConfig::from_virtual_file(source.to_string(), phase);
    config.lang_options.c_standard = std;
    let mut driver = CompilerDriver::from_config(config);
    let out = driver.run_pipeline(phase).expect("Pipeline failed");
    let first = out.units.values().next().unwrap();
    let ast = first.parsed_ast.clone().unwrap();
    let root = ast.get_root();
    resolve_node(&ast, root)
}
