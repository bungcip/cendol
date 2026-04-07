use super::semantic_common::setup_lowering;
use crate::ast::literal::Literal;
use crate::ast::{Ast, NodeKind, NodeRef, StringId};
use crate::semantic::{SymbolTable, TypeRegistry};
use serde::Serialize;

#[derive(Debug, Serialize)]
enum ResolvedAstNode {
    TranslationUnit(Vec<ResolvedAstNode>),
    VarDecl {
        name: StringId,
        ty: String,
        init: Option<Box<ResolvedAstNode>>,
        alignment: Option<u16>,
    },
    RecordDecl {
        name: StringId,
        members: Vec<ResolvedAstNode>,
    },
    FieldDecl {
        name: StringId,
        ty: String,
    },
    EnumDecl {
        name: StringId,
        members: Vec<ResolvedAstNode>,
    },
    EnumMember {
        name: StringId,
        value: i64,
    },
    Function {
        name: StringId,
        body: Box<ResolvedAstNode>,
    },
    FunctionCall {
        callee: Box<ResolvedAstNode>,
        args: Vec<ResolvedAstNode>,
    },
    BinaryOp {
        op: String,
        lhs: Box<ResolvedAstNode>,
        rhs: Box<ResolvedAstNode>,
    },
    CompoundStatement(Vec<ResolvedAstNode>),
    Return(Option<Box<ResolvedAstNode>>),
    LiteralInt(i64),
    Ident(StringId),
    // Fallback for nodes we haven't explicitly mapped yet
    #[serde(untagged)]
    Other(String),
}

fn resolve_node(ast: &Ast, registry: &TypeRegistry, symbol_table: &SymbolTable, node: NodeRef) -> ResolvedAstNode {
    let kind = ast.get_kind(node);

    match kind {
        NodeKind::TranslationUnit(data) => {
            let nodes = data
                .decl_start
                .range(data.decl_len)
                .map(|child| resolve_node(ast, registry, symbol_table, child))
                .collect();
            ResolvedAstNode::TranslationUnit(nodes)
        }
        NodeKind::VarDecl(data) => ResolvedAstNode::VarDecl {
            name: data.name,
            ty: registry.display_qual_type(data.qt),
            init: data
                .init
                .map(|r| Box::new(resolve_node(ast, registry, symbol_table, r))),
            alignment: data.alignment,
        },
        NodeKind::RecordDecl(data) => {
            let members = data
                .member_start
                .range(data.member_len)
                .map(|child| resolve_node(ast, registry, symbol_table, child))
                .collect();
            ResolvedAstNode::RecordDecl {
                name: data.name.unwrap_or_else(|| StringId::new("<anon>")),
                members,
            }
        }
        NodeKind::FieldDecl(data) => ResolvedAstNode::FieldDecl {
            name: data.name.unwrap_or_else(|| StringId::new("<anon>")),
            ty: registry.display_qual_type(data.qt),
        },
        NodeKind::EnumDecl(data) => {
            let members = data
                .member_start
                .range(data.member_len)
                .map(|child| resolve_node(ast, registry, symbol_table, child))
                .collect();
            ResolvedAstNode::EnumDecl {
                name: data.name.unwrap_or_else(|| StringId::new("<anon>")),
                members,
            }
        }
        NodeKind::EnumMember(data) => ResolvedAstNode::EnumMember {
            name: data.name,
            value: data.value,
        },
        NodeKind::Function(data) => {
            let symbol = symbol_table.get_symbol(data.symbol);
            ResolvedAstNode::Function {
                name: symbol.name,
                body: Box::new(resolve_node(ast, registry, symbol_table, data.body)),
            }
        }
        NodeKind::FunctionCall(call) => {
            let args = call
                .arg_start
                .range(call.arg_len)
                .map(|child| resolve_node(ast, registry, symbol_table, child))
                .collect();
            ResolvedAstNode::FunctionCall {
                callee: Box::new(resolve_node(ast, registry, symbol_table, call.callee)),
                args,
            }
        }
        NodeKind::BinaryOp(op, lhs, rhs) => ResolvedAstNode::BinaryOp {
            op: format!("{:?}", op),
            lhs: Box::new(resolve_node(ast, registry, symbol_table, *lhs)),
            rhs: Box::new(resolve_node(ast, registry, symbol_table, *rhs)),
        },
        NodeKind::CompoundStmt(data) => {
            let stmts = data
                .stmt_start
                .range(data.stmt_len)
                .map(|child| resolve_node(ast, registry, symbol_table, child))
                .collect();
            ResolvedAstNode::CompoundStatement(stmts)
        }
        NodeKind::Return(expr) => {
            ResolvedAstNode::Return(expr.map(|r| Box::new(resolve_node(ast, registry, symbol_table, r))))
        }
        NodeKind::Literal(literal) => match literal {
            Literal::Int { val, .. } => ResolvedAstNode::LiteralInt(*val),
            _ => panic!("Not implemented for this literal type"),
        },
        NodeKind::Ident(name, _) => ResolvedAstNode::Ident(*name),
        _ => ResolvedAstNode::Other(format!("{:?}", kind)),
    }
}

#[test]
fn test_const_pointer_init() {
    let (ast, registry, symbol_table) = setup_lowering("const int * const * volatile p;");
    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @r"
    TranslationUnit:
      - VarDecl:
          name: p
          ty: volatile const const int**
          init: ~
          alignment: ~
    ");
}

#[test]
fn test_record_decl_members_populated() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        struct Point {
            int x;
            int y;
        };
    "#,
    );
    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - RecordDecl:
          name: Point
          members:
            - FieldDecl:
                name: x
                ty: int
            - FieldDecl:
                name: y
                ty: int
    ");
}

#[test]
fn test_enum_decl_members_populated() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        enum Color {
            RED,
            GREEN,
            BLUE
        };
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - EnumDecl:
          name: Color
          members:
            - EnumMember:
                name: RED
                value: 0
            - EnumMember:
                name: GREEN
                value: 1
            - EnumMember:
                name: BLUE
                value: 2
    ");
}

#[test]
fn test_struct_member_qualifiers_preserved() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        struct S {
            const int x;
            volatile int *y;
        };
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @r"
    TranslationUnit:
      - RecordDecl:
          name: S
          members:
            - FieldDecl:
                name: x
                ty: const int
            - FieldDecl:
                name: y
                ty: volatile int*
    ");
}

#[test]
fn test_function_call_args_contiguity() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        int add(int a, int b) { return a + b; }
        int main() {
            return add(1 + 2, 3);
        }
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - Function:
          name: add
          body:
            CompoundStatement:
              - Return:
                  BinaryOp:
                    op: Add
                    lhs:
                      Ident: a
                    rhs:
                      Ident: b
      - Function:
          name: main
          body:
            CompoundStatement:
              - Return:
                  FunctionCall:
                    callee:
                      Ident: add
                    args:
                      - BinaryOp:
                          op: Add
                          lhs:
                            LiteralInt: 1
                          rhs:
                            LiteralInt: 2
                      - LiteralInt: 3
    ");
}

#[test]
fn test_alignment_specifier() {
    let (ast, registry, symbol_table) = setup_lowering(
        r#"
        _Alignas(8) int x;
        _Alignas(double) char c;
        _Alignas(16) _Alignas(8) int y;
    "#,
    );

    let root = ast.get_root();
    let resolved = resolve_node(&ast, &registry, &symbol_table, root);
    insta::assert_yaml_snapshot!(resolved, @"
    TranslationUnit:
      - VarDecl:
          name: x
          ty: int
          init: ~
          alignment: 8
      - VarDecl:
          name: c
          ty: char
          init: ~
          alignment: 8
      - VarDecl:
          name: y
          ty: int
          init: ~
          alignment: 16
    ");
}
