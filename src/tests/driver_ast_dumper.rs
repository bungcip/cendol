#![cfg(test)]
use crate::ast::dumper::AstDumper;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

fn get_artifact(source: &str, phase: CompilePhase) -> crate::driver::artifact::CompileArtifact {
    let (driver, result) = test_utils::run_pipeline(source, phase);
    let out = result.unwrap_or_else(|e| panic!("Pipeline failed: {}\nDiagnostics: {:?}", e, driver.get_diagnostics()));
    out.units.into_iter().next().unwrap().1
}

fn dump_parsed_ast(source: &str) -> String {
    let artifact = get_artifact(source, CompilePhase::Parse);
    AstDumper::dump_parsed_ast(artifact.parsed_ast.as_ref().unwrap()).to_string()
}

fn dump_parser_ast(source: &str) -> String {
    let artifact = get_artifact(source, CompilePhase::SemanticLowering);
    AstDumper::dump_ast(artifact.ast.as_ref().unwrap(), artifact.symbol_table.as_ref()).to_string()
}

fn dump_type_registry(source: &str) -> String {
    let artifact = get_artifact(source, CompilePhase::SemanticLowering);
    AstDumper::dump_type_registry(artifact.ast.as_ref().unwrap(), artifact.type_registry.as_ref().unwrap()).to_string()
}

#[test]
fn test_dump_parsed_ast_simple() {
    let output = dump_parsed_ast("int main() { return 0; }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[6])
    5: LiteralInt(0, None, base=8)
    6: Return(5)
    ");
}

#[test]
fn test_dump_parsed_ast_with_variables() {
    let output = dump_parsed_ast("int x = 42; int y = x + 5;");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199123918852) }] })
    3: LiteralInt(42, None, base=10)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(7), span: SourceSpan(2199174250512) }] })
    5: Ident(x)
    6: LiteralInt(5, None, base=10)
    7: BinaryOp(Add, 5, 6)
    "
    );
}

#[test]
fn test_dump_parsed_ast_with_structs() {
    let output = dump_parsed_ast("struct Point { int x; int y; } p = {1, 2};");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("Point"), Some(ParsedRecordDef { tag: Some("Point"), members: Some([3, 4]), is_union: false })))], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(7), span: SourceSpan(2199191027743) }] })
    3: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: None, span: SourceSpan(2199040032787) }] })
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: None, span: SourceSpan(2199040032794) }] })
    5: LiteralInt(1, None, base=10)
    6: LiteralInt(2, None, base=10)
    7: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 5 }, ParsedDesignatedInitializer { designation: [], initializer: 6 }])
    "#
    );
}

#[test]
fn test_dump_parsed_ast_with_enums() {
    let output = dump_parsed_ast("enum Color { RED, GREEN = 2, BLUE } c = RED;");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Enum(Some("Color"), Some([3, 5, 6])))], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(7), span: SourceSpan(2199140696100) }] })
    3: EnumConstant(RED, auto)
    4: LiteralInt(2, None, base=10)
    5: EnumConstant(GREEN, 4)
    6: EnumConstant(BLUE, auto)
    7: Ident(RED)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_strings() {
    let output = dump_parsed_ast("char* msg = \"Hello, world!\";");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(3), span: SourceSpan(2199409131524) }] })
    3: LiteralString(""Hello, world!"")
    "#);
}

#[test]
fn test_dump_parsed_ast_with_floats() {
    let output = dump_parsed_ast("float pi = 3.14159; double e = 2.71828;");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Float)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199224582150) }] })
    3: LiteralFloat(3.14159, None)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Double)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(5), span: SourceSpan(2199207804955) }] })
    5: LiteralFloat(2.71828, None)
    ");
}

#[test]
fn test_dump_parsed_ast_with_chars() {
    let output = dump_parsed_ast("char c = 'a'; signed char sc = 'b'; unsigned char uc = 'c';");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4, 6])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199140696069) }] })
    3: LiteralChar('a')
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Signed), TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(5), span: SourceSpan(2199157473306) }] })
    5: LiteralChar('b')
    6: Declaration(ParsedDecl { specifiers: [TypeSpec(Unsigned), TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(7), span: SourceSpan(2199157473330) }] })
    7: LiteralChar('c')
    ");
}

#[test]
fn test_dump_parsed_ast_with_pointers() {
    let output = dump_parsed_ast("int x = 10; int* ptr = &x; int** ptr_ptr = &ptr;");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4, 7])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199123918852) }] })
    3: LiteralInt(10, None, base=10)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(6), span: SourceSpan(2199191027727) }] })
    5: Ident(x)
    6: UnaryOp(AddrOf, 5)
    7: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 6, initializer: Some(9), span: SourceSpan(2199308468254) }] })
    8: Ident(ptr)
    9: UnaryOp(AddrOf, 8)
    ");
}

#[test]
fn test_dump_parsed_ast_with_arrays() {
    let output = dump_parsed_ast("int arr[5] = {1, 2, 3, 4, 5}; int* ptr_arr[3];");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 10])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(9), span: SourceSpan(2199425908740) }] })
    3: LiteralInt(5, None, base=10)
    4: LiteralInt(1, None, base=10)
    5: LiteralInt(2, None, base=10)
    6: LiteralInt(3, None, base=10)
    7: LiteralInt(4, None, base=10)
    8: LiteralInt(5, None, base=10)
    9: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 4 }, ParsedDesignatedInitializer { designation: [], initializer: 5 }, ParsedDesignatedInitializer { designation: [], initializer: 6 }, ParsedDesignatedInitializer { designation: [], initializer: 7 }, ParsedDesignatedInitializer { designation: [], initializer: 8 }])
    10: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: None, span: SourceSpan(2199224582177) }] })
    11: LiteralInt(3, None, base=10)
    ");
}

#[test]
fn test_dump_parsed_ast_with_loops() {
    let output = dump_parsed_ast(
        "int main() { int i = 0; while (i < 10) { i++; } for (int j = 0; j < 5; j++) { printf(\"%d\", j); } do { i--; } while (i > 0); return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[5, 14, 15, 36, 38])
    5: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: Some(6), span: SourceSpan(2199107141649) }] })
    6: LiteralInt(0, None, base=8)
    7: Ident(i)
    8: LiteralInt(10, None, base=10)
    9: BinaryOp(Less, 7, 8)
    10: CompoundStmt(stmts=[11])
    11: ExpressionStmt(13)
    12: Ident(i)
    13: PostIncrement(12)
    14: While(ParsedWhileStmt { condition: 9, body: 10 })
    15: For(ParsedForStmt { init: Some(16), condition: Some(20), increment: Some(22), body: 23 })
    16: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 6, initializer: Some(17), span: SourceSpan(2199107141689) }] })
    17: LiteralInt(0, None, base=8)
    18: Ident(j)
    19: LiteralInt(5, None, base=10)
    20: BinaryOp(Less, 18, 19)
    21: Ident(j)
    22: PostIncrement(21)
    23: CompoundStmt(stmts=[24])
    24: ExpressionStmt(28)
    25: Ident(printf)
    26: LiteralString(""%d"")
    27: Ident(j)
    28: FunctionCall(callee=25, args=[26, 27])
    29: CompoundStmt(stmts=[30])
    30: ExpressionStmt(32)
    31: Ident(i)
    32: PostDecrement(31)
    33: Ident(i)
    34: LiteralInt(0, None, base=8)
    35: BinaryOp(Greater, 33, 34)
    36: DoWhile(body=29, cond=35)
    37: LiteralInt(0, None, base=8)
    38: Return(37)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_conditional() {
    let output = dump_parsed_ast(
        "int main() { int x = 10; if (x > 5) { printf(\"x is greater than 5\"); } else if (x < 5) { printf(\"x is less than 5\"); } else { printf(\"x is 5\"); } return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[5, 29, 31])
    5: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: Some(6), span: SourceSpan(2199123918865) }] })
    6: LiteralInt(10, None, base=10)
    7: Ident(x)
    8: LiteralInt(5, None, base=10)
    9: BinaryOp(Greater, 7, 8)
    10: CompoundStmt(stmts=[11])
    11: ExpressionStmt(14)
    12: Ident(printf)
    13: LiteralString(""x is greater than 5"")
    14: FunctionCall(callee=12, args=[13])
    15: Ident(x)
    16: LiteralInt(5, None, base=10)
    17: BinaryOp(Less, 15, 16)
    18: CompoundStmt(stmts=[19])
    19: ExpressionStmt(22)
    20: Ident(printf)
    21: LiteralString(""x is less than 5"")
    22: FunctionCall(callee=20, args=[21])
    23: CompoundStmt(stmts=[24])
    24: ExpressionStmt(27)
    25: Ident(printf)
    26: LiteralString(""x is 5"")
    27: FunctionCall(callee=25, args=[26])
    28: If(ParsedIfStmt { condition: 17, then_branch: 18, else_branch: Some(23) })
    29: If(ParsedIfStmt { condition: 9, then_branch: 10, else_branch: Some(28) })
    30: LiteralInt(0, None, base=8)
    31: Return(30)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_switch() {
    let output = dump_parsed_ast(
        "int main() { int x = 2; switch (x) { case 1: printf(\"1\"); break; case 2: printf(\"2\"); break; default: printf(\"default\"); } return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[5, 28, 30])
    5: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: Some(6), span: SourceSpan(2199107141649) }] })
    6: LiteralInt(2, None, base=10)
    7: Ident(x)
    8: CompoundStmt(stmts=[14, 15, 21, 22, 27])
    9: LiteralInt(1, None, base=10)
    10: ExpressionStmt(13)
    11: Ident(printf)
    12: LiteralString(""1"")
    13: FunctionCall(callee=11, args=[12])
    14: Case(9, 10)
    15: Break
    16: LiteralInt(2, None, base=10)
    17: ExpressionStmt(20)
    18: Ident(printf)
    19: LiteralString(""2"")
    20: FunctionCall(callee=18, args=[19])
    21: Case(16, 17)
    22: Break
    23: ExpressionStmt(26)
    24: Ident(printf)
    25: LiteralString(""default"")
    26: FunctionCall(callee=24, args=[25])
    27: Default(23)
    28: Switch(7, 8)
    29: LiteralInt(0, None, base=8)
    30: Return(29)
    "#);
}

#[test]
fn test_dump_parser_ast() {
    let output = dump_parser_ast("int main() { return 0; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=main, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("main")
    4: CompoundStmt(stmts=5..5)
    5: Return(6)
    6: LiteralInt(0, None, base=8)
    "#);
}

#[test]
fn test_dump_parser_ast_with_functions() {
    let output = dump_parser_ast("int add(int a, int b) { return a + b; } int main() { return add(2, 3); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3)
    2: Function(name=add, symbol=4, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=5..6, body=7)
    3: Function(name=main, symbol=10, ty=TypeRef(base=22, class=Function, ptr=0, arr=None), params=[], body=13)
    4: LiteralString("add")
    5: Param(symbol=8, ty=QualType(8))
    6: Param(symbol=9, ty=QualType(8))
    7: CompoundStmt(stmts=8..8)
    8: Return(9)
    9: BinaryOp(Add, 10, 11)
    10: Ident(a)
    11: Ident(b)
    12: LiteralString("main")
    13: CompoundStmt(stmts=14..14)
    14: Return(15)
    15: FunctionCall(callee=16, args=17..18)
    16: Ident(add)
    17: LiteralInt(2, None, base=10)
    18: LiteralInt(3, None, base=10)
    "#);
}

#[test]
fn test_dump_type_registry() {
    let output = dump_type_registry("int main() { int x = 42; float y = 3.14; return x + (int)y; }");
    insta::assert_snapshot!(output, @"

    === TypeRegistry (Used TypeRefs) ===
    TypeRef(8): int
    TypeRef(14): float
    TypeRef(21): int()
    ");
}

#[test]
fn test_dump_type_registry_with_complex_types() {
    let output = dump_type_registry(
        "struct Point { int x; int y; }; int main() { struct Point p = {1, 2}; int *ptr = &p.x; float arr[10]; return 0; }",
    );
    insta::assert_snapshot!(output, @"

    === TypeRegistry (Used TypeRefs) ===
    TypeRef(8): int
    TypeRef(22): int()
    TypeRef(21): struct Point
    TypeRef(8): int*
    TypeRef(14): float[10]
    ");
}

#[test]
fn test_dump_parser_ast_with_designated_initializers() {
    let output = dump_parser_ast(
        "struct Point { int x; int y; }; int main() { struct Point p = {.x = 1, .y = 2}; int arr[5] = {[1] = 10, [3] = 30}; return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3)
    2: RecordDecl(name=Some("Point"), ty=1048597, is_union=false, members=4..5)
    3: Function(name=main, symbol=3, ty=TypeRef(base=22, class=Function, ptr=0, arr=None), params=[], body=7)
    4: FieldDecl(name=Some("x"), ty=Int)
    5: FieldDecl(name=Some("y"), ty=Int)
    6: LiteralString("main")
    7: CompoundStmt(stmts=8..10)
    8: VarDecl(name=p, ty=TypeRef(base=21, class=Record, ptr=0, arr=None), storage=None, is_tls=false)
    9: VarDecl(name=arr, ty=TypeRef(base=8, class=Array, ptr=0, arr=Some(5)), storage=None, is_tls=false)
    10: Return(28)
    11: InitializerList(inits=12..13)
    12: InitializerItem(.x = 14)
    13: InitializerItem(.y = 16)
    14: LiteralInt(1, None, base=10)
    15: Designator(.x)
    16: LiteralInt(2, None, base=10)
    17: Designator(.y)
    18: LiteralInt(5, None, base=10)
    19: InitializerList(inits=20..21)
    20: InitializerItem([24] = 22)
    21: InitializerItem([27] = 25)
    22: LiteralInt(10, None, base=10)
    23: Designator([24])
    24: LiteralInt(1, None, base=10)
    25: LiteralInt(30, None, base=10)
    26: Designator([27])
    27: LiteralInt(3, None, base=10)
    28: LiteralInt(0, None, base=8)
    "#);
}

#[test]
fn test_scope_of_function_decl() {
    use crate::ast::NodeKind;

    let source = "void foo();";
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let (_, artifact) = out.units.first_mut().unwrap();
    let ast = artifact.ast.as_ref().unwrap();

    let root = ast.get_root();
    if let NodeKind::TranslationUnit(tu) = ast.get_kind(root) {
        let expected_scope = tu.scope_id;
        let mut found = false;
        for decl in tu.decl_start.range(tu.decl_len) {
            if let NodeKind::FunctionDecl(_) = ast.get_kind(decl) {
                let scope_id = ast.scope_of(decl);
                assert_eq!(scope_id, expected_scope);
                found = true;
            }
        }
        assert!(found, "Did not find FunctionDecl node");
    } else {
        panic!("Root is not TranslationUnit");
    }
}
#[test]
fn test_parsed_ast_ternary() {
    let output = dump_parsed_ast("int f() { return 1 ? 2 : 3; }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[9])
    5: LiteralInt(1, None, base=10)
    6: LiteralInt(2, None, base=10)
    7: LiteralInt(3, None, base=10)
    8: TernaryOp(5, 6, 7)
    9: Return(8)
    ");
}

#[test]
fn test_parsed_ast_access() {
    let output = dump_parsed_ast(
        "struct S { int a; }; int f() { struct S s; struct S *p; int arr[10]; return s.a + p->a + arr[0]; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[4, 6])
    3: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: None, span: SourceSpan(2199040032783) }] })
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), Some(ParsedRecordDef { tag: Some("S"), members: Some([3]), is_union: false })))], init_declarators: [] })
    6: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 5, body: 7 })
    7: CompoundStmt(stmts=[8, 9, 10, 21])
    8: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), None))], init_declarators: [ParsedInitDeclarator { declarator: 6, initializer: None, span: SourceSpan(2199040032808) }] })
    9: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), None))], init_declarators: [ParsedInitDeclarator { declarator: 8, initializer: None, span: SourceSpan(2199056810036) }] })
    10: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 10, initializer: None, span: SourceSpan(2199140696124) }] })
    11: LiteralInt(10, None, base=10)
    12: Ident(s)
    13: MemberAccess(12, a, .)
    14: Ident(p)
    15: MemberAccess(14, a, ->)
    16: BinaryOp(Add, 13, 15)
    17: Ident(arr)
    18: LiteralInt(0, None, base=8)
    19: IndexAccess(17, 18)
    20: BinaryOp(Add, 16, 19)
    21: Return(20)
    "#);
}

#[test]
fn test_parsed_ast_sizeof_alignof() {
    let output = dump_parsed_ast("int f() { return (int)3.14 + sizeof(int) + sizeof(1) + _Alignof(int); }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[14])
    5: LiteralFloat(3.14, None)
    6: Cast(ParsedType { base: 1, declarator: 5, qualifiers: TypeQualifiers(0x0) }, 5)
    7: SizeOfType(ParsedType { base: 2, declarator: 6, qualifiers: TypeQualifiers(0x0) })
    8: BinaryOp(Add, 6, 7)
    9: LiteralInt(1, None, base=10)
    10: SizeOfExpr(9)
    11: BinaryOp(Add, 8, 10)
    12: AlignOfType(ParsedType { base: 3, declarator: 7, qualifiers: TypeQualifiers(0x0) })
    13: BinaryOp(Add, 11, 12)
    14: Return(13)
    ");
}

#[test]
fn test_parsed_ast_compound_literal() {
    let output = dump_parsed_ast("struct S { int a; }; int f() { return ((struct S){1}).a; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[4, 6])
    3: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: None, span: SourceSpan(2199040032783) }] })
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), Some(ParsedRecordDef { tag: Some("S"), members: Some([3]), is_union: false })))], init_declarators: [] })
    6: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 5, body: 7 })
    7: CompoundStmt(stmts=[12])
    8: LiteralInt(1, None, base=10)
    9: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 8 }])
    10: CompoundLiteral(ParsedType { base: 1, declarator: 6, qualifiers: TypeQualifiers(0x0) }, 9)
    11: MemberAccess(10, a, .)
    12: Return(11)
    "#);
}

#[test]
fn test_parsed_ast_gnu_stmt_expr() {
    let output = dump_parsed_ast("int f() { return ({ int x = 1; x; }); }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[11])
    5: CompoundStmt(stmts=[6, 8])
    6: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: Some(7), span: SourceSpan(2199107141656) }] })
    7: LiteralInt(1, None, base=10)
    8: ExpressionStmt(9)
    9: Ident(x)
    10: GnuStatementExpr(5, 9)
    11: Return(10)
    ");
}

#[test]
fn test_parsed_ast_builtins() {
    let output = dump_parsed_ast(
        "
        typedef __builtin_va_list va_list;
        int f(int x, ...) {
            va_list ap;
            __builtin_va_start(ap, x);
            int y = __builtin_va_arg(ap, int);
            __builtin_va_end(ap);
            __builtin_va_copy(ap, ap);
            return y;
        }
        struct S { int a; };
        int g() { return __builtin_offsetof(struct S, a); }
    ",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2, 4, 25, 27])
    2: Declaration(ParsedDecl { specifiers: [StorageClass(Typedef), TypeSpec(VaList)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: None, span: SourceSpan(2199140696099) }] })
    4: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 7, body: 5 })
    5: CompoundStmt(stmts=[6, 7, 11, 14, 17, 22])
    6: Declaration(ParsedDecl { specifiers: [TypeSpec(TypedefName("va_list"))], init_declarators: [ParsedInitDeclarator { declarator: 8, initializer: None, span: SourceSpan(2199056810076) }] })
    7: ExpressionStmt(10)
    8: Ident(ap)
    9: Ident(x)
    10: BuiltinVaStart(8, 9)
    11: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 9, initializer: Some(13), span: SourceSpan(2199509794967) }] })
    12: Ident(ap)
    13: BuiltinVaArg(ParsedType { base: 3, declarator: 10, qualifiers: TypeQualifiers(0x0) }, 12)
    14: ExpressionStmt(16)
    15: Ident(ap)
    16: BuiltinVaEnd(15)
    17: ExpressionStmt(20)
    18: Ident(ap)
    19: Ident(ap)
    20: BuiltinVaCopy(18, 19)
    21: Ident(y)
    22: Return(21)
    24: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 11, initializer: None, span: SourceSpan(2199040033078) }] })
    25: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), Some(ParsedRecordDef { tag: Some("S"), members: Some([24]), is_union: false })))], init_declarators: [] })
    27: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 15, body: 28 })
    28: CompoundStmt(stmts=[32])
    30: MemberAccess(29, a, .)
    31: BuiltinOffsetof(ParsedType { base: 4, declarator: 16, qualifiers: TypeQualifiers(0x0) }, 30)
    32: Return(31)
    "#);
}

#[test]
fn test_parsed_ast_generic() {
    let output = dump_parsed_ast("int f() { return _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[9])
    5: LiteralInt(1, None, base=10)
    6: GenericSelection(5, [ParsedGenericAssociation { type_name: Some(ParsedType { base: 1, declarator: 5, qualifiers: TypeQualifiers(0x0) }), result_expr: 7 }, ParsedGenericAssociation { type_name: None, result_expr: 8 }])
    7: LiteralInt(1, None, base=10)
    8: LiteralInt(0, None, base=8)
    9: Return(6)
    ");
}

#[test]
fn test_parsed_ast_labels() {
    let output = dump_parsed_ast("int f() { label: goto label; }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[6])
    5: Goto(label)
    6: Label(label, 5)
    ");
}

#[test]
fn test_parsed_ast_static_assert() {
    let source = r#"_Static_assert(1, "msg");"#;
    let parsed = dump_parsed_ast(source);
    insta::assert_snapshot!(parsed, @r#"
    1: TranslationUnit(decls=[5])
    3: LiteralInt(1, None, base=10)
    4: LiteralString(""msg"")
    5: StaticAssert(3, ""msg"")
    "#);

    let ast = dump_parser_ast(source);
    insta::assert_snapshot!(ast, @r#"
    1: TranslationUnit(decls=2..2)
    2: StaticAssert(condition=3, message=""msg"")
    3: LiteralInt(1, None, base=10)
    4: LiteralString(""msg"")
    "#);
}

#[test]
fn test_parsed_ast_empty_stmt() {
    let output = dump_parsed_ast("void f() { ; }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Void)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[5])
    5: EmptyStmt
    ");
}

#[test]
fn test_parser_ast_control_flow() {
    let output = dump_parser_ast("void f() { if (1) {} while(0) {} do {} while(0); for(;;) {} }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..8)
    5: If(condition=9, then=10, else=none)
    6: While(condition=11, body=12)
    7: DoWhile(13, 14)
    8: For(init=none, condition=none, increment=none, body=15)
    9: LiteralInt(1, None, base=10)
    10: CompoundStmt(stmts=[])
    11: LiteralInt(0, None, base=8)
    12: CompoundStmt(stmts=[])
    13: CompoundStmt(stmts=[])
    14: LiteralInt(0, None, base=8)
    15: CompoundStmt(stmts=[])
    "#);
}

#[test]
fn test_parser_ast_switch() {
    let output = dump_parser_ast("void f() { switch(1) { case 1: break; default: continue; } }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..5)
    5: Switch(6, 7)
    6: LiteralInt(1, None, base=10)
    7: CompoundStmt(stmts=8..9)
    8: Case(10, 11)
    9: Default(12)
    10: LiteralInt(1, None, base=10)
    11: Break
    12: Continue
    "#);
}

#[test]
fn test_parser_ast_ops() {
    let output =
        dump_parser_ast("void f() { int a = 1; int b = 2; int c; c = a + b; c = a > b ? a : b; c += 1; a++; ++b; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..12)
    5: VarDecl(name=a, ty=Int, storage=None, is_tls=false)
    6: VarDecl(name=b, ty=Int, storage=None, is_tls=false)
    7: VarDecl(name=c, ty=Int, storage=None, is_tls=false)
    8: ExpressionStmt(15)
    9: ExpressionStmt(20)
    10: ExpressionStmt(28)
    11: ExpressionStmt(31)
    12: ExpressionStmt(33)
    13: LiteralInt(1, None, base=10)
    14: LiteralInt(2, None, base=10)
    15: Assignment(Assign, 16, 17)
    16: Ident(c)
    17: BinaryOp(Add, 18, 19)
    18: Ident(a)
    19: Ident(b)
    20: Assignment(Assign, 21, 22)
    21: Ident(c)
    22: TernaryOp(23, 26, 27)
    23: BinaryOp(Greater, 24, 25)
    24: Ident(a)
    25: Ident(b)
    26: Ident(a)
    27: Ident(b)
    28: Assignment(AssignAdd, 29, 30)
    29: Ident(c)
    30: LiteralInt(1, None, base=10)
    31: PostIncrement(32)
    32: Ident(a)
    33: UnaryOp(PreIncrement, 34)
    34: Ident(b)
    "#);
}

#[test]
fn test_parser_ast_sizeof_alignof() {
    let output = dump_parser_ast("void f() { int a = (int)1.0; int s = sizeof(int) + sizeof(a) + _Alignof(int); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..6)
    5: VarDecl(name=a, ty=Int, storage=None, is_tls=false)
    6: VarDecl(name=s, ty=Int, storage=None, is_tls=false)
    7: Cast(Int, 8)
    8: LiteralFloat(1, None)
    9: BinaryOp(Add, 10, 14)
    10: BinaryOp(Add, 11, 12)
    11: SizeOfType(Int)
    12: SizeOfExpr(13)
    13: Ident(a)
    14: AlignOfType(Int)
    "#);
}

#[test]
fn test_parser_ast_access() {
    let output = dump_parser_ast(
        "struct S { int a; }; void f() { struct S s; struct S *p; int arr[10]; int x = s.a + p->a + arr[0]; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3)
    2: RecordDecl(name=Some("S"), ty=1048597, is_union=false, members=4..4)
    3: Function(name=f, symbol=3, ty=TypeRef(base=22, class=Function, ptr=0, arr=None), params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString("f")
    6: CompoundStmt(stmts=7..10)
    7: VarDecl(name=s, ty=TypeRef(base=21, class=Record, ptr=0, arr=None), storage=None, is_tls=false)
    8: VarDecl(name=p, ty=TypeRef(base=21, class=Pointer, ptr=1, arr=None), storage=None, is_tls=false)
    9: VarDecl(name=arr, ty=TypeRef(base=8, class=Array, ptr=0, arr=Some(10)), storage=None, is_tls=false)
    10: VarDecl(name=x, ty=Int, storage=None, is_tls=false)
    11: LiteralInt(10, None, base=10)
    12: BinaryOp(Add, 13, 18)
    13: BinaryOp(Add, 14, 16)
    14: MemberAccess(15, a, .)
    15: Ident(s)
    16: MemberAccess(17, a, ->)
    17: Ident(p)
    18: IndexAccess(19, 20)
    19: Ident(arr)
    20: LiteralInt(0, None, base=8)
    "#);
}

#[test]
fn test_parser_ast_compound_literal() {
    let output = dump_parser_ast("struct S { int a; }; void f() { struct S s = (struct S){1}; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3)
    2: RecordDecl(name=Some("S"), ty=1048597, is_union=false, members=4..4)
    3: Function(name=f, symbol=3, ty=TypeRef(base=22, class=Function, ptr=0, arr=None), params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString("f")
    6: CompoundStmt(stmts=7..7)
    7: VarDecl(name=s, ty=TypeRef(base=21, class=Record, ptr=0, arr=None), storage=None, is_tls=false)
    8: CompoundLiteral(TypeRef(base=21, class=Record, ptr=0, arr=None), 9)
    9: InitializerList(inits=10..10)
    10: InitializerItem(11)
    11: LiteralInt(1, None, base=10)
    "#);
}

#[test]
fn test_parser_ast_generic() {
    let output = dump_parser_ast("void f() { int x = _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..5)
    5: VarDecl(name=x, ty=Int, storage=None, is_tls=false)
    6: GenericSelection(control=7, associations=8..9)
    7: LiteralInt(1, None, base=10)
    8: GenericAssociation(ty=Some(QualType(8)), result_expr=10)
    9: GenericAssociation(ty=None, result_expr=11)
    10: LiteralInt(1, None, base=10)
    11: LiteralInt(0, None, base=8)
    "#);
}

#[test]
fn test_parser_ast_gnu_stmt_expr() {
    let output = dump_parser_ast("void f() { int x = ({ int y = 1; y; }); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..5)
    5: VarDecl(name=x, ty=Int, storage=None, is_tls=false)
    6: GnuStatementExpr(7, 11)
    7: CompoundStmt(stmts=8..9)
    8: VarDecl(name=y, ty=Int, storage=None, is_tls=false)
    9: ExpressionStmt(11)
    10: LiteralInt(1, None, base=10)
    11: Ident(y)
    "#);
}

#[test]
fn test_parser_ast_builtin_offsetof() {
    let output = dump_parser_ast("struct S { int a; }; void f() { int x = __builtin_offsetof(struct S, a); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3)
    2: RecordDecl(name=Some("S"), ty=1048597, is_union=false, members=4..4)
    3: Function(name=f, symbol=3, ty=TypeRef(base=22, class=Function, ptr=0, arr=None), params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString("f")
    6: CompoundStmt(stmts=7..7)
    7: VarDecl(name=x, ty=Int, storage=None, is_tls=false)
    8: BuiltinOffsetof(TypeRef(base=21, class=Record, ptr=0, arr=None), 9)
    9: MemberAccess(10, a, .)
    "#);
}
#[test]
fn test_parser_ast_labels() {
    let output = dump_parser_ast("void f() { L: goto L; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..5)
    5: Label(L, 6)
    6: Goto(L)
    "#);
}

#[test]
fn test_type_registry_complex() {
    let output = dump_type_registry(
        "
        typedef struct Point { int x, y; } Point;
        enum Color { RED, GREEN, BLUE };
        void f(int n) {
            _Complex double c;
            int arr[n]; // VLA
            Point p;
            enum Color color;
        }
        void g(int x, ...); // Variadic
    ",
    );
    insta::assert_snapshot!(output, @"

    === TypeRegistry (Used TypeRefs) ===
    TypeRef(8): int
    TypeRef(25): int[*]
    TypeRef(23): void(int)
    TypeRef(26): void(int, ...)
    TypeRef(21): struct Point
    TypeRef(22): enum Color
    TypeRef(24): _Complex double
    ");
}

#[test]
fn test_atomic_ops_and_case_range() {
    // __atomic_load_n etc are parser builtins that map to ParsedNodeKind::AtomicOp
    let output_parsed = dump_parsed_ast(
        "
        void f() {
            int a = 0;
            int b = __atomic_load_n(&a, 0);
            switch(a) {
                case 1 ... 5: break;
            }
        }
    ",
    );
    insta::assert_snapshot!(output_parsed, @"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Void)], declarator: 4, body: 4 })
    4: CompoundStmt(stmts=[5, 7, 18])
    5: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: Some(6), span: SourceSpan(2199107141668) }] })
    6: LiteralInt(0, None, base=8)
    7: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 6, initializer: Some(11), span: SourceSpan(2199459463227) }] })
    8: Ident(a)
    9: UnaryOp(AddrOf, 8)
    10: LiteralInt(0, None, base=8)
    11: AtomicOp(LoadN, args=[9, 10])
    12: Ident(a)
    13: CompoundStmt(stmts=[17])
    14: LiteralInt(1, None, base=10)
    15: LiteralInt(5, None, base=10)
    16: Break
    17: CaseRange(14, 15, 16)
    18: Switch(12, 13)
    ");

    let output_parser = dump_parser_ast(
        "
        void f() {
            int a = 0;
            // Semantic lowering currently doesn't support atomic ops fully or might convert them differently?
            // But let's check CaseRange.
            switch(a) {
                case 1 ... 5: break;
            }
        }
    ",
    );
    insta::assert_snapshot!(output_parser, @r#"
    1: TranslationUnit(decls=2..2)
    2: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..6)
    5: VarDecl(name=a, ty=Int, storage=None, is_tls=false)
    6: Switch(8, 9)
    7: LiteralInt(0, None, base=8)
    8: Ident(a)
    9: CompoundStmt(stmts=10..10)
    10: CaseRange(11, 12, 13)
    11: LiteralInt(1, None, base=10)
    12: LiteralInt(5, None, base=10)
    13: Break
    "#);
}
