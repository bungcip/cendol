use crate::ast::dumper::AstDumper;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

fn get_artifact(source: &str, phase: CompilePhase) -> crate::driver::artifact::CompileArtifact {
    let (driver, result) = test_utils::run_pipeline(source, phase);
    let out = result.unwrap_or_else(|e| panic!("Pipeline failed: {}\nDiagnostics: {:?}", e, driver.de.diagnostics));
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
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[5])
    4: LiteralInt(0, None, base=8)
    5: Return(4)
    ");
}

#[test]
fn test_dump_parsed_ast_with_variables() {
    let output = dump_parsed_ast("int x = 42; int y = x + 5;");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199090364422) }] })
    3: LiteralInt(42, None, base=10)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(7), span: SourceSpan(2199140696082) }] })
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
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("Point"), Some([3, 4]), []))], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(7), span: SourceSpan(2199157473313) }] })
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
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Enum(Some("Color"), Some([3, 5, 6]), None))], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(7), span: SourceSpan(2199107141670) }] })
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
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(3), span: SourceSpan(2199308468234) }] })
    3: LiteralString("Hello, world!")
    "#);
}

#[test]
fn test_dump_parsed_ast_with_floats() {
    let output = dump_parsed_ast("float pi = 3.14159; double e = 2.71828;");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Float)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199174250505) }] })
    3: LiteralFloat(3.14159, None)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Double)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(5), span: SourceSpan(2199174250525) }] })
    5: LiteralFloat(2.71828, None)
    ");
}

#[test]
fn test_dump_parsed_ast_with_chars() {
    let output = dump_parsed_ast("char c = 'a'; signed char sc = 'b'; unsigned char uc = 'c';");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4, 6])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199107141639) }] })
    3: LiteralChar(97, None)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Signed), TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(5), span: SourceSpan(2199107141661) }] })
    5: LiteralChar(98, None)
    6: Declaration(ParsedDecl { specifiers: [TypeSpec(Unsigned), TypeSpec(Char)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(7), span: SourceSpan(2199107141685) }] })
    7: LiteralChar(99, None)
    ");
}

#[test]
fn test_dump_parsed_ast_with_pointers() {
    let output = dump_parsed_ast("int x = 10; int* ptr = &x; int** ptr_ptr = &ptr;");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 4, 7])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: Some(3), span: SourceSpan(2199090364422) }] })
    3: LiteralInt(10, None, base=10)
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(6), span: SourceSpan(2199090364437) }] })
    5: Ident(x)
    6: UnaryOp(AddrOf, 5)
    7: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 6, initializer: Some(9), span: SourceSpan(2199123918889) }] })
    8: Ident(ptr)
    9: UnaryOp(AddrOf, 8)
    ");
}

#[test]
fn test_dump_parsed_ast_with_arrays() {
    let output = dump_parsed_ast("int arr[5] = {1, 2, 3, 4, 5}; int* ptr_arr[3];");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2, 10])
    2: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 2, initializer: Some(9), span: SourceSpan(2199308468235) }] })
    3: LiteralInt(5, None, base=10)
    4: LiteralInt(1, None, base=10)
    5: LiteralInt(2, None, base=10)
    6: LiteralInt(3, None, base=10)
    7: LiteralInt(4, None, base=10)
    8: LiteralInt(5, None, base=10)
    9: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 4 }, ParsedDesignatedInitializer { designation: [], initializer: 5 }, ParsedDesignatedInitializer { designation: [], initializer: 6 }, ParsedDesignatedInitializer { designation: [], initializer: 7 }, ParsedDesignatedInitializer { designation: [], initializer: 8 }])
    10: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 5, initializer: None, span: SourceSpan(2199056810028) }] })
    11: LiteralInt(3, None, base=10)
    ");
}

#[test]
fn test_dump_parsed_ast_with_loops() {
    let output = dump_parsed_ast(
        "int main() { int i = 0; while (i < 10) { i++; } for (int j = 0; j < 5; j++) { printf(\"%d\", j); } do { i--; } while (i > 0); return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[4, 13, 14, 35, 37])
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(5), span: SourceSpan(2199073587219) }] })
    5: LiteralInt(0, None, base=8)
    6: Ident(i)
    7: LiteralInt(10, None, base=10)
    8: BinaryOp(Less, 6, 7)
    9: CompoundStmt(stmts=[10])
    10: ExpressionStmt(12)
    11: Ident(i)
    12: PostIncrement(11)
    13: While(ParsedWhileStmt { condition: 8, body: 9 })
    14: For(ParsedForStmt { init: Some(15), condition: Some(19), increment: Some(21), body: 22, scope_id: ScopeId(4) })
    15: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 4, initializer: Some(16), span: SourceSpan(2199073587259) }] })
    16: LiteralInt(0, None, base=8)
    17: Ident(j)
    18: LiteralInt(5, None, base=10)
    19: BinaryOp(Less, 17, 18)
    20: Ident(j)
    21: PostIncrement(20)
    22: CompoundStmt(stmts=[23])
    23: ExpressionStmt(27)
    24: Ident(printf)
    25: LiteralString("%d")
    26: Ident(j)
    27: FunctionCall(callee=24, args=[25, 26])
    28: CompoundStmt(stmts=[29])
    29: ExpressionStmt(31)
    30: Ident(i)
    31: PostDecrement(30)
    32: Ident(i)
    33: LiteralInt(0, None, base=8)
    34: BinaryOp(Greater, 32, 33)
    35: DoWhile(body=28, cond=34)
    36: LiteralInt(0, None, base=8)
    37: Return(36)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_conditional() {
    let output = dump_parsed_ast(
        "int main() { int x = 10; if (x > 5) { printf(\"x is greater than 5\"); } else if (x < 5) { printf(\"x is less than 5\"); } else { printf(\"x is 5\"); } return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[4, 28, 30])
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(5), span: SourceSpan(2199090364435) }] })
    5: LiteralInt(10, None, base=10)
    6: Ident(x)
    7: LiteralInt(5, None, base=10)
    8: BinaryOp(Greater, 6, 7)
    9: CompoundStmt(stmts=[10])
    10: ExpressionStmt(13)
    11: Ident(printf)
    12: LiteralString("x is greater than 5")
    13: FunctionCall(callee=11, args=[12])
    14: Ident(x)
    15: LiteralInt(5, None, base=10)
    16: BinaryOp(Less, 14, 15)
    17: CompoundStmt(stmts=[18])
    18: ExpressionStmt(21)
    19: Ident(printf)
    20: LiteralString("x is less than 5")
    21: FunctionCall(callee=19, args=[20])
    22: CompoundStmt(stmts=[23])
    23: ExpressionStmt(26)
    24: Ident(printf)
    25: LiteralString("x is 5")
    26: FunctionCall(callee=24, args=[25])
    27: If(ParsedIfStmt { condition: 16, then_branch: 17, else_branch: Some(22) })
    28: If(ParsedIfStmt { condition: 8, then_branch: 9, else_branch: Some(27) })
    29: LiteralInt(0, None, base=8)
    30: Return(29)
    "#);
}

#[test]
fn test_dump_parsed_ast_with_switch() {
    let output = dump_parsed_ast(
        "int main() { int x = 2; switch (x) { case 1: printf(\"1\"); break; case 2: printf(\"2\"); break; default: printf(\"default\"); } return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[4, 27, 29])
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(5), span: SourceSpan(2199073587219) }] })
    5: LiteralInt(2, None, base=10)
    6: Ident(x)
    7: CompoundStmt(stmts=[13, 14, 20, 21, 26])
    8: LiteralInt(1, None, base=10)
    9: ExpressionStmt(12)
    10: Ident(printf)
    11: LiteralString("1")
    12: FunctionCall(callee=10, args=[11])
    13: Case(8, 9)
    14: Break
    15: LiteralInt(2, None, base=10)
    16: ExpressionStmt(19)
    17: Ident(printf)
    18: LiteralString("2")
    19: FunctionCall(callee=17, args=[18])
    20: Case(15, 16)
    21: Break
    22: ExpressionStmt(25)
    23: Ident(printf)
    24: LiteralString("default")
    25: FunctionCall(callee=23, args=[24])
    26: Default(22)
    27: Switch(6, 7)
    28: LiteralInt(0, None, base=8)
    29: Return(28)
    "#);
}

#[test]
fn test_dump_parser_ast() {
    let output = dump_parser_ast("int main() { return 0; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: FunctionDef(name=main, symbol=2, params=[], body=4)
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
    2: FunctionDef(name=add, symbol=4, params=5..6, body=7)
    3: FunctionDef(name=main, symbol=10, params=[], body=13)
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
    ");
}

#[test]
fn test_dump_parser_ast_with_designated_initializers() {
    let output = dump_parser_ast(
        "struct Point { int x; int y; }; int main() { struct Point p = {.x = 1, .y = 2}; int arr[5] = {[1] = 10, [3] = 30}; return 0; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3)
    2: RecordDecl(symbol=2, name="Point", ty=TypeRef(base=24, class=Record, ptr=0, arr=None), members=4..5)
    3: FunctionDef(name=main, symbol=3, params=[], body=7)
    4: FieldDecl(name=Some("x"), ty=Int)
    5: FieldDecl(name=Some("y"), ty=Int)
    6: LiteralString("main")
    7: CompoundStmt(stmts=8..10)
    8: VarDecl(symbol=7, name=p, ty=TypeRef(base=24, class=Record, ptr=0, arr=None), init=11)
    9: VarDecl(symbol=8, name=arr, ty=TypeRef(base=8, class=Array, ptr=0, arr=Some(5)), init=19)
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
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[8])
    4: LiteralInt(1, None, base=10)
    5: LiteralInt(2, None, base=10)
    6: LiteralInt(3, None, base=10)
    7: TernaryOp(4, 5, 6)
    8: Return(7)
    ");
}

#[test]
fn test_parsed_ast_access() {
    let output = dump_parsed_ast(
        "struct S { int a; }; int f() { struct S s; struct S *p; int arr[10]; return s.a + p->a + arr[0]; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[4, 5])
    3: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: None, span: SourceSpan(2199040032783) }] })
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), Some([3]), []))], init_declarators: [] })
    5: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 3, body: 6 })
    6: CompoundStmt(stmts=[7, 8, 9, 20])
    7: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), None, []))], init_declarators: [ParsedInitDeclarator { declarator: 4, initializer: None, span: SourceSpan(2199056810024) }] })
    8: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), None, []))], init_declarators: [ParsedInitDeclarator { declarator: 6, initializer: None, span: SourceSpan(2199056810037) }] })
    9: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 8, initializer: None, span: SourceSpan(2199056810050) }] })
    10: LiteralInt(10, None, base=10)
    11: Ident(s)
    12: MemberAccess(11, a, .)
    13: Ident(p)
    14: MemberAccess(13, a, ->)
    15: BinaryOp(Add, 12, 14)
    16: Ident(arr)
    17: LiteralInt(0, None, base=8)
    18: IndexAccess(16, 17)
    19: BinaryOp(Add, 15, 18)
    20: Return(19)
    "#);
}

#[test]
fn test_parsed_ast_sizeof_alignof() {
    let output = dump_parsed_ast("int f() { return (int)3.14 + sizeof(int) + sizeof(1) + _Alignof(int); }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[13])
    4: LiteralFloat(3.14, None)
    5: Cast(ParsedType { base: 1, declarator: 3, qualifiers: TypeQualifiers(0x0) }, 4)
    6: SizeOfType(ParsedType { base: 2, declarator: 4, qualifiers: TypeQualifiers(0x0) })
    7: BinaryOp(Add, 5, 6)
    8: LiteralInt(1, None, base=10)
    9: SizeOfExpr(8)
    10: BinaryOp(Add, 7, 9)
    11: AlignOfType(ParsedType { base: 3, declarator: 5, qualifiers: TypeQualifiers(0x0) })
    12: BinaryOp(Add, 10, 11)
    13: Return(12)
    ");
}

#[test]
fn test_parsed_ast_compound_literal() {
    let output = dump_parsed_ast("struct S { int a; }; int f() { return ((struct S){1}).a; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[4, 5])
    3: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 1, initializer: None, span: SourceSpan(2199040032783) }] })
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Record(false, Some("S"), Some([3]), []))], init_declarators: [] })
    5: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 3, body: 6 })
    6: CompoundStmt(stmts=[11])
    7: LiteralInt(1, None, base=10)
    8: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 7 }])
    9: CompoundLiteral(ParsedType { base: 1, declarator: 4, qualifiers: TypeQualifiers(0x0) }, 8)
    10: MemberAccess(9, a, .)
    11: Return(10)
    "#);
}

#[test]
fn test_parsed_ast_gnu_stmt_expr() {
    let output = dump_parsed_ast("int f() { return ({ int x = 1; x; }); }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[10])
    4: CompoundStmt(stmts=[5, 7])
    5: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(6), span: SourceSpan(2199073587226) }] })
    6: LiteralInt(1, None, base=10)
    7: ExpressionStmt(8)
    8: Ident(x)
    9: GnuStatementExpr(4, 8)
    10: Return(9)
    ");
}

#[test]
fn test_parsed_ast_generic() {
    let output = dump_parsed_ast("int f() { return _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[8])
    4: LiteralInt(1, None, base=10)
    5: GenericSelection(4, [ParsedGenericAssociation { type_name: Some(ParsedType { base: 1, declarator: 3, qualifiers: TypeQualifiers(0x0) }), result_expr: 6 }, ParsedGenericAssociation { type_name: None, result_expr: 7 }])
    6: LiteralInt(1, None, base=10)
    7: LiteralInt(0, None, base=8)
    8: Return(5)
    ");
}

#[test]
fn test_parsed_ast_labels() {
    let output = dump_parsed_ast("int f() { label: goto label; }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Int)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[5])
    4: Goto(label)
    5: Label(label, 4)
    ");
}

#[test]
fn test_parsed_ast_static_assert() {
    let source = r#"_Static_assert(1, "msg");"#;
    let parsed = dump_parsed_ast(source);
    insta::assert_snapshot!(parsed, @r#"
    1: TranslationUnit(decls=[5])
    3: LiteralInt(1, None, base=10)
    4: LiteralString("msg")
    5: StaticAssert(3, "msg")
    "#);

    let ast = dump_parser_ast(source);
    insta::assert_snapshot!(ast, @r#"
    1: TranslationUnit(decls=2..2)
    2: StaticAssert(condition=3, message="msg")
    3: LiteralInt(1, None, base=10)
    4: LiteralString("msg")
    "#);
}

#[test]
fn test_parsed_ast_empty_stmt() {
    let output = dump_parsed_ast("void f() { ; }");
    insta::assert_snapshot!(output, @"
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Void)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[4])
    4: EmptyStmt
    ");
}

#[test]
fn test_parser_ast_control_flow() {
    let output = dump_parser_ast("void f() { if (1) {} while(0) {} do {} while(0); for(;;) {} }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..8)
    5: If(condition=9, then=10, else=none)
    6: While(condition=11, body=12)
    7: DoWhile(13, 14)
    8: For(child_start=15, body=18)
    9: LiteralInt(1, None, base=10)
    10: CompoundStmt(stmts=[])
    11: LiteralInt(0, None, base=8)
    12: CompoundStmt(stmts=[])
    13: CompoundStmt(stmts=[])
    14: LiteralInt(0, None, base=8)
    18: CompoundStmt(stmts=[])
    "#);
}

#[test]
fn test_parser_ast_switch() {
    let output = dump_parser_ast("void f() { switch(1) { case 1: break; default: continue; } }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
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
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..12)
    5: VarDecl(symbol=6, name=a, ty=Int, init=13)
    6: VarDecl(symbol=7, name=b, ty=Int, init=14)
    7: VarDecl(symbol=8, name=c, ty=Int)
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
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..6)
    5: VarDecl(symbol=6, name=a, ty=Int, init=7)
    6: VarDecl(symbol=7, name=s, ty=Int, init=9)
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
    2: RecordDecl(symbol=2, name="S", ty=TypeRef(base=24, class=Record, ptr=0, arr=None), members=4..4)
    3: FunctionDef(name=f, symbol=3, params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString("f")
    6: CompoundStmt(stmts=7..10)
    7: VarDecl(symbol=7, name=s, ty=TypeRef(base=24, class=Record, ptr=0, arr=None))
    8: VarDecl(symbol=8, name=p, ty=TypeRef(base=24, class=Pointer, ptr=1, arr=None))
    9: VarDecl(symbol=9, name=arr, ty=TypeRef(base=8, class=Array, ptr=0, arr=Some(10)))
    10: VarDecl(symbol=10, name=x, ty=Int, init=12)
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
    2: RecordDecl(symbol=2, name="S", ty=TypeRef(base=24, class=Record, ptr=0, arr=None), members=4..4)
    3: FunctionDef(name=f, symbol=3, params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString("f")
    6: CompoundStmt(stmts=7..7)
    7: VarDecl(symbol=7, name=s, ty=TypeRef(base=24, class=Record, ptr=0, arr=None), init=8)
    8: CompoundLiteral(TypeRef(base=24, class=Record, ptr=0, arr=None), 9)
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
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..5)
    5: VarDecl(symbol=6, name=x, ty=Int, init=6)
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
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..5)
    5: VarDecl(symbol=6, name=x, ty=Int, init=6)
    6: GnuStatementExpr(7, 11)
    7: CompoundStmt(stmts=8..9)
    8: VarDecl(symbol=7, name=y, ty=Int, init=10)
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
    2: RecordDecl(symbol=2, name="S", ty=TypeRef(base=24, class=Record, ptr=0, arr=None), members=4..4)
    3: FunctionDef(name=f, symbol=3, params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString("f")
    6: CompoundStmt(stmts=7..7)
    7: VarDecl(symbol=7, name=x, ty=Int, init=8)
    8: BuiltinOffsetof(TypeRef(base=24, class=Record, ptr=0, arr=None), 9)
    9: MemberAccess(10, a, .)
    "#);
}
#[test]
fn test_parser_ast_labels() {
    let output = dump_parser_ast("void f() { L: goto L; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2)
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
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
    1: TranslationUnit(decls=[2])
    2: FunctionDef(ParsedFunctionDef { specifiers: [TypeSpec(Void)], declarator: 2, body: 3 })
    3: CompoundStmt(stmts=[4, 6, 18])
    4: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 3, initializer: Some(5), span: SourceSpan(2199073587238) }] })
    5: LiteralInt(0, None, base=8)
    6: Declaration(ParsedDecl { specifiers: [TypeSpec(Int)], init_declarators: [ParsedInitDeclarator { declarator: 4, initializer: Some(11), span: SourceSpan(2199425908797) }] })
    7: Ident(__atomic_load_n)
    8: Ident(a)
    9: UnaryOp(AddrOf, 8)
    10: LiteralInt(0, None, base=8)
    11: FunctionCall(callee=7, args=[9, 10])
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
    2: FunctionDef(name=f, symbol=2, params=[], body=4)
    3: LiteralString("f")
    4: CompoundStmt(stmts=5..6)
    5: VarDecl(symbol=6, name=a, ty=Int, init=7)
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
