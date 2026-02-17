#![cfg(test)]
use crate::ast::dumper::AstDumper;
use crate::driver::artifact::CompilePhase;
use crate::tests::test_utils;

fn dump_parsed_ast(source: &str) -> String {
    let phase = CompilePhase::Parse;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.parsed_ast.as_ref().unwrap();
    AstDumper::dump_parsed_ast(ast).to_string()
}

fn dump_parser_ast(source: &str) -> String {
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let symbol_table = artifact.symbol_table.as_ref().unwrap();
    AstDumper::dump_parser(ast, Some(symbol_table)).to_string()
}

fn dump_type_registry(source: &str) -> String {
    let phase = CompilePhase::SemanticLowering;
    let (_, out) = test_utils::run_pipeline(source, phase);
    let mut out = out.unwrap();
    let first = out.units.first_mut().unwrap();
    let artifact = first.1;
    let ast = artifact.ast.as_ref().unwrap();
    let type_registry = artifact.type_registry.as_ref().unwrap();
    AstDumper::dump_type_registry(ast, type_registry).to_string()
}

#[test]
fn test_parsed_ast_ternary() {
    let output = dump_parsed_ast("int f() { return 1 ? 2 : 3; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[9])
    5: LiteralInt(1, None)
    6: LiteralInt(2, None)
    7: LiteralInt(3, None)
    8: TernaryOp(5, 6, 7)
    9: Return(8)
    "#);
}

#[test]
fn test_parsed_ast_access() {
    let output = dump_parsed_ast(
        "struct S { int a; }; int f() { struct S s; struct S *p; int arr[10]; return s.a + p->a + arr[0]; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3, 5])
    3: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Record(false, Some("S"), Some(ParsedRecordDefData { tag: Some("S"), members: Some([ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("a", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199040032783) }] }]), is_union: false })))], init_declarators: [] })
    5: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 6 })
    6: CompoundStatement(stmts=[7, 8, 9, 20])
    7: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Record(false, Some("S"), None))], init_declarators: [ParsedInitDeclarator { declarator: Identifier("s", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199040032808) }] })
    8: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Record(false, Some("S"), None))], init_declarators: [ParsedInitDeclarator { declarator: Pointer(TypeQualifiers(0x0), Some(Identifier("p", TypeQualifiers(0x0)))), initializer: None, span: SourceSpan(2199056810036) }] })
    9: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Array(Identifier("arr", TypeQualifiers(0x0)), Expression { expr: 10, qualifiers: TypeQualifiers(0x0) }), initializer: None, span: SourceSpan(2199140696124) }] })
    10: LiteralInt(10, None)
    11: Ident(s)
    12: MemberAccess(11, a, .)
    13: Ident(p)
    14: MemberAccess(13, a, ->)
    15: BinaryOp(Add, 12, 14)
    16: Ident(arr)
    17: LiteralInt(0, None)
    18: IndexAccess(16, 17)
    19: BinaryOp(Add, 15, 18)
    20: Return(19)
    "#);
}

#[test]
fn test_parsed_ast_sizeof_alignof() {
    let output = dump_parsed_ast("int f() { return (int)3.14 + sizeof(int) + sizeof(1) + _Alignof(int); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[14])
    5: LiteralFloat(3.14, None)
    6: Cast(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) }, 5)
    7: SizeOfType(ParsedType { base: 2, declarator: 2, qualifiers: TypeQualifiers(0x0) })
    8: BinaryOp(Add, 6, 7)
    9: LiteralInt(1, None)
    10: SizeOfExpr(9)
    11: BinaryOp(Add, 8, 10)
    12: AlignOf(ParsedType { base: 3, declarator: 3, qualifiers: TypeQualifiers(0x0) })
    13: BinaryOp(Add, 11, 12)
    14: Return(13)
    "#);
}

#[test]
fn test_parsed_ast_compound_literal() {
    let output = dump_parsed_ast("struct S { int a; }; int f() { return ((struct S){1}).a; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3, 5])
    3: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Record(false, Some("S"), Some(ParsedRecordDefData { tag: Some("S"), members: Some([ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("a", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199040032783) }] }]), is_union: false })))], init_declarators: [] })
    5: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 6 })
    6: CompoundStatement(stmts=[11])
    7: LiteralInt(1, None)
    8: InitializerList([ParsedDesignatedInitializer { designation: [], initializer: 7 }])
    9: CompoundLiteral(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) }, 8)
    10: MemberAccess(9, a, .)
    11: Return(10)
    "#);
}

#[test]
fn test_parsed_ast_gnu_stmt_expr() {
    let output = dump_parsed_ast("int f() { return ({ int x = 1; x; }); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[11])
    5: CompoundStatement(stmts=[6, 8])
    6: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("x", TypeQualifiers(0x0)), initializer: Some(7), span: SourceSpan(2199107141656) }] })
    7: LiteralInt(1, None)
    8: ExpressionStatement(9)
    9: Ident(x)
    10: GnuStatementExpression(5, 9)
    11: Return(10)
    "#);
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
    1: TranslationUnit(decls=[2, 4, 24, 26])
    2: Declaration(ParsedDeclarationData { specifiers: [StorageClass(Typedef), TypeSpecifier(VaList)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("va_list", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199140696099) }] })
    4: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [ParsedParamData { specifiers: [TypeSpecifier(Int)], declarator: Some(Identifier("x", TypeQualifiers(0x0))), span: SourceSpan(2199107141690) }], is_variadic: true }, body: 5 })
    5: CompoundStatement(stmts=[6, 7, 11, 14, 17, 22])
    6: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(TypedefName("va_list"))], init_declarators: [ParsedInitDeclarator { declarator: Identifier("ap", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199056810076) }] })
    7: ExpressionStatement(10)
    8: Ident(ap)
    9: Ident(x)
    10: BuiltinVaStart(8, 9)
    11: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("y", TypeQualifiers(0x0)), initializer: Some(13), span: SourceSpan(2199509794967) }] })
    12: Ident(ap)
    13: BuiltinVaArg(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) }, 12)
    14: ExpressionStatement(16)
    15: Ident(ap)
    16: BuiltinVaEnd(15)
    17: ExpressionStatement(20)
    18: Ident(ap)
    19: Ident(ap)
    20: BuiltinVaCopy(18, 19)
    21: Ident(y)
    22: Return(21)
    24: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Record(false, Some("S"), Some(ParsedRecordDefData { tag: Some("S"), members: Some([ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("a", TypeQualifiers(0x0)), initializer: None, span: SourceSpan(2199040033078) }] }]), is_union: false })))], init_declarators: [] })
    26: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("g", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 27 })
    27: CompoundStatement(stmts=[31])
    29: MemberAccess(28, a, .)
    30: BuiltinOffsetof(ParsedType { base: 2, declarator: 2, qualifiers: TypeQualifiers(0x0) }, 29)
    31: Return(30)
    "#);
}

#[test]
fn test_parsed_ast_generic() {
    let output = dump_parsed_ast("int f() { return _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[9])
    5: LiteralInt(1, None)
    6: GenericSelection(5, [ParsedGenericAssociation { type_name: Some(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) }), result_expr: 7 }, ParsedGenericAssociation { type_name: None, result_expr: 8 }])
    7: LiteralInt(1, None)
    8: LiteralInt(0, None)
    9: Return(6)
    "#);
}

#[test]
fn test_parsed_ast_labels() {
    let output = dump_parsed_ast("int f() { label: goto label; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Int)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[6])
    5: Goto(label)
    6: Label(label, 5)
    "#);
}

#[test]
fn test_parsed_ast_static_assert() {
    let output = dump_parsed_ast("_Static_assert(1, \"msg\");");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[5])
    3: LiteralInt(1, None)
    4: LiteralString(""msg"")
    5: StaticAssert(3, ""msg"")
    "#);
}

#[test]
fn test_parsed_ast_empty_stmt() {
    let output = dump_parsed_ast("void f() { ; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Void)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[5])
    5: EmptyStatement
    "#);
}

#[test]
fn test_parser_ast_control_flow() {
    let output = dump_parser_ast("void f() { if (1) {} while(0) {} do {} while(0); for(;;) {} }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..8)
    5: If(condition=9, then=10, else=none)
    6: While(condition=11, body=12)
    7: DoWhile(body=13, condition=14)
    8: For(init=none, condition=none, increment=none, body=15)
    9: LiteralInt(1, None)
    10: CompoundStatement(stmts=[])
    11: LiteralInt(0, None)
    12: CompoundStatement(stmts=[])
    13: CompoundStatement(stmts=[])
    14: LiteralInt(0, None)
    15: CompoundStatement(stmts=[])
    ");
}

#[test]
fn test_parser_ast_switch() {
    let output = dump_parser_ast("void f() { switch(1) { case 1: break; default: continue; } }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..5)
    5: Switch(condition=6, body=7)
    6: LiteralInt(1, None)
    7: CompoundStatement(stmts=8..9)
    8: Case(10, 11)
    9: Default(12)
    10: LiteralInt(1, None)
    11: Break
    12: Continue
    ");
}

#[test]
fn test_parser_ast_ops() {
    let output =
        dump_parser_ast("void f() { int a = 1; int b = 2; int c; c = a + b; c = a > b ? a : b; c += 1; a++; ++b; }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..12)
    5: VarDecl(name=a, ty=Int, storage=None)
    6: VarDecl(name=b, ty=Int, storage=None)
    7: VarDecl(name=c, ty=Int, storage=None)
    8: ExpressionStatement(15)
    9: ExpressionStatement(20)
    10: ExpressionStatement(28)
    11: ExpressionStatement(31)
    12: ExpressionStatement(33)
    13: LiteralInt(1, None)
    14: LiteralInt(2, None)
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
    30: LiteralInt(1, None)
    31: PostIncrement(32)
    32: Ident(a)
    33: UnaryOp(PreIncrement, 34)
    34: Ident(b)
    ");
}

#[test]
fn test_parser_ast_sizeof_alignof() {
    let output = dump_parser_ast("void f() { int a = (int)1.0; int s = sizeof(int) + sizeof(a) + _Alignof(int); }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..6)
    5: VarDecl(name=a, ty=Int, storage=None)
    6: VarDecl(name=s, ty=Int, storage=None)
    7: Cast(Int, 8)
    8: LiteralFloat(1, None)
    9: BinaryOp(Add, 10, 14)
    10: BinaryOp(Add, 11, 12)
    11: SizeOfType(Int)
    12: SizeOfExpr(13)
    13: Ident(a)
    14: AlignOf(Int)
    ");
}

#[test]
fn test_parser_ast_access() {
    let output = dump_parser_ast(
        "struct S { int a; }; void f() { struct S s; struct S *p; int arr[10]; int x = s.a + p->a + arr[0]; }",
    );
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3) (parser kind)
    2: RecordDecl(name=Some("S"), ty=1048596, is_union=false, members=4..4)
    3: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString(f)
    6: CompoundStatement(stmts=7..10)
    7: VarDecl(name=s, ty=TypeRef(base=20, class=Record, ptr=0, arr=None), storage=None)
    8: VarDecl(name=p, ty=TypeRef(base=20, class=Pointer, ptr=1, arr=None), storage=None)
    9: VarDecl(name=arr, ty=TypeRef(base=8, class=Array, ptr=0, arr=Some(10)), storage=None)
    10: VarDecl(name=x, ty=Int, storage=None)
    11: LiteralInt(10, None)
    12: BinaryOp(Add, 13, 18)
    13: BinaryOp(Add, 14, 16)
    14: MemberAccess(15, a, .)
    15: Ident(s)
    16: MemberAccess(17, a, ->)
    17: Ident(p)
    18: IndexAccess(19, 20)
    19: Ident(arr)
    20: LiteralInt(0, None)
    "#);
}

#[test]
fn test_parser_ast_compound_literal() {
    let output = dump_parser_ast("struct S { int a; }; void f() { struct S s = (struct S){1}; }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3) (parser kind)
    2: RecordDecl(name=Some("S"), ty=1048596, is_union=false, members=4..4)
    3: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString(f)
    6: CompoundStatement(stmts=7..7)
    7: VarDecl(name=s, ty=TypeRef(base=20, class=Record, ptr=0, arr=None), storage=None)
    8: CompoundLiteral(TypeRef(base=20, class=Record, ptr=0, arr=None), 9)
    9: InitializerList(inits=10..10)
    10: InitializerItem(11)
    11: LiteralInt(1, None)
    "#);
}

#[test]
fn test_parser_ast_generic() {
    let output = dump_parser_ast("void f() { int x = _Generic(1, int: 1, default: 0); }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..5)
    5: VarDecl(name=x, ty=Int, storage=None)
    6: GenericSelection(control=7, associations=8..9)
    7: LiteralInt(1, None)
    8: GenericAssociation(ty=Some(QualType(8)), result_expr=10)
    9: GenericAssociation(ty=None, result_expr=11)
    10: LiteralInt(1, None)
    11: LiteralInt(0, None)
    ");
}

#[test]
fn test_parser_ast_gnu_stmt_expr() {
    let output = dump_parser_ast("void f() { int x = ({ int y = 1; y; }); }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..5)
    5: VarDecl(name=x, ty=Int, storage=None)
    6: GnuStatementExpression(7, 11)
    7: CompoundStatement(stmts=8..9)
    8: VarDecl(name=y, ty=Int, storage=None)
    9: ExpressionStatement(11)
    10: LiteralInt(1, None)
    11: Ident(y)
    ");
}

#[test]
fn test_parser_ast_builtin_offsetof() {
    let output = dump_parser_ast("struct S { int a; }; void f() { int x = __builtin_offsetof(struct S, a); }");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..3) (parser kind)
    2: RecordDecl(name=Some("S"), ty=1048596, is_union=false, members=4..4)
    3: Function(name=f, symbol=2, ty=TypeRef(base=21, class=Function, ptr=0, arr=None), params=[], body=6)
    4: FieldDecl(name=Some("a"), ty=Int)
    5: LiteralString(f)
    6: CompoundStatement(stmts=7..7)
    7: VarDecl(name=x, ty=Int, storage=None)
    8: BuiltinOffsetof(TypeRef(base=20, class=Record, ptr=0, arr=None), 9)
    9: MemberAccess(10, a, .)
    "#);
}

#[test]
fn test_parser_ast_static_assert() {
    let output = dump_parser_ast("_Static_assert(1, \"msg\");");
    insta::assert_snapshot!(output, @r#"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: StaticAssert(condition=3, message=""msg"")
    3: LiteralInt(1, None)
    4: LiteralString("msg")
    "#);
}

#[test]
fn test_parser_ast_labels() {
    let output = dump_parser_ast("void f() { L: goto L; }");
    insta::assert_snapshot!(output, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..5)
    5: Label(L, 6)
    6: Goto(L)
    ");
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
    insta::assert_snapshot!(output, @r"
    === TypeRegistry (Used TypeRefs) ===
    TypeRef(8): int
    TypeRef(24): int[*]
    TypeRef(22): void(int)
    TypeRef(25): void(int, ...)
    TypeRef(20): struct Point
    TypeRef(21): enum Color
    TypeRef(23): _Complex double
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
    insta::assert_snapshot!(output_parsed, @r#"
    1: TranslationUnit(decls=[3])
    3: FunctionDef(ParsedFunctionDefData { specifiers: [TypeSpecifier(Void)], declarator: Function { inner: Identifier("f", TypeQualifiers(0x0)), params: [], is_variadic: false }, body: 4 })
    4: CompoundStatement(stmts=[5, 7, 18])
    5: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("a", TypeQualifiers(0x0)), initializer: Some(6), span: SourceSpan(2199107141668) }] })
    6: LiteralInt(0, None)
    7: Declaration(ParsedDeclarationData { specifiers: [TypeSpecifier(Int)], init_declarators: [ParsedInitDeclarator { declarator: Identifier("b", TypeQualifiers(0x0)), initializer: Some(11), span: SourceSpan(2199459463227) }] })
    8: Ident(a)
    9: UnaryOp(AddrOf, 8)
    10: LiteralInt(0, None)
    11: AtomicOp(LoadN, args=[9, 10])
    12: Ident(a)
    13: CompoundStatement(stmts=[17])
    14: LiteralInt(1, None)
    15: LiteralInt(5, None)
    16: Break
    17: CaseRange(14, 15, 16)
    18: Switch(12, 13)
    "#);

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
    insta::assert_snapshot!(output_parser, @r"
    1: TranslationUnit(decls=2..2) (parser kind)
    2: Function(name=f, symbol=1, ty=TypeRef(base=20, class=Function, ptr=0, arr=None), params=[], body=4)
    3: LiteralString(f)
    4: CompoundStatement(stmts=5..6)
    5: VarDecl(name=a, ty=Int, storage=None)
    6: Switch(condition=8, body=9)
    7: LiteralInt(0, None)
    8: Ident(a)
    9: CompoundStatement(stmts=10..10)
    10: CaseRange(11, 12, 13)
    11: LiteralInt(1, None)
    12: LiteralInt(5, None)
    13: Break
    ");
}
