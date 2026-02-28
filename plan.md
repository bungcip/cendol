1. **Add `__typeof__` and `typeof` to lexer**
   - In `src/parser/lexer.rs`, add `Typeof` to `TokenKind`.
   - Update `keyword_map` in `src/parser/lexer.rs` to map `typeof`, `__typeof`, and `__typeof__` to `TokenKind::Typeof`.
   - Add `Typeof` to `is_type_specifier` method in `TokenKind`.

2. **Add `Typeof` to parsed types**
   - In `src/ast/parsed.rs`, add `Typeof(ParsedType)` and `TypeofExpr(ParsedNodeRef)` to `ParsedTypeSpecifier`. `typeof(expr)` returns a type, and `typeof(type)` is also allowed.

3. **Parse `typeof` in `src/parser/type_specifiers.rs`**
   - In `parse_type_specifier_or_qualifier_list`, handle `TokenKind::Typeof`.
   - It should expect an opening parenthesis `(`, followed by either an expression or a type name, and then a closing parenthesis `)`.

4. **Lower `typeof` in `src/semantic/lowering.rs`**
   - In `resolve_type_specifier`, handle `ParsedTypeSpecifier::Typeof` and `ParsedTypeSpecifier::TypeofExpr`.
   - For `Typeof(type)`, lower the parsed type.
   - For `TypeofExpr(expr)`, first analyze the expression to get its type, but without generating code/evaluating it. The type is `analyzer.visit_expr(expr)` and then `.get_type(expr)`.
   - Wait, if `typeof` takes an expression, it's evaluated statically (except for VM types which we might not support yet). So `typeof` should yield the type of the expression.

5. **Test**
   - Add a test checking `__typeof__(((void)0, x)) y = 5;`.
