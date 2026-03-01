The problem:
The C11 standard says: "If an identifier designates two different entities in the same name space, the scopes might overlap. If so, the scope of one entity... will be a strict subset of the scope of the other entity..."
This means we can have a `typedef int my_type;` in the outer scope, and then `float my_type = 1.0f;` in an inner scope.
Currently, our parser maintains a global set of typedef names (`TypeDefContext::typedef_names`) and it does NOT track scopes.
Once a name is added to the `typedef_names` set via `add_typedef`, it will forever be treated as a type name by the parser (`is_type_name`).

So in `int main(void) { float my_type = 1.0f; ... }`:
`my_type` is seen as a type name because it was added to `typedef_names`.
When we have `float my_type`, it might be incorrectly parsed, but it seems to parse as a declaration of `my_type`. However, when we do `sizeof(my_type)`, since `my_type` is in `typedef_names`, it is parsed as `SizeOfType` instead of `SizeOfExpr`.
Wait, in `float my_type = 1.0f;`, the parser parsed it as `float my_type`.
But because `my_type` was already registered as a typedef name, the parser thinks `my_type` is a type.
Let's see the AST dump for `test4.c` where we just do `sizeof(my_type)` after `int my_type = 1;`:
`SizeOfType(ParsedType { base: 1, declarator: 1, qualifiers: TypeQualifiers(0x0) })`

Ah, `my_type` is parsed as a type name instead of an expression!
This happens because `is_type_name_start_token` returns true for `my_type`.
So `sizeof(my_type)` is parsed as `sizeof(<type>)` instead of `sizeof(<expr>)`.
The semantic lowering phase receives `SizeOfType("my_type")`. It then tries to lower the type `"my_type"`. But the semantic lowering *does* have a proper symbol table with scopes! So when it looks up `"my_type"` as a type, it finds the variable `"my_type"` instead of the typedef (because the variable shadows the typedef in the inner scope), and it fails to convert it to a type, probably returning an incomplete type or error. Wait, the error is: `expected a typedef name, found my_type`. No, the error in `contoh.c` was `Invalid application of 'sizeof' to an incomplete type 'void'`. `convert_to_qual_type` must have failed, returned `void` (type_error), and then `sizeof(void)` is an error.

To fix this properly, `TypeDefContext` in the parser needs to support scopes.
Wait, C parsers generally handle this using "The Lexer Hack" or by having the parser maintain a scoped symbol table *just* for type names.
Since we already have `TypeDefContext`, we can just change `typedef_names` from `HashSet<NameId>` to a scoped structure:
```rust
struct TypeDefContext {
    scopes: Vec<HashSet<NameId>>,
}
```
Wait, no. The parser does not currently track scopes. `parse_compound_statement` does not push/pop scopes.
Wait! Does the parser need to track scopes? Yes, because of shadowing.
If the parser tracks scopes, when we do `float my_type = 1.0f;`, we are declaring `my_type` as a variable in the current scope.
We need to *remove* `my_type` from being a typedef in the current scope, or just record it as a "non-typedef" so that it shadows the outer typedef.
So a scoped table would map `NameId -> bool` (is it a typedef or not?).
When we see a declaration of a typedef `typedef int my_type;`, we add `my_type -> true` to the current scope.
When we see a declaration of a variable/function `float my_type;`, we add `my_type -> false` to the current scope.
When we look up `my_type` in `is_type_name()`, we search from the innermost scope outwards. If we find `true`, it's a type name. If we find `false`, it's not. If we don't find it, it's not.

To do this, the parser needs to:
1. Push a scope when entering a block (`{`), function parameter list, etc.
2. Pop a scope when leaving.
3. Record all declarations in the current scope.

Wait, the parser already parses declarations. But does it know when a new scope starts?
In C, scopes are created by:
- Translation unit (global scope)
- Function definitions (block scope for body, plus parameter scope)
- Compound statements (block scope)
- Prototype scopes (function declarations)

Let's check if we can easily add scope push/pop to the parser.
In `Parser`, we could add `push_scope()` and `pop_scope()`.
Wait, let's look at `src/parser/declarations.rs`.
```rust
    let mut init_declarators = ThinVec::new();
    loop {
        // ...
        let declarator = super::declarator::parse_declarator(trx.parser)?;

        let is_typedef = specifiers.iter().any(|s| matches!(s, ParsedDeclSpecifier::StorageClass(StorageClass::Typedef)));
        if let Some(name) = trx.parser.get_declarator_name(&declarator) {
            if is_typedef {
                trx.parser.add_typedef(name);
            } else {
                trx.parser.add_non_typedef(name);
            }
        }
        // ...
```
And similarly for function parameters, we should add non-typedef.
What about function definitions? The function name itself is a non-typedef.
Wait, `parse_declarator` parses identifiers. Is `get_declarator_name` enough? Yes, for variable and function declarations.

Let's modify `TypeDefContext` in `src/parser.rs`:
```rust
#[derive(Debug)]
pub(crate) struct TypeDefContext {
    /// Stack of scopes, each containing a map from NameId to a boolean indicating if it's a typedef
    scopes: Vec<HashMap<NameId, bool>>,
}

impl TypeDefContext {
    pub(crate) fn new() -> Self {
        let mut globals = HashMap::new();
        globals.insert(NameId::new("int8_t"), true);
        // ...
        TypeDefContext { scopes: vec![globals] }
    }

    pub(crate) fn is_type_name(&self, symbol: NameId) -> bool {
        for scope in self.scopes.iter().rev() {
            if let Some(&is_typedef) = scope.get(&symbol) {
                return is_typedef;
            }
        }
        false
    }

    pub(crate) fn add_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().insert(symbol, true);
    }

    pub(crate) fn add_non_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().insert(symbol, false);
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }
}
```

Wait, what about `ParserState`?
```rust
#[derive(Debug, Clone)]
pub(crate) struct ParserState {
    current_idx: usize,
    diag_len: usize,
    // We also need to save/restore the scope state if we do backtracking!
    type_context_depth: usize,
    type_context_last_scope_len: usize, // since we only add to the last scope, we can just truncate
}
```
Wait, backtracking across scopes is not very common, but `parse_compound_statement` does not use `save_state`/`restore_state`. Wait, `ParserTransaction` does!
`ParserTransaction` is used heavily in `parse_declaration` to rollback if parsing fails.
If a transaction adds a typedef/non-typedef, and then rolls back, the `typedef_names` set must be restored.
Currently `ParserTransaction` just restores `current_idx` and `diag_len`. It does NOT restore `typedef_names`.
But if `typedef_names` is modified during `parse_declaration`, it's done *after* `parse_declarator`. The transaction usually rolls back *before* that (e.g. if specifiers don't match). But if a declaration parses successfully and then we roll back for some reason... actually, `parse_declaration` only modifies `typedef_names` *before* committing? No, `trx.parser.add_typedef(name);` happens before `trx.commit()`. But the `loop` goes through init-declarators.
If an init-declarator fails, the transaction is dropped, rolling back. So `typedef_names` SHOULD be restored.
We can just `clone()` the `scopes` in `save_state` for simplicity, or just `clone` the last scope, since a transaction only adds to the current scope.
Wait, let's look at how Clang does this. Clang's parser has a `Sema` that tracks scopes and variables, so it can correctly disambiguate type names from variable names on the fly. We don't have a semantic checker interwoven with the parser. We do our own scoped disambiguation in `TypeDefContext`.
If we change `TypeDefContext` to use Scopes, we need:
1. `push_scope()`
2. `pop_scope()`
3. `add_typedef(name)` -> `scopes.last_mut().insert(name, true)`
4. `add_non_typedef(name)` -> `scopes.last_mut().insert(name, false)`
5. `is_type_name(name)` -> search scopes from last to first. If found `true`, return true. If found `false`, return false. If not found, return false.

Where do we push and pop scopes?
- Entering a translation unit (done inherently because we start with 1 scope)
- Entering a compound statement (`{`)
  - In `parse_compound_statement`, before parsing items, we `parser.type_context.push_scope()`. After parsing items, we `parser.type_context.pop_scope()`.
- Entering a function definition
  - The parameter list has its own scope! If a parameter shadows a typedef, it must not be parsed as a typedef in the body.
  - So `parse_function_definition` or `parse_declarator` might need to push a scope?
  - In C, function parameters are in the same scope as the function body's outermost block. But we parse parameters during `parse_declarator`, and then we parse the compound statement which pushes its own scope. If we do that, we have two scopes. That's fine for the parser's type disambiguation as long as they are nested.
  - Wait, if `parse_declarator` parses parameters, we need those parameter names to be added as `non-typedef`!
  - But `parse_declarator` doesn't currently add parameter names to the parser state. Let's see how `parse_declarator` handles parameter names.
Wait, `parse_function_parameters` parses parameters. But it does not add parameter names to the typedef context. If a parameter shadows a typedef, the parser would still think the typedef is a type! That is actually a bug.
We must fix it as part of introducing scoped `TypeDefContext`.
Wait, in `parse_function_parameters`, after parsing the declarator, if `declarator` has a name, we should add it as `non-typedef`.
But when do we push the parameter scope?
We can push a scope at the beginning of `parse_function_parameters`... but wait! If we push a scope there, when does it get popped?
If it's just a function *declaration* `void f(int my_type);`, the scope is popped at the end of `parse_function_parameters`?
But if it's a function *definition* `void f(int my_type) { ... }`, the parameters must remain in scope for the body!
Ah, so `parse_function_parameters` is called *inside* `parse_declarator`.
If we push a scope in `parse_declarator` when encountering `(`, we would need to know whether to pop it.
Wait! C's grammar says `declarator` can be parsed inside expressions (casts, sizeof), inside parameter lists, inside struct declarations...
And parameter scopes are tricky in C.
If `TypeDefContext` is only for disambiguating type names, maybe we don't need strict block scopes for *everything*, just a way to shadow typenames.
Actually, pushing/popping scopes at `{` and `}` and inside `parse_function_definition` is enough.
But wait, how does `parse_declarator` know we are in a function definition? It doesn't.
In Clang, the parser tells the semantic analyzer when a scope opens/closes.
For our `TypeDefContext`, it's just a parser hack.
If we add `push_scope` / `pop_scope` for `{` and `}` (in `parse_compound_statement`), that solves block-scope shadowing of typedefs.
But what about parameter scopes?
If a parameter name shadows a typedef, we need the body to see it as a non-typedef.
Since parameter names are parsed in `parse_function_parameters`, we can't easily keep their scope open *only* if it's a definition.
Wait! We could just rely on `{` and `}`? No, because the parameter is defined *before* `{`.
If we declare `int f(int my_type) { float f = my_type; }`, `my_type` must be an expression, not a type.
If we push a scope before `{`, it won't have the parameters.
If we push a scope in `parse_function_definition` *before* `parse_declarator`, then the parameter names will be added to that scope. Then we parse the compound statement. Then we pop the scope.
But wait, `parse_function_definition` first calls `parse_declarator`. It doesn't know it's a function definition until it sees `{`!
Actually, `parse_declaration` and `parse_function_definition` both start by parsing specifiers and declarator. They only diverge based on whether `{` follows. (Well, our `parse_translation_unit` uses `parse_declaration`, and if it fails, falls back to `parse_function_definition`.)
If `parse_declaration` fails, `parse_function_definition` runs. It parses specifiers and declarator, then body.
If we just push a scope in `parse_function_definition`? No, because when `parse_declaration` parses `int f(int my_type);`, `my_type` is added as a non-typedef to the *current* global scope! That would pollute the global scope!
So `parse_function_parameters` MUST push a scope and then POP it.
But if it pops it, how does `parse_function_definition` get the parameters?
It doesn't need to! Wait, if it pops the scope, then the parameter names are lost. When we enter the compound statement, `my_type` will be seen as a typedef again. That's a bug!

How to fix this elegantly?
Maybe `parse_function_parameters` doesn't push a scope, but instead returns the list of parameter names.
Then `parse_function_definition` can push a scope, and *re-add* the parameter names to the new scope as non-typedefs, before parsing the body!
Yes! `get_declarator_name` can extract the names from the parsed parameters.
And `parse_compound_statement` pushes a scope, parses items, pops a scope.
Wait, what if we just push a scope at the start of `parse_compound_statement`, and pop at the end?
Then any variables declared inside the block will be removed when the block ends.
For function parameters, `parse_function_definition` can extract parameter names from `declarator`, then push a scope, add parameter names, parse compound statement, and pop scope.
BUT wait! `parse_compound_statement` parses `{ ... }`. It would push *another* scope. That's fine. The parameter scope will be outside the block scope.
So `parse_function_definition`:
```rust
    let declarator = super::declarator::parse_declarator(parser)?;

    // Push scope for parameters
    parser.type_context.push_scope();
    let mut param_names = Vec::new();
    if let ParsedDeclarator::Function { params, .. } = get_innermost_declarator(&declarator) {
        for param in params {
            if let Some(name) = get_declarator_name(&param.declarator) {
                parser.type_context.add_non_typedef(name);
            }
        }
    }

    let (body, body_end_loc) = super::statements::parse_compound_statement(parser)?;

    // Pop parameter scope
    parser.type_context.pop_scope();
```
Is `get_innermost_declarator` needed? Yes, because `declarator` can be a pointer to a function: `int *f(int a)`.
Wait, in `ParsedDeclarator`, `Function` contains `inner` (which is the function name, e.g. `Identifier("f")`). Wait, no!
`int *f(int a)` is parsed as:
`Function { inner: Identifier("f"), params: [...] }` wrapped in `Pointer`? No.
Let's check how `Declarator` is structured.
```
ParsedDeclarator::Pointer(_, inner)
```
Wait, `parse_declarator` returns `ParsedDeclarator`.
For `int *f(int a)`, `parse_declarator` returns `Pointer(..., Function { inner: Identifier("f"), params: [...] })`.
Wait, no, the function returns a pointer, so it's a function returning a pointer.
`f` is a function. So the AST is `Function { inner: Pointer(..., Identifier("f")), ... }`?
Let's see: `int *f(int a)` -> `int` is specifier. `*f(int a)` is declarator.
`*f(int a)` has leading `*`, then `f(int a)`.
`parse_declarator` parses `*`, then `f(int a)`.
`f(int a)` is `Function { inner: Identifier("f") }`.
So `reconstruct_declarator_chain` makes it `Pointer(..., Function { inner: Identifier("f") })`?
No, `Pointer` wraps the base. The base is `Function { ... }`.
So it returns `Pointer(..., Function { ... })`?
Let's look at `reconstruct_declarator_chain`.
Wait, `parse_function_parameters` doesn't know if the function is just declared or defined. But it parses the parameter names.
When we call `parse_declarator`, it parses all function parameters.
If we can extract the function parameters after `parse_declarator`, we can push a scope and add them.
Wait! `get_declarator_name` recurses down to the inner identifier.
We can write a function `get_declarator_params(declarator)` that returns the `params` of the innermost function declarator.
```rust
pub(crate) fn get_declarator_params(declarator: &ParsedDeclarator) -> Option<&ThinVec<ParsedParamData>> {
    match declarator {
        ParsedDeclarator::Function { params, .. } => Some(params),
        ParsedDeclarator::Pointer(_, Some(inner)) => get_declarator_params(inner),
        ParsedDeclarator::Array(inner, _) => get_declarator_params(inner),
        _ => None,
    }
}
```
Wait, what if it's `void (*f(int a))(float b)`?
Then `get_declarator_params` should return `int a`. Because `f` is a function returning a pointer to a function.
The outermost `Function` declarator around the identifier?
Wait, if `f(int a)` is parsed:
`parse_trailing_declarators` handles `(int a)` and wraps `Identifier("f")` in `Function`.
Then `parse_abstract_declarator` for the outer part wraps that in `Pointer`.
Then the trailing `(float b)` wraps the `Pointer` in `Function`.
So the declarator is `Function(Pointer(Function(Identifier("f"), int a)), float b)`.
Wait, if it's `void (*f(int a))(float b)`, the innermost `Function` around `Identifier("f")` is the parameter list of `f`!
So we just need to search for the *first* `Function` declarator that we encounter when walking up from the identifier? No, when walking *down* the AST from the root of the declarator, it's the *last* `Function` declarator before the identifier.
Actually, if we just traverse and find the `Function` that directly encloses the `Identifier` (or is the closest to it).
```rust
pub(crate) fn get_declarator_params(declarator: &ParsedDeclarator) -> Option<&ThinVec<ParsedParamData>> {
    match declarator {
        ParsedDeclarator::Function { inner, params, .. } => {
            if let Some(inner_params) = get_declarator_params(inner) {
                Some(inner_params)
            } else {
                Some(params)
            }
        },
        ParsedDeclarator::Pointer(_, Some(inner)) => get_declarator_params(inner),
        ParsedDeclarator::Array(inner, _) => get_declarator_params(inner),
        _ => None,
    }
}
```
Yes, this will recurse down. If a deeper `Function` has params, it returns them. Otherwise it returns its own `params`.
So for `Function(Pointer(Function(Identifier("f"), params1)), params2)`, it visits the outer `Function`, recurses to `Pointer`, recurses to inner `Function`, recurses to `Identifier` (returns `None`), so inner `Function` returns `Some(params1)`. Outer `Function` gets `Some(params1)` and returns it.
This gets the exact parameters of the function being defined!

So in `parse_function_definition`:
```rust
    let declarator = super::declarator::parse_declarator(parser)?;

    // Start function parameter scope
    parser.type_context.push_scope();

    if let Some(params) = super::declarator::get_declarator_params(&declarator) {
        for param in params {
            if let Some(name) = super::declarator::get_declarator_name(&param.declarator) {
                parser.type_context.add_non_typedef(name);
            }
        }
    }

    let (body, body_end_loc) = super::statements::parse_compound_statement(parser)?;

    // Pop parameter scope
    parser.type_context.pop_scope();
```
And in `parse_compound_statement`:
```rust
    parser.type_context.push_scope();
    let mut items = Vec::new();
    // parse items
    parser.type_context.pop_scope();
```
And one edge case: what if `parse_compound_statement` fails with an error? We should ensure the scope is popped!
Since we return `Result`, we might early return!
```rust
    parser.type_context.push_scope();
    let res = parse_compound_statement_impl(parser);
    parser.type_context.pop_scope();
    res
```
Or use a struct with `Drop` to automatically pop the scope!
```rust
struct ScopeGuard<'a, 'arena, 'src> {
    parser: &'a mut Parser<'arena, 'src>,
}
impl<'a, 'arena, 'src> ScopeGuard<'a, 'arena, 'src> {
    fn new(parser: &'a mut Parser<'arena, 'src>) -> Self {
        parser.type_context.push_scope();
        Self { parser }
    }
}
impl<'a, 'arena, 'src> Drop for ScopeGuard<'a, 'arena, 'src> {
    fn drop(&mut self) {
        self.parser.type_context.pop_scope();
    }
}
```
This is much safer against early returns!
Wait, what if `parser.start_transaction()` saves state, then we parse a declaration in a nested scope, and then the transaction rolls back?
The transaction only saves `current_idx` and `diag_len`.
It does NOT save `type_context_depth` or `typedef_names`.
If we modify the *current* scope (adding typedef or non-typedef), and then roll back, the typedef remains in the current scope!
Is this a problem?
Yes. If we do `int my_type = 1, my_type2 = ...;` and it fails halfway, we rollback.
But wait! `parse_declaration` only modifies `type_context` *before* the loop continues.
Actually, let's look at `ParserTransaction`:
```rust
impl<'a, 'arena, 'src> ParserTransaction<'a, 'arena, 'src> {
    pub(crate) fn new(parser: &'a mut Parser<'arena, 'src>) -> Self {
        let state = parser.save_state();
        Self { parser, state, committed: false }
    }
    pub(crate) fn commit(mut self) {
        self.committed = true;
    }
}
impl<'a, 'arena, 'src> Drop for ParserTransaction<'a, 'arena, 'src> {
    fn drop(&mut self) {
        if !self.committed {
            self.parser.restore_state(self.state.clone());
        }
    }
}
```
If we change `ParserState` to include `type_context_last_scope_len`, we can restore it!
```rust
#[derive(Debug, Clone)]
pub(crate) struct ParserState {
    current_idx: usize,
    diag_len: usize,
    type_context_last_scope_len: usize,
}
```
In `save_state`:
```rust
    fn save_state(&self) -> ParserState {
        ParserState {
            current_idx: self.current_idx,
            diag_len: self.diag.diagnostics.len(),
            type_context_last_scope_len: self.type_context.scopes.last().map(|s| s.len()).unwrap_or(0),
        }
    }
```
But `HashMap` is not easily truncated.
Instead of `Vec<HashMap<NameId, bool>>`, we can use `Vec<Vec<(NameId, bool)>>` for scopes!
Then `len()` is just the `Vec::len`, and we can `truncate()` it on restore!
Since a block scope will typically have fewer than a dozen variables, linear search is perfectly fine and probably faster than `HashMap`.
```rust
#[derive(Debug)]
pub(crate) struct TypeDefContext {
    scopes: Vec<Vec<(NameId, bool)>>,
}

impl TypeDefContext {
    pub(crate) fn new() -> Self {
        let mut globals = Vec::new();
        globals.push((NameId::new("int8_t"), true));
        // ...
        TypeDefContext { scopes: vec![globals] }
    }

    pub(crate) fn is_type_name(&self, symbol: NameId) -> bool {
        for scope in self.scopes.iter().rev() {
            for &(name, is_typedef) in scope.iter().rev() {
                if name == symbol {
                    return is_typedef;
                }
            }
        }
        false
    }

    pub(crate) fn add_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().push((symbol, true));
    }

    pub(crate) fn add_non_typedef(&mut self, symbol: NameId) {
        self.scopes.last_mut().unwrap().push((symbol, false));
    }

    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(Vec::new());
    }

    pub(crate) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(crate) fn get_last_scope_len(&self) -> usize {
        self.scopes.last().map(|s| s.len()).unwrap_or(0)
    }

    pub(crate) fn truncate_last_scope(&mut self, len: usize) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.truncate(len);
        }
    }
}
```
This is brilliant! It perfectly supports transactional rollbacks.
Plan Summary:
1. Update `TypeDefContext` in `src/parser.rs` to support scopes and use a `Vec<Vec<(NameId, bool)>>` structure for scoping. Add `push_scope()`, `pop_scope()`, `add_non_typedef()`, `get_last_scope_len()`, and `truncate_last_scope()`.
2. Update `ParserState` to include `type_context_last_scope_len`, and update `save_state` and `restore_state` to truncate the innermost scope correctly.
3. In `src/parser/statements.rs`, add a `ScopeGuard` structure and use it in `parse_compound_statement` to ensure scopes are cleanly pushed and popped even if errors happen.
4. In `src/parser/declarations.rs`:
   - In `parse_declaration`, when an `init_declarator` is processed, add the declarator's name as a typedef or non-typedef depending on `StorageClass::Typedef`.
   - In `parse_function_definition`, use `ScopeGuard` to push a scope, extract the innermost function parameters via `get_declarator_params`, add parameter names as non-typedefs, and then parse the body.
5. In `src/parser/declarator.rs`, add `pub(crate) fn get_declarator_params`.
6. Finally, execute the pre-commit script.

Reviewing the logic for `parse_function_definition`:
```rust
    let declarator = super::declarator::parse_declarator(parser)?;

    // push scope for params, add params
    // parse body
    // pop scope
```
Wait, `parse_function_definition` doesn't use `ScopeGuard` because `ScopeGuard` takes an exclusive reference to parser.
```rust
struct ScopeGuard<'a, 'arena, 'src> {
    parser: &'a mut Parser<'arena, 'src>,
}
```
If we use `ScopeGuard`, we can't borrow `parser` out of it!
```rust
    let _guard = ScopeGuard::new(parser);
    // wait, I can't do parse_compound_statement(parser) now because parser is borrowed by _guard!
```
Ah! Rust borrow checker will complain.
Instead of `ScopeGuard`, we can just manually push and pop, and use a standard Rust `defer` or just pop at the end. Since `parse_compound_statement` handles errors by reporting them and continuing, we can just do:
```rust
    parser.type_context.push_scope();
    let res = parse_compound_statement_impl(parser);
    parser.type_context.pop_scope();
```
Actually, we can just do:
```rust
pub(crate) fn parse_compound_statement(parser: &mut Parser) -> Result<(ParsedNodeRef, SourceLoc), ParseError> {
    parser.type_context.push_scope();
    let res = parse_compound_statement_inner(parser);
    parser.type_context.pop_scope();
    res
}

fn parse_compound_statement_inner(parser: &mut Parser) -> Result<(ParsedNodeRef, SourceLoc), ParseError> {
   ...
}
```
For `parse_function_definition`:
```rust
    parser.type_context.push_scope();
    if let Some(params) = super::declarator::get_declarator_params(&declarator) {
        for param in params {
            if let Some(name) = super::declarator::get_declarator_name(&param.declarator) {
                parser.type_context.add_non_typedef(name);
            }
        }
    }
    let res = super::statements::parse_compound_statement(parser);
    parser.type_context.pop_scope();
    let (body, body_end_loc) = res?;
```
Wait! `parse_compound_statement` pushes ITS OWN scope. This means function parameters will be in one scope, and the body in another nested scope. That is PERFECTLY fine for type disambiguation.
Wait, what if `res` is an `Err`?
The `pop_scope` happens before the `?`! So it's safe.
