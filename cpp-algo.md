# C Preprocessor Algorithm Implementation Guide

This document describes the exact algorithm used by a C preprocessor to handle macro expansion, based on the behavior observed in both `arocc` and `gcc`. This explanation focuses on the core mechanisms that prevent infinite recursion and ensure correct expansion order.

## Core Data Structures

### Token
```rust
struct Token {
    kind: TokenKind,
    text: String,
    source_location: SourceLocation,
    hideset: HashSet<String>,  // Set of macro names that should not expand this token
    expansion_locs: Vec<SourceLocation>,  // Track where this token came from
}
```

### Macro
```rust
enum Macro {
    Object {
        tokens: Vec<Token>,
    },
    Function {
        parameters: Vec<String>,
        tokens: Vec<Token>,
        is_variadic: bool,
    },
}
```

## Algorithm Overview

The preprocessor operates in phases:

1. **Tokenization**: Convert source text to tokens
2. **Directive Processing**: Handle #define, #ifdef, etc.
3. **Macro Expansion**: Expand macros with recursive rescanning
4. **Hideset Management**: Prevent infinite recursion

## Phase 1: Tokenization

```rust
fn tokenize(input: &str) -> Vec<Token> {
    // Convert input string to tokens
    // Handle identifiers, keywords, operators, strings, etc.
    // Each token gets initial empty hideset
}
```

## Phase 2: Directive Processing

```rust
fn process_directives(tokens: &mut Vec<Token>) {
    let mut i = 0;
    while i < tokens.len() {
        if tokens[i].kind == TokenKind::Hash &&
           i + 1 < tokens.len() &&
           tokens[i + 1].kind == TokenKind::Identifier(name) {

            match name.as_str() {
                "define" => {
                    let macro = parse_define(&tokens[i + 2..]);
                    // Store macro in macro table
                    tokens.drain(i..i+2); // Remove #define
                }
                // Handle other directives...
                _ => {}
            }
        }
        i += 1;
    }
}
```

## Phase 3: Macro Expansion (Core Algorithm)

The key insight is that macro expansion uses **recursive rescanning** with **hideset propagation**:

```rust
fn expand_macros(tokens: &mut Vec<Token>, macros: &HashMap<String, Macro>) {
    let mut i = 0;
    while i < tokens.len() {
        if let Some(macro_def) = should_expand_macro(&tokens[i], macros) {
            if let Some(expanded) = expand_single_macro(&tokens[i], &macro_def, macros) {
                // Replace the macro call with its expansion
                let expansion_start = i;
                let expansion_end = i + 1; // Will be updated based on actual replacement

                // Insert expanded tokens
                tokens.splice(expansion_start..expansion_end, expanded);

                // Restart scanning from beginning of expansion
                i = expansion_start;
                continue;
            }
        }
        i += 1;
    }
}

fn should_expand_macro(token: &Token, macros: &HashMap<String, Macro>) -> Option<&Macro> {
    if let TokenKind::Identifier(name) = &token.kind {
        // Check if this identifier is a macro
        if let Some(macro_def) = macros.get(name) {
            // Check hideset - if macro name is in hideset, don't expand
            if token.hideset.contains(name) {
                return None;
            }
            return Some(macro_def);
        }
    }
    None
}
```

## Hideset Propagation

The critical mechanism for preventing infinite recursion:

```rust
fn expand_single_macro(token: &Token, macro_def: &Macro, macros: &HashMap<String, Macro>) -> Option<Vec<Token>> {
    let macro_name = match &token.kind {
        TokenKind::Identifier(name) => name,
        _ => return None,
    };

    match macro_def {
        Macro::Object { tokens } => {
            let mut expanded = substitute_tokens(tokens, &[], &[]);
            // Add macro name to hideset of all expanded tokens
            for t in &mut expanded {
                t.hideset.insert(macro_name.clone());
            }
            Some(expanded)
        }
        Macro::Function { parameters, tokens, .. } => {
            // Parse arguments after the macro token
            let args = parse_macro_arguments(token, parameters)?;

            // Expand arguments first
            let expanded_args = expand_arguments(args, macros)?;

            // Substitute parameters in macro body
            let mut expanded = substitute_tokens(tokens, parameters, &expanded_args);

            // Calculate intersection of hidesets from macro token and closing paren
            let hideset = calculate_hideset_intersection(token)?;

            // Add macro name to hideset
            let mut final_hideset = hideset;
            final_hideset.insert(macro_name.clone());

            // Apply hideset to all expanded tokens
            for t in &mut expanded {
                t.hideset = final_hideset.clone();
            }

            Some(expanded)
        }
    }
}

fn calculate_hideset_intersection(macro_token: &Token) -> Result<HashSet<String>, Error> {
    // Find the closing parenthesis of this macro call
    // Return intersection of hidesets from macro token and closing paren
    // This ensures proper hideset propagation across the entire macro call
}
```

## Token Pasting (## Operator)

```rust
fn handle_token_pasting(left: &Token, right: &Token) -> Token {
    let left_text = get_token_text(left);
    let right_text = get_token_text(right);

    // Concatenate the text
    let concatenated = format!("{}{}", left_text, right_text);

    // Re-tokenize the result
    let pasted_token = tokenize_single(&concatenated);

    // Hideset is intersection of left and right tokens' hidesets
    pasted_token.hideset = left.hideset.intersection(&right.hideset).collect();

    pasted_token
}
```

## Stringizing (# Operator)

```rust
fn handle_stringizing(tokens: &[Token]) -> Token {
    let mut result = String::from("\"");

    for token in tokens {
        let text = get_token_text(token);
        // Escape special characters
        let escaped = escape_for_string(text);
        result.push_str(&escaped);
    }

    result.push('"');

    Token {
        kind: TokenKind::String,
        text: result,
        // Other fields...
    }
}
```

## Rescanning Mechanism

The key to correct expansion order:

```rust
fn rescan_from_position(tokens: &mut Vec<Token>, start_pos: usize, macros: &HashMap<String, Macro>) {
    let mut i = start_pos;
    while i < tokens.len() {
        if let Some(macro_def) = should_expand_macro(&tokens[i], macros) {
            if let Some(expanded) = expand_single_macro(&tokens[i], &macro_def, macros) {
                // Replace tokens[i] with expanded tokens
                let old_len = 1;
                let new_tokens = expanded.len();

                tokens.splice(i..i+old_len, expanded);

                // Continue rescanning from current position
                // Don't increment i, let the loop handle it
                continue;
            }
        }
        i += 1;
    }
}
```

## Complete Expansion Algorithm

```rust
fn preprocess(input: &str) -> Vec<Token> {
    let mut tokens = tokenize(input);
    let mut macros = HashMap::new();

    // Phase 1: Process directives and collect macro definitions
    process_directives(&mut tokens, &mut macros);

    // Phase 2: Expand all macros with full rescanning
    expand_all_macros(&mut tokens, &macros);

    tokens
}

fn expand_all_macros(tokens: &mut Vec<Token>, macros: &HashMap<String, Macro>) {
    let mut changed = true;
    let mut iterations = 0;
    const MAX_ITERATIONS: usize = 10000; // Prevent infinite loops

    while changed && iterations < MAX_ITERATIONS {
        changed = false;
        iterations += 1;

        let mut i = 0;
        while i < tokens.len() {
            if let Some(macro_def) = should_expand_macro(&tokens[i], macros) {
                if let Some(expanded) = expand_single_macro(&tokens[i], &macro_def, macros) {
                    // Replace the macro invocation
                    tokens.splice(i..i+1, expanded);

                    // Mark that we made changes
                    changed = true;

                    // Restart from beginning of replacement
                    i = 0;
                    continue;
                }
            }
            i += 1;
        }
    }

    if iterations >= MAX_ITERATIONS {
        eprintln!("Warning: Possible infinite macro expansion detected");
    }
}
```

## Key Points for Correct Implementation

1. **Hideset Inheritance**: When expanding a macro, all resulting tokens inherit the hideset from the macro invocation point, with the macro name added.

2. **Rescanning**: After each macro expansion, restart scanning from the beginning of the expanded tokens.

3. **Argument Expansion**: Function macro arguments are fully expanded before substitution, except when used with # or ## operators.

4. **Token Pasting**: The ## operator creates new tokens by concatenation and re-tokenization.

5. **Order of Operations**: Stringizing (#) happens before token pasting (##) in the same macro expansion.

6. **Hideset Intersection**: For function macros, the hideset is the intersection of the hidesets from the macro token and the closing parenthesis.

## Detailed Example: Step-by-Step Expansion

Let's trace through your exact example to show how the algorithm works:

**Initial Macros:**
```c
#define F(acc)          F_PROGRESS(acc)
#define F_PROGRESS(acc) CONTINUE(F)(acc##X)
#define F_HOOK()        F
#define UNROLL(...)     __VA_ARGS__
#define DEFER(op)       op EMPTY
#define EMPTY
#define CONTINUE(k)     DEFER(k##_HOOK)()
```

**Step 1: UNROLL(F_PROGRESS(X))**
- `UNROLL` is a variadic macro, expands to its argument: `F_PROGRESS(X)`
- Hideset of result: `{UNROLL}`
- Token stream: `F_PROGRESS ( X )`

**Step 2: F_PROGRESS(X)**
- `F_PROGRESS` is a function macro, parameter `acc` = `X`
- Body: `CONTINUE(F)(acc##X)` → `CONTINUE(F)(XX)` (after pasting)
- Hideset of result: `{UNROLL, F_PROGRESS}`
- Token stream: `CONTINUE ( F ) ( XX )`

**Step 3: CONTINUE(F)(XX)**
- `CONTINUE` is a function macro, parameter `k` = `F`
- Body: `DEFER(k##_HOOK)()` → `DEFER(F_HOOK)()` (after pasting)
- Hideset of result: `{UNROLL, F_PROGRESS, CONTINUE}`
- Token stream: `DEFER ( F_HOOK ) ( ) ( XX )`

**Step 4: DEFER(F_HOOK)()(XX)**
- `DEFER` is a function macro, parameter `op` = `F_HOOK`
- Body: `op EMPTY` → `F_HOOK EMPTY`
- Hideset of result: `{UNROLL, F_PROGRESS, CONTINUE, DEFER}`
- Token stream: `F_HOOK EMPTY ( ) ( XX )`

**Step 5: F_HOOK EMPTY()(XX)**
- `EMPTY` is an object macro, expands to nothing
- Token stream: `F_HOOK ( ) ( XX )`
- Rescanning: `F_HOOK` followed by `(` triggers function macro expansion

**Step 6: F_HOOK()(XX)**
- `F_HOOK` is a function macro, expands to `F`
- **Critical**: The new `F` token inherits hideset `{UNROLL, F_PROGRESS, CONTINUE, DEFER, F_HOOK}`
- Token stream: `F ( XX )`

**Step 7: F(XX)**
- `F` is a function macro, parameter `acc` = `XX`
- Body: `F_PROGRESS(acc)` → `F_PROGRESS(XX)`
- Hideset of result: `{UNROLL, F_PROGRESS, CONTINUE, DEFER, F_HOOK, F}`
- Token stream: `F_PROGRESS ( XX )`

**Step 8: F_PROGRESS(XX)**
- `F_PROGRESS` is a function macro, parameter `acc` = `XX`
- Body: `CONTINUE(F)(acc##X)` → `CONTINUE(F)(XXX)` (after pasting)
- Hideset of result: `{UNROLL, F_PROGRESS, CONTINUE, DEFER, F_HOOK, F, F_PROGRESS}`
- Token stream: `CONTINUE ( F ) ( XXX )`

**Step 9: CONTINUE(F)(XXX)**
- `CONTINUE` is a function macro, parameter `k` = `F`
- Body: `DEFER(k##_HOOK)()` → `DEFER(F_HOOK)()`
- Hideset of result: `{UNROLL, F_PROGRESS, CONTINUE, DEFER, F_HOOK, F, F_PROGRESS, CONTINUE}`
- Token stream: `DEFER ( F_HOOK ) ( ) ( XXX )`

**Step 10: DEFER(F_HOOK)()(XXX)**
- `DEFER` is a function macro, parameter `op` = `F_HOOK`
- Body: `op EMPTY` → `F_HOOK EMPTY`
- Hideset of result: `{UNROLL, F_PROGRESS, CONTINUE, DEFER, F_HOOK, F, F_PROGRESS, CONTINUE, DEFER}`
- Token stream: `F_HOOK EMPTY ( ) ( XXX )`

**Step 11: F_HOOK EMPTY()(XXX)**
- `EMPTY` expands to nothing
- Token stream: `F_HOOK ( ) ( XXX )`
- **Critical Check**: The `F_HOOK` token has hideset `{..., F_HOOK, ...}`
- Since `F_HOOK` is in its own hideset, expansion stops here

**Final Result:** `F_HOOK ()(XXX)`

## Why This Algorithm is Correct

1. **Hideset Prevents Recursion**: Each macro name is added to the hideset of its expansion, preventing simple recursion like `#define A A`.

2. **Cross-Macro Hideset**: The hideset carries across multiple macro expansions, so when `F_HOOK` creates `F`, and `F` creates `F_PROGRESS`, the hideset accumulates all the macro names that led to the current token.

3. **Rescanning Enables Nesting**: After each expansion, the algorithm rescans from the beginning of the expanded tokens, allowing macros within macro expansions to be properly handled.

4. **Token Pasting Creates New Tokens**: The `##` operator creates genuinely new tokens (like `XX`, `XXX`) that don't carry the hideset baggage of their component parts.

This algorithm correctly handles the example provided:
- `UNROLL(F_PROGRESS(X))` → `F_PROGRESS(X)` → `CONTINUE(F)(XX)` → `DEFER(F_HOOK)()(XX)` → `F_HOOK EMPTY()(XX)` → `F_HOOK()(XX)` → `F(XX)` → `F_PROGRESS(XX)` → `CONTINUE(F)(XXX)` → `DEFER(F_HOOK)()(XXX)` → `F_HOOK EMPTY()(XXX)` → `F_HOOK()(XXX)`

The expansion stops at `F_HOOK ()(XXX)` because `F_HOOK` appears in its own hideset, preventing further expansion.
