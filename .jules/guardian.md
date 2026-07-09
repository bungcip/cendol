# Guardian's Journal

## 2024-05-18 - [Switch Jump To VLA Scope Span Anomaly]

Learning: When a `switch` jumps into the scope of a Variably Modified Type (VLA), the diagnostic span emitted by the MIR control flow analysis does not point to the `switch` keyword or the `case` label. Instead, it points to the first statement *after* the `case` label (e.g., the `return 0;` inside the case block). This is unintuitive because the jump occurs conceptually at the `case` or `switch` level.
Action: When testing `SemanticError::JumpIntoScopeVLA` for switch statements, the line and column assertions must precisely match this first statement's location until the semantic analyzer is refactored to anchor the error directly to the `case` or `switch` AST node. Do not hardcode line/col assertions blindly based on the keywords.
