// Re-export types from pp_lexer module for backward compatibility
pub use crate::pp::pp_lexer::{PPLexer, PPToken, PPTokenFlags, PPTokenKind};

// Re-export preprocessor types for backward compatibility
pub use crate::pp::preprocessor::*;

mod interpreter;
mod pp_lexer;
mod preprocessor;

#[cfg(test)]
mod tests_pp_lexer;
#[cfg(test)]
mod tests_preprocessor;
