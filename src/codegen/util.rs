use crate::codegen::error::CodegenError;
use crate::parser::ast::{TypedExpr, TypedLValue};
use crate::parser::string_interner::StringId;
use cranelift_module::DataId;
use std::collections::HashMap;

/// Context needed for resolving addresses in static initializers
pub struct StaticInitContext {
    /// Mapping from variable names to their data IDs
    pub global_variables: HashMap<StringId, DataId>,
}

/// The result of evaluating a static initializer.
#[derive(Debug)]
pub enum EvaluatedInitializer {
    /// A sequence of bytes.
    Bytes(Vec<u8>),
    /// A relocation to a symbol.
    Reloc { name: StringId, addend: i64 },
}

/// Unescapes string literals by processing escape sequences
pub fn unescape_string(s: &str) -> Vec<u8> {
    let mut unescaped = Vec::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            if let Some(next) = chars.next() {
                match next {
                    'n' => unescaped.push(b'\n'),
                    't' => unescaped.push(b'\t'),
                    'r' => unescaped.push(b'\r'),
                    '\\' => unescaped.push(b'\\'),
                    '"' => unescaped.push(b'"'),
                    '\'' => unescaped.push(b'\''),
                    '0' => unescaped.push(b'\0'),
                    _ => {
                        unescaped.push(b'\\');
                        unescaped.push(next as u8);
                    }
                }
            } else {
                unescaped.push(b'\\');
            }
        } else {
            unescaped.push(c as u8);
        }
    }
    unescaped
}

/// Evaluates a static initializer expression at compile time
pub fn evaluate_static_initializer(
    expr: &TypedExpr,
    _context: &StaticInitContext,
) -> Result<EvaluatedInitializer, CodegenError> {
    match expr {
        // Handle numeric literals
        TypedExpr::Number(num, _, _) => Ok(EvaluatedInitializer::Bytes(num.to_le_bytes().to_vec())),

        // Handle address-of expressions
        TypedExpr::AddressOf(lvalue, _, _) => match &**lvalue {
            TypedLValue::Variable(name, _, _) => Ok(EvaluatedInitializer::Reloc {
                name: *name,
                addend: 0,
            }),
            // Other lvalues like string literals will be handled separately.
            _ => Err(CodegenError::InvalidStaticInitializer),
        },

        // String literals are handled in `mod.rs`. Returning an error here to make it explicit.
        TypedExpr::String(_, _, _) => Err(CodegenError::InvalidStaticInitializer),

        // Other expressions are not supported as static initializers
        _ => Err(CodegenError::InvalidStaticInitializer),
    }
}
