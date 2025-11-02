use crate::codegen::error::CodegenError;
use crate::parser::ast::{TypedExpr, TypedLValue};
use crate::parser::string_interner::StringId;
use cranelift_codegen::binemit::Reloc;
use cranelift_module::{DataId, Linkage, Module};
use std::collections::HashMap;

/// Context needed for resolving addresses in static initializers
pub struct StaticInitContext {
    /// Mapping from variable names to their data IDs
    pub global_variables: HashMap<StringId, DataId>,
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
    expected_size: usize,
    context: &StaticInitContext,
) -> Result<Vec<u8>, CodegenError> {
    match expr {
        // Handle numeric literals
        TypedExpr::Number(num, _, _) => Ok(num.to_le_bytes().to_vec()),

        // Handle address-of expressions
        TypedExpr::AddressOf(lvalue, _, _) => evaluate_address_of(lvalue, expected_size, context),

        // Handle string literals - return placeholder for now (handled specially in mod.rs)
        TypedExpr::String(_s, _, _) => {
            Ok(vec![0xBDu8; expected_size]) // Placeholder for string literals
        }

        // Other expressions are not supported as static initializers
        _ => Err(CodegenError::InvalidStaticInitializer),
    }
}

/// Evaluates an address-of expression to get the address of a variable
pub fn evaluate_address_of(
    lvalue: &TypedLValue,
    expected_size: usize,
    context: &StaticInitContext,
) -> Result<Vec<u8>, CodegenError> {
    match lvalue {
        // For global variables, use relocations to get the actual address
        TypedLValue::Variable(_name, _, _) => {
            if let Some(_data_id) = context.global_variables.get(_name) {
                // For now, we'll create a relocation entry
                // In a real implementation, we'd use cranelift's relocation system
                // For now, store a placeholder that will be resolved by the linker
                // Use 0xDEADBEEF as a distinctive placeholder for debugging
                let mut placeholder = vec![0xEFu8; expected_size];
                if expected_size >= 8 {
                    // Store a distinctive pattern that we can identify later
                    placeholder[0..8].copy_from_slice(&0xDEADBEEFu64.to_le_bytes());
                }
                Ok(placeholder)
            } else {
                Err(CodegenError::InvalidStaticInitializer)
            }
        }

        // String literals - return placeholder address for now
        TypedLValue::String(_s, _, _) => {
            let mut placeholder = vec![0xEFu8; expected_size];
            if expected_size >= 8 {
                placeholder[0..8].copy_from_slice(&0xBEEFDEADu64.to_le_bytes());
            }
            Ok(placeholder)
        }

        // Other lvalue types are not supported as static initializers
        _ => Err(CodegenError::InvalidStaticInitializer),
    }
}
