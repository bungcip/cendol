use crate::codegen::error::CodegenError;
use crate::semantic::typed_ast::{TypedExpr, TypedLValue};
use crate::parser::string_interner::StringId;
use cranelift_module::DataId;
use std::collections::HashMap;

use crate::types::{DeclId, TypeId};

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

use crate::semantic::typed_ast::TypedInitializer;

/// Evaluates a static initializer expression at compile time
use crate::codegen::translator::FunctionTranslator;
use crate::semantic::typed_ast::TypedDesignator;

