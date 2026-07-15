use crate::ast::literal::StrPrefix;
use crate::semantic::BuiltinType;

pub struct StringLiteralValue {
    pub builtin_type: BuiltinType,
    pub values: Vec<i64>, // Store as i64 to handle all types
    pub size: usize,
}

/// Metadata about a string literal without its full value buffer.
/// Bolt ⚡: This allows phases like semantic analysis and lowering to resolve
/// literal types and sizes without incurring the heap allocation cost of a Vec<i64>.
pub(crate) fn get_string_builtin_type(prefix: StrPrefix) -> BuiltinType {
    match prefix {
        StrPrefix::Wide => BuiltinType::Int,
        StrPrefix::Utf16 => BuiltinType::UShort,
        StrPrefix::Utf32 => BuiltinType::UInt,
        StrPrefix::Utf8 => BuiltinType::UChar,
        StrPrefix::None => BuiltinType::Char,
    }
}

pub use crate::ast::literal::get_string_literal_size;

pub(crate) fn lower_string_literal(content: &str, prefix: StrPrefix) -> StringLiteralValue {
    let builtin_type = get_string_builtin_type(prefix);
    let size = get_string_literal_size(content, prefix);

    // Bolt ⚡: Use with_capacity to ensure a single allocation.
    let mut values = Vec::with_capacity(size);
    match prefix {
        StrPrefix::None | StrPrefix::Utf8 => {
            values.extend(content.bytes().map(|b| b as i64));
        }
        StrPrefix::Wide | StrPrefix::Utf32 => {
            values.extend(content.chars().map(|c| c as u32 as i64));
        }
        StrPrefix::Utf16 => {
            for c in content.chars() {
                let mut buf = [0; 2];
                values.extend(c.encode_utf16(&mut buf).iter().map(|&u| u as i64));
            }
        }
    }
    values.push(0); // Null terminator

    StringLiteralValue {
        builtin_type,
        size,
        values,
    }
}
