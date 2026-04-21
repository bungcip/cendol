use crate::ast::literal::StrPrefix;
use crate::semantic::BuiltinType;

pub struct StringLiteralValue {
    pub builtin_type: BuiltinType,
    pub values: Vec<i64>, // Store as i64 to handle all types
    pub size: usize,
}

pub(crate) fn lower_string_literal(content: &str, prefix: StrPrefix) -> StringLiteralValue {
    let builtin_type = match prefix {
        StrPrefix::Wide => BuiltinType::Int,
        StrPrefix::Utf16 => BuiltinType::UShort,
        StrPrefix::Utf32 => BuiltinType::UInt,
        StrPrefix::Utf8 => BuiltinType::UChar,
        StrPrefix::None => BuiltinType::Char,
    };

    let mut values = Vec::new();
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
        size: values.len(),
        values,
    }
}
