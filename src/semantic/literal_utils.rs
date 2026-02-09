use crate::ast::NameId;
use crate::ast::literal_parsing;
use crate::semantic::BuiltinType;

pub enum StringLiteralPrefix {
    None,
    Wide,   // L"..." -> wchar_t (int)
    Char16, // u"..." -> char16_t (uint16)
    Char32, // U"..." -> char32_t (uint32)
    Utf8,   // u8"..." -> char
}

pub struct ParsedStringLiteral {
    pub builtin_type: BuiltinType,
    pub values: Vec<i64>, // Store as i64 to handle all types
    pub size: usize,
}

pub(crate) fn parse_string_literal(name: NameId) -> ParsedStringLiteral {
    let raw = name.as_str();

    let (stripped, builtin_type, kind) = if let Some(s) = raw.strip_prefix("L\"") {
        (Some(s), BuiltinType::Int, StringLiteralPrefix::Wide)
    } else if let Some(s) = raw.strip_prefix("u\"") {
        (Some(s), BuiltinType::UShort, StringLiteralPrefix::Char16)
    } else if let Some(s) = raw.strip_prefix("U\"") {
        (Some(s), BuiltinType::UInt, StringLiteralPrefix::Char32)
    } else if let Some(s) = raw.strip_prefix("u8\"") {
        (Some(s), BuiltinType::Char, StringLiteralPrefix::Utf8)
    } else if let Some(s) = raw.strip_prefix("\"") {
        (Some(s), BuiltinType::Char, StringLiteralPrefix::None)
    } else {
        (None, BuiltinType::Char, StringLiteralPrefix::None)
    };

    let content = match stripped {
        Some(s) => literal_parsing::unescape_string(s.strip_suffix('"').unwrap_or(s)),
        None => raw.to_string(),
    };

    let mut values = Vec::new();
    match kind {
        StringLiteralPrefix::None | StringLiteralPrefix::Utf8 => {
            values.extend(content.bytes().map(|b| b as i64));
        }
        StringLiteralPrefix::Wide | StringLiteralPrefix::Char32 => {
            values.extend(content.chars().map(|c| c as u32 as i64));
        }
        StringLiteralPrefix::Char16 => {
            for c in content.chars() {
                let mut buf = [0; 2];
                values.extend(c.encode_utf16(&mut buf).iter().map(|&u| u as i64));
            }
        }
    }
    values.push(0); // Null terminator

    ParsedStringLiteral {
        builtin_type,
        size: values.len(),
        values,
    }
}
