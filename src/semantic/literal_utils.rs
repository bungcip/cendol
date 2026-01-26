use crate::ast::NameId;
use crate::lexer::Lexer;
use crate::semantic::BuiltinType;

pub enum StringLiteralKind {
    Char,
    Wide,   // L"..." -> wchar_t (int)
    Char16, // u"..." -> char16_t (uint16)
    Char32, // U"..." -> char32_t (uint32)
    Utf8,   // u8"..." -> char
}

pub struct ParsedStringLiteral {
    pub _kind: StringLiteralKind,
    pub builtin_type: BuiltinType,
    pub values: Vec<i64>, // Store as i64 to handle all types
    pub size: usize,
}

pub fn parse_string_literal(name: NameId) -> ParsedStringLiteral {
    let raw = name.as_str();

    // Check for prefixes.
    // Note: The lexer strips quotes/escapes for standard strings ("..."), but NOT for prefixed strings (L"...").
    // So if we see a prefix, it's a raw string that needs unescaping.
    // If we don't see a prefix (and it doesn't start with quote), it's likely a standard string that is already unescaped.

    if let Some(stripped) = raw.strip_prefix("L\"") {
        parse_prefixed(stripped, StringLiteralKind::Wide, BuiltinType::Int) // Assuming wchar_t is int (32-bit)
    } else if let Some(stripped) = raw.strip_prefix("u\"") {
        parse_prefixed(stripped, StringLiteralKind::Char16, BuiltinType::UShort)
    } else if let Some(stripped) = raw.strip_prefix("U\"") {
        parse_prefixed(stripped, StringLiteralKind::Char32, BuiltinType::UInt)
    } else if let Some(stripped) = raw.strip_prefix("u8\"") {
        parse_prefixed(stripped, StringLiteralKind::Utf8, BuiltinType::Char)
    } else {
        // Standard string, already unescaped by Lexer
        let mut values = Vec::new();
        for b in raw.bytes() {
            values.push(b as i64);
        }
        values.push(0); // Null terminator

        ParsedStringLiteral {
            _kind: StringLiteralKind::Char,
            builtin_type: BuiltinType::Char,
            size: values.len(),
            values,
        }
    }
}

fn parse_prefixed(content_raw: &str, kind: StringLiteralKind, builtin_type: BuiltinType) -> ParsedStringLiteral {
    // Remove trailing quote
    let content_raw = if content_raw.ends_with('"') {
        &content_raw[..content_raw.len() - 1]
    } else {
        content_raw
    };

    let content = Lexer::unescape_string(content_raw);
    let mut values = Vec::new();

    match kind {
        StringLiteralKind::Char | StringLiteralKind::Utf8 => {
            for b in content.bytes() {
                values.push(b as i64);
            }
        }
        StringLiteralKind::Wide => {
            for c in content.chars() {
                values.push(c as u32 as i64);
            }
        }
        StringLiteralKind::Char16 => {
            for c in content.chars() {
                let mut buf = [0; 2];
                let encoded = c.encode_utf16(&mut buf);
                for u in encoded {
                    values.push(*u as i64);
                }
            }
        }
        StringLiteralKind::Char32 => {
            for c in content.chars() {
                values.push(c as u32 as i64);
            }
        }
    }
    values.push(0); // Null terminator

    ParsedStringLiteral {
        _kind: kind,
        builtin_type,
        size: values.len(),
        values,
    }
}
