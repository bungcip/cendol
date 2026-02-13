use crate::ast::literal::{FloatSuffix, IntegerSuffix};
use std::char;
use std::iter::Peekable;
use std::str::Chars;

const INTEGER_SUFFIXES: &[(&str, IntegerSuffix)] = &[
    ("ull", IntegerSuffix::ULL),
    ("llu", IntegerSuffix::ULL),
    ("ul", IntegerSuffix::UL),
    ("lu", IntegerSuffix::UL),
    ("ll", IntegerSuffix::LL),
    ("u", IntegerSuffix::U),
    ("l", IntegerSuffix::L),
];

/// Strip integer literal suffix (u, l, ll, ul, ull, etc.)
fn strip_integer_suffix(text: &str) -> (&str, Option<IntegerSuffix>) {
    for &(suffix, variant) in INTEGER_SUFFIXES {
        if text.len() >= suffix.len() && text[text.len() - suffix.len()..].eq_ignore_ascii_case(suffix) {
            return (&text[..text.len() - suffix.len()], Some(variant));
        }
    }
    (text, None)
}

/// Parse C11 integer literal syntax
/// Returns (value, suffix)
pub(crate) fn parse_c11_integer_literal(text: &str) -> Option<(u64, Option<IntegerSuffix>)> {
    let (number_part, suffix) = strip_integer_suffix(text);

    if number_part.is_empty() {
        return None;
    }

    let (base, digits) = if let Some(stripped) = number_part.strip_prefix("0x") {
        (16, stripped)
    } else if let Some(stripped) = number_part.strip_prefix("0X") {
        (16, stripped)
    } else if let Some(stripped) = number_part.strip_prefix('0') {
        if stripped.is_empty() {
            return Some((0, suffix));
        }
        (8, stripped)
    } else {
        (10, number_part)
    };

    if digits.is_empty() {
        return None;
    }

    // Use built-in radix parsing which is robust and handles overflow checks
    let val = u64::from_str_radix(digits, base).ok()?;
    Some((val, suffix))
}

/// Parse C11 floating-point literal syntax
pub(crate) fn parse_c11_float_literal(text: &str) -> Option<(f64, Option<FloatSuffix>)> {
    if text.is_empty() {
        return None;
    }

    let (text_without_suffix, suffix) = if let Some(stripped) = text.strip_suffix(|c| c == 'f' || c == 'F') {
        (stripped, Some(FloatSuffix::F))
    } else if let Some(stripped) = text.strip_suffix(|c| c == 'l' || c == 'L') {
        (stripped, Some(FloatSuffix::L))
    } else {
        (text, None)
    };

    // Handle hexadecimal floating-point literals (C99/C11)
    if text.starts_with("0x") || text.starts_with("0X") {
        parse_hex_float_literal(text_without_suffix).map(|val| (val, suffix))
    } else {
        // Use Rust's built-in parsing for decimal floats
        text_without_suffix.parse::<f64>().ok().map(|val| (val, suffix))
    }
}

/// Parse hexadecimal floating-point literal (C99/C11)
fn parse_hex_float_literal(text: &str) -> Option<f64> {
    // Format: 0[xX][hexdigits][.hexdigits][pP[+|-]digits][fFlL]
    let mut chars = text.chars().peekable();

    // Skip "0x"
    if chars.next() != Some('0') {
        return None;
    }
    let x = chars.next()?;
    if x != 'x' && x != 'X' {
        return None;
    }

    let mut result = 0.0f64;
    let mut exponent = 0i32;
    let mut has_dot = false;
    let mut fraction_digits = 0;
    let mut has_digits = false;

    // Parse significand
    while let Some(&c) = chars.peek() {
        if let Some(digit) = c.to_digit(16) {
            result = result * 16.0 + digit as f64;
            if has_dot {
                fraction_digits += 1;
            }
            has_digits = true;
            chars.next();
        } else if c == '.' {
            if has_dot {
                return None;
            } // Double dot
            has_dot = true;
            chars.next();
        } else if c == 'p' || c == 'P' {
            break;
        } else {
            return None; // Invalid character
        }
    }

    if !has_digits {
        return None;
    }

    // Parse exponent
    if let Some('p' | 'P') = chars.peek() {
        chars.next();
        let mut exp_sign = 1;
        if let Some(&c) = chars.peek() {
            if c == '-' {
                exp_sign = -1;
                chars.next();
            } else if c == '+' {
                chars.next();
            }
        }

        let mut exp_val = 0i32;
        let mut has_exp_digits = false;
        while let Some(&c) = chars.peek() {
            if let Some(d) = c.to_digit(10) {
                exp_val = exp_val.checked_mul(10)?.checked_add(d as i32)?;
                has_exp_digits = true;
                chars.next();
            } else {
                break;
            }
        }
        if !has_exp_digits {
            return None;
        }
        exponent = exp_val * exp_sign;
    }

    // Apply adjustments
    if fraction_digits > 0 {
        result /= 16.0f64.powi(fraction_digits);
    }
    if exponent != 0 {
        result *= 2.0f64.powi(exponent);
    }

    Some(result)
}

/// Unescape C11 string literal content
pub(crate) fn unescape_string(s: &str) -> String {
    if !s.contains('\\') {
        return s.to_string();
    }
    let mut result = String::with_capacity(s.len());
    unescape_string_into(s, &mut result);
    result
}

/// Unescape C11 string literal content into a buffer
fn unescape_string_into(s: &str, result: &mut String) {
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\\' {
            parse_escape_sequence(&mut chars, result);
        } else {
            result.push(c);
        }
    }
}

fn parse_escape_sequence(chars: &mut Peekable<Chars>, result: &mut String) {
    match chars.peek() {
        Some('n') => {
            chars.next();
            result.push('\n');
        }
        Some('t') => {
            chars.next();
            result.push('\t');
        }
        Some('r') => {
            chars.next();
            result.push('\r');
        }
        Some('b') => {
            chars.next();
            result.push('\x08');
        }
        Some('f') => {
            chars.next();
            result.push('\x0C');
        }
        Some('v') => {
            chars.next();
            result.push('\x0B');
        }
        Some('a') => {
            chars.next();
            result.push('\x07');
        }
        Some('\\') => {
            chars.next();
            result.push('\\');
        }
        Some('\'') => {
            chars.next();
            result.push('\'');
        }
        Some('"') => {
            chars.next();
            result.push('"');
        }
        Some('?') => {
            chars.next();
            result.push('?');
        }
        Some('x') => parse_hex_escape(chars, result),
        Some('u') | Some('U') => parse_ucn_escape(chars, result),
        Some(c) if c.is_digit(8) => parse_octal_escape(chars, result),
        Some(c) => {
            // Unknown escape, keep char
            result.push(*c);
            chars.next();
        }
        None => {
            result.push('\\');
        }
    }
}

fn parse_hex_escape(chars: &mut Peekable<Chars>, result: &mut String) {
    chars.next(); // consume 'x'
    let mut val: u64 = 0;
    let mut has_digits = false;

    while let Some(&ch) = chars.peek() {
        if let Some(digit) = ch.to_digit(16) {
            val = val.saturating_mul(16).saturating_add(digit as u64);
            has_digits = true;
            chars.next();
        } else {
            break;
        }
    }

    if has_digits {
        let char_val = if val > 0x10FFFF { 0xFFFD } else { val as u32 };
        result.push(char::from_u32(char_val).unwrap_or(char::REPLACEMENT_CHARACTER));
    } else {
        result.push('\\');
        result.push('x');
    }
}

fn parse_octal_escape(chars: &mut Peekable<Chars>, result: &mut String) {
    let mut val = 0u32;
    for _ in 0..3 {
        if let Some(&ch) = chars.peek() {
            if let Some(digit) = ch.to_digit(8) {
                val = val * 8 + digit;
                chars.next();
            } else {
                break;
            }
        } else {
            break;
        }
    }
    result.push(char::from_u32(val).unwrap_or(char::REPLACEMENT_CHARACTER));
}

fn parse_ucn_escape(chars: &mut Peekable<Chars>, result: &mut String) {
    let is_u = chars.next() == Some('u'); // consume u/U
    let digits_needed = if is_u { 4 } else { 8 };
    let mut hex_str = String::new();

    for _ in 0..digits_needed {
        if let Some(&ch) = chars.peek() {
            if ch.is_ascii_hexdigit() {
                chars.next();
                hex_str.push(ch);
            } else {
                break;
            }
        } else {
            break;
        }
    }

    if hex_str.len() != digits_needed {
        // Invalid, preserve as raw
        result.push('\\');
        result.push(if is_u { 'u' } else { 'U' });
        result.push_str(&hex_str);
        return;
    }

    if let Some(c) = u32::from_str_radix(&hex_str, 16).ok().and_then(char::from_u32) {
        result.push(c);
        return;
    }

    // Invalid codepoint
    result.push(char::REPLACEMENT_CHARACTER);
}

/// Parse a character literal content (e.g. "a", "\n", "\x41") into a codepoint
pub(crate) fn parse_char_literal(s: &str) -> Option<u32> {
    if s.is_empty() {
        return None;
    }
    // Optimization: if simple char, just return it
    if !s.contains('\\') {
        let mut chars = s.chars();
        let c = chars.next()?;
        return Some(c as u32);
    }

    let unescaped = unescape_string(s);
    unescaped.chars().next().map(|c| c as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uppercase_hex_literals() {
        // Test 0X integer prefix
        assert_eq!(parse_c11_integer_literal("0X10"), Some((16, None)));

        // Test 0X float prefix
        // 0X1p0 -> 1.0 * 2^0 = 1.0
        assert_eq!(parse_c11_float_literal("0X1p0"), Some((1.0, None)));
    }

    #[test]
    fn test_escape_sequences() {
        // Test various C escape sequences
        assert_eq!(unescape_string(r"\n"), "\n");
        assert_eq!(unescape_string(r"\t"), "\t");
        assert_eq!(unescape_string(r"\r"), "\r");
        assert_eq!(unescape_string(r"\b"), "\x08"); // BS
        assert_eq!(unescape_string(r"\f"), "\x0C"); // FF
        assert_eq!(unescape_string(r"\v"), "\x0B"); // VT
        assert_eq!(unescape_string(r"\a"), "\x07"); // BEL
        assert_eq!(unescape_string(r"\\"), "\\");
        assert_eq!(unescape_string(r"\'"), "\'");
        assert_eq!(unescape_string(r#"\""#), "\"");
        assert_eq!(unescape_string(r"\?"), "?");

        // Mixed content
        assert_eq!(unescape_string(r"Hello\nWorld"), "Hello\nWorld");
    }
}
