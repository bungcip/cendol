use crate::ast::literal::{FloatSuffix, IntSuffix};
use std::char;
use std::iter::Peekable;
use std::str::Chars;

const INTEGER_SUFFIXES: &[(&str, IntSuffix)] = &[
    ("ull", IntSuffix::ULL),
    ("llu", IntSuffix::ULL),
    ("ul", IntSuffix::UL),
    ("lu", IntSuffix::UL),
    ("ll", IntSuffix::LL),
    ("u", IntSuffix::U),
    ("l", IntSuffix::L),
];

/// Strip integer literal suffix (u, l, ll, ul, ull, etc.)
fn strip_integer_suffix(text: &str) -> (&str, Option<IntSuffix>) {
    for &(suffix, variant) in INTEGER_SUFFIXES {
        if text.len() >= suffix.len() && text[text.len() - suffix.len()..].eq_ignore_ascii_case(suffix) {
            return (&text[..text.len() - suffix.len()], Some(variant));
        }
    }
    (text, None)
}

/// Parse C11 integer literal syntax
/// Returns (value, suffix, base)
pub(crate) fn parse_integer_literal(text: &str) -> Option<(i64, Option<IntSuffix>, u8)> {
    let (number_part, suffix) = strip_integer_suffix(text);

    if number_part.is_empty() {
        return None;
    }

    let (radix, digits) = if let Some(stripped) = number_part.strip_prefix("0x") {
        (16, stripped)
    } else if let Some(stripped) = number_part.strip_prefix("0X") {
        (16, stripped)
    } else if let Some(stripped) = number_part.strip_prefix("0b") {
        (2, stripped)
    } else if let Some(stripped) = number_part.strip_prefix("0B") {
        (2, stripped)
    } else if let Some(stripped) = number_part.strip_prefix('0') {
        if stripped.is_empty() {
            return Some((0, suffix, 8));
        }
        (8, stripped)
    } else {
        (10, number_part)
    };

    if digits.is_empty() {
        return None;
    }

    // Use built-in radix parsing which is robust and handles overflow checks
    let digits_no_sep = if digits.contains('\'') {
        std::borrow::Cow::Owned(digits.replace('\'', ""))
    } else {
        std::borrow::Cow::Borrowed(digits)
    };

    let val = u64::from_str_radix(&digits_no_sep, radix).ok()?;
    Some((val as i64, suffix, radix as u8))
}

fn strip_float_suffix(text: &str) -> (&str, Option<FloatSuffix>) {
    let mut is_float = false;
    let mut is_long = false;
    let mut is_imaginary = false;

    let mut len = text.len();
    while len > 0 {
        let ch = text.as_bytes()[len - 1];
        if (ch == b'f' || ch == b'F') && !is_float && !is_long {
            is_float = true;
            len -= 1;
        } else if (ch == b'l' || ch == b'L') && !is_long && !is_float {
            is_long = true;
            len -= 1;
        } else if (ch == b'i' || ch == b'I' || ch == b'j' || ch == b'J') && !is_imaginary {
            is_imaginary = true;
            len -= 1;
        } else {
            break;
        }
    }

    let stripped = &text[..len];
    let suffix = if is_imaginary {
        if is_float {
            Some(FloatSuffix::IF)
        } else if is_long {
            Some(FloatSuffix::IL)
        } else {
            Some(FloatSuffix::I)
        }
    } else if is_float {
        Some(FloatSuffix::F)
    } else if is_long {
        Some(FloatSuffix::L)
    } else {
        None
    };

    (stripped, suffix)
}

/// Parse C11 floating-point literal syntax
pub(crate) fn parse_float_literal(text: &str) -> Option<(f64, Option<FloatSuffix>)> {
    if text.is_empty() {
        return None;
    }

    let (text_without_suffix, suffix) = strip_float_suffix(text);

    // Handle hexadecimal floating-point literals (C99/C11)
    if text.starts_with("0x") || text.starts_with("0X") {
        parse_hex_float_literal(text_without_suffix).map(|val| (val, suffix))
    } else {
        // Use Rust's built-in parsing for decimal floats
        let text_no_sep = if text_without_suffix.contains('\'') {
            std::borrow::Cow::Owned(text_without_suffix.replace('\'', ""))
        } else {
            std::borrow::Cow::Borrowed(text_without_suffix)
        };
        text_no_sep.parse::<f64>().ok().map(|val| (val, suffix))
    }
}

/// Parse hexadecimal floating-point literal (C99/C11)
/// invariant: first 2 character must be 0x or 0X
fn parse_hex_float_literal(text: &str) -> Option<f64> {
    // Format: 0[xX][hexdigits][.hexdigits][pP[+|-]digits][fFlL]
    let mut chars = text.chars().peekable();

    // Skip "0x"
    chars.next(); // '0'
    chars.next(); // 'x' or 'X'

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
        } else if c == '\'' {
            chars.next(); // Skip digit separator
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
            } else if c == '\'' {
                chars.next(); // Skip digit separator
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
pub(crate) fn unescape<'a>(s: &'a str) -> std::borrow::Cow<'a, str> {
    if !s.contains('\\') {
        return std::borrow::Cow::Borrowed(s);
    }
    let mut result = String::with_capacity(s.len());
    unescape_into(s, &mut result);
    std::borrow::Cow::Owned(result)
}

/// Unescape C11 string literal content into a buffer
fn unescape_into(s: &str, result: &mut String) {
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

    let unescaped = unescape(s);
    unescaped.chars().next().map(|c| c as u32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uppercase_hex_literals() {
        // Test 0X integer prefix
        assert_eq!(parse_integer_literal("0X10"), Some((16, None, 16)));

        // Test 0X float prefix
        // 0X1p0 -> 1.0 * 2^0 = 1.0
        assert_eq!(parse_float_literal("0X1p0"), Some((1.0, None)));
    }

    #[test]
    fn test_float_literal_suffixes() {
        // Real part
        assert_eq!(parse_float_literal("1.0"), Some((1.0, None)));
        assert_eq!(parse_float_literal("1.0f"), Some((1.0, Some(FloatSuffix::F))));
        assert_eq!(parse_float_literal("1.0F"), Some((1.0, Some(FloatSuffix::F))));
        assert_eq!(parse_float_literal("1.0l"), Some((1.0, Some(FloatSuffix::L))));
        assert_eq!(parse_float_literal("1.0L"), Some((1.0, Some(FloatSuffix::L))));

        // Imaginary part
        assert_eq!(parse_float_literal("1.0i"), Some((1.0, Some(FloatSuffix::I))));
        assert_eq!(parse_float_literal("1.0I"), Some((1.0, Some(FloatSuffix::I))));
        assert_eq!(parse_float_literal("1.0j"), Some((1.0, Some(FloatSuffix::I))));
        assert_eq!(parse_float_literal("1.0J"), Some((1.0, Some(FloatSuffix::I))));

        assert_eq!(parse_float_literal("1.0fi"), Some((1.0, Some(FloatSuffix::IF))));
        assert_eq!(parse_float_literal("1.0if"), Some((1.0, Some(FloatSuffix::IF))));

        assert_eq!(parse_float_literal("1.0li"), Some((1.0, Some(FloatSuffix::IL))));
        assert_eq!(parse_float_literal("1.0il"), Some((1.0, Some(FloatSuffix::IL))));

        // Hex exponent value overflows i32
        assert_eq!(parse_float_literal("0x1p999999999999"), None);

        // Hex float without exponent
        assert_eq!(parse_float_literal("0x1.5"), Some((1.3125, None)));

        // Exponent without digits
        assert_eq!(parse_float_literal("0x1p"), None);
    }

    #[test]
    fn test_escape_sequences() {
        // Test various C escape sequences
        assert_eq!(unescape(r"\n"), "\n");
        assert_eq!(unescape(r"\t"), "\t");
        assert_eq!(unescape(r"\r"), "\r");
        assert_eq!(unescape(r"\b"), "\x08"); // BS
        assert_eq!(unescape(r"\f"), "\x0C"); // FF
        assert_eq!(unescape(r"\v"), "\x0B"); // VT
        assert_eq!(unescape(r"\a"), "\x07"); // BEL
        assert_eq!(unescape(r"\\"), "\\");
        assert_eq!(unescape(r"\'"), "\'");
        assert_eq!(unescape(r#"\""#), "\"");
        assert_eq!(unescape(r"\?"), "?");

        // Mixed content
        assert_eq!(unescape(r"Hello\nWorld"), "Hello\nWorld");
    }

    #[test]
    fn test_escape_edge_cases() {
        // Unknown escape -> keep char (e.g., \q -> q)
        assert_eq!(unescape(r"\q"), "q");

        // Trailing backslash -> keep backslash
        assert_eq!(unescape(r"foo\"), r"foo\");

        // Incomplete UCN -> keep raw
        assert_eq!(unescape(r"\u123"), r"\u123");
        assert_eq!(unescape(r"\U12345"), r"\U12345"); // too short for U

        // Invalid hex digits in UCN -> keep partial raw
        assert_eq!(unescape(r"\u12z"), r"\u12z");

        // Invalid codepoint in UCN -> replacement char (U+FFFD)
        // U+D800 is a surrogate, which is invalid in scalar value
        assert_eq!(unescape(r"\uD800"), "\u{FFFD}");

        // Empty hex escape -> \x
        assert_eq!(unescape(r"\xz"), r"\xz");
    }

    #[test]
    fn test_hex_float_edge_cases() {
        // Covers line 123 (digit separator in decimal float)
        assert_eq!(super::parse_float_literal("1'0.5"), Some((10.5, None)));

        // Covers line 163 (digit separator in hex float mantissa)
        assert_eq!(super::parse_hex_float_literal("0x1'A.5p2"), Some(105.25));

        // Covers line 196, 197 (digit separator in hex float exponent)
        assert_eq!(super::parse_hex_float_literal("0x1.0p1'0"), Some(1024.0));
    }
}
