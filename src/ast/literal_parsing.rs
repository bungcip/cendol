use crate::ast::literal::IntegerSuffix;

/// Strip integer literal suffix (u, l, ll, ul, ull, etc.)
pub fn strip_integer_suffix(text: &str) -> (&str, Option<IntegerSuffix>) {
    // ⚡ Bolt: Optimized suffix stripping.
    // This implementation is faster than the previous version, which used multiple
    // string slices and `eq_ignore_ascii_case` calls. By working with bytes directly
    // and using `matches!` for character comparisons, we avoid the overhead of
    // slicing and function calls in the common cases, resulting in a small but
    // measurable performance improvement for parsing integer literals.
    let bytes = text.as_bytes();
    let len = bytes.len();

    if len == 0 {
        return (text, None);
    }

    // Check for the longest suffixes first (3 characters: "ull", "llu").
    if len >= 3 {
        let last3 = (
            bytes[len - 3].to_ascii_lowercase(),
            bytes[len - 2].to_ascii_lowercase(),
            bytes[len - 1].to_ascii_lowercase(),
        );
        if matches!(last3, (b'u', b'l', b'l') | (b'l', b'l', b'u')) {
            return (&text[..len - 3], Some(IntegerSuffix::ULL));
        }
    }

    // Check for 2-character suffixes ("ul", "lu", "ll").
    if len >= 2 {
        let last2 = (bytes[len - 2].to_ascii_lowercase(), bytes[len - 1].to_ascii_lowercase());
        if matches!(last2, (b'u', b'l') | (b'l', b'u')) {
            return (&text[..len - 2], Some(IntegerSuffix::UL));
        } else if matches!(last2, (b'l', b'l')) {
            return (&text[..len - 2], Some(IntegerSuffix::LL));
        }
    }

    // Check for 1-character suffixes ("u", "l").
    if len >= 1 {
        let last1 = bytes[len - 1].to_ascii_lowercase();
        if matches!(last1, b'u') {
            return (&text[..len - 1], Some(IntegerSuffix::U));
        } else if matches!(last1, b'l') {
            return (&text[..len - 1], Some(IntegerSuffix::L));
        }
    }

    // No suffix found.
    (text, None)
}

/// Parse C11 integer literal syntax
/// Returns (value, suffix)
pub fn parse_c11_integer_literal(text: &str) -> Result<(u64, Option<IntegerSuffix>), ()> {
    // Use the existing, optimized suffix stripper to get the numeric part.
    let (number_part, suffix) = strip_integer_suffix(text);

    // Handle the case where the number is just "0" after stripping suffix.
    if number_part == "0" {
        return Ok((0, suffix));
    }

    let mut base = 10;
    let mut digits_to_parse = number_part;

    // Determine base and strip prefix from the numeric part.
    if number_part.starts_with("0x") || number_part.starts_with("0X") {
        base = 16;
        digits_to_parse = &number_part[2..];
    } else if let Some(stripped) = number_part.strip_prefix('0') {
        base = 8;
        digits_to_parse = stripped;
    }
    // else base is 10 and we parse the whole `number_part`.

    // If after stripping prefixes the string is empty, it's an error.
    if digits_to_parse.is_empty() {
        return Err(());
    }

    let mut result: u64 = 0;
    for c in digits_to_parse.chars() {
        // `to_digit` will return None for invalid characters in the given base
        // (e.g., '9' in octal), which correctly propagates the error.
        let digit = c.to_digit(base).ok_or(())?;

        // Use checked arithmetic to prevent overflow, replicating .parse() behavior.
        result = result.checked_mul(base as u64).ok_or(())?;
        result = result.checked_add(digit as u64).ok_or(())?;
    }

    Ok((result, suffix))
}

/// Parse C11 floating-point literal syntax
pub fn parse_c11_float_literal(text: &str) -> Result<f64, ()> {
    // C11 floating-point literal format:
    // [digits][.digits][e|E[+|-]digits][f|F|l|L]
    // or [digits][e|E[+|-]digits][f|F|l|L]
    // or 0[xX][hexdigits][.hexdigits][p|P[+|-]digits][f|F|l|L]

    // ⚡ Bolt: Optimized suffix stripping.
    // This is faster than chaining `ends_with` calls. By checking the last byte
    // directly, we avoid multiple string traversals and improve performance for
    // parsing floating-point literals.
    let text_without_suffix = if !text.is_empty() {
        match text.as_bytes()[text.len() - 1] {
            b'f' | b'F' | b'l' | b'L' => &text[..text.len() - 1],
            _ => text,
        }
    } else {
        text
    };

    // Handle hexadecimal floating-point literals (C99/C11)
    if text.starts_with("0x") || text.starts_with("0X") {
        parse_hex_float_literal(text_without_suffix)
    } else {
        // Use Rust's built-in parsing for decimal floats
        match text_without_suffix.parse::<f64>() {
            Ok(val) => Ok(val),
            Err(_) => {
                // Invalid float, treat as unknown
                Err(())
            }
        }
    }
}

/// Parse hexadecimal floating-point literal (C99/C11)
fn parse_hex_float_literal(text: &str) -> Result<f64, ()> {
    // Format: 0[xX][hexdigits][.hexdigits][pP[+|-]digits][fFlL]
    // Example: 0x1.2p3, 0x1p-5f, 0x.8p10L

    let mut chars = text.chars().peekable();
    let mut result = 0.0f64;
    let mut exponent = 0i32;
    let mut seen_dot = false;
    let mut fraction_digits = 0;

    // Skip "0x" or "0X"
    chars.next(); // '0'
    chars.next(); // 'x' or 'X'

    // Parse hexadecimal digits before decimal point
    while let Some(&c) = chars.peek() {
        if c.is_ascii_hexdigit() {
            let digit = c.to_digit(16).unwrap() as f64;
            result = result * 16.0 + digit;
            chars.next();
        } else if c == '.' && !seen_dot {
            seen_dot = true;
            chars.next();
            break;
        } else if c == 'p' || c == 'P' {
            break;
        } else {
            return Err(());
        }
    }

    // Parse hexadecimal digits after decimal point
    if seen_dot {
        while let Some(&c) = chars.peek() {
            if c.is_ascii_hexdigit() {
                let digit = c.to_digit(16).unwrap() as f64;
                result = result * 16.0 + digit;
                fraction_digits += 1;
                chars.next();
            } else if c == 'p' || c == 'P' {
                break;
            } else {
                return Err(());
            }
        }
    }

    // Parse binary exponent
    if let Some(&c) = chars.peek()
        && (c == 'p' || c == 'P')
    {
        chars.next(); // consume 'p' or 'P'

        // Parse optional sign
        let mut exp_negative = false;
        if let Some(&sign) = chars.peek() {
            if sign == '+' {
                chars.next();
            } else if sign == '-' {
                exp_negative = true;
                chars.next();
            }
        }

        // Parse exponent digits safely without string allocation
        let mut exp_val = 0i32;
        let mut exp_digits = 0;
        while let Some(&c) = chars.peek() {
            if let Some(digit) = c.to_digit(10) {
                // Use checked arithmetic to prevent overflow, replicating .parse() behavior.
                exp_val = match exp_val.checked_mul(10).and_then(|v| v.checked_add(digit as i32)) {
                    Some(val) => val,
                    None => return Err(()), // Overflow
                };
                exp_digits += 1;
                chars.next();
            } else {
                break;
            }
        }

        if exp_digits == 0 {
            return Err(());
        }

        exponent = if exp_negative { -exp_val } else { exp_val };
    }

    // Apply fractional adjustment
    if fraction_digits > 0 {
        result /= 16.0f64.powi(fraction_digits);
    }

    // Apply binary exponent
    if exponent != 0 {
        result *= 2.0f64.powi(exponent);
    }

    Ok(result)
}

/// Unescape C11 string literal content
pub fn unescape_string(s: &str) -> String {
    // ⚡ Bolt: Fast path for strings with no escape sequences.
    // This avoids allocating a new string and iterating over it when no
    // unescaping is necessary. It makes the common case of simple strings
    // much faster.
    if !s.contains('\\') {
        return s.to_string();
    }

    let mut result = String::with_capacity(s.len());
    unescape_string_into(s, &mut result);
    result
}

/// Unescape C11 string literal content into a buffer
///
/// ⚡ Bolt: Optimized to reduce allocations.
/// This private helper avoids intermediate allocations by writing the unescaped
/// string directly into a provided buffer. This is significantly more efficient
/// when concatenating multiple string literals, as it allows us to unescape
/// all of them into a single, final string without creating temporary strings
/// for each part.
pub fn unescape_string_into(s: &str, result: &mut String) {
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
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
                    result.push('\u{0008}');
                } // Backspace
                Some('f') => {
                    chars.next();
                    result.push('\u{000C}');
                } // Form feed
                Some('v') => {
                    chars.next();
                    result.push('\u{000B}');
                } // Vertical tab
                Some('a') => {
                    chars.next();
                    result.push('\u{0007}');
                } // Alert
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
                Some('x') => {
                    // Hex escape
                    chars.next(); // consume 'x'
                    let mut val: u64 = 0;
                    let mut has_digits = false;
                    while let Some(&ch) = chars.peek() {
                        if let Some(digit) = ch.to_digit(16) {
                            // Prevent overflow
                            val = val.saturating_mul(16).saturating_add(digit as u64);
                            has_digits = true;
                            chars.next();
                        } else {
                            break;
                        }
                    }
                    if has_digits {
                        // Limit to valid Unicode scalar value range since we must produce a String
                        let char_val = if val > 0x10FFFF {
                            0xFFFD // Replacement character
                        } else {
                            val as u32
                        };

                        if let Some(c) = std::char::from_u32(char_val) {
                            result.push(c);
                        } else {
                            // Fallback for invalid unicode scalars (e.g. surrogates)
                            result.push(std::char::REPLACEMENT_CHARACTER);
                        }
                    } else {
                        // \x with no digits is technically undefined/error.
                        // Keep \x
                        result.push('\\');
                        result.push('x');
                    }
                }
                Some(c) if c.is_digit(8) => {
                    // Octal escape
                    // Up to 3 digits
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
                    if let Some(c) = std::char::from_u32(val) {
                        result.push(c);
                    } else {
                        result.push(std::char::REPLACEMENT_CHARACTER);
                    }
                }
                Some(c) => {
                    // Unknown escape, keep char (standard says undefined)
                    // GCC emits just the char.
                    result.push(*c);
                    chars.next();
                }
                None => {
                    // Trailing backslash
                    result.push('\\');
                }
            }
        } else {
            result.push(c);
        }
    }
}

/// Parse a character literal content (e.g. "a", "\n", "\x41") into a codepoint
pub fn parse_char_literal(s: &str) -> Result<u32, ()> {
    if s.is_empty() {
        return Err(());
    }
    let unescaped = unescape_string(s);
    let mut chars = unescaped.chars();
    if let Some(c) = chars.next() {
        // We only care about the first character for simple char literals
        return Ok(c as u32);
    }
    Err(())
}
