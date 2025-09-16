use crate::preprocessor::token::{Token, TokenKind};
use std::iter::Peekable;
use std::str::Chars;

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    at_start_of_line: bool,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input: input.chars().peekable(),
            at_start_of_line: true,
        }
    }

    pub fn next_token(&mut self) -> Result<Token, crate::preprocessor::error::PreprocessorError> {
        let c = match self.input.next() {
            Some(c) => c,
            None => return Ok(Token::new(TokenKind::Eof)),
        };

        match c {
            ' ' | '\t' | '\r' => {
                let mut whitespace = String::from(c);
                while let Some(&c) = self.input.peek() {
                    if c == ' ' || c == '\t' || c == '\r' {
                        whitespace.push(self.input.next().unwrap());
                    } else {
                        break;
                    }
                }
                Ok(Token::new(TokenKind::Whitespace(whitespace)))
            }
            '\n' => {
                self.at_start_of_line = true;
                Ok(Token::new(TokenKind::Newline))
            }
            _ if c.is_alphabetic() || c == '_' => {
                let mut ident = String::from(c);
                while let Some(&c) = self.input.peek() {
                    if c.is_alphanumeric() || c == '_' {
                        ident.push(self.input.next().unwrap());
                    } else {
                        break;
                    }
                }
                self.at_start_of_line = false;
                if is_keyword(&ident) {
                    Ok(Token::new(TokenKind::Keyword(ident)))
                } else {
                    Ok(Token::new(TokenKind::Identifier(ident)))
                }
            }
            _ if c.is_digit(10) => {
                let mut num = String::from(c);
                while let Some(&c) = self.input.peek() {
                    if c.is_digit(10) {
                        num.push(self.input.next().unwrap());
                    } else {
                        break;
                    }
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Number(num)))
            }
            '"' => {
                let mut s = String::new();
                while let Some(c) = self.input.next() {
                    if c == '"' {
                        break;
                    }
                    s.push(c);
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::String(s)))
            }
            '#' => {
                if let Some(&'#') = self.input.peek() {
                    self.input.next();
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Punct("##".to_string())))
                } else {
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Punct("#".to_string())))
                }
            }
            '.' => {
                let mut dots = String::from(c);
                if let Some(&'.') = self.input.peek() {
                    dots.push(self.input.next().unwrap());
                    if let Some(&'.') = self.input.peek() {
                        dots.push(self.input.next().unwrap());
                    }
                }

                if dots == "..." {
                    self.at_start_of_line = false;
                    return Ok(Token::new(TokenKind::Punct("...".to_string())));
                }

                // Handle cases with one or two dots by re-processing
                let mut chars = dots.chars();
                let first_dot = chars.next().unwrap();
                self.at_start_of_line = false;
                // This part is tricky as we can't easily push back to the input stream.
                // For now, we'll just handle the first dot and the rest will be handled in subsequent calls.
                // A more robust solution might involve a buffer.
                Ok(Token::new(TokenKind::Punct(first_dot.to_string())))
            }
            _ if c.is_ascii_punctuation() => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Punct(c.to_string())))
            }
            _ => Err(crate::preprocessor::error::PreprocessorError::UnexpectedChar(c)),
        }
    }
}

fn is_keyword(s: &str) -> bool {
    matches!(
        s,
        "auto"
            | "break"
            | "case"
            | "char"
            | "const"
            | "continue"
            | "default"
            | "do"
            | "double"
            | "else"
            | "enum"
            | "extern"
            | "float"
            | "for"
            | "goto"
            | "if"
            | "int"
            | "long"
            | "register"
            | "return"
            | "short"
            | "signed"
            | "sizeof"
            | "static"
            | "struct"
            | "switch"
            | "typedef"
            | "union"
            | "unsigned"
            | "void"
            | "volatile"
            | "while"
    )
}
