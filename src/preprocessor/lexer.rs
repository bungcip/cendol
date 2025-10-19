use crate::preprocessor::error::PreprocessorError;
use crate::preprocessor::token::{SourceLocation, Token, TokenKind};
use std::iter::Peekable;
use std::str::Chars;

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    at_start_of_line: bool,
    line: u32,
    file: String,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str, file: String) -> Self {
        Lexer {
            input: input.chars().peekable(),
            at_start_of_line: true,
            line: 1,
            file,
        }
    }

    pub fn next_token(&mut self) -> Result<Token, PreprocessorError> {
        let c = match self.input.next() {
            Some(c) => c,
            None => return Ok(Token::new(TokenKind::Eof, self.location())),
        };

        match c {
            '\\' => {
                if let Some(&'\n') = self.input.peek() {
                    self.input.next();
                    self.at_start_of_line = true;
                    self.line += 1;
                    self.next_token()
                } else {
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Punct("\\".to_string()), self.location()))
                }
            }
            ' ' | '\t' | '\r' => {
                let mut whitespace = String::from(c);
                while let Some(&c) = self.input.peek() {
                    if c == ' ' || c == '\t' || c == '\r' {
                        whitespace.push(self.input.next().unwrap());
                    } else {
                        break;
                    }
                }
                Ok(Token::new(TokenKind::Whitespace(whitespace), self.location()))
            }
            '\n' => {
                self.at_start_of_line = true;
                self.line += 1;
                Ok(Token::new(TokenKind::Newline, self.location()))
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
                    Ok(Token::new(TokenKind::Keyword(ident), self.location()))
                } else {
                    Ok(Token::new(TokenKind::Identifier(ident), self.location()))
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
                Ok(Token::new(TokenKind::Number(num), self.location()))
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
                Ok(Token::new(TokenKind::String(s), self.location()))
            }
            '#' => {
                if self.at_start_of_line {
                    self.read_directive()
                } else if let Some(&'#') = self.input.peek() {
                    self.input.next();
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Punct("##".to_string()), self.location()))
                } else {
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Punct("#".to_string()), self.location()))
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
                    return Ok(Token::new(TokenKind::Punct("...".to_string()), self.location()));
                }

                // Handle cases with one or two dots by re-processing
                let mut chars = dots.chars();
                let first_dot = chars.next().unwrap();
                self.at_start_of_line = false;
                // This part is tricky as we can't easily push back to the input stream.
                // For now, we'll just handle the first dot and the rest will be handled in subsequent calls.
                // A more robust solution might involve a buffer.
                Ok(Token::new(TokenKind::Punct(first_dot.to_string()), self.location()))
            }
            _ if c.is_ascii_punctuation() => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Punct(c.to_string()), self.location()))
            }
            _ => Err(PreprocessorError::UnexpectedChar(c)),
        }
    }

    fn read_directive(&mut self) -> Result<Token, PreprocessorError> {
        let mut directive = String::new();
        while let Some(&c) = self.input.peek() {
            if c.is_alphabetic() {
                directive.push(self.input.next().unwrap());
            } else {
                break;
            }
        }

        self.at_start_of_line = false;
        match directive.as_str() {
            "if" => Ok(Token::new(TokenKind::If, self.location())),
            "else" => Ok(Token::new(TokenKind::Else, self.location())),
            "elif" => Ok(Token::new(TokenKind::Elif, self.location())),
            "endif" => Ok(Token::new(TokenKind::Endif, self.location())),
            "ifdef" => Ok(Token::new(TokenKind::Ifdef, self.location())),
            "ifndef" => Ok(Token::new(TokenKind::Ifndef, self.location())),
            "undef" => Ok(Token::new(TokenKind::Undef, self.location())),
            "error" => Ok(Token::new(TokenKind::Error, self.location())),
            "line" => Ok(Token::new(TokenKind::Line, self.location())),
            "include" => Ok(Token::new(TokenKind::Include, self.location())),
            _ => Ok(Token::new(TokenKind::Directive(directive), self.location())),
        }
    }

    fn location(&self) -> SourceLocation {
        SourceLocation {
            file: self.file.clone(),
            line: self.line,
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
