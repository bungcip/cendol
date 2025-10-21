use crate::file::FileId;
use crate::preprocessor::error::PreprocessorError;
use crate::preprocessor::token::{DirectiveKind, SourceLocation, Token, TokenKind};
use std::iter::Peekable;
use std::str::Chars;

/// A lexer for the C preprocessor.
pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    at_start_of_line: bool,
    line: u32,
    file: FileId,
}

impl<'a> Lexer<'a> {
    /// Creates a new `Lexer`.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to tokenize.
    /// * `file` - The name of the file being tokenized.
    pub fn new(input: &'a str, file: FileId) -> Self {
        Lexer {
            input: input.chars().peekable(),
            at_start_of_line: true,
            line: 1,
            file,
        }
    }

    /// Returns the next token in the input stream.
    ///
    /// # Returns
    ///
    /// A `Result` containing the next token, or a `PreprocessorError` if tokenization fails.
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
                    Ok(Token::new(TokenKind::Backslash, self.location()))
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
                Ok(Token::new(
                    TokenKind::Whitespace(whitespace),
                    self.location(),
                ))
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
                if let Ok(keyword) = ident.parse() {
                    Ok(Token::new(TokenKind::Keyword(keyword), self.location()))
                } else {
                    Ok(Token::new(TokenKind::Identifier(ident), self.location()))
                }
            }
            _ if c.is_ascii_digit() => {
                let mut num = String::from(c);
                while let Some(&c) = self.input.peek() {
                    if c.is_ascii_digit() {
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
                for c in self.input.by_ref() {
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
                    Ok(Token::new(TokenKind::HashHash, self.location()))
                } else {
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Hash, self.location()))
                }
            }
            '.' => {
                if self.input.peek() == Some(&'.') {
                    self.input.next();
                    if self.input.peek() == Some(&'.') {
                        self.input.next();
                        self.at_start_of_line = false;
                        return Ok(Token::new(TokenKind::Ellipsis, self.location()));
                    }
                    // This is a bit of a hack. A better solution would be to have a buffer.
                    // We are effectively putting the dots back into the stream.
                    // This is not yet implemented.
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Dot, self.location()))
            }
            '+' => {
                self.at_start_of_line = false;
                if let Some(&'+') = self.input.peek() {
                    self.input.next();
                    Ok(Token::new(TokenKind::PlusPlus, self.location()))
                } else {
                    Ok(Token::new(TokenKind::Plus, self.location()))
                }
            }
            '-' => {
                self.at_start_of_line = false;
                if let Some(&'-') = self.input.peek() {
                    self.input.next();
                    Ok(Token::new(TokenKind::MinusMinus, self.location()))
                } else if let Some(&'>') = self.input.peek() {
                    self.input.next();
                    Ok(Token::new(TokenKind::Arrow, self.location()))
                } else {
                    Ok(Token::new(TokenKind::Minus, self.location()))
                }
            }
            '*' => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Star, self.location()))
            }
            '|' => {
                self.at_start_of_line = false;
                if let Some(&'|') = self.input.peek() {
                    self.input.next();
                    Ok(Token::new(TokenKind::PipePipe, self.location()))
                } else {
                    Ok(Token::new(TokenKind::Pipe, self.location()))
                }
            }
            '&' => {
                self.at_start_of_line = false;
                if let Some(&'&') = self.input.peek() {
                    self.input.next();
                    Ok(Token::new(TokenKind::AmpersandAmpersand, self.location()))
                } else {
                    Ok(Token::new(TokenKind::Ampersand, self.location()))
                }
            }
            '^' => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Caret, self.location()))
            }
            '~' => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Tilde, self.location()))
            }
            '!' => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Bang, self.location()))
            }
            '?' => {
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Question, self.location()))
            }
            '/' => {
                self.at_start_of_line = false;
                if let Some(&'/') = self.input.peek() {
                    self.input.next();
                    let mut comment = String::new();
                    while let Some(&c) = self.input.peek() {
                        if c == '\n' {
                            break;
                        }
                        comment.push(self.input.next().unwrap());
                    }
                    Ok(Token::new(TokenKind::Comment(comment), self.location()))
                } else if let Some(&'*') = self.input.peek() {
                    self.input.next();
                    let mut comment = String::new();
                    while let Some(c) = self.input.next() {
                        if c == '*'
                            && let Some(&'/') = self.input.peek()
                        {
                            self.input.next();
                            break;
                        }
                        comment.push(c);
                    }
                    Ok(Token::new(TokenKind::Comment(comment), self.location()))
                } else {
                    Ok(Token::new(TokenKind::Slash, self.location()))
                }
            }
            _ if c.is_ascii_punctuation() => {
                self.at_start_of_line = false;
                let kind = match c {
                    '(' => TokenKind::LeftParen,
                    ')' => TokenKind::RightParen,
                    '{' => TokenKind::LeftBrace,
                    '}' => TokenKind::RightBrace,
                    '[' => TokenKind::LeftBracket,
                    ']' => TokenKind::RightBracket,
                    ';' => TokenKind::Semicolon,
                    ':' => TokenKind::Colon,
                    ',' => TokenKind::Comma,
                    '=' => TokenKind::Equal,
                    '<' => TokenKind::LessThan,
                    '>' => TokenKind::GreaterThan,
                    _ => return Err(PreprocessorError::UnexpectedChar(c)),
                };
                Ok(Token::new(kind, self.location()))
            }
            _ => Err(PreprocessorError::UnexpectedChar(c)),
        }
    }

    /// Reads a preprocessor directive.
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
        let kind = match directive.as_str() {
            "if" => DirectiveKind::If,
            "else" => DirectiveKind::Else,
            "elif" => DirectiveKind::Elif,
            "endif" => DirectiveKind::Endif,
            "ifdef" => DirectiveKind::Ifdef,
            "ifndef" => DirectiveKind::Ifndef,
            "undef" => DirectiveKind::Undef,
            "error" => DirectiveKind::Error,
            "line" => DirectiveKind::Line,
            "include" => DirectiveKind::Include,
            "define" => DirectiveKind::Define,
            "pragma" => return self.next_token(),
            _ => return Err(PreprocessorError::UnknownDirective(directive)),
        };
        Ok(Token::new(TokenKind::Directive(kind), self.location()))
    }

    /// Returns the current location in the source file.
    fn location(&self) -> SourceLocation {
        SourceLocation {
            file: self.file,
            line: self.line,
        }
    }
}
