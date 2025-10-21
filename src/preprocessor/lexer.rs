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
    verbose: bool,
}

impl<'a> Lexer<'a> {
    /// Creates a new `Lexer`.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to tokenize.
    /// * `file` - The name of the file being tokenized.
    /// * `verbose` - Whether to enable verbose debug output.
    pub fn new(input: &'a str, file: FileId, verbose: bool) -> Self {
        Lexer {
            input: input.chars().peekable(),
            at_start_of_line: true,
            line: 1,
            file,
            verbose,
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
            _ if c.is_ascii_punctuation() && c != '#' => {
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
                    '=' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            TokenKind::EqualEqual
                        } else {
                            TokenKind::Equal
                        }
                    }
                    '!' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            return Ok(Token::new(TokenKind::BangEqual, self.location()));
                        } else {
                            TokenKind::Bang
                        }
                    }
                    '<' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            return Ok(Token::new(TokenKind::LessThanEqual, self.location()));
                        } else {
                            TokenKind::LessThan
                        }
                    }
                    '>' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            return Ok(Token::new(TokenKind::GreaterThanEqual, self.location()));
                        } else {
                            TokenKind::GreaterThan
                        }
                    }
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

        if self.verbose {
            eprintln!(
                "[DEBUG] read_directive called: at_start_of_line={}, line={}",
                self.at_start_of_line, self.line
            );
        }

        // Check if we've reached the end of input before trying to read directive
        if let Some(&c) = self.input.peek() {
            if self.verbose {
                eprintln!("[DEBUG] First character after #: '{}'", c);
            }
            if c.is_alphabetic() {
                directive.push(self.input.next().unwrap());
                if self.verbose {
                    eprintln!("[DEBUG] Started reading directive with '{}'", c);
                }
                while let Some(&c) = self.input.peek() {
                    if c.is_alphabetic() || c.is_ascii_digit() || c == '_' {
                        directive.push(self.input.next().unwrap());
                        if self.verbose {
                            eprintln!("[DEBUG] Added '{}' to directive, now: '{}'", c, directive);
                        }
                    } else {
                        if self.verbose {
                            eprintln!("[DEBUG] Stopping directive at non-alphabetic '{}'", c);
                        }
                        break;
                    }
                }
            } else if c.is_whitespace() {
                // Skip whitespace after # and continue reading directive
                if self.verbose {
                    eprintln!("[DEBUG] Skipping whitespace after # on line {}", self.line);
                }
                // Skip whitespace characters
                while let Some(&c) = self.input.peek() {
                    if c.is_whitespace() && c != '\n' {
                        self.input.next();
                        if self.verbose {
                            eprintln!("[DEBUG] Skipped whitespace '{}'", c);
                        }
                    } else {
                        break;
                    }
                }
                // Now try to read the directive name
                if let Some(&c) = self.input.peek() {
                    if c.is_alphabetic() {
                        directive.push(self.input.next().unwrap());
                        if self.verbose {
                            eprintln!("[DEBUG] Started reading directive with '{}'", c);
                        }
                        while let Some(&c) = self.input.peek() {
                            if c.is_alphabetic() || c.is_ascii_digit() || c == '_' {
                                directive.push(self.input.next().unwrap());
                                if self.verbose {
                                    eprintln!(
                                        "[DEBUG] Added '{}' to directive, now: '{}'",
                                        c, directive
                                    );
                                }
                            } else {
                                if self.verbose {
                                    eprintln!(
                                        "[DEBUG] Stopping directive at non-alphabetic '{}'",
                                        c
                                    );
                                }
                                break;
                            }
                        }
                    } else {
                        // If after skipping whitespace we don't find alphabetic character, it's invalid
                        if self.verbose {
                            eprintln!("[DEBUG] No directive name after whitespace: '{}'", c);
                        }
                        return Err(PreprocessorError::UnknownDirective("".to_string()));
                    }
                } else {
                    // End of input reached
                    if self.verbose {
                        eprintln!("[DEBUG] End of input after whitespace");
                    }
                    return Err(PreprocessorError::UnknownDirective("".to_string()));
                }
            } else {
                // If the first character after # is not alphabetic or whitespace, it's not a valid directive
                if self.verbose {
                    eprintln!("[DEBUG] Invalid directive start: '{}'", c);
                }
                return Err(PreprocessorError::UnknownDirective("".to_string()));
            }
        } else {
            // End of input reached
            if self.verbose {
                eprintln!("[DEBUG] End of input reached while reading directive");
            }
            return Err(PreprocessorError::UnknownDirective("".to_string()));
        }

        if self.verbose {
            eprintln!(
                "[DEBUG] read_directive: directive='{}', at_start_of_line={}, line={}",
                directive, self.at_start_of_line, self.line
            );
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
            "warning" => DirectiveKind::Warning,
            "pragma" => {
                // Handle pragma by reading the rest of the line as a directive
                // For now, treat it as an unknown directive to avoid parsing issues
                if self.verbose {
                    eprintln!("[DEBUG] Pragma directive encountered, treating as unknown");
                }
                return Err(PreprocessorError::UnknownDirective("pragma".to_string()));
            }
            _ => {
                if self.verbose {
                    eprintln!("[DEBUG] Unknown directive '{}' encountered", directive);
                    eprintln!(
                        "[DEBUG] Available directives: if, else, elif, endif, ifdef, ifndef, undef, error, line, include, define, pragma"
                    );
                }
                return Err(PreprocessorError::UnknownDirective(directive));
            }
        };
        if self.verbose {
            eprintln!("[DEBUG] Successfully parsed directive: {:?}", kind);
        }
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
