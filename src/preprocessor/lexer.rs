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
    column: u32,
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
            column: 1,
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

        // Track the starting position of this token
        let start_location = self.location();

        match c {
            '\\' => {
                if let Some(&'\n') = self.input.peek() {
                    self.input.next();
                    self.consume_char('\n');
                    self.next_token()
                } else {
                    self.consume_char(c);
                    Ok(Token::new(TokenKind::Backslash, start_location))
                }
            }
            ' ' | '\t' | '\r' => {
                let mut whitespace = String::from(c);
                self.consume_char(c);
                while let Some(&c) = self.input.peek() {
                    if c == ' ' || c == '\t' || c == '\r' {
                        whitespace.push(self.input.next().unwrap());
                        self.consume_char(c);
                    } else {
                        break;
                    }
                }
                Ok(Token::new(
                    TokenKind::Whitespace(whitespace),
                    start_location,
                ))
            }
            '\n' => {
                self.consume_char(c);
                self.at_start_of_line = true; // Explicitly set this
                Ok(Token::new(TokenKind::Newline, start_location))
            }
            _ if c.is_alphabetic() || c == '_' => {
                let mut ident = String::from(c);
                self.consume_char(c);
                while let Some(&c) = self.input.peek() {
                    if c.is_alphanumeric() || c == '_' {
                        ident.push(self.input.next().unwrap());
                        self.consume_char(c);
                    } else {
                        break;
                    }
                }
                self.at_start_of_line = false;
                if let Ok(keyword) = ident.parse() {
                    Ok(Token::new(TokenKind::Keyword(keyword), start_location))
                } else {
                    Ok(Token::new(TokenKind::Identifier(ident), start_location))
                }
            }
            _ if c.is_ascii_digit() => {
                let mut num = String::from(c);
                self.consume_char(c);
                while let Some(&c) = self.input.peek() {
                    if c.is_ascii_digit() {
                        num.push(self.input.next().unwrap());
                        self.consume_char(c);
                    } else {
                        break;
                    }
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Number(num), start_location))
            }
            '"' => {
                let mut s = String::new();
                self.consume_char(c);
                let mut chars = Vec::new();
                for c in self.input.by_ref() {
                    if c == '"' {
                        break;
                    }
                    s.push(c);
                    chars.push(c);
                }
                // Consume all the characters we collected
                for ch in chars {
                    self.consume_char(ch);
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::String(s), start_location))
            }
            '#' => {
                if self.at_start_of_line {
                    self.consume_char(c);
                    self.read_directive()
                } else if let Some(&'#') = self.input.peek() {
                    self.consume_char(c);
                    self.input.next();
                    self.consume_char('#');
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::HashHash, start_location))
                } else {
                    self.consume_char(c);
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Hash, start_location))
                }
            }
            '.' => {
                self.consume_char(c);
                if self.input.peek() == Some(&'.') {
                    self.input.next();
                    self.consume_char('.');
                    if self.input.peek() == Some(&'.') {
                        self.input.next();
                        self.consume_char('.');
                        self.at_start_of_line = false;
                        return Ok(Token::new(TokenKind::Ellipsis, start_location));
                    }
                    // This is a bit of a hack. A better solution would be to have a buffer.
                    // We are effectively putting the dots back into the stream.
                    // This is not yet implemented.
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Dot, start_location))
            }
            '+' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'+') = self.input.peek() {
                    self.input.next();
                    self.consume_char('+');
                    Ok(Token::new(TokenKind::PlusPlus, start_location))
                } else {
                    Ok(Token::new(TokenKind::Plus, start_location))
                }
            }
            '-' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'-') = self.input.peek() {
                    self.input.next();
                    self.consume_char('-');
                    Ok(Token::new(TokenKind::MinusMinus, start_location))
                } else if let Some(&'>') = self.input.peek() {
                    self.input.next();
                    self.consume_char('>');
                    Ok(Token::new(TokenKind::Arrow, start_location))
                } else {
                    Ok(Token::new(TokenKind::Minus, start_location))
                }
            }
            '*' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Star, start_location))
            }
            '|' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'|') = self.input.peek() {
                    self.input.next();
                    self.consume_char('|');
                    Ok(Token::new(TokenKind::PipePipe, start_location))
                } else {
                    Ok(Token::new(TokenKind::Pipe, start_location))
                }
            }
            '&' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'&') = self.input.peek() {
                    self.input.next();
                    self.consume_char('&');
                    Ok(Token::new(TokenKind::AmpersandAmpersand, start_location))
                } else {
                    Ok(Token::new(TokenKind::Ampersand, start_location))
                }
            }
            '^' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Caret, start_location))
            }
            '~' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Tilde, start_location))
            }
            '!' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Bang, start_location))
            }
            '?' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Question, start_location))
            }
            '/' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'/') = self.input.peek() {
                    self.input.next();
                    self.consume_char('/');
                    let mut comment = String::new();
                    let mut chars = Vec::new();
                    while let Some(&c) = self.input.peek() {
                        if c == '\n' {
                            break;
                        }
                        comment.push(self.input.next().unwrap());
                        chars.push(c);
                    }
                    for ch in chars {
                        self.consume_char(ch);
                    }
                    Ok(Token::new(TokenKind::Comment(comment), start_location))
                } else if let Some(&'*') = self.input.peek() {
                    self.input.next();
                    self.consume_char('*');
                    let mut comment = String::new();
                    let mut chars = Vec::new();
                    while let Some(c) = self.input.next() {
                        if c == '*'
                            && let Some(&'/') = self.input.peek()
                        {
                            self.input.next();
                            break;
                        }
                        comment.push(c);
                        chars.push(c);
                    }
                    for ch in chars {
                        self.consume_char(ch);
                    }
                    Ok(Token::new(TokenKind::Comment(comment), start_location))
                } else {
                    Ok(Token::new(TokenKind::Slash, start_location))
                }
            }
            _ if c.is_ascii_punctuation() && c != '#' => {
                self.consume_char(c);
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
                            self.consume_char('=');
                            TokenKind::EqualEqual
                        } else {
                            TokenKind::Equal
                        }
                    }
                    '!' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            self.consume_char('=');
                            return Ok(Token::new(TokenKind::BangEqual, start_location));
                        } else {
                            TokenKind::Bang
                        }
                    }
                    '<' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            self.consume_char('=');
                            return Ok(Token::new(TokenKind::LessThanEqual, start_location));
                        } else {
                            TokenKind::LessThan
                        }
                    }
                    '>' => {
                        if let Some(&'=') = self.input.peek() {
                            self.input.next();
                            self.consume_char('=');
                            return Ok(Token::new(TokenKind::GreaterThanEqual, start_location));
                        } else {
                            TokenKind::GreaterThan
                        }
                    }
                    _ => return Err(PreprocessorError::UnexpectedChar(c)),
                };
                Ok(Token::new(kind, start_location))
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
        SourceLocation::new(self.file, self.line, self.column)
    }

    /// Consumes a character and updates position tracking.
    fn consume_char(&mut self, c: char) {
        if c == '\n' {
            self.line += 1;
            self.column = 1;
            self.at_start_of_line = true;
        } else {
            self.column += 1;
            self.at_start_of_line = false;
        }
    }
}
