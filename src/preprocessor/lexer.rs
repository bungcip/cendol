use crate::file::FileId;
use crate::preprocessor::error::PreprocessorError;
use crate::preprocessor::token::{DirectiveKind, SourceLocation, SourceSpan, Token, TokenKind};
use std::iter::Peekable;
use std::str::Chars;

/// A lexer for the C preprocessor.
pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    at_start_of_line: bool,
    line: u32,
    column: u32,
    file: FileId,
    start_line: u32,
    start_column: u32,
}

impl<'a> Lexer<'a> {
    /// Creates a new `Lexer`.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to tokenize.
    /// * `file` - The name of the file being tokenized.
    /// * `verbose` - Whether to enable verbose debug output.
    pub fn new(input: &'a str, file: FileId) -> Self {
        Lexer {
            input: input.chars().peekable(),
            at_start_of_line: true,
            line: 1,
            column: 1,
            file,
            start_line: 1,
            start_column: 1,
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
            None => return Ok(Token::new(TokenKind::Eof, self.current_span())),
        };

        // Track the starting position of this token
        self.start_line = self.line;
        self.start_column = self.column;

        match c {
            '\\' => {
                if let Some(&'\n') = self.input.peek() {
                    self.input.next();
                    self.consume_char('\n');
                    self.next_token()
                } else {
                    self.consume_char(c);
                    Ok(Token::new(TokenKind::Backslash, self.current_span()))
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
                    self.current_span(),
                ))
            }
            '\n' => {
                self.consume_char(c);
                self.at_start_of_line = true; // Explicitly set this
                Ok(Token::new(TokenKind::Newline, self.current_span()))
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
                    Ok(Token::new(TokenKind::Keyword(keyword), self.current_span()))
                } else {
                    Ok(Token::new(
                        TokenKind::Identifier(ident),
                        self.current_span(),
                    ))
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
                // Handle suffixes for long and unsigned
                if let Some(&c) = self.input.peek()
                    && (c == 'L' || c == 'U' || c == 'l' || c == 'u')
                {
                    num.push(self.input.next().unwrap());
                    self.consume_char(c);
                    // Handle LL or UU
                    if let Some(&c) = self.input.peek() {
                        if ((c == 'L' || c == 'l') && num.ends_with('L') || num.ends_with('l'))
                            || ((c == 'U' || c == 'u') && num.ends_with('U') || num.ends_with('u'))
                        {
                            num.push(self.input.next().unwrap());
                            self.consume_char(c);
                        }
                    }
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Number(num), self.current_span()))
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
                Ok(Token::new(TokenKind::String(s), self.current_span()))
            }
            '\'' => {
                let mut s = String::new();
                self.consume_char(c);
                let mut chars = Vec::new();
                for c in self.input.by_ref() {
                    if c == '\'' {
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
                Ok(Token::new(TokenKind::Char(s), self.current_span()))
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
                    Ok(Token::new(TokenKind::HashHash, self.current_span()))
                } else {
                    self.consume_char(c);
                    self.at_start_of_line = false;
                    Ok(Token::new(TokenKind::Hash, self.current_span()))
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
                        return Ok(Token::new(TokenKind::Ellipsis, self.current_span()));
                    }
                    // This is a bit of a hack. A better solution would be to have a buffer.
                    // We are effectively putting the dots back into the stream.
                    // This is not yet implemented.
                }
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Dot, self.current_span()))
            }
            '+' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::PlusEqual, self.current_span()))
                } else if let Some(&'+') = self.input.peek() {
                    self.input.next();
                    self.consume_char('+');
                    Ok(Token::new(TokenKind::PlusPlus, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Plus, self.current_span()))
                }
            }
            '-' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::MinusEqual, self.current_span()))
                } else if let Some(&'-') = self.input.peek() {
                    self.input.next();
                    self.consume_char('-');
                    Ok(Token::new(TokenKind::MinusMinus, self.current_span()))
                } else if let Some(&'>') = self.input.peek() {
                    self.input.next();
                    self.consume_char('>');
                    Ok(Token::new(TokenKind::Arrow, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Minus, self.current_span()))
                }
            }
            '*' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::AsteriskEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Star, self.current_span()))
                }
            }
            '/' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::SlashEqual, self.current_span()))
                } else if let Some(&'/') = self.input.peek() {
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
                    Ok(Token::new(TokenKind::Comment(comment), self.current_span()))
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
                    Ok(Token::new(TokenKind::Comment(comment), self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Slash, self.current_span()))
                }
            }
            '%' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::PercentEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Percent, self.current_span()))
                }
            }
            '|' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'|') = self.input.peek() {
                    self.input.next();
                    self.consume_char('|');
                    Ok(Token::new(TokenKind::PipePipe, self.current_span()))
                } else if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::PipeEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Pipe, self.current_span()))
                }
            }
            '&' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'&') = self.input.peek() {
                    self.input.next();
                    self.consume_char('&');
                    Ok(Token::new(
                        TokenKind::AmpersandAmpersand,
                        self.current_span(),
                    ))
                } else if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::AmpersandEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Ampersand, self.current_span()))
                }
            }
            '^' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::CaretEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Caret, self.current_span()))
                }
            }
            '~' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Tilde, self.current_span()))
            }
            '!' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::BangEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Bang, self.current_span()))
                }
            }
            '?' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Question, self.current_span()))
            }
            '=' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::EqualEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::Equal, self.current_span()))
                }
            }
            '<' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'<') = self.input.peek() {
                    self.input.next();
                    self.consume_char('<');
                    if let Some(&'=') = self.input.peek() {
                        self.input.next();
                        self.consume_char('=');
                        Ok(Token::new(
                            TokenKind::LessThanLessThanEqual,
                            self.current_span(),
                        ))
                    } else {
                        Ok(Token::new(TokenKind::LessThanLessThan, self.current_span()))
                    }
                } else if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::LessThanEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::LessThan, self.current_span()))
                }
            }
            '>' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                if let Some(&'>') = self.input.peek() {
                    self.input.next();
                    self.consume_char('>');
                    if let Some(&'=') = self.input.peek() {
                        self.input.next();
                        self.consume_char('=');
                        Ok(Token::new(
                            TokenKind::GreaterThanGreaterThanEqual,
                            self.current_span(),
                        ))
                    } else {
                        Ok(Token::new(
                            TokenKind::GreaterThanGreaterThan,
                            self.current_span(),
                        ))
                    }
                } else if let Some(&'=') = self.input.peek() {
                    self.input.next();
                    self.consume_char('=');
                    Ok(Token::new(TokenKind::GreaterThanEqual, self.current_span()))
                } else {
                    Ok(Token::new(TokenKind::GreaterThan, self.current_span()))
                }
            }
            ';' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Semicolon, self.current_span()))
            }
            ':' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Colon, self.current_span()))
            }
            ',' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::Comma, self.current_span()))
            }
            '(' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::LeftParen, self.current_span()))
            }
            ')' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::RightParen, self.current_span()))
            }
            '{' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::LeftBrace, self.current_span()))
            }
            '}' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::RightBrace, self.current_span()))
            }
            '[' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::LeftBracket, self.current_span()))
            }
            ']' => {
                self.consume_char(c);
                self.at_start_of_line = false;
                Ok(Token::new(TokenKind::RightBracket, self.current_span()))
            }
            _ => Err(PreprocessorError::UnexpectedChar(c)),
        }
    }

    /// Reads a preprocessor directive.
    fn read_directive(&mut self) -> Result<Token, PreprocessorError> {
        let mut directive = String::new();

        // Check if we've reached the end of input before trying to read directive
        if let Some(&c) = self.input.peek() {
            if c.is_alphabetic() {
                directive.push(self.input.next().unwrap());
                while let Some(&c) = self.input.peek() {
                    if c.is_alphabetic() || c.is_ascii_digit() || c == '_' {
                        directive.push(self.input.next().unwrap());
                    } else {
                        break;
                    }
                }
            } else if c.is_whitespace() {
                // Skip whitespace after # and continue reading directive
                // Skip whitespace characters
                while let Some(&c) = self.input.peek() {
                    if c.is_whitespace() && c != '\n' {
                        self.input.next();
                    } else {
                        break;
                    }
                }
                // Now try to read the directive name
                if let Some(&c) = self.input.peek() {
                    if c.is_alphabetic() {
                        directive.push(self.input.next().unwrap());
                        while let Some(&c) = self.input.peek() {
                            if c.is_alphabetic() || c.is_ascii_digit() || c == '_' {
                                directive.push(self.input.next().unwrap());
                            } else {
                                break;
                            }
                        }
                    } else {
                        // If after skipping whitespace we don't find alphabetic character, it's invalid
                        return Err(PreprocessorError::UnknownDirective("".to_string()));
                    }
                } else {
                    // End of input reached
                    return Err(PreprocessorError::UnknownDirective("".to_string()));
                }
            } else {
                // If the first character after # is not alphabetic or whitespace, it's not a valid directive
                return Err(PreprocessorError::UnknownDirective("".to_string()));
            }
        } else {
            // End of input reached
            return Err(PreprocessorError::UnknownDirective("".to_string()));
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
                return Err(PreprocessorError::UnknownDirective("pragma".to_string()));
            }
            _ => {
                return Err(PreprocessorError::UnknownDirective(directive));
            }
        };
        Ok(Token::new(TokenKind::Directive(kind), self.current_span()))
    }

    /// Returns the current location in the source file.
    fn current_location(&self) -> SourceLocation {
        SourceLocation::new(self.file, self.line, self.column)
    }

    /// Returns the current span from start to current.
    fn current_span(&self) -> SourceSpan {
        SourceSpan::new(
            self.file,
            SourceLocation::new(self.file, self.start_line, self.start_column),
            self.current_location(),
        )
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
