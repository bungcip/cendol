use crate::file::FileManager;
use crate::preprocessor::error::PreprocessorError;
use crate::preprocessor::lexer::Lexer;
use crate::preprocessor::token::{DirectiveKind, IncludeKind, Token, TokenKind};
use chrono::Local;
use std::collections::{HashMap, HashSet};

pub mod error;
pub mod lexer;
pub mod token;

/// Represents a C macro.
#[derive(Debug, Clone)]
enum Macro {
    /// An object-like macro.
    Object {
        /// The tokens that replace the macro.
        tokens: Vec<Token>,
    },
    /// A function-like macro.
    Function {
        /// The parameters of the macro.
        parameters: Vec<String>,
        /// Whether the macro is variadic.
        _is_variadic: bool,
        /// The tokens that replace the macro.
        tokens: Vec<Token>,
    },
}

/// A preprocessor expression.
#[derive(Debug, PartialEq)]
enum Expr {
    /// A number.
    Number(i32),
    /// A variable.
    Variable(String),
    /// A unary operation.
    Unary(TokenKind, Box<Expr>),
    /// A binary operation.
    Binary(TokenKind, Box<Expr>, Box<Expr>),
    /// A ternary operation.
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
}

/// The state of a single file being preprocessed.
struct FileState {
    tokens: Vec<Token>,
    index: usize,
}

/// A C preprocessor.
pub struct Preprocessor {
    macros: HashMap<String, Macro>,
    conditional_stack: Vec<bool>,
    file_manager: FileManager,
    file_stack: Vec<FileState>,
}

impl Preprocessor {
    /// Creates a new `Preprocessor`.
    pub fn new(file_manager: FileManager) -> Self {
        Preprocessor {
            macros: HashMap::new(),
            conditional_stack: Vec::new(),
            file_manager,
            file_stack: Vec::new(),
        }
    }

    /// Preprocesses a string of C code.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to preprocess.
    ///
    /// # Returns
    ///
    /// A `Result` containing a vector of tokens, or a `PreprocessorError` if preprocessing fails.
    pub fn preprocess(
        &mut self,
        input: &str,
        filename: &str,
    ) -> Result<Vec<Token>, PreprocessorError> {
        let initial_tokens = self.tokenize(input, filename)?;
        self.file_stack.push(FileState {
            tokens: initial_tokens,
            index: 0,
        });

        let mut final_tokens = Vec::new();
        while !self.file_stack.is_empty() {
            let mut tokens = self.process_directives()?;
            self.expand_all_macros(&mut tokens)?;
            final_tokens.extend(tokens);
        }

        final_tokens.retain(|t| !matches!(t.kind, TokenKind::Whitespace(_) | TokenKind::Newline));
        Ok(final_tokens)
    }

    /// Defines a macro.
    ///
    /// # Arguments
    ///
    /// * `definition` - The macro definition string.
    pub fn define(&mut self, definition: &str) -> Result<(), PreprocessorError> {
        if definition.is_empty() {
            return Err(PreprocessorError::Generic("Empty definition".to_string()));
        }
        let parts: Vec<&str> = definition.splitn(2, '=').collect();
        let name = parts[0].to_string();
        if name.is_empty() {
            return Err(PreprocessorError::Generic(
                "Macro name must not be empty".to_string(),
            ));
        }
        let value = if parts.len() > 1 { parts[1] } else { "1" };
        let file_id = self.file_manager.open("<cmdline>")?;
        let mut lexer = Lexer::new(value, file_id);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token()?;
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }
        self.macros.insert(name, Macro::Object { tokens });
        Ok(())
    }

    /// Tokenizes an input string.
    fn tokenize(&mut self, input: &str, filename: &str) -> Result<Vec<Token>, PreprocessorError> {
        let file_id = self
            .file_manager
            .open(filename)
            .map_err(|_| PreprocessorError::FileNotFound(filename.to_string()))?;
        let mut lexer = Lexer::new(input, file_id);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token()?;
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }
        Ok(tokens)
    }

    /// Processes preprocessor directives.
    fn process_directives(&mut self) -> Result<Vec<Token>, PreprocessorError> {
        let mut final_tokens = Vec::new();
        while !self.file_stack.is_empty() {
            let file_state = self.file_stack.last_mut().unwrap();
            if file_state.index >= file_state.tokens.len() {
                if !self.conditional_stack.is_empty() {
                    return Err(PreprocessorError::UnterminatedConditional);
                }
                self.file_stack.pop();
                continue;
            }

            let token = file_state.tokens[file_state.index].clone();
            file_state.index += 1;

            let in_true_branch = self.conditional_stack.iter().all(|&x| x);

            if let TokenKind::Directive(directive) = token.kind {
                match directive {
                    DirectiveKind::If => {
                        let (condition, end) = {
                            let file_state = self.file_stack.last_mut().unwrap();
                            parse_conditional_expression(file_state.index, &file_state.tokens)?
                        };
                        let result = evaluate_expression(&condition, &self.macros)?;
                        self.conditional_stack.push(result);
                        self.file_stack.last_mut().unwrap().index = end;
                    }
                    DirectiveKind::Elif => {
                        if self.conditional_stack.is_empty() {
                            return Err(PreprocessorError::UnexpectedElif);
                        }
                        let (condition, _end) = {
                            let file_state = self.file_stack.last().unwrap();
                            parse_conditional_expression(file_state.index, &file_state.tokens)?
                        };
                        if let Some(last) = self.conditional_stack.last_mut() {
                            if !*last {
                                let result = evaluate_expression(&condition, &self.macros)?;
                                *last = result;
                            } else {
                                *last = false;
                            }
                        }
                        let file_state = self.file_stack.last_mut().unwrap();
                        file_state.index = find_next_line(file_state.index, &file_state.tokens);
                    }
                    DirectiveKind::Else => {
                        if self.conditional_stack.is_empty() {
                            return Err(PreprocessorError::UnexpectedElse);
                        }
                        if let Some(last) = self.conditional_stack.last_mut() {
                            *last = !*last;
                        }
                        let file_state = self.file_stack.last_mut().unwrap();
                        file_state.index = find_next_line(file_state.index, &file_state.tokens);
                    }
                    DirectiveKind::Endif => {
                        if self.conditional_stack.is_empty() {
                            return Err(PreprocessorError::UnexpectedEndif);
                        }
                        self.conditional_stack.pop();
                        let file_state = self.file_stack.last_mut().unwrap();
                        file_state.index = find_next_line(file_state.index, &file_state.tokens);
                    }
                    DirectiveKind::Define => {
                        if in_true_branch {
                            let mut macro_tokens = Vec::new();
                            let file_state = self.file_stack.last_mut().unwrap();
                            while file_state.index < file_state.tokens.len() {
                                if matches!(file_state.tokens[file_state.index].kind, TokenKind::Newline)
                                {
                                    break;
                                }
                                macro_tokens.push(file_state.tokens[file_state.index].clone());
                                file_state.index += 1;
                            }
                            self.handle_define(&mut macro_tokens)?;
                        }
                        let file_state = self.file_stack.last_mut().unwrap();
                        file_state.index = find_next_line(file_state.index, &file_state.tokens);
                    }
                    DirectiveKind::Ifdef => {
                        let (name, end) = {
                            let file_state = self.file_stack.last().unwrap();
                            parse_identifier(file_state.index, &file_state.tokens)?
                        };
                        self.conditional_stack.push(self.macros.contains_key(&name));
                        self.file_stack.last_mut().unwrap().index = end;
                    }
                    DirectiveKind::Ifndef => {
                        let (name, end) = {
                            let file_state = self.file_stack.last().unwrap();
                            parse_identifier(file_state.index, &file_state.tokens)?
                        };
                        self.conditional_stack
                            .push(!self.macros.contains_key(&name));
                        self.file_stack.last_mut().unwrap().index = end;
                    }
                    DirectiveKind::Undef => {
                        if in_true_branch {
                            let (name, end) = {
                                let file_state = self.file_stack.last().unwrap();
                                parse_identifier(file_state.index, &file_state.tokens)?
                            };
                            self.macros.remove(&name);
                            self.file_stack.last_mut().unwrap().index = end;
                        } else {
                            let file_state = self.file_stack.last_mut().unwrap();
                            file_state.index =
                                find_next_line(file_state.index, &file_state.tokens);
                        }
                    }
                    DirectiveKind::Error => {
                        if in_true_branch {
                            let (message, _end) = {
                                let file_state = self.file_stack.last().unwrap();
                                parse_error_message(file_state.index, &file_state.tokens)?
                            };
                            return Err(PreprocessorError::Generic(message));
                        }
                        let file_state = self.file_stack.last_mut().unwrap();
                        file_state.index = find_next_line(file_state.index, &file_state.tokens);
                    }
                    DirectiveKind::Line => {
                        if in_true_branch {
                            let (_line, _filename, end) = {
                                let file_state = self.file_stack.last().unwrap();
                                parse_line_directive(file_state.index, &file_state.tokens)?
                            };
                            self.file_stack.last_mut().unwrap().index = end;
                        } else {
                            let file_state = self.file_stack.last_mut().unwrap();
                            file_state.index =
                                find_next_line(file_state.index, &file_state.tokens);
                        }
                    }
                    DirectiveKind::Include => {
                        if in_true_branch {
                            let (filename, include_kind, end) = {
                                let file_state = self.file_stack.last().unwrap();
                                parse_include(file_state.index, &file_state.tokens)?
                            };
                            let new_tokens = self.include_file(
                                &filename,
                                include_kind,
                                token.location.file,
                            )?;
                            self.file_stack.last_mut().unwrap().index = end;
                            self.file_stack.push(FileState {
                                tokens: new_tokens,
                                index: 0,
                            });
                        } else {
                            let file_state = self.file_stack.last_mut().unwrap();
                            file_state.index =
                                find_next_line(file_state.index, &file_state.tokens);
                        }
                    }
                }
                continue;
            }

            if in_true_branch {
                final_tokens.push(token);
            }
        }

        if !self.conditional_stack.is_empty() {
            return Err(PreprocessorError::UnterminatedConditional);
        }

        Ok(final_tokens)
    }

    /// Handles a `#define` directive.
    fn handle_define(&mut self, tokens: &mut Vec<Token>) -> Result<(), PreprocessorError> {
        self.consume_whitespace(tokens);
        if tokens.is_empty() {
            return Ok(());
        }
        let name_token = tokens.remove(0);
        let name = if let TokenKind::Identifier(name) = name_token.kind {
            name
        } else {
            return Err(PreprocessorError::ExpectedIdentifierAfterDefine);
        };

        if !tokens.is_empty() && matches!(&tokens[0].kind, TokenKind::LeftParen) {
            tokens.remove(0);
            let mut parameters = Vec::new();
            let mut is_variadic = false;
            loop {
                self.consume_whitespace(tokens);
                if tokens.is_empty() {
                    return Err(PreprocessorError::UnexpectedEofInMacroParams);
                }
                if let TokenKind::RightParen = &tokens[0].kind {
                    tokens.remove(0);
                    break;
                }

                if let TokenKind::Identifier(param) = tokens[0].kind.clone() {
                    parameters.push(param);
                    tokens.remove(0);
                } else if let TokenKind::Ellipsis = &tokens[0].kind {
                    is_variadic = true;
                    parameters.push("..".to_string());
                    tokens.remove(0);
                }

                self.consume_whitespace(tokens);
                if !tokens.is_empty()
                    && let TokenKind::Comma = &tokens[0].kind
                {
                    tokens.remove(0);
                }
            }
            self.consume_whitespace(tokens);
            let body = self.read_macro_body(tokens)?;
            self.macros.insert(
                name,
                Macro::Function {
                    parameters,
                    _is_variadic: is_variadic,
                    tokens: body,
                },
            );
        } else {
            self.consume_whitespace(tokens);
            let body = self.read_macro_body(tokens)?;
            self.macros.insert(name, Macro::Object { tokens: body });
        }
        Ok(())
    }

    /// Reads the body of a macro definition.
    fn read_macro_body(
        &mut self,
        tokens: &mut Vec<Token>,
    ) -> Result<Vec<Token>, PreprocessorError> {
        let mut body = Vec::new();
        while !tokens.is_empty() {
            if let TokenKind::Newline = tokens[0].kind {
                tokens.remove(0);
                break;
            }
            body.push(tokens.remove(0));
        }
        Ok(body)
    }

    /// Consumes whitespace tokens.
    fn consume_whitespace(&mut self, tokens: &mut Vec<Token>) {
        while !tokens.is_empty() && matches!(tokens[0].kind, TokenKind::Whitespace(_)) {
            tokens.remove(0);
        }
    }

    /// Expands all macros in a token stream.
    fn expand_all_macros(&mut self, tokens: &mut Vec<Token>) -> Result<(), PreprocessorError> {
        loop {
            let mut expanded = false;
            let mut i = 0;
            while i < tokens.len() {
                if let TokenKind::Identifier(name) = &tokens[i].kind
                    && !tokens[i].hideset.contains(name)
                {
                    if name == "__LINE__" {
                        let line = tokens[i].location.line;
                        tokens[i] = Token::new(
                            TokenKind::Number(line.to_string()),
                            tokens[i].location.clone(),
                        );
                        expanded = true;
                    } else if name == "__FILE__" {
                        let file = self
                            .file_manager
                            .get_path(tokens[i].location.file)
                            .unwrap()
                            .to_str()
                            .unwrap()
                            .to_string();
                        tokens[i] = Token::new(TokenKind::String(file), tokens[i].location.clone());
                        expanded = true;
                    } else if name == "__DATE__" {
                        let date = Local::now().format("%b %-d %Y").to_string();
                        tokens[i] = Token::new(TokenKind::String(date), tokens[i].location.clone());
                        expanded = true;
                    } else if name == "__TIME__" {
                        let time = Local::now().format("%H:%M:%S").to_string();
                        tokens[i] = Token::new(TokenKind::String(time), tokens[i].location.clone());
                        expanded = true;
                    } else if let Some(macro_def) = self.macros.get(name).cloned() {
                        let (start, end, expanded_tokens) =
                            self.expand_single_macro(&tokens[i], &macro_def, i, tokens)?;
                        tokens.splice(start..end, expanded_tokens);
                        expanded = true;
                        break;
                    }
                }
                i += 1;
            }
            if !expanded {
                break;
            }
        }
        Ok(())
    }

    /// Expands a single macro.
    fn expand_single_macro(
        &mut self,
        token: &Token,
        macro_def: &Macro,
        index: usize,
        tokens: &[Token],
    ) -> Result<(usize, usize, Vec<Token>), PreprocessorError> {
        let macro_name = match &token.kind {
            TokenKind::Identifier(name) => name.clone(),
            _ => return Ok((index, index + 1, vec![token.clone()])),
        };

        match macro_def {
            Macro::Object { tokens: body } => {
                let mut new_hideset = token.hideset.clone();
                new_hideset.insert(macro_name);
                let mut expanded = body.clone();
                for t in &mut expanded {
                    t.hideset.extend(new_hideset.clone());
                }
                Ok((index, index + 1, expanded))
            }
            Macro::Function {
                parameters,
                tokens: body,
                ..
            } => {
                let mut next_idx = index + 1;
                while next_idx < tokens.len() && tokens[next_idx].kind.is_whitespace() {
                    next_idx += 1;
                }

                if next_idx >= tokens.len()
                    || !matches!(&tokens[next_idx].kind, TokenKind::LeftParen)
                {
                    return Ok((index, index + 1, vec![token.clone()]));
                }

                let (args, end_idx) = self.parse_macro_args(next_idx, tokens)?;

                let mut new_hideset = token.hideset.clone();
                new_hideset.insert(macro_name.clone());

                let mut args_with_hideset = args.clone();
                for arg in &mut args_with_hideset {
                    for token in arg {
                        token.hideset.insert(macro_name.clone());
                    }
                }

                let mut expanded =
                    self.substitute_tokens(body, parameters, &args_with_hideset, &new_hideset)?;

                for t in &mut expanded {
                    t.hideset.extend(new_hideset.clone());
                }

                self.expand_all_macros(&mut expanded)?;
                Ok((index, end_idx + 1, expanded))
            }
        }
    }

    /// Parses the arguments of a function-like macro.
    fn parse_macro_args(
        &self,
        start_idx: usize,
        tokens: &[Token],
    ) -> Result<(Vec<Vec<Token>>, usize), PreprocessorError> {
        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut paren_level = 1;
        let mut i = start_idx + 1;
        while i < tokens.len() {
            let token = &tokens[i];
            match &token.kind {
                TokenKind::LeftParen => {
                    paren_level += 1;
                    current_arg.push(token.clone());
                }
                TokenKind::RightParen => {
                    paren_level -= 1;
                    if paren_level == 0 {
                        if !current_arg.is_empty() {
                            args.push(self.trim_whitespace(current_arg));
                        }
                        return Ok((args, i));
                    }
                    current_arg.push(token.clone());
                }
                TokenKind::Comma if paren_level == 1 => {
                    args.push(self.trim_whitespace(current_arg));
                    current_arg = Vec::new();
                }
                _ => current_arg.push(token.clone()),
            }
            i += 1;
        }
        Err(PreprocessorError::UnexpectedEofInMacroArgs)
    }

    /// Substitutes macro parameters with arguments.
    fn substitute_tokens(
        &mut self,
        body: &[Token],
        parameters: &[String],
        args: &[Vec<Token>],
        hideset: &HashSet<String>,
    ) -> Result<Vec<Token>, PreprocessorError> {
        let mut result = Vec::new();
        let mut i = 0;
        while i < body.len() {
            let token = &body[i];
            if let TokenKind::Hash = &token.kind {
                i += 1;
                if i < body.len()
                    && let TokenKind::Identifier(param_name) = &body[i].kind
                    && let Some(idx) = parameters.iter().position(|p| p == param_name)
                {
                    if idx < args.len() {
                        let arg_tokens = &args[idx];
                        let stringified = arg_tokens
                            .iter()
                            .map(|t| t.kind.to_string())
                            .collect::<String>();
                        result.push(Token::new(
                            TokenKind::String(stringified),
                            token.location.clone(),
                        ));
                    }
                    i += 1;
                    continue;
                }
            } else if let TokenKind::HashHash = &token.kind {
                let mut lhs: Token = result.pop().unwrap();
                while lhs.kind.is_whitespace() {
                    lhs = result.pop().unwrap();
                }

                i += 1;
                while i < body.len() && body[i].kind.is_whitespace() {
                    i += 1;
                }

                let rhs_tokens = if i < body.len() {
                    let next_token = &body[i];
                    let res = if let TokenKind::Identifier(name) = &next_token.kind {
                        if let Some(idx) = parameters.iter().position(|p| p == name) {
                            if idx < args.len() {
                                args[idx].clone()
                            } else {
                                vec![next_token.clone()]
                            }
                        } else {
                            vec![next_token.clone()]
                        }
                    } else {
                        vec![next_token.clone()]
                    };
                    i += 1;
                    res
                } else {
                    return Err(PreprocessorError::HashHashAtEndOfMacro);
                };

                let rhs_str = rhs_tokens
                    .iter()
                    .map(|t| t.kind.to_string())
                    .collect::<String>();
                let pasted_str = format!("{}{}", lhs.kind, rhs_str);
                let mut lexer = Lexer::new(&pasted_str, lhs.location.file);
                let mut new_token = lexer.next_token()?;
                if !matches!(new_token.kind, TokenKind::Eof) {
                    let mut new_hideset = lhs.hideset.clone();
                    new_token.location = lhs.location.clone();
                    for t in &rhs_tokens {
                        new_hideset.extend(t.hideset.clone());
                    }
                    new_token.hideset = new_hideset;
                    result.push(new_token);
                }
                continue;
            }
            if let TokenKind::Identifier(name) = &token.kind {
                if let Some(idx) = parameters.iter().position(|p| p == name) {
                    if idx < args.len() {
                        let mut arg_tokens = args[idx].clone();
                        for t in &mut arg_tokens {
                            t.hideset.extend(hideset.clone());
                        }
                        result.extend(arg_tokens);
                    }
                    i += 1;
                    continue;
                } else if name == "__VA_ARGS__" {
                    let vararg_start = parameters.iter().position(|p| p == "..");
                    if let Some(vararg_start) = vararg_start
                        && vararg_start < args.len()
                    {
                        for (i, arg) in args[vararg_start..].iter().enumerate() {
                            result.extend(arg.clone());
                            if i < args.len() - vararg_start - 1 {
                                result.push(Token::new(TokenKind::Comma, token.location.clone()));
                            }
                        }
                    }
                    i += 1;
                    continue;
                }
            }
            result.push(token.clone());
            i += 1;
        }
        Ok(result)
    }

    /// Trims whitespace from the beginning and end of a token vector.
    fn trim_whitespace(&self, mut tokens: Vec<Token>) -> Vec<Token> {
        if let Some(first) = tokens.first()
            && first.kind.is_whitespace()
        {
            tokens.remove(0);
        }
        if let Some(last) = tokens.last()
            && last.kind.is_whitespace()
        {
            tokens.pop();
        }
        tokens
    }

    /// Includes a file.
    fn include_file(
        &mut self,
        filename: &str,
        kind: IncludeKind,
        includer: crate::file::FileId,
    ) -> Result<Vec<Token>, PreprocessorError> {
        let file_id = self
            .file_manager
            .open_include(filename, kind, includer)
            .map_err(|_| PreprocessorError::FileNotFound(filename.to_string()))?;
        let content = self
            .file_manager
            .read(file_id)
            .map_err(|_| PreprocessorError::FileNotFound(filename.to_string()))?;
        let mut lexer = Lexer::new(&content, file_id);
        let mut tokens = Vec::new();
        loop {
            let token = lexer.next_token()?;
            if let TokenKind::Eof = token.kind {
                break;
            }
            tokens.push(token);
        }
        Ok(tokens)
    }
}

/// Parses an include directive.
fn parse_include(
    start_idx: usize,
    tokens: &[Token],
) -> Result<(String, IncludeKind, usize), PreprocessorError> {
    let mut i = start_idx;
    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    if i < tokens.len() {
        if let TokenKind::String(s) = &tokens[i].kind {
            return Ok((s.clone(), IncludeKind::Local, i + 1));
        }

        if let TokenKind::LessThan = &tokens[i].kind {
            i += 1;
            let mut filename = String::new();
            while i < tokens.len() {
                if let TokenKind::GreaterThan = &tokens[i].kind {
                    return Ok((filename, IncludeKind::System, i + 1));
                }
                filename.push_str(&tokens[i].kind.to_string());
                i += 1;
            }
        }
    }

    Err(PreprocessorError::InvalidInclude)
}

/// Parses a conditional expression.
fn parse_conditional_expression(
    start_idx: usize,
    tokens: &[Token],
) -> Result<(Vec<Token>, usize), PreprocessorError> {
    let mut condition = Vec::new();
    let mut i = start_idx;
    while i < tokens.len() {
        if let TokenKind::Newline = tokens[i].kind {
            break;
        }
        if !tokens[i].kind.is_whitespace() {
            condition.push(tokens[i].clone());
        }
        i += 1;
    }
    Ok((condition, i))
}

/// Evaluates a conditional expression.
fn evaluate_expression(
    tokens: &[Token],
    macros: &HashMap<String, Macro>,
) -> Result<bool, PreprocessorError> {
    if tokens.is_empty() {
        return Ok(false);
    }
    let expr = parse_expr(tokens)?;
    let result = eval(&expr, macros)?;
    Ok(result != 0)
}

fn eval(expr: &Expr, macros: &HashMap<String, Macro>) -> Result<i32, PreprocessorError> {
    match expr {
        Expr::Number(n) => Ok(*n),
        Expr::Variable(s) => Ok(if macros.contains_key(s) { 1 } else { 0 }),
        Expr::Unary(op, rhs) => {
            let rhs = eval(rhs, macros)?;
            match op {
                TokenKind::Minus => Ok(-rhs),
                TokenKind::Bang => Ok(if rhs == 0 { 1 } else { 0 }),
                _ => Err(PreprocessorError::Generic("Invalid unary operator".to_string())),
            }
        }
        Expr::Binary(op, lhs, rhs) => {
            let lhs = eval(lhs, macros)?;
            let rhs = eval(rhs, macros)?;
            match op {
                TokenKind::Plus => Ok(lhs + rhs),
                TokenKind::Minus => Ok(lhs - rhs),
                TokenKind::Star => Ok(lhs * rhs),
                TokenKind::Slash => Ok(lhs / rhs),
                TokenKind::PipePipe => Ok(if lhs != 0 || rhs != 0 { 1 } else { 0 }),
                TokenKind::AmpersandAmpersand => Ok(if lhs != 0 && rhs != 0 { 1 } else { 0 }),
                TokenKind::Pipe => Ok(lhs | rhs),
                TokenKind::Caret => Ok(lhs ^ rhs),
                TokenKind::Ampersand => Ok(lhs & rhs),
                TokenKind::Equal => Ok(if lhs == rhs { 1 } else { 0 }),
                TokenKind::Bang => Ok(if lhs != rhs { 1 } else { 0 }),
                TokenKind::LessThan => Ok(if lhs < rhs { 1 } else { 0 }),
                TokenKind::GreaterThan => Ok(if lhs > rhs { 1 } else { 0 }),
                _ => Err(PreprocessorError::Generic("Invalid binary operator".to_string())),
            }
        }
        Expr::Ternary(cond, then, else_) => {
            let cond = eval(cond, macros)?;
            if cond != 0 {
                eval(then, macros)
            } else {
                eval(else_, macros)
            }
        }
    }
}

/// Finds the index of the next newline token.
fn find_next_line(start_idx: usize, tokens: &[Token]) -> usize {
    let mut i = start_idx;
    while i < tokens.len() {
        if matches!(tokens[i].kind, TokenKind::Newline) {
            return i + 1;
        }
        i += 1;
    }
    i
}

/// Parses an identifier.
fn parse_identifier(
    start_idx: usize,
    tokens: &[Token],
) -> Result<(String, usize), PreprocessorError> {
    let mut i = start_idx;
    while i < tokens.len() {
        if let TokenKind::Identifier(name) = &tokens[i].kind {
            return Ok((name.clone(), i + 1));
        }
        i += 1;
    }
    Err(PreprocessorError::ExpectedIdentifierAfterDefine)
}

/// Parses an error message.
fn parse_error_message(
    start_idx: usize,
    tokens: &[Token],
) -> Result<(String, usize), PreprocessorError> {
    let mut message = String::new();
    let mut i = start_idx;
    while i < tokens.len() {
        if matches!(tokens[i].kind, TokenKind::Newline) {
            return Ok((message, i));
        }
        message.push_str(&tokens[i].kind.to_string());
        i += 1;
    }
    Ok((message, i))
}

/// Parses a line directive.
fn parse_line_directive(
    start_idx: usize,
    tokens: &[Token],
) -> Result<(u32, Option<String>, usize), PreprocessorError> {
    let mut i = start_idx;
    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    let line = if let TokenKind::Number(s) = &tokens[i].kind {
        s.parse().unwrap()
    } else {
        return Err(PreprocessorError::Generic(
            "Expected line number".to_string(),
        ));
    };
    i += 1;

    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    let filename = if i < tokens.len() {
        if let TokenKind::String(s) = &tokens[i].kind {
            i += 1;
            Some(s.clone())
        } else {
            None
        }
    } else {
        None
    };

    while i < tokens.len() {
        if matches!(tokens[i].kind, TokenKind::Newline) {
            return Ok((line, filename, i));
        }
        i += 1;
    }

    Ok((line, filename, i))
}

fn parse_expr(tokens: &[Token]) -> Result<Expr, PreprocessorError> {
    let mut i = 0;
    parse_expr_bp(tokens, &mut i, 0)
}

fn parse_expr_bp(
    tokens: &[Token],
    i: &mut usize,
    min_bp: u8,
) -> Result<Expr, PreprocessorError> {
    // dbg!(tokens);
    while tokens[*i].kind.is_whitespace() {
        *i += 1;
    }
    let op = &tokens[*i].kind;
    let mut lhs = match op {
        TokenKind::Number(n) => {
            *i += 1;
            Expr::Number(n.parse().unwrap())
        }
        TokenKind::Identifier(s) => {
            *i += 1;
            if s == "defined" {
                let name = if let TokenKind::LeftParen = &tokens[*i].kind {
                    *i += 1;
                    let name = if let TokenKind::Identifier(name) = &tokens[*i].kind {
                        name.clone()
                    } else {
                        return Err(PreprocessorError::Generic("Expected identifier".to_string()));
                    };
                    *i += 1;
                    if !matches!(tokens[*i].kind, TokenKind::RightParen) {
                        return Err(PreprocessorError::Generic("Expected ')'".to_string()));
                    }
                    *i += 1;
                    name
                } else if let TokenKind::Identifier(name) = &tokens[*i].kind {
                    *i += 1;
                    name.clone()
                } else {
                    return Err(PreprocessorError::Generic("Expected identifier".to_string()));
                };
                Expr::Variable(name)
            } else {
                Expr::Variable(s.clone())
            }
        }
        TokenKind::Minus | TokenKind::Bang => {
            *i += 1;
            let rhs = parse_expr_bp(tokens, i, 5)?;
            Expr::Unary(op.clone(), Box::new(rhs))
        }
        TokenKind::LeftParen => {
            *i += 1;
            let expr = parse_expr_bp(tokens, i, 0)?;
            if !matches!(tokens[*i].kind, TokenKind::RightParen) {
                return Err(PreprocessorError::Generic("Expected ')'".to_string()));
            }
            *i += 1;
            expr
        }
        _ => return Err(PreprocessorError::Generic("Expected expression".to_string())),
    };

    loop {
        if *i >= tokens.len() {
            break;
        }

        while tokens[*i].kind.is_whitespace() {
            *i += 1;
        }

        let op = &tokens[*i].kind;
        let (l_bp, r_bp) = match op {
            TokenKind::PipePipe => (1, 2),
            TokenKind::AmpersandAmpersand => (3, 4),
            TokenKind::Pipe => (5, 6),
            TokenKind::Caret => (7, 8),
            TokenKind::Ampersand => (9, 10),
            TokenKind::Equal | TokenKind::Bang => (11, 12),
            TokenKind::LessThan | TokenKind::GreaterThan => (13, 14),
            TokenKind::Plus | TokenKind::Minus => (15, 16),
            TokenKind::Star | TokenKind::Slash => (17, 18),
            _ => break,
        };

        if l_bp < min_bp {
            break;
        }

        *i += 1;
        let rhs = parse_expr_bp(tokens, i, r_bp)?;
        lhs = Expr::Binary(op.clone(), Box::new(lhs), Box::new(rhs));
    }

    Ok(lhs)
}
