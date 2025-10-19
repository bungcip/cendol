use crate::preprocessor::error::PreprocessorError;
use crate::preprocessor::lexer::Lexer;
use crate::preprocessor::token::{Token, TokenKind};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
enum Macro {
    Object {
        tokens: Vec<Token>,
    },
    Function {
        parameters: Vec<String>,
        _is_variadic: bool,
        tokens: Vec<Token>,
    },
}

pub struct Preprocessor {
    macros: HashMap<String, Macro>,
    conditional_stack: Vec<bool>,
}

impl Preprocessor {
    pub fn new() -> Self {
        Preprocessor {
            macros: HashMap::new(),
            conditional_stack: Vec::new(),
        }
    }

    pub fn preprocess(&mut self, input: &str) -> Result<Vec<Token>, PreprocessorError> {
        let mut tokens = self.tokenize(input)?;
        self.process_directives(&mut tokens)?;
        self.expand_all_macros(&mut tokens)?;
        tokens.retain(|t| !matches!(t.kind, TokenKind::Whitespace(_) | TokenKind::Newline));
        Ok(tokens)
    }

    fn tokenize(&self, input: &str) -> Result<Vec<Token>, PreprocessorError> {
        let mut lexer = Lexer::new(input, "<input>".to_string());
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

    fn process_directives(&mut self, tokens: &mut Vec<Token>) -> Result<(), PreprocessorError> {
        let mut i = 0;
        let mut final_tokens = Vec::new();
        let mut depth = 0;

        while i < tokens.len() {
            let in_true_branch = self.conditional_stack.iter().all(|&x| x);

            match tokens[i].kind {
                TokenKind::If => {
                    depth += 1;
                    let (condition, end) = parse_conditional_expression(i + 1, tokens)?;
                    let result = evaluate_expression(&condition)?;
                    self.conditional_stack.push(result);
                    i = end;
                    continue;
                }
                TokenKind::Elif => {
                    if depth == 0 {
                        return Err(PreprocessorError::UnexpectedElif);
                    }
                    if let Some(last) = self.conditional_stack.last_mut() {
                        if !*last {
                            let (condition, _end) = parse_conditional_expression(i + 1, tokens)?;
                            let result = evaluate_expression(&condition)?;
                            *last = result;
                        } else {
                            *last = false;
                        }
                    }
                    i = find_next_line(i + 1, tokens);
                    continue;
                }
                TokenKind::Else => {
                    if depth == 0 {
                        return Err(PreprocessorError::UnexpectedElse);
                    }
                    if let Some(last) = self.conditional_stack.last_mut() {
                        *last = !*last;
                    }
                    i = find_next_line(i + 1, tokens);
                    continue;
                }
                TokenKind::Endif => {
                    if depth == 0 {
                        return Err(PreprocessorError::UnexpectedEndif);
                    }
                    self.conditional_stack.pop();
                    depth -= 1;
                    i = find_next_line(i + 1, tokens);
                    continue;
                }
                TokenKind::Directive(ref name) if name == "define" => {
                    if in_true_branch {
                        let mut macro_tokens = Vec::new();
                        let mut j = i + 1;
                        while j < tokens.len() {
                            if matches!(tokens[j].kind, TokenKind::Newline) {
                                break;
                            }
                            macro_tokens.push(tokens[j].clone());
                            j += 1;
                        }
                        self.handle_define(&mut macro_tokens)?;
                    }
                    i = find_next_line(i + 1, tokens);
                    continue;
                }
                TokenKind::Ifdef => {
                    depth += 1;
                    let (name, end) = parse_identifier(i + 1, tokens)?;
                    self.conditional_stack.push(self.macros.contains_key(&name));
                    i = end;
                    continue;
                }
                TokenKind::Ifndef => {
                    depth += 1;
                    let (name, end) = parse_identifier(i + 1, tokens)?;
                    self.conditional_stack
                        .push(!self.macros.contains_key(&name));
                    i = end;
                    continue;
                }
                TokenKind::Undef => {
                    if in_true_branch {
                        let (name, end) = parse_identifier(i + 1, tokens)?;
                        self.macros.remove(&name);
                        i = end;
                    } else {
                        i = find_next_line(i + 1, tokens);
                    }
                    continue;
                }
                TokenKind::Error => {
                    if in_true_branch {
                        let (message, _end) = parse_error_message(i + 1, tokens)?;
                        return Err(PreprocessorError::Generic(message));
                    }
                    i = find_next_line(i + 1, tokens);
                    continue;
                }
                TokenKind::Line => {
                    if in_true_branch {
                        let (_line, _filename, end) = parse_line_directive(i + 1, tokens)?;
                        i = end;
                    } else {
                        i = find_next_line(i + 1, tokens);
                    }
                    continue;
                }
                TokenKind::Include => {
                    if in_true_branch {
                        let (filename, end) = parse_include(i + 1, tokens)?;
                        let new_tokens = self.include_file(&filename)?;
                        tokens.splice(i..end, new_tokens);
                    } else {
                        i = find_next_line(i + 1, tokens);
                    }
                    continue;
                }
                _ => {}
            }

            if in_true_branch {
                final_tokens.push(tokens[i].clone());
            }
            i += 1;
        }

        if depth != 0 {
            return Err(PreprocessorError::UnterminatedConditional);
        }

        *tokens = final_tokens;
        Ok(())
    }

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

        let mut next_token_idx = 0;
        while next_token_idx < tokens.len()
            && matches!(&tokens[next_token_idx].kind, TokenKind::Whitespace(_))
        {
            next_token_idx += 1;
        }

        if next_token_idx < tokens.len()
            && matches!(&tokens[next_token_idx].kind, TokenKind::Punct(p) if p == "(")
        {
            tokens.drain(0..next_token_idx);
            tokens.remove(0);
            let mut parameters = Vec::new();
            let mut is_variadic = false;
            loop {
                self.consume_whitespace(tokens);
                if tokens.is_empty() {
                    return Err(PreprocessorError::UnexpectedEofInMacroParams);
                }
                if let TokenKind::Punct(p) = &tokens[0].kind {
                    if p == ")" {
                        tokens.remove(0);
                        break;
                    }
                }

                if let TokenKind::Identifier(param) = tokens[0].kind.clone() {
                    parameters.push(param);
                    tokens.remove(0);
                } else if let TokenKind::Punct(p) = &tokens[0].kind {
                    if p == "..." {
                        is_variadic = true;
                        parameters.push("..".to_string());
                        tokens.remove(0);
                    }
                }

                self.consume_whitespace(tokens);
                if !tokens.is_empty() {
                    if let TokenKind::Punct(p) = &tokens[0].kind {
                        if p == "," {
                            tokens.remove(0);
                        }
                    }
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

    fn consume_whitespace(&mut self, tokens: &mut Vec<Token>) {
        while !tokens.is_empty() && matches!(tokens[0].kind, TokenKind::Whitespace(_)) {
            tokens.remove(0);
        }
    }

    fn expand_all_macros(&mut self, tokens: &mut Vec<Token>) -> Result<(), PreprocessorError> {
        loop {
            let mut expanded = false;
            let mut i = 0;
            while i < tokens.len() {
                if let TokenKind::Identifier(name) = &tokens[i].kind {
                    if !tokens[i].hideset.contains(name) {
                        if name == "__LINE__" {
                            let line = tokens[i].location.line;
                            tokens[i] = Token::new(
                                TokenKind::Number(line.to_string()),
                                tokens[i].location.clone(),
                            );
                            expanded = true;
                        } else if name == "__FILE__" {
                            let file = tokens[i].location.file.clone();
                            tokens[i] =
                                Token::new(TokenKind::String(file), tokens[i].location.clone());
                            expanded = true;
                        } else if let Some(macro_def) = self.macros.get(name).cloned() {
                            let (start, end, expanded_tokens) =
                                self.expand_single_macro(&tokens[i], &macro_def, i, tokens)?;
                            tokens.splice(start..end, expanded_tokens);
                            expanded = true;
                            break;
                        }
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
                    || !matches!(&tokens[next_idx].kind, TokenKind::Punct(p) if p == "(")
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
                TokenKind::Punct(p) if p == "(" => {
                    paren_level += 1;
                    current_arg.push(token.clone());
                }
                TokenKind::Punct(p) if p == ")" => {
                    paren_level -= 1;
                    if paren_level == 0 {
                        if !current_arg.is_empty() {
                            args.push(self.trim_whitespace(current_arg));
                        }
                        return Ok((args, i));
                    }
                    current_arg.push(token.clone());
                }
                TokenKind::Punct(p) if p == "," && paren_level == 1 => {
                    args.push(self.trim_whitespace(current_arg));
                    current_arg = Vec::new();
                }
                _ => current_arg.push(token.clone()),
            }
            i += 1;
        }
        Err(PreprocessorError::UnexpectedEofInMacroArgs)
    }

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
            if let TokenKind::Punct(p) = &token.kind {
                if p == "#" {
                    i += 1;
                    if i < body.len() {
                        if let TokenKind::Identifier(param_name) = &body[i].kind {
                            if let Some(idx) = parameters.iter().position(|p| p == param_name) {
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
                        }
                    }
                } else if p == "##" {
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
                    let mut lexer = Lexer::new(&pasted_str, lhs.location.file.clone());
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
                    if let Some(vararg_start) = vararg_start {
                        if vararg_start < args.len() {
                            for (i, arg) in args[vararg_start..].iter().enumerate() {
                                result.extend(arg.clone());
                                if i < args.len() - vararg_start - 1 {
                                    result.push(Token::new(
                                        TokenKind::Punct(",".to_string()),
                                        token.location.clone(),
                                    ));
                                }
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

    fn trim_whitespace(&self, mut tokens: Vec<Token>) -> Vec<Token> {
        if let Some(first) = tokens.first() {
            if first.kind.is_whitespace() {
                tokens.remove(0);
            }
        }
        if let Some(last) = tokens.last() {
            if last.kind.is_whitespace() {
                tokens.pop();
            }
        }
        tokens
    }

    fn include_file(&mut self, filename: &str) -> Result<Vec<Token>, PreprocessorError> {
        let content = std::fs::read_to_string(filename)
            .map_err(|_| PreprocessorError::FileNotFound(filename.to_string()))?;
        let mut lexer = Lexer::new(&content, filename.to_string());
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

fn parse_include(start_idx: usize, tokens: &[Token]) -> Result<(String, usize), PreprocessorError> {
    let mut i = start_idx;
    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    if i < tokens.len() {
        if let TokenKind::String(s) = &tokens[i].kind {
            return Ok((s.clone(), i + 1));
        }
    }

    Err(PreprocessorError::InvalidInclude)
}

fn parse_conditional_expression(
    start_idx: usize,
    tokens: &[Token],
) -> Result<(Vec<Token>, usize), PreprocessorError> {
    let mut condition = Vec::new();
    let mut i = start_idx;
    while i < tokens.len() {
        if matches!(tokens[i].kind, TokenKind::Newline) {
            return Ok((condition, i));
        }
        condition.push(tokens[i].clone());
        i += 1;
    }
    Ok((condition, i))
}

fn evaluate_expression(tokens: &[Token]) -> Result<bool, PreprocessorError> {
    let mut i = 0;
    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    if i >= tokens.len() {
        return Ok(false);
    }

    let lhs: i32 = if let TokenKind::Number(s) = &tokens[i].kind {
        s.parse().unwrap()
    } else {
        return Ok(false);
    };
    i += 1;

    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    if i >= tokens.len() {
        return Ok(lhs != 0);
    }

    let op = if let TokenKind::Punct(s) = &tokens[i].kind {
        s
    } else {
        return Ok(lhs != 0);
    };
    i += 1;

    while i < tokens.len() && tokens[i].kind.is_whitespace() {
        i += 1;
    }

    if i >= tokens.len() {
        return Ok(lhs != 0);
    }

    let rhs: i32 = if let TokenKind::Number(s) = &tokens[i].kind {
        s.parse().unwrap()
    } else {
        return Ok(lhs != 0);
    };

    match op.as_str() {
        "<" => Ok(lhs < rhs),
        ">" => Ok(lhs > rhs),
        _ => Ok(lhs != 0),
    }
}

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
