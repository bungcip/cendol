use crate::ast::StringId;
use crate::pp::error::{PPError, PPErrorKind};
use crate::pp::pp_lexer::PPLexer;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::{MacroFlags, MacroInfo};
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceManager};
use std::borrow::Cow;

impl<'src> Preprocessor<'src> {
    /// Expand a macro if it exists
    pub(crate) fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PPError> {
        let PPTokenKind::Identifier(symbol) = token.kind else {
            return Ok(None);
        };

        let macro_info = self
            .macros
            .get(&symbol)
            .filter(|m| !m.flags.contains(MacroFlags::DISABLED))
            .cloned();

        let Some(macro_info) = macro_info else {
            return Ok(None);
        };

        // Bolt ⚡: Check for recursive expansion here to avoid walking include stack for non-macros.
        // using Dave Prosser's hide sets intersection approach
        if self.hide_sets.contains(token.hide_set, symbol) {
            return Ok(None);
        }

        if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) {
            let next = self.lex_token();
            let is_call = matches!(next, Some(ref t) if t.kind == PPTokenKind::LeftParen);
            if let Some(t) = next {
                self.pending_tokens.push(t);
            }
            if !is_call {
                return Ok(None);
            }
        }

        if let Some(m) = self.macros.get_mut(&symbol) {
            m.flags |= MacroFlags::USED;
        }

        let result = if macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) {
            self.expand_function_macro(&macro_info, &symbol, token)
        } else {
            self.expand_object_macro(&macro_info, &symbol, token)
        };

        result.map(Some)
    }

    /// Helper to convert tokens to their string representation
    pub(crate) fn tokens_to_string(&self, tokens: &[PPToken]) -> String {
        // Bolt ⚡: Optimized two-pass string building.
        // We use the token's length field for the first pass as it's a fast u16 access.
        let total_len: usize = tokens.iter().map(|t| t.length as usize).sum();

        let mut result = String::with_capacity(total_len);
        let mut cache = SourceBufferCache::new(self.sm);

        for token in tokens {
            result.push_str(cache.get_token_text(token));
        }
        result
    }

    /// Helper to create a virtual buffer for macro expansion.
    /// Does NOT rescan — the caller is responsible for rescanning.
    /// This prevents double-rescan bugs (e.g. deferred macro patterns).
    pub(crate) fn expand_virtual_buffer(
        &mut self,
        tokens: &[PPToken],
        name: &str,
        location: SourceLoc,
    ) -> Result<Vec<PPToken>, PPError> {
        Ok(self.create_virtual_buffer_tokens(tokens, name, location))
    }

    /// Expand an object-like macro
    pub(crate) fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        let new_hs = self.hide_sets.insert(token.hide_set, *symbol);

        // No DISABLED flag needed — hide_sets.contains detects self-reference
        // via the virtual buffer's source location (<macro_NAME>).
        let mut tokens = self.expand_virtual_buffer(&macro_info.tokens, symbol.as_str(), token.location)?;
        for t in &mut tokens {
            t.hide_set = self.hide_sets.union(t.hide_set, new_hs);
        }
        Ok(tokens)
    }

    /// Expand a function-like macro
    pub(crate) fn expand_function_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: &StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        let (args, rparen_token) = match self.parse_macro_args_from_lexer(macro_info) {
            Ok(args) => args,
            Err(PPError {
                kind: PPErrorKind::InvalidMacroParameter,
                ..
            }) => {
                return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, token.location);
            }
            Err(e) => return Err(e),
        };

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for arg in &args {
            let mut arg_clone = arg.clone();
            self.expand_tokens(&mut arg_clone, false)?;
            expanded_args.push(arg_clone);
        }

        // Compute new hide set for expanded tokens.
        let intersect_hs = self.hide_sets.intersection(token.hide_set, rparen_token.hide_set);
        let new_hs = self.hide_sets.insert(intersect_hs, *symbol);

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(macro_info, &args, &expanded_args, new_hs)?;

        // No DISABLED flag needed — is_recursive_expansion() detects self-reference
        // via the virtual buffer's source location (<macro_NAME>).
        self.expand_virtual_buffer(&substituted, symbol.as_str(), token.location)
    }

    /// Parse macro arguments from the current lexer
    pub(crate) fn parse_macro_args_from_lexer(
        &mut self,
        macro_info: &MacroInfo,
    ) -> Result<(Vec<Vec<PPToken>>, PPToken), PPError> {
        let token = self.expect_token()?;
        if token.kind != PPTokenKind::LeftParen {
            self.pending_tokens.push(token);
            return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, token.location);
        }

        let mut args = Vec::with_capacity(macro_info.parameter_list.len());
        let mut current_arg = Vec::new();
        let mut depth = 0;

        while let Some(t) = self.lex_token() {
            match t.kind {
                PPTokenKind::Eof => break,
                PPTokenKind::LeftParen => {
                    depth += 1;
                    current_arg.push(t);
                }
                PPTokenKind::RightParen if depth > 0 => {
                    depth -= 1;
                    current_arg.push(t);
                }
                PPTokenKind::RightParen => {
                    if !current_arg.is_empty() || !args.is_empty() {
                        args.push(current_arg);
                    } else if macro_info.parameter_list.len() == 1 || macro_info.variadic_arg.is_some() {
                        // Empty arguments are allowed in C99/C11.
                        // For a macro taking 1 argument or variadic args, an empty list of tokens
                        // between parentheses represents 1 empty argument.
                        args.push(Vec::new());
                    }

                    let expected = macro_info.parameter_list.len();
                    let valid = if macro_info.variadic_arg.is_some() {
                        args.len() >= expected
                    } else {
                        args.len() == expected
                    };

                    if valid {
                        return Ok((args, t));
                    }

                    return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, macro_info.location);
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(t),
            }
        }

        self.emit_error(PPErrorKind::UnexpectedEndOfFile, self.get_current_span())
    }

    /// Helper to collect variadic arguments with commas inserted
    pub(crate) fn collect_variadic_args_with_commas(
        &mut self,
        args: &[Vec<PPToken>],
        start_index: usize,
        trigger_loc: SourceLoc,
    ) -> Vec<PPToken> {
        // ⚡ Bolt: Pre-allocate result vector and avoid redundant clones.
        let mut total_tokens = 0;
        let num_args = args.len().saturating_sub(start_index);
        if num_args > 0 {
            total_tokens += num_args - 1; // for commas
            for arg in args.iter().skip(start_index) {
                total_tokens += arg.len();
            }
        }
        let mut result = Vec::with_capacity(total_tokens);

        let mut first = true;

        // We need a source for the comma token.
        // We create a virtual buffer for it to ensure stringification works correctly.
        // We only create it if we actually need a comma.
        let comma_source_id = if num_args > 1 {
            Some(
                self.sm
                    .add_virtual_buffer(b",".to_vec(), "<comma>", Some(trigger_loc), FileKind::Virtual),
            )
        } else {
            None
        };

        for arg in args.iter().skip(start_index) {
            if !first && let Some(sid) = comma_source_id {
                result.push(PPToken::new(
                    PPTokenKind::Comma,
                    PPTokenFlags::empty(),
                    SourceLoc::new(sid, 0),
                    1,
                ));
            }
            result.extend_from_slice(arg);
            first = false;
        }
        result
    }

    pub(crate) fn is_macro_param(&self, macro_info: &MacroInfo, symbol: StringId) -> bool {
        macro_info.variadic_arg == Some(symbol) || macro_info.parameter_list.contains(&symbol)
    }

    pub(crate) fn get_macro_param_tokens<'a>(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        args: &'a [Vec<PPToken>],
        location: SourceLoc,
    ) -> Option<Cow<'a, [PPToken]>> {
        if let Some(idx) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
            return Some(Cow::Borrowed(&args[idx]));
        }
        if macro_info.variadic_arg == Some(symbol) {
            let start = macro_info.parameter_list.len();
            return Some(Cow::Owned(
                self.collect_variadic_args_with_commas(args, start, location),
            ));
        }
        None
    }

    /// Substitute parameters in macro body
    pub(crate) fn substitute_macro(
        &mut self,
        macro_info: &MacroInfo,
        args: &[Vec<PPToken>],
        expanded_args: &[Vec<PPToken>],
        new_hs: u32,
    ) -> Result<Vec<PPToken>, PPError> {
        // Bolt ⚡: Pre-allocate result vector to minimize reallocations during substitution.
        let mut result = Vec::with_capacity(macro_info.tokens.len());
        let mut i = 0;
        let mut last_token_produced_output = false;

        while i < macro_info.tokens.len() {
            let token = &macro_info.tokens[i];

            match token.kind {
                PPTokenKind::Hash if i + 1 < macro_info.tokens.len() => {
                    let next = &macro_info.tokens[i + 1];
                    if let PPTokenKind::Identifier(sym) = next.kind
                        && let Some(arg) = self.get_macro_param_tokens(macro_info, sym, args, token.location)
                    {
                        let mut stringified = self.stringify_tokens(&arg, token.location)?;
                        stringified.hide_set = self.hide_sets.union(stringified.hide_set, new_hs);
                        result.push(stringified);
                        last_token_produced_output = true;
                        i += 2;
                        continue;
                    }
                }
                PPTokenKind::HashHash if i + 1 < macro_info.tokens.len() => {
                    let right_token = &macro_info.tokens[i + 1];
                    let left = if last_token_produced_output { result.pop() } else { None };

                    let (pasted, produced_output) = self.perform_token_pasting(macro_info, left, right_token, args)?;

                    result.extend(pasted);
                    last_token_produced_output = produced_output;
                    i += 2;
                    continue;
                }
                PPTokenKind::Identifier(sym) if self.is_macro_param(macro_info, sym) => {
                    let next_is_hh =
                        i + 1 < macro_info.tokens.len() && macro_info.tokens[i + 1].kind == PPTokenKind::HashHash;
                    let src = if next_is_hh { args } else { expanded_args };
                    if let Some(param_tokens) = self.get_macro_param_tokens(macro_info, sym, src, token.location) {
                        if param_tokens.is_empty() {
                            last_token_produced_output = false;
                        } else {
                            for mut t in param_tokens.iter().copied() {
                                t.hide_set = self.hide_sets.union(t.hide_set, new_hs);
                                result.push(t);
                            }
                            last_token_produced_output = true;
                        }
                    } else {
                        last_token_produced_output = false;
                    }
                }
                _ => {
                    let mut t = *token;
                    t.hide_set = self.hide_sets.union(t.hide_set, new_hs);
                    result.push(t);
                    last_token_produced_output = true;
                }
            }
            i += 1;
        }

        Ok(result)
    }

    /// Perform token pasting logic for the ## operator, including GNU comma swallowing.
    pub(crate) fn perform_token_pasting(
        &mut self,
        macro_info: &MacroInfo,
        left: Option<PPToken>,
        right_token: &PPToken,
        args: &[Vec<PPToken>],
    ) -> Result<(Vec<PPToken>, bool), PPError> {
        let right_tokens = if let PPTokenKind::Identifier(sym) = right_token.kind {
            self.get_macro_param_tokens(macro_info, sym, args, right_token.location)
                .unwrap_or(Cow::Borrowed(std::slice::from_ref(right_token)))
        } else {
            Cow::Borrowed(std::slice::from_ref(right_token))
        };

        if right_tokens.is_empty() {
            // Right operand is empty (placemarker).
            let is_comma = left.as_ref().is_some_and(|t| t.kind == PPTokenKind::Comma);
            let is_variadic =
                matches!(right_token.kind, PPTokenKind::Identifier(s) if macro_info.variadic_arg == Some(s));

            if is_comma && is_variadic {
                // GNU Comma Swallowing extension: swallow the comma.
                Ok((Vec::new(), false))
            } else if let Some(l) = left {
                // Standard behavior: paste left with empty -> left.
                Ok((vec![l], true))
            } else {
                Ok((Vec::new(), false))
            }
        } else if let Some(l) = left {
            // Right is not empty, Left is not empty: paste left with right[0].
            let mut pasted = self.paste_tokens(&l, &right_tokens[0])?;
            let pasted_hs = self.hide_sets.intersection(l.hide_set, right_tokens[0].hide_set);
            for t in &mut pasted {
                t.hide_set = pasted_hs;
            }
            let pasted_count = pasted.len();
            pasted.extend(right_tokens.iter().skip(1).copied());
            Ok((pasted, pasted_count > 0 || right_tokens.len() > 1))
        } else {
            // Right is not empty, Left is empty: empty ## right -> right.
            Ok((right_tokens.into_owned(), true))
        }
    }

    /// Stringify tokens for # operator
    pub(crate) fn stringify_tokens(&self, tokens: &[PPToken], location: SourceLoc) -> Result<PPToken, PPError> {
        // Bolt ⚡: Use a two-pass approach to build the stringified token efficiently.
        let mut total_len = 2; // For the opening and closing quotes
        let mut cache = SourceBufferCache::new(self.sm);

        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                total_len += 1;
            }
            let bytes = cache.get_token_bytes(token);
            let should_escape = matches!(
                token.kind,
                PPTokenKind::StringLiteral(_) | PPTokenKind::CharLiteral(_, _)
            );

            for &b in bytes {
                if should_escape && (b == b'"' || b == b'\\') {
                    total_len += 2;
                } else {
                    total_len += 1;
                }
            }
        }

        let mut result = String::with_capacity(total_len);
        result.push('"');

        cache.reset();
        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                result.push(' ');
            }

            let bytes = cache.get_token_bytes(token);
            let should_escape = matches!(
                token.kind,
                PPTokenKind::StringLiteral(_) | PPTokenKind::CharLiteral(_, _)
            );

            let mut last_start = 0;
            for (j, &b) in bytes.iter().enumerate() {
                if should_escape && (b == b'"' || b == b'\\') {
                    if j > last_start {
                        result.push_str(unsafe { std::str::from_utf8_unchecked(&bytes[last_start..j]) });
                    }
                    result.push('\\');
                    result.push(b as char);
                    last_start = j + 1;
                }
            }
            if last_start < bytes.len() {
                result.push_str(unsafe { std::str::from_utf8_unchecked(&bytes[last_start..]) });
            }
        }

        result.push('"');

        Ok(PPToken::new(
            PPTokenKind::StringLiteral(StringId::new(&result)),
            PPTokenFlags::empty(),
            location,
            result.len() as u16,
        ))
    }

    /// Paste tokens for ## operator
    pub(crate) fn paste_tokens(&mut self, left: &PPToken, right: &PPToken) -> Result<Vec<PPToken>, PPError> {
        // Get text of both tokens
        let left_buffer = self.sm.get_buffer(left.location.source_id());
        let left_start = left.location.offset() as usize;
        let left_end = left_start + left.length as usize;
        let left_text = if left_end <= left_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&left_buffer[left_start..left_end]) }
        } else {
            return self.emit_error_loc(PPErrorKind::InvalidTokenPasting, left.location);
        };

        let right_buffer = self.sm.get_buffer(right.location.source_id());
        let right_start = right.location.offset() as usize;
        let right_end = right_start + right.length as usize;
        let right_text = if right_end <= right_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&right_buffer[right_start..right_end]) }
        } else {
            return self.emit_error_loc(PPErrorKind::InvalidTokenPasting, right.location);
        };

        // ⚡ Bolt: Avoid redundant format! and clone by building the byte buffer directly.
        let mut virtual_buffer = Vec::with_capacity(left_text.len() + right_text.len());
        virtual_buffer.extend_from_slice(left_text.as_bytes());
        virtual_buffer.extend_from_slice(right_text.as_bytes());
        let virtual_id = self.sm.add_virtual_buffer(
            virtual_buffer,
            "pasted-tokens",
            Some(left.location),
            FileKind::PastedToken,
        );

        // Create a temporary lexer to lex the pasted text
        let buffer = self.sm.get_buffer_arc(virtual_id);
        let mut lexer = PPLexer::new(virtual_id, buffer);

        let mut tokens = Vec::new();
        while let Some(token) = lexer.next_token() {
            if matches!(token.kind, PPTokenKind::Eod | PPTokenKind::Eof) {
                continue;
            }
            tokens.push(token);
        }

        // If the result is not a valid preprocessing token, the behavior is undefined.
        // We will return whatever tokens we got.
        Ok(tokens)
    }

    /// Finds the range of tokens between balanced parentheses, starting at `start_index`.
    /// Returns the end index (exclusive) if successful.
    pub(crate) fn find_balanced_paren_range(&self, tokens: &[PPToken], start_index: usize) -> Option<usize> {
        if start_index >= tokens.len() || tokens[start_index].kind != PPTokenKind::LeftParen {
            return None;
        }

        let mut depth = 0;
        for (i, t) in tokens.iter().enumerate().skip(start_index) {
            match t.kind {
                PPTokenKind::LeftParen => depth += 1,
                PPTokenKind::RightParen => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i + 1);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Collects macro arguments from a slice of tokens.
    pub(crate) fn collect_macro_args_from_slice(
        &self,
        tokens: &[PPToken],
        start_index: usize,
        end_index: usize,
    ) -> Vec<Vec<PPToken>> {
        let mut args = Vec::new();
        let mut current_arg = Vec::new();
        let mut depth = 0;
        for token in &tokens[start_index..end_index] {
            match token.kind {
                PPTokenKind::LeftParen => {
                    depth += 1;
                    current_arg.push(*token);
                }
                PPTokenKind::RightParen => {
                    depth -= 1;
                    current_arg.push(*token);
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(*token),
            }
        }
        if !current_arg.is_empty() || !args.is_empty() {
            args.push(current_arg);
        }
        args
    }

    pub(crate) fn expand_has_include_computed_args(&mut self, args: &mut Vec<PPToken>) {
        let mut j = 0;
        let mut expansions = 0;
        while j < args.len() && expansions < 1000 {
            if j == 0
                && !args.is_empty()
                && (args[0].kind == PPTokenKind::Less || matches!(args[0].kind, PPTokenKind::StringLiteral(_)))
            {
                break;
            }
            if let Some(expanded) = self.expand_macro(&args[j]).unwrap_or_default() {
                args.splice(j..j + 1, expanded);
                expansions += 1;
                continue;
            }
            j += 1;
        }
    }

    pub(crate) fn try_handle_conditional_operator(
        &mut self,
        tokens: &mut Vec<PPToken>,
        i: usize,
    ) -> Result<Option<usize>, PPError> {
        let PPTokenKind::Identifier(sym) = tokens[i].kind else {
            return Ok(None);
        };

        if sym == self.directive_keywords.defined {
            let next = i + 1;
            let end = match tokens.get(next).map(|t| &t.kind) {
                Some(PPTokenKind::LeftParen) => self.find_balanced_paren_range(tokens, next).unwrap_or(next),
                _ => next + 1,
            };
            return Ok(Some(end.min(tokens.len())));
        }
        if sym == self.directive_keywords.has_include || sym == self.directive_keywords.has_include_next {
            let next = i + 1;
            if let Some(PPTokenKind::LeftParen) = tokens.get(next).map(|t| &t.kind) {
                let arg_start = next + 1;
                if let Some(arg_t) = tokens.get(arg_start)
                    && let Some(arg_end) = self.find_balanced_paren_range(tokens, next)
                {
                    match arg_t.kind {
                        PPTokenKind::Less | PPTokenKind::StringLiteral(_) => {
                            return Ok(Some(arg_end));
                        }
                        _ => {
                            // Computed form: __has_include(MACRO)
                            let mut args = tokens[arg_start..arg_end - 1].to_vec();
                            self.expand_has_include_computed_args(&mut args);
                            let len = args.len();
                            tokens.splice(arg_start..arg_end - 1, args);
                            return Ok(Some(arg_start + len + 1));
                        }
                    }
                }
            }
            return Ok(Some(next.min(tokens.len())));
        }

        if sym == self.directive_keywords.has_builtin
            || sym == self.directive_keywords.has_attribute
            || sym == self.directive_keywords.has_feature
            || sym == self.directive_keywords.has_extension
        {
            let next = i + 1;
            let arg_end = tokens
                .get(next)
                .filter(|t| t.kind == PPTokenKind::LeftParen)
                .and_then(|_| self.find_balanced_paren_range(tokens, next));

            if let Some(arg_end) = arg_end {
                // Argument to __has_builtin and friends should be expanded if it's a macro.
                let arg_start = next + 1;
                let mut args = tokens[arg_start..arg_end - 1].to_vec();
                self.expand_tokens(&mut args, false)?;
                let len = args.len();
                tokens.splice(arg_start..arg_end - 1, args);
                return Ok(Some(arg_start + len + 1));
            }
            return Ok(Some(next.min(tokens.len())));
        }

        Ok(None)
    }

    pub(crate) fn try_expand_function_macro_in_tokens(
        &mut self,
        tokens: &mut Vec<PPToken>,
        i: usize,
        in_conditional: bool,
    ) -> Result<bool, PPError> {
        let symbol_token = tokens[i];
        let PPTokenKind::Identifier(symbol) = symbol_token.kind else {
            return Ok(false);
        };

        let macro_info = self.macros.get(&symbol).cloned();
        let Some(macro_info) = macro_info else {
            return Ok(false);
        };

        // Bolt ⚡: Check for recursive expansion here avoiding walking include stack for non-macros
        // using Dave Prosser hide set algorithm.
        if self.hide_sets.contains(symbol_token.hide_set, symbol) {
            return Ok(false);
        }

        if !macro_info.flags.contains(MacroFlags::FUNCTION_LIKE) || macro_info.flags.contains(MacroFlags::DISABLED) {
            return Ok(false);
        }

        if i + 1 >= tokens.len() || tokens[i + 1].kind != PPTokenKind::LeftParen {
            return Ok(false);
        }

        let Some(end_j) = self.find_balanced_paren_range(tokens, i + 1) else {
            return Ok(false);
        };

        let args = self.collect_macro_args_from_slice(tokens, i + 2, end_j - 1);

        // Validate argument count
        if args.len() != macro_info.parameter_list.len() {
            // For conditional expressions, just skip problematic macro expansions
            return Ok(false);
        }

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for arg in &args {
            let mut arg_clone = arg.clone();
            let _ = self.expand_tokens(&mut arg_clone, in_conditional);
            expanded_args.push(arg_clone);
        }

        let intersect_hs = self
            .hide_sets
            .intersection(symbol_token.hide_set, tokens[end_j - 1].hide_set);
        let new_hs = self.hide_sets.insert(intersect_hs, symbol);

        let substituted = self.substitute_macro(&macro_info, &args, &expanded_args, new_hs)?;
        let substituted = self.create_virtual_buffer_tokens(&substituted, symbol.as_str(), symbol_token.location);

        if substituted.len() > 10000 {
            return Ok(false);
        }

        tokens.splice(i..end_j, substituted);
        if let Some(m) = self.macros.get_mut(&symbol) {
            m.flags |= MacroFlags::USED;
        }

        Ok(true)
    }

    pub(crate) fn try_handle_pragma_operator_inline(&mut self, tokens: &mut Vec<PPToken>, i: usize) -> bool {
        let token = tokens[i];
        if !matches!(token.kind, PPTokenKind::Identifier(s) if s == self.directive_keywords.pragma_operator) {
            return false;
        }

        // Need at least 3 more tokens: ( "string" )
        if i + 3 < tokens.len()
            && tokens[i + 1].kind == PPTokenKind::LeftParen
            && let PPTokenKind::StringLiteral(sym) = tokens[i + 2].kind
            && tokens[i + 3].kind == PPTokenKind::RightParen
        {
            let content = self.destringize(sym.as_str());
            self.perform_pragma(&content);
            tokens.drain(i..i + 4);
            return true;
        }
        false
    }

    /// Expand tokens by rescanning for further macro expansion
    pub(crate) fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>, in_conditional: bool) -> Result<(), PPError> {
        let mut i = 0;
        while i < tokens.len() {
            let token = tokens[i];

            if let Some(magic) = self.try_expand_magic_macro(&token) {
                tokens[i] = magic;
                i += 1;
                continue;
            }

            if in_conditional && let Some(new_i) = self.try_handle_conditional_operator(tokens, i)? {
                i = new_i;
                continue;
            }

            if !matches!(token.kind, PPTokenKind::Identifier(_)) {
                i += 1;
                continue;
            }

            if self.try_expand_function_macro_in_tokens(tokens, i, in_conditional)? {
                continue;
            }

            // Expand object-like macros inline.
            if let PPTokenKind::Identifier(symbol) = tokens[i].kind {
                let macro_info = self
                    .macros
                    .get(&symbol)
                    .filter(|m| !m.flags.contains(MacroFlags::FUNCTION_LIKE) && !m.flags.contains(MacroFlags::DISABLED))
                    .cloned();
                if let Some(macro_info) = macro_info
                    && !self.hide_sets.contains(tokens[i].hide_set, symbol)
                {
                    if let Some(m) = self.macros.get_mut(&symbol) {
                        m.flags |= MacroFlags::USED;
                    }
                    let new_hs = self.hide_sets.insert(tokens[i].hide_set, symbol);
                    let mut expanded =
                        self.expand_virtual_buffer(&macro_info.tokens, symbol.as_str(), tokens[i].location)?;
                    for t in &mut expanded {
                        t.hide_set = new_hs;
                    }
                    tokens.splice(i..i + 1, expanded);
                    continue;
                }
            }

            if self.try_handle_pragma_operator_inline(tokens, i) {
                continue;
            }

            i += 1;
        }

        Ok(())
    }

    pub(crate) fn create_virtual_buffer_tokens(
        &mut self,
        tokens: &[PPToken],
        macro_name: &str,
        trigger_location: SourceLoc,
    ) -> Vec<PPToken> {
        // Pass 0: Sum up lengths for capacity hint.
        let total_upper_bound: usize = tokens.iter().map(|t| t.length as usize).sum();
        let mut buffer = Vec::with_capacity(total_upper_bound);

        // Metadata to avoid re-calculating things in the final mapping pass.
        // (preserve_original_loc, offset_in_new_buffer, length_in_new_buffer)
        let mut token_metadata = Vec::with_capacity(tokens.len());

        let mut last_preserve_sid = None;
        let mut last_preserve_val = false;

        {
            let mut cache = SourceBufferCache::new(self.sm);

            for t in tokens {
                let sid = t.location.source_id();

                let preserve_original_loc = if Some(sid) == last_preserve_sid {
                    last_preserve_val
                } else {
                    let val = self.sm.get_file_info(sid).is_some_and(|info| {
                        info.kind == FileKind::PastedToken || info.kind == FileKind::MacroExpansion
                    });
                    last_preserve_sid = Some(sid);
                    last_preserve_val = val;
                    val
                };

                let start_offset = buffer.len() as u32;

                // Build buffer efficiently using cache
                let bytes = cache.get_token_bytes(t);
                buffer.extend_from_slice(bytes);

                let len = (buffer.len() as u32 - start_offset) as u16;
                token_metadata.push((preserve_original_loc, start_offset, len));
            }
        }

        let virtual_id = self.sm.add_virtual_buffer(
            buffer,
            &format!("macro_{}", macro_name),
            Some(trigger_location),
            FileKind::MacroExpansion,
        );

        // Final pass: Construct new tokens using the pre-calculated metadata.
        tokens
            .iter()
            .zip(token_metadata)
            .map(|(t, (preserve_original_loc, offset, len))| {
                let loc = if preserve_original_loc {
                    t.location
                } else {
                    SourceLoc::new(virtual_id, offset)
                };

                let mut token = PPToken::new(t.kind, t.flags | PPTokenFlags::MACRO_EXPANDED, loc, len);
                token.hide_set = t.hide_set;
                token
            })
            .collect()
    }

    pub(crate) fn parse_macro_definition_params(
        &mut self,
        macro_name: &str,
    ) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPError> {
        let mut flags = MacroFlags::FUNCTION_LIKE;
        let mut params = Vec::new();
        let mut variadic = None;

        'param_parsing: loop {
            let param_token = self.expect_token()?;
            match param_token.kind {
                PPTokenKind::RightParen => break,
                PPTokenKind::Ellipsis => {
                    flags |= MacroFlags::C99_VARARGS;
                    variadic = Some(StringId::new("__VA_ARGS__"));
                    if !matches!(self.lex_token().map(|t| t.kind), Some(PPTokenKind::RightParen)) {
                        return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, param_token.location);
                    }
                    break;
                }
                PPTokenKind::Identifier(sym) => {
                    if params.contains(&sym) {
                        return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, param_token.location);
                    }
                    params.push(sym);

                    let sep = self.expect_token()?;
                    match sep.kind {
                        PPTokenKind::Comma => continue,
                        PPTokenKind::RightParen => break,
                        PPTokenKind::Ellipsis => {
                            variadic = Some(params.pop().unwrap());
                            flags |= MacroFlags::GNU_VARARGS;
                            if !matches!(self.lex_token().map(|t| t.kind), Some(PPTokenKind::RightParen)) {
                                return self.emit_error_loc(PPErrorKind::InvalidMacroParameter, sep.location);
                            }
                            break;
                        }
                        _ => {
                            // Not a standard parameter list separator; treat as start of body.
                            self.pending_tokens.push(sep);
                            self.pending_tokens.push(param_token);
                            break 'param_parsing;
                        }
                    }
                }
                _ => {
                    self.report_warning(
                        param_token.location,
                        format!("Invalid macro parameter token in #define '{}'", macro_name),
                    );

                    // Skip to the next divider
                    while let Some(t) = self.lex_token() {
                        if matches!(t.kind, PPTokenKind::Comma | PPTokenKind::RightParen) {
                            self.pending_tokens.push(t);
                            break;
                        }
                    }
                }
            }
        }

        Ok((flags, params, variadic))
    }
}

/// Helper to cache source buffers for efficient token text retrieval
pub(crate) struct SourceBufferCache<'a> {
    sm: &'a SourceManager,
    last_sid: Option<SourceId>,
    last_buffer: Option<&'a [u8]>,
}

impl<'a> SourceBufferCache<'a> {
    pub(crate) fn new(sm: &'a SourceManager) -> Self {
        Self {
            sm,
            last_sid: None,
            last_buffer: None,
        }
    }

    pub(crate) fn reset(&mut self) {
        self.last_sid = None;
        self.last_buffer = None;
    }

    pub(crate) fn get_token_bytes<'b>(&'b mut self, token: &'b PPToken) -> &'b [u8] {
        let sid = token.location.source_id();
        let buffer = if self.last_sid == Some(sid) {
            self.last_buffer.unwrap()
        } else if let Some(b) = self.sm.get_buffer_safe(sid) {
            self.last_sid = Some(sid);
            self.last_buffer = Some(b);
            b
        } else {
            return token.get_text().as_bytes();
        };

        let start = token.location.offset() as usize;
        let end = start + token.length as usize;
        if end <= buffer.len() {
            &buffer[start..end]
        } else {
            token.get_text().as_bytes()
        }
    }

    pub(crate) fn get_token_text<'b>(&'b mut self, token: &'b PPToken) -> &'b str {
        unsafe { std::str::from_utf8_unchecked(self.get_token_bytes(token)) }
    }
}
