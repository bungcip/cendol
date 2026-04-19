use crate::ast::StringId;
use crate::pp::error::{PPError, PPErrorKind};
use crate::pp::pp_lexer::PPLexer;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::{MacroFlags, MacroInfo};
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceManager};

#[derive(Clone, Copy)]
struct SubstitutionCtx<'a> {
    macro_info: &'a MacroInfo,
    symbol: StringId,
    args: &'a [Vec<PPToken>],
    expanded_args: &'a [Vec<PPToken>],
    intersect_hs: u32,
    new_hs: u32,
    is_variadic_empty: bool,
    is_va_missing: bool,
}

impl<'src> Preprocessor<'src> {
    /// Expand a macro if it exists
    pub(super) fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PPError> {
        let PPTokenKind::Identifier(symbol) = token.kind else {
            return Ok(None);
        };

        if token.flags.contains(PPTokenFlags::DISABLE_EXPANSION) {
            return Ok(None);
        }

        // Bolt ⚡: Check hide set FIRST. This avoids a HashMap lookup for every recursive
        // macro identifier encountered during expansion.
        if self.hide_sets.contains(token.hide_set, symbol) {
            return Ok(None);
        }

        // Bolt ⚡: Extract flags and drop the borrow of self.macros early to avoid borrow checker errors.
        let flags = self.macros.get(&symbol).map(|m| m.flags);
        let Some(flags) = flags else {
            return Ok(None);
        };

        if flags.contains(MacroFlags::DISABLED) {
            return Ok(None);
        }

        if flags.contains(MacroFlags::FUNCTION_LIKE) {
            let next = self.lex_token();
            let is_call = matches!(next, Some(ref t) if t.kind == PPTokenKind::LeftParen);
            if let Some(t) = next {
                self.pending_tokens.push(t);
            }
            if !is_call {
                return Ok(None);
            }
        }

        // Bolt ⚡: Consolidated lookup and flag update. We only clone once we are
        // committed to expansion. This avoids redundant hashing and Arc increments
        // for disabled or non-call function-like macros.
        let m = self.macros.get_mut(&symbol).unwrap();
        m.flags |= MacroFlags::USED;
        let macro_info = m.clone();

        let result = if flags.contains(MacroFlags::FUNCTION_LIKE) {
            self.expand_function_macro(&macro_info, symbol, token)
        } else {
            self.expand_object_macro(&macro_info, symbol, token)
        };

        result.map(Some)
    }

    /// Helper to convert tokens to their string representation
    pub(super) fn tokens_to_string(&self, tokens: &[PPToken]) -> String {
        let mut result = String::new();
        for token in tokens {
            result.push_str(&self.get_token_text(token));
        }
        result
    }

    /// Helper to create a virtual buffer for macro expansion.
    /// Does NOT rescan — the caller is responsible for rescanning.
    /// This prevents double-rescan bugs (e.g. deferred macro patterns).
    fn expand_virtual_buffer(
        &mut self,
        tokens: &[PPToken],
        name: StringId,
        location: SourceLoc,
    ) -> Result<Vec<PPToken>, PPError> {
        Ok(self.create_virtual_buffer_tokens(tokens, name, location))
    }

    /// Expand an object-like macro
    fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        let new_hs = self.hide_sets.insert(token.hide_set, symbol);

        // No DISABLED flag needed — hide_sets.contains detects self-reference
        // via the virtual buffer's source location (<macro_NAME>).
        let mut tokens = self.expand_virtual_buffer(&macro_info.tokens, symbol, token.location)?;
        let mut last_hs = (u32::MAX, 0u32);
        for t in &mut tokens {
            if t.hide_set == 0 {
                t.hide_set = new_hs;
            } else {
                if t.hide_set != last_hs.0 {
                    last_hs = (t.hide_set, self.hide_sets.union(t.hide_set, new_hs));
                }
                t.hide_set = last_hs.1;
            }
        }
        Ok(tokens)
    }

    /// Expand a function-like macro
    fn expand_function_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPError> {
        let (mut args, rparen_token) = match self.parse_macro_args_from_lexer(macro_info) {
            Ok(args) => args,
            Err(PPError {
                kind: PPErrorKind::InvalidMacroParameter,
                ..
            }) => {
                return self.emit_error(PPErrorKind::InvalidMacroParameter, token.location);
            }
            Err(e) => return Err(e),
        };

        let (is_variadic_empty, is_va_missing) = self.precalculate_variadic_args(macro_info, &mut args);

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for arg in &args {
            let mut arg_clone = arg.clone();
            self.expand_tokens(&mut arg_clone, false)?;
            expanded_args.push(arg_clone);
        }

        // Compute new hide set for expanded tokens.
        let intersect_hs = self.hide_sets.intersection(token.hide_set, rparen_token.hide_set);
        let new_hs = self.hide_sets.insert(intersect_hs, symbol);

        // Substitute parameters in macro body
        let substituted = self.substitute_macro(SubstitutionCtx {
            macro_info,
            symbol,
            args: &args,
            expanded_args: &expanded_args,
            intersect_hs,
            new_hs,
            is_variadic_empty,
            is_va_missing,
        })?;

        // No DISABLED flag needed — is_recursive_expansion() detects self-reference
        // via the virtual buffer's source location (<macro_NAME>).
        self.expand_virtual_buffer(&substituted, symbol, token.location)
    }

    /// Parse macro arguments from the current lexer
    fn parse_macro_args_from_lexer(&mut self, macro_info: &MacroInfo) -> Result<(Vec<Vec<PPToken>>, PPToken), PPError> {
        let token = self.expect_token()?;
        if token.kind != PPTokenKind::LeftParen {
            self.pending_tokens.push(token);
            return self.emit_error(PPErrorKind::InvalidMacroParameter, token.location);
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

                    return self.emit_error(PPErrorKind::InvalidMacroParameter, macro_info.location);
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(t),
            }
        }

        self.emit_error_span(PPErrorKind::UnexpectedEndOfFile, self.get_current_span())
    }

    /// Helper to collect variadic arguments with commas inserted
    /// ⚡ Bolt: Efficiently collect variadic arguments into a single token list.
    /// This optimization uses `SourceLoc::builtin()` for synthetic commas to avoid
    /// creating thousands of tiny virtual buffers and unique `SourceId`s, which
    /// significantly reduces memory pressure and `SourceManager` churn in large projects.
    /// Pre-calculates combined variadic tokens (with commas) and other variadic metadata.
    /// Bolt ⚡: This optimization allows get_macro_param_tokens to return &[PPToken] instead of Cow,
    /// eliminating redundant allocations in the substitution hot-path.
    fn precalculate_variadic_args(&mut self, macro_info: &MacroInfo, args: &mut Vec<Vec<PPToken>>) -> (bool, bool) {
        if macro_info.variadic_arg.is_some() {
            let start = macro_info.parameter_list.len();
            let is_empty = self.is_variadic_args_empty(macro_info, args);
            let is_missing = args.len() <= start;
            let combined = self.collect_variadic_args_with_commas(args, start);
            args.truncate(start);
            args.push(combined);
            (is_empty, is_missing)
        } else {
            (false, false)
        }
    }

    fn collect_variadic_args_with_commas(&mut self, args: &[Vec<PPToken>], start_index: usize) -> Vec<PPToken> {
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

        for arg in args.iter().skip(start_index) {
            if !first {
                result.push(PPToken::new(
                    PPTokenKind::Comma,
                    PPTokenFlags::MACRO_EXPANDED,
                    SourceLoc::builtin(),
                    1,
                ));
            }
            result.extend_from_slice(arg);
            first = false;
        }
        result
    }

    fn get_macro_param_tokens<'a>(
        &self,
        macro_info: &MacroInfo,
        symbol: StringId,
        args: &'a [Vec<PPToken>],
    ) -> Option<&'a [PPToken]> {
        if let Some(idx) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
            return Some(&args[idx]);
        }
        if macro_info.variadic_arg == Some(symbol) {
            // Combined variadic tokens are stored at the index matching parameter_list.len()
            let idx = macro_info.parameter_list.len();
            if idx < args.len() {
                return Some(&args[idx]);
            }
        }
        None
    }

    fn is_variadic_args_empty(&self, macro_info: &MacroInfo, args: &[Vec<PPToken>]) -> bool {
        let start = macro_info.parameter_list.len();
        if args.len() <= start {
            return true;
        }
        args[start..].iter().all(|arg| arg.is_empty())
    }

    fn resolve_va_opt(&mut self, ctx: &SubstitutionCtx) -> Result<Option<Vec<PPToken>>, PPError> {
        let macro_info = ctx.macro_info;
        if !macro_info.flags.contains(MacroFlags::HAS_VA_OPT) {
            return Ok(None);
        }

        let mut resolved = Vec::with_capacity(macro_info.tokens.len());
        let mut i = 0;
        let is_empty = ctx.is_variadic_empty;

        while i < macro_info.tokens.len() {
            let token = &macro_info.tokens[i];

            // Handle # __VA_OPT__(content)
            if token.kind == PPTokenKind::Hash && i + 1 < macro_info.tokens.len() {
                let next = &macro_info.tokens[i + 1];
                if let PPTokenKind::Identifier(sym) = next.kind
                    && sym == self.keywords.va_opt
                    && i + 2 < macro_info.tokens.len()
                    && macro_info.tokens[i + 2].kind == PPTokenKind::LeftParen
                    && let Some(rparen_idx) = Self::find_balanced_paren_range(&macro_info.tokens, i + 2)
                {
                    if !is_empty {
                        let content = &macro_info.tokens[i + 3..rparen_idx - 1];
                        let mut content_ctx = *ctx;
                        content_ctx.is_va_missing = false; // __VA_OPT__ content substitution doesn't use GNU comma swallowing
                        let substituted = self.substitute_tokens_slice(content, &content_ctx)?;
                        let mut stringified = self.stringify_tokens(&substituted, token.location)?;
                        stringified.hide_set = token.hide_set;
                        resolved.push(stringified);
                    } else {
                        let mut stringified = self.stringify_tokens(&[], token.location)?;
                        stringified.hide_set = token.hide_set;
                        resolved.push(stringified);
                    }
                    i = rparen_idx;
                    continue;
                }
            }

            // Handle __VA_OPT__(content)
            if let PPTokenKind::Identifier(sym) = token.kind
                && sym == self.keywords.va_opt
                && i + 1 < macro_info.tokens.len()
                && macro_info.tokens[i + 1].kind == PPTokenKind::LeftParen
                && let Some(rparen_idx) = Self::find_balanced_paren_range(&macro_info.tokens, i + 1)
            {
                if !is_empty {
                    let content = &macro_info.tokens[i + 2..rparen_idx - 1];
                    resolved.extend_from_slice(content);
                }
                i = rparen_idx;
                continue;
            }

            resolved.push(*token);
            i += 1;
        }

        Ok(Some(resolved))
    }

    /// Substitute parameters in macro body
    fn substitute_macro(&mut self, ctx: SubstitutionCtx) -> Result<Vec<PPToken>, PPError> {
        let tokens = self.resolve_va_opt(&ctx)?;
        let tokens_ref = tokens.as_deref().unwrap_or(&ctx.macro_info.tokens);
        self.substitute_tokens_slice(tokens_ref, &ctx)
    }

    fn substitute_tokens_slice(
        &mut self,
        tokens_slice: &[PPToken],
        ctx: &SubstitutionCtx,
    ) -> Result<Vec<PPToken>, PPError> {
        let mut result = Vec::with_capacity(tokens_slice.len());
        let mut i = 0;
        let mut last_token_produced_output = false;

        // Bolt ⚡: Single-item cache for hide-set updates.
        let mut last_hs = (u32::MAX, 0u32);
        let arg_empty_hs = if ctx.intersect_hs == 0 {
            ctx.new_hs
        } else {
            self.hide_sets.insert(0, ctx.symbol)
        };

        while i < tokens_slice.len() {
            let token = &tokens_slice[i];

            match token.kind {
                PPTokenKind::Hash if i + 1 < tokens_slice.len() => {
                    let next = &tokens_slice[i + 1];
                    let mut matched = false;

                    if let PPTokenKind::Identifier(sym) = next.kind
                        && let Some(arg) = self.get_macro_param_tokens(ctx.macro_info, sym, ctx.args)
                    {
                        let mut stringified = self.stringify_tokens(arg, token.location)?;
                        // Bolt ⚡: Stringified tokens always start with an empty hide-set (0).
                        stringified.hide_set = ctx.new_hs;
                        result.push(stringified);
                        last_token_produced_output = true;
                        i += 2;
                        matched = true;
                    }
                    if matched {
                        continue;
                    }
                    // Fallback: output isolated hash token
                    let mut t = *token;
                    t.hide_set = ctx.new_hs;
                    result.push(t);
                    last_token_produced_output = true;
                }
                PPTokenKind::HashHash if i + 1 < tokens_slice.len() => {
                    let right_token = &tokens_slice[i + 1];
                    let left = if last_token_produced_output { result.pop() } else { None };

                    let (pasted, produced_output) =
                        self.perform_token_pasting(ctx.macro_info, left, right_token, ctx.args, ctx.is_va_missing)?;

                    result.extend(pasted);
                    last_token_produced_output = produced_output;
                    i += 2;
                    continue;
                }
                PPTokenKind::Identifier(sym) => {
                    let next_is_hh = i + 1 < tokens_slice.len() && tokens_slice[i + 1].kind == PPTokenKind::HashHash;
                    let src = if next_is_hh { ctx.args } else { ctx.expanded_args };
                    if let Some(param_tokens) = self.get_macro_param_tokens(ctx.macro_info, sym, src) {
                        if param_tokens.is_empty() {
                            last_token_produced_output = false;
                        } else {
                            if ctx.intersect_hs == 0 {
                                // Bolt ⚡: Fast-path for top-level macro calls. All tokens receive new_hs.
                                let start_idx = result.len();
                                result.extend_from_slice(param_tokens);
                                for t in &mut result[start_idx..] {
                                    t.hide_set = ctx.new_hs;
                                }
                            } else {
                                for mut t in param_tokens.iter().copied() {
                                    // Bolt ⚡: Hide-set intersection logic for arguments (Dave Prosser algorithm).
                                    if t.hide_set == 0 {
                                        t.hide_set = arg_empty_hs;
                                    } else {
                                        if t.hide_set != last_hs.0 {
                                            let intersected = self.hide_sets.intersection(t.hide_set, ctx.intersect_hs);
                                            let updated = self.hide_sets.insert(intersected, ctx.symbol);
                                            last_hs = (t.hide_set, updated);
                                        }
                                        t.hide_set = last_hs.1;
                                    }
                                    result.push(t);
                                }
                            }
                            last_token_produced_output = true;
                        }
                    } else {
                        let mut t = *token;
                        // Bolt ⚡: Body tokens always start with an empty hide-set (0).
                        t.hide_set = ctx.new_hs;
                        result.push(t);
                        last_token_produced_output = true;
                    }
                }
                _ => {
                    let mut t = *token;
                    // Bolt ⚡: Body tokens always start with an empty hide-set (0).
                    t.hide_set = ctx.new_hs;
                    result.push(t);
                    last_token_produced_output = true;
                }
            }
            i += 1;
        }

        Ok(result)
    }

    /// Perform token pasting logic for the ## operator, including GNU comma swallowing.
    fn perform_token_pasting(
        &mut self,
        macro_info: &MacroInfo,
        left: Option<PPToken>,
        right_token: &PPToken,
        args: &[Vec<PPToken>],
        is_va_missing: bool,
    ) -> Result<(Vec<PPToken>, bool), PPError> {
        let right_tokens = if let PPTokenKind::Identifier(sym) = right_token.kind {
            self.get_macro_param_tokens(macro_info, sym, args)
                .unwrap_or(std::slice::from_ref(right_token))
        } else {
            std::slice::from_ref(right_token)
        };

        if right_tokens.is_empty() {
            // Right operand is empty (placemarker).
            let is_comma = left.as_ref().is_some_and(|t| t.kind == PPTokenKind::Comma);
            let is_variadic =
                matches!(right_token.kind, PPTokenKind::Identifier(s) if macro_info.variadic_arg == Some(s));

            if is_comma && is_variadic && is_va_missing {
                // GNU Comma Swallowing extension: swallow the comma only when
                // no variadic arguments were provided at all (e.g. M(a,b) for
                // #define M(x,y,...)).  When an explicit empty variadic argument
                // is supplied (e.g. M(a,b,)), the comma is preserved.
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
            Ok((right_tokens.to_vec(), true))
        }
    }

    /// Stringify tokens for # operator
    fn stringify_tokens(&mut self, tokens: &[PPToken], _location: SourceLoc) -> Result<PPToken, PPError> {
        let mut result = String::new();
        result.push('"');

        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                result.push(' ');
            }

            let text = self.get_token_text(token);

            if matches!(token.kind, PPTokenKind::StringLiteral | PPTokenKind::CharLiteral(_)) {
                for c in text.chars() {
                    if c == '"' || c == '\\' {
                        result.push('\\');
                    }
                    result.push(c);
                }
            } else {
                result.push_str(&text);
            }
        }

        result.push('"');

        let source_id = self.sm.add_virtual_buffer(
            result.as_bytes().to_vec(),
            "<stringified-tokens>",
            Some(_location),
            FileKind::MacroExpansion,
        );

        Ok(PPToken::new(
            PPTokenKind::StringLiteral,
            PPTokenFlags::empty(),
            SourceLoc::new(source_id, 0),
            result.len() as u16,
        ))
    }

    /// Paste tokens for ## operator
    fn paste_tokens(&mut self, left: &PPToken, right: &PPToken) -> Result<Vec<PPToken>, PPError> {
        // Get text of both tokens
        let left_buffer = self.sm.get_buffer(left.location.source_id());
        let left_start = left.location.offset() as usize;
        let left_end = left_start + left.length as usize;
        let left_text = if left_end <= left_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&left_buffer[left_start..left_end]) }
        } else {
            return self.emit_error(PPErrorKind::InvalidTokenPasting, left.location);
        };

        let right_buffer = self.sm.get_buffer(right.location.source_id());
        let right_start = right.location.offset() as usize;
        let right_end = right_start + right.length as usize;
        let right_text = if right_end <= right_buffer.len() {
            unsafe { std::str::from_utf8_unchecked(&right_buffer[right_start..right_end]) }
        } else {
            return self.emit_error(PPErrorKind::InvalidTokenPasting, right.location);
        };

        // ⚡ Bolt: Avoid redundant format! and clone by building the byte buffer directly.
        let mut virtual_buffer = Vec::with_capacity(left_text.len() + right_text.len());
        virtual_buffer.extend_from_slice(left_text.as_bytes());
        virtual_buffer.extend_from_slice(right_text.as_bytes());
        let virtual_id = self.sm.add_virtual_buffer(
            virtual_buffer,
            "<pasted-tokens>",
            Some(left.location),
            FileKind::MacroExpansion,
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
    fn find_balanced_paren_range(tokens: &[PPToken], start_index: usize) -> Option<usize> {
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
    fn collect_macro_args_from_slice(
        macro_info: &MacroInfo,
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
        } else if macro_info.parameter_list.len() == 1 || macro_info.variadic_arg.is_some() {
            // Empty arguments are allowed in C99/C11.
            // For a macro taking 1 argument or variadic args, an empty list of tokens
            // between parentheses represents 1 empty argument.
            args.push(Vec::new());
        }
        args
    }

    fn expand_has_include_computed_args(&mut self, args: &mut Vec<PPToken>) {
        let mut j = 0;
        let mut expansions = 0;
        while j < args.len() && expansions < 1000 {
            if j == 0
                && !args.is_empty()
                && (args[0].kind == PPTokenKind::Less || args[0].kind == PPTokenKind::StringLiteral)
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

    fn try_handle_conditional_operator(
        &mut self,
        tokens: &mut Vec<PPToken>,
        i: usize,
    ) -> Result<Option<usize>, PPError> {
        let PPTokenKind::Identifier(sym) = tokens[i].kind else {
            return Ok(None);
        };

        if sym == self.keywords.defined {
            let next = i + 1;
            let end = match tokens.get(next).map(|t| &t.kind) {
                Some(PPTokenKind::LeftParen) => Self::find_balanced_paren_range(tokens, next).unwrap_or(next),
                _ => next + 1,
            };
            return Ok(Some(end.min(tokens.len())));
        }
        if sym == self.keywords.has_include || sym == self.keywords.has_include_next {
            let next = i + 1;
            if let Some(PPTokenKind::LeftParen) = tokens.get(next).map(|t| &t.kind) {
                let arg_start = next + 1;
                if let Some(arg_t) = tokens.get(arg_start)
                    && let Some(arg_end) = Self::find_balanced_paren_range(tokens, next)
                {
                    match arg_t.kind {
                        PPTokenKind::Less | PPTokenKind::StringLiteral => {
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

        if sym == self.keywords.has_builtin
            || sym == self.keywords.has_attribute
            || sym == self.keywords.has_feature
            || sym == self.keywords.has_extension
        {
            let next = i + 1;
            let arg_end = tokens
                .get(next)
                .filter(|t| t.kind == PPTokenKind::LeftParen)
                .and_then(|_| Self::find_balanced_paren_range(tokens, next));

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

    fn try_handle_pragma_operator_inline(&mut self, tokens: &mut Vec<PPToken>, i: usize) -> bool {
        let token = tokens[i];
        if !matches!(token.kind, PPTokenKind::Identifier(s) if s == self.keywords.pragma_operator) {
            return false;
        }

        // Need at least 3 more tokens: ( "string" )
        if i + 3 < tokens.len()
            && tokens[i + 1].kind == PPTokenKind::LeftParen
            && let PPTokenKind::StringLiteral = tokens[i + 2].kind
            && tokens[i + 3].kind == PPTokenKind::RightParen
        {
            let content = self.destringize(&self.get_token_text(&tokens[i + 2]));
            self.perform_pragma(&content);
            tokens.drain(i..i + 4);
            return true;
        }
        false
    }

    /// Expand tokens by rescanning for further macro expansion
    pub(super) fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>, in_conditional: bool) -> Result<(), PPError> {
        let mut i = 0;
        while i < tokens.len() {
            let token = tokens[i];

            // Bolt ⚡: Hoist identifier guard. Magic macros, conditional operators,
            // function macros, object macros, and _Pragma all require an identifier.
            // This fast-tracks operators, numbers, and literals which are common in
            // macro arguments and conditional expressions.
            if !matches!(token.kind, PPTokenKind::Identifier(_)) {
                i += 1;
                continue;
            }

            if let Some(magic) = self.try_expand_magic_macro(&token) {
                tokens[i] = magic;
                i += 1;
                continue;
            }

            if in_conditional && let Some(new_i) = self.try_handle_conditional_operator(tokens, i)? {
                i = new_i;
                continue;
            }

            // Expand macros inline.
            if let PPTokenKind::Identifier(symbol) = tokens[i].kind {
                if tokens[i].flags.contains(PPTokenFlags::DISABLE_EXPANSION) {
                    i += 1;
                    continue;
                }

                // Bolt ⚡: Consolidated macro lookup logic.
                // We perform a single hide-set check and a single HashMap lookup per identifier
                // to determine if it should be expanded as a function-like or object-like macro.
                if !self.hide_sets.contains(tokens[i].hide_set, symbol) {
                    // Task to perform after dropping the borrow of self.macros.
                    enum ExpansionTask {
                        Function(MacroInfo, usize, Vec<Vec<PPToken>>),
                        Object(MacroInfo),
                    }

                    let task = if let Some(m) = self.macros.get_mut(&symbol) {
                        let flags = m.flags;
                        if !flags.contains(MacroFlags::DISABLED) {
                            if flags.contains(MacroFlags::FUNCTION_LIKE) {
                                // Try function-like expansion
                                if i + 1 < tokens.len() && tokens[i + 1].kind == PPTokenKind::LeftParen {
                                    if let Some(end_j) = Self::find_balanced_paren_range(tokens, i + 1) {
                                        let args = Self::collect_macro_args_from_slice(m, tokens, i + 2, end_j - 1);

                                        // Validate argument count
                                        let expected = m.parameter_list.len();
                                        let valid = if m.variadic_arg.is_some() {
                                            args.len() >= expected
                                        } else {
                                            args.len() == expected
                                        };

                                        if valid {
                                            m.flags |= MacroFlags::USED;
                                            Some(ExpansionTask::Function(m.clone(), end_j, args))
                                        } else {
                                            None
                                        }
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            } else {
                                // Object-like expansion
                                m.flags |= MacroFlags::USED;
                                Some(ExpansionTask::Object(m.clone()))
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    match task {
                        Some(ExpansionTask::Function(macro_info, end_j, mut args)) => {
                            let (is_variadic_empty, is_va_missing) =
                                self.precalculate_variadic_args(&macro_info, &mut args);

                            // Pre-expand arguments (prescan)
                            let mut expanded_args = Vec::with_capacity(args.len());
                            for arg in &args {
                                let mut arg_clone = arg.clone();
                                let _ = self.expand_tokens(&mut arg_clone, in_conditional);
                                expanded_args.push(arg_clone);
                            }

                            let intersect_hs = self
                                .hide_sets
                                .intersection(tokens[i].hide_set, tokens[end_j - 1].hide_set);
                            let new_hs = self.hide_sets.insert(intersect_hs, symbol);

                            let substituted = self.substitute_macro(SubstitutionCtx {
                                macro_info: &macro_info,
                                symbol,
                                args: &args,
                                expanded_args: &expanded_args,
                                intersect_hs,
                                new_hs,
                                is_variadic_empty,
                                is_va_missing,
                            })?;
                            let substituted =
                                self.create_virtual_buffer_tokens(&substituted, symbol, tokens[i].location);

                            if substituted.len() <= 10000 {
                                tokens.splice(i..end_j, substituted);
                                continue;
                            }
                        }
                        Some(ExpansionTask::Object(macro_info)) => {
                            let new_hs = self.hide_sets.insert(tokens[i].hide_set, symbol);
                            let mut expanded =
                                self.expand_virtual_buffer(&macro_info.tokens, symbol, tokens[i].location)?;
                            for t in &mut expanded {
                                t.hide_set = new_hs;
                            }
                            tokens.splice(i..i + 1, expanded);
                            continue;
                        }
                        None => {}
                    }
                } else {
                    // Mark as permanently disabled.
                    tokens[i].flags |= PPTokenFlags::DISABLE_EXPANSION;
                }
            }

            if self.try_handle_pragma_operator_inline(tokens, i) {
                continue;
            }

            i += 1;
        }

        Ok(())
    }

    fn create_virtual_buffer_tokens(
        &mut self,
        tokens: &[PPToken],
        macro_name: StringId,
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
                    let val = self
                        .sm
                        .get_file_info(sid)
                        .is_some_and(|info| info.kind == FileKind::MacroExpansion);
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
            macro_name.as_str(),
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

    pub(super) fn parse_macro_definition_params(
        &mut self,
        macro_name: StringId,
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
                        return self.emit_error(PPErrorKind::InvalidMacroParameter, param_token.location);
                    }
                    break;
                }
                PPTokenKind::Identifier(sym) => {
                    if params.contains(&sym) {
                        return self.emit_error(PPErrorKind::InvalidMacroParameter, param_token.location);
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
                                return self.emit_error(PPErrorKind::InvalidMacroParameter, sep.location);
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
    fn new(sm: &'a SourceManager) -> Self {
        Self {
            sm,
            last_sid: None,
            last_buffer: None,
        }
    }

    fn get_token_bytes<'b>(&'b mut self, token: &'b PPToken) -> &'b [u8] {
        let sid = token.location.source_id();
        let buffer = if self.last_sid == Some(sid) {
            self.last_buffer.unwrap()
        } else if let Some(b) = self.sm.get_buffer_safe(sid) {
            self.last_sid = Some(sid);
            self.last_buffer = Some(b);
            b
        } else {
            return &[];
        };

        let start = token.location.offset() as usize;
        let end = start + token.length as usize;
        if end <= buffer.len() { &buffer[start..end] } else { &[] }
    }
}
