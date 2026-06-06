use std::borrow::Cow;

use crate::ast::StringId;
use crate::pp::error::{PPDiag, PPError};
use crate::pp::pp_lexer::PPLexer;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::{MacroFlags, MacroInfo};
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceManager, SourceSpan};

#[derive(Clone, Copy)]
struct SubstitutionCtx<'a> {
    macro_info: &'a MacroInfo,
    symbol: StringId,
    args: &'a [Vec<PPToken>],
    expanded_args: &'a [Cow<'a, [PPToken]>],
    intersect_hs: u32,
    new_hs: u32,
    is_variadic_empty: bool,
    is_va_missing: bool,
}

enum ExpansionTask {
    Function {
        info: MacroInfo,
        symbol: StringId,
        end_idx: usize,
        args: Vec<Vec<PPToken>>,
    },
    Object {
        info: MacroInfo,
        symbol: StringId,
    },
}

impl<'src> Preprocessor<'src> {
    /// Expand a macro if it exists
    pub(super) fn expand_macro(&mut self, token: &PPToken) -> Result<Option<Vec<PPToken>>, PPDiag> {
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

    /// Helper to convert tokens to their string representation.
    /// Preserves LEADING_SPACE between tokens.
    pub(super) fn tokens_to_string(&self, tokens: &[PPToken]) -> String {
        if tokens.is_empty() {
            return String::new();
        }

        // Bolt ⚡: Pre-calculate capacity to avoid redundant reallocations.
        // We add tokens.len() as an upper bound for extra spaces.
        let capacity = tokens.iter().map(|t| t.length as usize).sum::<usize>() + tokens.len();
        let mut result = String::with_capacity(capacity);

        let mut cache = SourceBufferCache::new(self.sm);

        for (i, token) in tokens.iter().enumerate() {
            // Bolt ⚡: Preserve leading spaces between tokens.
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                result.push(' ');
            }
            result.push_str(&cache.get_token_text(token));
        }
        result
    }

    /// Expand an object-like macro
    fn expand_object_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPDiag> {
        let new_hs = self.hide_sets.insert(token.hide_set, symbol);

        let substituted = self.substitute_tokens_slice(
            &macro_info.tokens,
            &SubstitutionCtx {
                macro_info,
                symbol,
                args: &[],
                expanded_args: &[],
                intersect_hs: token.hide_set,
                new_hs,
                is_variadic_empty: false,
                is_va_missing: false,
            },
        )?;

        Ok(self.create_virtual_buffer_tokens(&substituted, symbol, token.location))
    }

    /// Expand a function-like macro
    fn expand_function_macro(
        &mut self,
        macro_info: &MacroInfo,
        symbol: StringId,
        token: &PPToken,
    ) -> Result<Vec<PPToken>, PPDiag> {
        let (mut args, rparen_token) = match self.parse_macro_args_from_lexer(macro_info) {
            Ok(args) => args,
            Err(PPDiag {
                kind: PPError::InvalidMacroParameter,
                ..
            }) => {
                return self.emit_error(PPError::InvalidMacroParameter, token.location);
            }
            Err(e) => return Err(e),
        };

        let (is_variadic_empty, is_va_missing) = self.precalculate_variadic_args(macro_info, &mut args);

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for (idx, arg) in args.iter().enumerate() {
            let needs_expansion = macro_info.parameter_needs_expansion.get(idx).copied().unwrap_or(false);

            if needs_expansion {
                let mut arg_clone = arg.clone();
                // GCC semantics: Arguments are pre-expanded in an independent context.
                // Do not inherit caller's hide sets during pre-expansion!
                for t in &mut arg_clone {
                    if let PPTokenKind::Identifier(symbol) = t.kind
                        && self.hide_sets.contains(t.hide_set, symbol)
                    {
                        t.flags |= PPTokenFlags::DISABLE_EXPANSION;
                    }
                    t.hide_set = 0;
                }
                self.expand_tokens(&mut arg_clone, false)?;
                expanded_args.push(Cow::Owned(arg_clone));
            } else {
                expanded_args.push(Cow::Borrowed(arg.as_slice()));
            }
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

        Ok(self.create_virtual_buffer_tokens(&substituted, symbol, token.location))
    }

    /// Parse macro arguments from the current lexer
    fn parse_macro_args_from_lexer(&mut self, macro_info: &MacroInfo) -> Result<(Vec<Vec<PPToken>>, PPToken), PPDiag> {
        let token = self.expect_token()?;
        if token.kind != PPTokenKind::LeftParen {
            self.pending_tokens.push(token);
            return self.emit_error(PPError::InvalidMacroParameter, token.location);
        }

        self.in_macro_argument_parsing += 1;
        let res = self.parse_macro_args_from_lexer_loop(macro_info);
        self.in_macro_argument_parsing -= 1;
        res
    }

    fn parse_macro_args_from_lexer_loop(
        &mut self,
        macro_info: &MacroInfo,
    ) -> Result<(Vec<Vec<PPToken>>, PPToken), PPDiag> {
        let mut args = Vec::with_capacity(macro_info.parameter_list.len());
        let mut current_arg = Vec::new();
        let mut depth = 0;

        while let Some(t) = self.next_token_with_directives()? {
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

                    return self.emit_error(PPError::InvalidMacroParameter, macro_info.location);
                }
                PPTokenKind::Comma if depth == 0 => {
                    args.push(std::mem::take(&mut current_arg));
                }
                _ => current_arg.push(t),
            }
        }

        self.emit_error_span(PPError::UnexpectedEndOfFile, self.get_current_span())
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
        if macro_info.variadic_arg.is_none() {
            return (false, false);
        }
        let start = macro_info.parameter_list.len();
        let is_empty = self.is_variadic_args_empty(macro_info, args);
        let is_missing = args.len() <= start;
        let combined = self.collect_variadic_args_with_commas(args, start);
        args.truncate(start);
        args.push(combined);
        (is_empty, is_missing)
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

    fn get_macro_param_tokens<'a, T: AsRef<[PPToken]>>(
        &self,
        macro_info: &MacroInfo,
        symbol: StringId,
        args: &'a [T],
    ) -> Option<&'a [PPToken]> {
        if let Some(idx) = macro_info.parameter_list.iter().position(|&p| p == symbol) {
            return Some(args[idx].as_ref());
        }
        if macro_info.variadic_arg == Some(symbol) {
            // Combined variadic tokens are stored at the index matching parameter_list.len()
            let idx = macro_info.parameter_list.len();
            if idx < args.len() {
                return Some(args[idx].as_ref());
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

    fn resolve_va_opt(&mut self, ctx: &SubstitutionCtx) -> Result<Option<Vec<PPToken>>, PPDiag> {
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
                    let substituted = if !is_empty {
                        let content = &macro_info.tokens[i + 3..rparen_idx - 1];
                        let mut content_ctx = *ctx;
                        content_ctx.is_va_missing = false; // __VA_OPT__ content substitution doesn't use GNU comma swallowing
                        self.substitute_tokens_slice(content, &content_ctx)?
                    } else {
                        Vec::new()
                    };
                    let mut stringified = self.stringify_tokens(&substituted, token.location)?;
                    stringified.hide_set = token.hide_set;
                    resolved.push(stringified);
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
    fn substitute_macro(&mut self, ctx: SubstitutionCtx) -> Result<Vec<PPToken>, PPDiag> {
        let tokens = self.resolve_va_opt(&ctx)?;
        let tokens_ref = tokens.as_deref().unwrap_or(&ctx.macro_info.tokens);
        self.substitute_tokens_slice(tokens_ref, &ctx)
    }

    fn substitute_tokens_slice(
        &mut self,
        tokens_slice: &[PPToken],
        ctx: &SubstitutionCtx,
    ) -> Result<Vec<PPToken>, PPDiag> {
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
                        if token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                            stringified.flags |= PPTokenFlags::LEADING_SPACE;
                        }
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
                    let param_tokens = if next_is_hh {
                        self.get_macro_param_tokens(ctx.macro_info, sym, ctx.args)
                    } else {
                        self.get_macro_param_tokens(ctx.macro_info, sym, ctx.expanded_args)
                    };

                    if let Some(param_tokens) = param_tokens {
                        if param_tokens.is_empty() {
                            last_token_produced_output = false;
                        } else {
                            let start_idx = result.len();
                            result.extend_from_slice(param_tokens);

                            // Bolt ⚡: Transfer LEADING_SPACE flag from the parameter identifier in the macro body
                            // to the first token of the argument expansion.
                            if token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                                result[start_idx].flags |= PPTokenFlags::LEADING_SPACE;
                            }

                            for t in &mut result[start_idx..] {
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
    ) -> Result<(Vec<PPToken>, bool), PPDiag> {
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
            if !pasted.is_empty() && l.flags.contains(PPTokenFlags::LEADING_SPACE) {
                pasted[0].flags |= PPTokenFlags::LEADING_SPACE;
            }
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
    fn stringify_tokens(&mut self, tokens: &[PPToken], location: SourceLoc) -> Result<PPToken, PPDiag> {
        // Bolt ⚡: Pre-calculate capacity and use Vec<u8> to avoid multiple reallocations and redundant UTF-8 validation.
        // We add a small margin (extra 8 bytes) to account for some escaped characters.
        let capacity = 10 + tokens.len() + tokens.iter().map(|t| t.length as usize).sum::<usize>();
        let mut result = Vec::with_capacity(capacity);
        result.push(b'"');

        let mut cache = SourceBufferCache::new(self.sm);

        for (i, token) in tokens.iter().enumerate() {
            if i > 0 && token.flags.contains(PPTokenFlags::LEADING_SPACE) {
                result.push(b' ');
            }

            let text = cache.get_token_text(token);

            if matches!(token.kind, PPTokenKind::StringLiteral | PPTokenKind::CharLiteral(_)) {
                // Bolt ⚡: High-speed byte-based iteration for escaping.
                for &b in text.as_bytes() {
                    if b == b'"' || b == b'\\' {
                        result.push(b'\\');
                    }
                    result.push(b);
                }
            } else {
                result.extend_from_slice(text.as_bytes());
            }
        }

        result.push(b'"');
        let final_len = result.len();

        let source_id = self
            .sm
            .add_buffer(result, "<stringified-tokens>", Some(location), FileKind::MacroExpansion);

        Ok(PPToken::new(
            PPTokenKind::StringLiteral,
            PPTokenFlags::empty(),
            SourceLoc::new(source_id, 0),
            final_len as u16,
        ))
    }

    /// Paste tokens for ## operator
    fn paste_tokens(&mut self, left: &PPToken, right: &PPToken) -> Result<Vec<PPToken>, PPDiag> {
        let left_span = SourceSpan::from_loc_and_length(left.location, left.length as u32);
        let left_text = self.sm.get_source_text(left_span);

        let right_span = SourceSpan::from_loc_and_length(right.location, right.length as u32);
        let right_text = self.sm.get_source_text(right_span);

        // ⚡ Bolt: Avoid redundant format! and clone by building the byte buffer directly.
        let mut virtual_buffer = Vec::with_capacity(left_text.len() + right_text.len());
        virtual_buffer.extend_from_slice(left_text.as_bytes());
        virtual_buffer.extend_from_slice(right_text.as_bytes());
        let virtual_id = self.sm.add_buffer(
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

    fn expand_range_and_splice(
        &mut self,
        tokens: &mut Vec<PPToken>,
        start: usize,
        end: usize,
        computed_include: bool,
    ) -> Result<usize, PPDiag> {
        let mut args = tokens[start..end].to_vec();
        if computed_include {
            self.expand_has_include_computed_args(&mut args);
        } else {
            self.expand_tokens(&mut args, false)?;
        }
        let len = args.len();
        tokens.splice(start..end, args);
        Ok(start + len)
    }

    fn try_handle_conditional_operator(
        &mut self,
        tokens: &mut Vec<PPToken>,
        i: usize,
    ) -> Result<Option<usize>, PPDiag> {
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
        if (sym == self.keywords.has_include || sym == self.keywords.has_include_next)
            && !self.macros.contains_key(&sym)
        {
            let next = i + 1;
            if let Some(PPTokenKind::LeftParen) = tokens.get(next).map(|t| &t.kind)
                && let arg_start = next + 1
                && let Some(arg_t) = tokens.get(arg_start)
                && let Some(arg_end) = Self::find_balanced_paren_range(tokens, next)
            {
                match arg_t.kind {
                    PPTokenKind::Less | PPTokenKind::StringLiteral => {
                        return Ok(Some(arg_end));
                    }
                    _ => {
                        // Computed form: __has_include(MACRO)
                        let next_i = self.expand_range_and_splice(tokens, arg_start, arg_end - 1, true)?;
                        return Ok(Some(next_i + 1));
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
                let next_i = self.expand_range_and_splice(tokens, arg_start, arg_end - 1, false)?;
                return Ok(Some(next_i + 1));
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
            let token_text = tokens[i + 2].get_text(self.sm);
            let content = self.destringize(&token_text).into_owned();
            self.perform_pragma(&content);
            tokens.drain(i..i + 4);
            return true;
        }
        false
    }

    /// Expand tokens by rescanning for further macro expansion
    pub(super) fn expand_tokens(&mut self, tokens: &mut Vec<PPToken>, in_conditional: bool) -> Result<(), PPDiag> {
        let mut i = 0;
        while i < tokens.len() {
            let token = tokens[i];

            // Bolt ⚡: Hoist identifier guard to fast-track literals/operators.
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

            if let Some(task) = self.try_get_expansion_task(tokens, i) {
                match task {
                    ExpansionTask::Function {
                        info,
                        symbol,
                        end_idx,
                        args,
                    } => {
                        let mut expanded =
                            self.do_function_expansion(info, symbol, end_idx, args, tokens, i, in_conditional)?;
                        if !expanded.is_empty() {
                            if tokens[i].flags.contains(PPTokenFlags::LEADING_SPACE) {
                                expanded[0].flags |= PPTokenFlags::LEADING_SPACE;
                            } else {
                                expanded[0].flags &= !PPTokenFlags::LEADING_SPACE;
                            }
                        } else if i + 1 < tokens.len() && tokens[i].flags.contains(PPTokenFlags::LEADING_SPACE) {
                            // Bolt ⚡: Propagation for empty expansion.
                            tokens[i + 1].flags |= PPTokenFlags::LEADING_SPACE;
                        }

                        if expanded.len() <= 10000 {
                            tokens.splice(i..end_idx, expanded);
                            continue;
                        }
                    }
                    ExpansionTask::Object { info, symbol } => {
                        let mut expanded = self.do_object_expansion(info, symbol, tokens, i)?;
                        if !expanded.is_empty() {
                            if tokens[i].flags.contains(PPTokenFlags::LEADING_SPACE) {
                                expanded[0].flags |= PPTokenFlags::LEADING_SPACE;
                            } else {
                                expanded[0].flags &= !PPTokenFlags::LEADING_SPACE;
                            }
                        } else if i + 1 < tokens.len() && tokens[i].flags.contains(PPTokenFlags::LEADING_SPACE) {
                            // Bolt ⚡: Propagation for empty expansion.
                            tokens[i + 1].flags |= PPTokenFlags::LEADING_SPACE;
                        }
                        tokens.splice(i..i + 1, expanded);
                        continue;
                    }
                }
            } else if let PPTokenKind::Identifier(symbol) = tokens[i].kind {
                // Bolt ⚡: Mark as permanently disabled for this rescan if it's in the hide-set.
                // This satisfies recursive expansion invariants and speeds up consecutive scans.
                if self.hide_sets.contains(tokens[i].hide_set, symbol) {
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

    fn try_get_expansion_task(&mut self, tokens: &[PPToken], i: usize) -> Option<ExpansionTask> {
        let PPTokenKind::Identifier(symbol) = tokens[i].kind else {
            return None;
        };

        if self.hide_sets.contains(tokens[i].hide_set, symbol) {
            // Mark as permanently disabled for this rescan.
            return None;
        }

        if tokens[i].flags.contains(PPTokenFlags::DISABLE_EXPANSION) {
            return None;
        }

        let m = self.macros.get_mut(&symbol)?;
        if m.flags.contains(MacroFlags::DISABLED) {
            return None;
        }

        if m.flags.contains(MacroFlags::FUNCTION_LIKE) {
            // Try function-like expansion
            if i + 1 < tokens.len()
                && tokens[i + 1].kind == PPTokenKind::LeftParen
                && let Some(end_idx) = Self::find_balanced_paren_range(tokens, i + 1)
            {
                let args = Self::collect_macro_args_from_slice(m, tokens, i + 2, end_idx - 1);

                let expected = m.parameter_list.len();
                let valid = if m.variadic_arg.is_some() {
                    args.len() >= expected
                } else {
                    args.len() == expected
                };

                if valid {
                    m.flags |= MacroFlags::USED;
                    let info = m.clone();
                    return Some(ExpansionTask::Function {
                        info,
                        symbol,
                        end_idx,
                        args,
                    });
                }
            }
            None
        } else {
            // Object-like expansion
            m.flags |= MacroFlags::USED;
            let info = m.clone();
            Some(ExpansionTask::Object { info, symbol })
        }
    }

    fn do_function_expansion(
        &mut self,
        info: MacroInfo,
        symbol: StringId,
        end_idx: usize,
        mut args: Vec<Vec<PPToken>>,
        tokens: &[PPToken],
        i: usize,
        in_conditional: bool,
    ) -> Result<Vec<PPToken>, PPDiag> {
        let (is_variadic_empty, is_va_missing) = self.precalculate_variadic_args(&info, &mut args);

        // Pre-expand arguments (prescan)
        let mut expanded_args = Vec::with_capacity(args.len());
        for (idx, arg) in args.iter().enumerate() {
            let needs_expansion = info.parameter_needs_expansion.get(idx).copied().unwrap_or(false);

            if needs_expansion {
                let mut arg_clone = arg.clone();
                // Bolt ⚡: Ignore errors during argument prescan to match original behavior.
                let _ = self.expand_tokens(&mut arg_clone, in_conditional);
                expanded_args.push(Cow::Owned(arg_clone));
            } else {
                expanded_args.push(Cow::Borrowed(arg.as_slice()));
            }
        }

        let intersect_hs = self
            .hide_sets
            .intersection(tokens[i].hide_set, tokens[end_idx - 1].hide_set);
        let new_hs = self.hide_sets.insert(intersect_hs, symbol);

        let substituted = self.substitute_macro(SubstitutionCtx {
            macro_info: &info,
            symbol,
            args: &args,
            expanded_args: &expanded_args,
            intersect_hs,
            new_hs,
            is_variadic_empty,
            is_va_missing,
        })?;

        Ok(self.create_virtual_buffer_tokens(&substituted, symbol, tokens[i].location))
    }

    fn do_object_expansion(
        &mut self,
        info: MacroInfo,
        symbol: StringId,
        tokens: &[PPToken],
        i: usize,
    ) -> Result<Vec<PPToken>, PPDiag> {
        let new_hs = self.hide_sets.insert(tokens[i].hide_set, symbol);
        let substituted = self.substitute_tokens_slice(
            &info.tokens,
            &SubstitutionCtx {
                macro_info: &info,
                symbol,
                args: &[],
                expanded_args: &[],
                intersect_hs: tokens[i].hide_set,
                new_hs,
                is_variadic_empty: false,
                is_va_missing: false,
            },
        )?;

        Ok(self.create_virtual_buffer_tokens(&substituted, symbol, tokens[i].location))
    }

    fn create_virtual_buffer_tokens(
        &mut self,
        tokens: &[PPToken],
        macro_name: StringId,
        trigger_location: SourceLoc,
    ) -> Vec<PPToken> {
        if tokens.is_empty() {
            return Vec::new();
        }

        // Bolt ⚡: Pre-calculate capacity to include potential spaces.
        // This avoids reallocations during buffer construction.
        let capacity = tokens.iter().map(|t| t.length as usize).sum::<usize>() + tokens.len();
        let mut buffer = Vec::with_capacity(capacity);
        let mut metadata = Vec::with_capacity(tokens.len());

        {
            let mut cache = SourceBufferCache::new(self.sm);
            let mut last_sid = (None, false);

            for t in tokens {
                let sid = t.location.source_id();
                if last_sid.0 != Some(sid) {
                    let is_virtual = self
                        .sm
                        .get_file_info(sid)
                        .is_some_and(|info| info.kind == FileKind::MacroExpansion);
                    last_sid = (Some(sid), is_virtual);
                }

                // Bolt ⚡: Preserve leading spaces between tokens in the virtual buffer.
                // This significantly improves diagnostic readability by preventing tokens
                // from being merged in error snippets (e.g. 'struct{inta;}' vs 'struct { int a; }').
                if !buffer.is_empty() && t.flags.contains(PPTokenFlags::LEADING_SPACE) {
                    buffer.push(b' ');
                }

                let offset = buffer.len() as u32;
                buffer.extend_from_slice(cache.get_token_bytes(t));
                let new_len = (buffer.len() as u32 - offset) as u16;
                metadata.push((last_sid.1, offset, new_len));
            }
        }

        let virtual_id = self.sm.add_buffer(
            buffer,
            macro_name.as_str(),
            Some(trigger_location),
            FileKind::MacroExpansion,
        );

        // Bolt ⚡: Use Vec::with_capacity and extend for the final token list.
        let mut result = Vec::with_capacity(tokens.len());
        for (t, (preserve, offset, len)) in tokens.iter().zip(metadata) {
            let loc = if preserve {
                t.location
            } else {
                SourceLoc::new(virtual_id, offset)
            };
            let mut token = PPToken::new(t.kind, t.flags | PPTokenFlags::MACRO_EXPANDED, loc, len);
            token.hide_set = t.hide_set;
            result.push(token);
        }
        result
    }

    pub(super) fn parse_macro_definition_params(
        &mut self,
        _macro_name: StringId,
    ) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPDiag> {
        let mut flags = MacroFlags::FUNCTION_LIKE;
        let mut params = Vec::new();
        let mut variadic = None;

        loop {
            let token = self.expect_token()?;
            match token.kind {
                PPTokenKind::RightParen => break,
                PPTokenKind::Ellipsis => {
                    flags |= MacroFlags::C99_VARARGS;
                    variadic = Some(self.keywords.va_args);
                    self.expect_kind(PPTokenKind::RightParen)?;
                    break;
                }
                PPTokenKind::Identifier(sym) => {
                    if sym == self.keywords.va_args {
                        self.report_warning_with_name(
                            token.location,
                            "__VA_ARGS__ can only appear in the expansion of a C99 variadic macro",
                            "variadic-macros",
                        );
                    }
                    if params.contains(&sym) {
                        return self.emit_error(PPError::DuplicateMacroParameter(sym), token.location);
                    }
                    params.push(sym);

                    let sep = self.expect_token()?;
                    match sep.kind {
                        PPTokenKind::Comma => continue,
                        PPTokenKind::RightParen => break,
                        PPTokenKind::Ellipsis => {
                            // GNU named varargs: `arg...`
                            variadic = Some(params.pop().unwrap());
                            flags |= MacroFlags::GNU_VARARGS;
                            self.expect_kind(PPTokenKind::RightParen)?;
                            break;
                        }
                        _ => {
                            return self.emit_error(PPError::ExpectedCommaInMacroParameterList, sep.location);
                        }
                    }
                }
                _ => {
                    return self.emit_error(PPError::InvalidMacroParameter, token.location);
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

    fn get_buffer(&mut self, sid: SourceId) -> Option<&'a [u8]> {
        if self.last_sid == Some(sid) {
            self.last_buffer
        } else {
            let b = self.sm.get_buffer_safe(sid);
            self.last_sid = Some(sid);
            self.last_buffer = b;
            b
        }
    }

    fn get_token_bytes<'b>(&'b mut self, token: &'b PPToken) -> &'b [u8] {
        let Some(buffer) = self.get_buffer(token.location.source_id()) else {
            return &[];
        };
        let start = token.location.offset() as usize;
        let end = start + token.length as usize;
        if end <= buffer.len() { &buffer[start..end] } else { &[] }
    }

    fn get_token_text<'b>(&'b mut self, token: &'b PPToken) -> Cow<'b, str> {
        let buffer = self.get_buffer(token.location.source_id()).unwrap_or(&[]);
        token.get_text_from_buffer(buffer)
    }
}
