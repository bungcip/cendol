use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticLevel};
use crate::pp::error::{PPDiag, PPError};
use crate::pp::pp_lexer::PPLexer;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::{IncludeStackInfo, MacroFlags, MacroInfo, PPConditionalInfo};
use crate::pp::{DirectiveKind, PPToken, PPTokenFlags, PPTokenKind, PragmaPackKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceManager, SourceSpan};
use std::sync::Arc;

impl<'src> Preprocessor<'src> {
    /// Handle preprocessor directives
    pub(super) fn handle_directive(&mut self) -> Result<(), PPDiag> {
        let token = self.expect_token()?;

        match token.kind {
            PPTokenKind::Identifier(sym) => match self.keywords.is_directive(sym) {
                Some(kind) => match kind {
                    DirectiveKind::If
                    | DirectiveKind::Ifdef
                    | DirectiveKind::Ifndef
                    | DirectiveKind::Elif
                    | DirectiveKind::Elifdef
                    | DirectiveKind::Elifndef
                    | DirectiveKind::Else
                    | DirectiveKind::Endif => self.handle_conditional_directive(kind, token.location),
                    _ => {
                        if self.is_currently_skipping() {
                            self.skip_directive()
                        } else {
                            self.execute_directive(kind)
                        }
                    }
                },
                None => self.emit_error(PPError::InvalidDirective, token.location),
            },
            PPTokenKind::Eod => Ok(()),
            _ => self.emit_error(PPError::InvalidDirective, token.location),
        }
    }

    fn handle_conditional_directive(&mut self, kind: DirectiveKind, location: SourceLoc) -> Result<(), PPDiag> {
        match kind {
            DirectiveKind::If | DirectiveKind::Ifdef | DirectiveKind::Ifndef => {
                if self.is_currently_skipping() {
                    self.push_skipped_conditional();
                    self.skip_directive()
                } else {
                    match kind {
                        DirectiveKind::If => {
                            let tokens = self.parse_conditional_expression()?;
                            let cond = self.evaluate_conditional_expression(tokens)?;
                            self.handle_if(cond)
                        }
                        DirectiveKind::Ifdef => self.handle_ifdef(),
                        DirectiveKind::Ifndef => self.handle_ifndef(),
                        _ => unreachable!(),
                    }
                }
            }
            DirectiveKind::Elif => {
                if self.should_evaluate_conditional() {
                    let tokens = self.parse_conditional_expression()?;
                    let cond = self.evaluate_conditional_expression(tokens)?;
                    self.handle_elif(cond, location)
                } else {
                    self.handle_elif(false, location)
                }
            }
            DirectiveKind::Elifdef | DirectiveKind::Elifndef => {
                let is_ifdef = kind == DirectiveKind::Elifdef;
                if self.should_evaluate_conditional() {
                    match self.expect_identifier() {
                        Ok((_, sym)) => {
                            let cond = self.is_macro_defined(sym) == is_ifdef;
                            self.expect_eod().unwrap_or(());
                            self.handle_elif(cond, location)
                        }
                        Err(_) => self.handle_elif(false, location),
                    }
                } else {
                    // We need to consume the identifier but ignore its result
                    let _ = self.expect_identifier();
                    let _ = self.expect_eod();
                    self.handle_elif(false, location)
                }
            }
            DirectiveKind::Else => self.handle_else(location),
            DirectiveKind::Endif => self.handle_endif(location),
            _ => unreachable!(),
        }
    }

    fn execute_directive(&mut self, kind: DirectiveKind) -> Result<(), PPDiag> {
        match kind {
            DirectiveKind::Define => self.handle_define(),
            DirectiveKind::Undef => self.handle_undef(),
            DirectiveKind::Include => self.handle_include(),
            DirectiveKind::IncludeNext => self.handle_include_next(),
            DirectiveKind::Line => self.handle_line(),
            DirectiveKind::Pragma => self.handle_pragma(),
            DirectiveKind::Error => self.handle_error(),
            DirectiveKind::Warning => self.handle_warning(),
            DirectiveKind::Embed => self.handle_embed(),
            _ => unreachable!("ICE: Conditional directives handled separately"),
        }
    }

    /// Handle _Pragma("...") operator
    pub(super) fn handle_pragma_operator(&mut self) -> Result<(), PPDiag> {
        // We have already consumed the `_Pragma` identifier.
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (symbol, _) = self.expect_string_literal()?;
        let pragma_content = self.destringize(symbol.as_str());
        self.expect_kind(PPTokenKind::RightParen)?;

        self.perform_pragma(&pragma_content);

        Ok(())
    }

    /// Destringize a string literal (remove quotes and handle escapes)
    pub(crate) fn destringize<'a>(&self, full_str: &'a str) -> std::borrow::Cow<'a, str> {
        crate::ast::literal_parsing::unescape(&full_str[1..full_str.len() - 1])
    }

    /// Tokenize the content of a pragma directive
    fn tokenize_pragma_content(&mut self, pragma_content: &str) -> Vec<PPToken> {
        let (mut tokens, source_id) =
            self.tokenize_synthetic(pragma_content.as_bytes().to_vec(), "<_Pragma>", FileKind::Synthetic);

        // Determine location for the synthetic EOD
        let eod_loc = tokens
            .last()
            .map(|t| t.location)
            .unwrap_or(SourceLoc::new(source_id, 0));

        // Append EOD token to mark end of pragma
        tokens.push(PPToken::new(PPTokenKind::Eod, PPTokenFlags::empty(), eod_loc, 0));

        tokens
    }

    /// Perform the action of a pragma directive
    pub(super) fn perform_pragma(&mut self, pragma_content: &str) {
        let tokens = self.tokenize_pragma_content(pragma_content);

        // Bolt ⚡: Use batch insertion to efficiently push pragma tokens onto the stack.
        // This avoids individual allocation checks for each token.
        self.pending_tokens.extend(tokens.into_iter().rev());

        // Execute pragma handler
        // handle_pragma will consume tokens from pending_tokens
        if self.handle_pragma().is_err() {
            // If handle_pragma failed (e.g. unknown pragma), it might not have consumed all tokens.
            // We must consume the remaining tokens of this pragma until EOD to ensure they don't leak.
            while let Some(token) = self.lex_token() {
                if token.kind == PPTokenKind::Eod {
                    break;
                }
            }
        }
    }

    /// Handle #define directive
    fn parse_define_args(&mut self, name: StringId) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPDiag> {
        let Some(token) = self.lex_token() else {
            return Ok((MacroFlags::empty(), Vec::new(), None));
        };

        if token.kind == PPTokenKind::LeftParen && !token.flags.contains(PPTokenFlags::LEADING_SPACE) {
            let first_param = self.expect_token()?;

            if matches!(
                first_param.kind,
                PPTokenKind::RightParen | PPTokenKind::Identifier(_) | PPTokenKind::Ellipsis
            ) {
                self.pending_tokens.push(first_param);
                return self.parse_macro_definition_params(name);
            }

            self.pending_tokens.push(first_param);
            self.pending_tokens.push(token);
            return Ok((MacroFlags::empty(), Vec::new(), None));
        }

        self.pending_tokens.push(token);
        Ok((MacroFlags::empty(), Vec::new(), None))
    }

    fn check_macro_redefinition(&mut self, name: StringId, name_token: &PPToken, macro_info: &MacroInfo) -> bool {
        if let Some(existing) = self.macros.get(&name) {
            // Check if definition is different
            // Mask out runtime state flags (USED, DISABLED) that don't affect definition identity.
            // We also exclude BUILTIN from the comparison itself because we want to allow
            // the user to redefine a built-in macro with an identical definition.
            let identity_flags_mask = MacroFlags::FUNCTION_LIKE | MacroFlags::C99_VARARGS | MacroFlags::GNU_VARARGS;

            let is_different = (existing.flags & identity_flags_mask) != (macro_info.flags & identity_flags_mask)
                || existing.parameter_list != macro_info.parameter_list
                || existing.variadic_arg != macro_info.variadic_arg
                || existing.tokens.len() != macro_info.tokens.len()
                || existing.tokens.iter().zip(macro_info.tokens.iter()).any(|(a, b)| {
                    if a.kind != b.kind {
                        return true;
                    }
                    // For tokens that store text externally, compare the text
                    match a.kind {
                        PPTokenKind::Identifier(_) => false, // Already covered by a.kind != b.kind (stores sym)
                        PPTokenKind::Number | PPTokenKind::StringLiteral | PPTokenKind::CharLiteral(_) => {
                            self.get_token_text(a) != self.get_token_text(b)
                        }
                        _ => false,
                    }
                });

            if existing.flags.contains(MacroFlags::BUILTIN) {
                if is_different {
                    self.report_warning_with_name(
                        name_token.location,
                        format!("Redefinition of built-in macro '{}'", name),
                        "builtin-macro-redefined",
                    );
                }
                // Return false to block overwriting the built-in macro,
                // but we only warn if it was actually different.
                return false;
            }

            if is_different {
                let err = self.error(PPError::MacroRedefined(name), name_token.location);
                self.report_pp_error(err);
            }
        }
        true
    }

    fn handle_define(&mut self) -> Result<(), PPDiag> {
        let (name_token, name) = self.expect_identifier()?;

        let (flags, params, variadic) = self.parse_define_args(name)?;

        // Collect body tokens
        // Use collect_tokens_until_eod which handles the loop and checking for Eod
        let tokens = self.collect_tokens_until_eod();

        // Store the macro
        let mut macro_info = MacroInfo {
            location: name_token.location,
            flags,
            tokens: Arc::from(tokens),
            parameter_list: Arc::from(params),
            variadic_arg: variadic,
            parameter_needs_expansion: Arc::from([]), // Temporarily empty
        };

        // Bolt ⚡: Pre-calculate expansion needs and detect __VA_OPT__.
        let mut needs_expansion = vec![false; macro_info.parameter_list.len() + if variadic.is_some() { 1 } else { 0 }];

        for i in 0..macro_info.tokens.len() {
            let t = &macro_info.tokens[i];
            if let PPTokenKind::Identifier(sym) = t.kind {
                // Check for __VA_OPT__
                if variadic.is_some() && sym == self.keywords.va_opt {
                    macro_info.flags |= MacroFlags::HAS_VA_OPT;
                }

                // Check for parameter usage that requires expansion
                let param_idx = if let Some(pos) = macro_info.parameter_list.iter().position(|&p| p == sym) {
                    Some(pos)
                } else if variadic == Some(sym) {
                    Some(macro_info.parameter_list.len())
                } else {
                    None
                };

                if let Some(idx) = param_idx {
                    let preceded_by_hash = i > 0 && macro_info.tokens[i - 1].kind == PPTokenKind::Hash;
                    let preceded_by_hashhash = i > 0 && macro_info.tokens[i - 1].kind == PPTokenKind::HashHash;
                    let followed_by_hashhash =
                        i + 1 < macro_info.tokens.len() && macro_info.tokens[i + 1].kind == PPTokenKind::HashHash;

                    if !preceded_by_hash && !preceded_by_hashhash && !followed_by_hashhash {
                        needs_expansion[idx] = true;
                    }
                }
            }
        }
        macro_info.parameter_needs_expansion = Arc::from(needs_expansion);

        if self.check_macro_redefinition(name, &name_token, &macro_info) {
            self.macros.insert(name, macro_info);
        }
        Ok(())
    }

    fn handle_undef(&mut self) -> Result<(), PPDiag> {
        let (token, name) = self.expect_identifier()?;

        if let Some(existing) = self.macros.get(&name)
            && existing.flags.contains(MacroFlags::BUILTIN)
        {
            self.report_warning_with_name(
                token.location,
                format!("Undefining built-in macro '{}'", name.as_str()),
                "builtin-macro-redefined",
            );
            self.expect_eod()?;
            return Ok(());
        }

        // Remove the macro from the table if it exists
        self.macros.remove(&name);

        self.expect_eod()?;

        Ok(())
    }

    fn do_handle_include(&mut self, is_next: bool) -> Result<(), PPDiag> {
        let first_token = self.expect_token()?;

        let mut tokens = std::iter::once(first_token)
            .chain(self.collect_tokens_until_eod())
            .collect::<Vec<_>>();

        let (path_str, is_angled) = match tokens[0].kind {
            PPTokenKind::StringLiteral | PPTokenKind::Less => {
                self.parse_include_path_tokens(&tokens, first_token.location, false)?
            }
            _ => {
                self.expand_tokens(&mut tokens, false)?;
                self.parse_include_path_tokens(&tokens, first_token.location, false)?
            }
        };

        if self.include_depth >= self.max_include_depth {
            return self.emit_error(PPError::IncludeDepthExceeded, first_token.location);
        }

        let include_source_id = if is_next {
            self.resolve_next_include_path(&path_str, is_angled, first_token.location)
        } else {
            self.resolve_include_path(&path_str, is_angled, first_token.location)
        }?;

        if !self.once_included.contains(&include_source_id) {
            self.include_stack.push(IncludeStackInfo {
                file_id: include_source_id,
            });

            let buffer = self.sm.get_buffer_arc(include_source_id);
            self.lexer_stack.push(PPLexer::new(include_source_id, buffer));
            self.include_depth += 1;
        }

        Ok(())
    }

    fn parse_include_path_tokens(
        &self,
        tokens: &[PPToken],
        diag_loc: SourceLoc,
        allow_extra: bool,
    ) -> Result<(String, bool), PPDiag> {
        if tokens.is_empty() {
            return self.emit_error(PPError::InvalidIncludePath, diag_loc);
        }

        let first = &tokens[0];
        match first.kind {
            PPTokenKind::StringLiteral => {
                if !allow_extra && tokens.len() > 1 {
                    return self.emit_error(PPError::ExpectedEod, tokens[1].location);
                }
                let text = self.get_token_text(first);
                let path = self
                    .extract_literal_content(&text, first.location, PPError::InvalidIncludePath)?
                    .to_string();
                Ok((path, false))
            }
            PPTokenKind::Less => {
                let mut greater_idx = None;
                for (i, t) in tokens.iter().enumerate().skip(1) {
                    if t.kind == PPTokenKind::Greater {
                        greater_idx = Some(i);
                        break;
                    }
                }
                let idx = greater_idx.ok_or_else(|| self.error(PPError::InvalidIncludePath, diag_loc))?;
                if !allow_extra && idx + 1 < tokens.len() {
                    return self.emit_error(PPError::ExpectedEod, tokens[idx + 1].location);
                }
                let path_parts = &tokens[1..idx];
                Ok((self.tokens_to_string(path_parts), true))
            }
            _ => self.emit_error(PPError::InvalidIncludePath, diag_loc),
        }
    }

    fn handle_include(&mut self) -> Result<(), PPDiag> {
        self.do_handle_include(false)
    }

    fn handle_include_next(&mut self) -> Result<(), PPDiag> {
        self.do_handle_include(true)
    }

    fn handle_embed(&mut self) -> Result<(), PPDiag> {
        let first_token = self.expect_token()?;

        let mut tokens = std::iter::once(first_token)
            .chain(self.collect_tokens_until_eod())
            .collect::<Vec<_>>();

        if !matches!(tokens[0].kind, PPTokenKind::StringLiteral | PPTokenKind::Less) {
            self.expand_tokens(&mut tokens, false)?;
        }

        let (path_str, is_angled) = self.parse_include_path_tokens(&tokens, first_token.location, true)?;

        let mut limit = None;
        let mut i = if is_angled {
            tokens
                .iter()
                .position(|t| t.kind == PPTokenKind::Greater)
                .ok_or_else(|| self.error(PPError::InvalidIncludePath, first_token.location))?
                + 1
        } else {
            1
        };

        while i < tokens.len() {
            let t = &tokens[i];
            if let PPTokenKind::Identifier(sym) = t.kind
                && sym.as_str() == "limit"
            {
                i += 1;
                if i < tokens.len() && tokens[i].kind == PPTokenKind::LeftParen {
                    i += 1;
                    if i < tokens.len() && tokens[i].kind == PPTokenKind::Number {
                        let text = self.get_token_text(&tokens[i]);
                        limit = Some(
                            text.parse::<usize>()
                                .map_err(|_| self.error(PPError::InvalidDirective, tokens[i].location))?,
                        );
                        i += 1;
                    } else {
                        let loc = if i < tokens.len() {
                            tokens[i].location
                        } else {
                            t.location
                        };
                        return self.emit_error(PPError::InvalidDirective, loc);
                    }

                    if i < tokens.len() && tokens[i].kind == PPTokenKind::RightParen {
                        i += 1;
                    } else {
                        return self.emit_error(PPError::InvalidDirective, t.location);
                    }
                } else {
                    return self.emit_error(PPError::InvalidDirective, t.location);
                }
                continue;
            }
            i += 1;
        }

        let include_source_id = self.resolve_include_path(&path_str, is_angled, first_token.location)?;
        let buffer = self.sm.get_buffer_arc(include_source_id);

        let bytes_to_embed = if let Some(l) = limit {
            buffer.len().min(l)
        } else {
            buffer.len()
        };

        if bytes_to_embed == 0 {
            return Ok(());
        }

        // ⚡ Bolt: Direct token generation for #embed.
        // Instead of building a massive string and lexing it, we directly generate
        // PPToken variants in reverse order and push them to the pending_tokens stack.
        // We use a shared "digits" source buffer to back the numeric tokens, which
        // avoids thousands of tiny allocations and lexing overhead.
        let digits_id = self.sm.get_digits_source_id();
        self.pending_tokens.reserve(bytes_to_embed * 2);

        // Pre-fetch metadata to avoid repeated OnceLock overhead in the loop.
        let mut metadata = [(0u32, 0u16); 256];
        for (i, entry) in metadata.iter_mut().enumerate() {
            *entry = SourceManager::get_digit_metadata(i as u8);
        }

        let comma_token = PPToken::new(PPTokenKind::Comma, PPTokenFlags::LEADING_SPACE, SourceLoc::builtin(), 1);

        for (idx, &byte) in buffer[..bytes_to_embed].iter().enumerate().rev() {
            let (offset, len) = metadata[byte as usize];
            let mut t = PPToken::new(
                PPTokenKind::Number,
                PPTokenFlags::LEADING_SPACE,
                SourceLoc::new(digits_id, offset),
                len,
            );
            // The first token in the stream (idx 0) has no leading space from #embed itself.
            if idx == 0 {
                t.flags &= !PPTokenFlags::LEADING_SPACE;
            }
            self.pending_tokens.push(t);

            if idx > 0 {
                self.pending_tokens.push(comma_token);
            }
        }

        Ok(())
    }

    fn resolve_include_path(&mut self, path: &str, is_angled: bool, loc: SourceLoc) -> Result<SourceId, PPDiag> {
        let current_dir = self.get_current_dir();
        let resolved = self.header_search.resolve_path(path, is_angled, current_dir);

        if let Some(id) = self.load_resolved_header(path, resolved, loc)? {
            return Ok(id);
        }

        let fallback_id = if is_angled {
            self.built_in_file_ids.get(path).copied()
        } else {
            self.sm.get_file_id(path)
        };

        if let Some(id) = fallback_id {
            Ok(id)
        } else {
            self.emit_error(PPError::FileNotFound { path: path.to_string() }, loc)
        }
    }

    fn resolve_next_include_path(&mut self, path: &str, is_angled: bool, loc: SourceLoc) -> Result<SourceId, PPDiag> {
        let current_dir = self.get_current_dir();
        let resolved = self.header_search.resolve_next_path(path, is_angled, current_dir);

        if let Some(id) = self.load_resolved_header(path, resolved, loc)? {
            return Ok(id);
        }

        if is_angled && let Some(id) = self.built_in_file_ids.get(path).copied() {
            let is_recursive = if let Some(current) = self.lexer_stack.last() {
                current.source_id == id
            } else {
                false
            };

            if !is_recursive {
                return Ok(id);
            }
        }

        self.emit_error(PPError::FileNotFound { path: path.to_string() }, loc)
    }

    fn handle_if(&mut self, condition: bool) -> Result<(), PPDiag> {
        // Bolt ⚡: Ensure the skipping state is propagated downward.
        let was_skipping = self.is_currently_skipping() || !condition;
        self.conditional_stack.push(PPConditionalInfo {
            was_skipping,
            found_else: false,
            found_non_skipping: condition,
        });
        Ok(())
    }

    fn handle_ifdef(&mut self) -> Result<(), PPDiag> {
        self.handle_conditional_def(true)
    }

    fn handle_ifndef(&mut self) -> Result<(), PPDiag> {
        self.handle_conditional_def(false)
    }

    fn handle_conditional_def(&mut self, is_ifdef: bool) -> Result<(), PPDiag> {
        let (_, sym) = self.expect_identifier()?;

        let condition = self.is_macro_defined(sym) == is_ifdef;
        self.handle_if(condition)?;
        self.expect_eod()
    }

    fn get_parent_skipping(&self) -> bool {
        if self.conditional_stack.len() > 1 {
            self.conditional_stack[self.conditional_stack.len() - 2].was_skipping
        } else {
            false
        }
    }

    fn handle_elif_or_else(&mut self, condition: Option<bool>, location: SourceLoc) -> Result<(), PPDiag> {
        let is_elif = condition.is_some();
        let empty_error = if is_elif {
            PPError::ElifWithoutIf
        } else {
            PPError::ElseWithoutIf
        };

        if self.conditional_stack.is_empty() {
            return self.emit_error(empty_error, location);
        }

        let parent_skipping = self.get_parent_skipping();
        let current = self.conditional_stack.last_mut().unwrap();

        let dup_error = if is_elif {
            PPError::ElifAfterElse
        } else {
            PPError::MultipleElse
        };
        if current.found_else {
            return self.emit_error(dup_error, location);
        }

        if !is_elif {
            current.found_else = true;
        }

        let cond = condition.unwrap_or(true);
        let should_process = !current.found_non_skipping && cond;
        if should_process {
            current.found_non_skipping = true;
        }
        current.was_skipping = parent_skipping || !should_process;

        Ok(())
    }

    fn handle_elif(&mut self, condition: bool, location: SourceLoc) -> Result<(), PPDiag> {
        self.handle_elif_or_else(Some(condition), location)
    }

    fn handle_else(&mut self, location: SourceLoc) -> Result<(), PPDiag> {
        self.handle_elif_or_else(None, location)?;
        self.expect_eod()
    }

    fn handle_endif(&mut self, location: SourceLoc) -> Result<(), PPDiag> {
        if self.conditional_stack.pop().is_none() {
            return self.emit_error(PPError::UnmatchedEndif, location);
        }
        self.expect_eod()
    }

    fn parse_line_directive_args(&self, tokens: &[PPToken]) -> Result<(u32, Option<String>), PPDiag> {
        let (first, rest) = tokens
            .split_first()
            .ok_or_else(|| self.error(PPError::InvalidLineDirective, SourceLoc::builtin()))?;

        let PPTokenKind::Number = first.kind else {
            return self.emit_error(PPError::InvalidLineDirective, first.location);
        };

        let symbol_text = self.get_token_text(first);
        let line_num = symbol_text
            .parse::<u32>()
            .ok()
            .filter(|&n| n > 0)
            .ok_or_else(|| self.error(PPError::InvalidLineDirective, first.location))?;

        let filename = match rest {
            [] => None,
            [t] => {
                let PPTokenKind::StringLiteral = t.kind else {
                    return self.emit_error(PPError::InvalidLineDirective, t.location);
                };
                let text = self.get_token_text(t);
                Some(
                    self.extract_literal_content(&text, t.location, PPError::InvalidLineDirective)?
                        .to_string(),
                )
            }
            _ => return self.emit_error(PPError::InvalidLineDirective, first.location),
        };

        Ok((line_num, filename))
    }

    fn handle_line(&mut self) -> Result<(), PPDiag> {
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line(self.sm)
        } else {
            0
        };

        // Collect tokens until end of line
        let mut tokens = self.collect_tokens_until_eod();

        if tokens.is_empty() {
            let loc = self.get_current_location();
            return self.emit_error(PPError::InvalidLineDirective, loc);
        }

        // Expand macros in tokens
        self.expand_tokens(&mut tokens, false)?;

        let (logical_line, logical_file) = self.parse_line_directive_args(&tokens)?;

        // Get current physical line (where #line directive appears)
        let physical_line = start_line;

        // The #line directive sets the line number for the following line,
        // so we need to adjust the logical_line for the entry
        let entry_logical_line = logical_line - 1;

        // Add entry to LineMap
        if let Some(lexer) = self.lexer_stack.last()
            && let Some(line_map) = self.sm.get_line_map_mut(lexer.source_id)
        {
            let entry = crate::source_manager::LineDirective::new(physical_line, entry_logical_line, logical_file);
            line_map.add_entry(entry);
        }

        Ok(())
    }

    fn handle_pragma(&mut self) -> Result<(), PPDiag> {
        let (token, symbol) = self.expect_identifier()?;

        if symbol == self.keywords.once {
            if let Some(lexer) = self.lexer_stack.last() {
                self.once_included.insert(lexer.source_id);
            }
        } else if symbol == self.keywords.push_macro {
            self.handle_push_macro()?;
        } else if symbol == self.keywords.pop_macro {
            self.handle_pop_macro()?;
        } else if symbol == self.keywords.message {
            self.handle_pragma_message()?;
        } else if symbol == self.keywords.warning {
            self.handle_pragma_warning(DiagnosticLevel::Warning)?;
        } else if symbol == self.keywords.error {
            self.handle_pragma_error(DiagnosticLevel::Error)?;
        } else if symbol == self.keywords.pack {
            return self.handle_pragma_pack();
        } else {
            return self.emit_error(PPError::UnknownPragma(symbol), token.location);
        }

        self.collect_tokens_until_eod();
        Ok(())
    }

    fn parse_pragma_macro_name(&mut self) -> Result<StringId, PPDiag> {
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (text, token_loc) = self.expect_string_literal()?;

        let name = self.extract_literal_content(&text, token_loc, PPError::InvalidDirective)?;
        self.expect_kind(PPTokenKind::RightParen)?;

        Ok(StringId::new(name))
    }

    fn handle_push_macro(&mut self) -> Result<(), PPDiag> {
        let name = self.parse_pragma_macro_name()?;
        let info = self.macros.get(&name).cloned();
        self.macro_stack.entry(name).or_default().push(info);

        Ok(())
    }

    fn handle_pop_macro(&mut self) -> Result<(), PPDiag> {
        let name = self.parse_pragma_macro_name()?;

        if let Some(stack) = self.macro_stack.get_mut(&name)
            && let Some(info_opt) = stack.pop()
        {
            if let Some(info) = info_opt {
                self.macros.insert(name, info);
            } else {
                self.macros.remove(&name);
            }
        }

        Ok(())
    }

    fn parse_pragma_message_content(&mut self) -> Result<String, PPDiag> {
        let mut tokens = self.collect_balanced_tokens(PPTokenKind::LeftParen, PPTokenKind::RightParen)?;
        self.expand_tokens(&mut tokens, false)?;

        tokens.into_iter().try_fold(String::new(), |mut acc, t| {
            let PPTokenKind::StringLiteral = t.kind else {
                return self.emit_error(PPError::InvalidDirective, t.location);
            };
            acc.push_str(&self.destringize(&self.get_token_text(&t)));
            Ok(acc)
        })
    }

    fn handle_pragma_diagnostic_message(&mut self, level: DiagnosticLevel) -> Result<(), PPDiag> {
        let message = self.parse_pragma_message_content()?;
        let loc = self.get_current_location();
        let diag = Diagnostic {
            level,
            message: message.clone(),
            span: SourceSpan::from_loc(loc),
            ..Default::default()
        };
        self.diag.report_diagnostic(diag);

        if level == DiagnosticLevel::Error {
            self.emit_error(PPError::PragmaError(message), loc)
        } else {
            Ok(())
        }
    }

    fn handle_pragma_message(&mut self) -> Result<(), PPDiag> {
        self.handle_pragma_diagnostic_message(DiagnosticLevel::Note)
    }

    fn handle_pragma_warning(&mut self, level: DiagnosticLevel) -> Result<(), PPDiag> {
        self.handle_pragma_diagnostic_message(level)
    }

    fn handle_pragma_error(&mut self, level: DiagnosticLevel) -> Result<(), PPDiag> {
        self.handle_pragma_diagnostic_message(level)
    }

    fn handle_diagnostic_directive(&mut self, is_error: bool) -> Result<(), PPDiag> {
        let directive_location = self.get_current_location();
        let message = self.read_directive_message();

        let formatted_message = if is_error {
            format!("#error directive: {}", message)
        } else {
            message.clone()
        };

        if is_error {
            self.report_error(directive_location, formatted_message);
        } else {
            self.report_warning_with_name(directive_location, formatted_message, "#warnings");
        }

        if is_error {
            self.emit_error(PPError::ErrorDirective(message), directive_location)
        } else {
            Ok(())
        }
    }

    fn handle_pragma_pack(&mut self) -> Result<(), PPDiag> {
        let tokens = self.collect_tokens_until_eod();
        let loc = self.get_current_location();

        if tokens.is_empty() {
            let token = PPToken::new(
                PPTokenKind::PragmaPack(PragmaPackKind::Set(None)),
                PPTokenFlags::empty(),
                loc,
                0,
            );
            self.pending_tokens.push(token);
            return Ok(());
        }

        let mut it = tokens.iter().peekable();

        // Optional '('
        let has_paren = if let Some(t) = it.peek()
            && t.kind == PPTokenKind::LeftParen
        {
            it.next();
            true
        } else {
            false
        };

        // If '()', it's Set(None)
        let kind = if has_paren && it.peek().map(|t| t.kind) == Some(PPTokenKind::RightParen) {
            PragmaPackKind::Set(None)
        } else if let Some(t) = it.next() {
            match t.kind {
                PPTokenKind::Identifier(sym) if sym == self.keywords.push => {
                    if it.peek().map(|t| t.kind) == Some(PPTokenKind::Comma) {
                        it.next(); // consume ','
                        let val_token = it
                            .next()
                            .ok_or_else(|| self.error(PPError::UnknownPragma(self.keywords.pack), t.location))?;
                        PragmaPackKind::PushSet(self.parse_pragma_pack_value(val_token)?)
                    } else {
                        PragmaPackKind::Push
                    }
                }
                PPTokenKind::Identifier(sym) if sym == self.keywords.pop => PragmaPackKind::Pop,
                PPTokenKind::Identifier(_) | PPTokenKind::Number => {
                    PragmaPackKind::Set(Some(self.parse_pragma_pack_value(t)?))
                }
                _ => return self.emit_error(PPError::UnknownPragma(self.keywords.pack), t.location),
            }
        } else {
            PragmaPackKind::Set(None)
        };

        if has_paren {
            if let Some(t) = it.next() {
                if t.kind != PPTokenKind::RightParen {
                    return self.emit_error(PPError::UnknownPragma(self.keywords.pack), t.location);
                }
            } else {
                return self.emit_error(PPError::UnknownPragma(self.keywords.pack), loc);
            }
        }

        if let Some(t) = it.next() {
            return self.emit_error(PPError::ExpectedEod, t.location);
        }

        self.pending_tokens.push(PPToken::new(
            PPTokenKind::PragmaPack(kind),
            PPTokenFlags::empty(),
            loc,
            0,
        ));

        Ok(())
    }

    fn parse_pragma_pack_value(&self, t: &PPToken) -> Result<u8, PPDiag> {
        let text = match t.kind {
            PPTokenKind::Number => self.get_token_text(t),
            PPTokenKind::Identifier(sym) => std::borrow::Cow::Borrowed(sym.as_str()),
            _ => return self.emit_error(PPError::UnknownPragma(self.keywords.pack), t.location),
        };

        match text.parse::<u8>() {
            Ok(v) if matches!(v, 1 | 2 | 4 | 8 | 16) => Ok(v),
            _ => {
                let sym = StringId::new(&text);
                self.emit_error(PPError::InvalidPragmaPackValue(sym), t.location)
            }
        }
    }

    fn handle_error(&mut self) -> Result<(), PPDiag> {
        self.handle_diagnostic_directive(true)
    }

    fn handle_warning(&mut self) -> Result<(), PPDiag> {
        self.handle_diagnostic_directive(false)
    }

    fn read_directive_message(&mut self) -> String {
        let tokens = self.collect_tokens_until_eod();
        self.tokens_to_string(&tokens)
    }
}
