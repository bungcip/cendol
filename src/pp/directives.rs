use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticLevel};
use crate::pp::error::{PPError, PPErrorKind};
use crate::pp::pp_lexer::PPLexer;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::{DirectiveKind, IncludeStackInfo, MacroFlags, MacroInfo, PPConditionalInfo};
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind, PragmaPackKind};
use crate::source_manager::{SourceId, SourceLoc, SourceSpan};
use std::path::Path;
use std::sync::Arc;

impl<'src> Preprocessor<'src> {
    /// Handle preprocessor directives
    pub(crate) fn handle_directive(&mut self) -> Result<(), PPError> {
        let token = self.expect_token()?;

        match token.kind {
            PPTokenKind::Identifier(sym) => match self.directive_keywords.is_directive(sym) {
                Some(kind) => match kind {
                    DirectiveKind::If
                    | DirectiveKind::Ifdef
                    | DirectiveKind::Ifndef
                    | DirectiveKind::Elif
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
                None => self.emit_error_loc(PPErrorKind::InvalidDirective, token.location),
            },
            PPTokenKind::Eod => Ok(()),
            _ => self.emit_error_loc(PPErrorKind::InvalidDirective, token.location),
        }
    }

    fn handle_conditional_directive(
        &mut self,
        kind: DirectiveKind,
        location: SourceLoc,
    ) -> Result<(), PPError> {
        match kind {
            DirectiveKind::If | DirectiveKind::Ifdef | DirectiveKind::Ifndef => {
                if self.is_currently_skipping() {
                    self.push_skipped_conditional();
                    self.skip_directive()
                } else {
                    match kind {
                        DirectiveKind::If => {
                            let tokens = self.parse_conditional_expression().unwrap_or_default();
                            let cond = self.evaluate_conditional_expression(tokens).unwrap_or(false);
                            self.handle_if_directive(cond)
                        }
                        DirectiveKind::Ifdef => self.handle_ifdef(),
                        DirectiveKind::Ifndef => self.handle_ifndef(),
                        _ => unreachable!(),
                    }
                }
            }
            DirectiveKind::Elif => {
                if self.should_evaluate_conditional() {
                    let tokens = self.parse_conditional_expression().unwrap_or_default();
                    let cond = self.evaluate_conditional_expression(tokens).unwrap_or(false);
                    self.handle_elif_directive(cond, location)
                } else {
                    self.handle_elif_directive(false, location)
                }
            }
            DirectiveKind::Else => self.handle_else(location),
            DirectiveKind::Endif => self.handle_endif(location),
            _ => unreachable!(),
        }
    }

    fn execute_directive(&mut self, kind: DirectiveKind) -> Result<(), PPError> {
        match kind {
            DirectiveKind::Define => self.handle_define(),
            DirectiveKind::Undef => self.handle_undef(),
            DirectiveKind::Include => self.handle_include(),
            DirectiveKind::IncludeNext => self.handle_include_next(),
            DirectiveKind::Line => self.handle_line(),
            DirectiveKind::Pragma => self.handle_pragma(),
            DirectiveKind::Error => self.handle_error(),
            DirectiveKind::Warning => self.handle_warning(),
            _ => unreachable!("Conditional directives handled separately"),
        }
    }

    /// Handle _Pragma("...") operator
    pub(crate) fn handle_pragma_operator(&mut self) -> Result<(), PPError> {
        // We have already consumed the `_Pragma` identifier.
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (symbol, _) = self.expect_string_literal()?;
        let pragma_content = self.destringize(symbol.as_str());
        self.expect_kind(PPTokenKind::RightParen)?;

        self.perform_pragma(&pragma_content);

        Ok(())
    }

    /// Destringize a string literal (remove quotes and handle escapes)
    pub(crate) fn destringize(&self, full_str: &str) -> String {
        crate::ast::literal_parsing::unescape_string(&full_str[1..full_str.len() - 1])
    }

    /// Tokenize the content of a pragma directive
    fn tokenize_pragma_content(&mut self, pragma_content: &str) -> Vec<PPToken> {
        // Create a buffer for the pragma content
        let source_id = self
            .sm
            .add_buffer(pragma_content.as_bytes().to_vec(), "<_Pragma>", None);
        let buffer = self.sm.get_buffer_arc(source_id);
        let mut temp_lexer = PPLexer::new(source_id, buffer);

        // Collect all tokens from the pragma content
        let mut tokens = Vec::new();
        while let Some(token) = temp_lexer.next_token() {
            if matches!(token.kind, PPTokenKind::Eod | PPTokenKind::Eof) {
                continue;
            }
            tokens.push(token);
        }

        // Determine location for the synthetic EOD
        let eod_loc = if let Some(last) = tokens.last() {
            last.location
        } else {
            SourceLoc::new(source_id, 0)
        };

        // Append EOD token to mark end of pragma
        tokens.push(PPToken::new(PPTokenKind::Eod, PPTokenFlags::empty(), eod_loc, 0));

        tokens
    }

    /// Perform the action of a pragma directive
    pub(crate) fn perform_pragma(&mut self, pragma_content: &str) {
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
    fn parse_define_args(
        &mut self,
        name: &str,
    ) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPError> {
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

    fn check_macro_redefinition(
        &mut self,
        name: StringId,
        name_token: &PPToken,
        macro_info: &MacroInfo,
    ) -> bool {
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
                || existing
                    .tokens
                    .iter()
                    .zip(macro_info.tokens.iter())
                    .any(|(a, b)| a.kind != b.kind);

            if existing.flags.contains(MacroFlags::BUILTIN) {
                if is_different {
                    self.report_warning(
                        name_token.location,
                        format!("Redefinition of built-in macro '{}'", name),
                    );
                }
                // Return false to block overwriting the built-in macro,
                // but we only warn if it was actually different.
                return false;
            }

            if is_different {
                let err = self.error_loc(
                    PPErrorKind::MacroRedefined {
                        name: name.as_str().to_string(),
                    },
                    name_token.location,
                );
                self.report_pp_error(err);
            }
        }
        true
    }

    fn handle_define(&mut self) -> Result<(), PPError> {
        let (name_token, name) = self.expect_identifier()?;

        let (flags, params, variadic) = self.parse_define_args(name.as_str())?;

        // Collect body tokens
        // Use collect_tokens_until_eod which handles the loop and checking for Eod
        let tokens = self.collect_tokens_until_eod();

        // Store the macro
        let macro_info = MacroInfo {
            location: name_token.location,
            flags,
            tokens: Arc::from(tokens),
            parameter_list: Arc::from(params),
            variadic_arg: variadic,
        };

        if self.check_macro_redefinition(name, &name_token, &macro_info) {
            self.macros.insert(name, macro_info);
        }
        Ok(())
    }

    fn handle_undef(&mut self) -> Result<(), PPError> {
        let (name_token, name) = self.expect_identifier()?;

        if let Some(existing) = self.macros.get(&name)
            && existing.flags.contains(MacroFlags::BUILTIN)
        {
            self.report_warning(
                name_token.location,
                format!("Undefining built-in macro '{}'", name.as_str()),
            );
            self.expect_eod()?;
            return Ok(());
        }

        // Remove the macro from the table if it exists
        self.macros.remove(&name);

        self.expect_eod()?;

        Ok(())
    }

    fn do_handle_include(&mut self, is_next: bool) -> Result<(), PPError> {
        let token = self.expect_token()?;
        let mut eod_consumed = false;

        let (path_str, is_angled) = match token.kind {
            PPTokenKind::StringLiteral(symbol) => {
                let path =
                    self.extract_string_literal_content(symbol, token.location, PPErrorKind::InvalidIncludePath)?;
                (path, false)
            }
            PPTokenKind::Less => {
                let mut path_parts = Vec::new();
                while let Some(t) = self.lex_token() {
                    if t.kind == PPTokenKind::Greater {
                        break;
                    }
                    path_parts.push(t);
                }
                (self.tokens_to_string(&path_parts), true)
            }
            _ => {
                // Computed include
                let mut tokens = vec![token];
                while let Some(t) = self.lex_token() {
                    if t.kind == PPTokenKind::Eod {
                        break;
                    }
                    tokens.push(t);
                }
                eod_consumed = true;
                self.expand_tokens(&mut tokens, false)?;

                if tokens.is_empty() {
                    return self.emit_error_loc(PPErrorKind::InvalidIncludePath, token.location);
                }

                let first = &tokens[0];
                match first.kind {
                    PPTokenKind::StringLiteral(symbol) => {
                        if tokens.len() > 1 {
                            return self.emit_error_loc(PPErrorKind::ExpectedEod, tokens[1].location);
                        }
                        let path = self.extract_string_literal_content(
                            symbol,
                            first.location,
                            PPErrorKind::InvalidIncludePath,
                        )?;
                        (path, false)
                    }
                    PPTokenKind::Less => {
                        let mut path_parts = Vec::new();
                        let mut greater_idx = None;
                        for (i, t) in tokens.iter().enumerate().skip(1) {
                            if t.kind == PPTokenKind::Greater {
                                greater_idx = Some(i);
                                break;
                            }
                            path_parts.push(*t);
                        }
                        let idx = greater_idx
                            .ok_or_else(|| self.error_loc(PPErrorKind::InvalidIncludePath, token.location))?;
                        if idx + 1 < tokens.len() {
                            return self.emit_error_loc(PPErrorKind::ExpectedEod, tokens[idx + 1].location);
                        }
                        (self.tokens_to_string(&path_parts), true)
                    }
                    _ => {
                        return self.emit_error_loc(PPErrorKind::InvalidIncludePath, token.location);
                    }
                }
            }
        };

        if self.include_depth >= self.max_include_depth {
            return self.emit_error_loc(PPErrorKind::IncludeDepthExceeded, token.location);
        }

        let include_source_id = if is_next {
            self.resolve_next_include_path(&path_str, is_angled, token.location)?
        } else {
            self.resolve_include_path(&path_str, is_angled, token.location)?
        };

        if self.once_included.contains(&include_source_id) {
            return Ok(());
        }

        self.include_stack.push(IncludeStackInfo {
            file_id: include_source_id,
        });

        if !eod_consumed {
            self.expect_eod()?;
        }

        let buffer = self.sm.get_buffer_arc(include_source_id);
        self.lexer_stack.push(PPLexer::new(include_source_id, buffer));
        self.include_depth += 1;

        Ok(())
    }

    fn handle_include(&mut self) -> Result<(), PPError> {
        self.do_handle_include(false)
    }

    fn handle_include_next(&mut self) -> Result<(), PPError> {
        self.do_handle_include(true)
    }

    fn resolve_include_path(
        &mut self,
        path: &str,
        is_angled: bool,
        loc: SourceLoc,
    ) -> Result<SourceId, PPError> {
        let current_dir = self
            .lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."));

        let resolved = self.header_search.resolve_path(path, is_angled, current_dir);

        if let Some(path_buf) = resolved {
            return self
                .sm
                .add_file_from_path(&path_buf, Some(loc))
                .map_err(|_| self.error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc));
        }

        let fallback_id = if is_angled {
            self.built_in_file_ids.get(path).copied()
        } else {
            self.sm.get_file_id(path)
        };

        if let Some(id) = fallback_id {
            Ok(id)
        } else {
            self.emit_error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc)
        }
    }

    fn resolve_next_include_path(
        &mut self,
        path: &str,
        is_angled: bool,
        loc: SourceLoc,
    ) -> Result<SourceId, PPError> {
        let current_dir = self
            .lexer_stack
            .last()
            .and_then(|lexer| self.sm.get_file_info(lexer.source_id))
            .and_then(|info| info.path.parent())
            .unwrap_or(Path::new("."));

        let resolved = self.header_search.resolve_next_path(path, is_angled, current_dir);

        if let Some(path_buf) = resolved {
            return self
                .sm
                .add_file_from_path(&path_buf, Some(loc))
                .map_err(|_| self.error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc));
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

        self.emit_error_loc(PPErrorKind::FileNotFound { path: path.to_string() }, loc)
    }

    fn handle_if_directive(&mut self, condition: bool) -> Result<(), PPError> {
        // Bolt ⚡: Ensure the skipping state is propagated downward.
        let was_skipping = self.is_currently_skipping() || !condition;
        self.conditional_stack.push(PPConditionalInfo {
            was_skipping,
            found_else: false,
            found_non_skipping: condition,
        });
        Ok(())
    }

    fn handle_conditional_def(&mut self, is_ifdef: bool) -> Result<(), PPError> {
        let (_, sym) = self.expect_identifier()?;

        let condition = self.macros.contains_key(&sym) == is_ifdef;
        self.handle_if_directive(condition)?;
        self.expect_eod()
    }

    fn handle_ifdef(&mut self) -> Result<(), PPError> {
        self.handle_conditional_def(true)
    }

    fn handle_ifndef(&mut self) -> Result<(), PPError> {
        self.handle_conditional_def(false)
    }

    fn handle_elif_directive(&mut self, condition: bool, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            return self.emit_error_loc(PPErrorKind::ElifWithoutIf, location);
        }

        // Bolt ⚡: Check parent's skipping state to propagate it downward.
        let parent_skipping = if self.conditional_stack.len() > 1 {
            self.conditional_stack[self.conditional_stack.len() - 2].was_skipping
        } else {
            false
        };

        let current = self.conditional_stack.last_mut().unwrap();

        if current.found_else {
            return self.emit_error_loc(PPErrorKind::ElifAfterElse, location);
        }

        let should_process = !current.found_non_skipping && condition;
        if should_process {
            current.found_non_skipping = true;
        }
        current.was_skipping = parent_skipping || !should_process;

        Ok(())
    }

    fn handle_else(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.is_empty() {
            return self.emit_error_loc(PPErrorKind::ElseWithoutIf, location);
        }

        // Bolt ⚡: Check parent's skipping state to propagate it downward.
        let parent_skipping = if self.conditional_stack.len() > 1 {
            self.conditional_stack[self.conditional_stack.len() - 2].was_skipping
        } else {
            false
        };

        let current = self.conditional_stack.last_mut().unwrap();

        if current.found_else {
            return self.emit_error_loc(PPErrorKind::MultipleElse, location);
        }

        current.found_else = true;
        let should_process = !current.found_non_skipping;
        current.was_skipping = parent_skipping || !should_process;

        self.expect_eod()
    }

    fn handle_endif(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.pop().is_none() {
            return self.emit_error_loc(PPErrorKind::UnmatchedEndif, location);
        }
        self.expect_eod()
    }

    fn collect_tokens_until_eod(&mut self) -> Vec<PPToken> {
        // ⚡ Bolt: Use a small initial capacity to avoid reallocations for common macro bodies and directives.
        let mut tokens = Vec::with_capacity(32);
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
            tokens.push(token);
        }
        tokens
    }

    fn parse_line_directive_args(&self, tokens: &[PPToken]) -> Result<(u32, Option<String>), PPError> {
        let (first, rest) = tokens
            .split_first()
            .ok_or_else(|| self.error_loc(PPErrorKind::InvalidLineDirective, SourceLoc::builtin()))?;

        let PPTokenKind::Number(symbol) = first.kind else {
            return self.emit_error_loc(PPErrorKind::InvalidLineDirective, first.location);
        };

        let line_num = symbol
            .as_str()
            .parse::<u32>()
            .ok()
            .filter(|&n| n > 0)
            .ok_or_else(|| self.error_loc(PPErrorKind::InvalidLineDirective, first.location))?;

        let filename = match rest {
            [] => None,
            [t] => {
                let PPTokenKind::StringLiteral(s) = t.kind else {
                    return self.emit_error_loc(PPErrorKind::InvalidLineDirective, t.location);
                };
                Some(self.extract_string_literal_content(s, t.location, PPErrorKind::InvalidLineDirective)?)
            }
            _ => return self.emit_error_loc(PPErrorKind::InvalidLineDirective, first.location),
        };

        Ok((line_num, filename))
    }

    fn handle_line(&mut self) -> Result<(), PPError> {
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line()
        } else {
            0
        };

        // Collect tokens until end of line
        let mut tokens = self.collect_tokens_until_eod();

        if tokens.is_empty() {
            let loc = self.get_current_location();
            return self.emit_error_loc(PPErrorKind::InvalidLineDirective, loc);
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

    fn handle_pragma(&mut self) -> Result<(), PPError> {
        let (token, symbol) = self.expect_identifier()?;

        let pragma_name = symbol.as_str();
        match pragma_name {
            "once" => {
                if let Some(lexer) = self.lexer_stack.last() {
                    self.once_included.insert(lexer.source_id);
                }
            }
            "push_macro" => self.handle_push_macro()?,
            "pop_macro" => self.handle_pop_macro()?,
            "message" => self.handle_pragma_message()?,
            "warning" => self.handle_pragma_warning(DiagnosticLevel::Warning)?,
            "error" => self.handle_pragma_error(DiagnosticLevel::Error)?,
            "pack" => return self.handle_pragma_pack(),
            _ => {
                return self.emit_error_loc(PPErrorKind::UnknownPragma(pragma_name.to_string()), token.location);
            }
        }

        self.collect_tokens_until_eod();
        Ok(())
    }

    fn parse_pragma_macro_name(&mut self) -> Result<StringId, PPError> {
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (symbol, token_loc) = self.expect_string_literal()?;

        let name = self.extract_string_literal_content(symbol, token_loc, PPErrorKind::InvalidDirective)?;

        self.expect_kind(PPTokenKind::RightParen)?;

        Ok(StringId::new(name))
    }

    fn handle_push_macro(&mut self) -> Result<(), PPError> {
        let name = self.parse_pragma_macro_name()?;

        let info = self.macros.get(&name).cloned();

        self.macro_stack.entry(name).or_default().push(info);

        Ok(())
    }

    fn handle_pop_macro(&mut self) -> Result<(), PPError> {
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

    fn parse_pragma_message_content(&mut self) -> Result<String, PPError> {
        let mut tokens = self.collect_balanced_tokens(PPTokenKind::LeftParen, PPTokenKind::RightParen)?;
        self.expand_tokens(&mut tokens, false)?;

        tokens.into_iter().try_fold(String::new(), |mut acc, t| {
            let PPTokenKind::StringLiteral(symbol) = t.kind else {
                return self.emit_error_loc(PPErrorKind::InvalidDirective, t.location);
            };
            acc.push_str(&self.destringize(symbol.as_str()));
            Ok(acc)
        })
    }

    fn handle_pragma_diagnostic_message(&mut self, level: DiagnosticLevel) -> Result<(), PPError> {
        let message = self.parse_pragma_message_content()?;
        let loc = self.get_current_location();
        let diag = Diagnostic {
            level,
            message: message.clone(),
            span: SourceSpan::new(loc, loc),
            ..Default::default()
        };
        self.diag.report_diagnostic(diag);

        if level == DiagnosticLevel::Error {
            self.emit_error_loc(PPErrorKind::PragmaError(message), loc)
        } else {
            Ok(())
        }
    }

    fn handle_pragma_message(&mut self) -> Result<(), PPError> {
        self.handle_pragma_diagnostic_message(DiagnosticLevel::Note)
    }

    fn handle_pragma_warning(&mut self, level: DiagnosticLevel) -> Result<(), PPError> {
        self.handle_pragma_diagnostic_message(level)
    }

    fn handle_pragma_error(&mut self, level: DiagnosticLevel) -> Result<(), PPError> {
        self.handle_pragma_diagnostic_message(level)
    }

    fn handle_diagnostic_directive(&mut self, is_error: bool) -> Result<(), PPError> {
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
            self.report_warning(directive_location, formatted_message);
        }

        if is_error {
            self.emit_error_loc(PPErrorKind::ErrorDirective(message), directive_location)
        } else {
            Ok(())
        }
    }

    fn handle_pragma_pack(&mut self) -> Result<(), PPError> {
        let mut tokens = Vec::new();
        while let Some(token) = self.lex_token() {
            if token.kind == PPTokenKind::Eod {
                break;
            }
            tokens.push(token);
        }

        if tokens.is_empty() {
            self.pending_tokens.push(PPToken::new(
                PPTokenKind::PragmaPack(PragmaPackKind::Set(None)),
                PPTokenFlags::empty(),
                self.get_current_location(),
                0,
            ));
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

        let kind = if has_paren && it.peek().map(|t| t.kind) == Some(PPTokenKind::RightParen) {
            PragmaPackKind::Set(None)
        } else if let Some(t) = it.next() {
            match t.kind {
                PPTokenKind::Identifier(sym) => {
                    let name = sym.as_str();
                    match name {
                        "push" => {
                            if it.peek().map(|t| t.kind) == Some(PPTokenKind::Comma) {
                                it.next(); // consume ','
                                let val = self.parse_pack_value_from_iter(&mut it, t.location)?;
                                PragmaPackKind::PushSet(val)
                            } else {
                                PragmaPackKind::Push
                            }
                        }
                        "pop" => PragmaPackKind::Pop,
                        _ => {
                            let val = name.parse::<u8>().ok();
                            if let Some(v) = val {
                                if [1, 2, 4, 8, 16].contains(&v) {
                                    PragmaPackKind::Set(Some(v))
                                } else {
                                    return self.emit_error_loc(
                                        PPErrorKind::UnknownPragma(format!("invalid pack value: {}", v)),
                                        t.location,
                                    );
                                }
                            } else {
                                return self
                                    .emit_error_loc(PPErrorKind::UnknownPragma(format!("pack({})", name)), t.location);
                            }
                        }
                    }
                }
                PPTokenKind::Number(_) => {
                    let val = self.parse_pack_value_from_token(t)?;
                    PragmaPackKind::Set(Some(val))
                }
                _ => return self.emit_error_loc(PPErrorKind::UnknownPragma("pack".to_string()), t.location),
            }
        } else {
            PragmaPackKind::Set(None)
        };

        if has_paren {
            if let Some(t) = it.next() {
                if t.kind != PPTokenKind::RightParen {
                    return self.emit_error_loc(PPErrorKind::UnknownPragma("pack".to_string()), t.location);
                }
            } else {
                return self.emit_error_loc(
                    PPErrorKind::UnknownPragma("pack".to_string()),
                    self.get_current_location(),
                );
            }
        }

        if let Some(t) = it.next() {
            return self.emit_error_loc(PPErrorKind::ExpectedEod, t.location);
        }

        self.pending_tokens.push(PPToken::new(
            PPTokenKind::PragmaPack(kind),
            PPTokenFlags::empty(),
            self.get_current_location(),
            0,
        ));

        Ok(())
    }

    fn parse_pack_value_from_token(&self, t: &PPToken) -> Result<u8, PPError> {
        let PPTokenKind::Number(sym) = t.kind else {
            return self.emit_error_loc(PPErrorKind::UnknownPragma("pack".to_string()), t.location);
        };
        let val = sym.as_str().parse::<u8>().ok().ok_or_else(|| {
            self.error_loc(
                PPErrorKind::UnknownPragma(format!("invalid pack value: {}", sym.as_str())),
                t.location,
            )
        })?;
        if [1, 2, 4, 8, 16].contains(&val) {
            Ok(val)
        } else {
            self.emit_error_loc(
                PPErrorKind::UnknownPragma(format!("invalid pack value: {}", val)),
                t.location,
            )
        }
    }

    fn parse_pack_value_from_iter(
        &self,
        it: &mut std::iter::Peekable<std::slice::Iter<'_, PPToken>>,
        loc: SourceLoc,
    ) -> Result<u8, PPError> {
        if let Some(t) = it.next() {
            self.parse_pack_value_from_token(t)
        } else {
            self.emit_error_loc(PPErrorKind::UnknownPragma("pack".to_string()), loc)
        }
    }

    fn handle_error(&mut self) -> Result<(), PPError> {
        self.handle_diagnostic_directive(true)
    }

    fn handle_warning(&mut self) -> Result<(), PPError> {
        self.handle_diagnostic_directive(false)
    }

    fn read_directive_message(&mut self) -> String {
        let tokens = self.collect_tokens_until_eod();
        self.tokens_to_string(&tokens)
    }
}
