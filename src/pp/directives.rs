use crate::ast::StringId;
use crate::diagnostic::{Diagnostic, DiagnosticLevel};
use crate::pp::error::{PPError, PPErrorKind};
use crate::pp::pp_lexer::PPLexer;
use crate::pp::preprocessor::Preprocessor;
use crate::pp::types::{IncludeStackInfo, MacroFlags, MacroInfo, PPConditionalInfo};
use crate::pp::{DirectiveKind, PPToken, PPTokenFlags, PPTokenKind, PragmaPackKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceSpan};
use std::sync::Arc;

impl<'src> Preprocessor<'src> {
    /// Handle preprocessor directives
    pub(super) fn handle_directive(&mut self) -> Result<(), PPError> {
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
                None => self.emit_error(PPErrorKind::InvalidDirective, token.location),
            },
            PPTokenKind::Eod => Ok(()),
            _ => self.emit_error(PPErrorKind::InvalidDirective, token.location),
        }
    }

    fn handle_conditional_directive(&mut self, kind: DirectiveKind, location: SourceLoc) -> Result<(), PPError> {
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
                            let cond = self.macros.contains_key(&sym) == is_ifdef;
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
            DirectiveKind::Embed => self.handle_embed(),
            _ => unreachable!("ICE: Conditional directives handled separately"),
        }
    }

    /// Handle _Pragma("...") operator
    pub(super) fn handle_pragma_operator(&mut self) -> Result<(), PPError> {
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
    fn parse_define_args(&mut self, name: StringId) -> Result<(MacroFlags, Vec<StringId>, Option<StringId>), PPError> {
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
                let err = self.error(PPErrorKind::MacroRedefined(name), name_token.location);
                self.report_pp_error(err);
            }
        }
        true
    }

    fn handle_define(&mut self) -> Result<(), PPError> {
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
        };

        // Bolt ⚡: Pre-detect __VA_OPT__ in variadic macros to speed up expansion.
        if macro_info.variadic_arg.is_some() {
            for t in macro_info.tokens.iter() {
                if let PPTokenKind::Identifier(sym) = t.kind
                    && sym == self.keywords.va_opt
                {
                    macro_info.flags |= MacroFlags::HAS_VA_OPT;
                    break;
                }
            }
        }

        if self.check_macro_redefinition(name, &name_token, &macro_info) {
            self.macros.insert(name, macro_info);
        }
        Ok(())
    }

    fn handle_undef(&mut self) -> Result<(), PPError> {
        let (token, name) = self.expect_identifier()?;

        if let Some(existing) = self.macros.get(&name)
            && existing.flags.contains(MacroFlags::BUILTIN)
        {
            self.report_warning(token.location, format!("Undefining built-in macro '{}'", name.as_str()));
            self.expect_eod()?;
            return Ok(());
        }

        // Remove the macro from the table if it exists
        self.macros.remove(&name);

        self.expect_eod()?;

        Ok(())
    }

    fn do_handle_include(&mut self, is_next: bool) -> Result<(), PPError> {
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
            return self.emit_error(PPErrorKind::IncludeDepthExceeded, first_token.location);
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
    ) -> Result<(String, bool), PPError> {
        if tokens.is_empty() {
            return self.emit_error(PPErrorKind::InvalidIncludePath, diag_loc);
        }

        let first = &tokens[0];
        match first.kind {
            PPTokenKind::StringLiteral => {
                if !allow_extra && tokens.len() > 1 {
                    return self.emit_error(PPErrorKind::ExpectedEod, tokens[1].location);
                }
                let text = self.get_token_text(first);
                let path = self
                    .extract_literal_content(&text, first.location, PPErrorKind::InvalidIncludePath)?
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
                let idx = greater_idx.ok_or_else(|| self.error(PPErrorKind::InvalidIncludePath, diag_loc))?;
                if !allow_extra && idx + 1 < tokens.len() {
                    return self.emit_error(PPErrorKind::ExpectedEod, tokens[idx + 1].location);
                }
                let path_parts = &tokens[1..idx];
                Ok((self.tokens_to_string(path_parts), true))
            }
            _ => self.emit_error(PPErrorKind::InvalidIncludePath, diag_loc),
        }
    }

    fn handle_include(&mut self) -> Result<(), PPError> {
        self.do_handle_include(false)
    }

    fn handle_include_next(&mut self) -> Result<(), PPError> {
        self.do_handle_include(true)
    }

    fn handle_embed(&mut self) -> Result<(), PPError> {
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
                .ok_or_else(|| self.error(PPErrorKind::InvalidIncludePath, first_token.location))?
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
                                .map_err(|_| self.error(PPErrorKind::InvalidDirective, tokens[i].location))?,
                        );
                        i += 1;
                    } else {
                        let loc = if i < tokens.len() {
                            tokens[i].location
                        } else {
                            t.location
                        };
                        return self.emit_error(PPErrorKind::InvalidDirective, loc);
                    }

                    if i < tokens.len() && tokens[i].kind == PPTokenKind::RightParen {
                        i += 1;
                    } else {
                        return self.emit_error(PPErrorKind::InvalidDirective, t.location);
                    }
                } else {
                    return self.emit_error(PPErrorKind::InvalidDirective, t.location);
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

        // ⚡ Bolt: Fast string building for #embed bytes using a pre-computed decimal table.
        // This avoids thousands of tiny allocations from byte.to_string() in large files.
        const DIGITS: [&str; 256] = [
            "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16", "17", "18",
            "19", "20", "21", "22", "23", "24", "25", "26", "27", "28", "29", "30", "31", "32", "33", "34", "35", "36",
            "37", "38", "39", "40", "41", "42", "43", "44", "45", "46", "47", "48", "49", "50", "51", "52", "53", "54",
            "55", "56", "57", "58", "59", "60", "61", "62", "63", "64", "65", "66", "67", "68", "69", "70", "71", "72",
            "73", "74", "75", "76", "77", "78", "79", "80", "81", "82", "83", "84", "85", "86", "87", "88", "89", "90",
            "91", "92", "93", "94", "95", "96", "97", "98", "99", "100", "101", "102", "103", "104", "105", "106",
            "107", "108", "109", "110", "111", "112", "113", "114", "115", "116", "117", "118", "119", "120", "121",
            "122", "123", "124", "125", "126", "127", "128", "129", "130", "131", "132", "133", "134", "135", "136",
            "137", "138", "139", "140", "141", "142", "143", "144", "145", "146", "147", "148", "149", "150", "151",
            "152", "153", "154", "155", "156", "157", "158", "159", "160", "161", "162", "163", "164", "165", "166",
            "167", "168", "169", "170", "171", "172", "173", "174", "175", "176", "177", "178", "179", "180", "181",
            "182", "183", "184", "185", "186", "187", "188", "189", "190", "191", "192", "193", "194", "195", "196",
            "197", "198", "199", "200", "201", "202", "203", "204", "205", "206", "207", "208", "209", "210", "211",
            "212", "213", "214", "215", "216", "217", "218", "219", "220", "221", "222", "223", "224", "225", "226",
            "227", "228", "229", "230", "231", "232", "233", "234", "235", "236", "237", "238", "239", "240", "241",
            "242", "243", "244", "245", "246", "247", "248", "249", "250", "251", "252", "253", "254", "255",
        ];

        let mut embed_text = String::with_capacity(bytes_to_embed * 4);
        for (idx, &byte) in buffer[..bytes_to_embed].iter().enumerate() {
            if idx > 0 {
                embed_text.push_str(", ");
            }
            embed_text.push_str(DIGITS[byte as usize]);
        }

        let (embed_tokens, _) = self.tokenize_synthetic(embed_text, "<embed>", FileKind::MacroExpansion);
        self.pending_tokens.extend(embed_tokens.into_iter().rev());

        Ok(())
    }

    fn resolve_include_path(&mut self, path: &str, is_angled: bool, loc: SourceLoc) -> Result<SourceId, PPError> {
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
            self.emit_error(PPErrorKind::FileNotFound { path: path.to_string() }, loc)
        }
    }

    fn resolve_next_include_path(&mut self, path: &str, is_angled: bool, loc: SourceLoc) -> Result<SourceId, PPError> {
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

        self.emit_error(PPErrorKind::FileNotFound { path: path.to_string() }, loc)
    }

    fn handle_if(&mut self, condition: bool) -> Result<(), PPError> {
        // Bolt ⚡: Ensure the skipping state is propagated downward.
        let was_skipping = self.is_currently_skipping() || !condition;
        self.conditional_stack.push(PPConditionalInfo {
            was_skipping,
            found_else: false,
            found_non_skipping: condition,
        });
        Ok(())
    }

    fn handle_ifdef(&mut self) -> Result<(), PPError> {
        self.handle_conditional_def(true)
    }

    fn handle_ifndef(&mut self) -> Result<(), PPError> {
        self.handle_conditional_def(false)
    }

    fn handle_conditional_def(&mut self, is_ifdef: bool) -> Result<(), PPError> {
        let (_, sym) = self.expect_identifier()?;

        let condition = self.macros.contains_key(&sym) == is_ifdef;
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

    fn handle_elif_or_else(&mut self, condition: Option<bool>, location: SourceLoc) -> Result<(), PPError> {
        let is_elif = condition.is_some();
        let empty_error = if is_elif {
            PPErrorKind::ElifWithoutIf
        } else {
            PPErrorKind::ElseWithoutIf
        };

        if self.conditional_stack.is_empty() {
            return self.emit_error(empty_error, location);
        }

        let parent_skipping = self.get_parent_skipping();
        let current = self.conditional_stack.last_mut().unwrap();

        let dup_error = if is_elif {
            PPErrorKind::ElifAfterElse
        } else {
            PPErrorKind::MultipleElse
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

    fn handle_elif(&mut self, condition: bool, location: SourceLoc) -> Result<(), PPError> {
        self.handle_elif_or_else(Some(condition), location)
    }

    fn handle_else(&mut self, location: SourceLoc) -> Result<(), PPError> {
        self.handle_elif_or_else(None, location)?;
        self.expect_eod()
    }

    fn handle_endif(&mut self, location: SourceLoc) -> Result<(), PPError> {
        if self.conditional_stack.pop().is_none() {
            return self.emit_error(PPErrorKind::UnmatchedEndif, location);
        }
        self.expect_eod()
    }

    fn parse_line_directive_args(&self, tokens: &[PPToken]) -> Result<(u32, Option<String>), PPError> {
        let (first, rest) = tokens
            .split_first()
            .ok_or_else(|| self.error(PPErrorKind::InvalidLineDirective, SourceLoc::builtin()))?;

        let PPTokenKind::Number = first.kind else {
            return self.emit_error(PPErrorKind::InvalidLineDirective, first.location);
        };

        let symbol_text = self.get_token_text(first);
        let line_num = symbol_text
            .parse::<u32>()
            .ok()
            .filter(|&n| n > 0)
            .ok_or_else(|| self.error(PPErrorKind::InvalidLineDirective, first.location))?;

        let filename = match rest {
            [] => None,
            [t] => {
                let PPTokenKind::StringLiteral = t.kind else {
                    return self.emit_error(PPErrorKind::InvalidLineDirective, t.location);
                };
                let text = self.get_token_text(t);
                Some(
                    self.extract_literal_content(&text, t.location, PPErrorKind::InvalidLineDirective)?
                        .to_string(),
                )
            }
            _ => return self.emit_error(PPErrorKind::InvalidLineDirective, first.location),
        };

        Ok((line_num, filename))
    }

    fn handle_line(&mut self) -> Result<(), PPError> {
        let start_line = if let Some(lexer) = self.lexer_stack.last() {
            lexer.get_current_line(self.sm)
        } else {
            0
        };

        // Collect tokens until end of line
        let mut tokens = self.collect_tokens_until_eod();

        if tokens.is_empty() {
            let loc = self.get_current_location();
            return self.emit_error(PPErrorKind::InvalidLineDirective, loc);
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
            return self.emit_error(PPErrorKind::UnknownPragma(symbol), token.location);
        }

        self.collect_tokens_until_eod();
        Ok(())
    }

    fn parse_pragma_macro_name(&mut self) -> Result<StringId, PPError> {
        self.expect_kind(PPTokenKind::LeftParen)?;
        let (text, token_loc) = self.expect_string_literal()?;

        let name = self.extract_literal_content(&text, token_loc, PPErrorKind::InvalidDirective)?;
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
            let PPTokenKind::StringLiteral = t.kind else {
                return self.emit_error(PPErrorKind::InvalidDirective, t.location);
            };
            acc.push_str(&self.destringize(&self.get_token_text(&t)));
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
            self.emit_error(PPErrorKind::PragmaError(message), loc)
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
            self.emit_error(PPErrorKind::ErrorDirective(message), directive_location)
        } else {
            Ok(())
        }
    }

    fn handle_pragma_pack(&mut self) -> Result<(), PPError> {
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
                            .ok_or_else(|| self.error(PPErrorKind::UnknownPragma(self.keywords.pack), t.location))?;
                        PragmaPackKind::PushSet(self.parse_pragma_pack_value(val_token)?)
                    } else {
                        PragmaPackKind::Push
                    }
                }
                PPTokenKind::Identifier(sym) if sym == self.keywords.pop => PragmaPackKind::Pop,
                PPTokenKind::Identifier(_) | PPTokenKind::Number => {
                    PragmaPackKind::Set(Some(self.parse_pragma_pack_value(t)?))
                }
                _ => return self.emit_error(PPErrorKind::UnknownPragma(self.keywords.pack), t.location),
            }
        } else {
            PragmaPackKind::Set(None)
        };

        if has_paren {
            if let Some(t) = it.next() {
                if t.kind != PPTokenKind::RightParen {
                    return self.emit_error(PPErrorKind::UnknownPragma(self.keywords.pack), t.location);
                }
            } else {
                return self.emit_error(PPErrorKind::UnknownPragma(self.keywords.pack), loc);
            }
        }

        if let Some(t) = it.next() {
            return self.emit_error(PPErrorKind::ExpectedEod, t.location);
        }

        self.pending_tokens.push(PPToken::new(
            PPTokenKind::PragmaPack(kind),
            PPTokenFlags::empty(),
            loc,
            0,
        ));

        Ok(())
    }

    fn parse_pragma_pack_value(&self, t: &PPToken) -> Result<u8, PPError> {
        let text = match t.kind {
            PPTokenKind::Number => self.get_token_text(t),
            PPTokenKind::Identifier(sym) => std::borrow::Cow::Borrowed(sym.as_str()),
            _ => return self.emit_error(PPErrorKind::UnknownPragma(self.keywords.pack), t.location),
        };

        match text.parse::<u8>() {
            Ok(v) if matches!(v, 1 | 2 | 4 | 8 | 16) => Ok(v),
            _ => {
                let sym = StringId::new(&text);
                self.emit_error(PPErrorKind::InvalidPragmaPackValue(sym), t.location)
            }
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
