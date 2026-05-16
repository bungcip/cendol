//! Preprocessor Dumper module
//!
//! This module handles dumping preprocessed tokens back to source text,
//! with support for line markers and whitespace reconstruction.

use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{SourceLoc, SourceManager};
use std::io::Write;

/// Dumper for preprocessed output
pub struct PPDumper<'a> {
    tokens: &'a [PPToken],
    source_manager: &'a SourceManager,
    suppress_line_markers: bool,
}

struct DumperState<'a> {
    file_id: crate::source_manager::SourceId,
    buffer: &'a [u8],
    last_pos: u32,
    at_line_start: bool,
    last_was_open_paren: bool,
}

impl<'a> PPDumper<'a> {
    /// Create a new preprocessor dumper
    pub(crate) fn new(tokens: &'a [PPToken], source_manager: &'a SourceManager, suppress_line_markers: bool) -> Self {
        Self {
            tokens,
            source_manager,
            suppress_line_markers,
        }
    }

    /// Dump preprocessed output to the given writer
    pub(crate) fn dump(&self, writer: &mut impl Write) -> std::io::Result<()> {
        if self.tokens.is_empty() {
            return Ok(());
        }

        let mut state = self.init_state();

        for token in self.tokens.iter() {
            if token.kind == PPTokenKind::Eof {
                break;
            }

            let loc = self.resolve_top_level_loc(token.location);
            let is_macro = token.flags.contains(PPTokenFlags::MACRO_EXPANDED);
            let (line, _) = self.source_manager.get_line_column(loc).unwrap_or((1, 1));

            if loc.source_id() != state.file_id {
                self.handle_file_transition(writer, &mut state, loc, line)?;
            }

            let mut token_start = loc.offset();
            if is_macro && loc.source_id() == state.file_id && token_start < state.last_pos {
                token_start = state.last_pos;
            }

            let gap_printed_space = self.handle_gap(writer, &mut state, token, token_start)?;
            self.handle_leading_space(writer, &state, token, token_start, is_macro, gap_printed_space)?;

            let text = self.get_token_text(token, state.buffer, is_macro);
            write!(writer, "{}", text)?;

            state.at_line_start = false;
            state.last_was_open_paren = text.ends_with('(');
            state.last_pos = if is_macro {
                token_start
            } else {
                token_start + token.length as u32
            };
        }

        writeln!(writer)?;
        Ok(())
    }

    fn init_state(&self) -> DumperState<'_> {
        let first_loc = self.resolve_top_level_loc(self.tokens[0].location);
        let file_id = first_loc.source_id();
        DumperState {
            file_id,
            buffer: self.source_manager.get_buffer_safe(file_id).unwrap_or(&[]),
            last_pos: 0,
            at_line_start: true,
            last_was_open_paren: false,
        }
    }

    fn handle_file_transition(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        loc: SourceLoc,
        line: u32,
    ) -> std::io::Result<()> {
        if !self.suppress_line_markers
            && let Some(info) = self.source_manager.get_file_info(loc.source_id())
        {
            let name = info.path.file_name().and_then(|n| n.to_str()).unwrap_or("<unknown>");
            if !state.at_line_start {
                writeln!(writer)?;
            }
            writeln!(writer, "# {} \"{}\" 1", line, name)?;
            state.at_line_start = true;
        }

        state.file_id = loc.source_id();
        state.buffer = self.source_manager.get_buffer_safe(state.file_id).unwrap_or(&[]);
        state.last_pos = 0;
        Ok(())
    }

    fn handle_gap(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        token: &PPToken,
        token_start: u32,
    ) -> std::io::Result<bool> {
        if token_start <= state.last_pos {
            return Ok(false);
        }

        let slice = &state.buffer[state.last_pos as usize..token_start as usize];
        let Ok(text) = std::str::from_utf8(slice) else {
            return Ok(false);
        };

        let is_all_ws = text.chars().all(|c| c.is_whitespace());
        let has_nl = text.contains('\n');

        if is_all_ws {
            if !self.suppress_line_markers {
                write!(writer, "{}", text)?;
                if has_nl {
                    state.at_line_start = text.ends_with('\n');
                }
                Ok(!text.is_empty() && !text.ends_with('\n'))
            } else if has_nl {
                if !state.at_line_start {
                    writeln!(writer)?;
                    state.at_line_start = true;
                }
                Ok(false)
            } else if !text.is_empty() {
                write!(writer, "{}", text)?;
                state.at_line_start = false;
                Ok(true)
            } else {
                Ok(false)
            }
        } else {
            self.handle_complex_gap(writer, state, token, text, has_nl)
        }
    }

    fn handle_complex_gap(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        token: &PPToken,
        text: &str,
        has_nl: bool,
    ) -> std::io::Result<bool> {
        let mut printed_space = false;

        let starts_with_ws = text.chars().next().is_some_and(|c| c.is_whitespace() && c != '\n');
        let ends_with_ws = text.chars().last().is_some_and(|c| c.is_whitespace() && c != '\n');

        if (starts_with_ws || ends_with_ws) && !state.at_line_start && !has_nl {
            let next_text = token.get_text_with_sm(self.source_manager);
            let is_sep = matches!(next_text.chars().next(), Some('(' | ')' | ';' | ',' | ']'));
            if (!is_sep && !text.trim_end().ends_with('(')) || ends_with_ws {
                write!(writer, " ")?;
                state.at_line_start = false;
                printed_space = true;
            }
        }

        if has_nl {
            if !self.suppress_line_markers {
                for _ in 0..text.chars().filter(|&c| c == '\n').count() {
                    writeln!(writer)?;
                }
                state.at_line_start = true;
            } else if !state.at_line_start && !printed_space {
                if self.is_macro_internal_newline(text) {
                    let next_text = token.get_text_with_sm(self.source_manager);
                    if !matches!(next_text.chars().next(), Some(')' | ';' | ',' | ']')) {
                        write!(writer, " ")?;
                    }
                    state.at_line_start = false;
                    printed_space = true;
                } else {
                    writeln!(writer)?;
                    state.at_line_start = true;
                }
            }
        }

        Ok(printed_space)
    }

    fn is_macro_internal_newline(&self, text: &str) -> bool {
        let mut depth = 0;
        for c in text.chars() {
            if c == '(' {
                depth += 1;
            } else if c == ')' {
                depth -= 1;
            } else if c == '\n' && depth > 0 {
                return true;
            }
        }
        false
    }

    fn handle_leading_space(
        &self,
        writer: &mut impl Write,
        state: &DumperState<'a>,
        token: &PPToken,
        token_start: u32,
        is_macro: bool,
        gap_printed_space: bool,
    ) -> std::io::Result<()> {
        if is_macro && token.flags.contains(PPTokenFlags::LEADING_SPACE) && !state.at_line_start && !gap_printed_space {
            let ended_with_paren = if token_start > state.last_pos {
                let slice = &state.buffer[state.last_pos as usize..token_start as usize];
                std::str::from_utf8(slice).is_ok_and(|s| s.trim_end().ends_with('('))
            } else {
                state.last_was_open_paren
            };

            if !ended_with_paren {
                write!(writer, " ")?;
            }
        }
        Ok(())
    }

    fn get_token_text<'b>(&'b self, token: &PPToken, buffer: &'b [u8], is_macro: bool) -> std::borrow::Cow<'b, str> {
        if is_macro {
            token.get_text_with_sm(self.source_manager)
        } else {
            let slice = token.get_raw_slice(buffer);
            std::str::from_utf8(slice)
                .map(std::borrow::Cow::Borrowed)
                .unwrap_or(std::borrow::Cow::Borrowed(""))
        }
    }

    /// Resolve a location back to its top-level source file (Real).
    /// This follows the include_loc chain up to the physical source file.
    fn resolve_top_level_loc(&self, loc: SourceLoc) -> SourceLoc {
        let mut current_loc = loc;
        loop {
            if let Some(file_info) = self.source_manager.get_file_info(current_loc.source_id())
                && let Some(include_loc) = file_info.include_loc
            {
                current_loc = include_loc;
                continue;
            }
            return current_loc;
        }
    }
}
