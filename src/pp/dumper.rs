//! Preprocessor Dumper module
//!
//! This module handles dumping preprocessed tokens back to source text,
//! with support for line markers and whitespace reconstruction.

use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{SourceId, SourceLoc, SourceManager, SourceSpan};
use std::io::Write;

/// Dumper for preprocessed output
pub struct PPDumper<'a> {
    tokens: &'a [PPToken],
    source_manager: &'a SourceManager,
    suppress_line_markers: bool,
}

struct DumperState<'a> {
    file_id: SourceId,
    file_name: Option<String>,
    current_line: u32,
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

        if !self.suppress_line_markers {
            let loc = self.resolve_top_level_loc(self.tokens[0].location);
            if let Some((_, _, Some(file_name))) = self.source_manager.get_presumed_location(loc) {
                self.print_line_marker(writer, &mut state, 1, file_name)?;
                state.file_id = loc.source_id();
                state.buffer = self.source_manager.get_buffer_safe(state.file_id).unwrap_or(&[]);
            }
        }

        for token in self.tokens.iter() {
            if token.kind == PPTokenKind::Eof {
                break;
            }

            let loc = self.resolve_top_level_loc(token.location);
            let is_macro = token.flags.contains(PPTokenFlags::MACRO_EXPANDED);
            let (line, _, file_name) = self.source_manager.get_presumed_location(loc).unwrap_or((1, 1, None));
            let file_name_str = file_name.unwrap_or("<unknown>");

            if loc.source_id() != state.file_id || state.file_name.as_deref() != Some(file_name_str) {
                self.handle_file_transition(writer, &mut state, loc, line, file_name_str)?;
            }

            let mut token_start = loc.offset();
            if is_macro && loc.source_id() == state.file_id && token_start < state.last_pos {
                token_start = state.last_pos;
            }

            let (gap_newlines, gap_printed_space) = self.handle_gap(writer, &mut state, token, token_start)?;
            state.current_line += gap_newlines;

            if line != state.current_line {
                self.print_line_marker(writer, &mut state, line, file_name_str)?;
            }

            self.handle_leading_space(writer, &state, token, gap_printed_space)?;

            let text = self.get_token_text(token, is_macro);
            write!(writer, "{}", text)?;

            state.at_line_start = false;
            state.last_was_open_paren = text.ends_with('(');
            state.last_pos = if is_macro {
                let macro_len = get_identifier_length(state.buffer, loc.offset() as usize);
                loc.offset() + macro_len
            } else {
                token_start + token.length as u32
            };
        }

        writeln!(writer)?;
        Ok(())
    }

    fn init_state(&self) -> DumperState<'_> {
        DumperState {
            file_id: SourceId(std::num::NonZeroU32::MAX),
            file_name: None,
            current_line: 0,
            buffer: &[],
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
        name: &str,
    ) -> std::io::Result<()> {
        self.print_line_marker(writer, state, line, name)?;
        state.file_id = loc.source_id();
        state.buffer = self.source_manager.get_buffer_safe(state.file_id).unwrap_or(&[]);
        state.last_pos = 0;
        Ok(())
    }

    fn print_line_marker(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        line: u32,
        name: &str,
    ) -> std::io::Result<()> {
        let old_line = state.current_line;
        state.current_line = line;
        let is_same_file = state.file_name.as_deref() == Some(name);
        state.file_name = Some(name.to_string());

        if !self.suppress_line_markers {
            if !state.at_line_start {
                writeln!(writer)?;
            }
            let display_name = self.get_display_name(name);
            writeln!(writer, "# {} \"{}\" 1", line, display_name)?;
            state.at_line_start = true;
        } else if old_line > 0 && line > old_line && is_same_file && !state.at_line_start {
            writeln!(writer)?;
            state.at_line_start = true;
        }
        Ok(())
    }

    fn get_display_name(&self, path: &str) -> String {
        if let Ok(cwd) = std::env::current_dir()
            && let Ok(rel) = std::path::Path::new(path).strip_prefix(cwd)
        {
            return rel.to_string_lossy().into_owned();
        }
        path.to_string()
    }

    fn handle_gap(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        token: &PPToken,
        token_start: u32,
    ) -> std::io::Result<(u32, bool)> {
        if token_start <= state.last_pos {
            return Ok((0, false));
        }

        let slice = &state.buffer[state.last_pos as usize..token_start as usize];
        let text = std::str::from_utf8(slice).unwrap_or("");
        let has_nl = text.contains('\n');
        let is_macro = token.flags.contains(PPTokenFlags::MACRO_EXPANDED);

        if is_macro {
            // ⚡ Bolt: Macro tokens should only trigger newlines from the gap if the gap is pure whitespace.
            // If the gap contains text (like a macro call), it should be collapsed in -P mode.
            if has_nl {
                if self.suppress_line_markers && !text.chars().all(|c| c.is_whitespace()) {
                    return Ok((0, true)); // Suppress newline and prevent follow-up space
                }
                let (newlines, space) = self.handle_whitespace_and_newlines(writer, state, text, true, true)?;
                return Ok((newlines, space));
            }
            if text.chars().all(|c| c.is_whitespace()) && !text.is_empty() {
                write!(writer, " ")?;
                state.at_line_start = false;
                return Ok((0, true));
            }
            return Ok((0, false));
        }

        if text.chars().all(|c| c.is_whitespace()) {
            self.handle_whitespace_and_newlines(writer, state, text, has_nl, false)
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
    ) -> std::io::Result<(u32, bool)> {
        let mut printed_space = false;

        let starts_with_ws = text.chars().next().is_some_and(|c| c.is_whitespace() && c != '\n');
        let ends_with_ws = text.chars().last().is_some_and(|c| c.is_whitespace() && c != '\n');

        if (starts_with_ws || ends_with_ws) && !state.at_line_start && !has_nl {
            let next_text = token.get_text_with_sm(self.source_manager);
            let is_sep = matches!(
                next_text.chars().next(),
                Some('(' | ')' | '{' | '}' | '[' | ']' | ';' | ',' | '.')
            );
            if (!is_sep && !text.trim_end().ends_with('(')) || ends_with_ws {
                write!(writer, " ")?;
                state.at_line_start = false;
                printed_space = true;
            }
        }

        let mut final_has_nl = has_nl;
        if self.suppress_line_markers && has_nl {
            final_has_nl = false;
            printed_space = true;
        }

        let (newlines, space) = self.handle_whitespace_and_newlines(writer, state, text, final_has_nl, false)?;
        Ok((newlines, printed_space || space))
    }

    fn handle_whitespace_and_newlines(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        text: &str,
        has_nl: bool,
        is_macro: bool,
    ) -> std::io::Result<(u32, bool)> {
        let mut newlines = 0;
        let mut printed_space = false;

        if has_nl {
            if !self.suppress_line_markers {
                for _ in 0..text.chars().filter(|&c| c == '\n').count() {
                    writeln!(writer)?;
                    newlines += 1;
                }
            } else if !state.at_line_start {
                writeln!(writer)?;
                newlines = 1;
            }
            state.at_line_start = true;
        }

        if let Some(last_nl) = text.rfind('\n')
            && has_nl
        {
            let indent = &text[last_nl + 1..];
            if !indent.is_empty() {
                write!(writer, " ")?;
                state.at_line_start = false;
                printed_space = true;
            }
        } else if !text.is_empty() && text.chars().all(|c| c.is_whitespace()) && !is_macro {
            write!(writer, " ")?;
            state.at_line_start = false;
            printed_space = true;
        }

        Ok((newlines, printed_space))
    }

    fn handle_leading_space(
        &self,
        writer: &mut impl Write,
        state: &DumperState<'a>,
        token: &PPToken,
        gap_printed_space: bool,
    ) -> std::io::Result<()> {
        if token.flags.contains(PPTokenFlags::LEADING_SPACE) && !gap_printed_space && !state.at_line_start {
            write!(writer, " ")?;
        }
        Ok(())
    }

    fn get_token_text<'b>(&'b self, token: &PPToken, is_macro: bool) -> std::borrow::Cow<'b, str> {
        if is_macro {
            token.get_text_with_sm(self.source_manager)
        } else {
            let span = SourceSpan::from_loc_and_length(token.location, token.length as u32);
            std::borrow::Cow::Borrowed(self.source_manager.get_source_text(span))
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

fn get_identifier_length(buffer: &[u8], offset: usize) -> u32 {
    let mut len = 0;
    while offset + len < buffer.len() {
        let c = buffer[offset + len];
        if c.is_ascii_alphanumeric() || c == b'_' {
            len += 1;
        } else {
            break;
        }
    }
    len as u32
}
