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
    sm: &'a SourceManager,
    suppress_line_markers: bool,
}

struct DumperState<'a> {
    file_id: SourceId,
    file_name: Option<&'a str>,
    current_line: u32,
    buffer: &'a [u8],
    last_pos: u32,
    at_line_start: bool,
    last_was_open_paren: bool,
}

impl<'a> PPDumper<'a> {
    /// Create a new preprocessor dumper
    pub(crate) fn new(tokens: &'a [PPToken], sm: &'a SourceManager, suppress_line_markers: bool) -> Self {
        Self {
            tokens,
            sm,
            suppress_line_markers,
        }
    }

    /// Dump preprocessed output to the given writer
    pub(crate) fn dump(&self, writer: &mut impl Write) -> std::io::Result<()> {
        if self.tokens.is_empty() {
            return Ok(());
        }

        let mut state = DumperState {
            file_id: SourceId(std::num::NonZeroU32::MAX),
            file_name: None,
            current_line: 0,
            buffer: &[],
            last_pos: 0,
            at_line_start: true,
            last_was_open_paren: false,
        };

        if !self.suppress_line_markers {
            let loc = self.resolve_top_level_loc(self.tokens[0].location);
            if let Some((_, _, Some(file_name))) = self.sm.get_presumed_location(loc) {
                self.print_line_marker(writer, &mut state, 1, file_name)?;
                state.file_id = loc.source_id();
                state.buffer = self.sm.get_buffer_safe(state.file_id).unwrap_or(&[]);
            }
        }

        for token in self.tokens.iter() {
            if token.kind == PPTokenKind::Eof {
                break;
            }

            let loc = self.resolve_top_level_loc(token.location);
            let is_macro = token.flags.contains(PPTokenFlags::MACRO_EXPANDED);
            let (line, _, file_name) = self.sm.get_presumed_location(loc).unwrap_or((1, 1, None));
            let file_name_str = file_name.unwrap_or("<unknown>");

            if loc.source_id() != state.file_id || state.file_name != Some(file_name_str) {
                self.print_line_marker(writer, &mut state, line, file_name_str)?;
                state.file_id = loc.source_id();
                state.buffer = self.sm.get_buffer_safe(state.file_id).unwrap_or(&[]);
                state.last_pos = 0;
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

            if token.flags.contains(PPTokenFlags::LEADING_SPACE) && !gap_printed_space && !state.at_line_start {
                write!(writer, " ")?;
            }

            let text = if is_macro {
                token.get_text(self.sm)
            } else {
                let span = SourceSpan::from_loc_and_length(token.location, token.length as u32);
                std::borrow::Cow::Borrowed(self.sm.get_source_text(span))
            };
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

    fn print_line_marker(
        &self,
        writer: &mut impl Write,
        state: &mut DumperState<'a>,
        line: u32,
        name: &'a str,
    ) -> std::io::Result<()> {
        let old_line = state.current_line;
        state.current_line = line;
        let is_same_file = state.file_name == Some(name);
        state.file_name = Some(name);

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
        std::env::current_dir()
            .ok()
            .and_then(|cwd| std::path::Path::new(path).strip_prefix(cwd).ok())
            .map(|rel| rel.to_string_lossy().into_owned())
            .unwrap_or_else(|| path.to_string())
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
            if has_nl {
                if self.suppress_line_markers && !text.chars().all(|c| c.is_whitespace()) {
                    return Ok((0, true));
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
            let next_text = token.get_text(self.sm);
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
                newlines = text.chars().filter(|&c| c == '\n').count() as u32;
                for _ in 0..newlines {
                    writeln!(writer)?;
                }
            } else if !state.at_line_start {
                writeln!(writer)?;
                newlines = 1;
            }
            state.at_line_start = true;

            let last_nl = text.rfind('\n').unwrap();
            if !text[last_nl + 1..].is_empty() {
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

    /// Resolve a location back to its top-level source file (Real).
    /// This follows the include_loc chain up to the physical source file.
    fn resolve_top_level_loc(&self, loc: SourceLoc) -> SourceLoc {
        let mut current_loc = loc;
        while let Some(file_info) = self.sm.get_file_info(current_loc.source_id())
            && let Some(include_loc) = file_info.include_loc
        {
            current_loc = include_loc;
        }
        current_loc
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
