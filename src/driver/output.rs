//! Output formatting and file writing module
//!
//! This module handles various output formats including preprocessed source,
//! parser AST dumps, and HTML AST dumps.

use crate::pp::PPToken;
use crate::source_manager::SourceManager;

use super::compiler::DriverError;

/// Handler for various output formats
pub(crate) struct OutputHandler;

impl Default for OutputHandler {
    fn default() -> Self {
        Self::new()
    }
}

impl OutputHandler {
    /// Create a new output handler
    pub(crate) fn new() -> Self {
        OutputHandler
    }

    /// Dump preprocessed output to the given writer
    pub(crate) fn dump_preprocessed_output(
        &self,
        writer: &mut impl std::io::Write,
        pp_tokens: &[PPToken],
        suppress_line_markers: bool,
        source_manager: &SourceManager,
    ) -> Result<(), DriverError> {
        if pp_tokens.is_empty() {
            return Ok(());
        }

        // Get the source buffer for the first token
        let first_token = &pp_tokens[0];

        // Initial heuristic: try to find the first non-macro-expanded token
        // to establish the "current file" context. This prevents line markers
        // generally being emitted for the file itself if it starts with a macro.
        let mut current_file_id = first_token.location.source_id();
        for token in pp_tokens {
            if !token.flags.contains(crate::pp::PPTokenFlags::MACRO_EXPANDED) {
                current_file_id = token.location.source_id();
                break;
            }
        }
        let mut current_buffer = source_manager.get_buffer(current_file_id);
        let mut last_pos = 0u32;
        let mut last_was_macro_expanded = false;

        for token in pp_tokens {
            if token.kind == crate::pp::PPTokenKind::Eof {
                break;
            }

            // Handle macro-expanded tokens (Level A: use canonical spelling)
            if token.flags.contains(crate::pp::PPTokenFlags::MACRO_EXPANDED) {
                // Heuristic: if we are entering a macro expansion (previous was not macro),
                // and there was whitespace at the current position in the source, print a space.
                // This preserves separation like "return FOO" -> "return 123".
                if !last_was_macro_expanded {
                    // Check if char at last_pos is whitespace
                    if let Some(&byte) = current_buffer.get(last_pos as usize)
                        && (byte as char).is_whitespace()
                    {
                        write!(writer, " ").map_err(|e| DriverError::IoError(e.to_string()))?;
                    }
                } else {
                    // Add space between consecutive macro-expanded tokens (linearization)
                    write!(writer, " ").map_err(|e| DriverError::IoError(e.to_string()))?;
                }

                // For macro-expanded tokens, just print the canonical spelling
                // No whitespace reconstruction for Level A - these tokens don't have
                // meaningful source locations for whitespace calculation
                write!(writer, "{}", token.get_text()).map_err(|e| DriverError::IoError(e.to_string()))?;
                last_was_macro_expanded = true;
                // Don't update last_pos for macro-expanded tokens
                continue;
            }

            // Check for file transitions and emit line markers
            if token.location.source_id() != current_file_id {
                // Emit line marker for file transition (unless suppressed)
                if !suppress_line_markers
                    && let Some(file_info) = source_manager.get_file_info(token.location.source_id())
                {
                    let line = source_manager
                        .get_line_column(token.location)
                        .map(|(l, _)| l)
                        .unwrap_or(1);
                    let filename = file_info
                        .path
                        .file_name()
                        .and_then(|n| n.to_str())
                        .unwrap_or("<unknown>");

                    // Ensure we start on a new line
                    writeln!(writer).map_err(|e| DriverError::IoError(e.to_string()))?;
                    writeln!(writer, "# {} \"{}\" 1", line, filename)
                        .map_err(|e| DriverError::IoError(e.to_string()))?;
                }

                current_file_id = token.location.source_id();
                current_buffer = source_manager.get_buffer(current_file_id);
                last_pos = token.location.offset();
            }

            let token_start = token.location.offset();
            let token_end = token_start + token.length as u32;

            // Print all bytes between last_pos and token_start (whitespace, comments)
            if token_start > last_pos {
                let slice = &current_buffer[last_pos as usize..token_start as usize];
                // Convert to string, assuming UTF-8 (preprocessor should ensure this)
                if let Ok(text) = std::str::from_utf8(slice) {
                    // Only print slices that are all whitespace to avoid printing directive text
                    if text.chars().all(|c| c.is_whitespace()) {
                        write!(writer, "{}", text).map_err(|e| DriverError::IoError(e.to_string()))?;
                    }
                }
            }

            // Print the token's raw bytes from source
            let token_slice = token.get_raw_slice(current_buffer);
            if let Ok(text) = std::str::from_utf8(token_slice) {
                write!(writer, "{}", text).map_err(|e| DriverError::IoError(e.to_string()))?;
            }

            last_pos = token_end;
            last_was_macro_expanded = false;
        }

        writeln!(writer).map_err(|e| DriverError::IoError(e.to_string()))?;
        Ok(())
    }
}
