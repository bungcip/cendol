with open("src/semantic/analyzer.rs", "r") as f:
    content = f.read()

# Fix the unused code artifact in check_vla_jump_into_scope
old_str = """                if let Some(span) = source_span {
                    let kind = if is_switch {
                        SemanticErrorKind::NoteSwitchStartsHere
                    } else {
                        // For goto, we don't have a NoteGotoStartsHere, we point to label definition later
                        // Actually, if it's goto, source_span will be the label span, which is handled in goto verification
                        SemanticErrorKind::NoteSwitchStartsHere
                    };
                    // Manually report diagnostic for Note
                    let diag = crate::diagnostic::Diagnostic {
                        level: crate::diagnostic::DiagnosticLevel::Note,
                        message: kind.display(self.registry),
                        span,
                        ..Default::default()
                    };
                    self.diag.report_diagnostic(diag);
                }"""

new_str = """                if let Some(span) = source_span {
                    // Manually report diagnostic for Note
                    let diag = crate::diagnostic::Diagnostic {
                        level: crate::diagnostic::DiagnosticLevel::Note,
                        message: SemanticErrorKind::NoteSwitchStartsHere.display(self.registry),
                        span,
                        ..Default::default()
                    };
                    self.diag.report_diagnostic(diag);
                }"""

content = content.replace(old_str, new_str)
with open("src/semantic/analyzer.rs", "w") as f:
    f.write(content)
