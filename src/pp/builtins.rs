use super::Preprocessor;
use crate::ast::StringId;
use crate::pp::pp_lexer::PPLexer;
use crate::pp::types::{MacroFlags, MacroInfo};
use crate::pp::{PPToken, PPTokenFlags, PPTokenKind};
use crate::source_manager::{FileKind, SourceId, SourceLoc, SourceManager};
use chrono::{DateTime, Datelike, Timelike, Utc};
use std::sync::Arc;
use target_lexicon::{Architecture, OperatingSystem};

impl<'src> Preprocessor<'src> {
    /// Initialize built-in macros
    pub(crate) fn initialize_builtin_macros(&mut self, current_time: Option<DateTime<Utc>>) {
        let now: DateTime<Utc> = current_time.unwrap_or_else(Utc::now);

        // __DATE__
        let date_str = format!("\"{:02} {:02} {}\"", now.format("%b"), now.day(), now.year());
        self.define_builtin_macro_string("__DATE__", &date_str);

        // __TIME__
        let time_str = format!("\"{:02}:{:02}:{:02}\"", now.hour(), now.minute(), now.second());
        self.define_builtin_macro_string("__TIME__", &time_str);

        // Other built-ins
        self.define_builtin_macro_one("__STDC__");

        // Split into smaller functions
        self.init_builtin_macros_limits();
        self.init_builtin_macros_target();
        self.init_builtin_macros_compiler_compat();
        self.init_builtin_macros_stdlib_types();
        self.init_builtin_macros_standards();
        self.init_builtin_macros_functions();
    }

    fn init_builtin_macros_limits(&mut self) {
        // Type limits
        self.define_builtin_macro_with_val("__CHAR_BIT__", "8");
        self.define_builtin_macro_with_val("__SCHAR_MAX__", "127");
        self.define_builtin_macro_with_val("__SHRT_MAX__", "32767");
        self.define_builtin_macro_with_val("__INT_MAX__", "2147483647");
        self.define_builtin_macro_with_val("__INT32_MAX__", "2147483647");
        self.define_builtin_macro_with_val("__UINT32_MAX__", "4294967295U");
        self.define_builtin_macro_with_val("__LONG_LONG_MAX__", "9223372036854775807LL");
        self.define_builtin_macro_with_val("__INT64_MAX__", "9223372036854775807LL");
        self.define_builtin_macro_with_val("__UINT64_MAX__", "18446744073709551615ULL");

        // Type sizes
        self.define_builtin_macro_with_val("__SIZEOF_SHORT__", "2");
        self.define_builtin_macro_with_val("__SIZEOF_INT__", "4");
        self.define_builtin_macro_with_val("__SIZEOF_LONG_LONG__", "8");
        self.define_builtin_macro_with_val("__SIZEOF_FLOAT__", "4");
        self.define_builtin_macro_with_val("__SIZEOF_DOUBLE__", "8");
        self.define_builtin_macro_with_val("__SIZEOF_LONG_DOUBLE__", "16");

        // Float limits
        self.define_builtin_macro_with_val("__FLT_MANT_DIG__", "24");
        self.define_builtin_macro_with_val("__FLT_DIG__", "6");
        self.define_builtin_macro_lexed("__FLT_MIN_EXP__", "(-125)");
        self.define_builtin_macro_with_val("__FLT_MAX_EXP__", "128");
        self.define_builtin_macro_lexed("__FLT_MIN_10_EXP__", "(-37)");
        self.define_builtin_macro_with_val("__FLT_MAX_10_EXP__", "38");
        self.define_builtin_macro_lexed("__FLT_MAX__", "3.40282346638528859811704183484516925e+38F");
        self.define_builtin_macro_lexed("__FLT_MIN__", "1.17549435082228750796873653722224568e-38F");
        self.define_builtin_macro_lexed("__FLT_EPSILON__", "1.19209289550781250000000000000000000e-7F");
        self.define_builtin_macro_with_val("__FLT_DECIMAL_DIG__", "9");

        self.define_builtin_macro_with_val("__DBL_MANT_DIG__", "53");
        self.define_builtin_macro_with_val("__DBL_DIG__", "15");
        self.define_builtin_macro_lexed("__DBL_MIN_EXP__", "(-1021)");
        self.define_builtin_macro_with_val("__DBL_MAX_EXP__", "1024");
        self.define_builtin_macro_lexed("__DBL_MIN_10_EXP__", "(-307)");
        self.define_builtin_macro_with_val("__DBL_MAX_10_EXP__", "308");
        self.define_builtin_macro_lexed("__DBL_MAX__", "((double)1.79769313486231570814527423731704357e+308L)");
        self.define_builtin_macro_lexed("__DBL_MIN__", "((double)2.22507385850720138309023271733240406e-308L)");
        self.define_builtin_macro_lexed(
            "__DBL_EPSILON__",
            "((double)2.22044604925031308084726333618164062e-16L)",
        );
        self.define_builtin_macro_with_val("__DBL_DECIMAL_DIG__", "17");

        self.define_builtin_macro_with_val("__LDBL_MANT_DIG__", "64");
        self.define_builtin_macro_with_val("__LDBL_DIG__", "18");
        self.define_builtin_macro_lexed("__LDBL_MIN_EXP__", "(-16381)");
        self.define_builtin_macro_with_val("__LDBL_MAX_EXP__", "16384");
        self.define_builtin_macro_lexed("__LDBL_MIN_10_EXP__", "(-4931)");
        self.define_builtin_macro_with_val("__LDBL_MAX_10_EXP__", "4932");
        self.define_builtin_macro_lexed("__LDBL_MAX__", "1.18973149535723176502e+4932L");
        self.define_builtin_macro_lexed("__LDBL_MIN__", "3.36210314311209350626e-4932L");
        self.define_builtin_macro_lexed("__LDBL_EPSILON__", "1.08420217248550443401e-19L");
        self.define_builtin_macro_with_val("__LDBL_DECIMAL_DIG__", "21");

        self.define_builtin_macro_with_val("__FLT_RADIX__", "2");
        self.define_builtin_macro_with_val("__DECIMAL_DIG__", "21");
        self.define_builtin_macro_with_val("__FLT_EVAL_METHOD__", "0");
        self.define_builtin_macro_with_val("__FLT_ROUNDS__", "1");

        self.define_builtin_macro_with_val("__FLT_HAS_SUBNORM__", "1");
        self.define_builtin_macro_with_val("__DBL_HAS_SUBNORM__", "1");
        self.define_builtin_macro_with_val("__LDBL_HAS_SUBNORM__", "1");

        self.define_builtin_macro_lexed("__FLT_TRUE_MIN__", "1.40129846e-45F");
        self.define_builtin_macro_lexed("__DBL_TRUE_MIN__", "4.9406564584124654e-324");
        self.define_builtin_macro_lexed("__LDBL_TRUE_MIN__", "3.64519953188247460253e-4951L");
    }

    fn init_builtin_macros_target(&mut self) {
        // Architecture
        match self.target.architecture {
            Architecture::X86_64 => {
                for macro_name in &["__x86_64__", "__x86_64", "__amd64__", "__amd64"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            Architecture::X86_32(_) => {
                for macro_name in &["__i386__", "__i386"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            Architecture::Aarch64(_) => {
                self.define_builtin_macro_one("__aarch64__");
            }
            Architecture::Arm(_) => {
                self.define_builtin_macro_one("__arm__");
            }
            _ => {}
        }

        // Pointer width
        if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(64) == 64 {
            for macro_name in &["__LP64__", "_LP64"] {
                self.define_builtin_macro_one(macro_name);
            }
            self.define_builtin_macro_with_val("__LONG_MAX__", "9223372036854775807L");
            self.define_builtin_macro_with_val("__SIZEOF_LONG__", "8");
            self.define_builtin_macro_with_val("__SIZEOF_POINTER__", "8");
            self.define_builtin_macro_with_val("__INTPTR_MAX__", "9223372036854775807L");
            self.define_builtin_macro_with_val("__UINTPTR_MAX__", "18446744073709551615UL");
            self.define_builtin_macro_with_val("__PTRDIFF_MAX__", "9223372036854775807L");
            self.define_builtin_macro_with_val("__SIZE_MAX__", "18446744073709551615UL");
        } else {
            for macro_name in &["__ILP32__", "_ILP32"] {
                self.define_builtin_macro_one(macro_name);
            }
            self.define_builtin_macro_with_val("__LONG_MAX__", "2147483647L");
            self.define_builtin_macro_with_val("__SIZEOF_LONG__", "4");
            self.define_builtin_macro_with_val("__SIZEOF_POINTER__", "4");
            self.define_builtin_macro_with_val("__INTPTR_MAX__", "2147483647L");
            self.define_builtin_macro_with_val("__UINTPTR_MAX__", "4294967295UL");
            self.define_builtin_macro_with_val("__PTRDIFF_MAX__", "2147483647L");
            self.define_builtin_macro_with_val("__SIZE_MAX__", "4294967295UL");
        }

        // OS
        match self.target.operating_system {
            OperatingSystem::Linux => {
                for macro_name in &["__linux__", "__linux", "__unix__", "__unix", "__ELF__", "__gnu_linux__"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            OperatingSystem::Darwin(_) => {
                for macro_name in &["__APPLE__", "__MACH__"] {
                    self.define_builtin_macro_one(macro_name);
                }
            }
            OperatingSystem::Windows => {
                self.define_builtin_macro_one("_WIN32");
                if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(32) == 64 {
                    self.define_builtin_macro_one("_WIN64");
                }
            }
            _ => {}
        }
    }

    fn init_builtin_macros_compiler_compat(&mut self) {
        // GCC version macros for compatibility with glibc headers
        // We define these to match what Clang does for GCC compatibility
        self.define_builtin_macro("__extension__", vec![]);
        self.define_builtin_macro("__restrict", vec![]);
        self.define_builtin_macro_with_val("__GNUC__", "4");
        self.define_builtin_macro_with_val("__GNUC_MINOR__", "2");
        self.define_builtin_macro_with_val("__GNUC_PATCHLEVEL__", "1");
        self.define_builtin_macro_string("__VERSION__", "\"4.2.1 (Cendol)\"");

        // Atomic memory ordering constants
        self.define_builtin_macro_with_val("__ATOMIC_RELAXED", "0");
        self.define_builtin_macro_with_val("__ATOMIC_CONSUME", "1");
        self.define_builtin_macro_with_val("__ATOMIC_ACQUIRE", "2");
        self.define_builtin_macro_with_val("__ATOMIC_RELEASE", "3");
        self.define_builtin_macro_with_val("__ATOMIC_ACQ_REL", "4");
        self.define_builtin_macro_with_val("__ATOMIC_SEQ_CST", "5");

        // Sync compare and swap availability
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_1");
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_2");
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_4");
        self.define_builtin_macro_one("__GCC_HAVE_SYNC_COMPARE_AND_SWAP_8");
    }

    fn init_builtin_macros_stdlib_types(&mut self) {
        // Type definitions
        if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(64) == 64 {
            self.define_builtin_macro_lexed("__SIZE_TYPE__", "unsigned long");
            self.define_builtin_macro_lexed("__PTRDIFF_TYPE__", "long");
            self.define_builtin_macro_with_val("__SIZE_WIDTH__", "64");
            self.define_builtin_macro_with_val("__PTRDIFF_WIDTH__", "64");
            self.define_builtin_macro_with_val("__SIZE_MAX__", "18446744073709551615UL");
            self.define_builtin_macro_with_val("__PTRDIFF_MAX__", "9223372036854775807L");
        } else {
            self.define_builtin_macro_lexed("__SIZE_TYPE__", "unsigned int");
            self.define_builtin_macro_lexed("__PTRDIFF_TYPE__", "int");
            self.define_builtin_macro_with_val("__SIZE_WIDTH__", "32");
            self.define_builtin_macro_with_val("__PTRDIFF_WIDTH__", "32");
            self.define_builtin_macro_with_val("__SIZE_MAX__", "4294967295U");
            self.define_builtin_macro_with_val("__PTRDIFF_MAX__", "2147483647");
        }

        self.define_builtin_macro_lexed("__WCHAR_TYPE__", "int");
        self.define_builtin_macro_lexed("__WINT_TYPE__", "unsigned int");
        self.define_builtin_macro_lexed("__SIG_ATOMIC_TYPE__", "int");
        self.define_builtin_macro_lexed("__INTMAX_TYPE__", "long long");
        self.define_builtin_macro_lexed("__UINTMAX_TYPE__", "unsigned long long");

        self.define_builtin_macro_with_val("__WCHAR_WIDTH__", "32");
        self.define_builtin_macro_with_val("__WINT_WIDTH__", "32");
        self.define_builtin_macro_with_val("__SIG_ATOMIC_WIDTH__", "32");
        self.define_builtin_macro_with_val("__INTMAX_WIDTH__", "64");

        self.define_builtin_macro_with_val("__INTMAX_MAX__", "9223372036854775807LL");
        self.define_builtin_macro_with_val("__UINTMAX_MAX__", "18446744073709551615ULL");
    }

    fn init_builtin_macros_standards(&mut self) {
        if self.lang_options.c_standard.is_c11() {
            self.define_builtin_macro_with_val("__STDC_VERSION__", "201112L");
            self.define_builtin_macro_one("__STDC_HOSTED__");
            self.define_builtin_macro_one("__STDC_MB_MIGHT_NEQ_WC__");
            self.define_builtin_macro_one("__STDC_IEC_559__");
            self.define_builtin_macro_one("__STDC_IEC_559_COMPLEX__");
            self.define_builtin_macro_with_val("__STDC_ISO_10646__", "201706L");
            self.define_builtin_macro_one("__STDC_UTF_16__");
            self.define_builtin_macro_one("__STDC_UTF_32__");
        }
        self.define_builtin_macro_with_val("__STDC__", "1");
    }

    fn init_builtin_macros_functions(&mut self) {
        // Integer constant macros
        self.define_builtin_function_macro("__INT8_C", &["c"], "c");
        self.define_builtin_function_macro("__INT16_C", &["c"], "c");
        self.define_builtin_function_macro("__INT32_C", &["c"], "c");
        self.define_builtin_function_macro("__UINT8_C", &["c"], "c");
        self.define_builtin_function_macro("__UINT16_C", &["c"], "c");
        self.define_builtin_function_macro("__UINT32_C", &["c"], "c ## U");

        if self.target.pointer_width().ok().map(|w| w.bits()).unwrap_or(64) == 64 {
            self.define_builtin_function_macro("__INT64_C", &["c"], "c ## L");
            self.define_builtin_function_macro("__UINT64_C", &["c"], "c ## UL");
        } else {
            self.define_builtin_function_macro("__INT64_C", &["c"], "c ## LL");
            self.define_builtin_function_macro("__UINT64_C", &["c"], "c ## ULL");
        }

        self.define_builtin_function_macro("__INTMAX_C", &["c"], "c ## LL");
        self.define_builtin_function_macro("__UINTMAX_C", &["c"], "c ## ULL");
    }

    /// Helper to define a built-in macro with value "1"
    fn define_builtin_macro_one(&mut self, name: &str) {
        self.define_builtin_macro_with_val(name, "1");
    }

    /// Helper to define a built-in macro with a specific number value
    fn define_builtin_macro_with_val(&mut self, name: &str, value: &str) {
        // Bolt ⚡: Reuse the shared digits buffer for small integers (0-255)
        // to avoid SourceId churn and redundant virtual buffers during preprocessor initialization.
        let (source_id, offset, len) = if let Ok(val) = value.parse::<u8>() {
            let (offset, len) = SourceManager::get_digit_metadata(val);
            (self.sm.get_digits_source_id(), offset, len)
        } else {
            let sid = self
                .sm
                .add_buffer(value.as_bytes().to_vec(), "<builtin>", None, FileKind::MacroExpansion);
            (sid, 0, value.len() as u16)
        };

        self.define_builtin_macro(
            name,
            vec![PPToken::new(
                PPTokenKind::Number,
                PPTokenFlags::empty(),
                SourceLoc::new(source_id, offset),
                len,
            )],
        );
    }

    /// Helper to define a built-in macro with a string value
    fn define_builtin_macro_string(&mut self, name: &str, value: &str) {
        let source_id = self
            .sm
            .add_buffer(value.as_bytes().to_vec(), "<builtin>", None, FileKind::MacroExpansion);

        self.define_builtin_macro(
            name,
            vec![PPToken::new(
                PPTokenKind::StringLiteral,
                PPTokenFlags::empty(),
                SourceLoc::new(source_id, 0),
                value.len() as u16,
            )],
        );
    }

    /// Helper to tokenize a string into a list of tokens, ignoring Eod/Eof.
    pub(crate) fn tokenize_synthetic(
        &mut self,
        content: impl Into<Vec<u8>>,
        name: &str,
        kind: FileKind,
    ) -> (Vec<PPToken>, SourceId) {
        let source_id = self.sm.add_buffer(content.into(), name, None, kind);
        let buffer = self.sm.get_buffer_arc(source_id);
        let lexer = PPLexer::new(source_id, buffer);

        // Bolt ⚡: Use Iterator implementation for concise token collection.
        let tokens = lexer
            .filter(|t| !matches!(t.kind, PPTokenKind::Eod | PPTokenKind::Eof))
            .collect();

        (tokens, source_id)
    }

    /// Helper to lex a macro value string into tokens
    fn lex_macro_value(&mut self, value: &str, source_name: &str) -> Vec<PPToken> {
        let kind = if source_name == "<command-line>" {
            FileKind::Synthetic
        } else {
            FileKind::Builtin
        };
        self.tokenize_synthetic(value.as_bytes().to_vec(), source_name, kind).0
    }

    /// Helper to define a built-in macro by lexing its value
    fn define_builtin_macro_lexed(&mut self, name: &str, value: &str) {
        let tokens = self.lex_macro_value(value, "<builtin>");
        self.define_builtin_macro(name, tokens);
    }

    /// Define a macro from command line or other external source
    pub(crate) fn define_user_macro(&mut self, name: &str, value: Option<&str>) {
        let value_str = value.unwrap_or("1");
        let tokens = self.lex_macro_value(value_str, "<command-line>");

        let symbol = StringId::new(name);
        let macro_info = MacroInfo {
            tokens: Arc::from(tokens),
            ..Default::default()
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Define a built-in macro
    fn define_builtin_macro(&mut self, name: &str, tokens: Vec<PPToken>) {
        let symbol = StringId::new(name);
        let macro_info = MacroInfo {
            flags: MacroFlags::BUILTIN,
            tokens: Arc::from(tokens),
            ..Default::default()
        };
        self.macros.insert(symbol, macro_info);
    }

    /// Define a built-in function-like macro
    fn define_builtin_function_macro(&mut self, name: &str, params: &[&str], body: &str) {
        let symbol = StringId::new(name);
        let param_symbols: Vec<StringId> = params.iter().map(|&p| StringId::new(p)).collect();
        let tokens = self.lex_macro_value(body, "<builtin>");

        // Pre-calculate expansion needs for built-in function-like macros
        let mut needs_expansion = vec![false; param_symbols.len()];
        for i in 0..tokens.len() {
            if let PPTokenKind::Identifier(sym) = tokens[i].kind
                && let Some(idx) = param_symbols.iter().position(|&p| p == sym)
            {
                let preceded_by_hash = i > 0 && tokens[i - 1].kind == PPTokenKind::Hash;
                let preceded_by_hashhash = i > 0 && tokens[i - 1].kind == PPTokenKind::HashHash;
                let followed_by_hashhash = i + 1 < tokens.len() && tokens[i + 1].kind == PPTokenKind::HashHash;

                if !preceded_by_hash && !preceded_by_hashhash && !followed_by_hashhash {
                    needs_expansion[idx] = true;
                }
            }
        }

        let macro_info = MacroInfo {
            flags: MacroFlags::BUILTIN | MacroFlags::FUNCTION_LIKE,
            tokens: Arc::from(tokens),
            parameter_list: Arc::from(param_symbols),
            parameter_needs_expansion: Arc::from(needs_expansion),
            ..Default::default()
        };
        self.macros.insert(symbol, macro_info);
    }
}
