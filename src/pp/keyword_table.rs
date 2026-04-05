use crate::ast::StringId;

/// Preprocessor directive kinds
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DirectiveKind {
    Define,
    Undef,
    Include,
    IncludeNext,
    If,
    Ifdef,
    Ifndef,
    Elif,
    Elifdef,
    Elifndef,
    Else,
    Endif,
    Line,
    Pragma,
    Error,
    Warning,
}

/// Table of pre-interned preprocessor keywords for O(1) identification
#[derive(Clone)]
pub struct PPKeywordTable {
    pub(crate) define: StringId,
    pub(crate) undef: StringId,
    pub(crate) include: StringId,
    pub(crate) include_next: StringId,
    pub(crate) if_: StringId,
    pub(crate) ifdef: StringId,
    pub(crate) ifndef: StringId,
    pub(crate) elif: StringId,
    pub(crate) elifdef: StringId,
    pub(crate) elifndef: StringId,
    pub(crate) else_: StringId,
    pub(crate) endif: StringId,
    pub(crate) line: StringId,
    pub(crate) pragma: StringId,
    pub(crate) error: StringId,
    pub(crate) warning: StringId,
    pub(crate) defined: StringId, // For the defined operator in expressions
    pub(crate) has_include: StringId,
    pub(crate) has_include_next: StringId,
    pub(crate) has_builtin: StringId,
    pub(crate) has_attribute: StringId,
    pub(crate) has_feature: StringId,
    pub(crate) has_extension: StringId,
    pub(crate) line_macro: StringId,
    pub(crate) file_macro: StringId,
    pub(crate) counter_macro: StringId,
    pub(crate) pragma_operator: StringId,
    pub(crate) va_opt: StringId,
    pub(crate) once: StringId,
    pub(crate) push_macro: StringId,
    pub(crate) pop_macro: StringId,
    pub(crate) message: StringId,
    pub(crate) pack: StringId,
    pub(crate) push: StringId,
    pub(crate) pop: StringId,
    pub(crate) c_true: StringId,
    pub(crate) builtin_va_arg: StringId,
    pub(crate) builtin_va_list: StringId,
    pub(crate) builtin_va_start: StringId,
    pub(crate) builtin_va_end: StringId,
    pub(crate) builtin_va_copy: StringId,
    pub(crate) builtin_expect: StringId,
    pub(crate) builtin_memcmp: StringId,
    pub(crate) builtin_memcpy: StringId,
    pub(crate) builtin_memset: StringId,
    pub(crate) builtin_memmove: StringId,
    pub(crate) builtin_offsetof: StringId,
    pub(crate) builtin_choose_expr: StringId,
    pub(crate) builtin_types_compatible_p: StringId,
    pub(crate) builtin_constant_p: StringId,
    pub(crate) builtin_unreachable: StringId,
    pub(crate) builtin_trap: StringId,
    pub(crate) builtin_prefetch: StringId,
    pub(crate) builtin_alloca: StringId,
    pub(crate) builtin_popcount: StringId,
    pub(crate) builtin_popcountl: StringId,
    pub(crate) builtin_popcountll: StringId,
    pub(crate) builtin_clz: StringId,
    pub(crate) builtin_clzl: StringId,
    pub(crate) builtin_clzll: StringId,
    pub(crate) builtin_ctz: StringId,
    pub(crate) builtin_ctzl: StringId,
    pub(crate) builtin_ctzll: StringId,
    pub(crate) builtin_ffs: StringId,
    pub(crate) builtin_ffsl: StringId,
    pub(crate) builtin_ffsll: StringId,
    pub(crate) builtin_bswap16: StringId,
    pub(crate) builtin_bswap32: StringId,
    pub(crate) builtin_bswap64: StringId,
    pub(crate) builtin_fabs: StringId,
    pub(crate) builtin_fabsf: StringId,
    pub(crate) builtin_fabsl: StringId,
    pub(crate) builtin_inf: StringId,
    pub(crate) builtin_inff: StringId,
    pub(crate) builtin_huge_val: StringId,
    pub(crate) builtin_huge_valf: StringId,
    pub(crate) builtin_nan: StringId,
    pub(crate) builtin_nanf: StringId,
    pub(crate) atomic_load_n: StringId,
    pub(crate) atomic_store_n: StringId,
    pub(crate) atomic_exchange_n: StringId,
    pub(crate) atomic_compare_exchange_n: StringId,
    pub(crate) atomic_fetch_add: StringId,
    pub(crate) atomic_fetch_sub: StringId,
    pub(crate) atomic_fetch_and: StringId,
    pub(crate) atomic_fetch_or: StringId,
    pub(crate) atomic_fetch_xor: StringId,
    pub(crate) c_static_assert: StringId,
    pub(crate) c_generic_selection: StringId,
    pub(crate) c_atomic: StringId,
    pub(crate) c_alignas: StringId,
    pub(crate) c_alignof: StringId,
    pub(crate) c_thread_local: StringId,
}

impl Default for PPKeywordTable {
    fn default() -> Self {
        Self::new()
    }
}

impl PPKeywordTable {
    pub(crate) fn new() -> Self {
        PPKeywordTable {
            define: StringId::new("define"),
            undef: StringId::new("undef"),
            include: StringId::new("include"),
            include_next: StringId::new("include_next"),
            if_: StringId::new("if"),
            ifdef: StringId::new("ifdef"),
            ifndef: StringId::new("ifndef"),
            elif: StringId::new("elif"),
            elifdef: StringId::new("elifdef"),
            elifndef: StringId::new("elifndef"),
            else_: StringId::new("else"),
            endif: StringId::new("endif"),
            line: StringId::new("line"),
            pragma: StringId::new("pragma"),
            error: StringId::new("error"),
            warning: StringId::new("warning"),
            defined: StringId::new("defined"),
            has_include: StringId::new("__has_include"),
            has_include_next: StringId::new("__has_include_next"),
            has_builtin: StringId::new("__has_builtin"),
            has_attribute: StringId::new("__has_attribute"),
            has_feature: StringId::new("__has_feature"),
            has_extension: StringId::new("__has_extension"),
            line_macro: StringId::new("__LINE__"),
            file_macro: StringId::new("__FILE__"),
            counter_macro: StringId::new("__COUNTER__"),
            pragma_operator: StringId::new("_Pragma"),
            va_opt: StringId::new("__VA_OPT__"),
            once: StringId::new("once"),
            push_macro: StringId::new("push_macro"),
            pop_macro: StringId::new("pop_macro"),
            message: StringId::new("message"),
            pack: StringId::new("pack"),
            push: StringId::new("push"),
            pop: StringId::new("pop"),
            builtin_va_arg: StringId::new("__builtin_va_arg"),
            builtin_va_list: StringId::new("__builtin_va_list"),
            builtin_va_start: StringId::new("__builtin_va_start"),
            builtin_va_end: StringId::new("__builtin_va_end"),
            builtin_va_copy: StringId::new("__builtin_va_copy"),
            builtin_expect: StringId::new("__builtin_expect"),
            builtin_memcmp: StringId::new("__builtin_memcmp"),
            builtin_memcpy: StringId::new("__builtin_memcpy"),
            builtin_memset: StringId::new("__builtin_memset"),
            builtin_memmove: StringId::new("__builtin_memmove"),
            builtin_offsetof: StringId::new("__builtin_offsetof"),
            builtin_choose_expr: StringId::new("__builtin_choose_expr"),
            builtin_types_compatible_p: StringId::new("__builtin_types_compatible_p"),
            builtin_constant_p: StringId::new("__builtin_constant_p"),
            builtin_unreachable: StringId::new("__builtin_unreachable"),
            builtin_trap: StringId::new("__builtin_trap"),
            builtin_prefetch: StringId::new("__builtin_prefetch"),
            builtin_alloca: StringId::new("__builtin_alloca"),
            builtin_popcount: StringId::new("__builtin_popcount"),
            builtin_popcountl: StringId::new("__builtin_popcountl"),
            builtin_popcountll: StringId::new("__builtin_popcountll"),
            builtin_clz: StringId::new("__builtin_clz"),
            builtin_clzl: StringId::new("__builtin_clzl"),
            builtin_clzll: StringId::new("__builtin_clzll"),
            builtin_ctz: StringId::new("__builtin_ctz"),
            builtin_ctzl: StringId::new("__builtin_ctzl"),
            builtin_ctzll: StringId::new("__builtin_ctzll"),
            builtin_ffs: StringId::new("__builtin_ffs"),
            builtin_ffsl: StringId::new("__builtin_ffsl"),
            builtin_ffsll: StringId::new("__builtin_ffsll"),
            builtin_bswap16: StringId::new("__builtin_bswap16"),
            builtin_bswap32: StringId::new("__builtin_bswap32"),
            builtin_bswap64: StringId::new("__builtin_bswap64"),
            builtin_fabs: StringId::new("__builtin_fabs"),
            builtin_fabsf: StringId::new("__builtin_fabsf"),
            builtin_fabsl: StringId::new("__builtin_fabsl"),
            builtin_inf: StringId::new("__builtin_inf"),
            builtin_inff: StringId::new("__builtin_inff"),
            builtin_huge_val: StringId::new("__builtin_huge_val"),
            builtin_huge_valf: StringId::new("__builtin_huge_valf"),
            builtin_nan: StringId::new("__builtin_nan"),
            builtin_nanf: StringId::new("__builtin_nanf"),
            atomic_load_n: StringId::new("__atomic_load_n"),
            atomic_store_n: StringId::new("__atomic_store_n"),
            atomic_exchange_n: StringId::new("__atomic_exchange_n"),
            atomic_compare_exchange_n: StringId::new("__atomic_compare_exchange_n"),
            atomic_fetch_add: StringId::new("__atomic_fetch_add"),
            atomic_fetch_sub: StringId::new("__atomic_fetch_sub"),
            atomic_fetch_and: StringId::new("__atomic_fetch_and"),
            atomic_fetch_or: StringId::new("__atomic_fetch_or"),
            atomic_fetch_xor: StringId::new("__atomic_fetch_xor"),
            c_true: StringId::new("true"),
            c_static_assert: StringId::new("c_static_assert"),
            c_generic_selection: StringId::new("c_generic_selection"),
            c_atomic: StringId::new("c_atomic"),
            c_alignas: StringId::new("c_alignas"),
            c_alignof: StringId::new("c_alignof"),
            c_thread_local: StringId::new("c_thread_local"),
        }
    }

    pub(crate) fn is_directive(&self, symbol: StringId) -> Option<DirectiveKind> {
        if symbol == self.define {
            Some(DirectiveKind::Define)
        } else if symbol == self.undef {
            Some(DirectiveKind::Undef)
        } else if symbol == self.include {
            Some(DirectiveKind::Include)
        } else if symbol == self.include_next {
            Some(DirectiveKind::IncludeNext)
        } else if symbol == self.if_ {
            Some(DirectiveKind::If)
        } else if symbol == self.ifdef {
            Some(DirectiveKind::Ifdef)
        } else if symbol == self.ifndef {
            Some(DirectiveKind::Ifndef)
        } else if symbol == self.elif {
            Some(DirectiveKind::Elif)
        } else if symbol == self.elifdef {
            Some(DirectiveKind::Elifdef)
        } else if symbol == self.elifndef {
            Some(DirectiveKind::Elifndef)
        } else if symbol == self.else_ {
            Some(DirectiveKind::Else)
        } else if symbol == self.endif {
            Some(DirectiveKind::Endif)
        } else if symbol == self.line {
            Some(DirectiveKind::Line)
        } else if symbol == self.pragma {
            Some(DirectiveKind::Pragma)
        } else if symbol == self.error {
            Some(DirectiveKind::Error)
        } else if symbol == self.warning {
            Some(DirectiveKind::Warning)
        } else {
            None
        }
    }

    /// Get the interned symbol for the "defined" operator
    pub(crate) fn defined_symbol(&self) -> StringId {
        self.defined
    }

    /// Get the interned symbol for the "__has_include" operator
    pub(crate) fn has_include_symbol(&self) -> StringId {
        self.has_include
    }

    /// Get the interned symbol for the "__has_include_next" operator
    pub(crate) fn has_include_next_symbol(&self) -> StringId {
        self.has_include_next
    }

    /// Get the interned symbol for the "__has_builtin" operator
    pub(crate) fn has_builtin_symbol(&self) -> StringId {
        self.has_builtin
    }

    /// Get the interned symbol for the "__has_attribute" operator
    pub(crate) fn has_attribute_symbol(&self) -> StringId {
        self.has_attribute
    }

    /// Get the interned symbol for the "__has_feature" operator
    pub(crate) fn has_feature_symbol(&self) -> StringId {
        self.has_feature
    }

    /// Get the interned symbol for the "__has_extension" operator
    pub(crate) fn has_extension_symbol(&self) -> StringId {
        self.has_extension
    }
}
