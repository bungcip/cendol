/// supported C standards
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CStandard {
    C89,
    C99,
    C11,
}

impl From<&str> for CStandard {
    fn from(s: &str) -> Self {
        match s {
            "c89" | "c90" => CStandard::C89,
            "c99" => CStandard::C99,
            "c11" => CStandard::C11,
            _ => CStandard::C11, // default to C11
        }
    }
}

/// Language options affecting compilation behavior
#[derive(Copy, Clone, Debug, Default)]
pub struct LangOptions {
    pub c_standard: Option<CStandard>, // C standard version (e.g., "c99", "c11")
}

impl LangOptions {
    #[cfg(test)]
    pub(crate) fn c11() -> Self {
        LangOptions {
            c_standard: Some(CStandard::C11),
        }
    }

    /// Check if C11 standard is enabled
    pub(crate) fn is_c11(&self) -> bool {
        matches!(self.c_standard, Some(CStandard::C11))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lang_options_c11() {
        let options = LangOptions::c11();
        assert!(options.is_c11());
        assert_eq!(options.c_standard, Some(CStandard::C11));
    }

    #[test]
    fn test_lang_options_default() {
        let options = LangOptions::default();
        assert!(!options.is_c11());
        assert_eq!(options.c_standard, None);
    }
}
