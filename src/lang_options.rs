use bitflags::bitflags;

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lang_flags_c11() {
        let options = LangOptions::c11();
        assert!(options.is_c11());
        assert!(!options.is_pedantic());
    }

    #[test]
    fn test_lang_flags_default() {
        let options = LangOptions::default();
        assert!(!options.is_c11());
        assert!(!options.is_pedantic());
    }

    #[test]
    fn test_lang_flags_combinations() {
        let flags = LangFlags::PEDANTIC;
        let options = LangOptions {
            flags,
            c_standard: Some(CStandard::C11),
        };
        assert!(options.is_c11());
        assert!(options.is_pedantic());
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct LangFlags: u8 {
        const PEDANTIC = 1 << 0;
    }
}

/// Language options affecting compilation behavior
#[derive(Copy, Clone, Debug)]
pub struct LangOptions {
    pub flags: LangFlags,
    pub c_standard: Option<CStandard>, // C standard version (e.g., "c99", "c11")
}

impl LangOptions {
    pub fn c11() -> Self {
        LangOptions {
            flags: LangFlags::empty(),
            c_standard: Some(CStandard::C11),
        }
    }

    /// Check if C11 standard is enabled
    pub fn is_c11(&self) -> bool {
        matches!(self.c_standard, Some(CStandard::C11))
    }

    /// Check if pedantic mode is enabled
    pub fn is_pedantic(&self) -> bool {
        self.flags.contains(LangFlags::PEDANTIC)
    }
}

impl Default for LangOptions {
    fn default() -> Self {
        LangOptions {
            flags: LangFlags::empty(),
            c_standard: None,
        }
    }
}
