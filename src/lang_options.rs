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
        assert!(options.flags.contains(LangFlags::C11));
    }

    #[test]
    fn test_lang_flags_default() {
        let options = LangOptions::default();
        assert!(!options.is_c11());
        assert!(options.flags.is_empty());
    }

    #[test]
    fn test_lang_flags_combinations() {
        let flags = LangFlags::C11;
        let options = LangOptions {
            flags,
            c_standard: None,
        };
        assert!(options.is_c11());
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
    pub struct LangFlags: u8 {
        const C11 = 1 << 0;
    }
}

/// Language options affecting compilation behavior
#[derive(Copy, Clone, Debug, Default)]
pub struct LangOptions {
    pub flags: LangFlags,
    pub c_standard: Option<CStandard>, // C standard version (e.g., "c99", "c11")
}

impl LangOptions {
    pub fn c11() -> Self {
        LangOptions {
            flags: LangFlags::C11,
            c_standard: Some(CStandard::C11),
        }
    }

    /// Check if C11 standard is enabled
    pub fn is_c11(&self) -> bool {
        self.flags.contains(LangFlags::C11)
    }
}
