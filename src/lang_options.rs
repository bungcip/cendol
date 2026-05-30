/// supported C standards
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum CStandard {
    #[default]
    C11,
    C17,
    C23,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default, serde::Serialize)]
pub enum SignedOverflowMode {
    #[default]
    Wrap,
    Trap,
    Undefined,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Default, Hash, serde::Serialize)]
pub enum Visibility {
    #[default]
    Default,
    Hidden,
    Protected,
    Internal,
}

impl std::str::FromStr for Visibility {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "default" => Ok(Visibility::Default),
            "hidden" => Ok(Visibility::Hidden),
            "protected" => Ok(Visibility::Protected),
            "internal" => Ok(Visibility::Internal),
            _ => Err(format!("invalid visibility: {}", s)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct LangOptions {
    pub c_standard: CStandard,
    pub pedantic: bool,
    pub pedantic_errors: bool,
    pub signed_overflow_mode: SignedOverflowMode,
    pub fpic: bool,
    pub visibility: Visibility,
}

impl Default for LangOptions {
    fn default() -> Self {
        Self {
            c_standard: CStandard::default(),
            pedantic: false,
            pedantic_errors: false,
            signed_overflow_mode: SignedOverflowMode::Wrap, // cendol defaults to wrapping
            fpic: true,                                     // cendol defaults to PIC
            visibility: Visibility::Default,
        }
    }
}

impl LangOptions {
    pub(crate) fn is_pedantic(&self) -> bool {
        self.pedantic || self.pedantic_errors
    }
}

impl CStandard {
    /// Check if C11 standard is enabled
    pub(crate) fn is_c11(&self) -> bool {
        matches!(self, CStandard::C11)
    }
}

impl std::str::FromStr for CStandard {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "c11" => Ok(CStandard::C11),
            "c17" => Ok(CStandard::C17),
            "c23" => Ok(CStandard::C23),
            _ => Err(format!("invalid C standard: {}", s)),
        }
    }
}

impl From<&str> for CStandard {
    fn from(s: &str) -> Self {
        s.parse().unwrap_or(CStandard::C11)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_c_standard_default() {
        assert_eq!(CStandard::default(), CStandard::C11);
    }

    #[test]
    fn test_c_standard_is_c11() {
        assert!(CStandard::C11.is_c11());
    }

    #[test]
    fn test_c_standard_from_str() {
        assert_eq!(CStandard::from("c11"), CStandard::C11);
        assert_eq!(CStandard::from("c17"), CStandard::C17);
        assert_eq!(CStandard::from("c23"), CStandard::C23);
        assert_eq!(CStandard::from("invalid"), CStandard::C11);
    }
}
