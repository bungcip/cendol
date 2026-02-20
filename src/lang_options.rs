/// supported C standards
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum CStandard {
    C89,
    C99,
    #[default]
    C11,
}

impl CStandard {
    /// Check if C11 standard is enabled
    pub(crate) fn is_c11(&self) -> bool {
        matches!(self, CStandard::C11)
    }
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
    fn test_c_standard_default() {
        assert_eq!(CStandard::default(), CStandard::C11);
    }

    #[test]
    fn test_c_standard_is_c11() {
        assert!(CStandard::C11.is_c11());
        assert!(!CStandard::C99.is_c11());
        assert!(!CStandard::C89.is_c11());
    }
}
