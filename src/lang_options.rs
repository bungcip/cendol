/// supported C standards
#[derive(Copy, Clone, Debug, PartialEq, Eq, Default)]
pub enum CStandard {
    #[default]
    C11,
    C17,
    C23,
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
            "c11" => CStandard::C11,
            "c17" => CStandard::C17,
            "c23" => CStandard::C23,
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
    }

    #[test]
    fn test_c_standard_from_str() {
        assert_eq!(CStandard::from("c11"), CStandard::C11);
        assert_eq!(CStandard::from("invalid"), CStandard::C11);
    }
}
