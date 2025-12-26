/// supported C standards
#[derive(Copy, Clone, Debug)]
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
/// TODO: change to bitflags
#[derive(Copy, Clone, Debug)]
pub struct LangOptions {
    pub c11: bool,                     // C11 standard compliance
    pub gnu_mode: bool,                // GNU extensions
    pub ms_extensions: bool,           // Microsoft extensions
    pub pedantic: bool,                // Pedantic mode (strict standards compliance)
    pub c_standard: Option<CStandard>, // C standard version (e.g., "c99", "c11")
}

impl LangOptions {
    pub fn c11() -> Self {
        LangOptions {
            c11: true,
            gnu_mode: false,
            ms_extensions: false,
            pedantic: false,
            c_standard: Some(CStandard::C11),
        }
    }
}

impl Default for LangOptions {
    fn default() -> Self {
        LangOptions {
            c11: false,
            gnu_mode: true,
            ms_extensions: false,
            pedantic: false,
            c_standard: None,
        }
    }
}
