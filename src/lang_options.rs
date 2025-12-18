/// Language options affecting compilation behavior
#[derive(Clone, Debug)]
pub struct LangOptions {
    pub c11: bool,                  // C11 standard compliance
    pub gnu_mode: bool,             // GNU extensions
    pub ms_extensions: bool,        // Microsoft extensions
    pub pedantic: bool,             // Pedantic mode (strict standards compliance)
    pub c_standard: Option<String>, // C standard version (e.g., "c99", "c11")
}

impl LangOptions {
    pub fn c11() -> Self {
        LangOptions {
            c11: true,
            gnu_mode: false,
            ms_extensions: false,
            pedantic: false,
            c_standard: Some("c11".to_string()),
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
