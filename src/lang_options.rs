/// Language options affecting compilation behavior
#[derive(Clone)]
pub struct LangOptions {
    pub c11: bool,           // C11 standard compliance
    pub gnu_mode: bool,      // GNU extensions
    pub ms_extensions: bool, // Microsoft extensions
}

impl LangOptions {
    pub fn c11() -> Self {
        LangOptions {
            c11: true,
            gnu_mode: false,
            ms_extensions: false,
        }
    }
}
