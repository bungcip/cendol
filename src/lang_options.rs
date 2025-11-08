/// Language options affecting compilation behavior
#[derive(Clone)]
pub struct LangOptions {
    pub c11: bool,              // C11 standard compliance
    pub gnu_mode: bool,         // GNU extensions
    pub ms_extensions: bool,    // Microsoft extensions
}