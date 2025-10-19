use crate::{
    codegen::error::CodegenError, parser::error::ParserError,
    preprocessor::error::PreprocessorError,
};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum Error {
    #[error("{0}")]
    Preprocessor(#[from] PreprocessorError),
    #[error("{0}")]
    Parser(#[from] ParserError),
    #[error("{0}")]
    Codegen(#[from] CodegenError),
}

#[derive(Debug, Clone)]
pub struct Report {
    msg: String,
    path: Option<String>,
    loc: Option<(usize, usize)>,
}

impl Report {
    pub fn new(msg: String, path: Option<String>, loc: Option<(usize, usize)>) -> Self {
        Self { msg, path, loc }
    }
}

pub fn report(report: &Report) {
    eprintln!("\x1b[31mError\x1b[0m: {}", report.msg);
    if let Some(path) = &report.path {
        if let Some((line, col)) = report.loc {
            eprintln!(" --> {}:{}:{}", path, line, col);
        } else {
            eprintln!(" --> {}", path);
        }
    }
}