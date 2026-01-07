use crate::ast::Ast;
use crate::ast::SourceId;
use crate::lexer::Token;
use crate::pp::PPToken;
use crate::semantic::output::SemaOutput;
use crate::semantic::{SymbolTable, TypeRegistry};

/// compilation outputs for all source files
pub struct PipelineOutputs {
    pub units: indexmap::IndexMap<SourceId, CompileArtifact>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Default)]
pub enum CompilePhase {
    Preprocess,
    Lex,
    Parse,
    SymbolResolver,
    Mir,
    Cranelift,
    #[default]
    EmitObject,
}

/// outputs for a single compilation unit
#[derive(Default)]
pub struct CompileArtifact {
    pub preprocessed: Option<Vec<PPToken>>,
    pub lexed: Option<Vec<Token>>,
    pub ast: Option<Ast>,
    pub sema_output: Option<SemaOutput>,
    pub clif_dump: Option<String>,
    pub object_file: Option<Vec<u8>>,
    pub type_registry: Option<TypeRegistry>,
    pub symbol_table: Option<SymbolTable>,
}
