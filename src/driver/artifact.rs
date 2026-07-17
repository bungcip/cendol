use crate::ast::SourceId;
use crate::ast::{Ast, PAst};
use crate::mir::MirProgram;
use crate::parser::Token;
use crate::pp::PPToken;
use crate::semantic::{SymbolTable, TypeRegistry};

/// compilation outputs for all source files
pub struct PipelineOutputs {
    pub(crate) units: indexmap::IndexMap<SourceId, CompileArtifact>,
    pub(crate) external_object_files: Vec<std::path::PathBuf>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum CompilePhase {
    Preprocess,
    Lex,
    Parse,
    SemanticLowering,
    Mir,
    Cranelift,
    #[default]
    EmitObject,
}

/// outputs for a single compilation unit
#[derive(Default)]
pub struct CompileArtifact {
    pub(crate) preprocessed: Option<Vec<PPToken>>,
    pub(crate) lexed: Option<Vec<Token>>,
    pub(crate) parsed_ast: Option<PAst>,
    pub(crate) ast: Option<Ast>,
    pub(crate) mir_program: Option<MirProgram>,
    pub(crate) clif_dump: Option<String>,
    pub(crate) object_file: Option<Vec<u8>>,
    pub(crate) type_registry: Option<TypeRegistry>,
    pub(crate) symbol_table: Option<SymbolTable>,
}
