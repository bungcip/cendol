use crate::mir::{
    ConstValue, ConstValueId, Global, GlobalId, Local, LocalId, MirBlock, MirBlockId, MirFunction, MirFunctionId,
    MirModule, MirStmt, MirStmtId, MirType, TypeId,
};
use hashbrown::HashMap;

/// Complete semantic analysis output containing all MIR data structures
/// NOTE: need better name
#[derive(Clone)]
pub struct SemaOutput {
    pub module: MirModule,
    pub functions: HashMap<MirFunctionId, MirFunction>,
    pub blocks: HashMap<MirBlockId, MirBlock>,
    pub locals: HashMap<LocalId, Local>,
    pub globals: HashMap<GlobalId, Global>,
    pub types: HashMap<TypeId, MirType>,
    pub constants: HashMap<ConstValueId, ConstValue>,
    pub statements: HashMap<MirStmtId, MirStmt>,
}

/// Semantic analysis output with AST for symbol resolver dumping
#[derive(Clone)]
pub struct SemaOutputWithAst {
    pub sema_output: SemaOutput,
}

impl SemaOutput {
    /// get type or panic if not found
    pub(crate) fn get_type(&self, id: TypeId) -> &MirType {
        match self.types.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Type ID {id} not found"),
        }
    }
    pub(crate) fn get_local(&self, id: LocalId) -> &Local {
        match self.locals.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Local ID {id} not found"),
        }
    }
    pub(crate) fn get_function(&self, id: MirFunctionId) -> &MirFunction {
        match self.functions.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Function ID {id} not found"),
        }
    }
    pub(crate) fn get_global(&self, id: GlobalId) -> &Global {
        match self.globals.get(&id) {
            Some(id) => id,
            None => panic!("ICE: Global ID {id} not found"),
        }
    }
}
