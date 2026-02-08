//! Object file generation from Cranelift IR.
//!
//! This module provides functionality for generating object files
//! from compiled Cranelift IR. Currently, the object generation logic
//! is integrated within `ClifGen::compile_module`, but this module
//! provides a future extension point for more advanced object file manipulation.

use cranelift_object::ObjectModule;

/// Object file generator.
///
/// This struct wraps the Cranelift ObjectModule finalization process.
pub struct ObjectGen;

impl ObjectGen {
    /// Finalize an ObjectModule and produce the raw object file bytes.
    pub fn finalize(module: ObjectModule) -> Result<Vec<u8>, String> {
        let product = module.finish();
        product
            .object
            .write()
            .map_err(|e| format!("Failed to write object file: {:?}", e))
    }
}
