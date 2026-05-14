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
pub(crate) struct ObjectGen;

impl ObjectGen {
    /// Finalize an ObjectModule and produce the raw object file bytes.
    pub(super) fn finalize(module: ObjectModule) -> Result<Vec<u8>, String> {
        let product = module.finish();
        let mut object = product.object;

        // Add .comment section with compiler fingerprint
        // We include a null terminator to follow standard conventions for this section.
        let comment = format!("cendol: (Cendol) {}\0", env!("CARGO_PKG_VERSION"));
        let section_id = object.add_section(
            vec![],
            b".comment".to_vec(),
            cranelift_object::object::SectionKind::Metadata,
        );
        object.append_section_data(section_id, comment.as_bytes(), 1);

        object
            .write()
            .map_err(|e| format!("Failed to write object file: {:?}", e))
    }
}
