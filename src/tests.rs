pub mod codegen_abi;
pub mod codegen_abi_compat;
pub mod codegen_basics;
pub mod codegen_calls;
pub mod codegen_common;
pub mod codegen_regr_movi;
pub mod codegen_runtime;
pub mod codegen_structs;
pub mod codegen_switch;
pub mod codegen_variadic;

pub mod driver_ast_dumper;
pub mod driver_source_manager;

pub mod pp_common;
pub mod pp_directives;
pub mod pp_expressions;
pub mod pp_include;

pub mod pp_internal;
pub mod pp_lexical;
pub mod pp_macros;
pub mod pp_output_dump;
pub mod pp_pragma;

pub mod semantic_arrays;
pub mod semantic_builtins;
pub mod semantic_control_flow;
pub mod semantic_enums;
pub mod semantic_expr;
pub mod semantic_functions;
pub mod semantic_init;
pub mod semantic_scope;
pub mod semantic_types;

pub mod semantic_common;
pub mod semantic_const_eval;
pub mod semantic_lowering;
pub mod semantic_mir;
pub mod semantic_negative;
pub mod semantic_regr_unary_promotion;
pub mod semantic_validation;

pub mod parser_decl;
pub mod parser_expr;
pub mod parser_lexical;
pub mod parser_regr;
pub mod parser_stmt;
pub mod parser_type_regr;
pub mod parser_utils;

pub mod codegen_ternary_array_size;
pub mod parser_gcc_extensions;

pub mod semantic_alignment;
pub mod semantic_alignment_constraints;
pub mod semantic_composite;
pub mod test_utils;

pub mod builtin_offsetof;
pub mod codegen_cast_init;
pub mod codegen_regr;
pub mod guardian_addr_sizeof_constraints;
pub mod guardian_alignof_sizeof_function;
pub mod guardian_bitfields;
pub mod guardian_linkage;
pub mod guardian_parameter_storage;
pub mod guardian_pointer_arithmetic;
pub mod guardian_restrict_constraints;
pub mod mir_unit;
pub mod parser_type_conflict;
pub mod pp_u8_literal;
pub mod semantic_atomic;
pub mod semantic_brace_elision;
pub mod semantic_complex_types;
pub mod semantic_generic;
pub mod semantic_mir_const_global;
pub mod semantic_scope_invariants;
