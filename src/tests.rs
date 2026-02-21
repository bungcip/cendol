pub mod codegen_abi;
pub mod codegen_abi_compat;
pub mod codegen_basics;
pub mod codegen_calls;
pub mod codegen_common;
pub mod codegen_large_array;

pub mod codegen_offsetof;
pub mod codegen_runtime;
pub mod codegen_structs;
pub mod codegen_switch;
pub mod codegen_variadic;

pub mod driver_ast_dumper;
pub mod driver_source_manager;

pub mod pp_common;
pub mod pp_conditionals;
pub mod pp_directives;
pub mod pp_features;
pub mod pp_includes;
pub mod pp_internal;
pub mod pp_lexical;
pub mod pp_macros;

pub mod semantic_arrays;
pub mod semantic_builtins;
pub mod semantic_control_flow;
pub mod semantic_deref_check;
pub mod semantic_enums;
pub mod semantic_expr;
pub mod semantic_float_init;
pub mod semantic_function_arg_check;
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
pub mod parser_declarator_coverage;
pub mod parser_expr;
pub mod parser_lexical;
pub mod parser_stmt;
pub mod parser_types;
pub mod parser_utils;

pub mod codegen_ternary_array_size;
pub mod parser_gcc_extensions;
pub mod parser_type_spec_coverage;

pub mod semantic_alignment;
pub mod semantic_alignment_constraints;
pub mod semantic_composite;
pub mod test_utils;

pub mod ast_dumper_coverage;

pub mod codegen_cast_init;
pub mod codegen_regr;
pub mod driver_defines;
pub mod guardian_addr_sizeof_constraints;
pub mod guardian_alignof_sizeof_function;
pub mod guardian_array_parameter_qualifiers;
pub mod guardian_bitfields;
pub mod guardian_function_specifiers;
pub mod guardian_generic_constraints;
pub mod guardian_linkage;
pub mod guardian_noreturn_break;
pub mod guardian_parameter_storage;
pub mod guardian_pointer_arithmetic;
pub mod guardian_restrict_constraints;
pub mod guardian_struct_member_constraints;
pub mod guardian_tentative_definitions;
pub mod guardian_type_limits;
pub mod guardian_typedef_constraints;
pub mod mir_dumper_coverage;
pub mod mir_gen_compound_assignment;
pub mod mir_gen_function_calls;
pub mod mir_gen_sizeof;
pub mod mir_unit;
pub mod mir_validation;
pub mod parser_attributes_declarator;
pub mod pp_dumper_coverage;
pub mod semantic_assignment_coverage;
pub mod semantic_atomic;
pub mod semantic_brace_elision;
pub mod semantic_caserange;
pub mod semantic_complex_types;
pub mod semantic_const_recursive;
pub mod semantic_generic;
pub mod semantic_integer_literals;
pub mod semantic_mir_const_global;
pub mod semantic_noreturn;
pub mod semantic_parsed_types_coverage;
pub mod semantic_return_check;
pub mod semantic_return_local_address;
pub mod semantic_scope_invariants;
pub mod semantic_shift_float;
pub mod semantic_static_assert;
pub mod semantic_enum_types;
