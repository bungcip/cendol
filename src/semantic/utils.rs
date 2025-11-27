//! Shared utility functions for semantic analysis.

use crate::ast::*;

/// Extract function name and parameters from a declarator
pub fn extract_function_info(declarator: &Declarator) -> (Option<Symbol>, Vec<FunctionParameter>) {
    // Find the function declarator that has the identifier as its direct base
    let (name, params) = find_function_with_name(declarator);
    if let Some((func_decl, params)) = name.zip(params) {
        let func_params: Vec<FunctionParameter> = params
            .iter()
            .filter_map(|param| {
                if let Some(decl) = &param.declarator {
                    let param_name = extract_identifier(decl);
                    param_name.map(|name| FunctionParameter {
                        param_type: TypeRef::new(1).unwrap(), // Placeholder
                        name: Some(name),
                    })
                } else {
                    None
                }
            })
            .collect();
        (Some(func_decl), func_params)
    } else {
        (None, Vec::new())
    }
}

pub fn find_function_with_name(declarator: &Declarator) -> (Option<Symbol>, Option<&Vec<ParamData>>) {
    match declarator {
        Declarator::Function(base, params) => {
            if let Declarator::Identifier(name, _, _) = base.as_ref() {
                // Found it
                (Some(*name), Some(params))
            } else {
                // Recurse
                find_function_with_name(base)
            }
        }
        Declarator::Pointer(_, Some(base)) => find_function_with_name(base),
        Declarator::Array(base, _) => find_function_with_name(base),
        _ => (None, None)
    }
}

pub fn extract_identifier(declarator: &Declarator) -> Option<Symbol> {
    match declarator {
        Declarator::Identifier(name, _, _) => Some(*name),
        Declarator::Pointer(_, Some(base)) => extract_identifier(base),
        Declarator::Array(base, _) => extract_identifier(base),
        Declarator::Function(base, _) => extract_identifier(base),
        Declarator::Abstract => None,
        _ => None
    }
}