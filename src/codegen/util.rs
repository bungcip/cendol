use crate::codegen::error::CodegenError;
use crate::semantic::typed_ast::{TypedExpr, TypedLValue};
use crate::parser::string_interner::StringId;
use cranelift_module::DataId;
use std::collections::HashMap;

use crate::types::TypeId;

/// Context needed for resolving addresses in static initializers
pub struct StaticInitContext<'a> {
    /// Mapping from variable names to their data IDs
    pub global_variables: HashMap<StringId, DataId>,
    pub structs: &'a HashMap<StringId, TypeId>,
    pub unions: &'a HashMap<StringId, TypeId>,
}

/// The result of evaluating a static initializer.
#[derive(Debug)]
pub enum EvaluatedInitializer {
    /// A sequence of bytes.
    Bytes(Vec<u8>),
    /// A relocation to a symbol.
    Reloc { name: StringId, addend: i64 },
}

/// Unescapes string literals by processing escape sequences
pub fn unescape_string(s: &str) -> Vec<u8> {
    let mut unescaped = Vec::with_capacity(s.len());
    let mut chars = s.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            if let Some(next) = chars.next() {
                match next {
                    'n' => unescaped.push(b'\n'),
                    't' => unescaped.push(b'\t'),
                    'r' => unescaped.push(b'\r'),
                    '\\' => unescaped.push(b'\\'),
                    '"' => unescaped.push(b'"'),
                    '\'' => unescaped.push(b'\''),
                    '0' => unescaped.push(b'\0'),
                    _ => {
                        unescaped.push(b'\\');
                        unescaped.push(next as u8);
                    }
                }
            } else {
                unescaped.push(b'\\');
            }
        } else {
            unescaped.push(c as u8);
        }
    }
    unescaped
}

use crate::semantic::typed_ast::TypedInitializer;

/// Evaluates a static initializer expression at compile time
use crate::codegen::translator::FunctionTranslator;
use crate::semantic::typed_ast::TypedDesignator;

pub fn evaluate_static_initializer(
    ty: TypeId,
    initializer: &TypedInitializer,
    context: &StaticInitContext,
) -> Result<EvaluatedInitializer, CodegenError> {
    match initializer {
        TypedInitializer::Expr(expr) => evaluate_static_expr(expr, context),
        TypedInitializer::List(initializers) => {
            let real_ty = crate::codegen::translator::FunctionTranslator::get_real_type_from_type_id(ty, context.structs, context.unions)?;
            let size =
                FunctionTranslator::get_type_size_from_type_id(ty, context.structs, context.unions)
                    as usize;
            let mut bytes = vec![0; size];
            let mut offset = 0;

            if let crate::types::TypeKind::Struct(_, members) = ty.kind() {
                let mut member_iter = members.iter();
                for (designators, init) in initializers {
                    let (member_offset, member_ty) = if !designators.is_empty() {
                        if let TypedDesignator::Member(name) = &designators[0] {
                            let mut current_offset = 0;
                            let mut found = false;
                            for member in &members {
                                let member_alignment =
                                    FunctionTranslator::get_type_alignment_from_type_id(
                                        member.ty,
                                        context.structs,
                                        context.unions,
                                    );
                                current_offset = (current_offset + member_alignment - 1)
                                    & !(member_alignment - 1);
                                if member.name == *name {
                                    found = true;
                                    break;
                                }
                                current_offset += FunctionTranslator::get_type_size_from_type_id(
                                    member.ty,
                                    context.structs,
                                    context.unions,
                                );
                            }
                            if found {
                                (
                                    current_offset,
                                    members.iter().find(|m| m.name == *name).unwrap().ty,
                                )
                            } else {
                                return Err(CodegenError::InvalidStaticInitializer);
                            }
                        } else {
                            return Err(CodegenError::InvalidStaticInitializer);
                        }
                    } else {
                        let member = member_iter.next().unwrap();
                        let member_alignment = FunctionTranslator::get_type_alignment_from_type_id(
                            member.ty,
                            context.structs,
                            context.unions,
                        );
                        offset = (offset + member_alignment - 1) & !(member_alignment - 1);
                        (offset, member.ty)
                    };

                    if let EvaluatedInitializer::Bytes(new_bytes) =
                        evaluate_static_initializer(member_ty, init, context)?
                    {
                        bytes[member_offset as usize..member_offset as usize + new_bytes.len()]
                            .copy_from_slice(&new_bytes);
                    } else {
                        return Err(CodegenError::InvalidStaticInitializer);
                    }

                    if designators.is_empty() {
                        offset += FunctionTranslator::get_type_size_from_type_id(
                            member_ty,
                            context.structs,
                            context.unions,
                        );
                    }
                }
            } else {
                for (_, init) in initializers {
                    if let EvaluatedInitializer::Bytes(mut new_bytes) =
                        evaluate_static_initializer(ty, init, context)?
                    {
                        bytes.append(&mut new_bytes);
                    } else {
                        return Err(CodegenError::InvalidStaticInitializer);
                    }
                }
            }
            Ok(EvaluatedInitializer::Bytes(bytes))
        }
    }
}

/// Evaluates a static initializer expression at compile time
pub fn evaluate_static_expr(
    expr: &TypedExpr,
    _context: &StaticInitContext,
) -> Result<EvaluatedInitializer, CodegenError> {
    match expr {
        // Handle numeric literals
        TypedExpr::Number(num, _, _) => Ok(EvaluatedInitializer::Bytes(num.to_le_bytes().to_vec())),
        TypedExpr::FloatNumber(num, _, _) => {
            Ok(EvaluatedInitializer::Bytes(num.to_le_bytes().to_vec()))
        }

        // Handle address-of expressions
        TypedExpr::AddressOf(lvalue, _, _) => match &**lvalue {
            TypedLValue::Variable(name, _, _) => Ok(EvaluatedInitializer::Reloc {
                name: *name,
                addend: 0,
            }),
            // Other lvalues like string literals will be handled separately.
            _ => Err(CodegenError::InvalidStaticInitializer),
        },

        // String literals are handled in `mod.rs`. Returning an error here to make it explicit.
        TypedExpr::String(_, _, _) => Err(CodegenError::InvalidStaticInitializer),

        // Other expressions are not supported as static initializers
        _ => Err(CodegenError::InvalidStaticInitializer),
    }
}
