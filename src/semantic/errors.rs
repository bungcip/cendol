use crate::ast::NameId;
use crate::diagnostic::{Diagnostic, DiagnosticLevel};
use crate::semantic::{QualType, TypeRef, TypeRegistry};
use crate::source_manager::SourceSpan;

#[derive(Debug, Clone)]
pub struct SemanticError {
    pub span: SourceSpan,
    pub kind: SemanticErrorKind,
    pub notes: Vec<(SourceSpan, SemanticErrorKind)>,
}

impl SemanticError {
    pub(crate) fn new(span: SourceSpan, kind: SemanticErrorKind) -> Self {
        Self {
            span,
            kind,
            notes: Vec::new(),
        }
    }

    pub(crate) fn into_diagnostic(self, registry: &TypeRegistry) -> Vec<Diagnostic> {
        let level = match &self.kind {
            SemanticErrorKind::EmptyDeclaration
            | SemanticErrorKind::IncompatiblePointerComparison { .. }
            | SemanticErrorKind::IncompatiblePointerTypes { .. }
            | SemanticErrorKind::PointerSignednessMismatch { .. }
            | SemanticErrorKind::PointerAssignmentDiscardsQualifiers { .. }
            | SemanticErrorKind::ReturnLocalAddress { .. }
            | SemanticErrorKind::ImplicitConstantConversion { .. }
            | SemanticErrorKind::SwitchCaseOverflow { .. }
            | SemanticErrorKind::AddressOfArrayAlwaysTrue { .. }
            | SemanticErrorKind::EnumeratorValueNotRepresentable { .. } => DiagnosticLevel::Warning,
            _ => DiagnosticLevel::Error,
        };

        let mut diagnostics = vec![Diagnostic {
            level,
            message: self.kind.display(registry),
            span: self.span,
            ..Default::default()
        }];

        if let Some((message, span)) = match &self.kind {
            SemanticErrorKind::Redefinition { first_def, .. }
            | SemanticErrorKind::RedefinitionWithDifferentType { first_def, .. } => {
                Some(("previous definition is here", *first_def))
            }
            SemanticErrorKind::GenericMultipleDefault { first_def, .. } => {
                Some(("previous default association is here", *first_def))
            }
            SemanticErrorKind::GenericDuplicateMatch { first_def, .. } => {
                Some(("previous association is here", *first_def))
            }
            SemanticErrorKind::ConflictingLinkage { first_def, .. }
            | SemanticErrorKind::DuplicateMember { first_def, .. }
            | SemanticErrorKind::ConflictingTypes { first_def, .. } => {
                Some(("previous declaration is here", *first_def))
            }
            _ => None,
        } {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Note,
                message: message.to_string(),
                span,
                ..Default::default()
            });
        }

        for (note_span, note_kind) in self.notes {
            diagnostics.push(Diagnostic {
                level: DiagnosticLevel::Note,
                message: note_kind.display(registry),
                span: note_span,
                ..Default::default()
            });
        }

        diagnostics
    }
}

/// Semantic errors
#[derive(Debug, Clone)]
pub enum SemanticErrorKind {
    VariableOfVoidType,
    CalledNonFunctionType {
        ty: QualType,
    },
    UndeclaredIdentifier {
        name: NameId,
    },
    Redefinition {
        name: NameId,
        first_def: SourceSpan,
    },
    RedefinitionWithDifferentType {
        name: NameId,
        first_def: SourceSpan,
    },
    TypeMismatch {
        expected: QualType,
        found: QualType,
    },
    NotAnLvalue,
    InvalidBinaryOperands {
        left_ty: QualType,
        right_ty: QualType,
    },
    InvalidUnaryOperand {
        ty: QualType,
    },
    IndirectionRequiresPointer {
        ty: QualType,
    },
    NonConstantInitializer,
    InvalidInitializer,
    ConflictingTypes {
        name: NameId,
        first_def: SourceSpan,
    },
    VoidReturnWithValue {
        name: NameId,
    },
    NonVoidReturnWithoutValue {
        name: NameId,
    },
    EmptyDeclaration,
    InvalidNumberOfArguments {
        expected: usize,
        found: usize,
    },
    InvalidAtomicArgument {
        ty: QualType,
    },
    ExcessElements {
        kind: &'static str,
    },
    UnsupportedFeature {
        feature: &'static str,
    },
    InvalidArraySize,
    ArraySizeNotInteger,
    InvalidBitfieldWidth,
    NonConstantBitfieldWidth,
    BitfieldWidthExceedsType {
        width: u16,
        type_width: u64,
    },
    NamedZeroWidthBitfield,
    InvalidBitfieldType {
        ty: QualType,
    },
    BitfieldHasAtomicType,
    ConflictingStorageClasses,
    ConflictingLinkage {
        name: NameId,
        first_def: SourceSpan,
    },
    ConflictingTypeSpec {
        prev: QualType,
    },
    InvalidFunctionSpec {
        spec: &'static str,
    },
    DuplicateMember {
        name: NameId,
        first_def: SourceSpan,
    },
    MemberAccessOnNonRecord {
        ty: QualType,
    },
    MemberHasFunctionType {
        name: NameId,
    },
    MemberNotFound {
        name: NameId,
        ty: QualType,
    },
    ExpectedTypedefName {
        found: NameId,
    },
    MissingTypeSpec,
    StaticAssertFailed {
        message: String,
    },
    StaticAssertNotConstant,
    RecursiveType {
        ty: TypeRef,
    },
    SizeOfIncompleteType {
        ty: TypeRef,
    },
    SizeOfFunctionType,
    AlignOfIncompleteType {
        ty: TypeRef,
    },
    AlignOfFunctionType,
    GenericNoMatch {
        ty: QualType,
    },
    GenericFunctionAssociation {
        ty: QualType,
    },
    GenericVlaAssociation {
        ty: QualType,
    },
    AddressOfBitfield,
    AddressOfRegister,
    SizeOfBitfield,
    GenericIncompleteControl {
        ty: QualType,
    },
    GenericIncompleteAssociation {
        ty: QualType,
    },
    GenericMultipleDefault {
        first_def: SourceSpan,
    },
    GenericDuplicateMatch {
        ty: QualType,
        prev_ty: QualType,
        first_def: SourceSpan,
    },
    InvalidAlignment {
        value: i64,
    },
    NonConstantAlignment,
    AssignmentToReadOnly,
    IncompleteType {
        ty: QualType,
    },
    IncompleteReturnType,
    IncompatiblePointerComparison {
        lhs: QualType,
        rhs: QualType,
    },
    IncompatiblePointerTypes {
        expected: QualType,
        found: QualType,
    },
    PointerSignednessMismatch {
        expected: QualType,
        found: QualType,
    },
    PointerAssignmentDiscardsQualifiers {
        expected: QualType,
        found: QualType,
    },
    CaseNotInSwitch,
    DuplicateCase {
        value: i64,
    },
    NonConstantCaseValue,
    InvalidSwitchCondition {
        ty: QualType,
    },
    ThreadLocalNotAllowed,
    ThreadLocalBlockScopeRequiresStaticOrExtern,
    MultipleDefaultLabels,
    FlexibleArrayNotLast,
    FlexibleArrayInEmptyStruct,
    InvalidRestrict,
    InvalidStorageClassForParameter,
    NoreturnFunctionHasReturn {
        name: NameId,
    },
    NoreturnFunctionFallsOff {
        name: NameId,
    },
    AlignmentNotAllowed {
        context: &'static str,
    },
    AlignmentTooLoose {
        requested: u32,
        natural: u32,
    },
    CompoundLiteralIncomplete {
        ty: QualType,
    },
    CompoundLiteralVla {
        ty: QualType,
    },
    CompoundLiteralFunction {
        ty: QualType,
    },
    InvalidAtomicQualifier {
        type_kind: &'static str,
    },
    InvalidAtomicSpec {
        reason: &'static str,
    },
    ArrayStaticOutsideParameter,
    ArrayQualifierOutsideParameter,
    ArrayStaticNotOutermost,
    ArrayQualifierNotOutermost,
    BreakNotInLoop,
    ContinueNotInLoop,
    ExpectedArrayType {
        found: QualType,
    },
    InvalidOffsetofDesignator,
    ReturnLocalAddress {
        name: NameId,
    },
    ImplicitConstantConversion {
        from: QualType,
        to: QualType,
        from_val: i64,
        to_val: i64,
    },
    SwitchCaseOverflow {
        from_val: i64,
        to_val: i64,
    },
    ExpectedScalarType {
        found: QualType,
    },
    ExpectedIntegerType {
        found: QualType,
    },
    BuiltinChooseExprNotConstant,
    AddressOfArrayAlwaysTrue {
        name: NameId,
    },
    EnumeratorValueNotRepresentable {
        name: NameId,
        value: i64,
    },
    FileScopeSpecifiesStorageClass {
        name: NameId,
        specifier: &'static str,
    },

    JumpIntoScopeVLA {
        is_switch: bool,
    },
    NoteLabelDefinedHere {
        name: NameId,
    },
    NoteSwitchStartsHere,
    NoteVLADeclaredHere {
        name: NameId,
    },
    InvalidStorageClassForFunction {
        name: NameId,
        specifier: &'static str,
    },
    VlaAtFileScope,
    VlaInitializerNotAllowed,
}

impl SemanticErrorKind {
    pub(crate) fn display(&self, registry: &TypeRegistry) -> String {
        match self {
            SemanticErrorKind::VariableOfVoidType => "variable has incomplete type 'void'".to_string(),
            SemanticErrorKind::CalledNonFunctionType { ty } => format!(
                "called object type '{}' is not a function or function pointer",
                registry.display_qual_type(*ty)
            ),
            SemanticErrorKind::UndeclaredIdentifier { name } => {
                format!("Undeclared identifier '{}'", name)
            }
            SemanticErrorKind::Redefinition { name, .. } => format!("redefinition of '{}'", name),
            SemanticErrorKind::RedefinitionWithDifferentType { name, .. } => {
                format!("redefinition of '{}' with a different type", name)
            }
            SemanticErrorKind::TypeMismatch { expected, found } => format!(
                "type mismatch: expected {}, found {}",
                registry.display_qual_type(*expected),
                registry.display_qual_type(*found)
            ),
            SemanticErrorKind::NotAnLvalue => "Expression is not assignable (not an lvalue)".to_string(),
            SemanticErrorKind::InvalidBinaryOperands { left_ty, right_ty } => format!(
                "Invalid operands for binary operation: have '{}' and '{}'",
                registry.display_qual_type(*left_ty),
                registry.display_qual_type(*right_ty)
            ),
            SemanticErrorKind::InvalidUnaryOperand { ty } => {
                format!(
                    "Invalid operand for unary operation: have '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::IndirectionRequiresPointer { ty } => format!(
                "indirection requires pointer operand ('{}' invalid)",
                registry.display_qual_type(*ty)
            ),
            SemanticErrorKind::NonConstantInitializer => {
                "Initializer element is not a compile-time constant".to_string()
            }
            SemanticErrorKind::InvalidInitializer => "invalid initializer".to_string(),
            SemanticErrorKind::ConflictingTypes { name, .. } => format!("conflicting types for '{}'", name),
            SemanticErrorKind::VoidReturnWithValue { name } => {
                format!("void function '{}' should not return a value", name)
            }
            SemanticErrorKind::NonVoidReturnWithoutValue { name } => {
                format!("non-void function '{}' should return a value", name)
            }
            SemanticErrorKind::EmptyDeclaration => "declaration does not declare anything".to_string(),
            SemanticErrorKind::InvalidNumberOfArguments { expected, found } => {
                format!("invalid number of arguments: expected {}, found {}", expected, found)
            }
            SemanticErrorKind::InvalidAtomicArgument { ty } => {
                format!(
                    "invalid argument type for atomic builtin: {}",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::ExcessElements { kind } => format!("excess elements in {} initializer", kind),
            SemanticErrorKind::UnsupportedFeature { feature } => format!("Unsupported feature: {}", feature),
            SemanticErrorKind::InvalidArraySize => "size of array is negative".to_string(),
            SemanticErrorKind::ArraySizeNotInteger => "size of array has non-integer type".to_string(),
            SemanticErrorKind::InvalidBitfieldWidth => "invalid bit-field width".to_string(),
            SemanticErrorKind::NonConstantBitfieldWidth => "bit-field width is not a constant expression".to_string(),
            SemanticErrorKind::BitfieldWidthExceedsType { width, type_width } => format!(
                "width of bit-field ({} bits) exceeds width of its type ({} bits)",
                width, type_width
            ),
            SemanticErrorKind::NamedZeroWidthBitfield => {
                "zero-width bit-field shall not specify a declarator".to_string()
            }
            SemanticErrorKind::InvalidBitfieldType { ty } => {
                format!("bit-field type '{}' is invalid", registry.display_qual_type(*ty))
            }
            SemanticErrorKind::BitfieldHasAtomicType => "bit-field shall not have an atomic type".to_string(),
            SemanticErrorKind::ConflictingStorageClasses => "conflicting storage class specifiers".to_string(),
            SemanticErrorKind::ConflictingLinkage { name, .. } => {
                format!("conflicting linkage for '{}'", name)
            }
            SemanticErrorKind::ConflictingTypeSpec { prev } => {
                format!(
                    "cannot combine with previous '{}' declaration specifier",
                    registry.display_qual_type(*prev)
                )
            }
            SemanticErrorKind::InvalidFunctionSpec { spec } => {
                format!("'{}' function specifier appears on non-function declaration", spec)
            }
            SemanticErrorKind::DuplicateMember { name, .. } => format!("duplicate member '{}'", name),
            SemanticErrorKind::MemberAccessOnNonRecord { ty } => format!(
                "member reference base type '{}' is not a structure or union",
                registry.display_qual_type(*ty)
            ),
            SemanticErrorKind::MemberHasFunctionType { name } => {
                format!("member '{}' has function type", name)
            }
            SemanticErrorKind::MemberNotFound { name, ty } => {
                format!("no member named '{}' in '{}'", name, registry.display_qual_type(*ty))
            }
            SemanticErrorKind::ExpectedTypedefName { found } => {
                format!("expected a typedef name, found {}", found)
            }
            SemanticErrorKind::MissingTypeSpec => "missing type specifier in declaration".to_string(),
            SemanticErrorKind::StaticAssertFailed { message } => {
                format!("static assertion failed: {}", message)
            }
            SemanticErrorKind::StaticAssertNotConstant => "expression in static assertion is not constant".to_string(),
            SemanticErrorKind::RecursiveType { ty } => {
                format!("recursive type definition: {}", registry.display_type(*ty))
            }
            SemanticErrorKind::SizeOfIncompleteType { ty } => {
                format!(
                    "Invalid application of 'sizeof' to an incomplete type '{}'",
                    registry.display_type(*ty)
                )
            }
            SemanticErrorKind::SizeOfFunctionType => "Invalid application of 'sizeof' to a function type".to_string(),
            SemanticErrorKind::AlignOfIncompleteType { ty } => {
                format!(
                    "Invalid application of '_Alignof' to an incomplete type '{}'",
                    registry.display_type(*ty)
                )
            }
            SemanticErrorKind::AlignOfFunctionType => {
                "Invalid application of '_Alignof' to a function type".to_string()
            }
            SemanticErrorKind::GenericNoMatch { ty } => format!(
                "controlling expression type '{}' not compatible with any generic association",
                registry.display_qual_type(*ty)
            ),
            SemanticErrorKind::GenericFunctionAssociation { ty } => {
                format!(
                    "generic association specifies function type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::GenericVlaAssociation { ty } => {
                format!(
                    "generic association specifies variably modified type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::AddressOfBitfield => "cannot take address of bit-field".to_string(),
            SemanticErrorKind::AddressOfRegister => "cannot take address of 'register' variable".to_string(),
            SemanticErrorKind::SizeOfBitfield => "cannot apply 'sizeof' to a bit-field".to_string(),
            SemanticErrorKind::GenericIncompleteControl { ty } => {
                format!(
                    "controlling expression type '{}' is an incomplete type",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::GenericIncompleteAssociation { ty } => {
                format!(
                    "generic association specifies incomplete type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::GenericMultipleDefault { .. } => {
                "duplicate default association in generic selection".to_string()
            }
            SemanticErrorKind::GenericDuplicateMatch { ty, prev_ty, .. } => format!(
                "type '{}' in generic association compatible with previously specified type '{}'",
                registry.display_qual_type(*ty),
                registry.display_qual_type(*prev_ty)
            ),
            SemanticErrorKind::InvalidAlignment { value } => {
                format!("requested alignment is not a positive power of 2: {}", value)
            }
            SemanticErrorKind::NonConstantAlignment => "requested alignment is not a constant expression".to_string(),
            SemanticErrorKind::AssignmentToReadOnly => "cannot assign to read-only location".to_string(),
            SemanticErrorKind::IncompleteType { ty } => {
                format!("incomplete type '{}'", registry.display_qual_type(*ty))
            }
            SemanticErrorKind::IncompleteReturnType => "function has incomplete return type".to_string(),
            SemanticErrorKind::IncompatiblePointerComparison { lhs, rhs } => format!(
                "comparison of incompatible pointer types '{}' and '{}'",
                registry.display_qual_type(*lhs),
                registry.display_qual_type(*rhs)
            ),
            SemanticErrorKind::IncompatiblePointerTypes { expected, found } => format!(
                "incompatible pointer types passing '{}' to parameter of type '{}'",
                registry.display_qual_type(*found),
                registry.display_qual_type(*expected)
            ),
            SemanticErrorKind::PointerSignednessMismatch { expected, found } => format!(
                "pointer targets in assignment differ in signedness (passing '{}' to '{}')",
                registry.display_qual_type(*found),
                registry.display_qual_type(*expected)
            ),
            SemanticErrorKind::PointerAssignmentDiscardsQualifiers { expected, found } => format!(
                "assignment discards qualifiers from pointer target type (passing '{}' to '{}')",
                registry.display_qual_type(*found),
                registry.display_qual_type(*expected)
            ),
            SemanticErrorKind::CaseNotInSwitch => "'case' or 'default' label not in switch statement".to_string(),
            SemanticErrorKind::DuplicateCase { value } => format!("duplicate case value '{}'", value),
            SemanticErrorKind::NonConstantCaseValue => {
                "expression in 'case' label is not an integer constant expression".to_string()
            }
            SemanticErrorKind::InvalidSwitchCondition { ty } => {
                format!(
                    "switch condition has non-integer type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::ExpectedScalarType { found } => {
                format!(
                    "type mismatch: expected scalar type, found {}",
                    registry.display_qual_type(*found)
                )
            }
            SemanticErrorKind::ExpectedIntegerType { found } => {
                format!(
                    "type mismatch: expected integer type, found {}",
                    registry.display_qual_type(*found)
                )
            }
            SemanticErrorKind::BuiltinChooseExprNotConstant => {
                "condition in '__builtin_choose_expr' is not a constant expression".to_string()
            }
            SemanticErrorKind::ThreadLocalNotAllowed => "_Thread_local is not allowed here".to_string(),
            SemanticErrorKind::ThreadLocalBlockScopeRequiresStaticOrExtern => {
                "_Thread_local in block scope must be combined with 'static' or 'extern'".to_string()
            }
            SemanticErrorKind::MultipleDefaultLabels => "multiple default labels in one switch".to_string(),
            SemanticErrorKind::FlexibleArrayNotLast => {
                "flexible array member must be the last member of a structure".to_string()
            }
            SemanticErrorKind::FlexibleArrayInEmptyStruct => {
                "flexible array member in otherwise empty structure".to_string()
            }
            SemanticErrorKind::InvalidRestrict => "restrict requires a pointer type".to_string(),
            SemanticErrorKind::InvalidStorageClassForParameter => {
                "invalid storage class for function parameter".to_string()
            }
            SemanticErrorKind::NoreturnFunctionHasReturn { name } => {
                format!("function '{}' declared '_Noreturn' contains a return statement", name)
            }
            SemanticErrorKind::NoreturnFunctionFallsOff { name } => {
                format!("function '{}' declared '_Noreturn' can fall off the end", name)
            }
            SemanticErrorKind::AlignmentNotAllowed { context } => {
                format!("alignment specifier cannot be used in a {}", context)
            }
            SemanticErrorKind::AlignmentTooLoose { requested, natural } => format!(
                "alignment specifier specifies {}-byte alignment, but {}-byte alignment is required",
                requested, natural
            ),
            SemanticErrorKind::CompoundLiteralIncomplete { ty } => {
                format!(
                    "compound literal specifies incomplete type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::CompoundLiteralVla { ty } => {
                format!(
                    "compound literal specifies variably modified type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::CompoundLiteralFunction { ty } => {
                format!(
                    "compound literal specifies function type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticErrorKind::InvalidAtomicQualifier { type_kind } => {
                format!("_Atomic qualifier cannot be used with {} type", type_kind)
            }
            SemanticErrorKind::InvalidAtomicSpec { reason } => {
                format!("_Atomic(type-name) specifier cannot be used with {}", reason)
            }
            SemanticErrorKind::ArrayStaticOutsideParameter => {
                "static in array declarator only allowed in function parameters".to_string()
            }
            SemanticErrorKind::ArrayQualifierOutsideParameter => {
                "type qualifiers in array declarator only allowed in function parameters".to_string()
            }
            SemanticErrorKind::ArrayStaticNotOutermost => {
                "static in array declarator only allowed in outermost array type".to_string()
            }
            SemanticErrorKind::ArrayQualifierNotOutermost => {
                "type qualifiers in array declarator only allowed in outermost array type".to_string()
            }
            SemanticErrorKind::BreakNotInLoop => "break statement not in loop or switch".to_string(),
            SemanticErrorKind::ContinueNotInLoop => "continue statement not in loop statement".to_string(),
            SemanticErrorKind::ExpectedArrayType { found } => {
                format!(
                    "subscripted value is not an array (have '{}')",
                    registry.display_qual_type(*found)
                )
            }
            SemanticErrorKind::InvalidOffsetofDesignator => "invalid designator in 'offsetof'".to_string(),
            SemanticErrorKind::ReturnLocalAddress { name } => {
                format!(
                    "address of stack memory associated with local variable '{}' returned",
                    name
                )
            }
            SemanticErrorKind::ImplicitConstantConversion {
                from,
                to,
                from_val,
                to_val,
            } => format!(
                "implicit conversion from '{}' to '{}' changes value from {} to {}",
                registry.display_qual_type(*from),
                registry.display_qual_type(*to),
                from_val,
                to_val
            ),
            SemanticErrorKind::SwitchCaseOverflow { from_val, to_val } => format!(
                "overflow converting case value to switch condition type ({} to {})",
                from_val, to_val
            ),
            SemanticErrorKind::AddressOfArrayAlwaysTrue { name } => {
                format!("address of array '{}' will always evaluate to 'true'", name)
            }
            SemanticErrorKind::EnumeratorValueNotRepresentable { name, value } => format!(
                "enumerator value {} for '{}' is not representable as 'int'",
                value, name
            ),
            SemanticErrorKind::FileScopeSpecifiesStorageClass { name, specifier } => {
                format!("file-scope declaration of '{}' specifies '{}'", name, specifier)
            }

            SemanticErrorKind::JumpIntoScopeVLA { is_switch } => {
                if *is_switch {
                    "switch jumps into scope of identifier with variably modified type".to_string()
                } else {
                    "jump into scope of identifier with variably modified type".to_string()
                }
            }
            SemanticErrorKind::NoteLabelDefinedHere { name } => format!("label '{}' defined here", name),
            SemanticErrorKind::NoteSwitchStartsHere => "switch starts here".to_string(),
            SemanticErrorKind::NoteVLADeclaredHere { name } => format!("'{}' declared here", name),
            SemanticErrorKind::InvalidStorageClassForFunction { name, specifier } => {
                format!("invalid storage class '{}' for function '{}'", specifier, name)
            }
            SemanticErrorKind::VlaAtFileScope => {
                "variable length array declaration not allowed at file scope".to_string()
            }
            SemanticErrorKind::VlaInitializerNotAllowed => "variable-length array may not be initialized".to_string(),
        }
    }
}
