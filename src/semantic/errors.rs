use crate::ast::{NameId, StringId};
use crate::diagnostic::{Diagnostic, DiagnosticLevel};
use crate::semantic::{QualType, TypeRef, TypeRegistry};
use crate::source_manager::SourceSpan;

#[derive(Debug, Clone)]
pub struct SemanticDiag {
    pub span: SourceSpan,
    pub kind: SemanticError,
    pub notes: Vec<(SourceSpan, SemanticError)>,
    pub level: Option<DiagnosticLevel>,
}

impl SemanticDiag {
    pub(crate) fn new(span: SourceSpan, kind: SemanticError) -> Self {
        Self {
            span,
            kind,
            notes: Vec::new(),
            level: None,
        }
    }

    pub(crate) fn into_diagnostic(self, registry: &TypeRegistry) -> Vec<Diagnostic> {
        let level = self.level.unwrap_or(match &self.kind {
            SemanticError::EmptyDeclaration
            | SemanticError::IncompatiblePointerComparison { .. }
            | SemanticError::IncompatiblePointerTypes { .. }
            | SemanticError::PointerSignednessMismatch { .. }
            | SemanticError::PointerAssignmentDiscardsQualifiers { .. }
            | SemanticError::ReturnLocalAddress { .. }
            | SemanticError::ImplicitConstantConversion { .. }
            | SemanticError::SwitchCaseOverflow { .. }
            | SemanticError::AddressOfArrayAlwaysTrue { .. }
            | SemanticError::EnumeratorValueNotRepresentable { .. }
            | SemanticError::AlignOfExpression
            | SemanticError::GnuStatementExpression
            | SemanticError::GnuTypeof
            | SemanticError::GnuDesignatedInitializerRange
            | SemanticError::GnuCaseRange
            | SemanticError::InlineAsmIgnored
            | SemanticError::ExcessElements { .. } => DiagnosticLevel::Warning,
            _ => DiagnosticLevel::Error,
        });

        let mut diagnostics = vec![Diagnostic {
            level,
            message: self.kind.display(registry),
            span: self.span,
            warning_name: self.kind.warning_name(),
            ..Default::default()
        }];

        if let Some((message, span)) = match &self.kind {
            SemanticError::Redefinition { first_def, .. }
            | SemanticError::RedefinitionWithDifferentType { first_def, .. }
            | SemanticError::MismatchedAlignment { first_def, .. }
            | SemanticError::MissingInitialAlignment { first_def, .. } => {
                Some(("previous definition is here", *first_def))
            }
            SemanticError::GenericMultipleDefault { first_def, .. } => {
                Some(("previous default association is here", *first_def))
            }
            SemanticError::GenericMultipleMatches { first_match, .. } => Some(("other match is here", *first_match)),
            SemanticError::GenericDuplicateMatch { first_def, .. } => {
                Some(("previous association is here", *first_def))
            }
            SemanticError::ConflictingLinkage { first_def, .. }
            | SemanticError::DuplicateMember { first_def, .. }
            | SemanticError::ConflictingTypes { first_def, .. } => Some(("previous declaration is here", *first_def)),
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
pub enum SemanticError {
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
    MismatchedAlignment {
        name: NameId,
        existing_align: u16,
        new_align: u16,
        first_def: SourceSpan,
    },
    MissingInitialAlignment {
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
    ZeroOrNegativeSizeArray {
        name: NameId,
    },
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
    FunctionReturningArray,
    FunctionReturningFunction,
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
    AlignOfBitfield,
    GenericIncompleteControl {
        ty: QualType,
    },
    GenericIncompleteAssociation {
        ty: QualType,
    },
    GenericMultipleDefault {
        first_def: SourceSpan,
    },
    GenericMultipleMatches {
        first_match: SourceSpan,
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
    EnumForwardDeclaration,
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
    FlexibleArrayMemberInStruct,
    FlexibleArrayElementInArray,
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
        requested: u64,
        natural: u64,
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
    AlignasOnVla,
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
    ExpectedFloatingType {
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
    EnumeratorValueFixedNotRepresentable {
        name: NameId,
        value: i64,
        target_ty: StringId,
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
    VlaStarOutsidePrototype,
    VlaInitializerNotAllowed,
    OffsetofBitfield,
    OffsetofIncompleteType {
        ty: QualType,
    },
    SubscriptIncompleteType {
        ty: QualType,
    },
    AutoTypeRequiresInitializer,
    ConstexprRequiresInitializer,
    AutoTypeIncompatibleDeduction {
        first: QualType,
        new: QualType,
    },
    AutoTypeNotAllowed {
        context: &'static str,
    },
    BuiltinPrefetchNotConstant {
        arg: &'static str,
    },
    BuiltinPrefetchOutOfRange {
        arg: &'static str,
    },
    AlignOfExpression,
    GnuStatementExpression,
    GnuTypeof,
    GnuDesignatedInitializerRange,
    GnuCaseRange,
    GnuZeroLengthArray,
    InlineAsmIgnored,
    InvalidEnumUnderlyingType {
        ty: QualType,
    },
}

impl SemanticError {
    pub(crate) fn warning_name(&self) -> Option<&'static str> {
        match self {
            SemanticError::EmptyDeclaration => Some("empty-translation-unit"),
            SemanticError::IncompatiblePointerComparison { .. } => Some("pointer-compare"),
            SemanticError::IncompatiblePointerTypes { .. } => Some("incompatible-pointer-types"),
            SemanticError::PointerSignednessMismatch { .. } => Some("pointer-sign"),
            SemanticError::PointerAssignmentDiscardsQualifiers { .. } => {
                Some("incompatible-pointer-types-discards-qualifiers")
            }
            SemanticError::ReturnLocalAddress { .. } => Some("return-stack-address"),
            SemanticError::ImplicitConstantConversion { .. } => Some("constant-conversion"),
            SemanticError::SwitchCaseOverflow { .. } => Some("switch"),
            SemanticError::AddressOfArrayAlwaysTrue { .. } => Some("tautological-pointer-compare"),
            SemanticError::EnumeratorValueNotRepresentable { .. } => Some("enum-conversion"),
            SemanticError::EnumeratorValueFixedNotRepresentable { .. } => None,
            SemanticError::ExcessElements { .. } => Some("excess-initializers"),
            SemanticError::AlignOfExpression => Some("gnu-alignof-expression"),
            SemanticError::GnuStatementExpression => Some("gnu-statement-expression"),
            SemanticError::GnuTypeof => Some("gnu-typeof-expression"),
            SemanticError::GnuDesignatedInitializerRange => Some("gnu-designated-init"),
            SemanticError::GnuCaseRange => Some("gnu-case-range"),
            SemanticError::GnuZeroLengthArray => Some("gnu-zero-length-array"),
            SemanticError::InlineAsmIgnored => Some("inline-asm"),
            _ => None,
        }
    }

    pub(crate) fn display(&self, registry: &TypeRegistry) -> String {
        match self {
            SemanticError::VariableOfVoidType => "variable has incomplete type 'void'".to_string(),
            SemanticError::CalledNonFunctionType { ty } => format!(
                "called object type '{}' is not a function or function pointer",
                registry.display_qual_type(*ty)
            ),
            SemanticError::UndeclaredIdentifier { name } => {
                format!("Undeclared identifier '{}'", name)
            }
            SemanticError::Redefinition { name, .. } => format!("redefinition of '{}'", name),
            SemanticError::RedefinitionWithDifferentType { name, .. } => {
                format!("redefinition of '{}' with a different type", name)
            }
            SemanticError::MismatchedAlignment {
                name,
                new_align,
                existing_align,
                ..
            } => format!(
                "alignment of '{}' ({}) does not match the first declaration ({})",
                name, new_align, existing_align
            ),
            SemanticError::MissingInitialAlignment { name, .. } => {
                format!("first declaration of '{}' does not specify an alignment", name)
            }
            SemanticError::TypeMismatch { expected, found } => format!(
                "type mismatch: expected {}, found {}",
                registry.display_qual_type(*expected),
                registry.display_qual_type(*found)
            ),
            SemanticError::NotAnLvalue => "Expression is not assignable (not an lvalue)".to_string(),
            SemanticError::InvalidBinaryOperands { left_ty, right_ty } => format!(
                "Invalid operands for binary operation: have '{}' and '{}'",
                registry.display_qual_type(*left_ty),
                registry.display_qual_type(*right_ty)
            ),
            SemanticError::InvalidUnaryOperand { ty } => {
                format!(
                    "Invalid operand for unary operation: have '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::IndirectionRequiresPointer { ty } => format!(
                "indirection requires pointer operand ('{}' invalid)",
                registry.display_qual_type(*ty)
            ),
            SemanticError::NonConstantInitializer => "Initializer element is not a compile-time constant".to_string(),
            SemanticError::InvalidInitializer => "invalid initializer".to_string(),
            SemanticError::ConflictingTypes { name, .. } => format!("conflicting types for '{}'", name),
            SemanticError::VoidReturnWithValue { name } => {
                format!("void function '{}' should not return a value", name)
            }
            SemanticError::NonVoidReturnWithoutValue { name } => {
                format!("non-void function '{}' should return a value", name)
            }
            SemanticError::EmptyDeclaration => "declaration does not declare anything".to_string(),
            SemanticError::InvalidNumberOfArguments { expected, found } => {
                format!("invalid number of arguments: expected {}, found {}", expected, found)
            }
            SemanticError::InvalidAtomicArgument { ty } => {
                format!(
                    "invalid argument type for atomic builtin: {}",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::ExcessElements { kind } => format!("excess elements in {} initializer", kind),
            SemanticError::UnsupportedFeature { feature } => format!("Unsupported feature: {}", feature),
            SemanticError::InvalidArraySize => "size of array is negative".to_string(),
            SemanticError::ZeroOrNegativeSizeArray { name } => {
                format!("zero or negative size array '{}'", name)
            }
            SemanticError::ArraySizeNotInteger => "size of array has non-integer type".to_string(),
            SemanticError::InvalidBitfieldWidth => "invalid bit-field width".to_string(),
            SemanticError::NonConstantBitfieldWidth => "bit-field width is not a constant expression".to_string(),
            SemanticError::BitfieldWidthExceedsType { width, type_width } => format!(
                "width of bit-field ({} bits) exceeds width of its type ({} bits)",
                width, type_width
            ),
            SemanticError::NamedZeroWidthBitfield => "zero-width bit-field shall not specify a declarator".to_string(),
            SemanticError::InvalidBitfieldType { ty } => {
                format!("bit-field type '{}' is invalid", registry.display_qual_type(*ty))
            }
            SemanticError::BitfieldHasAtomicType => "bit-field shall not have an atomic type".to_string(),
            SemanticError::ConflictingStorageClasses => "conflicting storage class specifiers".to_string(),
            SemanticError::ConflictingLinkage { name, .. } => {
                format!("conflicting linkage for '{}'", name)
            }
            SemanticError::ConflictingTypeSpec { prev } => {
                format!(
                    "cannot combine with previous '{}' declaration specifier",
                    registry.display_qual_type(*prev)
                )
            }
            SemanticError::InvalidFunctionSpec { spec } => {
                format!("'{}' function specifier appears on non-function declaration", spec)
            }
            SemanticError::DuplicateMember { name, .. } => format!("duplicate member '{}'", name),
            SemanticError::MemberAccessOnNonRecord { ty } => format!(
                "member reference base type '{}' is not a structure or union",
                registry.display_qual_type(*ty)
            ),
            SemanticError::MemberHasFunctionType { name } => {
                format!("member '{}' has function type", name)
            }
            SemanticError::FunctionReturningArray => "function cannot return an array type".to_string(),
            SemanticError::FunctionReturningFunction => "function cannot return a function type".to_string(),
            SemanticError::MemberNotFound { name, ty } => {
                format!("no member named '{}' in '{}'", name, registry.display_qual_type(*ty))
            }
            SemanticError::ExpectedTypedefName { found } => {
                format!("expected a typedef name, found {}", found)
            }
            SemanticError::MissingTypeSpec => "missing type specifier in declaration".to_string(),
            SemanticError::StaticAssertFailed { message } => {
                format!("static assertion failed: {}", message)
            }
            SemanticError::StaticAssertNotConstant => "expression in static assertion is not constant".to_string(),
            SemanticError::RecursiveType { ty } => {
                format!("recursive type definition: {}", registry.display_type(*ty))
            }
            SemanticError::SizeOfIncompleteType { ty } => {
                format!(
                    "Invalid application of 'sizeof' to an incomplete type '{}'",
                    registry.display_type(*ty)
                )
            }
            SemanticError::SizeOfFunctionType => "Invalid application of 'sizeof' to a function type".to_string(),
            SemanticError::AlignOfIncompleteType { ty } => {
                format!(
                    "Invalid application of '_Alignof' to an incomplete type '{}'",
                    registry.display_type(*ty)
                )
            }
            SemanticError::AlignOfFunctionType => "Invalid application of '_Alignof' to a function type".to_string(),
            SemanticError::GenericNoMatch { ty } => format!(
                "controlling expression type '{}' not compatible with any generic association",
                registry.display_qual_type(*ty)
            ),
            SemanticError::GenericFunctionAssociation { ty } => {
                format!(
                    "generic association specifies function type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::GenericVlaAssociation { ty } => {
                format!(
                    "generic association specifies variably modified type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::AddressOfBitfield => "cannot take address of bit-field".to_string(),
            SemanticError::AddressOfRegister => "cannot take address of 'register' variable".to_string(),
            SemanticError::SizeOfBitfield => "cannot apply 'sizeof' to a bit-field".to_string(),
            SemanticError::AlignOfBitfield => "cannot apply '_Alignof' to a bit-field".to_string(),
            SemanticError::GenericIncompleteControl { ty } => {
                format!(
                    "controlling expression type '{}' is an incomplete type",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::GenericIncompleteAssociation { ty } => {
                format!(
                    "generic association specifies incomplete type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::GenericMultipleDefault { .. } => {
                "duplicate default association in generic selection".to_string()
            }
            SemanticError::GenericMultipleMatches { .. } => {
                "controlling expression in '_Generic' selector matches multiple associations".to_string()
            }
            SemanticError::GenericDuplicateMatch { ty, prev_ty, .. } => format!(
                "type '{}' in generic association compatible with previously specified type '{}'",
                registry.display_qual_type(*ty),
                registry.display_qual_type(*prev_ty)
            ),
            SemanticError::InvalidAlignment { value } => {
                format!("requested alignment is not a positive power of 2: {}", value)
            }
            SemanticError::NonConstantAlignment => "requested alignment is not a constant expression".to_string(),
            SemanticError::AssignmentToReadOnly => "cannot assign to read-only location".to_string(),
            SemanticError::IncompleteType { ty } => {
                format!("incomplete type '{}'", registry.display_qual_type(*ty))
            }
            SemanticError::IncompleteReturnType => "function has incomplete return type".to_string(),
            SemanticError::EnumForwardDeclaration => "ISO C forbids forward references to 'enum' types".to_string(),
            SemanticError::IncompatiblePointerComparison { lhs, rhs } => format!(
                "comparison of incompatible pointer types '{}' and '{}'",
                registry.display_qual_type(*lhs),
                registry.display_qual_type(*rhs)
            ),
            SemanticError::IncompatiblePointerTypes { expected, found } => format!(
                "incompatible pointer types passing '{}' to parameter of type '{}'",
                registry.display_qual_type(*found),
                registry.display_qual_type(*expected)
            ),
            SemanticError::PointerSignednessMismatch { expected, found } => format!(
                "pointer targets in assignment differ in signedness (passing '{}' to '{}')",
                registry.display_qual_type(*found),
                registry.display_qual_type(*expected)
            ),
            SemanticError::PointerAssignmentDiscardsQualifiers { expected, found } => format!(
                "assignment discards qualifiers from pointer target type (passing '{}' to '{}')",
                registry.display_qual_type(*found),
                registry.display_qual_type(*expected)
            ),
            SemanticError::CaseNotInSwitch => "'case' or 'default' label not in switch statement".to_string(),
            SemanticError::DuplicateCase { value } => format!("duplicate case value '{}'", value),
            SemanticError::NonConstantCaseValue => {
                "expression in 'case' label is not an integer constant expression".to_string()
            }
            SemanticError::InvalidSwitchCondition { ty } => {
                format!(
                    "switch condition has non-integer type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::ExpectedScalarType { found } => {
                format!(
                    "type mismatch: expected scalar type, found {}",
                    registry.display_qual_type(*found)
                )
            }
            SemanticError::ExpectedFloatingType { found } => {
                format!(
                    "type mismatch: expected floating-point type, found {}",
                    registry.display_qual_type(*found)
                )
            }
            SemanticError::ExpectedIntegerType { found } => {
                format!(
                    "type mismatch: expected integer type, found {}",
                    registry.display_qual_type(*found)
                )
            }
            SemanticError::BuiltinChooseExprNotConstant => {
                "condition in '__builtin_choose_expr' is not a constant expression".to_string()
            }
            SemanticError::ThreadLocalNotAllowed => "_Thread_local is not allowed here".to_string(),
            SemanticError::ThreadLocalBlockScopeRequiresStaticOrExtern => {
                "_Thread_local in block scope must be combined with 'static' or 'extern'".to_string()
            }
            SemanticError::MultipleDefaultLabels => "multiple default labels in one switch".to_string(),
            SemanticError::FlexibleArrayNotLast => {
                "flexible array member must be the last member of a structure".to_string()
            }
            SemanticError::FlexibleArrayInEmptyStruct => {
                "flexible array member in otherwise empty structure".to_string()
            }
            SemanticError::FlexibleArrayMemberInStruct => {
                "invalid use of structure with flexible array member as a member".to_string()
            }
            SemanticError::FlexibleArrayElementInArray => {
                "invalid use of structure with flexible array member as an array element".to_string()
            }
            SemanticError::InvalidRestrict => "restrict requires a pointer type".to_string(),
            SemanticError::InvalidStorageClassForParameter => {
                "invalid storage class for function parameter".to_string()
            }
            SemanticError::NoreturnFunctionHasReturn { name } => {
                format!("function '{}' declared '_Noreturn' contains a return statement", name)
            }
            SemanticError::NoreturnFunctionFallsOff { name } => {
                format!("function '{}' declared '_Noreturn' can fall off the end", name)
            }
            SemanticError::AlignmentNotAllowed { context } => {
                format!("alignment specifier cannot be used in a {}", context)
            }
            SemanticError::AlignmentTooLoose { requested, natural } => format!(
                "alignment specifier specifies {}-byte alignment, but {}-byte alignment is required",
                requested, natural
            ),
            SemanticError::CompoundLiteralIncomplete { ty } => {
                format!(
                    "compound literal specifies incomplete type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::CompoundLiteralVla { ty } => {
                format!(
                    "compound literal specifies variably modified type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::CompoundLiteralFunction { ty } => {
                format!(
                    "compound literal specifies function type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::AlignasOnVla => "alignment specifier cannot be used in a variably modified type".to_string(),
            SemanticError::InvalidAtomicQualifier { type_kind } => {
                format!("_Atomic qualifier cannot be used with {} type", type_kind)
            }
            SemanticError::InvalidAtomicSpec { reason } => {
                format!("_Atomic(type-name) specifier cannot be used with {}", reason)
            }
            SemanticError::ArrayStaticOutsideParameter => {
                "static in array declarator only allowed in function parameters".to_string()
            }
            SemanticError::ArrayQualifierOutsideParameter => {
                "type qualifiers in array declarator only allowed in function parameters".to_string()
            }
            SemanticError::ArrayStaticNotOutermost => {
                "static in array declarator only allowed in outermost array type".to_string()
            }
            SemanticError::ArrayQualifierNotOutermost => {
                "type qualifiers in array declarator only allowed in outermost array type".to_string()
            }
            SemanticError::BreakNotInLoop => "break statement not in loop or switch".to_string(),
            SemanticError::ContinueNotInLoop => "continue statement not in loop statement".to_string(),
            SemanticError::ExpectedArrayType { found } => {
                format!(
                    "subscripted value is not an array (have '{}')",
                    registry.display_qual_type(*found)
                )
            }
            SemanticError::InvalidOffsetofDesignator => "invalid designator in 'offsetof'".to_string(),
            SemanticError::ReturnLocalAddress { name } => {
                format!(
                    "address of stack memory associated with local variable '{}' returned",
                    name
                )
            }
            SemanticError::ImplicitConstantConversion {
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
            SemanticError::SwitchCaseOverflow { from_val, to_val } => format!(
                "overflow converting case value to switch condition type ({} to {})",
                from_val, to_val
            ),
            SemanticError::AddressOfArrayAlwaysTrue { name } => {
                format!("address of array '{}' will always evaluate to 'true'", name)
            }
            SemanticError::EnumeratorValueNotRepresentable { name, value } => format!(
                "enumerator value {} for '{}' is not representable as 'int'",
                value, name
            ),
            SemanticError::EnumeratorValueFixedNotRepresentable { name, value, target_ty } => format!(
                "enumerator value {} for '{}' is not representable as '{}'",
                value, name, target_ty
            ),
            SemanticError::FileScopeSpecifiesStorageClass { name, specifier } => {
                format!("file-scope declaration of '{}' specifies '{}'", name, specifier)
            }

            SemanticError::JumpIntoScopeVLA { is_switch } => {
                if *is_switch {
                    "switch jumps into scope of identifier with variably modified type".to_string()
                } else {
                    "jump into scope of identifier with variably modified type".to_string()
                }
            }
            SemanticError::NoteLabelDefinedHere { name } => format!("label '{}' defined here", name),
            SemanticError::NoteSwitchStartsHere => "switch starts here".to_string(),
            SemanticError::NoteVLADeclaredHere { name } => format!("'{}' declared here", name),
            SemanticError::InvalidStorageClassForFunction { name, specifier } => {
                format!("invalid storage class '{}' for function '{}'", specifier, name)
            }
            SemanticError::VlaAtFileScope => "variable length array declaration not allowed at file scope".to_string(),
            SemanticError::VlaStarOutsidePrototype => {
                "[*] array size only allowed in function prototype scope".to_string()
            }
            SemanticError::VlaInitializerNotAllowed => "variable-length array may not be initialized".to_string(),
            SemanticError::InvalidEnumUnderlyingType { ty } => {
                format!("invalid underlying type '{}' for enum", registry.display_qual_type(*ty))
            }
            SemanticError::OffsetofBitfield => "cannot apply 'offsetof' to a bit-field".to_string(),
            SemanticError::OffsetofIncompleteType { ty } => {
                format!("offsetof of incomplete type '{}'", registry.display_qual_type(*ty))
            }
            SemanticError::SubscriptIncompleteType { ty } => {
                format!(
                    "subscript of pointer to incomplete type '{}'",
                    registry.display_qual_type(*ty)
                )
            }
            SemanticError::AutoTypeRequiresInitializer => "__auto_type requires an initializer".to_string(),
            SemanticError::ConstexprRequiresInitializer => {
                "constexpr requires an initialized data declaration".to_string()
            }
            SemanticError::AutoTypeIncompatibleDeduction { first, new } => format!(
                "__auto_type deduced as '{}' for one declarator, but '{}' for another",
                registry.display_qual_type(*first),
                registry.display_qual_type(*new)
            ),
            SemanticError::AutoTypeNotAllowed { context } => {
                format!("__auto_type is not allowed in {}", context)
            }
            SemanticError::BuiltinPrefetchNotConstant { arg } => {
                format!("argument '{}' to '__builtin_prefetch' must be a constant", arg)
            }
            SemanticError::BuiltinPrefetchOutOfRange { arg } => {
                format!("argument '{}' to '__builtin_prefetch' is out of range", arg)
            }
            SemanticError::AlignOfExpression => "'_Alignof' applied to an expression is a GNU extension".to_string(),
            SemanticError::GnuStatementExpression => "use of GNU statement expression extension".to_string(),
            SemanticError::GnuTypeof => "use of GNU typeof extension".to_string(),
            SemanticError::GnuDesignatedInitializerRange => {
                "use of GNU designated initializer range extension".to_string()
            }
            SemanticError::GnuCaseRange => "use of GNU case range extension".to_string(),
            SemanticError::GnuZeroLengthArray => "use of GNU zero-length array extension".to_string(),
            SemanticError::InlineAsmIgnored => "inline assembly is currently ignored by cendol".to_string(),
        }
    }
}
