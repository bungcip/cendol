use crate::ast::NameId;
use crate::diagnostic::{DiagDisplay, DiagFormatter, Diagnostic, DiagnosticLevel, format_diag};
use crate::semantic::{QualType, TypeRef, TypeRegistry};
use crate::source_manager::SourceSpan;
use std::fmt::Write;

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
            | SemanticError::EnumeratorValueNotRepresentable { target_ty: None, .. }
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
            message: format_diag(registry, &self.kind),
            span: self.span,
            warning_name: self.kind.warning_name(),
            ..Default::default()
        }];

        if let Some((message, span)) = match &self.kind {
            SemanticError::Redefinition { first_def, .. }
            | SemanticError::RedefinitionWithDifferentType { first_def, .. } => {
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
                message: format_diag(registry, &note_kind),
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
    VoidReturnWithVoidExpr {
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
    ExcessElements {
        kind: &'static str,
    },
    UnsupportedFeature {
        feature: &'static str,
    },
    CleanupNotAFunction,
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
        target_ty: Option<QualType>,
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
    VmStaticStorage,
    VmThreadStorage,
    VmHasLinkage,
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
    AttributeCleanupOnType,
    AttributeCleanupOnNonLocal,
}

impl SemanticError {
    pub(crate) fn is_pedantic(&self) -> bool {
        matches!(
            self,
            SemanticError::EnumForwardDeclaration
                | SemanticError::AlignOfExpression
                | SemanticError::GnuStatementExpression
                | SemanticError::GnuTypeof
                | SemanticError::GnuDesignatedInitializerRange
                | SemanticError::GnuCaseRange
                | SemanticError::GnuZeroLengthArray
                | SemanticError::ExcessElements { .. }
                | SemanticError::VoidReturnWithVoidExpr { .. }
        )
    }

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
            SemanticError::ExcessElements { .. } => Some("excess-initializers"),
            SemanticError::AlignOfExpression => Some("gnu-alignof-expression"),
            SemanticError::GnuStatementExpression => Some("gnu-statement-expression"),
            SemanticError::GnuTypeof => Some("gnu-typeof-expression"),
            SemanticError::GnuDesignatedInitializerRange => Some("gnu-designated-init"),
            SemanticError::GnuCaseRange => Some("gnu-case-range"),
            SemanticError::GnuZeroLengthArray => Some("gnu-zero-length-array"),
            SemanticError::InlineAsmIgnored => Some("inline-asm"),
            SemanticError::AttributeCleanupOnType => Some("attributes"),
            SemanticError::AttributeCleanupOnNonLocal => Some("ignored-attributes"),
            SemanticError::VoidReturnWithVoidExpr { .. } => Some("pedantic"),
            _ => None,
        }
    }
}

impl DiagDisplay for SemanticError {
    fn fmt(&self, f: &mut DiagFormatter<'_>) -> std::fmt::Result {
        match self {
            SemanticError::VariableOfVoidType => write!(f, "variable has incomplete type 'void'"),
            SemanticError::CalledNonFunctionType { ty } => write!(
                f,
                "called object type '{}' is not a function or function pointer",
                f.display_qual_type(*ty)
            ),
            SemanticError::UndeclaredIdentifier { name } => {
                write!(f, "Undeclared identifier '{}'", name)
            }
            SemanticError::Redefinition { name, .. } => write!(f, "redefinition of '{}'", name),
            SemanticError::RedefinitionWithDifferentType { name, .. } => {
                write!(f, "redefinition of '{}' with a different type", name)
            }
            SemanticError::TypeMismatch { expected, found } => write!(
                f,
                "type mismatch: expected {}, found {}",
                f.display_qual_type(*expected),
                f.display_qual_type(*found)
            ),
            SemanticError::NotAnLvalue => write!(f, "Expression is not assignable (not an lvalue)"),
            SemanticError::InvalidBinaryOperands { left_ty, right_ty } => write!(
                f,
                "Invalid operands for binary operation: have '{}' and '{}'",
                f.display_qual_type(*left_ty),
                f.display_qual_type(*right_ty)
            ),
            SemanticError::InvalidUnaryOperand { ty } => {
                write!(
                    f,
                    "Invalid operand for unary operation: have '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::IndirectionRequiresPointer { ty } => write!(
                f,
                "indirection requires pointer operand ('{}' invalid)",
                f.display_qual_type(*ty)
            ),
            SemanticError::NonConstantInitializer => write!(f, "Initializer element is not a compile-time constant"),
            SemanticError::InvalidInitializer => write!(f, "invalid initializer"),
            SemanticError::ConflictingTypes { name, .. } => write!(f, "conflicting types for '{}'", name),
            SemanticError::VoidReturnWithValue { name } => {
                write!(f, "void function '{}' should not return a value", name)
            }
            SemanticError::VoidReturnWithVoidExpr { name } => {
                write!(f, "void function '{}' should not return a value", name)
            }
            SemanticError::NonVoidReturnWithoutValue { name } => {
                write!(f, "non-void function '{}' should return a value", name)
            }
            SemanticError::EmptyDeclaration => write!(f, "declaration does not declare anything"),
            SemanticError::InvalidNumberOfArguments { expected, found } => {
                write!(f, "invalid number of arguments: expected {}, found {}", expected, found)
            }
            SemanticError::ExcessElements { kind } => write!(f, "excess elements in {} initializer", kind),
            SemanticError::UnsupportedFeature { feature } => write!(f, "Unsupported feature: {}", feature),
            SemanticError::CleanupNotAFunction => write!(f, "cleanup argument not a function"),
            SemanticError::InvalidArraySize => write!(f, "size of array is negative"),
            SemanticError::ZeroOrNegativeSizeArray { name } => {
                write!(f, "zero or negative size array '{}'", name)
            }
            SemanticError::ArraySizeNotInteger => write!(f, "size of array has non-integer type"),
            SemanticError::InvalidBitfieldWidth => write!(f, "invalid bit-field width"),
            SemanticError::NonConstantBitfieldWidth => write!(f, "bit-field width is not a constant expression"),
            SemanticError::BitfieldWidthExceedsType { width, type_width } => write!(
                f,
                "width of bit-field ({} bits) exceeds width of its type ({} bits)",
                width, type_width
            ),
            SemanticError::NamedZeroWidthBitfield => write!(f, "zero-width bit-field shall not specify a declarator"),
            SemanticError::InvalidBitfieldType { ty } => {
                write!(f, "bit-field type '{}' is invalid", f.display_qual_type(*ty))
            }
            SemanticError::BitfieldHasAtomicType => write!(f, "bit-field shall not have an atomic type"),
            SemanticError::ConflictingStorageClasses => write!(f, "conflicting storage class specifiers"),
            SemanticError::ConflictingLinkage { name, .. } => {
                write!(f, "conflicting linkage for '{}'", name)
            }
            SemanticError::ConflictingTypeSpec { prev } => {
                write!(
                    f,
                    "cannot combine with previous '{}' declaration specifier",
                    f.display_qual_type(*prev)
                )
            }
            SemanticError::InvalidFunctionSpec { spec } => {
                write!(f, "'{}' function specifier appears on non-function declaration", spec)
            }
            SemanticError::DuplicateMember { name, .. } => write!(f, "duplicate member '{}'", name),
            SemanticError::MemberAccessOnNonRecord { ty } => write!(
                f,
                "member reference base type '{}' is not a structure or union",
                f.display_qual_type(*ty)
            ),
            SemanticError::MemberHasFunctionType { name } => {
                write!(f, "member '{}' has function type", name)
            }
            SemanticError::FunctionReturningArray => write!(f, "function cannot return an array type"),
            SemanticError::FunctionReturningFunction => write!(f, "function cannot return a function type"),
            SemanticError::MemberNotFound { name, ty } => {
                write!(f, "no member named '{}' in '{}'", name, f.display_qual_type(*ty))
            }
            SemanticError::ExpectedTypedefName { found } => {
                write!(f, "expected a typedef name, found {}", found)
            }
            SemanticError::MissingTypeSpec => write!(f, "missing type specifier in declaration"),
            SemanticError::StaticAssertFailed { message } => {
                write!(f, "static assertion failed: {}", message)
            }
            SemanticError::StaticAssertNotConstant => write!(f, "expression in static assertion is not constant"),
            SemanticError::RecursiveType { ty } => {
                write!(f, "recursive type definition: {}", f.display_type(*ty))
            }
            SemanticError::SizeOfIncompleteType { ty } => {
                write!(
                    f,
                    "Invalid application of 'sizeof' to an incomplete type '{}'",
                    f.display_type(*ty)
                )
            }
            SemanticError::SizeOfFunctionType => write!(f, "Invalid application of 'sizeof' to a function type"),
            SemanticError::AlignOfIncompleteType { ty } => {
                write!(
                    f,
                    "Invalid application of '_Alignof' to an incomplete type '{}'",
                    f.display_type(*ty)
                )
            }
            SemanticError::AlignOfFunctionType => write!(f, "Invalid application of '_Alignof' to a function type"),
            SemanticError::GenericNoMatch { ty } => write!(
                f,
                "controlling expression type '{}' not compatible with any generic association",
                f.display_qual_type(*ty)
            ),
            SemanticError::GenericFunctionAssociation { ty } => {
                write!(
                    f,
                    "generic association specifies function type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::GenericVlaAssociation { ty } => {
                write!(
                    f,
                    "generic association specifies variably modified type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::AddressOfBitfield => write!(f, "cannot take address of bit-field"),
            SemanticError::AddressOfRegister => write!(f, "cannot take address of 'register' variable"),
            SemanticError::SizeOfBitfield => write!(f, "cannot apply 'sizeof' to a bit-field"),
            SemanticError::AlignOfBitfield => write!(f, "cannot apply '_Alignof' to a bit-field"),
            SemanticError::GenericIncompleteControl { ty } => {
                write!(
                    f,
                    "controlling expression type '{}' is an incomplete type",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::GenericIncompleteAssociation { ty } => {
                write!(
                    f,
                    "generic association specifies incomplete type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::GenericMultipleDefault { .. } => {
                write!(f, "duplicate default association in generic selection")
            }
            SemanticError::GenericMultipleMatches { .. } => {
                write!(
                    f,
                    "controlling expression in '_Generic' selector matches multiple associations"
                )
            }
            SemanticError::GenericDuplicateMatch { ty, prev_ty, .. } => write!(
                f,
                "type '{}' in generic association compatible with previously specified type '{}'",
                f.display_qual_type(*ty),
                f.display_qual_type(*prev_ty)
            ),
            SemanticError::InvalidAlignment { value } => {
                write!(f, "requested alignment is not a positive power of 2: {}", value)
            }
            SemanticError::NonConstantAlignment => write!(f, "requested alignment is not a constant expression"),
            SemanticError::AssignmentToReadOnly => write!(f, "cannot assign to read-only location"),
            SemanticError::IncompleteType { ty } => {
                write!(f, "incomplete type '{}'", f.display_qual_type(*ty))
            }
            SemanticError::IncompleteReturnType => write!(f, "function has incomplete return type"),
            SemanticError::EnumForwardDeclaration => write!(f, "ISO C forbids forward references to 'enum' types"),
            SemanticError::IncompatiblePointerComparison { lhs, rhs } => write!(
                f,
                "comparison of incompatible pointer types '{}' and '{}'",
                f.display_qual_type(*lhs),
                f.display_qual_type(*rhs)
            ),
            SemanticError::IncompatiblePointerTypes { expected, found } => write!(
                f,
                "incompatible pointer types passing '{}' to parameter of type '{}'",
                f.display_qual_type(*found),
                f.display_qual_type(*expected)
            ),
            SemanticError::PointerSignednessMismatch { expected, found } => write!(
                f,
                "pointer targets in assignment differ in signedness (passing '{}' to '{}')",
                f.display_qual_type(*found),
                f.display_qual_type(*expected)
            ),
            SemanticError::PointerAssignmentDiscardsQualifiers { expected, found } => write!(
                f,
                "assignment discards qualifiers from pointer target type (passing '{}' to '{}')",
                f.display_qual_type(*found),
                f.display_qual_type(*expected)
            ),
            SemanticError::CaseNotInSwitch => write!(f, "'case' or 'default' label not in switch statement"),
            SemanticError::DuplicateCase { value } => write!(f, "duplicate case value '{}'", value),
            SemanticError::NonConstantCaseValue => {
                write!(f, "expression in 'case' label is not an integer constant expression")
            }
            SemanticError::InvalidSwitchCondition { ty } => {
                write!(
                    f,
                    "switch condition has non-integer type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::ExpectedScalarType { found } => {
                write!(
                    f,
                    "type mismatch: expected scalar type, found {}",
                    f.display_qual_type(*found)
                )
            }
            SemanticError::ExpectedFloatingType { found } => {
                write!(
                    f,
                    "type mismatch: expected floating-point type, found {}",
                    f.display_qual_type(*found)
                )
            }
            SemanticError::ExpectedIntegerType { found } => {
                write!(
                    f,
                    "type mismatch: expected integer type, found {}",
                    f.display_qual_type(*found)
                )
            }
            SemanticError::BuiltinChooseExprNotConstant => {
                write!(f, "condition in '__builtin_choose_expr' is not a constant expression")
            }
            SemanticError::ThreadLocalNotAllowed => write!(f, "_Thread_local is not allowed here"),
            SemanticError::ThreadLocalBlockScopeRequiresStaticOrExtern => {
                write!(
                    f,
                    "_Thread_local in block scope must be combined with 'static' or 'extern'"
                )
            }
            SemanticError::MultipleDefaultLabels => write!(f, "multiple default labels in one switch"),
            SemanticError::FlexibleArrayNotLast => {
                write!(f, "flexible array member must be the last member of a structure")
            }
            SemanticError::FlexibleArrayInEmptyStruct => {
                write!(f, "flexible array member in otherwise empty structure")
            }
            SemanticError::FlexibleArrayMemberInStruct => {
                write!(f, "invalid use of structure with flexible array member as a member")
            }
            SemanticError::FlexibleArrayElementInArray => {
                write!(
                    f,
                    "invalid use of structure with flexible array member as an array element"
                )
            }
            SemanticError::InvalidRestrict => write!(f, "restrict requires a pointer type"),
            SemanticError::InvalidStorageClassForParameter => {
                write!(f, "invalid storage class for function parameter")
            }
            SemanticError::NoreturnFunctionHasReturn { name } => {
                write!(
                    f,
                    "function '{}' declared '_Noreturn' contains a return statement",
                    name
                )
            }
            SemanticError::NoreturnFunctionFallsOff { name } => {
                write!(f, "function '{}' declared '_Noreturn' can fall off the end", name)
            }
            SemanticError::AlignmentNotAllowed { context } => {
                write!(f, "alignment specifier cannot be used in a {}", context)
            }
            SemanticError::AlignmentTooLoose { requested, natural } => write!(
                f,
                "alignment specifier specifies {}-byte alignment, but {}-byte alignment is required",
                requested, natural
            ),
            SemanticError::CompoundLiteralIncomplete { ty } => {
                write!(
                    f,
                    "compound literal specifies incomplete type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::CompoundLiteralVla { ty } => {
                write!(
                    f,
                    "compound literal specifies variably modified type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::CompoundLiteralFunction { ty } => {
                write!(
                    f,
                    "compound literal specifies function type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::AlignasOnVla => write!(f, "alignment specifier cannot be used in a variably modified type"),
            SemanticError::InvalidAtomicQualifier { type_kind } => {
                write!(f, "_Atomic qualifier cannot be used with {} type", type_kind)
            }
            SemanticError::InvalidAtomicSpec { reason } => {
                write!(f, "_Atomic(type-name) specifier cannot be used with {}", reason)
            }
            SemanticError::ArrayStaticOutsideParameter => {
                write!(f, "static in array declarator only allowed in function parameters")
            }
            SemanticError::ArrayQualifierOutsideParameter => {
                write!(
                    f,
                    "type qualifiers in array declarator only allowed in function parameters"
                )
            }
            SemanticError::ArrayStaticNotOutermost => {
                write!(f, "static in array declarator only allowed in outermost array type")
            }
            SemanticError::ArrayQualifierNotOutermost => {
                write!(
                    f,
                    "type qualifiers in array declarator only allowed in outermost array type"
                )
            }
            SemanticError::BreakNotInLoop => write!(f, "break statement not in loop or switch"),
            SemanticError::ContinueNotInLoop => write!(f, "continue statement not in loop statement"),
            SemanticError::ExpectedArrayType { found } => {
                write!(
                    f,
                    "subscripted value is not an array (have '{}')",
                    f.display_qual_type(*found)
                )
            }
            SemanticError::InvalidOffsetofDesignator => write!(f, "invalid designator in 'offsetof'"),
            SemanticError::ReturnLocalAddress { name } => {
                write!(
                    f,
                    "address of stack memory associated with local variable '{}' returned",
                    name
                )
            }
            SemanticError::ImplicitConstantConversion {
                from,
                to,
                from_val,
                to_val,
            } => write!(
                f,
                "implicit conversion from '{}' to '{}' changes value from {} to {}",
                f.display_qual_type(*from),
                f.display_qual_type(*to),
                from_val,
                to_val
            ),
            SemanticError::SwitchCaseOverflow { from_val, to_val } => write!(
                f,
                "overflow converting case value to switch condition type ({} to {})",
                from_val, to_val
            ),
            SemanticError::AddressOfArrayAlwaysTrue { name } => {
                write!(f, "address of array '{}' will always evaluate to 'true'", name)
            }
            SemanticError::EnumeratorValueNotRepresentable { name, value, target_ty } => write!(
                f,
                "enumerator value {} for '{}' is not representable as '{}'",
                value,
                name,
                f.display_qual_type(
                    target_ty
                        .unwrap_or_else(|| QualType::unqualified(f.registry.expect("TypeRegistry required").type_int))
                )
            ),
            SemanticError::FileScopeSpecifiesStorageClass { name, specifier } => {
                write!(f, "file-scope declaration of '{}' specifies '{}'", name, specifier)
            }

            SemanticError::JumpIntoScopeVLA { is_switch } => {
                if *is_switch {
                    write!(f, "switch jumps into scope of identifier with variably modified type")
                } else {
                    write!(f, "jump into scope of identifier with variably modified type")
                }
            }
            SemanticError::NoteLabelDefinedHere { name } => write!(f, "label '{}' defined here", name),
            SemanticError::NoteSwitchStartsHere => write!(f, "switch starts here"),
            SemanticError::NoteVLADeclaredHere { name } => write!(f, "'{}' declared here", name),
            SemanticError::InvalidStorageClassForFunction { name, specifier } => {
                write!(f, "invalid storage class '{}' for function '{}'", specifier, name)
            }
            SemanticError::VmStaticStorage => {
                write!(
                    f,
                    "object with static storage duration shall not have a variably modified type"
                )
            }
            SemanticError::VmThreadStorage => {
                write!(
                    f,
                    "object with thread storage duration shall not have a variably modified type"
                )
            }
            SemanticError::VmHasLinkage => write!(f, "identifier with variably modified type shall have no linkage"),
            SemanticError::VlaStarOutsidePrototype => {
                write!(f, "[*] array size only allowed in function prototype scope")
            }
            SemanticError::VlaInitializerNotAllowed => write!(f, "variable-length array may not be initialized"),
            SemanticError::InvalidEnumUnderlyingType { ty } => {
                write!(f, "invalid underlying type '{}' for enum", f.display_qual_type(*ty))
            }
            SemanticError::OffsetofBitfield => write!(f, "cannot apply 'offsetof' to a bit-field"),
            SemanticError::OffsetofIncompleteType { ty } => {
                write!(f, "offsetof of incomplete type '{}'", f.display_qual_type(*ty))
            }
            SemanticError::SubscriptIncompleteType { ty } => {
                write!(
                    f,
                    "subscript of pointer to incomplete type '{}'",
                    f.display_qual_type(*ty)
                )
            }
            SemanticError::AutoTypeRequiresInitializer => write!(f, "__auto_type requires an initializer"),
            SemanticError::ConstexprRequiresInitializer => {
                write!(f, "constexpr requires an initialized data declaration")
            }
            SemanticError::AutoTypeIncompatibleDeduction { first, new } => write!(
                f,
                "__auto_type deduced as '{}' for one declarator, but '{}' for another",
                f.display_qual_type(*first),
                f.display_qual_type(*new)
            ),
            SemanticError::AutoTypeNotAllowed { context } => {
                write!(f, "__auto_type is not allowed in {}", context)
            }
            SemanticError::BuiltinPrefetchNotConstant { arg } => {
                write!(f, "argument '{}' to '__builtin_prefetch' must be a constant", arg)
            }
            SemanticError::BuiltinPrefetchOutOfRange { arg } => {
                write!(f, "argument '{}' to '__builtin_prefetch' is out of range", arg)
            }
            SemanticError::AlignOfExpression => write!(f, "'_Alignof' applied to an expression is a GNU extension"),
            SemanticError::GnuStatementExpression => write!(f, "use of GNU statement expression extension"),
            SemanticError::GnuTypeof => write!(f, "use of GNU typeof extension"),
            SemanticError::GnuDesignatedInitializerRange => {
                write!(f, "use of GNU designated initializer range extension")
            }
            SemanticError::GnuCaseRange => write!(f, "use of GNU case range extension"),
            SemanticError::GnuZeroLengthArray => write!(f, "use of GNU zero-length array extension"),
            SemanticError::InlineAsmIgnored => write!(f, "inline assembly is currently ignored by cendol"),
            SemanticError::AttributeCleanupOnType => write!(f, "attribute '__cleanup__' ignored on type"),
            SemanticError::AttributeCleanupOnNonLocal => {
                write!(f, "'__cleanup__' attribute only applies to local variables")
            }
        }
    }
}
