use std::fmt::Display;

use crate::SourceSpan;
use crate::parser::string_interner::StringId;
use thin_vec::ThinVec;

/// Type alias for initializer lists.
pub type InitializerList = ThinVec<(ThinVec<Designator>, Box<Initializer>)>;

/// Type alias for typed initializer lists.
pub type TypedInitializerList = ThinVec<(ThinVec<TypedDesignator>, Box<TypedInitializer>)>;

/// Represents a type in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    /// The `int` type.
    Int(SourceSpan),
    /// The `char` type.
    Char(SourceSpan),
    /// The `short` type.
    Short(SourceSpan),
    /// The `float` type.
    Float(SourceSpan),
    /// The `double` type.
    Double(SourceSpan),
    /// The `long` type.
    Long(SourceSpan),
    /// The `long long` type.
    LongLong(SourceSpan),
    /// The `unsigned int` type.
    UnsignedInt(SourceSpan),
    /// The `unsigned char` type.
    UnsignedChar(SourceSpan),
    /// The `unsigned short` type.
    UnsignedShort(SourceSpan),
    /// The `unsigned long` type.
    UnsignedLong(SourceSpan),
    /// The `unsigned long long` type.
    UnsignedLongLong(SourceSpan),
    /// The `void` type.
    Void(SourceSpan),
    /// The `_Bool` type.
    Bool(SourceSpan),
    /// A pointer to another type.
    Pointer(Box<Type>, SourceSpan),
    /// An array of a specific size.
    Array(Box<Type>, usize, SourceSpan),
    /// A struct definition.
    Struct(Option<StringId>, ThinVec<Parameter>, SourceSpan),
    /// A union definition.
    Union(Option<StringId>, ThinVec<Parameter>, SourceSpan),
    /// An enum definition.
    Enum(
        Option<StringId>,
        ThinVec<(StringId, Option<Box<Expr>>, SourceSpan)>,
        SourceSpan,
    ),
    Const(Box<Type>, SourceSpan),
    Volatile(Box<Type>, SourceSpan),
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Int(_) => write!(f, "int"),
            Type::Char(_) => write!(f, "char"),
            Type::Short(_) => write!(f, "short"),
            Type::Float(_) => write!(f, "float"),
            Type::Double(_) => write!(f, "double"),
            Type::Long(_) => write!(f, "long"),
            Type::LongLong(_) => write!(f, "long long"),
            Type::UnsignedInt(_) => write!(f, "unsigned int"),
            Type::UnsignedChar(_) => write!(f, "unsigned char"),
            Type::UnsignedShort(_) => write!(f, "unsigned short"),
            Type::UnsignedLong(_) => write!(f, "unsigned long"),
            Type::UnsignedLongLong(_) => write!(f, "unsigned long long"),
            Type::Void(_) => write!(f, "void"),
            Type::Bool(_) => write!(f, "_Bool"),
            Type::Pointer(inner, _) => {
                write!(f, "{}*", inner)
            }
            Type::Array(inner, size, _) => {
                write!(f, "{}[{}]", inner, size)
            }
            Type::Struct(name, _members, _) => {
                if let Some(name) = name {
                    write!(f, "struct {}", name)
                } else {
                    write!(f, "struct {{ /* anonymous */ }}")
                }
            }
            Type::Union(name, _members, _) => {
                if let Some(name) = name {
                    write!(f, "union {}", name)
                } else {
                    write!(f, "union {{ /* anonymous */ }}")
                }
            }
            Type::Enum(name, _variants, _) => {
                if let Some(name) = name {
                    write!(f, "enum {}", name)
                } else {
                    write!(f, "enum {{ /* anonymous */ }}")
                }
            }
            Type::Const(inner, _) => {
                write!(f, "const {}", inner)
            }
            Type::Volatile(inner, _) => {
                write!(f, "volatile {}", inner)
            }
        }
    }
}

impl Type {
    /// Returns `true` if the type is a pointer.
    pub fn is_pointer(&self) -> bool {
        match self {
            Type::Pointer(_, _) => true,
            Type::Const(ty, _) => ty.is_pointer(),
            Type::Volatile(ty, _) => ty.is_pointer(),
            _ => false,
        }
    }

    /// Returns `true` if the type is unsigned.
    pub fn is_unsigned(&self) -> bool {
        match self {
            Type::UnsignedInt(_)
            | Type::UnsignedChar(_)
            | Type::UnsignedShort(_)
            | Type::UnsignedLong(_)
            | Type::UnsignedLongLong(_) => true,
            Type::Const(ty, _) => ty.is_unsigned(),
            Type::Volatile(ty, _) => ty.is_unsigned(),
            _ => false,
        }
    }

    pub fn is_record(&self) -> bool {
        matches!(self, Type::Struct(..) | Type::Union(..))
    }

    pub fn is_array(&self) -> bool {
        matches!(self, Type::Array(..))
    }

    pub fn is_aggregate(&self) -> bool {
        matches!(self, Type::Struct(..) | Type::Union(..) | Type::Array(..))
    }

    /// Returns the rank of an integer type.
    pub fn get_integer_rank(&self) -> i32 {
        match self {
            Type::Bool(_) => 1,
            Type::Char(_) | Type::UnsignedChar(_) => 2,
            Type::Short(_) | Type::UnsignedShort(_) => 3,
            Type::Int(_) | Type::UnsignedInt(_) => 4,
            Type::Long(_) | Type::UnsignedLong(_) => 5,
            Type::LongLong(_) | Type::UnsignedLongLong(_) => 6,
            Type::Const(ty, _) => ty.get_integer_rank(),
            Type::Volatile(ty, _) => ty.get_integer_rank(),
            _ => 0,
        }
    }

    /// Returns `true` if the type is a floating-point type.
    pub fn is_floating(&self) -> bool {
        match self {
            Type::Float(_) | Type::Double(_) => true,
            Type::Const(ty, _) => ty.is_floating(),
            Type::Volatile(ty, _) => ty.is_floating(),
            _ => false,
        }
    }

    /// Returns `true` if the type is numeric.
    pub fn is_numeric(&self) -> bool {
        match self {
            Type::Int(_)
            | Type::Char(_)
            | Type::Short(_)
            | Type::Long(_)
            | Type::LongLong(_)
            | Type::Float(_)
            | Type::Double(_)
            | Type::Enum(_, _, _) => true,
            Type::Const(ty, _) => ty.is_numeric(),
            Type::Volatile(ty, _) => ty.is_numeric(),
            _ => false,
        }
    }

    /// Returns the arithmetic conversion rank for usual arithmetic conversions.
    pub fn get_arithmetic_rank(&self) -> i32 {
        match self {
            Type::Bool(_) => 1,
            Type::Char(_) | Type::UnsignedChar(_) => 2,
            Type::Short(_) | Type::UnsignedShort(_) => 3,
            Type::Int(_) | Type::UnsignedInt(_) => 4,
            Type::Long(_) | Type::UnsignedLong(_) => 5,
            Type::LongLong(_) | Type::UnsignedLongLong(_) => 6,
            Type::Float(_) => 7,
            Type::Double(_) => 8,
            Type::Const(ty, _) => ty.get_arithmetic_rank(),
            Type::Volatile(ty, _) => ty.get_arithmetic_rank(),
            _ => 0,
        }
    }

    /// Recursively unwraps `const` qualifiers from a type.
    pub fn unwrap_const(&self) -> &Type {
        match self {
            Type::Const(ty, _) => ty.unwrap_const(),
            _ => self,
        }
    }

    /// Recursively unwraps `volatile` qualifiers from a type.
    pub fn unwrap_volatile(&self) -> &Type {
        match self {
            Type::Volatile(ty, _) => ty.unwrap_volatile(),
            _ => self,
        }
    }

    pub fn equals_ignore_span(&self, other: &Type) -> bool {
        if std::mem::discriminant(self) != std::mem::discriminant(other) {
            return false;
        }
        match (self, other) {
            (Type::Pointer(a, _), Type::Pointer(b, _)) => a.equals_ignore_span(b),
            (Type::Array(a, s_a, _), Type::Array(b, s_b, _)) => {
                s_a == s_b && a.equals_ignore_span(b)
            }
            (Type::Const(a, _), Type::Const(b, _)) => a.equals_ignore_span(b),
            (Type::Volatile(a, _), Type::Volatile(b, _)) => a.equals_ignore_span(b),
            // For structs/unions, named types are nominally typed.
            // If they have a name, the names must match.
            (Type::Struct(n1, _, _), Type::Struct(n2, _, _)) if n1.is_some() && n2.is_some() => {
                n1 == n2
            }
            (Type::Union(n1, _, _), Type::Union(n2, _, _)) if n1.is_some() && n2.is_some() => {
                n1 == n2
            }
            // For other types that have no inner type, discriminant check is enough.
            _ => true,
        }
    }

    pub fn span(&self) -> SourceSpan {
        match self {
            Type::Int(span) => *span,
            Type::Char(span) => *span,
            Type::Short(span) => *span,
            Type::Float(span) => *span,
            Type::Double(span) => *span,
            Type::Long(span) => *span,
            Type::LongLong(span) => *span,
            Type::UnsignedInt(span) => *span,
            Type::UnsignedChar(span) => *span,
            Type::UnsignedShort(span) => *span,
            Type::UnsignedLong(span) => *span,
            Type::UnsignedLongLong(span) => *span,
            Type::Void(span) => *span,
            Type::Bool(span) => *span,
            Type::Pointer(_, span) => *span,
            Type::Array(_, _, span) => *span,
            Type::Struct(_, _, span) => *span,
            Type::Union(_, _, span) => *span,
            Type::Enum(_, _, span) => *span,
            Type::Const(_, span) => *span,
            Type::Volatile(_, span) => *span,
        }
    }
}

/// Represents the initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum ForInit {
    /// A variable declaration.
    Declaration(Type, StringId, Option<Initializer>),
    /// An expression.
    Expr(Expr),
}

/// Represents a declarator, which includes the type modifiers (pointers, arrays) and the identifier.
#[derive(Debug, PartialEq, Clone)]
pub struct Declarator {
    pub ty: Type,
    pub name: StringId,
    pub initializer: Option<Initializer>,
    pub span: SourceSpan,
}

/// Represents a statement in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum Stmt {
    /// A `return` statement.
    Return(Box<Expr>),
    /// An `if` statement.
    If(Box<Expr>, Box<Stmt>, Option<Box<Stmt>>),
    /// A `while` loop.
    While(Box<Expr>, Box<Stmt>),
    /// A `for` loop.
    For(
        Option<Box<ForInit>>,
        Option<Box<Expr>>,
        Option<Box<Expr>>,
        Box<Stmt>,
    ),
    /// A block of statements.
    Block(ThinVec<Stmt>),
    /// A `switch` statement.
    Switch(Box<Expr>, Box<Stmt>),
    /// A `case` statement.
    Case(Box<Expr>, Box<Stmt>),
    /// A `default` statement in a `switch`.
    Default(Box<Stmt>),
    /// A labeled statement.
    Label(StringId, Box<Stmt>, SourceSpan),
    /// A `goto` statement.
    Goto(StringId, SourceSpan),
    /// A variable declaration.
    Declaration(Box<Type>, ThinVec<Declarator>, bool),
    FunctionDeclaration {
        ty: Box<Type>,
        name: StringId,
        params: ThinVec<Parameter>,
        is_variadic: bool,
        is_inline: bool,
        is_noreturn: bool,
    },
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `do-while` loop.
    DoWhile(Box<Stmt>, Box<Expr>),
    /// An empty statement.
    Empty,
    /// An expression statement.
    Expr(Box<Expr>),
    /// A `_Static_assert` declaration.
    StaticAssert(Box<Expr>, StringId),
}

impl Stmt {
    pub fn span(&self) -> SourceSpan {
        match self {
            Stmt::Return(expr) => expr.span(),
            Stmt::If(cond, _, _) => cond.span(),
            Stmt::While(cond, _) => cond.span(),
            Stmt::For(init, _, _, _) => {
                if let Some(init) = init {
                    match &**init {
                        ForInit::Declaration(_, _, initializer) => {
                            if let Some(initializer) = initializer {
                                match initializer {
                                    Initializer::Expr(expr) => expr.span(),
                                    Initializer::List(_) => SourceSpan::default(),
                                }
                            } else {
                                SourceSpan::default()
                            }
                        }
                        ForInit::Expr(expr) => expr.span(),
                    }
                } else {
                    SourceSpan::default()
                }
            }
            Stmt::Block(stmts) => stmts.first().map_or(SourceSpan::default(), |s| s.span()),
            Stmt::Switch(expr, _) => expr.span(),
            Stmt::Case(expr, _) => expr.span(),
            Stmt::Default(body) => body.span(),
            Stmt::Label(_, _, span) => *span,
            Stmt::Goto(_, span) => *span,
            Stmt::Declaration(_, declarators, _) => declarators
                .first()
                .map_or(SourceSpan::default(), |d| d.span),
            Stmt::FunctionDeclaration { .. } => SourceSpan::default(),
            Stmt::Break => SourceSpan::default(),
            Stmt::Continue => SourceSpan::default(),
            Stmt::DoWhile(body, _) => body.span(),
            Stmt::Empty => SourceSpan::default(),
            Stmt::Expr(expr) => expr.span(),
            Stmt::StaticAssert(expr, _) => expr.span(),
        }
    }
}

/// Represents an expression in the C language.
#[derive(Debug, PartialEq, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Equal,
    NotEqual,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
    LeftShift,
    RightShift,
    LogicalAnd,
    LogicalOr,
    BitwiseOr,
    BitwiseXor,
    BitwiseAnd,
    Comma,
}

/// Represents assignment operators.
#[derive(Debug, PartialEq, Clone)]
pub enum AssignOp {
    Assign,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    LeftShift,
    RightShift,
    BitwiseAnd,
    BitwiseXor,
    BitwiseOr,
}

/// Represents logical operators.
#[derive(Debug, PartialEq, Clone)]
pub enum LogicalOp {
    And,
    Or,
}

impl LogicalOp {
    /// Converts a LogicalOp to the corresponding BinOp.
    pub fn to_binop(&self) -> BinOp {
        match self {
            LogicalOp::And => BinOp::LogicalAnd,
            LogicalOp::Or => BinOp::LogicalOr,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expr {
    /// A number literal.
    Number(i64, SourceSpan),
    /// A float number literal.
    FloatNumber(f64, SourceSpan),
    /// A string literal.
    String(StringId, SourceSpan),
    /// A character literal.
    Char(StringId, SourceSpan),
    /// A variable.
    Variable(StringId, SourceSpan),
    /// An assignment expression.
    Assign(Box<Expr>, Box<Expr>),
    /// A compound assignment expression (e.g., +=, -=, *=, /=, %=).
    AssignAdd(Box<Expr>, Box<Expr>),
    AssignSub(Box<Expr>, Box<Expr>),
    AssignMul(Box<Expr>, Box<Expr>),
    AssignDiv(Box<Expr>, Box<Expr>),
    AssignMod(Box<Expr>, Box<Expr>),
    AssignLeftShift(Box<Expr>, Box<Expr>),
    AssignRightShift(Box<Expr>, Box<Expr>),
    AssignBitwiseAnd(Box<Expr>, Box<Expr>),
    AssignBitwiseXor(Box<Expr>, Box<Expr>),
    AssignBitwiseOr(Box<Expr>, Box<Expr>),
    /// An addition expression.
    Add(Box<Expr>, Box<Expr>),
    /// A subtraction expression.
    Sub(Box<Expr>, Box<Expr>),
    /// A multiplication expression.
    Mul(Box<Expr>, Box<Expr>),
    /// A division expression.
    Div(Box<Expr>, Box<Expr>),
    /// A modulo expression.
    Mod(Box<Expr>, Box<Expr>),
    /// An equality comparison.
    Equal(Box<Expr>, Box<Expr>),
    /// An inequality comparison.
    NotEqual(Box<Expr>, Box<Expr>),
    /// A less-than comparison.
    LessThan(Box<Expr>, Box<Expr>),
    /// A greater-than comparison.
    GreaterThan(Box<Expr>, Box<Expr>),
    /// A less-than-or-equal-to comparison.
    LessThanOrEqual(Box<Expr>, Box<Expr>),
    /// A greater-than-or-equal-to comparison.
    GreaterThanOrEqual(Box<Expr>, Box<Expr>),
    /// A left shift expression.
    LeftShift(Box<Expr>, Box<Expr>),
    /// A right shift expression.
    RightShift(Box<Expr>, Box<Expr>),
    /// A function call.
    Call(StringId, ThinVec<Expr>, SourceSpan),
    /// A logical AND expression.
    LogicalAnd(Box<Expr>, Box<Expr>),
    /// A logical OR expression.
    LogicalOr(Box<Expr>, Box<Expr>),
    /// A bitwise OR expression.
    BitwiseOr(Box<Expr>, Box<Expr>),
    /// A bitwise XOR expression.
    BitwiseXor(Box<Expr>, Box<Expr>),
    /// A bitwise AND expression.
    BitwiseAnd(Box<Expr>, Box<Expr>),
    /// A logical NOT expression.
    LogicalNot(Box<Expr>),
    /// A dereference expression.
    Deref(Box<Expr>),
    /// An address-of expression.
    AddressOf(Box<Expr>),
    /// A negation expression.
    Neg(Box<Expr>),
    /// A bitwise NOT expression.
    BitwiseNot(Box<Expr>),
    /// A sizeof expression.
    Sizeof(Box<Expr>),
    /// A sizeof type expression.
    SizeofType(Type),
    /// An alignof expression.
    Alignof(Box<Expr>),
    /// An alignof type expression.
    AlignofType(Type),
    /// A pre-increment expression.
    PreIncrement(Box<Expr>),
    /// A pre-decrement expression.
    PreDecrement(Box<Expr>),
    /// A post-increment expression.
    PostIncrement(Box<Expr>),
    /// A post-decrement expression.
    PostDecrement(Box<Expr>),
    /// A ternary conditional expression.
    Ternary(Box<Expr>, Box<Expr>, Box<Expr>),
    /// An initializer list expression.
    InitializerList(InitializerList),
    /// A member access expression.
    Member(Box<Expr>, StringId),
    /// A pointer member access expression.
    PointerMember(Box<Expr>, StringId),
    /// An explicit type cast expression.
    ExplicitCast(Box<Type>, Box<Expr>),
    /// An implicit type cast expression.
    ImplicitCast(Box<Type>, Box<Expr>),
    /// A compound literal expression.
    CompoundLiteral(Box<Type>, Box<Initializer>),
    /// A comma expression.
    Comma(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn get_logical_expr(&self) -> Option<(LogicalOp, &Expr, &Expr)> {
        match self {
            Expr::LogicalAnd(lhs, rhs) => Some((LogicalOp::And, lhs, rhs)),
            Expr::LogicalOr(lhs, rhs) => Some((LogicalOp::Or, lhs, rhs)),
            _ => None,
        }
    }

    pub fn get_binary_expr(&self) -> Option<(BinOp, &Expr, &Expr)> {
        if let Some((logical_op, lhs, rhs)) = self.get_logical_expr() {
            Some((logical_op.to_binop(), lhs, rhs))
        } else {
            match self {
                Expr::Add(lhs, rhs) => Some((BinOp::Add, lhs, rhs)),
                Expr::Sub(lhs, rhs) => Some((BinOp::Sub, lhs, rhs)),
                Expr::Mul(lhs, rhs) => Some((BinOp::Mul, lhs, rhs)),
                Expr::Div(lhs, rhs) => Some((BinOp::Div, lhs, rhs)),
                Expr::Mod(lhs, rhs) => Some((BinOp::Mod, lhs, rhs)),
                Expr::Equal(lhs, rhs) => Some((BinOp::Equal, lhs, rhs)),
                Expr::NotEqual(lhs, rhs) => Some((BinOp::NotEqual, lhs, rhs)),
                Expr::LessThan(lhs, rhs) => Some((BinOp::LessThan, lhs, rhs)),
                Expr::GreaterThan(lhs, rhs) => Some((BinOp::GreaterThan, lhs, rhs)),
                Expr::LessThanOrEqual(lhs, rhs) => Some((BinOp::LessThanOrEqual, lhs, rhs)),
                Expr::GreaterThanOrEqual(lhs, rhs) => Some((BinOp::GreaterThanOrEqual, lhs, rhs)),
                Expr::LeftShift(lhs, rhs) => Some((BinOp::LeftShift, lhs, rhs)),
                Expr::RightShift(lhs, rhs) => Some((BinOp::RightShift, lhs, rhs)),
                Expr::BitwiseOr(lhs, rhs) => Some((BinOp::BitwiseOr, lhs, rhs)),
                Expr::BitwiseXor(lhs, rhs) => Some((BinOp::BitwiseXor, lhs, rhs)),
                Expr::BitwiseAnd(lhs, rhs) => Some((BinOp::BitwiseAnd, lhs, rhs)),
                Expr::Comma(lhs, rhs) => Some((BinOp::Comma, lhs, rhs)),
                _ => None,
            }
        }
    }

    pub fn get_assign_expr(&self) -> Option<(AssignOp, &Expr, &Expr)> {
        match self {
            Expr::Assign(lhs, rhs) => Some((AssignOp::Assign, lhs, rhs)),
            Expr::AssignAdd(lhs, rhs) => Some((AssignOp::Add, lhs, rhs)),
            Expr::AssignSub(lhs, rhs) => Some((AssignOp::Sub, lhs, rhs)),
            Expr::AssignMul(lhs, rhs) => Some((AssignOp::Mul, lhs, rhs)),
            Expr::AssignDiv(lhs, rhs) => Some((AssignOp::Div, lhs, rhs)),
            Expr::AssignMod(lhs, rhs) => Some((AssignOp::Mod, lhs, rhs)),
            Expr::AssignLeftShift(lhs, rhs) => Some((AssignOp::LeftShift, lhs, rhs)),
            Expr::AssignRightShift(lhs, rhs) => Some((AssignOp::RightShift, lhs, rhs)),
            Expr::AssignBitwiseAnd(lhs, rhs) => Some((AssignOp::BitwiseAnd, lhs, rhs)),
            Expr::AssignBitwiseXor(lhs, rhs) => Some((AssignOp::BitwiseXor, lhs, rhs)),
            Expr::AssignBitwiseOr(lhs, rhs) => Some((AssignOp::BitwiseOr, lhs, rhs)),
            _ => None,
        }
    }

    pub fn span(&self) -> SourceSpan {
        match self {
            Expr::Variable(_, span) => *span,
            Expr::Call(_, _, span) => *span,
            Expr::Assign(lhs, _)
            | Expr::AssignAdd(lhs, _)
            | Expr::AssignSub(lhs, _)
            | Expr::AssignMul(lhs, _)
            | Expr::AssignDiv(lhs, _)
            | Expr::AssignMod(lhs, _)
            | Expr::AssignLeftShift(lhs, _)
            | Expr::AssignRightShift(lhs, _)
            | Expr::AssignBitwiseAnd(lhs, _)
            | Expr::AssignBitwiseXor(lhs, _)
            | Expr::AssignBitwiseOr(lhs, _)
            | Expr::Add(lhs, _)
            | Expr::Sub(lhs, _)
            | Expr::Mul(lhs, _)
            | Expr::Div(lhs, _)
            | Expr::Mod(lhs, _)
            | Expr::Equal(lhs, _)
            | Expr::NotEqual(lhs, _)
            | Expr::LessThan(lhs, _)
            | Expr::GreaterThan(lhs, _)
            | Expr::LessThanOrEqual(lhs, _)
            | Expr::GreaterThanOrEqual(lhs, _)
            | Expr::LeftShift(lhs, _)
            | Expr::RightShift(lhs, _)
            | Expr::LogicalAnd(lhs, _)
            | Expr::LogicalOr(lhs, _)
            | Expr::BitwiseOr(lhs, _)
            | Expr::BitwiseXor(lhs, _)
            | Expr::BitwiseAnd(lhs, _)
            | Expr::Comma(lhs, _) => lhs.span(),
            Expr::LogicalNot(expr)
            | Expr::Deref(expr)
            | Expr::AddressOf(expr)
            | Expr::Neg(expr)
            | Expr::BitwiseNot(expr)
            | Expr::Sizeof(expr)
            | Expr::Alignof(expr)
            | Expr::PreIncrement(expr)
            | Expr::PreDecrement(expr)
            | Expr::PostIncrement(expr)
            | Expr::PostDecrement(expr) => expr.span(),
            Expr::Ternary(cond, _, _) => cond.span(),
            Expr::Member(expr, _) | Expr::PointerMember(expr, _) => expr.span(),
            Expr::ExplicitCast(_, expr) | Expr::ImplicitCast(_, expr) => expr.span(),
            // For literals and other complex types, a default span is returned for now.
            // A more robust solution would involve storing spans in all Expr variants.
            _ => SourceSpan::default(),
        }
    }
}

/// Represents a C designator for initializers.
#[derive(Debug, PartialEq, Clone)]
pub enum Designator {
    /// An array designator, e.g., `[0]`.
    Index(Box<Expr>),
    /// A struct/union member designator, e.g., `.foo`.
    Member(StringId),
}

/// Represents a C initializer.
#[derive(Debug, PartialEq, Clone)]
pub enum Initializer {
    /// A single expression initializer.
    Expr(Box<Expr>),
    /// An initializer list, e.g., `{ [0] = 1, .x = 2 }`.
    List(InitializerList),
}

/// Represents a function parameter.
#[derive(Debug, PartialEq, Clone)]
pub struct Parameter {
    /// The type of the parameter.
    pub ty: Type,
    /// The name of the parameter.
    pub name: StringId,
    /// The span of the parameter.
    pub span: SourceSpan,
}

/// Represents a function definition.
#[derive(Debug, PartialEq, Clone)]
pub struct Function {
    /// The return type of the function.
    pub return_type: Type,
    /// The name of the function.
    pub name: StringId,
    /// The parameters of the function.
    pub params: ThinVec<Parameter>,
    /// The body of the function.
    pub body: ThinVec<Stmt>,
    /// Whether the function is declared as inline.
    pub is_inline: bool,
    /// Whether the function is variadic.
    pub is_variadic: bool,
    /// Whether the function is declared as noreturn.
    pub is_noreturn: bool,
}

/// Represents a program.
#[derive(Debug, PartialEq, Clone)]
pub struct TranslationUnit {
    /// The global variables.
    pub globals: ThinVec<Stmt>,
    /// The functions in the program.
    pub functions: ThinVec<Function>,
}

/// Represents a typed expression with type information.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedExpr {
    Number(i64, SourceSpan, Type),
    FloatNumber(f64, SourceSpan, Type),
    String(StringId, SourceSpan, Type),
    Char(StringId, SourceSpan, Type),
    Variable(StringId, SourceSpan, Type),
    Call(StringId, ThinVec<TypedExpr>, SourceSpan, Type),
    Assign(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignAdd(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignSub(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignMul(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignDiv(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignMod(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignLeftShift(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignRightShift(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignBitwiseAnd(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignBitwiseXor(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    AssignBitwiseOr(Box<TypedLValue>, Box<TypedExpr>, SourceSpan, Type),
    Add(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Sub(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Mul(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Div(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Mod(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Equal(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    NotEqual(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    LessThan(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    GreaterThan(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    LessThanOrEqual(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    GreaterThanOrEqual(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    LogicalAnd(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    LogicalOr(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    BitwiseOr(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    BitwiseXor(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    BitwiseAnd(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    LeftShift(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    RightShift(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Comma(Box<TypedExpr>, Box<TypedExpr>, SourceSpan, Type),
    Neg(Box<TypedExpr>, SourceSpan, Type),
    LogicalNot(Box<TypedExpr>, SourceSpan, Type),
    BitwiseNot(Box<TypedExpr>, SourceSpan, Type),
    Sizeof(Box<TypedExpr>, SourceSpan, Type),
    Deref(Box<TypedExpr>, SourceSpan, Type),
    AddressOf(Box<TypedLValue>, SourceSpan, Type),
    SizeofType(Type, SourceSpan, Type),
    Alignof(Box<TypedExpr>, SourceSpan, Type),
    AlignofType(Type, SourceSpan, Type),
    Ternary(
        Box<TypedExpr>,
        Box<TypedExpr>,
        Box<TypedExpr>,
        SourceSpan,
        Type,
    ),
    Member(Box<TypedExpr>, StringId, SourceSpan, Type),
    PointerMember(Box<TypedExpr>, StringId, SourceSpan, Type),
    InitializerList(TypedInitializerList, SourceSpan, Type),
    ExplicitCast(Box<Type>, Box<TypedExpr>, SourceSpan, Type),
    ImplicitCast(Box<Type>, Box<TypedExpr>, SourceSpan, Type),
    CompoundLiteral(Box<Type>, Box<TypedInitializer>, SourceSpan, Type),
    PreIncrement(Box<TypedLValue>, SourceSpan, Type),
    PreDecrement(Box<TypedLValue>, SourceSpan, Type),
    PostIncrement(Box<TypedLValue>, SourceSpan, Type),
    PostDecrement(Box<TypedLValue>, SourceSpan, Type),
}

/// Represents a typed LValue expression with type information.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedLValue {
    /// A variable identifier.
    Variable(StringId, SourceSpan, Type),
    /// A dereference of a pointer expression.
    Deref(Box<TypedExpr>, SourceSpan, Type),
    /// A member access of a struct/union expression.
    Member(Box<TypedExpr>, StringId, SourceSpan, Type),
    /// A string literal.
    String(StringId, SourceSpan, Type),
}

impl TypedLValue {
    pub fn ty(&self) -> &Type {
        match self {
            TypedLValue::Variable(_, _, ty) => ty,
            TypedLValue::Deref(_, _, ty) => ty,
            TypedLValue::Member(_, _, _, ty) => ty,
            TypedLValue::String(_, _, ty) => ty,
        }
    }

    pub fn is_modifiable(&self) -> bool {
        matches!(self, TypedLValue::String(_, _, _)) == false
    }
}

impl TypedExpr {
    pub fn get_logical_expr(&self) -> Option<(LogicalOp, &TypedExpr, &TypedExpr)> {
        match self {
            TypedExpr::LogicalAnd(lhs, rhs, _, _) => Some((LogicalOp::And, lhs, rhs)),
            TypedExpr::LogicalOr(lhs, rhs, _, _) => Some((LogicalOp::Or, lhs, rhs)),
            _ => None,
        }
    }

    pub fn get_binary_expr(&self) -> Option<(BinOp, &TypedExpr, &TypedExpr)> {
        if let Some((logical_op, lhs, rhs)) = self.get_logical_expr() {
            Some((logical_op.to_binop(), lhs, rhs))
        } else {
            match self {
                TypedExpr::Add(lhs, rhs, _, _) => Some((BinOp::Add, lhs, rhs)),
                TypedExpr::Sub(lhs, rhs, _, _) => Some((BinOp::Sub, lhs, rhs)),
                TypedExpr::Mul(lhs, rhs, _, _) => Some((BinOp::Mul, lhs, rhs)),
                TypedExpr::Div(lhs, rhs, _, _) => Some((BinOp::Div, lhs, rhs)),
                TypedExpr::Mod(lhs, rhs, _, _) => Some((BinOp::Mod, lhs, rhs)),
                TypedExpr::Equal(lhs, rhs, _, _) => Some((BinOp::Equal, lhs, rhs)),
                TypedExpr::NotEqual(lhs, rhs, _, _) => Some((BinOp::NotEqual, lhs, rhs)),
                TypedExpr::LessThan(lhs, rhs, _, _) => Some((BinOp::LessThan, lhs, rhs)),
                TypedExpr::GreaterThan(lhs, rhs, _, _) => Some((BinOp::GreaterThan, lhs, rhs)),
                TypedExpr::LessThanOrEqual(lhs, rhs, _, _) => {
                    Some((BinOp::LessThanOrEqual, lhs, rhs))
                }
                TypedExpr::GreaterThanOrEqual(lhs, rhs, _, _) => {
                    Some((BinOp::GreaterThanOrEqual, lhs, rhs))
                }
                TypedExpr::LeftShift(lhs, rhs, _, _) => Some((BinOp::LeftShift, lhs, rhs)),
                TypedExpr::RightShift(lhs, rhs, _, _) => Some((BinOp::RightShift, lhs, rhs)),
                TypedExpr::BitwiseOr(lhs, rhs, _, _) => Some((BinOp::BitwiseOr, lhs, rhs)),
                TypedExpr::BitwiseXor(lhs, rhs, _, _) => Some((BinOp::BitwiseXor, lhs, rhs)),
                TypedExpr::BitwiseAnd(lhs, rhs, _, _) => Some((BinOp::BitwiseAnd, lhs, rhs)),
                TypedExpr::Comma(lhs, rhs, _, _) => Some((BinOp::Comma, lhs, rhs)),
                _ => None,
            }
        }
    }

    pub fn get_assign_expr(&self) -> Option<(AssignOp, &TypedLValue, &TypedExpr)> {
        match self {
            TypedExpr::Assign(lhs, rhs, _, _) => Some((AssignOp::Assign, lhs, rhs)),
            TypedExpr::AssignAdd(lhs, rhs, _, _) => Some((AssignOp::Add, lhs, rhs)),
            TypedExpr::AssignSub(lhs, rhs, _, _) => Some((AssignOp::Sub, lhs, rhs)),
            TypedExpr::AssignMul(lhs, rhs, _, _) => Some((AssignOp::Mul, lhs, rhs)),
            TypedExpr::AssignDiv(lhs, rhs, _, _) => Some((AssignOp::Div, lhs, rhs)),
            TypedExpr::AssignMod(lhs, rhs, _, _) => Some((AssignOp::Mod, lhs, rhs)),
            TypedExpr::AssignLeftShift(lhs, rhs, _, _) => Some((AssignOp::LeftShift, lhs, rhs)),
            TypedExpr::AssignRightShift(lhs, rhs, _, _) => Some((AssignOp::RightShift, lhs, rhs)),
            TypedExpr::AssignBitwiseAnd(lhs, rhs, _, _) => Some((AssignOp::BitwiseAnd, lhs, rhs)),
            TypedExpr::AssignBitwiseXor(lhs, rhs, _, _) => Some((AssignOp::BitwiseXor, lhs, rhs)),
            TypedExpr::AssignBitwiseOr(lhs, rhs, _, _) => Some((AssignOp::BitwiseOr, lhs, rhs)),
            _ => None,
        }
    }

    pub fn ty(&self) -> &Type {
        match self {
            TypedExpr::Number(_, _, ty) => ty,
            TypedExpr::FloatNumber(_, _, ty) => ty,
            TypedExpr::String(_, _, ty) => ty,
            TypedExpr::Char(_, _, ty) => ty,
            TypedExpr::Variable(_, _, ty) => ty,
            TypedExpr::Call(_, _, _, ty) => ty,
            TypedExpr::Assign(_, _, _, ty) => ty,
            TypedExpr::AssignAdd(_, _, _, ty) => ty,
            TypedExpr::AssignSub(_, _, _, ty) => ty,
            TypedExpr::AssignMul(_, _, _, ty) => ty,
            TypedExpr::AssignDiv(_, _, _, ty) => ty,
            TypedExpr::AssignMod(_, _, _, ty) => ty,
            TypedExpr::AssignLeftShift(_, _, _, ty) => ty,
            TypedExpr::AssignRightShift(_, _, _, ty) => ty,
            TypedExpr::AssignBitwiseAnd(_, _, _, ty) => ty,
            TypedExpr::AssignBitwiseXor(_, _, _, ty) => ty,
            TypedExpr::AssignBitwiseOr(_, _, _, ty) => ty,
            TypedExpr::Add(_, _, _, ty) => ty,
            TypedExpr::Sub(_, _, _, ty) => ty,
            TypedExpr::Mul(_, _, _, ty) => ty,
            TypedExpr::Div(_, _, _, ty) => ty,
            TypedExpr::Mod(_, _, _, ty) => ty,
            TypedExpr::Equal(_, _, _, ty) => ty,
            TypedExpr::NotEqual(_, _, _, ty) => ty,
            TypedExpr::LessThan(_, _, _, ty) => ty,
            TypedExpr::GreaterThan(_, _, _, ty) => ty,
            TypedExpr::LessThanOrEqual(_, _, _, ty) => ty,
            TypedExpr::GreaterThanOrEqual(_, _, _, ty) => ty,
            TypedExpr::LogicalAnd(_, _, _, ty) => ty,
            TypedExpr::LogicalOr(_, _, _, ty) => ty,
            TypedExpr::BitwiseOr(_, _, _, ty) => ty,
            TypedExpr::BitwiseXor(_, _, _, ty) => ty,
            TypedExpr::BitwiseAnd(_, _, _, ty) => ty,
            TypedExpr::LeftShift(_, _, _, ty) => ty,
            TypedExpr::RightShift(_, _, _, ty) => ty,
            TypedExpr::Comma(_, _, _, ty) => ty,
            TypedExpr::Neg(_, _, ty) => ty,
            TypedExpr::LogicalNot(_, _, ty) => ty,
            TypedExpr::BitwiseNot(_, _, ty) => ty,
            TypedExpr::Sizeof(_, _, ty) => ty,
            TypedExpr::Deref(_, _, ty) => ty,
            TypedExpr::AddressOf(_, _, ty) => ty,
            TypedExpr::SizeofType(_, _, ty) => ty,
            TypedExpr::Alignof(_, _, ty) => ty,
            TypedExpr::AlignofType(_, _, ty) => ty,
            TypedExpr::Ternary(_, _, _, _, ty) => ty,
            TypedExpr::Member(_, _, _, ty) => ty,
            TypedExpr::PointerMember(_, _, _, ty) => ty,
            TypedExpr::InitializerList(_, _, ty) => ty,
            TypedExpr::ExplicitCast(_, _, _, ty) => ty,
            TypedExpr::ImplicitCast(_, _, _, ty) => ty,
            TypedExpr::CompoundLiteral(_, _, _, ty) => ty,
            TypedExpr::PreIncrement(_, _, ty) => ty,
            TypedExpr::PreDecrement(_, _, ty) => ty,
            TypedExpr::PostIncrement(_, _, ty) => ty,
            TypedExpr::PostDecrement(_, _, ty) => ty,
        }
    }

    pub fn implicit_cast(self, to_ty: Type) -> TypedExpr {
        if self.ty() == &to_ty {
            self
        } else {
            TypedExpr::ImplicitCast(
                Box::new(to_ty.clone()),
                Box::new(self),
                SourceSpan::default(),
                to_ty,
            )
        }
    }

    pub fn span(&self) -> SourceSpan {
        match self {
            TypedExpr::Number(_, span, _) => *span,
            TypedExpr::FloatNumber(_, span, _) => *span,
            TypedExpr::String(_, span, _) => *span,
            TypedExpr::Char(_, span, _) => *span,
            TypedExpr::Variable(_, span, _) => *span,
            TypedExpr::Call(_, _, span, _) => *span,
            TypedExpr::Assign(_, _, span, _) => *span,
            TypedExpr::AssignAdd(_, _, span, _) => *span,
            TypedExpr::AssignSub(_, _, span, _) => *span,
            TypedExpr::AssignMul(_, _, span, _) => *span,
            TypedExpr::AssignDiv(_, _, span, _) => *span,
            TypedExpr::AssignMod(_, _, span, _) => *span,
            TypedExpr::AssignLeftShift(_, _, span, _) => *span,
            TypedExpr::AssignRightShift(_, _, span, _) => *span,
            TypedExpr::AssignBitwiseAnd(_, _, span, _) => *span,
            TypedExpr::AssignBitwiseXor(_, _, span, _) => *span,
            TypedExpr::AssignBitwiseOr(_, _, span, _) => *span,
            TypedExpr::Add(_, _, span, _) => *span,
            TypedExpr::Sub(_, _, span, _) => *span,
            TypedExpr::Mul(_, _, span, _) => *span,
            TypedExpr::Div(_, _, span, _) => *span,
            TypedExpr::Mod(_, _, span, _) => *span,
            TypedExpr::Equal(_, _, span, _) => *span,
            TypedExpr::NotEqual(_, _, span, _) => *span,
            TypedExpr::LessThan(_, _, span, _) => *span,
            TypedExpr::GreaterThan(_, _, span, _) => *span,
            TypedExpr::LessThanOrEqual(_, _, span, _) => *span,
            TypedExpr::GreaterThanOrEqual(_, _, span, _) => *span,
            TypedExpr::LogicalAnd(_, _, span, _) => *span,
            TypedExpr::LogicalOr(_, _, span, _) => *span,
            TypedExpr::BitwiseOr(_, _, span, _) => *span,
            TypedExpr::BitwiseXor(_, _, span, _) => *span,
            TypedExpr::BitwiseAnd(_, _, span, _) => *span,
            TypedExpr::LeftShift(_, _, span, _) => *span,
            TypedExpr::RightShift(_, _, span, _) => *span,
            TypedExpr::Comma(_, _, span, _) => *span,
            TypedExpr::Neg(_, span, _) => *span,
            TypedExpr::LogicalNot(_, span, _) => *span,
            TypedExpr::BitwiseNot(_, span, _) => *span,
            TypedExpr::Sizeof(_, span, _) => *span,
            TypedExpr::Deref(_, span, _) => *span,
            TypedExpr::AddressOf(_, span, _) => *span,
            TypedExpr::SizeofType(_, span, _) => *span,
            TypedExpr::Alignof(_, span, _) => *span,
            TypedExpr::AlignofType(_, span, _) => *span,
            TypedExpr::Ternary(_, _, _, span, _) => *span,
            TypedExpr::Member(_, _, span, _) => *span,
            TypedExpr::PointerMember(_, _, span, _) => *span,
            TypedExpr::InitializerList(_, span, _) => *span,
            TypedExpr::ExplicitCast(_, _, span, _) => *span,
            TypedExpr::ImplicitCast(_, _, span, _) => *span,
            TypedExpr::CompoundLiteral(_, _, span, _) => *span,
            TypedExpr::PreIncrement(_, span, _) => *span,
            TypedExpr::PreDecrement(_, span, _) => *span,
            TypedExpr::PostIncrement(_, span, _) => *span,
            TypedExpr::PostDecrement(_, span, _) => *span,
        }
    }
}

/// Represents a typed C designator for initializers.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedDesignator {
    /// An array designator, e.g., `[0]`.
    Index(Box<TypedExpr>),
    /// A struct/union member designator, e.g., `.foo`.
    Member(StringId),
}

/// Represents a typed C initializer.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedInitializer {
    /// A single expression initializer.
    Expr(Box<TypedExpr>),
    /// An initializer list, e.g., `{ [0] = 1, .x = 2 }`.
    List(TypedInitializerList),
}

/// Represents a typed declarator, which includes the type modifiers (pointers, arrays) and the identifier.
#[derive(Debug, PartialEq, Clone)]
pub struct TypedDeclarator {
    pub ty: Type,
    pub name: StringId,
    pub initializer: Option<TypedInitializer>,
}

/// Represents the typed initializer of a `for` loop.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedForInit {
    /// A variable declaration.
    Declaration(Type, StringId, Option<TypedInitializer>),
    /// An expression.
    Expr(TypedExpr),
}

/// Represents a typed statement with type information where applicable.
#[derive(Debug, PartialEq, Clone)]
pub enum TypedStmt {
    /// A `return` statement.
    Return(TypedExpr),
    /// An `if` statement.
    If(TypedExpr, Box<TypedStmt>, Option<Box<TypedStmt>>),
    /// A `while` loop.
    While(TypedExpr, Box<TypedStmt>),
    /// A `for` loop.
    For(
        Box<Option<TypedForInit>>,
        Box<Option<TypedExpr>>,
        Box<Option<TypedExpr>>,
        Box<TypedStmt>,
    ),
    /// A block of statements.
    Block(ThinVec<TypedStmt>),
    /// A `switch` statement.
    Switch(TypedExpr, Box<TypedStmt>),
    /// A `case` statement.
    Case(TypedExpr, Box<TypedStmt>),
    /// A `default` statement in a `switch`.
    Default(Box<TypedStmt>),
    /// A labeled statement.
    Label(StringId, Box<TypedStmt>),
    /// A `goto` statement.
    Goto(StringId),
    /// A variable declaration.
    Declaration(Type, ThinVec<TypedDeclarator>, bool),
    FunctionDeclaration {
        ty: Type,
        name: StringId,
        params: ThinVec<Parameter>,
        is_variadic: bool,
        is_inline: bool,
        is_noreturn: bool,
    },
    /// A `break` statement.
    Break,
    /// A `continue` statement.
    Continue,
    /// A `do-while` loop.
    DoWhile(Box<TypedStmt>, TypedExpr),
    /// An empty statement.
    Empty,
    /// An expression statement.
    Expr(TypedExpr),
    /// A `_Static_assert` declaration.
    StaticAssert(Box<TypedExpr>, StringId),
}

/// Represents a typed function declaration with type information.
#[derive(Debug, PartialEq, Clone)]
pub struct TypedFunctionDecl {
    /// The return type of the function.
    pub return_type: Type,
    /// The name of the function.
    pub name: StringId,
    /// The parameters of the function.
    pub params: ThinVec<Parameter>,
    /// The body of the function.
    pub body: ThinVec<TypedStmt>,
    /// Whether the function is declared as inline.
    pub is_inline: bool,
    /// Whether the function is variadic.
    pub is_variadic: bool,
    /// Whether the function is declared as noreturn.
    pub is_noreturn: bool,
}

/// Represents a typed translation unit (program) with type information.
#[derive(Debug, PartialEq, Clone, Default)]
pub struct TypedTranslationUnit {
    /// The global variables.
    pub globals: ThinVec<TypedStmt>,
    /// The functions in the program.
    pub functions: ThinVec<TypedFunctionDecl>,
}
