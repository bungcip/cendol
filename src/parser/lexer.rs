use crate::ast::literal::{CharPrefix, FloatSuffix, IntSuffix, LitRef, LitVal, StrPrefix};
use crate::ast::literal_parsing;
use crate::ast::{FunctionSpec, PragmaPackKind, StorageClass, StringId, TypeQualifier};
use crate::lang_options::CStandard;
use crate::pp::error::PPError;
use crate::pp::{PPToken, PPTokenKind, Preprocessor};
use crate::source_manager::SourceSpan;

use serde::Serialize;
use smallvec::SmallVec;
/// C11 token kinds for the lexical analyzer
#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub enum TokenKind {
    // === LITERALS ===
    Literal(LitRef),

    // === IDENTIFIERS ===
    Identifier(StringId), // Interned identifier

    // === KEYWORDS ===
    // Storage class specifiers
    Auto,
    Extern,
    Register,
    Static,
    ThreadLocal,
    Constexpr,

    // Type qualifiers
    Const,
    Restrict,
    Volatile,
    Atomic,

    // Type specifiers
    Bool,
    Char,
    Double,
    Float,
    Int,
    Long,
    Short,
    Signed,
    Unsigned,
    Void,
    Complex,

    // Complex type specifiers
    Struct,
    Union,
    Enum,

    // Control flow
    Break,
    Case,
    Continue,
    Default,
    Do,
    Else,
    For,
    Goto,
    If,
    Return,
    Switch,
    While,

    // Other keywords
    Alignas,
    Alignof,
    Generic,
    Inline,
    Noreturn,
    Pragma,
    Sizeof,
    StaticAssert,
    Typedef,
    Typeof,
    TypeofUnqual,
    Real,
    Imag,
    Attribute,
    BuiltinVaArg,
    BuiltinBitCast,
    BuiltinConvertVector,
    BuiltinVaList,
    BuiltinChooseExpr,
    BuiltinComplex,
    BuiltinOffsetof,
    BuiltinTypesCompatibleP,
    Asm,
    AutoType,

    // Reserved identifiers as keywords
    Func,           // __func__
    Function,       // __FUNCTION__
    PrettyFunction, // __PRETTY_FUNCTION__

    // === OPERATORS ===
    // Arithmetic operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Increment,
    Decrement,

    // Bitwise operators
    And,
    Or,
    Xor,
    Not,
    Tilde,
    LeftShift,
    RightShift,

    // Comparison operators
    Less,
    Greater,
    LessEqual,
    GreaterEqual,
    Equal,
    NotEqual,

    // Assignment operators
    Assign,
    PlusAssign,
    MinusAssign,
    StarAssign,
    DivAssign,
    ModAssign,
    AndAssign,
    OrAssign,
    XorAssign,
    LeftShiftAssign,
    RightShiftAssign,

    // Logical operators
    LogicAnd,
    LogicOr,

    // Member access
    Arrow,
    Dot,

    // Ternary operator
    Question,
    Colon,

    // === PUNCTUATION ===
    Comma,
    Semicolon,
    Ellipsis,

    // Brackets and parentheses
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,

    // === SPECIAL TOKENS ===
    EndOfFile,
    Unknown,
    Invalid, // Lexing error
    PragmaPack(PragmaPackKind),
}

impl TokenKind {
    fn is_storage_class_specifier(&self) -> bool {
        use TokenKind::*;
        matches!(
            self,
            Typedef | Extern | Static | ThreadLocal | Auto | Register | Constexpr
        )
    }

    pub(super) fn is_type_specifier(&self) -> bool {
        use TokenKind::*;
        matches!(
            self,
            Void | Char
                | Short
                | Int
                | Long
                | Float
                | Double
                | Signed
                | Unsigned
                | Bool
                | Complex
                | Atomic
                | Struct
                | Union
                | Enum
                | BuiltinVaList
                | Typeof
                | TypeofUnqual
                | AutoType
        )
    }

    pub(super) fn is_type_qualifier(&self) -> bool {
        self.as_type_qualifier().is_some()
    }

    pub(crate) fn as_type_qualifier(&self) -> Option<TypeQualifier> {
        use TokenKind::*;
        match self {
            Const => Some(TypeQualifier::Const),
            Restrict => Some(TypeQualifier::Restrict),
            Volatile => Some(TypeQualifier::Volatile),
            Atomic => Some(TypeQualifier::Atomic),
            _ => None,
        }
    }

    fn is_function_specifier(&self) -> bool {
        self.as_function_spec().is_some()
    }

    pub(crate) fn as_storage_class(&self) -> Option<StorageClass> {
        use TokenKind::*;
        match self {
            Typedef => Some(StorageClass::Typedef),
            Extern => Some(StorageClass::Extern),
            Static => Some(StorageClass::Static),
            Auto => Some(StorageClass::Auto),
            Register => Some(StorageClass::Register),
            ThreadLocal => Some(StorageClass::ThreadLocal),
            Constexpr => Some(StorageClass::Constexpr),
            _ => None,
        }
    }

    pub(crate) fn as_function_spec(&self) -> Option<FunctionSpec> {
        use TokenKind::*;
        match self {
            Inline => Some(FunctionSpec::Inline),
            Noreturn => Some(FunctionSpec::Noreturn),
            _ => None,
        }
    }

    fn is_alignment_specifier(&self) -> bool {
        matches!(self, TokenKind::Alignas)
    }

    pub(super) fn is_declaration_specifier_start(&self) -> bool {
        self.is_storage_class_specifier()
            || self.is_type_specifier()
            || self.is_type_qualifier()
            || self.is_function_specifier()
            || self.is_alignment_specifier()
            || matches!(self, TokenKind::Attribute | TokenKind::LeftBracket)
    }

    pub(super) fn is_declaration_start(&self, is_typedef: bool) -> bool {
        self.is_declaration_specifier_start()
            || *self == TokenKind::StaticAssert
            || matches!(self, TokenKind::Identifier(_) if is_typedef)
    }

    pub(crate) fn display(&self) -> &'static str {
        use TokenKind::*;
        match self {
            Literal(_) => "literal",
            Identifier(_) => "identifier",
            Auto => "auto",
            Extern => "extern",
            Register => "register",
            Static => "static",
            ThreadLocal => "_Thread_local",
            Constexpr => "constexpr",
            Const => "const",
            Restrict => "restrict",
            Volatile => "volatile",
            Atomic => "_Atomic",
            Bool => "_Bool",
            Char => "char",
            Double => "double",
            Float => "float",
            Int => "int",
            Long => "long",
            Short => "short",
            Signed => "signed",
            Unsigned => "unsigned",
            Void => "void",
            Complex => "_Complex",
            Struct => "struct",
            Union => "union",
            Enum => "enum",
            Break => "break",
            Case => "case",
            Continue => "continue",
            Default => "default",
            Do => "do",
            Else => "else",
            For => "for",
            Goto => "goto",
            If => "if",
            Return => "return",
            Switch => "switch",
            While => "while",
            Alignas => "_Alignas",
            Alignof => "_Alignof",
            Generic => "_Generic",
            Inline => "inline",
            Noreturn => "_Noreturn",
            Pragma => "_Pragma",
            Sizeof => "sizeof",
            StaticAssert => "_Static_assert",
            Typedef => "typedef",
            Typeof => "typeof",
            TypeofUnqual => "typeof_unqual",
            Real => "__real__",
            Imag => "__imag__",
            Attribute => "__attribute__",
            BuiltinVaArg => "__builtin_va_arg",
            BuiltinBitCast => "__builtin_bit_cast",
            BuiltinConvertVector => "__builtin_convertvector",
            BuiltinVaList => "__builtin_va_list",
            BuiltinChooseExpr => "__builtin_choose_expr",
            BuiltinComplex => "__builtin_complex",
            BuiltinOffsetof => "__builtin_offsetof",
            BuiltinTypesCompatibleP => "__builtin_types_compatible_p",
            Asm => "asm",
            AutoType => "__auto_type",
            PrettyFunction => "__PRETTY_FUNCTION__",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            Percent => "%",
            Increment => "++",
            Decrement => "--",
            And => "&",
            Or => "|",
            Xor => "^",
            Not => "!",
            Tilde => "~",
            LeftShift => "<<",
            RightShift => ">>",
            Less => "<",
            Greater => ">",
            LessEqual => "<=",
            GreaterEqual => ">=",
            Equal => "==",
            NotEqual => "!=",
            Assign => "=",
            PlusAssign => "+=",
            MinusAssign => "-=",
            StarAssign => "*=",
            DivAssign => "/=",
            ModAssign => "%=",
            AndAssign => "&=",
            OrAssign => "|=",
            XorAssign => "^=",
            LeftShiftAssign => "<<=",
            RightShiftAssign => ">>=",
            LogicAnd => "&&",
            LogicOr => "||",
            Arrow => "->",
            Dot => ".",
            Question => "?",
            Colon => ":",
            Comma => ",",
            Semicolon => ";",
            Ellipsis => "...",
            LeftParen => "(",
            RightParen => ")",
            LeftBracket => "[",
            RightBracket => "]",
            LeftBrace => "{",
            RightBrace => "}",
            EndOfFile => "end of file",
            Unknown => "unknown token",
            PragmaPack(_) => "#pragma pack",
            Func => "__func__",
            Function => "__FUNCTION__",
            Invalid => "invalid token",
        }
    }
}

impl std::fmt::Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenKind::Literal(lit) => match lit.get_val() {
                LitVal::Int { value, .. } => write!(f, "{}", value),
                LitVal::Float { bits, .. } => write!(f, "{}", f64::from_bits(bits)),
                LitVal::String { value, .. } => write!(f, "\"{}\"", value),
                LitVal::Char(c, _prefix) => {
                    if let Some(ch) = char::from_u32(c) {
                        write!(f, "'{}'", ch)
                    } else {
                        write!(f, "'\\u{{{:x}}}'", c)
                    }
                }
                _ => write!(f, "{}", self.display()),
            },
            TokenKind::Identifier(sym) => write!(f, "{}", sym.as_str()),
            _ => write!(f, "{}", self.display()),
        }
    }
}

/// Token with source span for the parser
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: SourceSpan,
}

/// Classify a preprocessor punctuation token into a lexical token.
///
/// ⚡ Bolt: Optimized with a `match` statement.
/// This is significantly faster than the previous `HashMap` implementation because
/// the Rust compiler can optimize it into a perfect hash table or a more direct
/// jump table, avoiding the overhead of runtime hashing and lookups.
fn classify_punctuation(pp_token_kind: PPTokenKind) -> TokenKind {
    match pp_token_kind {
        // Arithmetic operators
        PPTokenKind::Plus => TokenKind::Plus,
        PPTokenKind::Minus => TokenKind::Minus,
        PPTokenKind::Star => TokenKind::Star,
        PPTokenKind::Slash => TokenKind::Slash,
        PPTokenKind::Percent => TokenKind::Percent,
        PPTokenKind::Increment => TokenKind::Increment,
        PPTokenKind::Decrement => TokenKind::Decrement,

        // Bitwise operators
        PPTokenKind::And => TokenKind::And,
        PPTokenKind::Or => TokenKind::Or,
        PPTokenKind::Xor => TokenKind::Xor,
        PPTokenKind::Not => TokenKind::Not,
        PPTokenKind::Tilde => TokenKind::Tilde,
        PPTokenKind::LeftShift => TokenKind::LeftShift,
        PPTokenKind::RightShift => TokenKind::RightShift,

        // Comparison operators
        PPTokenKind::Less => TokenKind::Less,
        PPTokenKind::Greater => TokenKind::Greater,
        PPTokenKind::LessEqual => TokenKind::LessEqual,
        PPTokenKind::GreaterEqual => TokenKind::GreaterEqual,
        PPTokenKind::Equal => TokenKind::Equal,
        PPTokenKind::NotEqual => TokenKind::NotEqual,

        // Assignment operators
        PPTokenKind::Assign => TokenKind::Assign,
        PPTokenKind::PlusAssign => TokenKind::PlusAssign,
        PPTokenKind::MinusAssign => TokenKind::MinusAssign,
        PPTokenKind::StarAssign => TokenKind::StarAssign,
        PPTokenKind::DivAssign => TokenKind::DivAssign,
        PPTokenKind::ModAssign => TokenKind::ModAssign,
        PPTokenKind::AndAssign => TokenKind::AndAssign,
        PPTokenKind::OrAssign => TokenKind::OrAssign,
        PPTokenKind::XorAssign => TokenKind::XorAssign,
        PPTokenKind::LeftShiftAssign => TokenKind::LeftShiftAssign,
        PPTokenKind::RightShiftAssign => TokenKind::RightShiftAssign,

        // Logical operators
        PPTokenKind::LogicAnd => TokenKind::LogicAnd,
        PPTokenKind::LogicOr => TokenKind::LogicOr,

        // Member access
        PPTokenKind::Arrow => TokenKind::Arrow,
        PPTokenKind::Dot => TokenKind::Dot,

        // Ternary operator
        PPTokenKind::Question => TokenKind::Question,
        PPTokenKind::Colon => TokenKind::Colon,

        // Punctuation
        PPTokenKind::Comma => TokenKind::Comma,
        PPTokenKind::Semicolon => TokenKind::Semicolon,
        PPTokenKind::Ellipsis => TokenKind::Ellipsis,

        // Brackets and parentheses
        PPTokenKind::LeftParen => TokenKind::LeftParen,
        PPTokenKind::RightParen => TokenKind::RightParen,
        PPTokenKind::LeftBracket => TokenKind::LeftBracket,
        PPTokenKind::RightBracket => TokenKind::RightBracket,
        PPTokenKind::LeftBrace => TokenKind::LeftBrace,
        PPTokenKind::RightBrace => TokenKind::RightBrace,

        // Tokens that don't map directly to a parser token
        PPTokenKind::Hash | PPTokenKind::HashHash => TokenKind::Unknown,

        // Non-punctuation tokens are not handled by this function
        _ => TokenKind::Unknown,
    }
}

/// Check if a symbol represents a C11 keyword.
///
/// ⚡ Bolt: Optimized with a pre-initialized `HashMap`.
/// This is significantly faster than the previous match-based implementation, which
/// required converting the `StringId` to a `&str` for every lookup. This version
// pre-interns all keywords and stores them in a lazily-initialized `HashMap`.
/// Subsequent lookups use the `StringId` directly, resulting in a much faster
/// integer comparison instead of a string comparison.
fn is_keyword(symbol: StringId, std: crate::lang_options::CStandard) -> Option<TokenKind> {
    let kind = keyword_map().get(&symbol).copied()?;

    // C23 keywords: block certain spellings if standard is older than C23.
    // e.g. 'static_assert' is a keyword in C23, but in C11 it is only a keyword
    // when spelled as '_Static_assert'.
    if std < crate::lang_options::CStandard::C23 {
        let sk = special_keywords();
        match kind {
            TokenKind::StaticAssert if symbol == sk.static_assert => return None,
            TokenKind::Literal(lit) if lit == LitRef::NULLPTR || lit == LitRef::TRUE || lit == LitRef::FALSE => {
                return None;
            }
            TokenKind::TypeofUnqual if symbol == sk.typeof_unqual => return None,
            TokenKind::Bool if symbol == sk.bool_kw => return None,
            TokenKind::Alignas if symbol == sk.alignas => return None,
            TokenKind::Alignof if symbol == sk.alignof => return None,
            TokenKind::ThreadLocal if symbol == sk.thread_local => return None,
            TokenKind::Constexpr if symbol == sk.constexpr => return None,
            _ => {}
        }
    }

    Some(kind)
}

struct SpecialKeywords {
    static_assert: StringId,
    typeof_unqual: StringId,
    bool_kw: StringId,
    alignas: StringId,
    alignof: StringId,
    thread_local: StringId,
    constexpr: StringId,
}

fn special_keywords() -> &'static SpecialKeywords {
    static KEYWORDS: std::sync::OnceLock<SpecialKeywords> = std::sync::OnceLock::new();
    KEYWORDS.get_or_init(|| SpecialKeywords {
        static_assert: StringId::new("static_assert"),
        typeof_unqual: StringId::new("typeof_unqual"),
        bool_kw: StringId::new("bool"),
        alignas: StringId::new("alignas"),
        alignof: StringId::new("alignof"),
        thread_local: StringId::new("thread_local"),
        constexpr: StringId::new("constexpr"),
    })
}

fn keyword_map() -> &'static hashbrown::HashMap<StringId, TokenKind> {
    static KEYWORDS: std::sync::OnceLock<hashbrown::HashMap<StringId, TokenKind>> = std::sync::OnceLock::new();
    KEYWORDS.get_or_init(|| {
        let mut m = hashbrown::HashMap::new();
        m.insert(StringId::new("auto"), TokenKind::Auto);
        m.insert(StringId::new("break"), TokenKind::Break);
        m.insert(StringId::new("case"), TokenKind::Case);
        m.insert(StringId::new("char"), TokenKind::Char);
        m.insert(StringId::new("const"), TokenKind::Const);
        m.insert(StringId::new("continue"), TokenKind::Continue);
        m.insert(StringId::new("default"), TokenKind::Default);
        m.insert(StringId::new("do"), TokenKind::Do);
        m.insert(StringId::new("double"), TokenKind::Double);
        m.insert(StringId::new("else"), TokenKind::Else);
        m.insert(StringId::new("enum"), TokenKind::Enum);
        m.insert(StringId::new("extern"), TokenKind::Extern);
        m.insert(StringId::new("float"), TokenKind::Float);
        m.insert(StringId::new("for"), TokenKind::For);
        m.insert(StringId::new("goto"), TokenKind::Goto);
        m.insert(StringId::new("if"), TokenKind::If);
        m.insert(StringId::new("inline"), TokenKind::Inline);
        m.insert(StringId::new("int"), TokenKind::Int);
        m.insert(StringId::new("long"), TokenKind::Long);
        m.insert(StringId::new("register"), TokenKind::Register);
        m.insert(StringId::new("restrict"), TokenKind::Restrict);
        m.insert(StringId::new("return"), TokenKind::Return);
        m.insert(StringId::new("short"), TokenKind::Short);
        m.insert(StringId::new("signed"), TokenKind::Signed);
        m.insert(StringId::new("sizeof"), TokenKind::Sizeof);
        m.insert(StringId::new("static"), TokenKind::Static);
        m.insert(StringId::new("struct"), TokenKind::Struct);
        m.insert(StringId::new("switch"), TokenKind::Switch);
        m.insert(StringId::new("typedef"), TokenKind::Typedef);
        m.insert(StringId::new("typeof"), TokenKind::Typeof);
        m.insert(StringId::new("__typeof"), TokenKind::Typeof);
        m.insert(StringId::new("__typeof__"), TokenKind::Typeof);
        m.insert(StringId::new("typeof_unqual"), TokenKind::TypeofUnqual);
        m.insert(StringId::new("__typeof_unqual"), TokenKind::TypeofUnqual);
        m.insert(StringId::new("__typeof_unqual__"), TokenKind::TypeofUnqual);
        m.insert(StringId::new("union"), TokenKind::Union);
        m.insert(StringId::new("unsigned"), TokenKind::Unsigned);
        m.insert(StringId::new("void"), TokenKind::Void);
        m.insert(StringId::new("volatile"), TokenKind::Volatile);
        m.insert(StringId::new("while"), TokenKind::While);
        m.insert(StringId::new("__auto_type"), TokenKind::AutoType);
        m.insert(StringId::new("__auto_type__"), TokenKind::AutoType);
        m.insert(StringId::new("bool"), TokenKind::Bool);
        m.insert(StringId::new("nullptr"), TokenKind::Literal(LitRef::NULLPTR));
        m.insert(StringId::new("true"), TokenKind::Literal(LitRef::TRUE));
        m.insert(StringId::new("false"), TokenKind::Literal(LitRef::FALSE));
        m.insert(StringId::new("alignas"), TokenKind::Alignas);
        m.insert(StringId::new("alignof"), TokenKind::Alignof);
        m.insert(StringId::new("thread_local"), TokenKind::ThreadLocal);
        m.insert(StringId::new("constexpr"), TokenKind::Constexpr);
        m.insert(StringId::new("__real__"), TokenKind::Real);
        m.insert(StringId::new("__builtin_real"), TokenKind::Real);
        m.insert(StringId::new("__imag__"), TokenKind::Imag);
        m.insert(StringId::new("__builtin_imag"), TokenKind::Imag);
        m.insert(StringId::new("_Alignas"), TokenKind::Alignas);
        m.insert(StringId::new("__alignas"), TokenKind::Alignas);
        m.insert(StringId::new("__alignas__"), TokenKind::Alignas);
        m.insert(StringId::new("_Alignof"), TokenKind::Alignof);
        m.insert(StringId::new("__alignof"), TokenKind::Alignof);
        m.insert(StringId::new("__alignof__"), TokenKind::Alignof);
        m.insert(StringId::new("_Atomic"), TokenKind::Atomic);
        m.insert(StringId::new("_Bool"), TokenKind::Bool);
        m.insert(StringId::new("_Complex"), TokenKind::Complex);
        m.insert(StringId::new("_Generic"), TokenKind::Generic);
        m.insert(StringId::new("_Noreturn"), TokenKind::Noreturn);
        m.insert(StringId::new("_Pragma"), TokenKind::Pragma);
        m.insert(StringId::new("_Static_assert"), TokenKind::StaticAssert);
        m.insert(StringId::new("static_assert"), TokenKind::StaticAssert);
        m.insert(StringId::new("_Thread_local"), TokenKind::ThreadLocal);
        m.insert(StringId::new("__attribute__"), TokenKind::Attribute);
        m.insert(StringId::new("__attribute"), TokenKind::Attribute);
        m.insert(StringId::new("__builtin_va_arg"), TokenKind::BuiltinVaArg);
        m.insert(StringId::new("__builtin_bit_cast"), TokenKind::BuiltinBitCast);
        m.insert(
            StringId::new("__builtin_convertvector"),
            TokenKind::BuiltinConvertVector,
        );
        m.insert(StringId::new("__builtin_va_list"), TokenKind::BuiltinVaList);
        m.insert(StringId::new("__gnuc_va_list"), TokenKind::BuiltinVaList); // GCC alias for __builtin_va_list
        m.insert(StringId::new("__builtin_choose_expr"), TokenKind::BuiltinChooseExpr);
        m.insert(StringId::new("__builtin_complex"), TokenKind::BuiltinComplex);
        m.insert(StringId::new("__builtin_offsetof"), TokenKind::BuiltinOffsetof);
        m.insert(
            StringId::new("__builtin_types_compatible_p"),
            TokenKind::BuiltinTypesCompatibleP,
        );

        // GCC/Clang extensions
        m.insert(StringId::new("__restrict"), TokenKind::Restrict);
        m.insert(StringId::new("__restrict__"), TokenKind::Restrict);
        m.insert(StringId::new("__const"), TokenKind::Const);
        m.insert(StringId::new("__const__"), TokenKind::Const);
        m.insert(StringId::new("__volatile"), TokenKind::Volatile);
        m.insert(StringId::new("__volatile__"), TokenKind::Volatile);
        m.insert(StringId::new("__inline"), TokenKind::Inline);
        m.insert(StringId::new("__inline__"), TokenKind::Inline);
        m.insert(StringId::new("__signed"), TokenKind::Signed);
        m.insert(StringId::new("__signed__"), TokenKind::Signed);
        m.insert(StringId::new("__unsigned"), TokenKind::Unsigned);
        m.insert(StringId::new("__unsigned__"), TokenKind::Unsigned);
        m.insert(StringId::new("__asm"), TokenKind::Asm);
        m.insert(StringId::new("__asm__"), TokenKind::Asm);
        m.insert(StringId::new("asm"), TokenKind::Asm);

        // Reserved identifiers
        m.insert(StringId::new("__func__"), TokenKind::Func);
        m.insert(StringId::new("__FUNCTION__"), TokenKind::Function);
        m.insert(StringId::new("__PRETTY_FUNCTION__"), TokenKind::PrettyFunction);
        m
    })
}

/// Lexer state machine
pub struct Lexer<'src> {
    pub(crate) preprocessor: &'src mut Preprocessor<'src>,
    pub(crate) pp_lookahead: Option<PPToken>,
    c_standard: CStandard,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer with the given preprocessor token stream
    pub(crate) fn new(preprocessor: &'src mut Preprocessor<'src>, c_standard: CStandard) -> Self {
        Lexer {
            pp_lookahead: None,
            preprocessor,
            c_standard,
        }
    }

    /// Classify a preprocessor token into a lexical token
    fn classify_token(&mut self, pptoken: &PPToken) -> TokenKind {
        match pptoken.kind {
            PPTokenKind::Identifier(symbol) => {
                // Check if it's a keyword
                is_keyword(symbol, self.c_standard).unwrap_or(TokenKind::Identifier(symbol))
            }
            PPTokenKind::StringLiteral => {
                // This is now handled in next_token to support concatenation
                unreachable!("String literal should be handled in next_token")
            }
            PPTokenKind::CharLiteral(codepoint) => {
                let text = self.preprocessor.get_token_text(pptoken);
                let prefix = if text.starts_with("u8'") {
                    CharPrefix::Utf8
                } else if text.starts_with("L'") {
                    CharPrefix::Wide
                } else if text.starts_with("u'") {
                    CharPrefix::Char16
                } else if text.starts_with("U'") {
                    CharPrefix::Char32
                } else {
                    CharPrefix::None
                };
                let lit = LitRef::from_char(codepoint, prefix);
                TokenKind::Literal(lit)
            }
            PPTokenKind::Number => {
                let text = self.preprocessor.get_token_text(pptoken);
                // Try to parse as integer first, then float, then unknown
                if let Some((value, suffix, radix)) = literal_parsing::parse_integer_literal(&text) {
                    let lit = LitRef::from_int(value, suffix.unwrap_or(IntSuffix::None), radix);
                    TokenKind::Literal(lit)
                } else if let Some((float_val, suffix)) = literal_parsing::parse_float_literal(&text) {
                    TokenKind::Literal(LitRef::from_f64(float_val, suffix.unwrap_or(FloatSuffix::None)))
                } else {
                    TokenKind::Invalid
                }
            }
            PPTokenKind::Eof => TokenKind::EndOfFile,
            PPTokenKind::Eod => TokenKind::Unknown,
            PPTokenKind::PragmaPack(kind) => TokenKind::PragmaPack(kind),
            // Handle punctuation tokens using the optimized match-based function
            pptoken_kind => classify_punctuation(pptoken_kind),
        }
    }

    /// Retrieve the next preprocessor token, respecting lookahead
    fn next_pp_token(&mut self) -> Result<Option<PPToken>, PPError> {
        if let Some(token) = self.pp_lookahead.take() {
            return Ok(Some(token));
        }
        self.preprocessor.next_token()
    }

    /// Peek at the next preprocessor token
    fn peek_pp_token(&mut self) -> Result<Option<PPToken>, PPError> {
        if self.pp_lookahead.is_none() {
            self.pp_lookahead = self.preprocessor.next_token()?;
        }
        Ok(self.pp_lookahead)
    }

    /// Retrieve the next lexed token from the stream
    pub(crate) fn tokenize_all(&mut self) -> Result<Vec<Token>, PPError> {
        let mut tokens = Vec::new();
        while let Some(token) = self.next_token()? {
            let is_eof = matches!(token.kind, TokenKind::EndOfFile);
            tokens.push(token);
            if is_eof {
                break;
            }
        }
        Ok(tokens)
    }

    pub(crate) fn next_token(&mut self) -> Result<Option<Token>, PPError> {
        let pptoken = match self.next_pp_token()? {
            Some(t) => t,
            None => return Ok(None),
        };

        let span = SourceSpan::new_with_length(
            pptoken.location.source_id(),
            pptoken.location.offset(),
            pptoken.length as u32,
        );

        if pptoken.kind == PPTokenKind::StringLiteral {
            // Collect all adjacent string literals FIRST to avoid borrow checker issues
            let mut string_tokens: SmallVec<[PPToken; 4]> = smallvec::smallvec![pptoken];
            while let Some(next) = self.peek_pp_token()? {
                if next.kind == PPTokenKind::StringLiteral {
                    string_tokens.push(self.next_pp_token()?.unwrap());
                } else {
                    break;
                }
            }

            let mut prefix = "";
            let mut content = String::new();
            let mut merged_span = span;

            for (i, t) in string_tokens.iter().enumerate() {
                let text = self.preprocessor.get_token_text(t);
                let (next_prefix, next_content) = Self::extract_literal_parts(&text).unwrap_or(("", &text));
                if i == 0 || prefix.is_empty() {
                    prefix = next_prefix;
                }
                content.push_str(next_content);
                let t_span = SourceSpan::new_with_length(t.location.source_id(), t.location.offset(), t.length as u32);
                merged_span = merged_span.merge(t_span);
            }

            let unescaped = literal_parsing::unescape(&content);
            return Ok(Some(Token {
                kind: TokenKind::Literal(LitRef::from_string(unescaped, StrPrefix::from_str(prefix))),
                span: merged_span,
            }));
        }

        Ok(Some(Token {
            kind: self.classify_token(&pptoken),
            span,
        }))
    }

    /// Extract parts from a string literal symbol: (prefix, content_without_quotes)
    fn extract_literal_parts(s: &str) -> Option<(&'static str, &str)> {
        for prefix in ["L", "u8", "u", "U"] {
            if let Some(rest) = s.strip_prefix(prefix)
                && let Some(inner) = rest.strip_prefix('"')?.strip_suffix('"')
            {
                return Some((prefix, inner));
            }
        }
        if let Some(inner) = s.strip_prefix('"')?.strip_suffix('"') {
            return Some(("", inner));
        }
        None
    }
}
