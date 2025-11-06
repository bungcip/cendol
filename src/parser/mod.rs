use crate::SourceSpan;
use crate::parser::ast::{
    Decl, Designator, Expr, ForInit, FuncDecl, Initializer, InitializerList, Stmt, RecordFieldDecl, TranslationUnit
};
use crate::types::{DeclId, TypeSpec, TypeSpecKind, TypeQual, StorageClass, TypeKeywordMask};
use crate::semantic::type_spec_to_type_id;
use crate::parser::error::ParserError;
use crate::parser::expr_interner::ExprInterner;
use crate::parser::array_expr_interner::ArrayExprListInterner;
use crate::parser::string_interner::{StringId, StringInterner};
use crate::parser::token::{KeywordKind, Token, TokenKind};
use crate::preprocessor;
use std::collections::HashMap;
use thin_vec::ThinVec;

pub mod ast;
pub mod error;
pub mod string_interner;
pub mod expr_interner;
pub mod array_expr_interner;
pub mod token;

pub struct FuncSignature(TypeSpec, StringId, ThinVec<ast::ParamDecl>, bool, bool, bool);

/// A parser that converts a stream of tokens into an abstract syntax tree.
pub struct Parser {
    tokens: Vec<Token>,
    position: usize,
    typedefs: HashMap<StringId, (TypeSpec, DeclId)>,
    struct_defs: HashMap<StringId, usize>,
    union_defs: HashMap<StringId, usize>,
    enum_defs: HashMap<StringId, usize>,
    globals: ThinVec<Decl>,
}

impl Parser {
    /// Creates a new `Parser`.
    ///
    /// # Arguments
    ///
    /// * `tokens` - A vector of preprocessor tokens.
    ///
    /// # Returns
    ///
    /// A `Result` containing the new `Parser` instance, or a `ParserError` if tokenization fails.
    pub fn new(tokens: Vec<preprocessor::token::Token>) -> Result<Self, ParserError> {
        // Filter out tokens that the parser can't handle
        let mut filtered_tokens: Vec<Token> = Vec::new();
        let mut skip_next_tokens = false;

        for token in tokens {
            match &token.kind {
                preprocessor::token::TokenKind::Directive(_) => {
                    skip_next_tokens = true;
                    continue;
                }
                preprocessor::token::TokenKind::Whitespace(_)
                | preprocessor::token::TokenKind::Newline
                | preprocessor::token::TokenKind::Comment(_) => {
                    continue;
                }
                // Skip tokens that come from directive expansions
                _ if !token.expansion_locs.is_empty() => {
                    continue;
                }
                // Skip tokens that immediately follow a directive (like line directive arguments)
                _ if skip_next_tokens => {
                    // Check if this is likely a directive argument (Number or String at the beginning)
                    if (matches!(
                        token.kind,
                        preprocessor::token::TokenKind::Number(_)
                            | preprocessor::token::TokenKind::String(_)
                    )) && filtered_tokens.is_empty()
                    {
                        continue;
                    }
                    skip_next_tokens = false;
                }
                _ => {}
            }
            filtered_tokens.push(Token::from(token));
        }

        let parser = Parser {
            tokens: filtered_tokens,
            position: 0,
            typedefs: HashMap::new(),
            struct_defs: HashMap::new(),
            union_defs: HashMap::new(),
            enum_defs: HashMap::new(),
            globals: ThinVec::new(),
        };
        Ok(parser)
    }

    /// Creates a new TypeSpec with default values for common fields.
    fn new_typespec(kind: TypeSpecKind) -> crate::types::TypeSpec {
        // Use TypeSpec::new which handles packing header and setting align_expr/array_exprs to None.
        // Assuming StorageClass::Auto is the default storage class (0).
        crate::types::TypeSpec::new(
            kind,
            TypeQual::empty(),
            StorageClass::Auto,
            0,
            0,
        )
    }

    /// Returns the current token without consuming it.
    fn current_token(&self) -> Result<Token, ParserError> {
        self.tokens
            .get(self.position)
            .cloned()
            .ok_or(ParserError::UnexpectedEof(SourceSpan::default()))
    }

    /// Returns the kind of the current token.
    fn current_kind(&self) -> Result<TokenKind, ParserError> {
        self.current_token().map(|t| t.kind)
    }

    fn peek(&self) -> Result<TokenKind, ParserError> {
        self.tokens
            .get(self.position + 1)
            .cloned()
            .map(|t| t.kind)
            .ok_or(ParserError::UnexpectedEof(SourceSpan::default()))
    }

    /// Consumes the current token and return the last token. will error if current token is eof
    fn eat(&mut self) -> Result<&Token, ParserError> {
        let current = self
            .tokens
            .get(self.position)
            .ok_or(ParserError::UnexpectedEof(SourceSpan::default()));
        self.position += 1;
        current
    }

    /// consume the current token if same kind
    fn eat_token(&mut self, kind: &TokenKind) -> Result<bool, ParserError> {
        if self.current_kind()? == *kind {
            self.eat()?;
            return Ok(true);
        }
        Ok(false)
    }

    /// Expects a specific punctuation token.
    fn expect_punct(&mut self, value: TokenKind) -> Result<(), ParserError> {
        if self.eat_token(&value)? {
            return Ok(());
        }
        let token = self.current_token()?;
        Err(ParserError::UnexpectedToken(token))
    }

    /// Expects a specific keyword.
    fn expect_keyword(&mut self, value: KeywordKind) -> Result<(), ParserError> {
        if self.eat_token(&TokenKind::Keyword(value))? {
            return Ok(());
        }
        let token = self.current_token()?;
        Err(ParserError::UnexpectedToken(token))
    }

    /// Peeks if the current token sequence is a type name without consuming tokens.
    fn is_type_name(&mut self) -> bool {
        let original_pos = self.position;
        let result = self.parse_type().is_ok();
        self.position = original_pos;
        result
    }

    /// Expects and consumes an optional identifier, returning its name if present.
    fn maybe_name(&mut self) -> Result<Option<StringId>, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind {
            self.eat()?;
            Ok(Some(id))
        } else {
            Ok(None)
        }
    }

    /// Expects and consumes an identifier, returning its name.
    fn expect_name(&mut self) -> Result<StringId, ParserError> {
        let token = self.current_token()?;
        if let TokenKind::Identifier(id) = token.kind {
            self.eat()?;
            Ok(id)
        } else {
            Err(ParserError::UnexpectedToken(token))
        }
    }

    /// Parses a type specifier (e.g., `int`, `struct S`, `long long`).
    /// Returns (TypeSpec, Option<Decl>) where Decl contains the full declaration for structs/unions/enums.
    fn parse_type_specifier(&mut self) -> Result<(crate::types::TypeSpec, Option<Decl>), ParserError> {
        let mut modifiers: Vec<Box<dyn FnOnce(&mut crate::types::TypeSpec)>> = Vec::new();
        loop {
            let token = self.current_token()?.clone();
            if let TokenKind::Keyword(k) = token.kind {
                if k == KeywordKind::Const {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        let current_qual = ts.qualifiers();
                        let new_qual = current_qual | TypeQual::CONST;
                        ts.header = (ts.header & !0xFF) | (new_qual.bits() as u32);
                    }));
                    continue;
                }
                if k == KeywordKind::Volatile {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        let current_qual = ts.qualifiers();
                        let new_qual = current_qual | TypeQual::VOLATILE;
                        ts.header = (ts.header & !0xFF) | (new_qual.bits() as u32);
                    }));
                    continue;
                }
                if k == KeywordKind::Restrict {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        let current_qual = ts.qualifiers();
                        let new_qual = current_qual | TypeQual::RESTRICT;
                        ts.header = (ts.header & !0xFF) | (new_qual.bits() as u32);
                    }));
                    continue;
                }
                if k == KeywordKind::Complex {
                    self.eat()?;
                    // no modifier
                    continue;
                }
                if k == KeywordKind::Imaginary {
                    self.eat()?;
                    // no modifier
                    continue;
                }
                if k == KeywordKind::_Alignas {
                    self.eat()?;
                    self.expect_punct(TokenKind::LeftParen)?;
                    let alignment_expr = self.parse_expr()?;
                    self.expect_punct(TokenKind::RightParen)?;
                    let expr_id = ExprInterner::intern(alignment_expr);
                    modifiers.push(Box::new(move |ts: &mut crate::types::TypeSpec| {
                        *ts = ts.with_align(expr_id);
                    }));
                    continue;
                }
                if k == KeywordKind::Typedef {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        ts.header = (ts.header & !0xFF00) | ((StorageClass::Typedef as u32) << 8);
                    }));
                    continue;
                }
                if k == KeywordKind::Extern {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        ts.header = (ts.header & !0xFF00) | ((StorageClass::Extern as u32) << 8);
                    }));
                    continue;
                }
                if k == KeywordKind::Static {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        ts.header = (ts.header & !0xFF00) | ((StorageClass::Static as u32) << 8);
                    }));
                    continue;
                }
                if k == KeywordKind::Auto {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        ts.header = (ts.header & !0xFF00) | ((StorageClass::Auto as u32) << 8);
                    }));
                    continue;
                }
                if k == KeywordKind::Register {
                    self.eat()?;
                    modifiers.push(Box::new(|ts: &mut crate::types::TypeSpec| {
                        ts.header = (ts.header & !0xFF00) | ((StorageClass::Register as u32) << 8);
                    }));
                    continue;
                }
                // _Thread_local is not in KeywordKind, skip for now
            }
            break;
        }
        // now parse the base
        let token = self.current_token()?.clone();
        let (mut type_spec, decl) = if let TokenKind::Keyword(k) = token.kind {
            self.parse_type_specifier_kind(k, token.span)?
        } else if let TokenKind::Identifier(id) = token.kind {
            let typedef_entry = self.typedefs.get(&id).cloned();
            if let Some((_, decl_id)) = typedef_entry {
                self.eat()?;
                (Parser::new_typespec(TypeSpecKind::Typedef(decl_id)), None)
            } else {
                return Err(ParserError::UnexpectedToken(token));
            }
        } else {
            return Err(ParserError::UnexpectedToken(token));
        };
        // apply modifiers in reverse order
        for modifier in modifiers.into_iter().rev() {
            modifier(&mut type_spec);
        }
        Ok((type_spec, decl))
    }

    /// Parses a type specifier kind.
    fn parse_type_specifier_kind(
        &mut self,
        k: KeywordKind,
        span: SourceSpan,
    ) -> Result<(crate::types::TypeSpec, Option<Decl>), ParserError> {
        self.eat()?; // consume the keyword
        match k {
            KeywordKind::Unsigned => {
                let mut mask = TypeKeywordMask::UNSIGNED;
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token {
                    if let TokenKind::Keyword(KeywordKind::Long) = next.kind {
                        self.eat()?; // consume "long"
                        let next2 = self.tokens.get(self.position).cloned();
                        if let Some(n2) = next2.clone() && let TokenKind::Keyword(KeywordKind::Long) = n2.kind {
                            self.eat()?; // consume second "long"
                            mask |= TypeKeywordMask::LONGLONG;
                            let next3 = self.tokens.get(self.position).cloned();
                            if let Some(n3) = next3
                                && let TokenKind::Keyword(KeywordKind::Int) = n3.kind
                            {
                                self.eat()?; // consume "int"
                                mask |= TypeKeywordMask::INT;
                            }
                        } else {
                            mask |= TypeKeywordMask::LONG;
                            if let Some(n2) = next2 && let TokenKind::Keyword(KeywordKind::Int) = n2.kind {
                                self.eat()?; // consume "int"
                                mask |= TypeKeywordMask::INT;
                            }
                        }
                    } else if let TokenKind::Keyword(KeywordKind::Int) = next.kind {
                        self.eat()?; // consume "int"
                        mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::INT;
                    } else if let TokenKind::Keyword(KeywordKind::Char) = next.kind {
                        self.eat()?; // consume "char"
                        mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::CHAR;
                    } else if let TokenKind::Keyword(KeywordKind::Short) = next.kind {
                        self.eat()?; // consume "short"
                        mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::SHORT;
                    }
                }
                Ok((
                    Parser::new_typespec(TypeSpecKind::Builtin(mask)),
                    None,
                ))
            }
            KeywordKind::Short => {
                let mut mask = TypeKeywordMask::SHORT;
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token
                    && let TokenKind::Keyword(KeywordKind::Int) = next.kind
                {
                    self.eat()?; // consume "int"
                    mask |= TypeKeywordMask::INT;
                }
                Ok((
                    Parser::new_typespec(TypeSpecKind::Builtin(mask)),
                    None,
                ))
            }
            KeywordKind::Long => {
                let mut mask = TypeKeywordMask::LONG;
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token {
                    if let TokenKind::Keyword(KeywordKind::Long) = next.kind {
                        self.eat()?; // consume second "long"
                        mask |= TypeKeywordMask::LONGLONG;
                        let next2 = self.tokens.get(self.position).cloned();
                        if let Some(n2) = next2 {
                            if let TokenKind::Keyword(KeywordKind::Unsigned) = n2.kind {
                                self.eat()?; // consume "unsigned"
                                mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::LONGLONG;
                            } else if let TokenKind::Keyword(KeywordKind::Int) = n2.kind {
                                self.eat()?; // consume "int"
                                mask |= TypeKeywordMask::INT;
                            }
                        }
                    } else if let TokenKind::Keyword(KeywordKind::Unsigned) = next.kind {
                        self.eat()?; // consume "unsigned"
                        let next2 = self.tokens.get(self.position).cloned();
                        if let Some(n2) = next2 {
                            if let TokenKind::Keyword(KeywordKind::Long) = n2.kind {
                                self.eat()?; // consume "long"
                                mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::LONGLONG;
                            } else if let TokenKind::Keyword(KeywordKind::Int) = n2.kind {
                                self.eat()?; // consume "int"
                                mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::LONG | TypeKeywordMask::INT;
                            }
                        }
                        if mask == TypeKeywordMask::LONG {
                            mask = TypeKeywordMask::UNSIGNED | TypeKeywordMask::LONG;
                        }
                    } else if let TokenKind::Keyword(KeywordKind::Int) = next.kind {
                        self.eat()?; // consume "int"
                        mask |= TypeKeywordMask::INT;
                    }
                }
                Ok((
                    Parser::new_typespec(TypeSpecKind::Builtin(mask)),
                    None,
                ))
            }
            KeywordKind::Int => {
                let mut mask = TypeKeywordMask::INT;
                let next_token = self.tokens.get(self.position).cloned();
                if let Some(next) = next_token
                    && let TokenKind::Keyword(KeywordKind::Long) = next.kind
                {
                    self.eat()?; // consume "long"
                    mask |= TypeKeywordMask::LONG;
                }
                Ok((
                    Parser::new_typespec(TypeSpecKind::Builtin(mask)),
                    None,
                ))
            }
            KeywordKind::Char => Ok((
                Parser::new_typespec(TypeSpecKind::Builtin(TypeKeywordMask::CHAR)),
                None,
            )),
            KeywordKind::Float => Ok((
                Parser::new_typespec(TypeSpecKind::Builtin(TypeKeywordMask::FLOAT)),
                None,
            )),
            KeywordKind::Double => Ok((
                Parser::new_typespec(TypeSpecKind::Builtin(TypeKeywordMask::DOUBLE)),
                None,
            )),
            KeywordKind::Void => Ok((
                Parser::new_typespec(TypeSpecKind::Builtin(TypeKeywordMask::VOID)),
                None,
            )),
            KeywordKind::Bool => Ok((
                Parser::new_typespec(TypeSpecKind::Builtin(TypeKeywordMask::BOOL)),
                None,
            )),
            KeywordKind::Struct => {
                let name = self.maybe_name()?;
                if self.eat_token(&TokenKind::LeftBrace)? {
                    let fields = self.parse_record_fields()?;
                    let mut struct_decl = Decl::Struct(ast::RecordDecl {
                        id: None,
                        name,
                        fields,
                        span,
                    });
                    let mut added = false;
                    let index = if let Some(name) = name {
                        if let Some(&idx) = self.struct_defs.get(&name) {
                            idx
                        } else {
                            let idx = self.globals.len();
                            self.struct_defs.insert(name, idx);
                            self.globals.push(struct_decl.clone());
                            added = true;
                            idx
                        }
                    } else {
                        let idx = self.globals.len();
                        self.globals.push(struct_decl.clone());
                        added = true;
                        idx
                    };
                    if let Decl::Struct(rec) = &mut struct_decl {
                        rec.id = Some(DeclId::new(index));
                    }
                    let type_spec = Parser::new_typespec(TypeSpecKind::Struct(DeclId::new(index)));
                    let struct_decl_opt = if added { None } else { Some(struct_decl) };
                    Ok((type_spec, struct_decl_opt))
                } else {
                    // Forward declaration
                    let index = if let Some(name) = name {
                        if let Some(&idx) = self.struct_defs.get(&name) {
                            idx
                        } else {
                            let idx = self.globals.len();
                            self.struct_defs.insert(name, idx);
                            // For forward, don't push yet
                            idx
                        }
                    } else {
                        // Anonymous forward? Not possible
                        0
                    };
                    let type_spec = Parser::new_typespec(TypeSpecKind::Struct(DeclId::new(index)));
                    Ok((type_spec, None))
                }
            }
            KeywordKind::Union => {
                let name = self.maybe_name()?;
                if self.eat_token(&TokenKind::LeftBrace)? {
                    let fields = self.parse_record_fields()?;
                    let mut union_decl = Decl::Union(ast::RecordDecl {
                        id: None,
                        name,
                        fields,
                        span,
                    });
                    let mut added = false;
                    let index = if let Some(name) = name {
                        if let Some(&idx) = self.union_defs.get(&name) {
                            idx
                        } else {
                            let idx = self.globals.len();
                            self.union_defs.insert(name, idx);
                            self.globals.push(union_decl.clone());
                            added = true;
                            idx
                        }
                    } else {
                        let idx = self.globals.len();
                        self.globals.push(union_decl.clone());
                        added = true;
                        idx
                    };
                    if let Decl::Union(rec) = &mut union_decl {
                        rec.id = Some(DeclId::new(index));
                    }
                    let type_spec = Parser::new_typespec(TypeSpecKind::Union(DeclId::new(index)));
                    let union_decl_opt = if added { None } else { Some(union_decl) };
                    Ok((type_spec, union_decl_opt))
                } else {
                    // Forward declaration
                    let index = if let Some(name) = name {
                        if let Some(&idx) = self.union_defs.get(&name) {
                            idx
                        } else {
                            let idx = self.globals.len();
                            self.union_defs.insert(name, idx);
                            // For forward, don't push yet
                            idx
                        }
                    } else {
                        // Anonymous forward? Not possible
                        0
                    };
                    let type_spec = Parser::new_typespec(TypeSpecKind::Union(DeclId::new(index)));
                    Ok((type_spec, None))
                }
            }
            KeywordKind::Enum => {
                let name = self.maybe_name()?;
                if self.eat_token(&TokenKind::LeftBrace)? {
                    let enumerators = self.parse_enum_specifier_members()?;
                    let mut enum_decl = Decl::Enum(ast::EnumDecl {
                        id: None,
                        name,
                        members: enumerators
                            .into_iter()
                            .map(|(name, value, span)| ast::EnumMember { name, value, span })
                            .collect(),
                        span,
                    });
                    let mut added = false;
                    let index = if let Some(name) = name {
                        if let Some(&idx) = self.enum_defs.get(&name) {
                            idx
                        } else {
                            let idx = self.globals.len();
                            self.enum_defs.insert(name, idx);
                            self.globals.push(enum_decl.clone());
                            added = true;
                            idx
                        }
                    } else {
                        let idx = self.globals.len();
                        self.globals.push(enum_decl.clone());
                        added = true;
                        idx
                    };
                    if let Decl::Enum(en) = &mut enum_decl {
                        en.id = Some(DeclId::new(index));
                    }
                    let type_spec = Parser::new_typespec(TypeSpecKind::Enum(DeclId::new(index)));
                    let enum_decl_opt = if added { None } else { Some(enum_decl) };
                    Ok((type_spec, enum_decl_opt))
                } else {
                    // Forward declaration
                    let index = if let Some(name) = name {
                        if let Some(&idx) = self.enum_defs.get(&name) {
                            idx
                        } else {
                            let idx = self.globals.len();
                            self.enum_defs.insert(name, idx);
                            // For forward, don't push yet
                            idx
                        }
                    } else {
                        // Anonymous forward? Not possible
                        0
                    };
                    let type_spec = Parser::new_typespec(TypeSpecKind::Enum(DeclId::new(index)));
                    Ok((type_spec, None))
                }
            }
            _ => {
                let token = self.current_token()?;
                Err(ParserError::UnexpectedToken(token))
            }
        }
    }

    /// Parses enum members without returning a full Type.
    fn parse_enum_specifier_members(
        &mut self,
    ) -> Result<ThinVec<(StringId, Option<Box<Expr>>, SourceSpan)>, ParserError> {
        let mut enumerators = ThinVec::new();
        if !self.eat_token(&TokenKind::RightBrace)? {
            loop {
                enumerators.push(self.parse_enumerator()?);
                if !self.eat_token(&TokenKind::Comma)? {
                    self.expect_punct(TokenKind::RightBrace)?;
                    break;
                }
                if self.eat_token(&TokenKind::RightBrace)? {
                    break;
                }
            }
        }
        Ok(enumerators)
    }

    /// Parses a single enumerator.
    fn parse_enumerator(
        &mut self,
    ) -> Result<(StringId, Option<Box<Expr>>, SourceSpan), ParserError> {
        let token = self.current_token()?;
        let name = self.expect_name()?;
        if self.eat_token(&TokenKind::Equal)? {
            let expr = self.parse_pratt_expr(2)?; // Assignment precedence
            Ok((name, Some(Box::new(expr)), token.span))
        } else {
            Ok((name, None, token.span))
        }
    }
    /// Parses members for struct or union.
    fn parse_record_fields(&mut self) -> Result<ThinVec<RecordFieldDecl>, ParserError> {
        let mut members = ThinVec::new();

        // Parse fields until we hit the closing brace
        while !self.eat_token(&TokenKind::RightBrace)? {
            // Skip any empty declarations or invalid tokens
            if let Ok(kind) = self.current_kind() {
                if matches!(kind, TokenKind::Semicolon) {
                    self.eat_token(&TokenKind::Semicolon)?;
                    continue;
                }

                // Try to parse a field declaration
                if let Ok(field_param) = self.parse_struct_field() {
                    members.push(field_param);
                } else {
                    // If parsing fails, skip the problematic token and continue
                    let _ = self.eat();
                }
            } else {
                // EOF or error, break out
                break;
            }
        }

        Ok(members)
    }

    /// Parses a single struct/union field
    fn parse_struct_field(&mut self) -> Result<RecordFieldDecl, ParserError> {
        let (base_type_spec, _) = self.parse_type_specifier()?;
        let (base, declarator) = self.parse_declarator_suffix(base_type_spec)?;
        let ty = self.apply_declarator_modifiers(&base, &declarator);
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(RecordFieldDecl { 
            type_spec: ty,
            name: declarator.name,
            span: declarator.span,
        })
    }

    /// Applies declarator modifiers to a base type spec to produce the final type spec.
    fn apply_declarator_modifiers(&self, base: &TypeSpec, declarator: &ast::Declarator) -> TypeSpec {
        let mut ty = base.clone();

        // 1. Update pointer depth (bits 16-23)
        let current_ptr_depth = ty.pointer_depth();
        let new_ptr_depth = current_ptr_depth.saturating_add(declarator.pointer_depth);
        ty.header = (ty.header & !0xFF0000) | ((new_ptr_depth as u32) << 16);

        // 2. Update qualifiers (bits 0-7)
        let current_qual = ty.qualifiers();
        let new_qual = current_qual | TypeQual::from_bits_truncate(declarator.qualifiers as u8);
        ty.header = (ty.header & !0xFF) | (new_qual.bits() as u32);

        // 3. Handle array dimensions (intern array_sizes and update array_exprs/array_rank)
        if !declarator.array_sizes.is_empty() {
            let array_id = ArrayExprListInterner::intern(declarator.array_sizes.clone());
            let current_rank = ty.array_rank();
            let new_rank = current_rank.saturating_add(declarator.array_sizes.len() as u8);
            
            // Update array_exprs
            ty = ty.with_array_exprs(array_id);

            // Update array_rank (bits 24-31)
            ty.header = (ty.header & !0xFF000000) | ((new_rank as u32) << 24);
        }

        // 4. Recurse for inner declarator
        if let Some(inner) = &declarator.inner {
            ty = self.apply_declarator_modifiers(&ty, inner);
        }
        ty
    }

    /// Helper function to recursively extract the name from the innermost declarator.
    fn get_declarator_name(&self, declarator: &ast::Declarator) -> Option<StringId> {
        if let Some(name) = declarator.name {
            Some(name)
        } else if let Some(inner) = &declarator.inner {
            self.get_declarator_name(inner)
        } else {
            None
        }
    }

    /// Parses declarator suffixes (pointers and arrays) and returns the base type and declarator.
    /// This function assumes the base type has already been parsed.
    fn parse_declarator_suffix(
        &mut self,
        base_type_spec: crate::types::TypeSpec,
    ) -> Result<(crate::types::TypeSpec, ast::Declarator), ParserError> {
        let mut pointer_depth = 0;
        let mut qualifiers = 0;
        // Parse pointers and their qualifiers
        while let Ok(token) = self.current_token() {
            if token.kind == TokenKind::Star {
                self.eat()?;
                pointer_depth += 1;
                while let Ok(token) = self.current_token() {
                    if token.kind == TokenKind::Keyword(KeywordKind::Const) {
                        self.eat()?;
                        qualifiers |= TypeQual::CONST.bits();
                    } else if token.kind == TokenKind::Keyword(KeywordKind::Volatile) {
                        self.eat()?;
                        qualifiers |= TypeQual::VOLATILE.bits();
                    } else if token.kind == TokenKind::Keyword(KeywordKind::Restrict) {
                        self.eat()?;
                        qualifiers |= TypeQual::RESTRICT.bits();
                    } else {
                        break;
                    }
                }
            } else {
                break;
            }
        }

        // Parse optional parenthesized inner declarator
        let inner = if self.eat_token(&TokenKind::LeftParen)? {
            let (_, inner_decl) = self.parse_declarator_suffix(base_type_spec.clone())?;
            self.expect_punct(TokenKind::RightParen)?;
            Some(Box::new(inner_decl))
        } else {
            None
        };

        let id_token = self.current_token()?;
        let (name, span) = if let TokenKind::Identifier(id) = id_token.kind.clone() {
            self.eat()?;
            (Some(id), id_token.span)
        } else {
            (None, id_token.span)
        };

        // Function parameters are NOT parsed here - they are handled in parse_function_signature
        
        // Parse array dimensions
        let mut array_sizes = ThinVec::new();
        while let Ok(token) = self.current_token() {
            if token.kind == TokenKind::LeftBracket {
                self.eat()?;
                let size_expr = if self.eat_token(&TokenKind::RightBracket)? {
                    // Unsized array
                    Expr::Number(0, token.span)
                } else {
                    let expr = self.parse_expr()?;
                    self.expect_punct(TokenKind::RightBracket)?;
                    expr
                };
                array_sizes.push(size_expr);
            } else {
                break;
            }
        }
        let mut declarator = ast::Declarator {
            name,
            pointer_depth,
            array_sizes,
            func_params: None,  // Function parameters are handled separately
            is_variadic: false, // Function parameters are handled separately
            qualifiers: qualifiers as u16,
            inner,
            init: None,
            span,
        };

        // Propagate name and pointer depth from inner declarator if outer has no name
        if declarator.name.is_none() {
            if let Some(inner) = &mut declarator.inner {
                declarator.name = self.get_declarator_name(inner);
                declarator.pointer_depth += inner.pointer_depth;
                inner.pointer_depth = 0;
            }
        }

        Ok((base_type_spec, declarator))
    }

    /// Parses a declarator with optional initializer.
    fn parse_declarator(
        &mut self,
        base_type_spec: crate::types::TypeSpec,
    ) -> Result<ast::Declarator, ParserError> {
        let (base, mut declarator) = self.parse_declarator_suffix(base_type_spec)?;
        declarator.init = self.parse_initializer_expr()?.map(|i| Box::new(match i {
            Initializer::Expr(expr) => *expr,
            Initializer::List(list) => Expr::InitializerList(list),
        }));

        Ok(declarator)
    }

    /// parse initializer expression
    fn parse_initializer_expr(&mut self) -> Result<Option<Initializer>, ParserError> {
        self.maybe_start(&TokenKind::Equal, |p| p.parse_initializer())
    }

    /// Parses a C initializer.
    fn parse_initializer(&mut self) -> Result<Initializer, ParserError> {
        if self.eat_token(&TokenKind::LeftBrace)? {
            let list = self.parse_initializer_list()?;
            self.expect_punct(TokenKind::RightBrace)?;
            Ok(Initializer::List(list))
        } else {
            let expr = self.parse_pratt_expr(2)?; // Assignment precedence
            Ok(Initializer::Expr(Box::new(expr)))
        }
    }

    /// Parses a type. This function now orchestrates `parse_type_specifier` and `parse_declarator_suffix`.
    fn parse_type(&mut self) -> Result<crate::types::TypeSpec, ParserError> {
        let (base_type_spec, _) = self.parse_type_specifier()?;
        // For abstract declarators (e.g., `int *`), there might not be an identifier immediately.
        // This function is primarily for parsing a full type with a declarator.
        // If we are just parsing a type for a cast or sizeof, we might not have an identifier.
        // The `is_type_name` function will handle backtracking if no identifier is found.
        let original_pos = self.position;
        if let Ok(kind) = self.current_kind()
            && matches!(kind, TokenKind::Star | TokenKind::LeftBracket | TokenKind::Identifier(_))
            && let Ok((base, declarator)) = self.parse_declarator_suffix(base_type_spec.clone())
        {
            let type_spec = self.apply_declarator_modifiers(&base, &declarator);
            return Ok(type_spec);
        }
        self.position = original_pos; // Backtrack if no declarator suffix found
        Ok(base_type_spec)
    }

    /// Parses an expression.
    fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        self.parse_pratt_expr(0)
    }

    /// Gets the prefix binding power of a token.
    fn prefix_binding_power(&self, kind: &TokenKind) -> Option<((), u8)> {
        match kind {
            TokenKind::Plus | TokenKind::Minus | TokenKind::PlusPlus | TokenKind::MinusMinus => {
                Some(((), 15))
            }
            TokenKind::Bang | TokenKind::Tilde => Some(((), 15)),
            TokenKind::Keyword(KeywordKind::Sizeof) => Some(((), 15)),
            TokenKind::Keyword(KeywordKind::Alignof) => Some(((), 15)),
            TokenKind::Keyword(KeywordKind::_Generic) => Some(((), 15)),
            _ => None,
        }
    }

    /// Gets the postfix binding power of a token.
    fn postfix_binding_power(&self, kind: &TokenKind) -> Option<(u8, ())> {
        match kind {
            TokenKind::PlusPlus | TokenKind::MinusMinus => Some((17, ())),
            _ => None,
        }
    }

    /// Gets the infix binding power of a token.
    fn infix_binding_power(&self, kind: &TokenKind) -> Option<(u8, u8)> {
        match kind {
            TokenKind::Comma => Some((2, 1)),
            TokenKind::PipePipe => Some((3, 4)),
            TokenKind::AmpersandAmpersand => Some((5, 6)),
            TokenKind::Pipe => Some((7, 8)),
            TokenKind::Caret => Some((9, 10)),
            TokenKind::Ampersand => Some((11, 12)),
            TokenKind::EqualEqual | TokenKind::BangEqual => Some((13, 14)),
            TokenKind::LessThan
            | TokenKind::GreaterThan
            | TokenKind::LessThanEqual
            | TokenKind::GreaterThanEqual => Some((15, 16)),
            TokenKind::LessThanLessThan | TokenKind::GreaterThanGreaterThan => Some((17, 18)),
            TokenKind::Plus | TokenKind::Minus => Some((19, 20)),
            TokenKind::Star | TokenKind::Slash | TokenKind::Percent => Some((21, 22)),
            TokenKind::Arrow | TokenKind::Dot => Some((23, 24)),
            TokenKind::Equal
            | TokenKind::PlusEqual
            | TokenKind::MinusEqual
            | TokenKind::AsteriskEqual
            | TokenKind::SlashEqual
            | TokenKind::PercentEqual
            | TokenKind::LessThanLessThanEqual
            | TokenKind::GreaterThanGreaterThanEqual
            | TokenKind::AmpersandEqual
            | TokenKind::CaretEqual
            | TokenKind::PipeEqual => Some((4, 3)),
            _ => None,
        }
    }
    /// Creates a binary expression based on the operator token.
    fn create_binary_expr(&self, lhs: Expr, rhs: Expr, op: TokenKind) -> Result<Expr, ParserError> {
        if op.is_assignment() {
            let lhs = Box::new(lhs);
            let rhs = Box::new(rhs);
            match op {
                TokenKind::Equal => Ok(Expr::Assign(lhs, rhs)),
                TokenKind::PlusEqual => Ok(Expr::AssignAdd(lhs, rhs)),
                TokenKind::MinusEqual => Ok(Expr::AssignSub(lhs, rhs)),
                TokenKind::AsteriskEqual => Ok(Expr::AssignMul(lhs, rhs)),
                TokenKind::SlashEqual => Ok(Expr::AssignDiv(lhs, rhs)),
                TokenKind::PercentEqual => Ok(Expr::AssignMod(lhs, rhs)),
                TokenKind::LessThanLessThanEqual => Ok(Expr::AssignLeftShift(lhs, rhs)),
                TokenKind::GreaterThanGreaterThanEqual => Ok(Expr::AssignRightShift(lhs, rhs)),
                TokenKind::AmpersandEqual => Ok(Expr::AssignBitwiseAnd(lhs, rhs)),
                TokenKind::CaretEqual => Ok(Expr::AssignBitwiseXor(lhs, rhs)),
                TokenKind::PipeEqual => Ok(Expr::AssignBitwiseOr(lhs, rhs)),
                _ => unreachable!(),
            }
        } else {
            let lhs = Box::new(lhs);
            let rhs = Box::new(rhs);
            match op {
                TokenKind::Comma => Ok(Expr::Comma(lhs, rhs)),
                TokenKind::Plus => Ok(Expr::Add(lhs, rhs)),
                TokenKind::Minus => Ok(Expr::Sub(lhs, rhs)),
                TokenKind::Star => Ok(Expr::Mul(lhs, rhs)),
                TokenKind::Slash => Ok(Expr::Div(lhs, rhs)),
                TokenKind::Percent => Ok(Expr::Mod(lhs, rhs)),
                TokenKind::EqualEqual => Ok(Expr::Equal(lhs, rhs)),
                TokenKind::BangEqual => Ok(Expr::NotEqual(lhs, rhs)),
                TokenKind::LessThan => Ok(Expr::LessThan(lhs, rhs)),
                TokenKind::GreaterThan => Ok(Expr::GreaterThan(lhs, rhs)),
                TokenKind::LessThanEqual => Ok(Expr::LessThanOrEqual(lhs, rhs)),
                TokenKind::GreaterThanEqual => Ok(Expr::GreaterThanOrEqual(lhs, rhs)),
                TokenKind::AmpersandAmpersand => Ok(Expr::LogicalAnd(lhs, rhs)),
                TokenKind::PipePipe => Ok(Expr::LogicalOr(lhs, rhs)),
                TokenKind::Pipe => Ok(Expr::BitwiseOr(lhs, rhs)),
                TokenKind::Caret => Ok(Expr::BitwiseXor(lhs, rhs)),
                TokenKind::Ampersand => Ok(Expr::BitwiseAnd(lhs, rhs)),
                TokenKind::LessThanLessThan => Ok(Expr::LeftShift(lhs, rhs)),
                TokenKind::GreaterThanGreaterThan => Ok(Expr::RightShift(lhs, rhs)),
                _ => unreachable!(),
            }
        }
    }

    /// Parses an expression using the Pratt parsing algorithm.
    fn parse_pratt_expr(&mut self, min_bp: u8) -> Result<Expr, ParserError> {
        let mut lhs = if let Some(((), r_bp)) = self.prefix_binding_power(&self.current_kind()?) {
            let kind = self.current_kind()?;
            self.eat()?;
            match kind {
                TokenKind::PlusPlus => {
                    let expr = self.parse_pratt_expr(r_bp)?;
                    Expr::PreIncrement(Box::new(expr))
                }
                TokenKind::MinusMinus => {
                    let expr = self.parse_pratt_expr(r_bp)?;
                    Expr::PreDecrement(Box::new(expr))
                }
                TokenKind::Plus => self.parse_pratt_expr(r_bp)?,
                TokenKind::Minus => {
                    let rhs = self.parse_pratt_expr(r_bp)?;
                    Expr::Neg(Box::new(rhs))
                }
                TokenKind::Bang => {
                    let rhs = self.parse_pratt_expr(r_bp)?;
                    Expr::LogicalNot(Box::new(rhs))
                }
                TokenKind::Tilde => {
                    let rhs = self.parse_pratt_expr(r_bp)?;
                    Expr::BitwiseNot(Box::new(rhs))
                }
                TokenKind::Keyword(KeywordKind::Sizeof) => {
                    if self.eat_token(&TokenKind::LeftParen)? {
                        let expr = if self.is_type_name() {
                            let ty = self.parse_type()?;
                            Expr::SizeofType(ty)
                        } else {
                            let expr = self.parse_expr()?;
                            Expr::Sizeof(Box::new(expr))
                        };
                        self.expect_punct(TokenKind::RightParen)?;
                        expr
                    } else {
                        let expr = self.parse_pratt_expr(r_bp)?;
                        Expr::Sizeof(Box::new(expr))
                    }
                }
                TokenKind::Keyword(KeywordKind::Alignof) => {
                    if self.eat_token(&TokenKind::LeftParen)? {
                        let expr = if self.is_type_name() {
                            let ty = self.parse_type()?;
                            Expr::AlignofType(ty)
                        } else {
                            let expr = self.parse_expr()?;
                            Expr::Alignof(Box::new(expr))
                        };
                        self.expect_punct(TokenKind::RightParen)?;
                        expr
                    } else {
                        let expr = self.parse_pratt_expr(r_bp)?;
                        Expr::Alignof(Box::new(expr))
                    }
                }
                TokenKind::Keyword(KeywordKind::_Generic) => {
                    self.expect_punct(TokenKind::LeftParen)?;
                    let controlling_expr = self.parse_expr()?;
                    self.expect_punct(TokenKind::Comma)?;
                    let mut associations = Vec::new();
                    loop {
                        let ty = if self.eat_token(&TokenKind::Keyword(KeywordKind::Default))? {
                            None
                        } else {
                            Some(self.parse_type()?)
                        };
                        self.expect_punct(TokenKind::Colon)?;
                        let expr = self.parse_expr()?;
                        associations.push((ty, Box::new(expr)));
                        if !self.eat_token(&TokenKind::Comma)? {
                            break;
                        }
                    }
                    self.expect_punct(TokenKind::RightParen)?;
                    Expr::Generic(Box::new(controlling_expr), associations)
                }
                _ => unreachable!(),
            }
        } else {
            self.parse_primary()?
        };

        loop {
            let kind = self.current_kind()?;
            if let Some((l_bp, ())) = self.postfix_binding_power(&kind) {
                if l_bp <= min_bp {
                    break;
                }

                self.eat()?;

                lhs = match kind {
                    TokenKind::PlusPlus => Expr::PostIncrement(Box::new(lhs)),
                    TokenKind::MinusMinus => Expr::PostDecrement(Box::new(lhs)),
                    _ => unreachable!(),
                };
                continue;
            }
            if let Some((l_bp, r_bp)) = self.infix_binding_power(&kind) {
                if l_bp <= min_bp {
                    break;
                }

                self.eat()?;
                let rhs = self.parse_pratt_expr(r_bp)?;

                lhs = match kind {
                    TokenKind::Arrow => {
                        if let Expr::Variable(name, _) = rhs {
                            Expr::PointerMember(Box::new(lhs), name)
                        } else {
                            let token = self.current_token()?;
                            return Err(ParserError::UnexpectedToken(token));
                        }
                    }
                    TokenKind::Dot => {
                        if let Expr::Variable(name, _) = rhs {
                            Expr::Member(Box::new(lhs), name)
                        } else {
                            let token = self.current_token()?;
                            return Err(ParserError::UnexpectedToken(token));
                        }
                    }
                    _ => self.create_binary_expr(lhs, rhs, kind)?,
                };
                continue;
            }
            if kind == TokenKind::Question {
                let (l_bp, r_bp) = (5, 4);
                if l_bp < min_bp {
                    break;
                }
                self.eat()?; // Consume '?'
                let then_expr = self.parse_pratt_expr(0)?;
                self.expect_punct(TokenKind::Colon)?;
                let else_expr = self.parse_pratt_expr(r_bp)?;
                lhs = Expr::Ternary(Box::new(lhs), Box::new(then_expr), Box::new(else_expr));
                continue;
            }
            break;
        }
        Ok(lhs)
    }

    /// Parses a primary expression.
    fn parse_primary(&mut self) -> Result<Expr, ParserError> {
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::Number(n) => {
                self.eat()?;
                let num_str = n.as_str();
                if num_str.contains('.') || num_str.contains('e') || num_str.contains('E') {
                    let trimmed = num_str.trim_end_matches(['f', 'F', 'l', 'L']);
                    Ok(Expr::FloatNumber(trimmed.parse().unwrap(), token.span))
                } else {
                    let trimmed = num_str.trim_end_matches(['L', 'U', 'l', 'u']);
                    Ok(Expr::Number(trimmed.parse().unwrap(), token.span))
                }
            }
            TokenKind::String(s) => {
                self.eat()?;
                Ok(Expr::String(s, token.span))
            }
            TokenKind::Char(s) => {
                self.eat()?;
                Ok(Expr::Char(s, token.span))
            }
            TokenKind::Identifier(name) => {
                self.eat()?;
                let mut expr = Expr::Variable(name, token.span);
                while let Ok(token) = self.current_token() {
                    match token.kind {
                        TokenKind::LeftParen => {
                            let location = if let Expr::Variable(_, span) = expr {
                                span
                            } else {
                                token.span
                            };
                            let token_for_error = token.clone();
                            self.eat()?; // consume '('
                            let mut args = ThinVec::new();
                            if self.current_token()?.kind != TokenKind::RightParen {
                                loop {
                                    // Use a binding power of 2 to stop parsing at a comma
                                    args.push(self.parse_pratt_expr(2)?);
                                    if self.current_token()?.kind == TokenKind::RightParen {
                                        break;
                                    }
                                    self.expect_punct(TokenKind::Comma)?;
                                }
                            }
                            self.expect_punct(TokenKind::RightParen)?;
                            let name = match expr {
                                Expr::Variable(name, _) => name,
                                _ => return Err(ParserError::UnexpectedToken(token_for_error)),
                            };
                            expr = Expr::Call(name, args, location);
                        }
                        TokenKind::LeftBracket => {
                            self.eat()?;
                            let index = self.parse_expr()?;
                            self.expect_punct(TokenKind::RightBracket)?;
                            expr =
                                Expr::Deref(Box::new(Expr::Add(Box::new(expr), Box::new(index))));
                        }
                        _ => break,
                    }
                }
                Ok(expr)
            }
            TokenKind::Star => {
                self.eat()?;
                let expr = self.parse_pratt_expr(27)?;
                Ok(Expr::Deref(Box::new(expr)))
            }
            TokenKind::Ampersand => {
                self.eat()?;
                let expr = self.parse_pratt_expr(27)?;
                Ok(Expr::AddressOf(Box::new(expr)))
            }
            TokenKind::Minus => {
                self.eat()?;
                let expr = self.parse_pratt_expr(7)?;
                Ok(Expr::Neg(Box::new(expr)))
            }
            TokenKind::Plus => {
                self.eat()?;
                self.parse_pratt_expr(7)
            }
            TokenKind::Bang => {
                self.eat()?;
                let expr = self.parse_pratt_expr(15)?;
                Ok(Expr::LogicalNot(Box::new(expr)))
            }
            TokenKind::LeftParen => {
                self.eat()?; // Consume '('

                // Check for cast or compound literal
                let pos = self.position;
                let is_type = if let Ok(_ty) = self.parse_type() {
                    if let Ok(token) = self.current_token() {
                        token.kind == TokenKind::RightParen
                    } else {
                        false
                    }
                } else {
                    false
                };
                self.position = pos; // backtrack after peeking

                if is_type {
                    let param_ty = self.parse_type()?;
                    self.expect_punct(TokenKind::RightParen)?;

                    if let Ok(TokenKind::LeftBrace) = self.current_kind() {
                        // Compound Literal: (type){...}
                        let initializer = self.parse_initializer()?;
                        Ok(Expr::CompoundLiteral(
                            Box::new(param_ty),
                            Box::new(initializer),
                        ))
                    } else {
                        // Cast: (type)expr
                        let expr = self.parse_pratt_expr(15)?; // High precedence for cast's operand
                        Ok(Expr::ExplicitCast(Box::new(param_ty), Box::new(expr)))
                    }
                } else {
                    // Grouped expression: (expr)
                    let expr = self.parse_expr()?;
                    self.expect_punct(TokenKind::RightParen)?;
                    Ok(expr)
                }
            }
            TokenKind::LeftBrace => {
                let initializers = self.parse_initializer_list()?;
                self.expect_punct(TokenKind::RightBrace)?;
                Ok(Expr::InitializerList(initializers))
            }
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }

    fn parse_designator(&mut self) -> Result<ThinVec<Designator>, ParserError> {
        let mut designators = ThinVec::new();
        loop {
            if self.eat_token(&TokenKind::Dot)? {
                let member = self.expect_name()?;
                designators.push(Designator::Member(member));
            } else if self.eat_token(&TokenKind::LeftBracket)? {
                let index = self.parse_expr()?;
                self.expect_punct(TokenKind::RightBracket)?;
                designators.push(Designator::Index(Box::new(index)));
            } else {
                break;
            }
        }
        Ok(designators)
    }

    /// Parses an initializer list.
    fn parse_initializer_list(&mut self) -> Result<InitializerList, ParserError> {
        let mut initializers = ThinVec::new();
        if self.eat_token(&TokenKind::RightBrace)? {
            return Ok(initializers);
        }

        loop {
            let designators = self.parse_designator()?;
            let initializer = if !designators.is_empty() {
                self.expect_punct(TokenKind::Equal)?;
                self.parse_initializer()?
            } else {
                // Use a binding power of 2 to stop parsing at a comma
                Initializer::Expr(Box::new(self.parse_pratt_expr(2)?))
            };
            initializers.push((designators, Box::new(initializer)));

            if !self.eat_token(&TokenKind::Comma)? {
                break;
            }

            if self.eat_token(&TokenKind::RightBrace)? {
                break;
            }
        }
        Ok(initializers)
    }

    /// Parses a statement.
    fn parse_stmt(&mut self) -> Result<Stmt, ParserError> {
        if self.current_kind()? == TokenKind::Keyword(KeywordKind::StaticAssert) {
            // Static assert in statements should be handled differently, but for now, we'll skip it
            let decl = self.parse_static_assert()?;
            if let Decl::StaticAssert(expr, msg) = decl {
                return Ok(Stmt::Declaration(Decl::StaticAssert(expr, msg)));
            } else {
                return Ok(Stmt::Empty);
            }
        }
        if self.current_kind()? == TokenKind::Keyword(KeywordKind::Static) {
            let (base_type_spec, _) = self.parse_type_specifier()?;
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::Empty);
            }
            let mut declarators = ThinVec::new();
            loop {
                let declarator = self.parse_declarator(base_type_spec.clone())?;
                declarators.push(declarator);

                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(Decl::VarGroup(base_type_spec, declarators)));
        }

        if self.is_type_name() && self.peek()? != TokenKind::LeftParen {
            let (base_type_spec, _) = self.parse_type_specifier()?;
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::Empty);
            }
            let mut declarators = ThinVec::new();
            loop {
                let declarator = self.parse_declarator(base_type_spec.clone())?;
                declarators.push(declarator);

                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(Decl::VarGroup(base_type_spec, declarators)));
        }
        let token = self.current_token()?;
        if let TokenKind::LeftBrace = token.kind.clone() {
            self.eat()?;
            let mut stmts = ThinVec::new();
            while self.eat_token(&TokenKind::RightBrace)? == false {
                stmts.push(self.parse_stmt()?);
            }
            return Ok(Stmt::Block(stmts));
        } else if self.eat_token(&TokenKind::Keyword(KeywordKind::Static))? {
            let (base_type_spec, _) = self.parse_type_specifier()?;
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::Empty);
            }
            let mut declarators = ThinVec::new();
            loop {
                let declarator = self.parse_declarator(base_type_spec.clone())?;
                declarators.push(declarator);

                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(Decl::VarGroup(base_type_spec, declarators)));
        }

        if self.is_type_name() && self.peek()? != TokenKind::LeftParen {
            let (base_type_spec, _) = self.parse_type_specifier()?;
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok(Stmt::Empty);
            }
            let mut declarators = ThinVec::new();
            loop {
                let declarator = self.parse_declarator(base_type_spec.clone())?;
                declarators.push(declarator);

                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            return Ok(Stmt::Declaration(Decl::VarGroup(base_type_spec, declarators)));
        }

        if let TokenKind::Keyword(k) = token.kind {
            if k == KeywordKind::Return {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Return(Box::new(expr)));
            } else if k == KeywordKind::If {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let then = self.parse_stmt()?;
                let else_stmt = self.maybe_start(&TokenKind::Keyword(KeywordKind::Else), |p| {
                    Ok(Box::new(p.parse_stmt()?))
                })?;
                return Ok(Stmt::If(Box::new(cond), Box::new(then), else_stmt));
            } else if k == KeywordKind::While {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let body = self.parse_stmt()?;
                return Ok(Stmt::While(Box::new(cond), Box::new(body)));
            } else if k == KeywordKind::For {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;

                let init = self.maybe_end(&TokenKind::Semicolon, |p| {
                    if p.eat_token(&TokenKind::Keyword(KeywordKind::Static))? {
                        return Err(ParserError::UnexpectedToken(p.current_token()?));
                    }
                    let result = if let Ok((type_spec, _)) = p.parse_type_specifier() {
                        let id = p.expect_name()?;
                        let initializer = p.parse_initializer_expr()?;
                        ForInit::Declaration(type_spec, id, initializer)
                    } else {
                        ForInit::Expr(p.parse_expr()?)
                    };

                    Ok(Box::new(result))
                })?;

                let cond =
                    self.maybe_end(&TokenKind::Semicolon, |p| Ok(Box::new(p.parse_expr()?)))?;
                let inc =
                    self.maybe_end(&TokenKind::RightParen, |p| Ok(Box::new(p.parse_expr()?)))?;
                let body = self.parse_stmt()?;

                return Ok(Stmt::For(init, cond, inc, Box::new(body)));
            } else if k == KeywordKind::Switch {
                self.eat()?;
                self.expect_punct(TokenKind::LeftParen)?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Switch(Box::new(expr), Box::new(stmt)));
            } else if k == KeywordKind::Case {
                self.eat()?;
                let expr = self.parse_expr()?;
                self.expect_punct(TokenKind::Colon)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Case(Box::new(expr), Box::new(stmt)));
            } else if k == KeywordKind::Default {
                self.eat()?;
                self.expect_punct(TokenKind::Colon)?;
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Default(Box::new(stmt)));
            } else if k == KeywordKind::Goto {
                self.eat()?;
                let token = self.current_token()?;
                let id = self.expect_name()?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Goto(id, token.span));
            } else if k == KeywordKind::Break {
                return self.parse_simple_statement(Stmt::Break);
            } else if k == KeywordKind::Continue {
                return self.parse_simple_statement(Stmt::Continue);
            } else if k == KeywordKind::Do {
                self.eat()?;
                let body = self.parse_stmt()?;
                self.expect_keyword(KeywordKind::While)?;
                self.expect_punct(TokenKind::LeftParen)?;
                let cond = self.parse_expr()?;
                self.expect_punct(TokenKind::RightParen)?;
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::DoWhile(Box::new(body), Box::new(cond)));
            } else if k == KeywordKind::Typedef {
                self.eat()?;
                let (base_type_spec, _) = self.parse_type_specifier()?;
                loop {
                    let (base, declarator) = self.parse_declarator_suffix(base_type_spec.clone())?;
                    let type_spec = self.apply_declarator_modifiers(&base, &declarator);
                    let name = declarator.name.unwrap_or_else(|| crate::parser::string_interner::StringInterner::empty_id());
                    self.typedefs.insert(name, (type_spec, DeclId::new(0)));
                    if !self.eat_token(&TokenKind::Comma)? {
                        break;
                    }
                }
                self.expect_punct(TokenKind::Semicolon)?;
                return Ok(Stmt::Empty);
            }
        }

        // Check for a label
        let pos = self.position;
        if let Ok(TokenKind::Identifier(id)) = self.current_kind() {
            let token = self.current_token()?;
            self.eat()?;
            if self.eat_token(&TokenKind::Colon)? {
                let stmt = self.parse_stmt()?;
                return Ok(Stmt::Label(id, Box::new(stmt), token.span));
            }
            self.position = pos;
        }

        if self.eat_token(&TokenKind::Semicolon)? {
            return Ok(Stmt::Empty);
        }

        let expr = self.parse_expr()?;
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(Stmt::Expr(Box::new(expr)))
    }
    /// Parses a simple statement like Break or Continue.
    fn parse_simple_statement(&mut self, stmt: Stmt) -> Result<Stmt, ParserError> {
        self.eat()?; // eat the keyword
        self.expect_punct(TokenKind::Semicolon)?;
        Ok(stmt)
    }

    /// Parses a function signature.
    fn parse_function_signature(&mut self) -> Result<FuncSignature, ParserError> {
        let (base_type_spec, _) = self.parse_type_specifier()?;

        // Parse declarator suffix (including pointers, arrays, and function name)
        let (base, declarator) = self.parse_declarator_suffix(base_type_spec)?;
        let type_spec = self.apply_declarator_modifiers(&base, &declarator);
        let id = declarator.name.unwrap_or_else(|| crate::parser::string_interner::StringInterner::empty_id());

        self.expect_punct(TokenKind::LeftParen)?;
        let mut params = ThinVec::new();
        let mut is_variadic = false;
        while self.eat_token(&TokenKind::RightParen)? == false {
            if self.eat_token(&TokenKind::Ellipsis)? {
                is_variadic = true;
                // Expect a closing parenthesis after ...
                self.expect_punct(TokenKind::RightParen)?;
                break;
            }
            let (base_type, _) = self.parse_type_specifier()?;
            let declarator = self.parse_declarator(base_type.clone())?;
            let ty = self.apply_declarator_modifiers(&base_type, &declarator);
            params.push(ast::ParamDecl {
                name: declarator.name.unwrap_or_else(|| crate::parser::string_interner::StringInterner::empty_id()),
                type_spec: ty,
                span: declarator.span,
            });

            if !self.eat_token(&TokenKind::Comma)? {
                self.expect_punct(TokenKind::RightParen)?;
                break;
            }
        }
        let param_decls: ThinVec<ast::ParamDecl> = params.into_iter().map(|p| ast::ParamDecl {
            name: p.name,
            type_spec: p.type_spec,
            span: p.span,
        }).collect();
        Ok(FuncSignature(
            type_spec,
            id,
            param_decls,
            false, // is_inline - handled in external declaration
            is_variadic,
            false, // is_noreturn - handled in external declaration
        ))
    }

    /// Parses a function.
    fn parse_function(&mut self, signature: FuncSignature) -> Result<FuncDecl, ParserError> {
        let FuncSignature(return_type_spec, name, params, is_inline, is_variadic, is_noreturn) =
            signature;

        let body = if self.eat_token(&TokenKind::LeftBrace)?{
            let mut stmts = ThinVec::new();
            while self.eat_token(&TokenKind::RightBrace)? == false {
                stmts.push(self.parse_stmt()?);
            }
            Some(stmts)
        }else{
            None
        };
        Ok(FuncDecl {
            return_type: return_type_spec,
            name,
            params,
            body,
            is_inline,
            is_variadic,
            is_noreturn,
            span: SourceSpan::default(),
        })
    }

    /// Parses a translation unit (the entire C program).
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `TranslationUnit`, or a `ParserError` if parsing fails.
    /// Parses a translation unit (the entire C program).
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `TranslationUnit`, or a `ParserError` if parsing fails.
    pub fn parse_translation_unit(&mut self) -> Result<TranslationUnit, ParserError> {
        self.globals.clear();
        while self.current_token()?.kind != TokenKind::Eof {
            let (mut global, additional_decls) = self.parse_external_declaration()?;

            // Assign DeclId based on current length of globals
            let current_index = self.globals.len();
            match &mut global {
                ast::Decl::Struct(rec) => rec.id = Some(crate::types::DeclId::new(current_index)),
                ast::Decl::Union(rec) => rec.id = Some(crate::types::DeclId::new(current_index)),
                ast::Decl::Enum(en) => en.id = Some(crate::types::DeclId::new(current_index)),
                ast::Decl::Typedef { id, .. } => *id = Some(crate::types::DeclId::new(current_index)),
                _ => {}
            }
            self.globals.push(global);

            // Update typedefs if it's a typedef
            if let Some(Decl::Typedef { name, ty, id: Some(id) }) = self.globals.last() {
                self.typedefs.insert(*name, (ty.clone(), *id));
            }

            // If there are additional declarations (like variables after enum definition),
            // add them to the globals list
            if let Some(additional) = additional_decls {
                for mut decl in additional.into_iter() {
                    let current_index = self.globals.len();
                    match &mut decl {
                        ast::Decl::Struct(rec) => rec.id = Some(crate::types::DeclId::new(current_index)),
                        ast::Decl::Union(rec) => rec.id = Some(crate::types::DeclId::new(current_index)),
                        ast::Decl::Enum(en) => en.id = Some(crate::types::DeclId::new(current_index)),
                        ast::Decl::Typedef { id, .. } => *id = Some(crate::types::DeclId::new(current_index)),
                        _ => {}
                    }
                    self.globals.push(decl);
                }
            }
        }
        Ok(TranslationUnit { globals: self.globals.clone() })
    }

    /// Parses an external declaration (function or variable declaration at global scope).
    ///
    /// # Returns
    ///
    /// A `Result` containing the parsed `Decl`, or a `ParserError` if parsing fails.
    fn parse_external_declaration(&mut self) -> Result<(Decl, Option<ThinVec<Decl>>), ParserError> {
        // Try to parse function specifiers first
        let mut is_inline = false;
        let mut is_noreturn = false;
        loop {
            if self.eat_token(&TokenKind::Keyword(KeywordKind::Inline))? {
                is_inline = true;
            } else if self.eat_token(&TokenKind::Keyword(KeywordKind::_Noreturn))? {
                is_noreturn = true;
            } else {
                break;
            }
        }

        let pos = self.position;
        if let Ok(signature) = self.parse_function_signature() {
            if self.eat_token(&TokenKind::Semicolon)? {
                return Ok((
                    Decl::Func(FuncDecl {
                        name: signature.1,
                        return_type: signature.0,
                        params: signature.2
                            .into_iter()
                            .map(|p| ast::ParamDecl {
                                name: p.name,
                                type_spec: p.type_spec,
                                span: p.span,
                            })
                            .collect(),
                        body: None,
                        is_variadic: signature.5,
                        is_inline: signature.3 || is_inline,
                        is_noreturn: signature.4 || is_noreturn,
                        span: SourceSpan::default(),
                    }),
                    None
                ));
            } else {
                // Function definition with body
                let mut func = self.parse_function(signature)?;
                func.is_inline |= is_inline;
                func.is_noreturn |= is_noreturn;
                return Ok((Decl::Func(func), None));
            }
        }
        self.position = pos;

        if self.eat_token(&TokenKind::Keyword(KeywordKind::Typedef))? {
            let (base_type_spec, _) = self.parse_type_specifier()?;
            let mut typedefs = ThinVec::new();
            loop {
                let (base, declarator) = self.parse_declarator_suffix(base_type_spec.clone())?;
                let type_spec = self.apply_declarator_modifiers(&base, &declarator);
                let name = declarator.name.unwrap_or_else(|| crate::parser::string_interner::StringInterner::empty_id());
                self.typedefs.insert(name, (type_spec.clone(), DeclId::new(0))); // placeholder
                typedefs.push((name, type_spec));
                if !self.eat_token(&TokenKind::Comma)? {
                    break;
                }
            }
            self.expect_punct(TokenKind::Semicolon)?;
            // Return the first typedef, or handle multiple
            if let Some((name, type_spec)) = typedefs.into_iter().next() {
                return Ok((Decl::Typedef { name, ty: type_spec, id: None }, None));
            } else {
                return Ok((Decl::Typedef {
                    name: crate::parser::string_interner::StringInterner::empty_id(),
                    ty: base_type_spec,
                    id: None,
                }, None));
            }
        }

        let is_static = self.eat_token(&TokenKind::Keyword(KeywordKind::Static))?;
        let (base_type_spec, decl_opt) = self.parse_type_specifier()?;
        if self.eat_token(&TokenKind::Semicolon)? {
            // Forward declaration or empty declaration
            if let Some(decl) = decl_opt {
                return Ok((decl, None));
            } else {
                // Empty variable declaration, but we need to create a Decl
                // For now, we'll create a dummy VarGroup
                return Ok((Decl::VarGroup(base_type_spec, thin_vec::ThinVec::new()), None));
            }
        }
        let mut declarators = ThinVec::new();
        loop {
            let declarator = self.parse_declarator(base_type_spec.clone())?;
            declarators.push(declarator);

            if self.eat_token(&TokenKind::Comma)? == false {
                break;
            }
        }
        self.expect_punct(TokenKind::Semicolon)?;
        
        // Handle the case where we have an enum/struct/union definition followed by variables
        // In this case, we need to return both the definition and the variable declarations
        if let Some(definition_decl) = decl_opt {
            // We have both a definition and declarators, so we need to return both
            let var_group = Decl::VarGroup(base_type_spec, declarators);
            return Ok((definition_decl, Some(ThinVec::from([var_group]))));
        }
        
        Ok((Decl::VarGroup(base_type_spec, declarators), None))
    }

    pub fn parse(&mut self) -> Result<TranslationUnit, ParserError> {
        self.parse_translation_unit()
    }

    /// parse a option action when start token is found
    fn maybe_start<T, F>(
        &mut self,
        start_token: &TokenKind,
        mut parse_fn: F,
    ) -> Result<Option<T>, ParserError>
    where
        F: FnMut(&mut Self) -> Result<T, ParserError>,
    {
        if self.eat_token(start_token)? {
            let item = parse_fn(self)?;
            Ok(Some(item))
        } else {
            Ok(None)
        }
    }

    /// Parses a optional action
    fn maybe_end<T, F>(
        &mut self,
        end_token: &TokenKind,
        mut parse_fn: F,
    ) -> Result<Option<T>, ParserError>
    where
        F: FnMut(&mut Self) -> Result<T, ParserError>,
    {
        if self.eat_token(end_token)? {
            Ok(None)
        } else {
            let item = parse_fn(self)?;
            self.expect_punct(end_token.clone())?;

            Ok(Some(item))
        }
    }

    /// Parses a `_Static_assert` declaration.
    fn parse_static_assert(&mut self) -> Result<Decl, ParserError> {
        self.eat()?; // consume `_Static_assert`
        self.expect_punct(TokenKind::LeftParen)?;
        let expr = self.parse_pratt_expr(3)?;
        self.expect_punct(TokenKind::Comma)?;
        let token = self.current_token()?;
        match token.kind.clone() {
            TokenKind::String(s) => {
                self.eat()?;
                self.expect_punct(TokenKind::RightParen)?;
                self.expect_punct(TokenKind::Semicolon)?;
                Ok(Decl::StaticAssert(Box::new(expr), s))
            }
            _ => Err(ParserError::UnexpectedToken(token.clone())),
        }
    }
}
