use crate::parser::ast::{
    Decl, Declarator, Expr, ForInit, FuncDecl, Initializer, Stmt, TranslationUnit, BinOp, AssignOp
};
use crate::parser::string_interner::StringId;
use crate::types::{TypeSpec, TypeSpecKind, TypeQual};
use std::fmt::Write;

pub struct Dumper {
    indent: String,
}

impl Dumper {
    pub fn new() -> Self {
        Self {
            indent: String::new(),
        }
    }

    pub fn dump(&mut self, tu: &TranslationUnit) {
        println!("TranslationUnit");
        let mut globals_iter = tu.globals.iter().peekable();
        while let Some(decl) = globals_iter.next() {
            let is_last = globals_iter.peek().is_none();
            self.dump_decl(decl, is_last);
        }
    }

    fn dump_decl(&mut self, decl: &Decl, is_last: bool) {
        let prefix = if is_last { "└─ " } else { "├─ " };
        let child_indent = if is_last { "   " } else { "│  " };

        print!("{}{}", self.indent, prefix);

        match decl {
            Decl::Func(func) => self.dump_func_decl(func, child_indent),
            Decl::VarGroup(type_spec, declarators) => {
                println!("VarGroup '{}'", type_spec_to_string(type_spec));
                self.indent.push_str(child_indent);
                let mut decls_iter = declarators.iter().peekable();
                while let Some(declarator) = decls_iter.next() {
                    let is_last_decl = decls_iter.peek().is_none();
                    self.dump_declarator(declarator, is_last_decl);
                }
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Decl::Struct(s) => {
                let name = s.name.map_or("".to_string(), |id| id.as_str().to_string());
                println!("StructDecl '{}'", name);
            }
            Decl::Union(u) => {
                let name = u.name.map_or("".to_string(), |id| id.as_str().to_string());
                println!("UnionDecl '{}'", name);
            }
            Decl::Enum(e) => {
                let name = e.name.map_or("".to_string(), |id| id.as_str().to_string());
                println!("EnumDecl '{}'", name);
            }
            Decl::Typedef { name, ty: type_spec, .. } => {
                println!("Typedef '{}' '{}'", name.as_str(), type_spec_to_string(type_spec));
            }
            Decl::StaticAssert(expr, message) => {
                 println!("StaticAssert '{}'", message.as_str());
                 self.indent.push_str(child_indent);
                 self.dump_expr(expr, true);
                 self.indent.truncate(self.indent.len() - child_indent.len());
            }
        }
    }

    fn dump_declarator(&mut self, declarator: &Declarator, is_last: bool) {
        let prefix = if is_last { "└─ " } else { "├─ " };
        let child_indent = if is_last { "   " } else { "│  " };

        print!("{}{}", self.indent, prefix);
        let name = declarator.name.map_or("<unnamed>".to_string(), |id| id.as_str().to_string());
        println!("Declarator '{}'", name);

        if let Some(init) = &declarator.init {
            self.indent.push_str(child_indent);
            self.dump_expr(init, true);
            self.indent.truncate(self.indent.len() - child_indent.len());
        }
    }


    fn dump_func_decl(&mut self, func: &FuncDecl, child_indent: &str) {
        let name = func.name.as_str();
        let return_type = type_spec_to_string(&func.return_type);
        println!("FunctionDecl {} '{}'", name, return_type);

        self.indent.push_str(child_indent);
        if let Some(body) = &func.body {
            let mut stmts_iter = body.iter().peekable();
            while let Some(stmt) = stmts_iter.next() {
                let is_last = stmts_iter.peek().is_none();
                self.dump_stmt(stmt, is_last);
            }
        }
        self.indent.truncate(self.indent.len() - child_indent.len());
    }

    fn dump_stmt(&mut self, stmt: &Stmt, is_last: bool) {
        let prefix = if is_last { "└─ " } else { "├─ " };
        let child_indent = if is_last { "   " } else { "│  " };

        print!("{}{}", self.indent, prefix);

        match stmt {
            Stmt::Return(expr) => {
                println!("Return");
                self.indent.push_str(child_indent);
                self.dump_expr(expr, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::If(cond, then_stmt, else_stmt) => {
                println!("If");
                self.indent.push_str(child_indent);
                self.dump_expr(cond, false);
                self.dump_stmt(then_stmt, else_stmt.is_none());
                if let Some(else_s) = else_stmt {
                    self.dump_stmt(else_s, true);
                }
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::While(cond, body) => {
                println!("While");
                self.indent.push_str(child_indent);
                self.dump_expr(cond, false);
                self.dump_stmt(body, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
             Stmt::For(init, cond, inc, body) => {
                println!("For");
                self.indent.push_str(child_indent);
                let has_cond = cond.is_some();
                let has_inc = inc.is_some();

                if let Some(init_expr) = init {
                    let is_last_child = !has_cond && !has_inc;
                    let prefix = if is_last_child { "└─ " } else { "├─ " };
                    print!("{}{}", self.indent, prefix);
                    match &**init_expr {
                        ForInit::Declaration(ts, id, init) => {
                            println!("ForInit Declaration '{} {}'", type_spec_to_string(ts), id.as_str());
                            if let Some(init_val) = init {
                                self.indent.push_str("│     ");
                                match init_val {
                                    Initializer::Expr(e) => self.dump_expr(e, true),
                                    Initializer::List(_) => println!("InitializerList"),
                                }
                                self.indent.truncate(self.indent.len() - 6);
                            }
                        },
                        ForInit::Expr(e) => {
                            println!("ForInit Expr");
                            self.dump_expr(e, true);
                        }
                    }
                }
                if let Some(cond_expr) = cond {
                    let is_last_child = !has_inc;
                    self.dump_expr(cond_expr, is_last_child);
                }
                if let Some(inc_expr) = inc {
                    self.dump_expr(inc_expr, true);
                }
                self.dump_stmt(body, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::Block(stmts) => {
                println!("Block");
                self.indent.push_str(child_indent);
                let mut stmts_iter = stmts.iter().peekable();
                while let Some(s) = stmts_iter.next() {
                    let is_last_stmt = stmts_iter.peek().is_none();
                    self.dump_stmt(s, is_last_stmt);
                }
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::Expr(expr) => {
                println!("ExprStmt");
                self.indent.push_str(child_indent);
                self.dump_expr(expr, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::Declaration(decl) => {
                 match decl {
                     Decl::VarGroup(type_spec, declarators) => {
                         println!("VarGroup '{}'", type_spec_to_string(type_spec));
                         self.indent.push_str(child_indent);
                         let mut decls_iter = declarators.iter().peekable();
                         while let Some(declarator) = decls_iter.next() {
                             let is_last_decl = decls_iter.peek().is_none();
                             self.dump_declarator(declarator, is_last_decl);
                         }
                         self.indent.truncate(self.indent.len() - child_indent.len());
                     }
                     _ => self.dump_decl(decl, is_last),
                 }
            }
            Stmt::Empty => {
                println!("Empty");
            }
            Stmt::Break => println!("Break"),
            Stmt::Continue => println!("Continue"),
            Stmt::Switch(expr, body) => {
                println!("Switch");
                self.indent.push_str(child_indent);
                self.dump_expr(expr, false);
                self.dump_stmt(body, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::Case(expr, body) => {
                println!("Case");
                self.indent.push_str(child_indent);
                self.dump_expr(expr, false);
                self.dump_stmt(body, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::Default(body) => {
                println!("Default");
                self.indent.push_str(child_indent);
                self.dump_stmt(body, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::DoWhile(body, cond) => {
                println!("DoWhile");
                self.indent.push_str(child_indent);
                self.dump_stmt(body, false);
                self.dump_expr(cond, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
             Stmt::Label(name, body, _) => {
                println!("Label '{}'", name.as_str());
                self.indent.push_str(child_indent);
                self.dump_stmt(body, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Stmt::Goto(name, _) => {
                println!("Goto '{}'", name.as_str());
            }
        }
    }

    fn dump_expr(&mut self, expr: &Expr, is_last: bool) {
        let prefix = if is_last { "└─ " } else { "├─ " };
        let child_indent = if is_last { "   " } else { "│  " };

        print!("{}{}", self.indent, prefix);

        match expr {
            Expr::Variable(name, _) => {
                println!("Variable '{}'", name.as_str());
            }
            Expr::Number(val, _) => {
                println!("Number '{}'", val);
            }
            Expr::FloatNumber(val, _) => {
                println!("FloatNumber '{}'", val);
            }
            Expr::String(id, _) => {
                println!("String '{}'", id.as_str());
            }
            Expr::Char(id, _) => {
                println!("Char '{}'", id.as_str());
            }
            Expr::Call(name, args, _) => {
                println!("Call '{}'", name.as_str());
                self.indent.push_str(child_indent);
                let mut args_iter = args.iter().peekable();
                while let Some(arg) = args_iter.next() {
                    let is_last_arg = args_iter.peek().is_none();
                    self.dump_expr(arg, is_last_arg);
                }
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Expr::PostIncrement(e) | Expr::PostDecrement(e) | Expr::PreIncrement(e) | Expr::PreDecrement(e) | Expr::Deref(e) | Expr::AddressOf(e) | Expr::Sizeof(e) | Expr::Neg(e) | Expr::BitwiseNot(e) | Expr::LogicalNot(e) => {
                let op_name = match expr {
                    Expr::PostIncrement(_) => "PostIncrement",
                    Expr::PostDecrement(_) => "PostDecrement",
                    Expr::PreIncrement(_) => "PreIncrement",
                    Expr::PreDecrement(_) => "PreDecrement",
                    Expr::Deref(_) => "Deref",
                    Expr::AddressOf(_) => "AddressOf",
                    Expr::Sizeof(_) => "Sizeof",
                    Expr::Neg(_) => "Neg",
                    Expr::BitwiseNot(_) => "BitwiseNot",
                    Expr::LogicalNot(_) => "LogicalNot",
                    _ => unreachable!(),
                };
                println!("{}", op_name);
                self.indent.push_str(child_indent);
                self.dump_expr(e, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
            Expr::SizeofType(type_spec) => {
                println!("SizeofType '{}'", type_spec_to_string(type_spec));
            }
            Expr::ExplicitCast(ts, e) => {
                 println!("ExplicitCast to '{}'", type_spec_to_string(ts));
                self.indent.push_str(child_indent);
                self.dump_expr(e, true);
                self.indent.truncate(self.indent.len() - child_indent.len());
            }
             _ => {
                if let Some((op, lhs, rhs)) = expr.get_binary_expr() {
                    self.dump_binary_op(op, lhs, rhs, child_indent);
                } else if let Some((op, lhs, rhs)) = expr.get_assign_expr() {
                    self.dump_assign_op(op, lhs, rhs, child_indent);
                } else {
                     println!("Other Expr");
                }
            }
        }
    }

    fn dump_binary_op(&mut self, op: BinOp, lhs: &Expr, rhs: &Expr, child_indent: &str) {
        println!("{:?}", op);
        self.indent.push_str(child_indent);
        self.dump_expr(lhs, false);
        self.dump_expr(rhs, true);
        self.indent.truncate(self.indent.len() - child_indent.len());
    }

    fn dump_assign_op(&mut self, op: AssignOp, lhs: &Expr, rhs: &Expr, child_indent: &str) {
        println!("Assign {:?}", op);
        self.indent.push_str(child_indent);
        self.dump_expr(lhs, false);
        self.dump_expr(rhs, true);
        self.indent.truncate(self.indent.len() - child_indent.len());
    }
}

fn type_spec_to_string(ts: &TypeSpec) -> String {
    let mut s = String::new();
    if ts.qualifiers().contains(TypeQual::CONST) {
        s.push_str("const ");
    }
    if ts.qualifiers().contains(TypeQual::VOLATILE) {
        s.push_str("volatile ");
    }
    match &ts.kind {
        TypeSpecKind::Builtin(mask) => {
            let builtin_name = builtin_mask_to_name(mask.bits());
            s.push_str(&builtin_name);
        },
        TypeSpecKind::Struct(id) => write!(s, "struct #{}", id.to_usize_index()).unwrap(),
        TypeSpecKind::Union(id) => write!(s, "union #{}", id.to_usize_index()).unwrap(),
        TypeSpecKind::Enum(id) => write!(s, "enum #{}", id.to_usize_index()).unwrap(),
        TypeSpecKind::Typedef(id) => write!(s, "Typedef #{}", id.to_usize_index()).unwrap(),
    }

    for _ in 0..ts.pointer_depth() {
        s.push('*');
    }

    // Note: Array sizes are stored in ArrayExprListId, which is not easily accessible here.
    // We rely on the pointer depth and array rank in the header for basic dumping.
    s
}

fn builtin_mask_to_name(mask: u16) -> String {
    use crate::types::TypeKeywordMask;
    
    // Handle compound types by checking for common combinations first
    let has_unsigned = mask & TypeKeywordMask::UNSIGNED.bits() != 0;
    let has_signed = mask & TypeKeywordMask::SIGNED.bits() != 0;
    let has_void = mask & TypeKeywordMask::VOID.bits() != 0;
    let has_bool = mask & TypeKeywordMask::BOOL.bits() != 0;
    let has_char = mask & TypeKeywordMask::CHAR.bits() != 0;
    let has_short = mask & TypeKeywordMask::SHORT.bits() != 0;
    let has_int = mask & TypeKeywordMask::INT.bits() != 0;
    let has_long = mask & TypeKeywordMask::LONG.bits() != 0;
    let has_longlong = mask & TypeKeywordMask::LONGLONG.bits() != 0;
    let has_float = mask & TypeKeywordMask::FLOAT.bits() != 0;
    let has_double = mask & TypeKeywordMask::DOUBLE.bits() != 0;
    let has_complex = mask & TypeKeywordMask::COMPLEX.bits() != 0;
    let has_imaginary = mask & TypeKeywordMask::IMAGINARY.bits() != 0;
    let has_atomic = mask & TypeKeywordMask::ATOMIC.bits() != 0;
    
    // Check for single-bit masks first (most common case)
    if mask.count_ones() == 1 {
        return match mask {
            mask if mask == TypeKeywordMask::VOID.bits() => "void".to_string(),
            mask if mask == TypeKeywordMask::BOOL.bits() => "_Bool".to_string(),
            mask if mask == TypeKeywordMask::CHAR.bits() => "char".to_string(),
            mask if mask == TypeKeywordMask::SHORT.bits() => "short".to_string(),
            mask if mask == TypeKeywordMask::INT.bits() => "int".to_string(),
            mask if mask == TypeKeywordMask::LONG.bits() => "long".to_string(),
            mask if mask == TypeKeywordMask::LONGLONG.bits() => "long long".to_string(),
            mask if mask == TypeKeywordMask::FLOAT.bits() => "float".to_string(),
            mask if mask == TypeKeywordMask::DOUBLE.bits() => "double".to_string(),
            mask if mask == TypeKeywordMask::SIGNED.bits() => "signed".to_string(),
            mask if mask == TypeKeywordMask::UNSIGNED.bits() => "unsigned".to_string(),
            mask if mask == TypeKeywordMask::COMPLEX.bits() => "_Complex".to_string(),
            mask if mask == TypeKeywordMask::IMAGINARY.bits() => "_Imaginary".to_string(),
            mask if mask == TypeKeywordMask::ATOMIC.bits() => "_Atomic".to_string(),
            _ => format!("Builtin({})", mask),
        };
    }
    
    // Handle compound types - build the type name step by step
    let mut parts = Vec::new();
    
    // Add sign modifier first
    if has_unsigned {
        parts.push("unsigned");
    } else if has_signed {
        parts.push("signed");
    }
    
    // Add type specifier
    if has_void {
        parts.push("void");
    } else if has_bool {
        parts.push("_Bool");
    } else if has_char {
        parts.push("char");
    } else if has_short {
        parts.push("short");
        if has_int {
            parts.push("int");
        }
    } else if has_longlong {
        parts.push("long long");
    } else if has_long {
        parts.push("long");
        if has_int {
            parts.push("int");
        }
    } else if has_int {
        parts.push("int");
    } else if has_float {
        parts.push("float");
    } else if has_double {
        parts.push("double");
    }
    
    // Add complex/imaginary modifiers
    if has_complex {
        parts.push("_Complex");
    }
    if has_imaginary {
        parts.push("_Imaginary");
    }
    if has_atomic {
        parts.push("_Atomic");
    }
    
    if parts.is_empty() {
        format!("Builtin({})", mask)
    } else {
        parts.join(" ")
    }
}
