//! Parser: turns tokens into an AST using a hand-written recursive-descent parser.
//!
//! Major entrypoints:
//! - Parser::parse_compilation_unit: whole-file parse
//! - Parser::parse_decl: top-level declarations
//! - Parser::parse_block: statement lists in braces
//! - Parser::parse_expr / parse_binary_expr / parse_primary: expressions
//!
//! Utilities:
//! - expect: consume expected token with diagnostics
//! - peek_pos_len: current token span for error reporting
use crate::ast::*;
use crate::diagnostics::Diagnostic;
use crate::lexer::{Token, TokenKind};
use anyhow::{bail, Result, Context};

/// Stateful parser over a token slice
pub struct Parser<'a> {
    tokens: &'a [Token],
    pos: usize,
    pub errors: Vec<Diagnostic>,
    scope_path: Vec<String>,
}

impl<'a> Parser<'a> {
    /// Create a new parser over the token slice
    pub fn new(tokens: &'a [Token]) -> Self {
        Self { tokens, pos: 0, errors: Vec::new(), scope_path: Vec::new() }
    }

    /// Parse a whole source file into a compilation unit
    pub fn parse_compilation_unit(&mut self) -> Result<CompilationUnit> {
        let mut decls = Vec::new();
        while !self.eof() {
            // Allow stray semicolons at the top level
            if matches!(self.peek_kind(), Some(TokenKind::Semicolon)) { self.bump_kind(); continue; }
            decls.push(self.parse_decl()?);
        }
        Ok(CompilationUnit { decls })
    }

    /// Parse a single top-level declaration
    fn parse_decl(&mut self) -> Result<Decl> {
        match self.peek_kind() {
            Some(TokenKind::Dealer) => Ok(Decl::Dealer(self.parse_dealer()?)),
            Some(TokenKind::Trait) => Ok(Decl::Trait(self.parse_trait()?)),
            Some(TokenKind::MemberKw) => Ok(Decl::Struct(self.parse_member_struct()?)),
            Some(TokenKind::Ident(_)) | Some(TokenKind::Fn) => {
                // Could be struct/impl/fn — for MVP, focus on fn and struct/impl later
                // For now, only allow free functions starting with 'fn'
                if matches!(self.peek_kind(), Some(TokenKind::Fn)) {
                    Ok(Decl::Fn(self.parse_fn_decl()?))
                } else {
                    let (o, l) = self.peek_pos_len();
                    self.errors.push(Diagnostic { message: "unexpected declaration start".to_string(), offset: o, len: l, path: self.scope_path.clone() });
                    bail!("parse error")
                }
            },
            None => {
                let (o, l) = self.peek_pos_len();
                self.errors.push(Diagnostic { message: "unexpected EOF while parsing declaration".to_string(), offset: o, len: l, path: self.scope_path.clone() });
                bail!("parse error")
            }
            _ => {
                let (o, l) = self.peek_pos_len();
                let tk = self.peek_kind();
                self.errors.push(Diagnostic { message: format!("unsupported top-level declaration: {:?}", tk), offset: o, len: l, path: self.scope_path.clone() });
                bail!("parse error")
            }
        }
    }

    /// Parse an identifier and return it
    fn parse_ident(&mut self) -> Result<Ident> {
        match self.bump_kind() {
            Some(TokenKind::Ident(id)) => Ok(id),
            other => bail!("expected identifier, found {:?}", other),
        }
    }

    /// Consume exactly the expected token, else record a diagnostic
    fn expect(&mut self, expected: TokenKind) -> Result<()> {
        let (err_off, err_len) = self.peek_pos_len();
        let got = match self.bump_kind() {
            Some(k) => k,
            None => {
                self.errors.push(Diagnostic { message: format!("expected {:?}, found EOF", expected), offset: err_off, len: err_len, path: self.scope_path.clone() });
                bail!("parse error")
            }
        };
        if std::mem::discriminant(&got) == std::mem::discriminant(&expected) {
            Ok(())
        } else {
            self.errors.push(Diagnostic { message: format!("expected {:?}, found {:?}", expected, got), offset: err_off, len: err_len, path: self.scope_path.clone() });
            bail!("parse error")
        }
    }

    /// Span (offset, len) of the current token, or EOF position
    fn peek_pos_len(&self) -> (usize, usize) {
        if let Some(tok) = self.tokens.get(self.pos) {
            (tok.offset, tok.len)
        } else if let Some(last) = self.tokens.last() {
            (last.offset + last.len, 0)
        } else {
            (0, 0)
        }
    }

    /// Parse a brace-delimited block of statements
    fn parse_block(&mut self) -> Result<Block> {
        self.expect(TokenKind::LBrace)?;
        let mut stmts = Vec::new();
        while !self.check(&TokenKind::RBrace) {
            // Very small MVP: allow empty or semicolons and identifiers calls
            if self.check(&TokenKind::Semicolon) { self.bump_kind(); continue; }
            // start Dealer;
            if self.check(&TokenKind::Start) {
                self.bump_kind();
                let name = self.parse_ident()?;
                stmts.push(Stmt::StartDealer { name });
                if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
                continue;
            }
            // if cond { ... } OR if let ... , cond { ... }
            if self.check(&TokenKind::If) {
                self.bump_kind();
                // optional pre-binding: let ... then optional comma
                let mut pre_binding: Option<LetBinding> = None;
                if self.check(&TokenKind::Let) {
                    self.bump_kind();
                    let is_mut = if self.check(&TokenKind::Mut) { self.bump_kind(); true } else { false };
                    let name = self.parse_ident()?;
                    // require explicit type
                    self.expect(TokenKind::Colon)?;
                    let ty = Some(self.parse_type()?);
                    let mut init = None;
                    if self.check(&TokenKind::Equals) { self.bump_kind(); init = Some(self.parse_expr()?); }
                    if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
                    pre_binding = Some(LetBinding { name, is_mut, ty, init });
                    if self.check(&TokenKind::Comma) { self.bump_kind(); }
                }
                // condition expression directly (no braces)
                let cond = self.parse_expr()?;
                let then_block = self.parse_block()?;
                let mut elifs = Vec::new();
                let mut else_block = None;
                loop {
                    if self.check(&TokenKind::Else) {
                        self.bump_kind();
                        if self.check(&TokenKind::If) {
                            self.bump_kind();
                            let c = self.parse_expr()?;
                            let b = self.parse_block()?;
                            elifs.push((c, b));
                            continue;
                        } else {
                            else_block = Some(self.parse_block()?);
                        }
                    }
                    break;
                }
                stmts.push(Stmt::If { pre_binding, cond, then_block, elifs, else_block });
                continue;
            }
            // for var [, var2] in iterable { ... }
            if self.check(&TokenKind::For) {
                let for_decl = self.parse_for_loop()?;
                stmts.push(Stmt::For(for_decl));
                continue;
            }
            // let [mut] name [: Type] [= expr] ;
            if self.check(&TokenKind::Let) {
                self.bump_kind();
                let mut_flag = if self.check(&TokenKind::Mut) { self.bump_kind(); true } else { false };
                let name = self.parse_ident()?;
                // optional explicit type
                let mut ty: Option<TypeName> = None;
                if self.check(&TokenKind::Colon) { self.bump_kind(); ty = Some(self.parse_type()?); }
                let mut init = None;
                if self.check(&TokenKind::Equals) {
                    self.bump_kind();
                    // Special-case typed empty list literal: int[] / i32[] / MyType[]
                    // Recognize base type immediately followed by [] as an empty list of that type
                    let init_expr = if let Some(TokenKind::Ident(idpeek)) = self.peek_kind() {
                        // lookahead pattern: Ident LBracket RBracket
                        let save = self.pos;
                        let _ = self.bump_kind();
                        if self.check(&TokenKind::LBracket) {
                            self.bump_kind();
                            if self.check(&TokenKind::RBracket) {
                                self.bump_kind();
                                // Map the ident to a TypeName, fallback Named
                                let mut ty = match idpeek {
                                    Ident(ref s) if s == "int" => TypeName::Int,
                                    Ident(ref s) if s == "i8" => TypeName::I8,
                                    Ident(ref s) if s == "i16" => TypeName::I16,
                                    Ident(ref s) if s == "i32" => TypeName::I32,
                                    Ident(ref s) if s == "i64" => TypeName::I64,
                                    Ident(ref s) if s == "u8" => TypeName::U8,
                                    Ident(ref s) if s == "u16" => TypeName::U16,
                                    Ident(ref s) if s == "u32" => TypeName::U32,
                                    Ident(ref s) if s == "u64" => TypeName::U64,
                                    Ident(ref s) if s == "f32" => TypeName::F32,
                                    Ident(ref s) if s == "f64" => TypeName::F64,
                                    Ident(ref s) if s == "char" => TypeName::Char,
                                    Ident(ref s) if s == "string" => TypeName::String,
                                    Ident(ref s) if s == "bool" => TypeName::Bool,
                                    Ident(ref s) if s == "any" => TypeName::Any,
                                    other => TypeName::Named(other.clone()),
                                };
                                // allow repeated [] for nested lists, e.g., int[][]
                                while self.check(&TokenKind::LBracket) {
                                    self.bump_kind();
                                    self.expect(TokenKind::RBracket)?;
                                    ty = TypeName::List(Box::new(ty));
                                }
                                Expr::EmptyListOf(ty)
                            } else { self.pos = save; self.parse_expr()? }
                        } else { self.pos = save; self.parse_expr()? }
                    } else { self.parse_expr()? };
                    init = Some(init_expr);
                }
                if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
                stmts.push(Stmt::Let { name, is_mut: mut_flag, ty, init });
                continue;
            }
            // index assignment: name[expr] = expr ; (Go-like map/array set)
            if self.check_kind_ident() {
                let save = self.pos;
                if let Some(TokenKind::Ident(id)) = self.bump_kind() {
                    if self.check(&TokenKind::LBracket) {
                        self.bump_kind();
                        let idx = self.parse_expr()?;
                        self.expect(TokenKind::RBracket)?;
                        if self.check(&TokenKind::Equals) {
                            self.bump_kind();
                            let val = self.parse_expr()?;
                            if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
                            stmts.push(Stmt::IndexAssign { target: id, index: idx, value: val });
                            continue;
                        }
                    }
                    self.pos = save;
                } else { self.pos = save; }
            }

            // simple assignment: name = expr ;
            if self.check_kind_ident() {
                // lookahead for '='
                let save = self.pos;
                if let Some(TokenKind::Ident(id)) = self.bump_kind() {
                    if self.check(&TokenKind::Equals) {
                        self.bump_kind();
                        let expr = self.parse_expr()?;
                        if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
                        stmts.push(Stmt::Assign { target: id, value: expr });
                        continue;
                    }
                    // rollback if not assignment
                    self.pos = save;
                } else { self.pos = save; }
            }
            if self.check_kind_expr_start() {
                let expr = self.parse_expr()?;
                if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
                stmts.push(Stmt::Expr(expr));
            } else { break; }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(Block { stmts })
    }

    /// Parse a `for` loop header and body
    fn parse_for_loop(&mut self) -> Result<ForDecl> {
        // We arrive here only when current token is 'for'
        self.expect(TokenKind::For)?;
        let mut vars = Vec::new();
        vars.push(self.parse_ident()?); // first Variable
        if self.check(&TokenKind::Comma) {
            self.bump_kind();
            vars.push(self.parse_ident()?); // second variable
        }
        self.expect(TokenKind::In)?;
        let iterable = self.parse_expr()?;
        let body = self.parse_block()?;
        Ok(ForDecl { var: vars, iterable, body })
    }
    /// Parse an expression
    fn parse_expr(&mut self) -> Result<Expr> { self.parse_binary_expr(0) }

    /// Parse a primary-expression (atoms, calls, member, literals)
    fn parse_primary(&mut self) -> Result<Expr> {
        match self.peek_kind() {
            // Struct literal: Name { a: expr, b: expr }
            // Disambiguate from blocks after expressions (e.g., `for x in nums { ... }`)
            // Only treat as struct literal if after '{' we see an identifier followed by ':'
            Some(TokenKind::Ident(_)) if self.peek_is_struct_lit_start() => {
                let name = self.parse_ident()?;
                self.expect(TokenKind::LBrace)?;
                let mut fields = Vec::new();
                if !self.check(&TokenKind::RBrace) {
                    loop {
                        let fname = self.parse_ident()?;
                        self.expect(TokenKind::Colon)?;
                        let fexpr = self.parse_expr()?;
                        fields.push((fname, fexpr));
                        if self.check(&TokenKind::Comma) { self.bump_kind(); continue; }
                        break;
                    }
                }
                self.expect(TokenKind::RBrace)?;
                Ok(Expr::StructLit { name, fields })
            }
            Some(TokenKind::Bang) => { self.bump_kind(); let e = self.parse_primary()?; Ok(Expr::Unary { op: UnOp::Not, expr: Box::new(e) }) }
            Some(TokenKind::Minus) => { self.bump_kind(); let e = self.parse_primary()?; Ok(Expr::Unary { op: UnOp::Neg, expr: Box::new(e) }) }
            Some(TokenKind::Amp) => { self.bump_kind(); let e = self.parse_primary()?; Ok(Expr::Ref(Box::new(e))) }
            Some(TokenKind::Ident(_)) => {
                // typed empty list literal like int[] or MyType[] at expression start
                // Lookahead without consuming: Ident '[' ']'
                let save_pos = self.pos;
                let mut typed_empty: Option<Expr> = None;
                if let Some(TokenKind::Ident(idpeek)) = self.peek_kind() {
                    // temporarily consume to check brackets
                    let _ = self.bump_kind();
                    if self.check(&TokenKind::LBracket) {
                        self.bump_kind();
                        if self.check(&TokenKind::RBracket) {
                            self.bump_kind();
                            // map idpeek to TypeName and allow repeated [] nesting
                            let mut ty = match idpeek.0.as_str() {
                                "int" => TypeName::Int,
                                "i8" => TypeName::I8,
                                "i16" => TypeName::I16,
                                "i32" => TypeName::I32,
                                "i64" => TypeName::I64,
                                "u8" => TypeName::U8,
                                "u16" => TypeName::U16,
                                "u32" => TypeName::U32,
                                "u64" => TypeName::U64,
                                "f32" => TypeName::F32,
                                "f64" => TypeName::F64,
                                "char" => TypeName::Char,
                                "string" => TypeName::String,
                                "bool" => TypeName::Bool,
                                "any" => TypeName::Any,
                                _ => TypeName::Named(idpeek.clone()),
                            };
                            while self.check(&TokenKind::LBracket) {
                                self.bump_kind();
                                self.expect(TokenKind::RBracket)?;
                                ty = TypeName::List(Box::new(ty));
                            }
                            typed_empty = Some(Expr::EmptyListOf(ty));
                        }
                    }
                }
                if let Some(e) = typed_empty { return Ok(e); } else { self.pos = save_pos; }

                // Support nested dotted identifiers: A.B.C
                let mut expr = Expr::Ident(self.parse_ident()?);
                while self.check(&TokenKind::Dot) {
                    self.bump_kind();
                    let name = self.parse_ident()?;
                    expr = Expr::Member { target: Box::new(expr), name };
                }
                // Postfix chain: .member, (args), [index or slice], typed empty list suffix base[]
                loop {
                    if self.check(&TokenKind::Dot) {
                        self.bump_kind();
                        let name = self.parse_ident()?;
                        expr = Expr::Member { target: Box::new(expr), name };
                        continue;
                    }
                    if self.check(&TokenKind::LParen) {
                        self.bump_kind();
                        let mut args = Vec::new();
                        if !self.check(&TokenKind::RParen) {
                            loop {
                                args.push(self.parse_expr()?);
                                if self.check(&TokenKind::Comma) { self.bump_kind(); continue; }
                                break;
                            }
                        }
                        self.expect(TokenKind::RParen)?;
                        expr = Expr::Call { callee: Box::new(expr), args };
                        continue;
                    }
                    if self.check(&TokenKind::LBracket) {
                        // index or slice
                        self.bump_kind();
                        let mut start: Option<Expr> = None;
                        let mut end: Option<Expr> = None;
                        let mut inclusive = false;
                        if self.check(&TokenKind::RBracket) {
                            // empty index [] is invalid
                            self.expect(TokenKind::RBracket)?; // will error later
                            bail!("empty index/slice");
                        }
                        let first = if !self.check(&TokenKind::DoubleDot) && !self.check(&TokenKind::DoubleDotEq) {
                            Some(self.parse_expr()?)
                        } else { None };
                        if self.check(&TokenKind::DoubleDot) || self.check(&TokenKind::DoubleDotEq) {
                            // slice
                            inclusive = self.check(&TokenKind::DoubleDotEq);
                            self.bump_kind();
                            start = first;
                            if !self.check(&TokenKind::RBracket) {
                                end = Some(self.parse_expr()?);
                            }
                            self.expect(TokenKind::RBracket)?;
                            expr = Expr::Slice { target: Box::new(expr), start: start.map(Box::new), end: end.map(Box::new), inclusive };
                        } else {
                            // index
                            self.expect(TokenKind::RBracket)?;
                            expr = Expr::Index { target: Box::new(expr), index: Box::new(first.unwrap()) };
                        }
                        continue;
                    }
                    break;
                }
                Ok(expr)
            }
            Some(TokenKind::Await) => { self.bump_kind(); let inner = self.parse_expr()?; Ok(Expr::Await(Box::new(inner))) }
            Some(TokenKind::Recv) => { self.bump_kind(); Ok(Expr::Recv) }
            Some(TokenKind::String(s)) => { let s = s.clone(); self.bump_kind(); Ok(Expr::String(s)) }
            Some(TokenKind::True) => { self.bump_kind(); Ok(Expr::Bool(true)) }
            Some(TokenKind::False) => { self.bump_kind(); Ok(Expr::Bool(false)) }
            Some(TokenKind::LParen) => {
                self.bump_kind();
                let e = self.parse_expr()?;
                self.expect(TokenKind::RParen)?;
                Ok(e)
            }
            Some(TokenKind::LBracket) => {
                // list literal: [e1, e2, ...]
                self.bump_kind();
                let mut items = Vec::new();
                if !self.check(&TokenKind::RBracket) {
                    loop {
                        items.push(self.parse_expr()?);
                        if self.check(&TokenKind::Comma) { self.bump_kind(); continue; }
                        break;
                    }
                }
                self.expect(TokenKind::RBracket)?;
                Ok(Expr::List(items))
            }
            Some(TokenKind::Number(n)) => {
                let n: f64 = n.parse().unwrap_or(0.0);
                self.bump_kind();
                if self.check(&TokenKind::DoubleDot) {
                    self.bump_kind();
                    let end = self.parse_expr()?;
                    Ok(Expr::Range { start: Box::new(Expr::Number(n)), end: Box::new(end), inclusive: false })
                } else if self.check(&TokenKind::DoubleDotEq) {
                    self.bump_kind();
                    let end = self.parse_expr()?;
                    Ok(Expr::Range { start: Box::new(Expr::Number(n)), end: Box::new(end), inclusive: true })
                } else {
                    Ok(Expr::Number(n))
                }
            }
            other => bail!("unexpected token in expr: {:?}", other)
        }
    }

    /// Operator precedence table (higher binds tighter)
    fn precedence(tok: &TokenKind) -> Option<u8> {
        use crate::lexer::TokenKind::*;
        Some(match tok {
            DStar => 8,           // ** highest (right-assoc)
            Star | Slash | Percent => 7,
            Plus | Minus => 6,
            Lt | Le | Gt | Ge => 5,
            EqEq | BangEq => 4,
            // Pipe has very low precedence to sequence computations
            Arrow => 1, // not used here but reserved
            _ => return None,
        })
    }

    /// Map a token to a binary operator enum
    fn binop_of(tok: &TokenKind) -> Option<BinOp> {
        use crate::lexer::TokenKind::*;
        Some(match tok {
            Plus => BinOp::Add,
            Minus => BinOp::Sub,
            Star => BinOp::Mul,
            Slash => BinOp::Div,
            Percent => BinOp::Mod,
            DStar => BinOp::Pow,
            Lt => BinOp::Lt,
            Le => BinOp::Le,
            Gt => BinOp::Gt,
            Ge => BinOp::Ge,
            EqEq => BinOp::Eq,
            BangEq => BinOp::Ne,
            _ => return None,
        })
    }

    /// Precedence-climbing parser for binary expressions
    fn parse_binary_expr(&mut self, min_prec: u8) -> Result<Expr> {
        let mut left = self.parse_primary()?;
        loop {
            let Some(op_tok) = self.peek_kind() else { break };
            if matches!(op_tok, TokenKind::PipeArrow) {
                // custom handling for |> dataflow
                self.bump_kind();
                let rhs = self.parse_primary()?;
                left = Expr::PipeArrow(Box::new(left), Box::new(rhs));
                continue;
            }
            let Some(op_prec) = Self::precedence(&op_tok) else { break };
            if op_prec < min_prec { break; }
            // consume operator
            let op_tok = self.bump_kind().unwrap();
            let right_min_prec = if matches!(op_tok, crate::lexer::TokenKind::DStar) { op_prec } else { op_prec + 1 };
            let right = self.parse_binary_expr(right_min_prec)?;
            let op = Self::binop_of(&op_tok).unwrap();
            left = Expr::Binary { op, left: Box::new(left), right: Box::new(right) };
        }
        Ok(left)
    }

    fn parse_type(&mut self) -> Result<TypeName> {
        // Grammar: Type := Ident ('[' ']')*
        // Ident may be a primitive (int, string, bool, ...) or a named type.
        let base_ident = match self.bump_kind() {
            Some(TokenKind::Ident(id)) => id,
            other => bail!("expected type, found {:?}", other),
        };

        let mut ty = match base_ident.0.as_str() {
            // integers
            "int" => TypeName::Int,
            "i8" => TypeName::I8,
            "i16" => TypeName::I16,
            "i32" => TypeName::I32,
            "i64" => TypeName::I64,
            "u8" => TypeName::U8,
            "u16" => TypeName::U16,
            "u32" => TypeName::U32,
            "u64" => TypeName::U64,
            // floats
            "f32" => TypeName::F32,
            "f64" => TypeName::F64,
            // others
            "char" => TypeName::Char,
            "string" => TypeName::String,
            "bool" => TypeName::Bool,
            "dealer" => TypeName::Dealer,
            "any" => TypeName::Any,
            _ => TypeName::Named(base_ident),
        };

        // zero or more [] suffixes (support nested lists)
        while self.check(&TokenKind::LBracket) {
            self.bump_kind();
            self.expect(TokenKind::RBracket)?;
            ty = TypeName::List(Box::new(ty));
        }
        Ok(ty)
    }

    fn parse_fn_decl(&mut self) -> Result<FuncDecl> {
        self.expect(TokenKind::Fn)?;
        // Optional receiver: fn (recv: Type) name(...)
        let mut receiver: Option<(Ident, TypeName)> = None;
        let save = self.pos;
        if self.check(&TokenKind::LParen) {
            self.bump_kind();
            if matches!(self.peek_kind(), Some(TokenKind::Ident(_))) {
                let rname = self.parse_ident()?;
                if self.check(&TokenKind::Colon) {
                    self.bump_kind();
                    let rty = self.parse_type()?;
                    self.expect(TokenKind::RParen)?;
                    receiver = Some((rname, rty));
                } else {
                    self.pos = save;
                }
            } else {
                self.pos = save;
            }
        }
        let name = self.parse_ident()?;
        self.expect(TokenKind::LParen)?;
        let mut params: Vec<(Ident, TypeName)> = Vec::new();
        if !self.check(&TokenKind::RParen) {
            loop {
                let n = self.parse_ident()?;
                self.expect(TokenKind::Colon)?;
                let t = self.parse_type()?;
                params.push((n, t));
                if self.check(&TokenKind::Comma) { self.bump_kind(); continue; }
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        let sig = FuncSig { name, params, ret: TypeName::Unit, is_pub: false, receiver };
        let body = self.parse_block()?;
        Ok(FuncDecl { sig, body })
    }

    fn parse_trait(&mut self) -> Result<TraitDecl> {
        self.expect(TokenKind::Trait)?;
        let name = self.parse_ident()?;
        let mut methods = Vec::new();
        self.expect(TokenKind::LBrace)?;
        while !self.check(&TokenKind::RBrace) {
            // MVP: parse a method signature without params for now
            self.expect(TokenKind::Fn)?;
            let mname = self.parse_ident()?;
            self.expect(TokenKind::LParen)?; self.expect(TokenKind::RParen)?;
            if self.check(&TokenKind::Semicolon) { self.bump_kind(); }
            methods.push(FuncSig { name: mname, params: vec![], ret: TypeName::Unit, is_pub: false, receiver: None });
        }
        self.expect(TokenKind::RBrace)?;
        Ok(TraitDecl { name, methods, is_pub: false })
    }

    fn parse_dealer(&mut self) -> Result<DealerDecl> {
        self.expect(TokenKind::Dealer)?;
        let name = self.parse_ident()?;
        self.scope_path.push(format!("Dealer {}", name.0));
        self.expect(TokenKind::LBrace)?;
        let mut members: Vec<Ident> = Vec::new();
        let mut trait_name: Option<Ident> = None;
        let mut entry_fn: Option<FuncDecl> = None;
        while !self.check(&TokenKind::RBrace) {
            match self.peek_kind() {
                Some(TokenKind::Members) => {
                    self.bump_kind();
                    self.expect(TokenKind::LBrace)?;
                    while !self.check(&TokenKind::RBrace) {
                        let id = self.parse_ident()?;
                        members.push(id);
                        if self.check(&TokenKind::Comma) { self.bump_kind(); }
                    }
                    self.expect(TokenKind::RBrace)?;
                }
                Some(TokenKind::Trait) => {
                    self.bump_kind();
                    // the trait name should match dealer in your model, but we allow any for now
                    let tname = self.parse_ident()?;
                    self.expect(TokenKind::LBrace)?; // allow empty block for MVP
                    self.expect(TokenKind::RBrace)?;
                    trait_name = Some(tname);
                }
                Some(TokenKind::Fn) => {
                    let f = self.parse_fn_decl()?;
                    entry_fn = Some(f);
                }
                other => bail!("unexpected token in dealer body: {:?}", other),
            }
        }
        self.expect(TokenKind::RBrace)?;
        self.scope_path.pop();
        let entry_fn = entry_fn.context("dealer missing entry function").ok();
        Ok(DealerDecl { name, members, trait_name, entry_fn, is_pub: false })
    }

    fn check(&self, kind: &TokenKind) -> bool {
        self.peek_kind().map_or(false, |k| std::mem::discriminant(&k) == std::mem::discriminant(kind))
    }
    fn check_kind_ident(&self) -> bool {
         matches!(self.peek_kind(), Some(TokenKind::Ident(_))) }
    fn check_kind_expr_start(&self) -> bool {
         matches!(self.peek_kind(),
          Some(TokenKind::Ident(_)) |
           Some(TokenKind::Await) |
            Some(TokenKind::Recv) |
              Some(TokenKind::String(_)) |
               Some(TokenKind::Number(_)) |
                Some(TokenKind::True) |
                 Some(TokenKind::False)) }
    fn peek_kind(&self) -> Option<TokenKind>
     { self.tokens.get(self.pos).map(|t| t.kind.clone()) }
    fn bump_kind(&mut self) -> Option<TokenKind> {
         let k = self.peek_kind()?; self.pos += 1; Some(k) }
    fn eof(&self) -> bool { self.pos >= self.tokens.len() }

    fn peek_n_is_lbrace(&self, n: usize) -> bool {
        self.tokens.get(self.pos + n).map_or(false, |t| matches!(t.kind, TokenKind::LBrace))
    }

    /// Look ahead to see if the upcoming pattern is a struct literal start: Ident '{' Ident ':' ...
    fn peek_is_struct_lit_start(&self) -> bool {
        // current must be Ident, next must be '{', and then we want Ident ':' to reduce ambiguity
        if !matches!(self.peek_kind(), Some(TokenKind::Ident(_))) { return false; }
        if !self.peek_n_is_lbrace(1) { return false; }
        let t2 = self.tokens.get(self.pos + 2);
        let t3 = self.tokens.get(self.pos + 3);
        matches!((t2.map(|t| &t.kind), t3.map(|t| &t.kind)), (Some(TokenKind::Ident(_)), Some(TokenKind::Colon)))
    }

    fn parse_member_struct(&mut self) -> Result<StructDecl> {
        self.expect(TokenKind::MemberKw)?;
        let name = self.parse_ident()?;
        self.expect(TokenKind::LBrace)?;
        let mut fields = Vec::new();
        let mut embedded = Vec::new();
        while !self.check(&TokenKind::RBrace) {
            // Embedded member: starts with Ident and followed by ';' or comma/newline
            let save = self.pos;
            if let Some(TokenKind::Ident(id)) = self.peek_kind() {
                // lookahead if the next token is ':' => named field with type
                self.bump_kind();
                if self.check(&TokenKind::Colon) {
                    self.bump_kind();
                    let ty = self.parse_type()?;
                    fields.push((id, ty));
                } else {
                    // treat as embedded type name (no methods imported, just fields later at runtime)
                    embedded.push(id);
                }
            } else {
                self.pos = save;
                break;
            }
        }
        self.expect(TokenKind::RBrace)?;
        Ok(StructDecl { name, fields, embedded, is_pub: false })
    }
}


