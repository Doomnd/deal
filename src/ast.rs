#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ident(pub String);

#[derive(Debug, Clone, PartialEq)]
pub enum TypeName {
    // integers
    Int,   // legacy alias for i64
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    // floats
    F32,
    F64,
    // other primitives
    Char,
    Any,
    Dealer, // dynamic dealer type (interface-like)
    String,
    Bool,
    Named(Ident),
    Generic { base: Ident, args: Vec<TypeName> },
    List(Box<TypeName>),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CompilationUnit {
    pub decls: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Decl {
    Dealer(DealerDecl),
    Trait(TraitDecl),
    Struct(StructDecl),
    Impl(ImplDecl),
    Fn(FuncDecl),
}

#[derive(Debug, Clone, PartialEq)]
pub struct DealerDecl {
    pub name: Ident,
    pub members: Vec<Ident>,
    pub trait_name: Option<Ident>,
    pub entry_fn: Option<FuncDecl>,
    pub is_pub: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TraitDecl {
    pub name: Ident,
    pub methods: Vec<FuncSig>,
    pub is_pub: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDecl {
    pub name: Ident,
    pub fields: Vec<(Ident, TypeName)>,
    pub embedded: Vec<Ident>,
    pub is_pub: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ImplDecl {
    pub trait_name: Ident,
    pub for_type: Ident,
    pub methods: Vec<FuncDecl>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncSig {
    pub name: Ident,
    pub params: Vec<(Ident, TypeName)>,
    pub ret: TypeName,
    pub is_pub: bool,
    pub receiver: Option<(Ident, TypeName)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FuncDecl {
    pub sig: FuncSig,
    pub body: Block,
}


#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let {
        name: Ident,
        is_mut: bool,
        ty: Option<TypeName>,
        init: Option<Expr>,
    },
    Assign { target: Ident, value: Expr },
    If {
        pre_binding: Option<LetBinding>,
        cond: Expr,
        then_block: Block,
        elifs: Vec<(Expr, Block)>,
        else_block: Option<Block>,
    },
    StartDealer { name: Ident },
    Expr(Expr),
    For(ForDecl)
,
    IndexAssign { target: Ident, index: Expr, value: Expr },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ForDecl{
    pub  var : Vec<Ident>,
    pub iterable : Expr,
    pub body : Block, 
}
#[derive(Debug, Clone, PartialEq)]
pub struct LetBinding {
    pub name: Ident,
    pub is_mut: bool,
    pub ty: Option<TypeName>,
    pub init: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Unit,
    Ident(Ident),
    String(String),
    Number(f64),
    Bool(bool),
    List(Vec<Expr>),
    EmptyListOf(TypeName),
    Index { target: Box<Expr>, index: Box<Expr> },
    Slice { target: Box<Expr>, start: Option<Box<Expr>>, end: Option<Box<Expr>>, inclusive: bool },
    Unary { op: UnOp, expr: Box<Expr> },
    Ref(Box<Expr>),
    Await(Box<Expr>),
    Send { target: Box<Expr>, message: Box<Expr> },
    Recv, // await recv()
    Call { callee: Box<Expr>, args: Vec<Expr> },
    Member { target: Box<Expr>, name: Ident },
    Binary { op: BinOp, left: Box<Expr>, right: Box<Expr> },
    StructLit { name: Ident, fields: Vec<(Ident, Expr)> },
    Range { start: Box<Expr>, end:Box<Expr>, inclusive : bool},
    PipeArrow(Box<Expr>, Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum BinOp { Add, Sub, Mul, Div, Mod, Pow, Lt, Le, Gt, Ge, Eq, Ne }

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum UnOp { Not, Neg }


