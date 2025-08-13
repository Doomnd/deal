// Runtime: thread orchestration, execution, and value model
use crate::ast::*;
use anyhow::{bail, Result};
use rustc_hash::FxHashMap as HashMap;
use std::cell::RefCell;
use std::rc::Rc;
use crossbeam_channel::{unbounded, Sender, Receiver};
use std::thread::{self, JoinHandle};

/// Execute the `Main.main` entry and supervise spawned dealers
pub fn run_main(unit: &CompilationUnit) -> Result<()> {
    let mut entries: HashMap<String, Block> = HashMap::default();
    let mut main_fn: Option<Block> = None;
    for d in &unit.decls {
        if let Decl::Dealer(dd) = d {
            if let Some(entry) = &dd.entry_fn {
                if dd.name.0 == "Main" && entry.sig.name.0 == "main" {
                    main_fn = Some(entry.body.clone());
                } else {
                    entries.insert(dd.name.0.clone(), entry.body.clone());
                }
            }
        }
    }
    let main_body = main_fn.ok_or_else(|| anyhow::anyhow!("Main dealer with fn main not found"))?;
    // Collect free functions and struct methods
    let mut free_functions: HashMap<String, FuncDecl> = HashMap::default();
    let mut methods: HashMap<String, HashMap<String, FuncDecl>> = HashMap::default();
    for d in &unit.decls {
        if let Decl::Fn(f) = d {
            if let Some((_, recv_ty)) = &f.sig.receiver {
                if let TypeName::Named(Ident(type_name)) = recv_ty {
                    methods.entry(type_name.clone()).or_default().insert(f.sig.name.0.clone(), f.clone());
                }
            } else {
                free_functions.insert(f.sig.name.0.clone(), f.clone());
            }
        }
    }
    let mut ctx = RuntimeCtx { dealer_entries: entries, dealer_handles: Vec::new(), dealer_inbox: HashMap::default(), free_functions, methods };
    let mut vars: HashMap<String, Rc<RefCell<Value>>> = HashMap::default();
    exec_block(&mut ctx, &main_body, &mut vars)?;
    for h in ctx.dealer_handles { let _ = h.join(); }
    Ok(())
}

/// Process-wide runtime state for dealers and messaging
struct RuntimeCtx {
    dealer_entries: HashMap<String, Block>,
    dealer_handles: Vec<JoinHandle<()>>,
    dealer_inbox: HashMap<String, Sender<RpcMessage>>, // Main -> dealer
    free_functions: HashMap<String, FuncDecl>,
    methods: HashMap<String, HashMap<String, FuncDecl>>, // type_name -> (method_name -> func)
}

/// Execute a block with the given environment
fn exec_block(ctx: &mut RuntimeCtx, block: &Block, vars: &mut HashMap<String, Rc<RefCell<Value>>>) -> Result<()> {
    for stmt in &block.stmts {
        match stmt {
            Stmt::Expr(expr) => { let _ = exec_expr_env(ctx, expr, vars)?; }
            Stmt::Let { name, init, .. } => {
                let val = if let Some(e) = init { exec_expr_env(ctx, e, vars)? } else { Value::Unit };
                vars.insert(name.0.clone(), Rc::new(RefCell::new(val)));
            }
            Stmt::Assign { target, value } => {
                let val = exec_expr_env(ctx, value, vars)?;
                if let Some(cell) = vars.get(&target.0) {
                    *cell.borrow_mut() = val;
                } else {
                    vars.insert(target.0.clone(), Rc::new(RefCell::new(val)));
                }
            }
            Stmt::IndexAssign { target, index, value } => {
                let idx_v = exec_expr_env(ctx, index, vars)?;
                let val_v = exec_expr_env(ctx, value, vars)?;
                let idx = match idx_v { Value::Num(n) => n as isize, Value::Str(s) => {
                    // allow string keys -> map-like via Struct fields fallback
                    let key = s;
                    match vars.get(&target.0) {
                        Some(cell) => {
                            let mut tv = cell.borrow_mut();
                            if let Value::Struct { fields, .. } = &mut *tv { fields.insert(key, val_v); continue; }
                            bail!("index assignment on non-map with string key");
                        }
                        None => { bail!("unknown variable"); }
                    }
                } _ => bail!("index must be number or string") };
                match vars.get(&target.0) {
                    Some(cell) => {
                        let mut tv = cell.borrow_mut();
                        match &mut *tv {
                            Value::List(items) => {
                                if idx < 0 || (idx as usize) >= items.len() { bail!("index out of bounds"); }
                                items[idx as usize] = val_v;
                            }
                            Value::Struct { .. } => bail!("use string key for struct field assignment"),
                            _ => bail!("index assignment on non-list"),
                        }
                    }
                    None => bail!("unknown variable"),
                }
            }
            Stmt::If { pre_binding, cond, then_block, elifs, else_block } => {
                if let Some(b) = pre_binding {
                    let val = if let Some(e) = &b.init { exec_expr_env(ctx, e, vars)? } else { Value::Unit };
                    vars.insert(b.name.0.clone(), Rc::new(RefCell::new(val)));
                }
                let c = exec_expr_env(ctx, cond, vars)?;
                if truthy(&c) {
                    exec_block(ctx, then_block, vars)?;
                } else {
                    let mut taken = false;
                    for (ec, eb) in elifs {
                        if truthy(&exec_expr_env(ctx, ec, vars)?) { exec_block(ctx, eb, vars)?; taken = true; break; }
                    }
                    if !taken { if let Some(b) = else_block { exec_block(ctx, b, vars)?; } }
                }
            }
            Stmt::StartDealer { name } => {
                if let Some(entry) = ctx.dealer_entries.get(&name.0).cloned() {
                    println!("starting dealer {}", name.0);
                    let (tx, rx) = unbounded::<RpcMessage>();
                    let dealer_name = name.0.clone();
                    ctx.dealer_inbox.insert(dealer_name.clone(), tx);
                    let handle = thread::spawn(move || {
                        dealer_loop(dealer_name, entry, rx);
                    });
                    ctx.dealer_handles.push(handle);
                } else {
                    eprintln!("unknown dealer {}", name.0);
                }
            }
            Stmt::For (for_decl) => {
                exec_for_loop(ctx, for_decl, vars)?;
            }
        }
    }
    Ok(())
}

/// Run a numeric for-range loop
fn exec_for_loop(ctx: &mut RuntimeCtx, for_decl: &ForDecl, vars: &mut HashMap<String, Rc<RefCell<Value>>>) -> Result<()> {
    let iterable = exec_expr_env(ctx, &for_decl.iterable,vars)?;
    match iterable {
        Value::Range {start,end,inclusive} => {
            let mut current = start;
            while current < end || (inclusive && current <= end){
                // bind only if not discard '_'
                if let Some(first) = for_decl.var.get(0) {
                    if first.0 != "_" {
                        vars.insert(first.0.clone(), Rc::new(RefCell::new(Value::Num(current))));
                    }
                }
                exec_block(ctx, &for_decl.body, vars)?;
                current += 1.0;
            }
        }
        Value::List(items) => {
            if for_decl.var.is_empty() {
                bail!("for loop needs at least one variable");
            }
            if for_decl.var.len() == 1 {
                let name = for_decl.var[0].0.clone();
                for (i, v) in items.into_iter().enumerate() {
                    // implicit index available as `_index`
                    vars.insert("_index".to_string(), Rc::new(RefCell::new(Value::Num(i as f64))));
                    if name != "_" { vars.insert(name.clone(), Rc::new(RefCell::new(v))); }
                    exec_block(ctx, &for_decl.body, vars)?;
                }
            } else if for_decl.var.len() == 2 {
                let idx_name = for_decl.var[0].0.clone();
                let val_name = for_decl.var[1].0.clone();
                for (i, v) in items.into_iter().enumerate() {
                    if idx_name != "_" { vars.insert(idx_name.clone(), Rc::new(RefCell::new(Value::Num(i as f64)))); }
                    if val_name != "_" { vars.insert(val_name.clone(), Rc::new(RefCell::new(v))); }
                    // implicit index mirrors named one
                    vars.insert("_index".to_string(), Rc::new(RefCell::new(Value::Num(i as f64))));
                    exec_block(ctx, &for_decl.body, vars)?;
                }
            } else {
                bail!("for over list supports at most 2 variables");
            }
        }
        _ =>{ bail!("unsupported iterable type for loop"); }
    }
    Ok(())
}

/// Future RPC messages for dealer communications
enum RpcMessage {
    Shutdown,
}

/// Dealer thread main loop (MVP: just run entry block once)
fn dealer_loop(_name: String, entry: Block, _rx: Receiver<RpcMessage>) {
    let mut dummy = RuntimeCtx { dealer_entries: HashMap::default(), dealer_handles: Vec::new(), dealer_inbox: HashMap::default(), free_functions: HashMap::default(), methods: HashMap::default() };
    let mut env: HashMap<String, Rc<RefCell<Value>>> = HashMap::default();
    let _ = exec_block(&mut dummy, &entry, &mut env);
}

/// Evaluate an expression under the given environment
fn exec_expr_env(ctx: &mut RuntimeCtx, expr: &Expr, vars: &mut HashMap<String, Rc<RefCell<Value>>>) -> Result<Value> {
    match expr {
        Expr::String(s) => Ok(Value::Str(s.clone())),
        Expr::Number(n) => Ok(Value::Num(*n)),
        Expr::Bool(b) => Ok(Value::Bool(*b)),
        Expr::Ident(Ident(name)) => Ok(vars.get(name).map(|c| c.borrow().clone()).unwrap_or(Value::Unit)),
        Expr::StructLit { name, fields } => {
            let mut map = HashMap::default();
            for (k, vexpr) in fields { map.insert(k.0.clone(), exec_expr_env(ctx, vexpr, vars)?); }
            Ok(Value::Struct { name: name.0.clone(), fields: map })
        }
        Expr::List(items) => {
            let mut out = Vec::with_capacity(items.len());
            for e in items { out.push(exec_expr_env(ctx, e, vars)?); }
            Ok(Value::List(out))
        }
        Expr::Unary { op, expr } => {
            let v = exec_expr_env(ctx, expr, vars)?;
            match (op, v) {
                (UnOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                (UnOp::Neg, Value::Num(n)) => Ok(Value::Num(-n)),
                _ => bail!("type error in unary op"),
            }
        }
        Expr::Ref(inner) => {
            // For now, reference just returns the current value; full aliasing would require LValue support
            // This stub allows syntax without breaking runtime; mut-by-ref can be added next.
            let v = exec_expr_env(ctx, inner, vars)?;
            Ok(v)
        }
        Expr::Call { callee, args } => {
            if let Expr::Ident(Ident(name)) = &**callee {
                if name == "print" {
                    if args.is_empty() { println!(); return Ok(Value::Unit); }
                    for (i, a) in args.iter().enumerate() {
                        let v = exec_expr_env(ctx, a, vars)?;
                        if i > 0 { print!(" "); }
                        print!("{}", v);
                    }
                    println!();
                    return Ok(Value::Unit);
                }
                let f_opt = ctx.free_functions.get(name).cloned();
                if let Some(f) = f_opt {
                    let mut local_env: HashMap<String, Rc<RefCell<Value>>> = HashMap::default();
                    if f.sig.params.len() != args.len() { bail!("arity mismatch calling {}", name); }
                    for ((pname, _), a) in f.sig.params.iter().zip(args.iter()) {
                        let av = exec_expr_env(ctx, a, vars)?;
                        local_env.insert(pname.0.clone(), Rc::new(RefCell::new(av)));
                    }
                    exec_block(ctx, &f.body, &mut local_env)?;
                    return Ok(Value::Unit);
                }
            }
            if let Expr::Member { target, name } = &**callee {
                let recv = exec_expr_env(ctx, target, vars)?;
                if let Value::Struct { name: type_name, .. } = &recv {
                    let f_opt = ctx
                        .methods
                        .get(type_name)
                        .and_then(|mtbl| mtbl.get(&name.0))
                        .cloned();
                    if let Some(f) = f_opt {
                        let mut local_env: HashMap<String, Rc<RefCell<Value>>> = HashMap::default();
                        let mut recv_var: Option<Ident> = None;
                        if let Some((recv_name, _)) = &f.sig.receiver { recv_var = Some(recv_name.clone()); local_env.insert(recv_name.clone().0, Rc::new(RefCell::new(recv.clone()))); }
                        if f.sig.params.len() != args.len() { bail!("arity mismatch calling {}.{}", type_name, name.0); }
                        for ((pname, _), a) in f.sig.params.iter().zip(args.iter()) {
                            let av = exec_expr_env(ctx, a, vars)?;
                            local_env.insert(pname.0.clone(), Rc::new(RefCell::new(av)));
                        }
                        exec_block(ctx, &f.body, &mut local_env)?;
                        if let Some(rn) = recv_var {
                            return Ok(local_env.get(&rn.0).map(|c| c.borrow().clone()).unwrap_or(Value::Unit));
                        }
                        return Ok(Value::Unit);
                    }
                }
            }
            bail!("unsupported call")
        }
        Expr::Binary { op, left, right } => {
            let lv = exec_expr_env(ctx, left, vars)?;
            let rv = exec_expr_env(ctx, right, vars)?;
            match (op, lv, rv) {
                (BinOp::Add, Value::Num(a), Value::Num(b)) => Ok(Value::Num(a + b)),
                (BinOp::Sub, Value::Num(a), Value::Num(b)) => Ok(Value::Num(a - b)),
                (BinOp::Mul, Value::Num(a), Value::Num(b)) => Ok(Value::Num(a * b)),
                (BinOp::Div, Value::Num(a), Value::Num(b)) => Ok(Value::Num(a / b)),
                (BinOp::Mod, Value::Num(a), Value::Num(b)) => Ok(Value::Num(a % b)),
                (BinOp::Pow, Value::Num(a), Value::Num(b)) => Ok(Value::Num(a.powf(b))),
                (BinOp::Lt, Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a < b)),
                (BinOp::Le, Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a <= b)),
                (BinOp::Gt, Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a > b)),
                (BinOp::Ge, Value::Num(a), Value::Num(b)) => Ok(Value::Bool(a >= b)),
                (BinOp::Eq, Value::Num(a), Value::Num(b)) => Ok(Value::Bool((a - b).abs() < std::f64::EPSILON)),
                (BinOp::Ne, Value::Num(a), Value::Num(b)) => Ok(Value::Bool((a - b).abs() >= std::f64::EPSILON)),
                _ => bail!("type error in binary op"),
            }
        }
        Expr::PipeArrow(lhs, rhs, pattern) => {
            // Dataflow: lhs |> rhs -> pattern
            let result: Value = match &**rhs {
                Expr::Call { callee, args } => {
                    // build a synthetic call with lhs as first arg
                    let mut new_args = Vec::with_capacity(args.len() + 1);
                    new_args.push((**lhs).clone());
                    new_args.extend(args.clone());
                    exec_expr_env(ctx, &Expr::Call { callee: callee.clone(), args: new_args }, vars)?
                }
                Expr::Member { .. } => {
                    // treat as method call with zero args: lhs |> obj.method  => obj.method(lhs)
                    exec_expr_env(ctx, &Expr::Call { callee: rhs.clone(), args: vec![(**lhs).clone()] }, vars)?
                }
                _ => {
                    // default: return rhs(lhs) if rhs is Ident, else just return lhs
                    if let Expr::Ident(_) = &**rhs {
                        exec_expr_env(ctx, &Expr::Call { callee: rhs.clone(), args: vec![(**lhs).clone()] }, vars)?
                    } else {
                        exec_expr_env(ctx, lhs, vars)?
                    }
                }
            };
            if let Some(pat) = pattern {
                apply_pattern(pat, &result, vars)?;
            }
            Ok(result)
        }
        Expr::Member { target, name } => {
            let v = exec_expr_env(ctx, target, vars)?;
            match v {
                Value::Struct { fields, .. } => Ok(fields.get(&name.0).cloned().unwrap_or(Value::Unit)),
                _ => bail!("member access on non-struct"),
            }
        }
        Expr::Index { target, index } => {
            let container = exec_expr_env(ctx, target, vars)?;
            let key = exec_expr_env(ctx, index, vars)?;
            match (container, key) {
                (Value::List(items), Value::Num(n)) => {
                    let idx = n as isize;
                    if idx < 0 || (idx as usize) >= items.len() { bail!("index out of bounds"); }
                    Ok(items[idx as usize].clone())
                }
                (Value::Struct { fields, .. }, Value::Str(field)) => {
                    Ok(fields.get(&field).cloned().unwrap_or(Value::Unit))
                }
                (Value::Struct { .. }, _) => bail!("struct index must be string"),
                (Value::List(_), _) => bail!("list index must be number"),
                _ => bail!("indexing unsupported target"),
            }
        }
        Expr::Slice { target, start, end, inclusive } => {
            let list = exec_expr_env(ctx, target, vars)?;
            match list {
                Value::List(items) => {
                    let len = items.len();
                    let s = if let Some(s) = start { match exec_expr_env(ctx, s, vars)? { Value::Num(n) => (n as isize).max(0) as usize, _ => bail!("slice start must be number") } } else { 0 };
                    let e = if let Some(e) = end { match exec_expr_env(ctx, e, vars)? { Value::Num(n) => (n as isize).max(0) as usize, _ => bail!("slice end must be number") } } else { len };
                    if s > e || e > len { bail!("invalid slice bounds"); }
                    let end_excl = if *inclusive { e.saturating_add(1).min(len) } else { e };
                    Ok(Value::List(items[s..end_excl].to_vec()))
                }
                _ => bail!("slicing non-list"),
            }
        }
        Expr::Await(_) | Expr::Recv | Expr::Send { .. } | Expr::Unit => Ok(Value::Unit),
        Expr::EmptyListOf(_) => Ok(Value::List(Vec::new())),
        Expr::Range { start, end, inclusive } => {
            let start_val = exec_expr_env(ctx, start, vars)?;
            let end_val = exec_expr_env(ctx, end, vars)?;
            match (start_val, end_val){
                (Value::Num(s), Value::Num(e)) => 
                Ok(Value::Range { start: s, end: e, inclusive: *inclusive }),
                _ => bail!("Range bounds must be numbers"),
            }
        }
        Expr::Tuple(items) => {
            let mut out = Vec::with_capacity(items.len());
            for e in items { out.push(exec_expr_env(ctx, e, vars)?); }
            Ok(Value::Tuple(out))
        }
    }
}

/// Dynamic runtime values
#[derive(Debug, Clone)]
    pub enum Value { 
    Unit,
    Num(f64),
    Str(String),
    Bool(bool),
    Struct { name: String, fields: HashMap<String, Value> },
    Range {start: f64, end: f64, inclusive: bool},
    List(Vec<Value>),
    Tuple(Vec<Value>),
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Num(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "{}", s),
            Value::Bool(b) => write!(f, "{}", b),
            Value::Struct { name, fields } => {
                write!(f, "{} {{", name)?;
                let mut first = true;
                for (k, v) in fields.iter() {
                    if !first { write!(f, ", ")?; }
                    first = false;
                    write!(f, "{}: {}", k, v)?;
                }
                write!(f, "}}")
            }
            Value::Range { start, end, inclusive } => {
                if *inclusive { write!(f, "{}..={}", start, end) } else { write!(f, "{}..{}", start, end) }
            }
            Value::List(items) => {
                write!(f, "[")?;
                for (i, v) in items.iter().enumerate() {
                    if i > 0 { write!(f, " | ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, "]")
            }
            Value::Tuple(items) => {
                write!(f, "(")?;
                for (i, v) in items.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}", v)?;
                }
                write!(f, ")")
            }
        }
    }
}

fn truthy(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        Value::Num(n) => *n != 0.0,
        Value::Str(s) => !s.is_empty(),
        Value::Struct { .. } => true,
        Value::Unit => false,
        Value::Range { .. } => true,
        Value::List(items) => !items.is_empty(),
        Value::Tuple(items) => !items.is_empty(),
    }
}
fn apply_pattern(
    pat: &Pattern,
    value: &Value,
    vars: &mut HashMap<String, Rc<RefCell<Value>>>,
) -> Result<()> {
    match (pat, value) {
        (Pattern::Ident(name), v) => {
            vars.insert(name.0.clone(), Rc::new(RefCell::new(v.clone())));
        }
        (Pattern::Tuple(patterns), Value::Tuple(items)) => {
            if patterns.len() != items.len() {
                bail!("pattern arity mismatch");
            }
            for (p, item) in patterns.iter().zip(items.iter()) {
                apply_pattern(p, item, vars)?;
            }
        }
        (Pattern::Wildcard, _) => {}
        _ => bail!("pattern mismatch"),
    }
    Ok(())
}




