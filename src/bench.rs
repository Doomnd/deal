use anyhow::{bail, Result};
use std::time::Instant;

// Parse a Deal source into an AST once
fn parse_deal(src: &str) -> Result<crate::ast::CompilationUnit> {
    let tokens = crate::lexer::Lexer::new(src).collect::<Result<Vec<_>, _>>()?;
    let mut parser = crate::parser::Parser::new(&tokens);
    let unit = parser.parse_compilation_unit()?;
    if !parser.errors.is_empty() {
        // We do not have a path/filename in bench; use "<bench>"
        crate::diagnostics::print_diagnostics("<bench>", src, &parser.errors);
        bail!("parse errors");
    }
    Ok(unit)
}

// Run the interpreter once on the provided, already parsed AST
fn run_deal_once(unit: &crate::ast::CompilationUnit) -> Result<()> {
    crate::runtime::runner::run_main(unit)
}

pub fn run_bench() -> Result<()> {
    // Fair benchmark: same number of adds in Rust vs Deal's interpreter runtime.
    // We parse once (excluded from timing), then time the execution.
    let iterations: u64 = 200_000;

    // Rust baseline: perform `iterations` simple additions
    let rust_start = Instant::now();
    let mut acc = 0.0f64;
    for _ in 0..iterations {
        acc += 1.0;
    }
    // prevent optimization
    std::hint::black_box(acc);
    let rust_dur = rust_start.elapsed();

    // Deal program that performs the same number of additions in its main
    // dealer Main { fn main() { let mut acc = 0; for i in 1..=ITER { acc = acc + 1; } } }
    let deal_src = format!(
        "dealer Main {{ fn main() {{ let mut acc = 0; for i in 1..={iters} {{ acc = acc + 1; }} }} }}",
        iters = iterations
    );

    // Parse once (excluded from runtime timing)
    let unit = parse_deal(&deal_src)?;

    // Time interpreter runtime only
    let deal_start = Instant::now();
    run_deal_once(&unit)?;
    let deal_dur = deal_start.elapsed();

    println!(
        "Rust: {} adds in {:?}  ({:.1} Mops/s)",
        iterations,
        rust_dur,
        (iterations as f64) / rust_dur.as_secs_f64() / 1e6
    );
    println!(
        "Deal (interp): {} adds in {:?}  ({:.1} kops/s)",
        iterations,
        deal_dur,
        (iterations as f64) / deal_dur.as_secs_f64() / 1e3
    );

    // Additional benchmark: iterate a list and sum elements using `for _, v in list`
    let list_len: usize = 10_000;
    let mut list_lit = String::with_capacity(list_len * 6);
    list_lit.push('[');
    for i in 0..list_len {
        if i > 0 { list_lit.push_str(", "); }
        list_lit.push_str(&i.to_string());
    }
    list_lit.push(']');

    let deal_list_prog = format!(
        "dealer Main {{ fn main() {{ let mut acc = 0; let xs = {xs}; for _, v in xs {{ acc = acc + v; }} }} }}",
        xs = list_lit
    );
    let unit_list = parse_deal(&deal_list_prog)?;
    let list_start = Instant::now();
    run_deal_once(&unit_list)?;
    let list_dur = list_start.elapsed();
    println!(
        "Deal (list iter): {} elems in {:?}  ({:.1} kiter/s)",
        list_len,
        list_dur,
        (list_len as f64) / list_dur.as_secs_f64() / 1e3
    );

    // 1) Branching numeric loop: if i % 2 == 0 then +1 else +2
    let iterations_branch: u64 = 200_000;
    let rust_branch_start = Instant::now();
    let mut acc_b = 0.0f64;
    for i in 1..=iterations_branch {
        if i % 2 == 0 { acc_b += 1.0; } else { acc_b += 2.0; }
    }
    std::hint::black_box(acc_b);
    let rust_branch_dur = rust_branch_start.elapsed();

    let deal_branch_src = format!(
        "dealer Main {{ fn main() {{ let mut acc = 0; for i in 1..={iters} {{ if i % 2 == 0 {{ acc = acc + 1; }} else {{ acc = acc + 2; }} }} }} }}",
        iters = iterations_branch
    );
    let unit_branch = parse_deal(&deal_branch_src)?;
    let deal_branch_start = Instant::now();
    run_deal_once(&unit_branch)?;
    let deal_branch_dur = deal_branch_start.elapsed();
    println!(
        "Branch loop — Rust: {:?} ({:.1} Mops/s) | Deal: {:?} ({:.1} kops/s)",
        rust_branch_dur,
        (iterations_branch as f64) / rust_branch_dur.as_secs_f64() / 1e6,
        deal_branch_dur,
        (iterations_branch as f64) / deal_branch_dur.as_secs_f64() / 1e3,
    );

    // 2) Nested loops: 1000 x 200 iterations (200k inner ops)
    let outer: u64 = 1_000;
    let inner: u64 = 200;
    let total_nested = outer * inner;
    let rust_nested_start = Instant::now();
    let mut acc_n = 0.0f64;
    for _ in 0..outer {
        for _ in 0..inner { acc_n += 1.0; }
    }
    std::hint::black_box(acc_n);
    let rust_nested_dur = rust_nested_start.elapsed();

    let deal_nested_src = format!(
        "dealer Main {{ fn main() {{ let mut acc = 0; for _ in 1..={outer} {{ for _ in 1..={inner} {{ acc = acc + 1; }} }} }} }}",
        outer = outer,
        inner = inner
    );
    let unit_nested = parse_deal(&deal_nested_src)?;
    let deal_nested_start = Instant::now();
    run_deal_once(&unit_nested)?;
    let deal_nested_dur = deal_nested_start.elapsed();
    println!(
        "Nested loops — Rust: {:?} ({:.1} Mops/s) | Deal: {:?} ({:.1} kops/s)",
        rust_nested_dur,
        (total_nested as f64) / rust_nested_dur.as_secs_f64() / 1e6,
        deal_nested_dur,
        (total_nested as f64) / deal_nested_dur.as_secs_f64() / 1e3,
    );

    // 3) List filter loop: sum v where index % 3 == 0
    let list_len2: usize = 20_000;
    let mut list_lit2 = String::with_capacity(list_len2 * 6);
    list_lit2.push('[');
    for i in 0..list_len2 {
        if i > 0 { list_lit2.push_str(", "); }
        list_lit2.push_str(&i.to_string());
    }
    list_lit2.push(']');
    let rust_listf_start = Instant::now();
    let mut acc_l = 0.0f64;
    for (i, v) in (0..list_len2).enumerate() { if i % 3 == 0 { acc_l += v as f64; } }
    std::hint::black_box(acc_l);
    let rust_listf_dur = rust_listf_start.elapsed();

    let deal_listf_src = format!(
        "dealer Main {{ fn main() {{ let mut acc = 0; let xs = {xs}; for i, v in xs {{ if i % 3 == 0 {{ acc = acc + v; }} }} }} }}",
        xs = list_lit2
    );
    let unit_listf = parse_deal(&deal_listf_src)?;
    let deal_listf_start = Instant::now();
    run_deal_once(&unit_listf)?;
    let deal_listf_dur = deal_listf_start.elapsed();
    println!(
        "List filter — Rust: {:?} ({:.1} Miter/s) | Deal: {:?} ({:.1} kiter/s)",
        rust_listf_dur,
        (list_len2 as f64) / rust_listf_dur.as_secs_f64() / 1e6,
        deal_listf_dur,
        (list_len2 as f64) / deal_listf_dur.as_secs_f64() / 1e3,
    );

    // Useful task: Fibonacci iteration
    let fib_n: u64 = 200_000; // same scale as adds
    let rust_fib_start = Instant::now();
    let mut a = 0.0f64; let mut b = 1.0f64;
    for _ in 0..fib_n { let next = a + b; a = b; b = next; }
    std::hint::black_box((a, b));
    let rust_fib_dur = rust_fib_start.elapsed();

    let deal_fib_src = format!(
        "dealer Main {{ fn main() {{ let mut a = 0; let mut b = 1; for _ in 1..={n} {{ let next = a + b; a = b; b = next; }} }} }}",
        n = fib_n
    );
    let unit_fib = parse_deal(&deal_fib_src)?;
    let deal_fib_start = Instant::now();
    run_deal_once(&unit_fib)?;
    let deal_fib_dur = deal_fib_start.elapsed();
    println!(
        "Fibonacci — Rust: {:?} ({:.1} Miter/s) | Deal: {:?} ({:.1} kiter/s)",
        rust_fib_dur,
        (fib_n as f64) / rust_fib_dur.as_secs_f64() / 1e6,
        deal_fib_dur,
        (fib_n as f64) / deal_fib_dur.as_secs_f64() / 1e3,
    );

    Ok(())
}

// A "compiled" benchmark that simulates Deal compiled-to-Rust by running the same
// addition loop in Rust. This gives you a comparable upper bound for a Deal→Rust backend.
pub fn run_bench_compiled() -> Result<()> {
    let iterations: u64 = 200_000;
    let start = Instant::now();
    let mut acc = 0.0f64;
    for _ in 0..iterations {
        acc += 1.0;
    }
    std::hint::black_box(acc);
    let dur = start.elapsed();
    println!(
        "Deal (compiled-to-Rust sim): {} adds in {:?}  ({:.1} Mops/s)",
        iterations,
        dur,
        (iterations as f64) / dur.as_secs_f64() / 1e6
    );
    Ok(())
}


