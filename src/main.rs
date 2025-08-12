// Wire modules with custom file names (use lowercase for portability)
#[path = "ast.rs"]
mod ast;
#[path = "lexer.rs"]
mod lexer;
#[path = "parser.rs"]
mod parser;
mod diagnostics;
mod runtime;
mod bench;
mod codegen;

use anyhow::{bail, Context, Result};
use clap::{Parser as ClapParser, Subcommand};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(ClapParser, Debug)]
#[command(name = "deal", version, about = "Deal the poker language tool")] 
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand, Debug)]
enum Commands {
    /// Run a source file (.deal) or a directory (uses ./main.deal)
    Run { path: PathBuf },
    /// Build/emit compiled artifacts
    Build {
        /// Source file or directory (defaults to current dir)
        #[arg(default_value = ".")]
        path: PathBuf,
        /// Emit Rust to the given path
        #[arg(long)]
        emit_rs: Option<PathBuf>,
        /// Compile the emitted Rust with rustc -O
        #[arg(long)]
        compile: bool,
        /// Run the produced executable after compiling
        #[arg(long)]
        run: bool,
        /// Output executable path (when compiling); defaults to ./out.exe on Windows or ./out on others
        #[arg(long)]
        out_exe: Option<PathBuf>,
    },
    /// Run tests (placeholder)
    Test {},
    /// Run built-in benchmarks
    Bench {
        /// Also run a compiled (Rust) variant that simulates Deal compiled-to-Rust
        #[arg(long)]
        compiled: bool,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();
    let cmd = cli.command.unwrap_or(Commands::Run { path: PathBuf::from(".") });
    match cmd {
        Commands::Run { path } => run_path(&path),
        Commands::Build { path, emit_rs, compile, run, out_exe } => build_path(&path, emit_rs, compile, run, out_exe),
        Commands::Test {} => { println!("test: ok (placeholder)"); Ok(()) },
        Commands::Bench { compiled } => {
            if compiled { bench::run_bench_compiled()?; }
            bench::run_bench()
        },
        // later: add `deal build --emit-rs out.rs` and write file with codegen::emit_rust
    }
}

fn run_path(path: &PathBuf) -> Result<()> {
    let path = resolve_entry(path)?;
    ensure_deal_file(&path)?;
    let src = fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let mut tokens = crate::lexer::Lexer::new(&src).collect::<Result<Vec<_>, _>>()?;
    for token in &tokens{
    let f = format!("name : {:?} offset : {} len : {}",token.kind, token.offset, token.len);
    print!("{}\n",f.to_lowercase());
    }
    // Append synthetic EOF token for better EOF diagnostics (offset at end of file)
    tokens.push(crate::lexer::Token { kind: crate::lexer::TokenKind::Semicolon, offset: src.len(), len: 0 });
    let mut p = crate::parser::Parser::new(&tokens);
    let unit = match p.parse_compilation_unit() {
        Ok(u) => u,
        Err(e) => {
            crate::diagnostics::print_diagnostics(&path.display().to_string(), &src, &p.errors);
            return Err(e);
        }
    };
    if !p.errors.is_empty() {
        crate::diagnostics::print_diagnostics(&path.display().to_string(), &src, &p.errors);
        bail!("parse errors");
    }
    // Use new runtime grouping
    crate::runtime::runner::run_main(&unit)?;
    println!("ok: ran {} (parsed, {} tokens)", path.display(), tokens.len());
    Ok(())
}

fn build_path(path: &PathBuf, emit_rs: Option<PathBuf>, compile: bool, run_after: bool, out_exe: Option<PathBuf>) -> Result<()> {
    let path = resolve_entry(path)?;
    ensure_deal_file(&path)?;
    let src = fs::read_to_string(&path).with_context(|| format!("reading {}", path.display()))?;
    let mut tokens = crate::lexer::Lexer::new(&src).collect::<Result<Vec<_>, _>>()?;
    tokens.push(crate::lexer::Token { kind: crate::lexer::TokenKind::Semicolon, offset: src.len(), len: 0 });
    let mut p = crate::parser::Parser::new(&tokens);
    let unit = match p.parse_compilation_unit() {
        Ok(u) => u,
        Err(e) => {
            crate::diagnostics::print_diagnostics(&path.display().to_string(), &src, &p.errors);
            return Err(e);
        }
    };
    if !p.errors.is_empty() {
        crate::diagnostics::print_diagnostics(&path.display().to_string(), &src, &p.errors);
        bail!("parse errors");
    }

    let rs = crate::codegen::emit_rust(&unit)?;
    let rs_path = if let Some(p) = emit_rs { p } else { PathBuf::from("out.rs") };
    fs::write(&rs_path, rs).with_context(|| format!("writing {}", rs_path.display()))?;
    println!("emitted Rust: {}", rs_path.display());

    if compile {
        let exe = if let Some(out) = out_exe { out } else {
            if cfg!(windows) { PathBuf::from("out.exe") } else { PathBuf::from("out") }
        };
        let status = std::process::Command::new("rustc")
            .arg("-O")
            .arg(&rs_path)
            .arg("-o").arg(&exe)
            .status()
            .context("invoking rustc")?;
        if !status.success() { bail!("rustc failed"); }
        println!("compiled: {}", exe.display());
        if run_after {
            let status = std::process::Command::new(&exe)
                .status()
                .context("running compiled exe")?;
            if !status.success() { bail!("program exited with error"); }
        }
    }
    Ok(())
}

fn resolve_entry(input: &Path) -> Result<PathBuf> {
    if input.is_dir() {
        let candidate = input.join("main.deal");
        if candidate.exists() { return Ok(candidate); }
        bail!("no entry file: {} not found", candidate.display());
    }
    Ok(input.to_path_buf())
}

fn ensure_deal_file(path: &Path) -> Result<()> {
    if path.extension().and_then(|s| s.to_str()) != Some("deal") {
        bail!("expected a .deal file: {}", path.display());
    }
    Ok(())
}
