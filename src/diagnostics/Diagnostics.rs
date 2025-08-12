#[derive(Debug, Clone)]
pub struct Diagnostic {
    pub message: String,
    pub offset: usize,
    pub len: usize,
    pub path: Vec<String>, // e.g., ["Dealer Blue", "fn main", "variable x"]
}

pub fn line_starts(src: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, ch) in src.char_indices() {
        if ch == '\n' { starts.push(i + 1); }
    }
    starts
}

pub fn offset_to_line_col(starts: &[usize], offset: usize) -> (usize, usize) {
    // binary search for greatest start <= offset
    let mut lo = 0; let mut hi = starts.len();
    while lo + 1 < hi {
        let mid = (lo + hi) / 2;
        if starts[mid] <= offset { lo = mid; } else { hi = mid; }
    }
    let line = lo; // 0-based
    let col = offset.saturating_sub(starts[lo]);
    (line + 1, col + 1) // 1-based for humans
}

pub fn print_diagnostics(src_name: &str, src: &str, diags: &[Diagnostic]) {
    let starts = line_starts(src);
    for d in diags {
        let (line, col) = offset_to_line_col(&starts, d.offset);
        let _preview = src.get(d.offset..d.offset + d.len).unwrap_or("");
        let scope = if d.path.is_empty() { String::new() } else { d.path.join(" > ") };
        if scope.is_empty() {
            eprintln!("{}:{}:{}: error: {}", src_name, line, col, d.message);
        } else {
            eprintln!("{}:{}:{}: error: {} — {}", src_name, line, col, d.message, scope);
        }
        // Optionally print the line and caret
        if let Some(line_start) = starts.get(line - 1).copied() {
            let line_end = src[line_start..].find('\n').map(|i| line_start + i).unwrap_or(src.len());
            let line_text = &src[line_start..line_end];
            eprintln!("  {} | {}", line, line_text);
            let caret_pos = col;
            let mut caret_line = String::new();
            caret_line.push_str("      ");
            for _ in 1..caret_pos { caret_line.push(' '); }
            caret_line.push('^');
            eprintln!("{}", caret_line);
        }
    }
}


