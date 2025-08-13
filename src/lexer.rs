use crate::ast::Ident;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // keywords
    Dealer,
    Members,
    Trait,
    Fn,
    Let,
    Mut,
    MemberKw,
    Start,
    Await,
    Send,
    Recv,
    True,
    False,
    Equals,
    If,
    Else,
    Pub,
    For,
    In,
    DoubleDot,
    DoubleDotEq,
    Fold,
    Break,
    // punctuation
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Comma,
    Semicolon,
    Colon,
    Arrow,
    Dot,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    DStar,
    Bang,
    EqEq,
    BangEq,
    Lt,
    Le,
    Gt,
    Ge,
    DoublePipe,
    PipeArrow,
    Bar,
    Amp,
    // literals/idents
    Ident(Ident),
    String(String),
    Number(String),
    // typed list literal starter like int[] u32[] f64[] etc.
    // We will parse as Ident followed by LBracket RBracket in parser; no new token needed.
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub offset: usize,
    pub len: usize,
}

#[derive(Debug, Error)]
pub enum LexError {
    #[error("unexpected character '{ch}' at {pos}")]
    UnexpectedChar { ch: char, pos: usize },
    #[error("unterminated string starting at {pos}")]
    UnterminatedString { pos: usize },
}

pub struct Lexer<'a> {
    src: &'a str,
    iter: std::str::CharIndices<'a>,
    peeked: Option<(usize, char)>,
}

impl<'a> Lexer<'a> {
    pub fn new(src: &'a str) -> Self {
        Self { src, iter: src.char_indices(), peeked: None }
    }

    fn bump(&mut self) -> Option<(usize, char)> {
        if let Some(p) = self.peeked.take() { Some(p) } else { self.iter.next() }
    }

    fn peek(&mut self) -> Option<(usize, char)> {
        if self.peeked.is_none() {
            self.peeked = self.iter.next();
        }
        self.peeked
    }

    fn eat_while<F: Fn(char) -> bool>(&mut self, start: usize, pred: F) -> (usize, usize) {
        let mut end = start;
        while let Some((i, c)) = self.peek() {
            if pred(c) {
                end = i;
                self.bump();
            } else {
                break;
            }
        }
        (start, end + 1)
    }

    fn skip_ws_and_comments(&mut self, mut i: usize) -> usize {
        loop {
            // consume whitespace
            let mut progressed = false;
            while let Some((j, c)) = self.peek() {
                if c.is_whitespace() { self.bump(); i = j + 1; progressed = true; } else { break; }
            }
            // consume // line comments
            if let Some((j, '/')) = self.peek() {
                // peek next char from source without disturbing iterator state
                if let Some(next_ch) = self.src.get(j..).and_then(|s| s.chars().nth(1)) {
                    if next_ch == '/' {
                        // consume two slashes
                        self.bump();
                        self.bump();
                        // consume until newline or EOF
                        while let Some((k, ch)) = self.peek() {
                            if ch == '\n' { self.bump(); i = k + 1; break; }
                            self.bump();
                        }
                        progressed = true;
                        continue;
                    }
                }
            }
            if !progressed { break; }
        }
        i
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, LexError>;

    fn next(&mut self) -> Option<Self::Item> {
        // Skip whitespace and comments; do not consume a character prematurely
        let _ = self.skip_ws_and_comments(0);
        let (start, c) = match self.peek() {
            Some((j, c2)) => (j, c2),
            None => return None,
        };
        // Now consume the current character
        self.bump();

        // punctuation and tokens
        match c {
            '{' => return Some(Ok(Token { kind: TokenKind::LBrace, offset: start, len: 1 })),
            '}' => return Some(Ok(Token { kind: TokenKind::RBrace, offset: start, len: 1 })),
            '(' => return Some(Ok(Token { kind: TokenKind::LParen, offset: start, len: 1 })),
            ')' => return Some(Ok(Token { kind: TokenKind::RParen, offset: start, len: 1 })),
            '[' => return Some(Ok(Token { kind: TokenKind::LBracket, offset: start, len: 1 })),
            ']' => return Some(Ok(Token { kind: TokenKind::RBracket, offset: start, len: 1 })),
            ',' => return Some(Ok(Token { kind: TokenKind::Comma, offset: start, len: 1 })),
            ';' => return Some(Ok(Token { kind: TokenKind::Semicolon, offset: start, len: 1 })),
            ':' => return Some(Ok(Token { kind: TokenKind::Colon, offset: start, len: 1 })),
            '.' => {
                // Check for ".." and "..=" ranges
                if let Some((_, '.')) = self.peek() {
                    self.bump(); // consume the second dot
                    if let Some((_, '=')) = self.peek() {
                        self.bump(); // consume '='
                        return Some(Ok(Token { kind: TokenKind::DoubleDotEq, offset: start, len: 3 }));
                    }
                    return Some(Ok(Token { kind: TokenKind::DoubleDot, offset: start, len: 2 }));
                }
                return Some(Ok(Token { kind: TokenKind::Dot, offset: start, len: 1 }));
            }
            '-' => {
                if let Some((_, '>')) = self.peek() {
                    self.bump();
                    return Some(Ok(Token { kind: TokenKind::Arrow, offset: start, len: 2 }));
                }
                return Some(Ok(Token { kind: TokenKind::Minus, offset: start, len: 1 }));
            }
            '|' => {
                if let Some((_, '>')) = self.peek() { self.bump();
                    return Some(Ok(Token {kind: TokenKind::PipeArrow,offset: start, len: 2 }));
                } else if let Some((_,'|')) = self.peek() { self.bump();

                    return Some(Ok(Token { kind: TokenKind::DoublePipe, offset: start, len: 2 }));} else {
                return Some(Ok(Token {kind: TokenKind::Bar, offset: start, len: 1})); // this should
                                                                                    // dealt with 
                    }}
            '!' => {
                if let Some((_, '=')) = self.peek() { self.bump(); return Some(Ok(Token { kind: TokenKind::BangEq, offset: start, len: 2 })); }
                return Some(Ok(Token { kind: TokenKind::Bang, offset: start, len: 1 }));
            }
            '=' => {
                if let Some((_, '=')) = self.peek() { self.bump(); return Some(Ok(Token { kind: TokenKind::EqEq, offset: start, len: 2 })); }
                return Some(Ok(Token { kind: TokenKind::Equals, offset: start, len: 1 }));
            }
            '<' => {
                if let Some((_, '=')) = self.peek() { self.bump(); return Some(Ok(Token { kind: TokenKind::Le, offset: start, len: 2 })); }
                return Some(Ok(Token { kind: TokenKind::Lt, offset: start, len: 1 }));
            }
            '>' => {
                if let Some((_, '=')) = self.peek() { self.bump(); return Some(Ok(Token { kind: TokenKind::Ge, offset: start, len: 2 })); }
                return Some(Ok(Token { kind: TokenKind::Gt, offset: start, len: 1 }));
            }
            '+' => { return Some(Ok(Token { kind: TokenKind::Plus, offset: start, len: 1 })); }
            '*' => {
                if let Some((_, '*')) = self.peek() {
                    self.bump();
                    return Some(Ok(Token { kind: TokenKind::DStar, offset: start, len: 2 }));
                }
                return Some(Ok(Token { kind: TokenKind::Star, offset: start, len: 1 }));
            }
            '/' => { return Some(Ok(Token { kind: TokenKind::Slash, offset: start, len: 1 })); }
            '%' => { return Some(Ok(Token { kind: TokenKind::Percent, offset: start, len: 1 })); }
            '"' => {
                let mut s = String::new();
                while let Some((_, ch)) = self.bump() {
                    match ch {
                        '"' => {
                            let slen = s.len();
                            return Some(Ok(Token { kind: TokenKind::String(s), offset: start, len: slen + 2 }));
                        }
                        '\\' => {
                            if let Some((_, esc)) = self.bump() { s.push(esc); } else { return Some(Err(LexError::UnterminatedString { pos: start })); }
                        }
                        c => s.push(c),
                    }
                }
                return Some(Err(LexError::UnterminatedString { pos: start }));
            }
            c if c.is_ascii_digit() => {
                // Parse a sequence of digits as a number token. Do not consume '.' here
                // so that ranges like 1..5 are lexed correctly.
                let (s, e) = self.eat_while(start, |ch| ch.is_ascii_digit());
                let text = &self.src[s..e];
                return Some(Ok(Token { kind: TokenKind::Number(text.to_string()), offset: s, len: e - s }));
            }
            c if is_ident_start(c) => {
                let (s, e) = self.eat_while(start, |ch| is_ident_continue(ch));
                let text = &self.src[s..e];
                let kind = match text {
                    "in" => TokenKind::In,
                    "dealer" => TokenKind::Dealer,
                    "members" => TokenKind::Members,
                    "trait" => TokenKind::Trait,
                    "member" => TokenKind::MemberKw,
                    "fn" => TokenKind::Fn,
                    "let" => TokenKind::Let,
                    "mut" => TokenKind::Mut,
                    "start" => TokenKind::Start,
                    "for" => TokenKind::For,
                    "fold" => TokenKind::Fold,
                    "break" => TokenKind::Break,
                    "await" => TokenKind::Await,
                    "send" => TokenKind::Send,
                    "recv" => TokenKind::Recv,
                    "true" => TokenKind::True,
                    "false" => TokenKind::False,
                    "if" => TokenKind::If,
                    "else" => TokenKind::Else,
                    "pub" => TokenKind::Pub,
                    _ => TokenKind::Ident(Ident(text.to_string())),
                };
                return Some(Ok(Token { kind, offset: s, len: e - s }));
            }
            c if c.is_whitespace() => {
                return self.next();
            }
            other => return Some(Err(LexError::UnexpectedChar { ch: other, pos: start })),
        }
    }
}

#[inline]
fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic()
}

#[inline]
fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric()
}


