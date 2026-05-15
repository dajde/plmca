//! Shared logic for parsing PL formulas and automata.

use std::fmt::Debug;
use std::iter::Peekable;

/// Get an optional name in the token.
pub trait TokenName {
    fn name(&self) -> Option<String>;
}

/// Parse a sequence of `tokens` according to one of the expected `patterns`.
/// Returns a list of identifiers parsed along the way.
pub fn parse_line<T: TokenName + Eq + Debug>(
    tokens: &mut Peekable<impl Iterator<Item = T>>,
    patterns: &[&[(T, &str)]],
) -> Result<Vec<String>, String> {
    let Some(longest) = patterns.iter().max_by_key(|line| line.len()) else {
        return Err("no expected pattern provided".to_owned());
    };
    let max_len = longest.len();
    let mut possible_patterns = vec![true; patterns.len()];
    let mut identifiers = Vec::new();

    for i in 0..max_len {
        let Some(token) = tokens.next() else {
            return Err("unexpected end of input".to_owned());
        };

        if let Some(name) = token.name() {
            identifiers.push(name);
        }

        for (expected_pattern_id, expected_pattern) in patterns.iter().enumerate() {
            if !possible_patterns[expected_pattern_id] {
                continue;
            }

            let (expected_token, message) = expected_pattern.get(i).unwrap();

            if std::mem::discriminant(&token) != std::mem::discriminant(expected_token) {
                possible_patterns[expected_pattern_id] = false;

                if possible_patterns.iter().all(|x| !x) {
                    return Err(format!("expected {message}, got {token:?}"));
                }
            }
        }

        for (candidate_pattern_id, candidate_pattern) in patterns.iter().enumerate() {
            if !possible_patterns[candidate_pattern_id] {
                continue;
            }

            if candidate_pattern.get(i + 1).is_none() {
                let Some(next_token) = tokens.peek() else {
                    return Ok(identifiers);
                };

                let mut exists_other_candidate = false;
                for (pattern_id, pattern) in patterns.iter().enumerate() {
                    if !possible_patterns[pattern_id] || pattern_id == candidate_pattern_id {
                        continue;
                    }
                    let Some((t, _)) = pattern.get(i + 1) else {
                        continue;
                    };
                    if std::mem::discriminant(next_token) != std::mem::discriminant(t) {
                        continue;
                    }
                    exists_other_candidate = true;
                }

                if !exists_other_candidate {
                    return Ok(identifiers);
                }
                possible_patterns[candidate_pattern_id] = false;
            }
        }
    }

    Ok(identifiers)
}

/// Lexical analysis token without any processing.
#[derive(Debug, Eq, PartialEq)]
pub enum RawToken {
    Forall,       // "forall"
    Exists,       // "exists"
    Name(String), // any alphanumeric string
    Colon,        // ":"
    Comma,        // ","
    And,          // "/\"
    Or,           // "\/"
    Neg,          // "!"
    Eq,           // "="
    Prefix,       // "#>"
    LangBelong,   // "$>"
    LessEq,       // "<="
    Final,        // "final"
    Init,         // "init"
    ReachFinal,   // "reach_final"
    ReachInit,    // "reach_init"
    LParen,       // "("
    RParen,       // ")"
    DoubleMinus,  // "--"
    Arrow,        // "->"
    Plus,         // "+"
    Dot,          // "."
}

impl TokenName for RawToken {
    fn name(&self) -> Option<String> {
        match self {
            Self::Name(name) => Some(name.clone()),
            _ => None,
        }
    }
}

fn consume_name(bytes: &[u8], i: &mut usize) -> Option<RawToken> {
    let mut t = String::new();

    while *i < bytes.len() {
        let c = bytes[*i];

        if !c.is_ascii() {
            return None;
        }

        if !(c.is_ascii_alphanumeric() || c == b'_' || c == b'*' || c == b'|' || c == b'-') {
            break;
        }

        t.push(c as char);
        *i += 1;
    }

    if t.is_empty() {
        return None;
    }

    match t.as_str() {
        "forall" => Some(RawToken::Forall),
        "exists" => Some(RawToken::Exists),
        "init" => Some(RawToken::Init),
        "final" => Some(RawToken::Final),
        "reach_init" => Some(RawToken::ReachInit),
        "reach_final" => Some(RawToken::ReachFinal),
        _ => Some(RawToken::Name(t)),
    }
}

/// Get the lexed tokens from the given character iterator.
pub fn tokens(stream: &str) -> Result<Vec<RawToken>, String> {
    let bytes = stream.as_bytes();
    let mut toks = Vec::new();
    let mut i = 0;

    while i < bytes.len() {
        let c = bytes[i];

        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }

        if i + 2 <= bytes.len() {
            let tok = match &bytes[i..i + 2] {
                b"/\\" => Some(RawToken::And),
                b"\\/" => Some(RawToken::Or),
                b"->" => Some(RawToken::Arrow),
                b"--" => Some(RawToken::DoubleMinus),
                b"$>" => Some(RawToken::LangBelong),
                b"#>" => Some(RawToken::Prefix),
                b"<=" => Some(RawToken::LessEq),
                _ => None,
            };

            if let Some(t) = tok {
                i += 2;
                toks.push(t);
                continue;
            }
        }

        let tok = match &bytes[i] {
            b':' => Some(RawToken::Colon),
            b',' => Some(RawToken::Comma),
            b'(' => Some(RawToken::LParen),
            b')' => Some(RawToken::RParen),
            b'!' => Some(RawToken::Neg),
            b'=' => Some(RawToken::Eq),
            b'+' => Some(RawToken::Plus),
            b'.' => Some(RawToken::Dot),
            _ => None,
        };

        if let Some(t) = tok {
            i += 1;
            toks.push(t);
            continue;
        }

        let tok = consume_name(bytes, &mut i);

        let Some(t) = tok else {
            return Err("syntax error".to_owned());
        };

        toks.push(t);
    }
    Ok(toks)
}
