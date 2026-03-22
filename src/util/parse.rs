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
}

impl TokenName for RawToken {
    fn name(&self) -> Option<String> {
        match self {
            Self::Name(name) => Some(name.clone()),
            _ => None,
        }
    }
}

fn consume_and_check(
    it: &mut Peekable<impl Iterator<Item = char>>,
    arr: Vec<(char, RawToken)>,
) -> Option<RawToken> {
    let t: String = it.by_ref().take(2).collect();
    assert!(t.len() == 2);
    for (c, tok) in arr {
        if t.ends_with(c) {
            return Some(tok);
        }
    }

    None
}

fn consume(it: &mut Peekable<impl Iterator<Item = char>>, tok: RawToken) -> Option<RawToken> {
    it.next();
    Some(tok)
}

fn consume_name(it: &mut Peekable<impl Iterator<Item = char>>) -> Option<RawToken> {
    let mut t = String::new();
    while let Some(&c) = it.peek() {
        if !(c.is_alphanumeric() || c == '_' || c == '*') {
            break;
        }
        t.push(it.next().unwrap());

        match t.as_str() {
            "exists" => return Some(RawToken::Exists),
            "init" => return Some(RawToken::Init),
            "final" => return Some(RawToken::Final),
            "reach_init" => return Some(RawToken::ReachInit),
            "reach_final" => return Some(RawToken::ReachFinal),
            _ => continue,
        }
    }

    if t.is_empty() {
        return None;
    }

    Some(RawToken::Name(t))
}

/// Get the lexed tokens from the given character iterator.
pub fn tokens(mut it: Peekable<impl Iterator<Item = char>>) -> Result<Vec<RawToken>, String> {
    let mut toks = Vec::new();

    while let Some(c) = it.peek() {
        let opt_t = match c {
            '/' => consume_and_check(&mut it, vec![('\\', RawToken::And)]),
            '\\' => consume_and_check(&mut it, vec![('/', RawToken::Or)]),
            ':' => consume(&mut it, RawToken::Colon),
            ',' => consume(&mut it, RawToken::Comma),
            '(' => consume(&mut it, RawToken::LParen),
            ')' => consume(&mut it, RawToken::RParen),
            '!' => consume(&mut it, RawToken::Neg),
            '=' => consume(&mut it, RawToken::Eq),
            '<' => consume_and_check(&mut it, vec![('=', RawToken::LessEq)]),
            '#' => consume_and_check(&mut it, vec![('>', RawToken::Prefix)]),
            '$' => consume_and_check(&mut it, vec![('>', RawToken::LangBelong)]),
            '-' => consume_and_check(
                &mut it,
                vec![('-', RawToken::DoubleMinus), ('>', RawToken::Arrow)],
            ),
            _ => consume_name(&mut it),
        };

        if let Some(t) = opt_t {
            toks.push(t);
        } else {
            return Err("unknown token".to_owned());
        }
    }

    Ok(toks)
}
