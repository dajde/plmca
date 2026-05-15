//! Parsing for finite automata.

use crate::util::{self, parse::RawToken};
use std::collections::{BTreeSet, HashMap, HashSet};

/// A raw transition "from" state and letter as read from the input.
#[derive(Eq, Hash, PartialEq, Debug)]
pub struct RawTransOn {
    pub state: String,
    pub letter: String,
}

/// A raw transition "to" state and optional output as read from the input.
#[derive(Eq, Hash, PartialEq, Debug)]
pub struct RawTransTo {
    pub output: String,
    pub state: String,
}

pub struct RawAutomaton {
    pub init: BTreeSet<String>,
    pub fin: BTreeSet<String>,
    pub trans: HashMap<RawTransOn, HashSet<RawTransTo>>,
}

/// Parse the input string consisting of transitions each on a separate line into a FA.
pub fn parse_automaton(input: &str) -> Result<RawAutomaton, String> {
    let lines = input.lines();

    let mut init: BTreeSet<String> = BTreeSet::new();
    let mut fin: BTreeSet<String> = BTreeSet::new();
    let mut trans: HashMap<RawTransOn, HashSet<RawTransTo>> = HashMap::new();

    for (index, line) in lines.enumerate() {
        if line.is_empty() {
            continue;
        }

        let transition = match parse_line(line) {
            Ok(x) => x,
            Err(x) => return Err(format!("{x} on line: {}", index + 1)),
        };

        check_state_nfa(&transition.0.state, &mut init, &mut fin);
        check_state_nfa(&transition.1.state, &mut init, &mut fin);

        let on = RawTransOn {
            state: transition.0.state,
            letter: transition.0.letter,
        };
        let to = RawTransTo {
            output: transition.1.output,
            state: transition.1.state,
        };

        trans.entry(on).or_default().insert(to);
    }

    Ok(RawAutomaton { init, fin, trans })
}

fn check_state_nfa(state: &str, init: &mut BTreeSet<String>, fin: &mut BTreeSet<String>) {
    if state.starts_with("_") {
        init.insert(state.to_owned());
    }

    if state.ends_with("*") {
        fin.insert(state.to_owned());
    }
}

fn parse_line(line: &str) -> Result<(RawTransOn, RawTransTo), String> {
    let mut tokens = util::parse::tokens(line)?.into_iter().peekable();

    let line_no_output: Vec<(RawToken, &str)> = vec![
        (RawToken::Name(String::new()), "from state identifier"),
        (RawToken::Arrow, "arrow `->`"),
        (RawToken::Name(String::new()), "to state identifier"),
        (RawToken::Colon, "colon `:`"),
        (RawToken::Name(String::new()), "transition letter"),
    ];

    let line_output: Vec<(RawToken, &str)> = vec![
        (RawToken::Name(String::new()), "from state identifier"),
        (RawToken::Arrow, "arrow `->`"),
        (RawToken::Name(String::new()), "to state identifier"),
        (RawToken::Colon, "colon `:`"),
        (RawToken::Name(String::new()), "transition letter"),
        (RawToken::Comma, "comma `,`"),
        (RawToken::Name(String::new()), "output word"),
    ];

    let formats = vec![&line_no_output[..], &line_output[..]];
    let idents = util::parse::parse_line(&mut tokens, &formats)?;

    match idents.as_slice() {
        [from, to, letter] => Ok((
            RawTransOn {
                state: from.to_string(),
                letter: letter.to_string(),
            },
            RawTransTo {
                state: to.to_string(),
                output: String::new(),
            },
        )),
        [from, to, letter, output] => Ok((
            RawTransOn {
                state: from.to_string(),
                letter: letter.to_string(),
            },
            RawTransTo {
                state: to.to_string(),
                output: output.to_string(),
            },
        )),
        _ => Err("invalid line encountered".to_owned()),
    }
}
