//! The PathsN automaton used for representing the paths of the `TargetNfa`.

use crate::{
    automaton::{
        Letter, NumberTransTo, OutputNumber, State, TargetNfa, TransOn, TransTo, Transitions,
    },
    util,
};
use std::{
    collections::{BTreeSet, HashMap, HashSet},
    hash::Hash,
};

/// A symbol which is consumed by a single dimension of the PathsN automaton.
#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug, Ord, PartialOrd)]
pub enum PathSymbol {
    State(State),
    Letter(Letter),
    OutNum(OutputNumber),
    Bottom,
}

/// An n-dimensional tuple of `PathSymbol`s, which is consumed by the PathsN automaton.
#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct PathTuple(pub Vec<PathSymbol>);

impl From<Vec<PathSymbol>> for PathTuple {
    fn from(v: Vec<PathSymbol>) -> Self {
        PathTuple(v)
    }
}

impl PathTuple {
    /// Get the output of this `PathTuple`.
    pub fn output(&self) -> Vec<usize> {
        let PathTuple(inner) = &self;

        let mut output = Vec::new();

        for l in inner {
            let PathSymbol::OutNum(OutputNumber(x)) = l else {
                output.push(0);
                continue;
            };

            output.push(*x);
        }

        output
    }
}

/// A state of a single dimension of the PathsN automaton.
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Clone, Debug)]
pub enum PathsAState {
    ExpectState(State), // we expect to read the name of the state.
    ExpectOutputNumberWithState(OutputNumber, State), // we expect to read the output number.
    State(State), // we are in this state for real, we can read the actual letter and proceed non-deterministically.
    Trap,         // we ended this path component. We can only get to this from `State`.
}

impl PathsAState {
    /// Check whether this state is accepting.
    pub fn accepting(&self) -> bool {
        matches!(self, PathsAState::State(_) | PathsAState::Trap)
    }
}

/// The PathsN automaton.
pub struct NfaPathsN<'a> {
    pub init: Vec<BTreeSet<PathsAState>>,
    nfa_trans: &'a Transitions,
}

impl<'a> NfaPathsN<'a> {
    /// Create a new `NfaPathsN`, which consumes n-tuples of paths of the given automaton.
    pub fn new(nfa: &'a TargetNfa, n: usize) -> NfaPathsN<'a> {
        let trans = &nfa.trans;
        let states = nfa.states();

        let init_paths_a: BTreeSet<_> = states
            .iter()
            .copied()
            .map(PathsAState::ExpectState)
            .collect();

        let mut init = Vec::new();
        for _ in 0..n {
            init.push(init_paths_a.clone());
        }

        NfaPathsN {
            init,
            nfa_trans: trans,
        }
    }

    /// Get the next state for the given `state` and `letter`.
    pub fn trans(
        &self,
        state: &[BTreeSet<PathsAState>],
        letter: &PathTuple,
    ) -> Vec<BTreeSet<PathsAState>> {
        let mut to = Vec::new();

        for (i, state) in state.iter().enumerate() {
            let l = &letter.0[i];
            let mut next: BTreeSet<PathsAState> = BTreeSet::new();

            for s in state {
                let x: BTreeSet<PathsAState> = match &self.nfa_trans {
                    Transitions::None(t) => paths_n_none_trans(t, s, l),
                    Transitions::Number(t) => paths_n_number_trans(t, s, l),
                };
                next.extend(x.into_iter());
            }
            to.push(next);
        }

        to
    }
}

fn paths_n_none_trans(
    transitions: &HashMap<TransOn, HashSet<TransTo>>,
    state: &PathsAState,
    letter: &PathSymbol,
) -> BTreeSet<PathsAState> {
    match state {
        &PathsAState::ExpectState(x) => match letter {
            &PathSymbol::State(y) if x == y => BTreeSet::from([PathsAState::State(x)]),
            _ => BTreeSet::new(),
        },

        &PathsAState::State(x) => match letter {
            &PathSymbol::Letter(y) => {
                let trans_on = TransOn {
                    state: x,
                    letter: y,
                };

                if let Some(next) = transitions.get(&trans_on) {
                    next.iter()
                        .map(|x| PathsAState::ExpectState(x.state))
                        .collect()
                } else {
                    BTreeSet::new()
                }
            }
            PathSymbol::Bottom => BTreeSet::from([PathsAState::Trap]),
            _ => BTreeSet::new(),
        },
        PathsAState::Trap => match letter {
            PathSymbol::Bottom => BTreeSet::from([PathsAState::Trap]),
            _ => BTreeSet::new(),
        },
        _ => BTreeSet::new(),
    }
}

fn paths_n_number_trans(
    transitions: &HashMap<TransOn, HashSet<NumberTransTo>>,
    state: &PathsAState,
    letter: &PathSymbol,
) -> BTreeSet<PathsAState> {
    match state {
        PathsAState::ExpectState(x) => match letter {
            PathSymbol::State(y) if x == y => BTreeSet::from([PathsAState::State(*x)]),
            _ => BTreeSet::new(),
        },

        PathsAState::State(x) => match letter {
            PathSymbol::Letter(y) => {
                let trans_on = TransOn {
                    state: *x,
                    letter: *y,
                };

                if let Some(next) = transitions.get(&trans_on) {
                    let next: BTreeSet<_> = next
                        .iter()
                        .map(|x| PathsAState::ExpectOutputNumberWithState(x.output, x.state))
                        .collect();

                    next
                } else {
                    BTreeSet::new()
                }
            }
            PathSymbol::Bottom => BTreeSet::from([PathsAState::Trap]),
            _ => BTreeSet::new(),
        },
        PathsAState::ExpectOutputNumberWithState(output, state) => match letter {
            PathSymbol::OutNum(x) if output == x => {
                BTreeSet::from([PathsAState::ExpectState(*state)])
            }
            _ => BTreeSet::new(),
        },
        PathsAState::Trap => match letter {
            PathSymbol::Bottom => BTreeSet::from([PathsAState::Trap]),
            _ => BTreeSet::new(),
        },
    }
}

/// Create the alphabet of the PathsN NFA.
pub fn paths_n_alphabet(nfa: &TargetNfa, n: usize) -> Vec<PathTuple> {
    let letters = nfa.trans.get_letters().into_iter().map(PathSymbol::Letter);
    let states = nfa
        .state_to_id
        .ids()
        .into_iter()
        .map(|s| PathSymbol::State(State(s)));
    let bottom = [PathSymbol::Bottom];

    fn collect_outputs<T, F>(trans: &HashMap<TransOn, HashSet<T>>, f: F) -> Vec<PathSymbol>
    where
        F: Fn(&T) -> PathSymbol,
    {
        let mut out = Vec::new();
        for tos in trans.values() {
            for to in tos {
                out.push(f(to));
            }
        }
        out
    }

    let outputs = match &nfa.trans {
        Transitions::None(_) => Vec::new(),
        Transitions::Number(trans) => collect_outputs(trans, |to| PathSymbol::OutNum(to.output)),
    };

    // Collect into set to remove duplicates.
    let paths_a_alphabet: BTreeSet<_> = letters
        .into_iter()
        .chain(states)
        .chain(bottom)
        .chain(outputs)
        .collect();

    let meaningful_letters = |PathTuple(x): &PathTuple| {
        x.iter()
            .all(|&x| matches!(x, PathSymbol::Bottom | PathSymbol::State(_)))
            || x.iter()
                .all(|&x| matches!(x, PathSymbol::Bottom | PathSymbol::Letter(_)))
            || x.iter()
                .all(|&x| matches!(x, PathSymbol::Bottom | PathSymbol::OutNum(_)))
    };

    util::cartesian_power(&paths_a_alphabet.into_iter().collect(), n)
        .into_iter()
        .map(|x| PathTuple(x.into_iter().copied().collect()))
        .filter(meaningful_letters)
        .collect()
}
