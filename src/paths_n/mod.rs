//! The PathsN automaton used for representing the paths of the `TargetNfa`.

use crate::{
    automaton::{
        Letter, NumberTransTo, OutputNumber, OutputWordRef, State, TargetNfa, TransOn, TransTo,
        Transitions, WordTransTo,
    },
    util,
};
use std::{
    collections::{BTreeSet, HashMap, HashSet},
    hash::Hash,
};

/// A symbol which is consumed by a single dimension of the PathsN automaton.
#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug, Ord, PartialOrd)]
pub enum PathSymbol<'a> {
    State(State),
    Letter(Letter),
    OutWord(OutputWordRef<'a>),
    OutNum(OutputNumber),
    Bottom,
}

/// An n-dimensional tuple of `PathSymbol`s, which is consumed by the PathsN automaton.
#[derive(Eq, PartialEq, Hash, Clone, Debug)]
pub struct PathTuple<'a>(pub Vec<PathSymbol<'a>>);

impl<'a> From<Vec<PathSymbol<'a>>> for PathTuple<'a> {
    fn from(v: Vec<PathSymbol<'a>>) -> Self {
        PathTuple(v)
    }
}

impl PathTuple<'_> {
    /// Get the output of this `PathTuple`.
    pub fn output(&self) -> Vec<i32> {
        let PathTuple(inner) = &self;

        let mut output = Vec::new();

        for l in inner {
            let &PathSymbol::OutNum(OutputNumber(x)) = l else {
                output.push(0);
                continue;
            };

            output.push(x);
        }

        output
    }
}

/// A state of a single dimension of the PathsN automaton.
#[derive(Eq, PartialEq, Hash, Ord, PartialOrd, Clone, Debug)]
pub enum PathsAState<'a> {
    ExpectState(State), // we expect to read the name of the state.
    ExpectOutputNumberWithState(OutputNumber, State), // we expect to read the output number and a state after.
    ExpectOutputWordWithState(OutputWordRef<'a>, State), // we expect to read the output word and a state after.
    State(State), // we are in this state for real, we can read the actual letter and proceed non-deterministically.
    Trap,         // we ended this path component. We can only get to this from `State`.
}

impl PathsAState<'_> {
    /// Check whether this state is accepting.
    pub fn accepting(&self) -> bool {
        matches!(self, PathsAState::State(_) | PathsAState::Trap)
    }
}

/// `NfaPathsNState` is a state representation of the `NfaPathsN`.
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct NfaPathsNState<'a>(Vec<BTreeSet<PathsAState<'a>>>);

impl NfaPathsNState<'_> {
    pub fn is_final(&self) -> bool {
        self.0
            .iter()
            .all(|set| set.iter().any(|state| state.accepting()))
    }

    pub fn is_dead(&self) -> bool {
        self.0.iter().any(|x| x.is_empty())
    }
}

/// The PathsN automaton.
pub struct NfaPathsN<'a> {
    pub init: NfaPathsNState<'a>,
    nfa_trans: &'a Transitions,
}

#[derive(Clone, Copy)]
pub enum StartStateProp {
    Init,
    NotInit,
    Final,
    NotFinal,
    ReachInit,
    NotReachInit,
    ReachFinal,
    NotReachFinal,
    EqualTo(State),
}

impl<'a> NfaPathsN<'a> {
    /// Create a new `NfaPathsN`, which consumes n-tuples of paths of the given automaton.
    ///
    /// `restrictions` encodes the initial state constraint for a single path, for example
    /// in `exists pi: p -- u -> q`, where `p` is in a `init` or `final` predicate.
    pub fn new(
        nfa: &'_ TargetNfa,
        n: usize,
        restrictions: Vec<Vec<StartStateProp>>,
    ) -> NfaPathsN<'_> {
        assert!(restrictions.len() == n);

        let trans = &nfa.trans;
        let states = nfa.states();
        let reach_init = nfa.reach_init();
        let reach_final = nfa.reach_final();
        let mut init = Vec::new();

        use StartStateProp::*;
        for restriction in restrictions.iter().take(n) {
            type FilterFn<'b> = Box<dyn Fn(&State) -> bool + 'b>;
            let mut filters: Vec<FilterFn> = Vec::new();

            for property in restriction {
                let filter: FilterFn = match property {
                    Init => Box::new(|x| nfa.init.contains(x)),
                    NotInit => Box::new(|x| !nfa.init.contains(x)),
                    Final => Box::new(|x| nfa.fin.contains(x)),
                    NotFinal => Box::new(|x| !nfa.fin.contains(x)),
                    ReachInit => Box::new(|x| reach_init.contains(x)),
                    NotReachInit => Box::new(|x| !reach_init.contains(x)),
                    ReachFinal => Box::new(|x| reach_final.contains(x)),
                    NotReachFinal => Box::new(|x| !reach_final.contains(x)),
                    EqualTo(state) => Box::new(move |x| x == state),
                };

                filters.push(filter);
            }

            let init_dim: BTreeSet<_> = states
                .iter()
                .copied()
                .filter(|x| filters.iter().all(|f| f(x)))
                .map(PathsAState::ExpectState)
                .collect();

            init.push(init_dim.clone());
        }

        NfaPathsN {
            init: NfaPathsNState(init),
            nfa_trans: trans,
        }
    }

    /// Get the next state for the given `state` and `letter`.
    pub fn trans(
        &'_ self,
        NfaPathsNState(state): &NfaPathsNState,
        letter: &PathTuple,
    ) -> NfaPathsNState<'_> {
        let mut to = Vec::new();

        for (i, state) in state.iter().enumerate() {
            let l = &letter.0[i];
            let mut next: BTreeSet<PathsAState> = BTreeSet::new();

            for s in state {
                let x: BTreeSet<PathsAState> = match &self.nfa_trans {
                    Transitions::None(t) => paths_n_none_trans(t, s, l),
                    Transitions::Number(t) => paths_n_number_trans(t, s, l),
                    Transitions::Word(t) => paths_n_word_trans(t, s, l),
                };
                next.extend(x.into_iter());
            }
            to.push(next);
        }

        NfaPathsNState(to)
    }
}

fn paths_n_none_trans<'a>(
    transitions: &HashMap<TransOn, HashSet<TransTo>>,
    state: &PathsAState,
    letter: &PathSymbol,
) -> BTreeSet<PathsAState<'a>> {
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

fn paths_n_number_trans<'a>(
    transitions: &HashMap<TransOn, HashSet<NumberTransTo>>,
    state: &PathsAState,
    letter: &PathSymbol,
) -> BTreeSet<PathsAState<'a>> {
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
        _ => BTreeSet::new(),
    }
}

fn paths_n_word_trans<'a>(
    transitions: &'a HashMap<TransOn, HashSet<WordTransTo>>,
    state: &PathsAState,
    letter: &PathSymbol,
) -> BTreeSet<PathsAState<'a>> {
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
                        .map(|x| PathsAState::ExpectOutputWordWithState(&x.output, x.state))
                        .collect();

                    next
                } else {
                    BTreeSet::new()
                }
            }
            PathSymbol::Bottom => BTreeSet::from([PathsAState::Trap]),
            _ => BTreeSet::new(),
        },
        PathsAState::ExpectOutputWordWithState(output, state) => match letter {
            PathSymbol::OutWord(x) if output == x => {
                BTreeSet::from([PathsAState::ExpectState(*state)])
            }
            _ => BTreeSet::new(),
        },
        PathsAState::Trap => match letter {
            PathSymbol::Bottom => BTreeSet::from([PathsAState::Trap]),
            _ => BTreeSet::new(),
        },
        _ => BTreeSet::new(),
    }
}

/// Create the alphabet of the PathsN NFA.
pub fn paths_n_alphabet(nfa: &'_ TargetNfa, n: usize) -> Vec<PathTuple<'_>> {
    let letters = nfa.trans.get_letters().into_iter().map(PathSymbol::Letter);
    let states = nfa
        .state_to_id
        .ids()
        .into_iter()
        .map(|s| PathSymbol::State(State(s)));
    let bottom = [PathSymbol::Bottom];

    fn collect_outputs<T, F>(trans: &'_ HashMap<TransOn, HashSet<T>>, f: F) -> Vec<PathSymbol<'_>>
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
        Transitions::Word(trans) => collect_outputs(trans, |to| PathSymbol::OutWord(&to.output)),
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
            || x.iter()
                .all(|&x| matches!(x, PathSymbol::Bottom | PathSymbol::OutWord(_)))
    };

    util::cartesian_power(&paths_a_alphabet, n)
        .into_iter()
        .map(|x| PathTuple(x.into_iter().copied().collect()))
        .filter(meaningful_letters)
        .collect()
}
