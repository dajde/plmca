//! Automata definitions and algorithms.

use crate::automaton::parse::{RawTransOn, RawTransTo};
use crate::util::IdMap;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;

mod parse;

/// A state of a finite automaton.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug)]
pub struct State(pub usize);

/// A letter of an alphabet of a finite automaton.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug)]
pub struct Letter(pub usize);

/// An output number of a finite automaton with outputs.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug)]
pub struct OutputNumber(pub usize);

/// A starting state and letter of a transition of a finite automaton.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug)]
pub struct TransOn {
    pub state: State,
    pub letter: Letter,
}

/// An ending state of a transition of a finite automaton.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug)]
pub struct TransTo {
    pub state: State,
}

/// An ending state of a transition of a finite automaton with outputs.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug)]
pub struct NumberTransTo {
    pub state: State,
    pub output: OutputNumber,
}

/// Possible transitions variants.
/// `None` is for classic finite automaton.
/// `Number` is for finite automata with number outputs.
pub enum Transitions {
    None(HashMap<TransOn, HashSet<TransTo>>),
    Number(HashMap<TransOn, HashSet<NumberTransTo>>),
}

impl Transitions {
    /// Get the alphabet over which this `Transitions` is constructed.
    pub fn get_letters(&self) -> Vec<Letter> {
        fn extract<'a>(t: impl Iterator<Item = &'a TransOn>) -> Vec<Letter> {
            t.map(|trans_on| trans_on.letter).collect()
        }

        match &self {
            Transitions::None(t) => extract(t.keys()),
            Transitions::Number(t) => extract(t.keys()),
        }
    }

    fn extract_base_trans<T, F>(
        trans: &HashMap<TransOn, HashSet<T>>,
        extract: F,
    ) -> HashMap<TransOn, HashSet<TransTo>>
    where
        F: Fn(&T) -> TransTo,
    {
        trans
            .iter()
            .map(|(&on, to)| (on, to.iter().map(&extract).collect()))
            .collect()
    }

    /// Returns the transitions in a basic form without the optional outputs.
    pub fn base_trans(&self) -> HashMap<TransOn, HashSet<TransTo>> {
        match &self {
            Transitions::None(trans) => Self::extract_base_trans(trans, |&t_on| t_on),
            Transitions::Number(trans) => {
                Self::extract_base_trans(trans, |t_on| TransTo { state: t_on.state })
            }
        }
    }
}

/// Possible output types for finite automata.
#[derive(Clone, Copy)]
pub enum OutputType {
    None,
    Number,
}

/// Target Non-Deterministic Finite Automaton for Model-Checking.
pub struct TargetNfa {
    pub init: BTreeSet<State>,
    pub fin: BTreeSet<State>,
    pub trans: Transitions,
    pub state_to_id: IdMap<String>,
    pub letter_to_id: IdMap<String>,
    pub output_type: OutputType,
}

fn add_trans_to<T, F>(
    raw_trans_to_set: HashSet<RawTransTo>,
    trans_on: TransOn,
    transition: &mut HashMap<TransOn, HashSet<T>>,
    mut convert: F,
) where
    T: Eq + Hash,
    F: FnMut(RawTransTo) -> T,
{
    let mut trans_to_set = HashSet::new();

    for to in raw_trans_to_set {
        trans_to_set.insert(convert(to));
    }
    transition.insert(trans_on, trans_to_set);
}

impl TargetNfa {
    /// Create a new `TargetNfa` by parsing from a `&str`.
    pub fn parse(value: &str) -> Self {
        let (init, fin, transitions) = parse::parse_automaton(value);

        let output_type = if transitions
            .iter()
            .all(|x| x.1.iter().all(|y| y.output.is_empty()))
        {
            OutputType::None
        } else {
            OutputType::Number
        };

        TargetNfa::new(init, fin, transitions, output_type)
    }

    fn new(
        initial_states: BTreeSet<String>,
        final_states: BTreeSet<String>,
        transitions: HashMap<RawTransOn, HashSet<RawTransTo>>,
        output_type: OutputType,
    ) -> TargetNfa {
        let mut state_to_id = IdMap::new();
        let mut letter_to_id = IdMap::new();

        let mut initial_ids = BTreeSet::new();
        for state in initial_states {
            let init_id = state_to_id.insert(state);
            initial_ids.insert(State(init_id));
        }

        let mut transition = match output_type {
            OutputType::None => Transitions::None(HashMap::new()),
            OutputType::Number => Transitions::Number(HashMap::new()),
        };

        for (raw_trans_on, raw_trans_to_set) in transitions {
            let trans_on = TransOn {
                state: State(state_to_id.insert(raw_trans_on.state)),
                letter: Letter(letter_to_id.insert(raw_trans_on.letter)),
            };

            match transition {
                Transitions::None(ref mut transition) => {
                    let convert = |to: RawTransTo| TransTo {
                        state: State(state_to_id.insert(to.state)),
                    };

                    add_trans_to(raw_trans_to_set, trans_on, transition, convert);
                }
                Transitions::Number(ref mut transition) => {
                    let convert = |to: RawTransTo| NumberTransTo {
                        state: State(state_to_id.insert(to.state)),
                        output: OutputNumber(to.output.parse().unwrap()),
                    };

                    add_trans_to(raw_trans_to_set, trans_on, transition, convert);
                }
            }
        }

        let mut final_ids = BTreeSet::new();
        for state in final_states {
            let final_id = state_to_id.insert(state);
            final_ids.insert(State(final_id));
        }

        Self {
            init: initial_ids,
            fin: final_ids,
            trans: transition,
            state_to_id,
            letter_to_id,
            output_type,
        }
    }

    /// Get the states in this `TargetNfa`.
    pub fn states(&self) -> Vec<State> {
        self.state_to_id.ids().iter().map(|&i| State(i)).collect()
    }

    /// Get the states we can reach from an initial state.
    pub fn reach_init(&self) -> BTreeSet<State> {
        let transitions = self.trans.base_trans();

        let mut queue = Vec::new();
        queue.extend(self.init.iter().copied());

        let mut reachable = BTreeSet::new();

        while let Some(s) = queue.pop() {
            reachable.insert(s);

            for (_, ns) in transitions.iter().filter(|&(t_on, _)| t_on.state == s) {
                for &s in ns {
                    if !reachable.contains(&s.state) {
                        queue.push(s.state);
                    }
                }
            }
        }

        reachable
    }

    /// Get the states from which we can reach a final state.
    pub fn reach_final(&self) -> BTreeSet<State> {
        let transitions = self.trans.base_trans();

        let mut queue = Vec::new();
        queue.extend(self.fin.iter().copied());

        let mut reachable = BTreeSet::new();

        while let Some(s) = queue.pop() {
            reachable.insert(s);

            for (ns, _) in transitions
                .iter()
                .filter(|&(_, t_to)| t_to.contains(&TransTo { state: s }))
            {
                if !reachable.contains(&ns.state) {
                    queue.push(ns.state);
                }
            }
        }

        reachable
    }
}

/// Deterministic Finite Automaton for defining a "language belongs to" predicate.
#[derive(Clone, Debug)]
pub struct LangDfa {
    pub init: State,
    pub fin: BTreeSet<State>,
    pub trans: HashMap<TransOn, State>,
}

impl LangDfa {
    /// Create a new `LangDfa` by parsing from a string.
    ///
    /// We need `target_letter_to_id` so that the letters in
    /// `TargetNfa` match with the letters in `LangDfa`.
    ///
    /// The `input` can also be an NFA.
    pub fn parse(input: &str, target_letter_to_id: &IdMap<String>) -> LangDfa {
        let (init, fin, transitions) = parse::parse_automaton(input);

        LangDfa::new(init, fin, transitions, target_letter_to_id)
    }

    fn new(
        initial_states: BTreeSet<String>,
        final_states: BTreeSet<String>,
        transitions: HashMap<RawTransOn, HashSet<RawTransTo>>,
        target_letter_to_id: &IdMap<String>,
    ) -> LangDfa {
        let mut state_to_id = IdMap::new();
        let mut target_letter_to_id = target_letter_to_id.clone();

        let initial_ids: BTreeSet<State> = initial_states
            .into_iter()
            .map(|x| State(state_to_id.insert(x)))
            .collect();

        let final_ids: BTreeSet<State> = final_states
            .into_iter()
            .map(|x| State(state_to_id.insert(x)))
            .collect();

        let mut trans = HashMap::new();
        for (raw_trans_on, raw_trans_to_set) in transitions {
            let trans_on = TransOn {
                state: State(state_to_id.insert(raw_trans_on.state)),
                letter: Letter(target_letter_to_id.insert(raw_trans_on.letter)),
            };

            let mut trans_to = HashSet::new();
            for t in raw_trans_to_set {
                trans_to.insert(State(state_to_id.insert(t.state)));
            }

            trans.insert(trans_on, trans_to);
        }

        let alphabet: Vec<Letter> = target_letter_to_id
            .ids()
            .iter()
            .map(|&i| Letter(i))
            .collect();
        Self::make_deterministic(initial_ids, final_ids, trans, &alphabet)
    }

    fn make_deterministic(
        init: BTreeSet<State>,
        fin: BTreeSet<State>,
        trans: HashMap<TransOn, HashSet<State>>,
        alphabet: &Vec<Letter>,
    ) -> Self {
        let mut dfa_states = IdMap::new();
        let mut trans_dfa = HashMap::new();
        let init_dfa = State(dfa_states.insert(init.clone()));
        let mut final_dfa: BTreeSet<State> = BTreeSet::new();
        let mut queue = VecDeque::new();
        queue.push_front(init);

        let mut visited: HashSet<usize> = HashSet::new();

        while let Some(from_set) = queue.pop_front() {
            let from_id = dfa_states.insert(from_set.clone());

            if visited.contains(&from_id) {
                continue;
            } else {
                visited.insert(from_id);
            }

            // Check if this state should be final, if so, add it to final set.
            let is_final = !from_set.is_disjoint(&fin);
            if is_final {
                final_dfa.insert(State(from_id));
            }

            // We examine each possible transition from the state `from`.
            // So, we iterate over the alphabet and find all transitions.
            for &l in alphabet {
                let mut to_set: BTreeSet<State> = BTreeSet::new();

                // Extend the `to_set` with sets of next states
                // for each single state from `from_set`.
                for &state in &from_set {
                    let trans_on = TransOn { state, letter: l };
                    if let Some(to) = trans.get(&trans_on) {
                        to_set.extend(to);
                    }
                }

                // Store DFA transition and queue this state for processing.
                let to_id = dfa_states.insert(to_set.clone());
                trans_dfa.insert(
                    TransOn {
                        state: State(from_id),
                        letter: l,
                    },
                    State(to_id),
                );
                if !visited.contains(&to_id) {
                    queue.push_front(to_set);
                }
            }
        }

        Self {
            init: init_dfa,
            fin: final_dfa,
            trans: trans_dfa,
        }
    }

    /// Create a complementary `LangDfa` from this `LangDfa`.
    pub fn complement(self) -> Self {
        let alphabet: Vec<_> = self.trans.keys().map(|x| x.letter).collect();
        let states: Vec<_> = self
            .trans
            .keys()
            .map(|x| x.state)
            .chain(self.trans.values().copied())
            .collect();

        let mut new_fin = BTreeSet::new();
        let mut new_trans = HashMap::new();

        let trap = State(states.iter().max().map(|State(s)| s).unwrap_or(&0) + 1);
        new_fin.insert(trap);

        for &s in &states {
            for &l in &alphabet {
                let trans_on = TransOn {
                    state: s,
                    letter: l,
                };
                let to = self.trans.get(&trans_on);

                let Some(&to) = to else {
                    new_trans.insert(trans_on, trap);
                    continue;
                };

                new_trans.insert(trans_on, to);

                if !self.fin.contains(&to) {
                    new_fin.insert(to);
                }
            }

            if !self.fin.contains(&s) {
                new_fin.insert(s);
            }
        }

        Self {
            init: self.init,
            fin: new_fin,
            trans: new_trans,
        }
    }
}
