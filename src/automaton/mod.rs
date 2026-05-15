//! Automata definitions and algorithms.

use crate::automaton::parse::{RawAutomaton, RawTransTo};
use crate::util::IdMap;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::hash::Hash;

mod parse;

/// A state of a finite automaton.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug, Default)]
pub struct State(pub usize);

/// A letter of an alphabet of a finite automaton.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug)]
pub struct Letter(pub usize);

/// An output number of a finite automaton with outputs.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug)]
pub struct OutputNumber(pub i32);

/// An output letter of a finite automaton with number outputs.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug)]
pub struct OutputLetter(pub usize);

/// An output word of a finite automaton with word outputs.
pub type OutputWord = Vec<OutputLetter>;
pub type OutputWordRef<'a> = &'a [OutputLetter];

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

/// An ending state of a transition of a finite automaton with number outputs.
#[derive(Eq, Hash, PartialEq, Clone, Copy, Debug)]
pub struct NumberTransTo {
    pub state: State,
    pub output: OutputNumber,
}

/// An ending state of a transition of a finite automaton with word outputs.
#[derive(Eq, Hash, PartialEq, Clone)]
pub struct WordTransTo {
    pub state: State,
    pub output: OutputWord,
}

/// Possible transitions variants.
/// `None` is for classic finite automaton.
/// `Number` is for finite automata with number outputs.
pub enum Transitions {
    None(HashMap<TransOn, HashSet<TransTo>>),
    Number(HashMap<TransOn, HashSet<NumberTransTo>>),
    Word(HashMap<TransOn, HashSet<WordTransTo>>),
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
            Transitions::Word(t) => extract(t.keys()),
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
            Transitions::Word(trans) => {
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
    Word,
}

/// Target Non-Deterministic Finite Automaton for Model-Checking.
pub struct TargetNfa {
    pub init: BTreeSet<State>,
    pub fin: BTreeSet<State>,
    pub trans: Transitions,
    pub state_to_id: IdMap<String, usize>,
    pub letter_to_id: IdMap<String, usize>,
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

pub struct ReachSets {
    pub init: BTreeSet<State>,
    pub fin: BTreeSet<State>,
}

impl TargetNfa {
    /// Create a new `TargetNfa` by parsing from a `&str`.
    pub fn parse(value: &str) -> Result<Self, String> {
        let raw_automaton = parse::parse_automaton(value)?;

        let all_empty = raw_automaton
            .trans
            .iter()
            .all(|(_, ys)| ys.iter().all(|y| y.output.is_empty()));

        let all_number = raw_automaton
            .trans
            .iter()
            .all(|(_, ys)| ys.iter().all(|y| y.output.parse::<i32>().is_ok()));

        let output_type = if all_empty {
            OutputType::None
        } else if all_number {
            OutputType::Number
        } else {
            OutputType::Word
        };

        Ok(TargetNfa::new(raw_automaton, output_type))
    }

    fn new(raw_automaton: RawAutomaton, output_type: OutputType) -> TargetNfa {
        let mut state_to_id = IdMap::new();
        let mut letter_to_id = IdMap::new();

        let mut initial_ids = BTreeSet::new();
        for state in raw_automaton.init {
            let init_id = state_to_id.insert(state);
            initial_ids.insert(State(init_id));
        }

        let mut transition = match output_type {
            OutputType::None => Transitions::None(HashMap::new()),
            OutputType::Number => Transitions::Number(HashMap::new()),
            OutputType::Word => Transitions::Word(HashMap::new()),
        };

        for (raw_trans_on, raw_trans_to_set) in raw_automaton.trans {
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

                Transitions::Word(ref mut transition) => {
                    let convert = |to: RawTransTo| WordTransTo {
                        state: State(state_to_id.insert(to.state)),
                        output: to
                            .output
                            .split("|")
                            .map(|l| OutputLetter(letter_to_id.insert(l.to_owned())))
                            .collect(),
                    };

                    add_trans_to(raw_trans_to_set, trans_on, transition, convert);
                }
            }
        }

        let mut final_ids = BTreeSet::new();
        for state in raw_automaton.fin {
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
    pub fn states(&self) -> BTreeSet<State> {
        self.state_to_id.ids().iter().map(|&i| State(i)).collect()
    }

    pub fn reach_sets(&self) -> ReachSets {
        ReachSets {
            init: self.reach_init(),
            fin: self.reach_final(),
        }
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
#[derive(Clone, Debug, Default)]
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
    pub fn parse(
        input: &str,
        target_letter_to_id: &IdMap<String, usize>,
    ) -> Result<LangDfa, String> {
        let raw_automaton = parse::parse_automaton(input)?;

        Ok(LangDfa::new(raw_automaton, target_letter_to_id))
    }

    fn new(raw_automaton: RawAutomaton, target_letter_to_id: &IdMap<String, usize>) -> LangDfa {
        let mut state_to_id = IdMap::new();
        let mut target_letter_to_id = target_letter_to_id.clone();

        let initial_ids: BTreeSet<State> = raw_automaton
            .init
            .into_iter()
            .map(|x| State(state_to_id.insert(x)))
            .collect();

        let final_ids: BTreeSet<State> = raw_automaton
            .fin
            .into_iter()
            .map(|x| State(state_to_id.insert(x)))
            .collect();

        let mut trans = HashMap::new();
        for (raw_trans_on, raw_trans_to_set) in raw_automaton.trans {
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

    pub fn states(&self) -> Vec<State> {
        let states: HashSet<_> = self
            .trans
            .keys()
            .map(|x| x.state)
            .chain(self.trans.values().copied())
            .collect();

        states.into_iter().collect()
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
        let alphabet: BTreeSet<_> = self.trans.keys().map(|x| x.letter).collect();
        let states: BTreeSet<_> = self
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
            if !self.fin.contains(&s) {
                new_fin.insert(s);
            }

            for &l in &alphabet {
                let trans_on = TransOn {
                    state: s,
                    letter: l,
                };
                let to = *self.trans.get(&trans_on).unwrap_or(&trap);
                new_trans.insert(trans_on, to);
            }
        }

        for &l in &alphabet {
            new_trans.insert(
                TransOn {
                    state: trap,
                    letter: l,
                },
                trap,
            );
        }

        Self {
            init: self.init,
            fin: new_fin,
            trans: new_trans,
        }
    }
}
