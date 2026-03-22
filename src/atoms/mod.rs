//! Construction of automata encoding PL literals.

use crate::{
    automaton::{LangDfa, OutputNumber, OutputType, State, TargetNfa, TransOn},
    formula::{Atom, Declarations, Var, simplify::Literal},
    paths_n::{PathSymbol, PathTuple},
};
use std::{
    borrow::Cow,
    collections::{BTreeSet, HashMap},
};

const INIT: State = State(usize::MAX); // initial state constant
const FIN: State = State(usize::MAX - 1); // final state constant

/// `NfaM` represents the automaton encoding a single PL_NFA literal.
#[derive(Clone, Debug)]
pub struct NfaM<'a> {
    pub init: State,
    pub fin: BTreeSet<State>,
    pred: Predicate,
    i: usize,
    j: usize,
    condition_set: Option<&'a BTreeSet<State>>,
    lang_dfa: Option<LangDfa>,
}

#[derive(Clone, Copy, Debug)]
enum Predicate {
    InputPrefix,
    InputEq,
    LangBelong,
    InputLength,
    PathEq,
    StartBelongsTo,
    EndBelongsTo,
    StartStartEq,
    EndEndEq,
    StartEndEq,
    EndStartEq,

    NotInputPrefix,
    NotInputEq,
    NotInputLength,
    NotPathEq,
    NotStartBelongsTo,
    NotEndBelongsTo,
    NotStartStartEq,
    NotEndEndEq,
    NotStartEndEq,
    NotEndStartEq,
}

impl<'a> NfaM<'a> {
    fn trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        match self.pred {
            Predicate::InputPrefix => self.prefix_trans(state, letter),
            Predicate::InputEq => self.input_eq_trans(state, letter),
            Predicate::LangBelong => self.lang_belong_trans(state, letter),
            Predicate::InputLength => self.length_trans(state, letter),
            Predicate::PathEq => self.path_eq_trans(state, letter),
            Predicate::StartBelongsTo => self.start_belongs_to_trans(state, letter),
            Predicate::EndBelongsTo => self.end_belongs_to_trans(state, letter),
            Predicate::StartStartEq => self.init_init_eq_trans(state, letter),
            Predicate::EndEndEq => self.final_final_eq_trans(state, letter),
            Predicate::StartEndEq => self.init_final_eq_trans(state, letter),
            Predicate::EndStartEq => self.final_init_eq_trans(state, letter),

            Predicate::NotInputPrefix => self.not_prefix_trans(state, letter),
            Predicate::NotInputEq => self.not_input_eq_trans(state, letter),
            Predicate::NotInputLength => self.not_length_trans(state, letter),
            Predicate::NotPathEq => self.not_path_eq_trans(state, letter),
            Predicate::NotStartBelongsTo => self.not_start_belongs_to_trans(state, letter),
            Predicate::NotEndBelongsTo => self.not_end_belongs_to_trans(state, letter),
            Predicate::NotStartStartEq => self.not_init_init_eq_trans(state, letter),
            Predicate::NotEndEndEq => self.not_final_final_eq_trans(state, letter),
            Predicate::NotStartEndEq => self.not_init_final_eq_trans(state, letter),
            Predicate::NotEndStartEq => self.not_final_init_eq_trans(state, letter),
        }
    }

    /// Construct an `NfaM` for the prefix predicate.
    pub fn prefix(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotInputPrefix,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::InputPrefix,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the input equality.
    pub fn input_eq(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotInputEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::InputEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the language inclusion predicate.
    pub fn lang_belong(i: usize, lang_dfa: LangDfa) -> NfaM<'a> {
        NfaM {
            init: lang_dfa.init,
            fin: lang_dfa.fin.clone(),
            pred: Predicate::LangBelong,
            i,
            j: 0,
            condition_set: None,
            lang_dfa: Some(lang_dfa),
        }
    }

    /// Construct an `NfaM` for the length comparison predicate.
    pub fn length(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotInputLength,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::InputLength,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the path equality predicate.
    pub fn path_eq(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotPathEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::PathEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the "start state belongs to" predicate.
    pub fn start_belongs_to(is_neg: bool, i: usize, condition_set: &BTreeSet<State>) -> NfaM<'_> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotStartBelongsTo,
                i,
                j: 0,
                condition_set: Some(condition_set),
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::StartBelongsTo,
                i,
                j: 0,
                condition_set: Some(condition_set),
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the "end state belongs to" predicate.
    pub fn end_belongs_to(is_neg: bool, i: usize, condition_set: &BTreeSet<State>) -> NfaM<'_> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotEndBelongsTo,
                i,
                j: 0,
                condition_set: Some(condition_set),
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::EndBelongsTo,
                i,
                j: 0,
                condition_set: Some(condition_set),
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the start state equality predicate.
    pub fn start_start_eq(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotStartStartEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::StartStartEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the end state equality predicate.
    pub fn end_end_eq(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotEndEndEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::EndEndEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the start/end state equality predicate.
    pub fn start_end_eq(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotStartEndEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::StartEndEq,
                i,
                j,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    /// Construct an `NfaM` for the end/start state equality predicate.
    pub fn end_start_eq(is_neg: bool, i: usize, j: usize) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotEndStartEq,
                i: j,
                j: i,
                condition_set: None,
                lang_dfa: None,
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::EndStartEq,
                i: j,
                j: i,
                condition_set: None,
                lang_dfa: None,
            }
        }
    }

    fn prefix_trans(&self, _: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if let PathSymbol::Letter(_) = l[self.i] {
            if l[self.i] == l[self.j] {
                return Cow::Borrowed(&[INIT]);
            }
        } else {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[])
    }

    fn not_prefix_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::Letter(_) = l[self.i]
            && l[self.i] != l[self.j]
        {
            return Cow::Borrowed(&[FIN]);
        }
        Cow::Borrowed(&[INIT])
    }

    fn input_eq_trans(&self, _: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match (l[self.i], l[self.j]) {
            (PathSymbol::Letter(l1), PathSymbol::Letter(l2)) => {
                if l1 == l2 {
                    return Cow::Borrowed(&[INIT]);
                }
                Cow::Borrowed(&[])
            }
            (_, PathSymbol::Letter(_)) | (PathSymbol::Letter(_), _) => Cow::Borrowed(&[]),
            _ => Cow::Borrowed(&[INIT]),
        }
    }

    fn not_input_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        match (l[self.i], l[self.j]) {
            (PathSymbol::Letter(l1), PathSymbol::Letter(l2)) => {
                if l1 != l2 {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[INIT])
            }
            (_, PathSymbol::Letter(_)) | (PathSymbol::Letter(_), _) => Cow::Borrowed(&[FIN]),
            _ => Cow::Borrowed(&[INIT]),
        }
    }

    fn lang_belong_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;
        let lang_dfa = self.lang_dfa.as_ref().unwrap();

        match l[self.i] {
            PathSymbol::Letter(x) => {
                let trans_on = TransOn { state, letter: x };
                let to_state = lang_dfa.trans.get(&trans_on);

                let Some(&to_state) = to_state else {
                    return Cow::Borrowed(&[]);
                };

                Cow::Owned(Vec::from([to_state]))
            }
            _ => Cow::Owned(Vec::from([state])),
        }
    }

    fn length_trans(&self, _: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if l[self.j] == PathSymbol::Bottom {
            if l[self.i] == PathSymbol::Bottom {
                return Cow::Borrowed(&[INIT]);
            }
        } else {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[])
    }

    fn not_length_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if l[self.j] == PathSymbol::Bottom && l[self.i] != PathSymbol::Bottom {
            return Cow::Borrowed(&[FIN]);
        }
        Cow::Borrowed(&[INIT])
    }

    fn path_eq_trans(&self, _: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if l[self.i] == l[self.j] {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[])
    }

    fn not_path_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if l[self.i] == l[self.j] {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[FIN])
    }

    fn start_belongs_to_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;
        let Some(condition_set) = self.condition_set else {
            return Cow::Borrowed(&[]);
        };

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::State(x) = l[self.i]
            && condition_set.contains(&x)
        {
            return Cow::Borrowed(&[FIN]);
        }

        Cow::Borrowed(&[])
    }

    fn not_start_belongs_to_trans(
        &self,
        state: State,
        letter: &PathTuple,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;
        let Some(condition_set) = self.condition_set else {
            return Cow::Borrowed(&[]);
        };

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::State(x) = l[self.i]
            && !condition_set.contains(&x)
        {
            return Cow::Borrowed(&[FIN]);
        }
        Cow::Borrowed(&[])
    }

    fn end_belongs_to_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;
        let Some(condition_set) = self.condition_set else {
            return Cow::Borrowed(&[]);
        };

        match (state, l[self.i]) {
            (INIT, PathSymbol::State(x)) if condition_set.contains(&x) => {
                Cow::Borrowed(&[INIT, FIN])
            }
            (INIT, _) => Cow::Borrowed(&[INIT]),
            (FIN, PathSymbol::Bottom) => Cow::Borrowed(&[FIN]),
            _ => Cow::Borrowed(&[]),
        }
    }

    fn not_end_belongs_to_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;
        let Some(condition_set) = self.condition_set else {
            return Cow::Borrowed(&[]);
        };

        match (state, l[self.i]) {
            (INIT, PathSymbol::State(x)) if !condition_set.contains(&x) => {
                Cow::Borrowed(&[INIT, FIN])
            }
            (INIT, _) => Cow::Borrowed(&[INIT]),
            (FIN, PathSymbol::Bottom) => Cow::Borrowed(&[FIN]),
            _ => Cow::Borrowed(&[]),
        }
    }

    fn init_init_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::State(x) = l[self.i]
            && let PathSymbol::State(y) = l[self.j]
            && x == y
        {
            return Cow::Borrowed(&[FIN]);
        }

        Cow::Borrowed(&[])
    }

    fn not_init_init_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::State(x) = l[self.i]
            && let PathSymbol::State(y) = l[self.j]
            && x != y
        {
            return Cow::Borrowed(&[FIN]);
        }

        Cow::Borrowed(&[])
    }

    fn final_final_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = Vec::from([INIT]);

                if let PathSymbol::State(State(x)) = l[self.i] {
                    let state_id = x * 2;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(State(x)) = l[self.j] {
                    let state_id = (x * 2) + 1;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(x) = l[self.i]
                    && let PathSymbol::State(y) = l[self.j]
                    && x == y
                {
                    to.push(FIN);
                }

                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[self.i] == PathSymbol::Bottom && l[self.j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            State(state) if state % 2 == 0 => {
                let mut to = Vec::new();
                if l[self.i] == PathSymbol::Bottom {
                    let target = State(state / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[self.j]
                        && target == y
                    {
                        to.push(FIN);
                    }
                }

                Cow::Owned(to)
            }
            State(state) if state % 2 == 1 => {
                let mut to = Vec::new();
                if l[self.j] == PathSymbol::Bottom {
                    let target = State((state - 1) / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[self.i]
                        && target == y
                    {
                        to.push(FIN);
                    }
                }

                Cow::Owned(to)
            }
            _ => Cow::Borrowed(&[]),
        }
    }

    fn not_final_final_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = Vec::from([INIT]);

                if let PathSymbol::State(State(x)) = l[self.i] {
                    let state_id = x * 2;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(State(x)) = l[self.j] {
                    let state_id = (x * 2) + 1;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(x) = l[self.i]
                    && let PathSymbol::State(y) = l[self.j]
                    && x != y
                {
                    to.push(FIN);
                }

                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[self.i] == PathSymbol::Bottom && l[self.j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            State(state) if state % 2 == 0 => {
                let mut to = Vec::new();
                if l[self.i] == PathSymbol::Bottom {
                    let target = State(state / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[self.j]
                        && target != y
                    {
                        to.push(FIN);
                    }
                }

                Cow::Owned(to)
            }
            State(state) if state % 2 == 1 => {
                let mut to = Vec::new();
                if l[self.j] == PathSymbol::Bottom {
                    let target = State((state - 1) / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[self.i]
                        && target != y
                    {
                        to.push(FIN);
                    }
                }

                Cow::Owned(to)
            }
            _ => Cow::Borrowed(&[]),
        }
    }

    fn init_final_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = Vec::new();
                if let PathSymbol::State(x) = l[self.i] {
                    to.push(x);
                }
                if let PathSymbol::State(x) = l[self.i]
                    && let PathSymbol::State(y) = l[self.j]
                    && x == y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[self.j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            state => {
                let mut to = Vec::from([state]);
                if let PathSymbol::State(y) = l[self.j]
                    && state == y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
        }
    }

    fn not_init_final_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = Vec::new();
                if let PathSymbol::State(x) = l[self.i] {
                    to.push(x);
                }
                if let PathSymbol::State(x) = l[self.i]
                    && let PathSymbol::State(y) = l[self.j]
                    && x != y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[self.j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            state => {
                let mut to = Vec::from([state]);
                if let PathSymbol::State(y) = l[self.j]
                    && state != y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
        }
    }

    fn final_init_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        self.init_final_eq_trans(state, letter)
    }

    fn not_final_init_eq_trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        self.not_init_final_eq_trans(state, letter)
    }
}

/// `MAutomata` is a container for multiple `NfaM`.
pub struct MAutomata<'a> {
    ms: Vec<NfaM<'a>>,
}

impl<'a> MAutomata<'a> {
    /// Get the initial states for these `MAutomata`.
    pub fn inits(&self) -> Vec<BTreeSet<State>> {
        let inits_ms: Vec<State> = self.ms.iter().map(|x| x.init).collect();

        inits_ms.iter().map(|&x| BTreeSet::from([x])).collect()
    }

    /// Run these `MAutomata` on the `state` and `letter`, returning the new states.
    pub fn trans(&self, state: &[BTreeSet<State>], letter: &PathTuple) -> Vec<BTreeSet<State>> {
        let mut states = Vec::new();

        for (i, state) in state.iter().enumerate() {
            let mut to: BTreeSet<State> = BTreeSet::new();

            for &s in state {
                let x = self.ms.get(i).unwrap().trans(s, letter);
                to.extend(x.iter());
            }
            states.push(to);
        }

        states
    }

    /// Check whether these `MAutomata` are in final state.
    pub fn is_final(&self, state: &[BTreeSet<State>]) -> bool {
        let fins = self.ms.iter().map(|m| &m.fin);

        state.iter().zip(fins).all(|(s, f)| !s.is_disjoint(f))
    }

    /// Extend these `MAutomata` with other ones.
    pub fn extend(&mut self, other: &MAutomata<'a>) {
        self.ms.extend(other.ms.iter().cloned());
    }
}

impl<'a> From<Vec<NfaM<'a>>> for MAutomata<'a> {
    fn from(value: Vec<NfaM<'a>>) -> Self {
        MAutomata { ms: value }
    }
}

/// `NpaM` represents the Parikh automaton encoding a single PL_SUM literal.
pub struct NpaM {
    pub init: State,
    pred: CountPredicate,
    i: usize,
    j: usize,
}

/// A state of a single `NpaM`.
#[derive(Eq, Hash, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct ParikhState {
    pub state: State,
    pub counter: (usize, usize),
}

enum CountPredicate {
    NotEq,
}

impl NpaM {
    /// Construct an `NpaM` for the "count is not equal to" predicate.
    pub fn count_neq(i: usize, j: usize) -> NpaM {
        NpaM {
            init: INIT,
            pred: CountPredicate::NotEq,
            i,
            j,
        }
    }

    fn trans(&self, state: ParikhState, letter: &PathTuple) -> Vec<ParikhState> {
        match self.pred {
            CountPredicate::NotEq => self.count_pa_trans(state, letter),
        }
    }

    fn accepts(&self, state: ParikhState) -> bool {
        match self.pred {
            CountPredicate::NotEq => self.count_not_eq_accepts(state),
        }
    }

    fn count_pa_trans(&self, state: ParikhState, letter: &PathTuple) -> Vec<ParikhState> {
        let PathTuple(l) = letter;

        match (l[self.i], l[self.j]) {
            (PathSymbol::OutNum(OutputNumber(n1)), PathSymbol::OutNum(OutputNumber(n2))) => {
                let counter = (state.counter.0 + n1, state.counter.1 + n2);

                Vec::from([ParikhState {
                    state: INIT,
                    counter,
                }])
            }
            (_, PathSymbol::OutNum(OutputNumber(n))) => {
                let counter = (state.counter.0, state.counter.1 + n);

                Vec::from([ParikhState {
                    state: INIT,
                    counter,
                }])
            }
            (PathSymbol::OutNum(OutputNumber(n)), _) => {
                let counter = (state.counter.0 + n, state.counter.1);

                Vec::from([ParikhState {
                    state: INIT,
                    counter,
                }])
            }
            _ => Vec::from([state]),
        }
    }

    fn count_not_eq_accepts(&self, state: ParikhState) -> bool {
        state.counter.0 != state.counter.1
    }
}

/// `ParikhAutomata` is a container for multiple `NpaM`.
pub struct ParikhAutomata {
    pas: Vec<NpaM>,
}

impl ParikhAutomata {
    /// Create an empty instance of `ParikhAutomata`.
    pub fn empty() -> Self {
        ParikhAutomata { pas: Vec::new() }
    }

    /// Get the initial states for these `ParikhAutomata`.
    pub fn inits(&self) -> Vec<BTreeSet<ParikhState>> {
        let inits_pa: Vec<State> = self.pas.iter().map(|x| x.init).collect();

        inits_pa
            .iter()
            .map(|&s| {
                BTreeSet::from([ParikhState {
                    state: s,
                    counter: (0, 0),
                }])
            })
            .collect()
    }

    /// Run these `ParikhAutomata` on the `state` and `letter`, returning the new states.
    pub fn trans(
        &self,
        state: &[BTreeSet<ParikhState>],
        letter: &PathTuple,
    ) -> Vec<BTreeSet<ParikhState>> {
        let mut states = Vec::new();

        for (i, state) in state.iter().enumerate() {
            let mut to: BTreeSet<ParikhState> = BTreeSet::new();

            for &s in state {
                let x = self.pas.get(i).unwrap().trans(s, letter);
                to.extend(x);
            }
            states.push(to);
        }

        states
    }

    /// Check whether these `MAutomata` are in final state.
    pub fn is_final(&self, state: &[BTreeSet<ParikhState>]) -> bool {
        self.pas
            .iter()
            .zip(state)
            .all(|(pa, states)| states.iter().any(|s| pa.accepts(*s)))
    }

    /// Check whether there are no `ParikhAutomata`.
    pub fn is_empty(&self) -> bool {
        self.pas.is_empty()
    }

    /// Get the number of `ParikhAutomata`.
    pub fn len(&self) -> usize {
        self.pas.len()
    }
}

/// Take a list of literals (a single conjunction of atoms or negated atoms)
/// and return a list of NfaM and NpaM automata that correspond to these literals.
pub fn literals_to_automata<'a>(
    lits: Vec<Literal>,
    declarations: &Declarations,
    target_nfa: &'a TargetNfa,
    reach_init: &'a BTreeSet<State>,
    reach_final: &'a BTreeSet<State>,
    language_automata: &'a HashMap<String, LangDfa>,
) -> (MAutomata<'a>, ParikhAutomata) {
    let mut ms = Vec::new();
    let mut pas = Vec::new();

    for tok in lits {
        let pred: Atom;
        let is_neg: bool;

        match tok {
            Literal::Predicate(p) => {
                pred = p;
                is_neg = false;
            }
            Literal::NotPredicate(p) => {
                pred = p;
                is_neg = true;
            }
        }

        // TODO: refactor
        match pred {
            Atom::Prefix(var1, var2) => match (var1, var2) {
                (Var::Input(var1), Var::Input(var2)) => {
                    let pi1 = declarations.path_id_by_input_var(var1);
                    let pi2 = declarations.path_id_by_input_var(var2);

                    let m = NfaM::prefix(is_neg, pi1, pi2);
                    ms.push(m);
                }
                _ => panic!("wrong variable type for prefix"),
            },
            Atom::LessOrEq(var1, var2) => match (var1, var2) {
                (Var::Input(var1), Var::Input(var2)) => {
                    let pi1 = declarations.path_id_by_input_var(var1);
                    let pi2 = declarations.path_id_by_input_var(var2);

                    let m = NfaM::length(is_neg, pi1, pi2);
                    ms.push(m);
                }
                _ => panic!("wrong variable type for less-or-eq"),
            },
            Atom::Belongs(var, lang) => match var {
                Var::Input(var) => {
                    let pi = declarations.path_id_by_input_var(var);
                    let dfa = language_automata
                        .get(&lang)
                        .unwrap_or_else(|| panic!("undeclared language {lang}"))
                        .clone();

                    let dfa = if is_neg { dfa.complement() } else { dfa };

                    let m = NfaM::lang_belong(pi, dfa);
                    ms.push(m);
                }
                _ => panic!("wrong variable type for langugage inclusion"),
            },
            Atom::Init(var) | Atom::Final(var) | Atom::ReachInit(var) | Atom::ReachFinal(var) => {
                let m: NfaM;
                let set = match pred {
                    Atom::Init(_) => &target_nfa.init,
                    Atom::Final(_) => &target_nfa.fin,
                    Atom::ReachInit(_) => reach_init,
                    Atom::ReachFinal(_) => reach_final,
                    _ => {
                        continue;
                    }
                };

                if let Some(path) = declarations.path_id_by_start_state(var) {
                    m = NfaM::start_belongs_to(is_neg, path, set);
                } else if let Some(path) = declarations.path_id_by_end_state(var) {
                    m = NfaM::end_belongs_to(is_neg, path, set);
                } else {
                    panic!("unknown state variable")
                }

                ms.push(m);
            }
            Atom::Eq(var1, var2) => match (var1, var2) {
                (Var::Path(var1), Var::Path(var2)) => {
                    let m = NfaM::path_eq(is_neg, var1, var2);
                    ms.push(m);
                }
                (Var::State(var1), Var::State(var2)) => {
                    let m: NfaM;

                    if let Some(path1) = declarations.path_id_by_start_state(var1) {
                        if let Some(path2) = declarations.path_id_by_start_state(var2) {
                            m = NfaM::start_start_eq(is_neg, path1, path2);

                            ms.push(m);
                        } else if let Some(path2) = declarations.path_id_by_end_state(var2) {
                            m = NfaM::start_end_eq(is_neg, path1, path2);

                            ms.push(m);
                        } else {
                            panic!("unknown state variable")
                        }
                    } else if let Some(path1) = declarations.path_id_by_end_state(var1) {
                        if let Some(path2) = declarations.path_id_by_start_state(var2) {
                            m = NfaM::end_start_eq(is_neg, path1, path2);

                            ms.push(m);
                        } else if let Some(path2) = declarations.path_id_by_end_state(var2) {
                            m = NfaM::end_end_eq(is_neg, path1, path2);

                            ms.push(m);
                        } else {
                            panic!("unknown state variable")
                        }
                    } else {
                        panic!("unknown state variable")
                    }
                }
                (Var::Input(var1), Var::Input(var2)) => {
                    let pi1 = declarations.path_id_by_input_var(var1);
                    let pi2 = declarations.path_id_by_input_var(var2);

                    let m = NfaM::input_eq(is_neg, pi1, pi2);
                    ms.push(m);
                }
                (Var::Output(var1), Var::Output(var2)) => {
                    let pi1 = declarations.path_id_by_output_var(var1);
                    let pi2 = declarations.path_id_by_output_var(var2);

                    if !is_neg {
                        unimplemented!("no output equality")
                    }

                    match target_nfa.output_type {
                        OutputType::None => unimplemented!("no output equality for trivial monoid"),
                        OutputType::Number => pas.push(NpaM::count_neq(pi1, pi2)),
                    }
                }
                _ => panic!("wrong variable type for eq"),
            },
        }
    }

    (MAutomata { ms }, ParikhAutomata { pas })
}
