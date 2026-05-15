//! Construction of automata encoding PL literals.

use crate::{
    automaton::{
        LangDfa, Letter, OutputLetter, OutputNumber, OutputType, ReachSets, State, TargetNfa,
        TransOn,
    },
    formula::{Atom, PathId, simplify::Literal},
    paths_n::{PathSymbol, PathTuple},
    util,
};
use std::{
    borrow::Cow,
    collections::{BTreeSet, HashMap},
};

const INIT: State = State(usize::MAX); // initial state constant
const FIN: State = State(usize::MAX - 1); // final state constant
const TRAP: State = State(usize::MAX - 2); // trap state constant

/// `NfaM` represents the automaton encoding a single PL_NFA literal.
#[derive(Clone, Debug)]
pub struct NfaM<'a> {
    init: State,
    fin: BTreeSet<State>,
    pred: Predicate<'a>,
}

#[derive(Clone, Debug)]
enum Predicate<'a> {
    InputPrefix { i: PathId, j: PathId },
    InputEq { i: PathId, j: PathId },
    InputLangBelong { i: PathId, lang: LangDfa },
    InputLength { i: PathId, j: PathId },
    PathEq { i: PathId, j: PathId },
    EndBelongsTo { i: PathId, set: &'a BTreeSet<State> },
    EndEqualTo { i: PathId, s: State },
    StartStartEq { i: PathId, j: PathId },
    EndEndEq { i: PathId, j: PathId },
    StartEndEq { i: PathId, j: PathId },
    EndStartEq { i: PathId, j: PathId },

    NotInputPrefix { i: PathId, j: PathId },
    NotInputEq { i: PathId, j: PathId },
    NotInputLength { i: PathId, j: PathId },
    NotPathEq { i: PathId, j: PathId },
    NotEndBelongsTo { i: PathId, set: &'a BTreeSet<State> },
    NotStartStartEq { i: PathId, j: PathId },
    NotEndEndEq { i: PathId, j: PathId },
    NotStartEndEq { i: PathId, j: PathId },
    NotEndStartEq { i: PathId, j: PathId },
}

impl<'a> Predicate<'a> {
    fn trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        use Predicate::*;
        match self {
            InputPrefix { i, j } => Self::prefix_trans(state, letter, *i, *j),
            InputEq { i, j } => Self::input_eq_trans(state, letter, *i, *j),
            InputLangBelong { i, lang } => Self::input_lang_belong_trans(state, letter, *i, lang),
            InputLength { i, j } => Self::length_trans(state, letter, *i, *j),
            PathEq { i, j } => Self::path_eq_trans(state, letter, *i, *j),
            EndBelongsTo { i, set } => Self::end_belongs_to_trans(state, letter, *i, set),
            EndEqualTo { i, s } => Self::end_equal_to_trans(state, letter, *i, *s),
            StartStartEq { i, j } => Self::init_init_eq_trans(state, letter, *i, *j),
            EndEndEq { i, j } => Self::final_final_eq_trans(state, letter, *i, *j),
            StartEndEq { i, j } => Self::init_final_eq_trans(state, letter, *i, *j),
            EndStartEq { i, j } => Self::final_init_eq_trans(state, letter, *i, *j),

            NotInputPrefix { i, j } => Self::not_prefix_trans(state, letter, *i, *j),
            NotInputEq { i, j } => Self::not_input_eq_trans(state, letter, *i, *j),
            NotInputLength { i, j } => Self::not_length_trans(state, letter, *i, *j),
            NotPathEq { i, j } => Self::not_path_eq_trans(state, letter, *i, *j),
            NotEndBelongsTo { i, set } => Self::not_end_belongs_to_trans(state, letter, *i, set),
            NotStartStartEq { i, j } => Self::not_init_init_eq_trans(state, letter, *i, *j),
            NotEndEndEq { i, j } => Self::not_final_final_eq_trans(state, letter, *i, *j),
            NotStartEndEq { i, j } => Self::not_init_final_eq_trans(state, letter, *i, *j),
            NotEndStartEq { i, j } => Self::not_final_init_eq_trans(state, letter, *i, *j),
        }
    }

    fn prefix_trans(
        _: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if let PathSymbol::Letter(_) = l[i] {
            if l[i] == l[j] {
                return Cow::Borrowed(&[INIT]);
            }
        } else {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[])
    }

    fn not_prefix_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::Letter(_) = l[i]
            && l[i] != l[j]
        {
            return Cow::Borrowed(&[FIN]);
        }
        Cow::Borrowed(&[INIT])
    }

    fn input_eq_trans(
        _: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match (l[i], l[j]) {
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

    fn not_input_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        match (l[i], l[j]) {
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

    fn input_lang_belong_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        lang: &LangDfa,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match l[i] {
            PathSymbol::Letter(x) => {
                let trans_on = TransOn { state, letter: x };
                let to_state = lang.trans.get(&trans_on);

                let Some(&to_state) = to_state else {
                    return Cow::Borrowed(&[]);
                };

                Cow::Owned(vec![to_state])
            }
            _ => Cow::Owned(vec![state]),
        }
    }

    fn length_trans(
        _: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if l[j] == PathSymbol::Bottom {
            if l[i] == PathSymbol::Bottom {
                return Cow::Borrowed(&[INIT]);
            }
        } else {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[])
    }

    fn not_length_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if l[j] == PathSymbol::Bottom && l[i] != PathSymbol::Bottom {
            return Cow::Borrowed(&[FIN]);
        }
        Cow::Borrowed(&[INIT])
    }

    fn path_eq_trans(
        _: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if l[i] == l[j] {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[])
    }

    fn not_path_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if l[i] == l[j] {
            return Cow::Borrowed(&[INIT]);
        }
        Cow::Borrowed(&[FIN])
    }

    fn end_belongs_to_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        set: &BTreeSet<State>,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match (state, l[i]) {
            (INIT, PathSymbol::State(x)) if set.contains(&x) => Cow::Borrowed(&[INIT, FIN]),
            (INIT, _) => Cow::Borrowed(&[INIT]),
            (FIN, PathSymbol::Bottom) => Cow::Borrowed(&[FIN]),
            _ => Cow::Borrowed(&[]),
        }
    }

    fn not_end_belongs_to_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        set: &BTreeSet<State>,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match (state, l[i]) {
            (INIT, PathSymbol::State(x)) if !set.contains(&x) => Cow::Borrowed(&[INIT, FIN]),
            (INIT, _) => Cow::Borrowed(&[INIT]),
            (FIN, PathSymbol::Bottom) => Cow::Borrowed(&[FIN]),
            _ => Cow::Borrowed(&[]),
        }
    }

    fn end_equal_to_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        target_state: State,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match (state, l[i]) {
            (INIT, PathSymbol::State(x)) if x == target_state => Cow::Borrowed(&[INIT, FIN]),
            (INIT, _) => Cow::Borrowed(&[INIT]),
            (FIN, PathSymbol::Bottom) => Cow::Borrowed(&[FIN]),
            _ => Cow::Borrowed(&[]),
        }
    }

    fn init_init_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::State(x) = l[i]
            && let PathSymbol::State(y) = l[j]
            && x == y
        {
            return Cow::Borrowed(&[FIN]);
        }

        Cow::Borrowed(&[])
    }

    fn not_init_init_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        if state == FIN {
            return Cow::Borrowed(&[FIN]);
        }

        if let PathSymbol::State(x) = l[i]
            && let PathSymbol::State(y) = l[j]
            && x != y
        {
            return Cow::Borrowed(&[FIN]);
        }

        Cow::Borrowed(&[])
    }

    fn final_final_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = vec![INIT];

                if let PathSymbol::State(State(x)) = l[i] {
                    let state_id = x * 2;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(State(x)) = l[j] {
                    let state_id = (x * 2) + 1;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(x) = l[i]
                    && let PathSymbol::State(y) = l[j]
                    && x == y
                {
                    to.push(FIN);
                }

                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[i] == PathSymbol::Bottom && l[j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            State(state) if state % 2 == 0 => {
                let mut to = Vec::new();
                if l[i] == PathSymbol::Bottom {
                    let target = State(state / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[j]
                        && target == y
                    {
                        to.push(FIN);
                    }
                }

                Cow::Owned(to)
            }
            State(state) if state % 2 == 1 => {
                let mut to = Vec::new();
                if l[j] == PathSymbol::Bottom {
                    let target = State((state - 1) / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[i]
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

    fn not_final_final_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = vec![INIT];

                if let PathSymbol::State(State(x)) = l[i] {
                    let state_id = x * 2;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(State(x)) = l[j] {
                    let state_id = (x * 2) + 1;
                    to.push(State(state_id));
                }
                if let PathSymbol::State(x) = l[i]
                    && let PathSymbol::State(y) = l[j]
                    && x != y
                {
                    to.push(FIN);
                }

                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[i] == PathSymbol::Bottom && l[j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            State(state) if state % 2 == 0 => {
                let mut to = Vec::new();
                if l[i] == PathSymbol::Bottom {
                    let target = State(state / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[j]
                        && target != y
                    {
                        to.push(FIN);
                    }
                }

                Cow::Owned(to)
            }
            State(state) if state % 2 == 1 => {
                let mut to = Vec::new();
                if l[j] == PathSymbol::Bottom {
                    let target = State((state - 1) / 2);

                    to.push(State(state));
                    if let PathSymbol::State(y) = l[i]
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

    fn init_final_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = Vec::new();
                if let PathSymbol::State(x) = l[i] {
                    to.push(x);
                }
                if let PathSymbol::State(x) = l[i]
                    && let PathSymbol::State(y) = l[j]
                    && x == y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            state => {
                let mut to = vec![state];
                if let PathSymbol::State(y) = l[j]
                    && state == y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
        }
    }

    fn not_init_final_eq_trans(
        state: State,
        letter: &PathTuple,
        PathId(i): PathId,
        PathId(j): PathId,
    ) -> Cow<'static, [State]> {
        let PathTuple(l) = letter;

        match state {
            state if state == INIT => {
                let mut to = Vec::new();
                if let PathSymbol::State(x) = l[i] {
                    to.push(x);
                }
                if let PathSymbol::State(x) = l[i]
                    && let PathSymbol::State(y) = l[j]
                    && x != y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
            state if state == FIN => {
                if l[j] == PathSymbol::Bottom {
                    return Cow::Borrowed(&[FIN]);
                }
                Cow::Borrowed(&[])
            }
            state => {
                let mut to = vec![state];
                if let PathSymbol::State(y) = l[j]
                    && state != y
                {
                    to.push(FIN);
                }
                Cow::Owned(to)
            }
        }
    }

    fn final_init_eq_trans(
        state: State,
        letter: &PathTuple,
        i: PathId,
        j: PathId,
    ) -> Cow<'static, [State]> {
        Self::init_final_eq_trans(state, letter, j, i) // swap
    }

    fn not_final_init_eq_trans(
        state: State,
        letter: &PathTuple,
        i: PathId,
        j: PathId,
    ) -> Cow<'static, [State]> {
        Self::not_init_final_eq_trans(state, letter, j, i) // swap
    }
}

impl<'a> NfaM<'a> {
    fn trans(&self, state: State, letter: &PathTuple) -> Cow<'static, [State]> {
        self.pred.trans(state, letter)
    }

    /// Construct an `NfaM` for the prefix predicate.
    fn prefix(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotInputPrefix { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::InputPrefix { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the input equality.
    pub fn input_eq(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotInputEq { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::InputEq { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the input language inclusion predicate.
    fn input_lang_belong(i: PathId, lang: LangDfa) -> NfaM<'a> {
        NfaM {
            init: lang.init,
            fin: lang.fin.clone(),
            pred: Predicate::InputLangBelong { i, lang },
        }
    }

    /// Construct an `NfaM` for the length comparison predicate.
    fn length(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotInputLength { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::InputLength { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the path equality predicate.
    fn path_eq(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotPathEq { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([INIT]),
                pred: Predicate::PathEq { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the "end state belongs to" predicate.
    fn end_belongs_to(is_neg: bool, i: PathId, set: &BTreeSet<State>) -> NfaM<'_> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotEndBelongsTo { i, set },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::EndBelongsTo { i, set },
            }
        }
    }

    /// Construct an `NfaM` for the "end state is equal to" predicate.
    pub fn end_equal_to(i: PathId, state: State) -> NfaM<'a> {
        NfaM {
            init: INIT,
            fin: BTreeSet::from([FIN]),
            pred: Predicate::EndEqualTo { i, s: state },
        }
    }

    /// Construct an `NfaM` for the start state equality predicate.
    pub fn start_start_eq(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotStartStartEq { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::StartStartEq { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the end state equality predicate.
    pub fn end_end_eq(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotEndEndEq { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::EndEndEq { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the start/end state equality predicate.
    pub fn start_end_eq(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotStartEndEq { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::StartEndEq { i, j },
            }
        }
    }

    /// Construct an `NfaM` for the end/start state equality predicate.
    pub fn end_start_eq(is_neg: bool, i: PathId, j: PathId) -> NfaM<'a> {
        if is_neg {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::NotEndStartEq { i, j },
            }
        } else {
            NfaM {
                init: INIT,
                fin: BTreeSet::from([FIN]),
                pred: Predicate::EndStartEq { i, j },
            }
        }
    }
}

/// `MAutomata` is a container for multiple `NfaM`.
#[derive(Clone, Default)]
pub struct MAutomata<'a> {
    ms: Vec<NfaM<'a>>,
}

/// `MAutomataState` is the state representation of `MAutomata`.
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct MAutomataState(Vec<BTreeSet<State>>);

impl MAutomataState {
    pub fn is_dead(&self) -> bool {
        self.0.iter().any(|x| x.is_empty()) && !self.0.is_empty()
    }
}

impl<'a> MAutomata<'a> {
    pub fn new() -> Self {
        MAutomata::default()
    }

    /// Get the initial states for these `MAutomata`.
    pub fn inits(&self) -> MAutomataState {
        let inits_ms: Vec<State> = self.ms.iter().map(|x| x.init).collect();

        MAutomataState(inits_ms.iter().map(|&x| BTreeSet::from([x])).collect())
    }

    /// Run these `MAutomata` on the `state` and `letter`, returning the new states.
    pub fn trans(
        &self,
        MAutomataState(state): &MAutomataState,
        letter: &PathTuple,
    ) -> MAutomataState {
        let mut states = Vec::new();

        for (state, automaton) in state.iter().zip(&self.ms) {
            let mut to: BTreeSet<State> = BTreeSet::new();

            for &s in state {
                let x = automaton.trans(s, letter);
                to.extend(x.iter());
            }
            states.push(to);
        }

        MAutomataState(states)
    }

    /// Check whether these `MAutomata` are in final state.
    pub fn is_final(&self, MAutomataState(state): &MAutomataState) -> bool {
        let fins = self.ms.iter().map(|m| &m.fin);

        state.iter().zip(fins).all(|(s, f)| !s.is_disjoint(f))
    }

    pub fn push(&mut self, m: NfaM<'a>) {
        self.ms.push(m);
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

#[derive(Clone)]
struct NfaMTuple {
    init: TupleState,
    fin: BTreeSet<TupleState>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TupleState(Vec<State>);

impl TupleState {
    fn is_dead(&self) -> bool {
        self.0.is_empty()
    }
}

impl NfaMTuple {
    fn new(lang: &LangDfa, config_state: Vec<State>) -> Self {
        let mut init = config_state.clone();
        init.insert(0, lang.init);
        let mut fin = BTreeSet::new();

        for &f in &lang.fin {
            let mut f_vec = config_state.clone();
            f_vec.push(f);
            fin.insert(TupleState(f_vec));
        }

        NfaMTuple {
            init: TupleState(init),
            fin,
        }
    }

    fn trans(
        &self,
        term: &[PathId],
        lang: &LangDfa,
        state: &TupleState,
        letter: &PathTuple,
    ) -> TupleState {
        let TupleState(s) = state;
        let PathTuple(l) = letter;

        let mut new_state = vec![TRAP; term.len()];

        for (i, &PathId(dim)) in term.iter().enumerate() {
            match l[dim] {
                PathSymbol::OutWord(v) => {
                    let mut state = s[i];

                    for &OutputLetter(c) in v {
                        let trans_on = TransOn {
                            state,
                            letter: Letter(c),
                        };

                        let Some(&s) = lang.trans.get(&trans_on) else {
                            state = TRAP;
                            break;
                        };
                        state = s;
                    }

                    new_state[i] = state;
                }
                _ => new_state[i] = s[i],
            }
        }

        TupleState(new_state)
    }
}

#[derive(Clone, Default)]
struct MTupleUnion {
    m_tuples: Vec<NfaMTuple>,
    term: Vec<PathId>,
    lang: LangDfa,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct MTupleUnionState(Vec<TupleState>);

impl MTupleUnionState {
    fn is_dead(&self) -> bool {
        self.0.iter().all(|s| s.is_dead())
    }
}

impl MTupleUnion {
    fn new(term: Vec<PathId>, lang: LangDfa, config_states: Vec<Vec<State>>) -> Self {
        let mut m_tuples = Vec::new();

        if config_states.is_empty() {
            let m_tuple = NfaMTuple::new(&lang, vec![]);
            return MTupleUnion {
                m_tuples: vec![m_tuple],
                term,
                lang,
            };
        }

        for config_state in config_states {
            m_tuples.push(NfaMTuple::new(&lang, config_state));
        }

        MTupleUnion {
            m_tuples,
            term,
            lang,
        }
    }

    fn trans(&self, states: &MTupleUnionState, letter: &PathTuple) -> MTupleUnionState {
        let MTupleUnionState(states) = states;
        let mut new_states = Vec::new();

        for (m_tuple, state) in self.m_tuples.iter().zip(states) {
            new_states.push(m_tuple.trans(&self.term, &self.lang, state, letter));
        }

        MTupleUnionState(new_states)
    }
}

/// `MTupleAutomata` is a container for multiple `NfaMTuple`.
#[derive(Clone, Default)]
pub struct MTupleUnionAutomata {
    m_union_tuples: Vec<MTupleUnion>,
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct MTupleUnionAutomataState(Vec<MTupleUnionState>);

impl MTupleUnionAutomataState {
    pub fn is_dead(&self) -> bool {
        self.0.iter().any(|s| s.is_dead())
    }
}

impl MTupleUnionAutomata {
    pub fn new() -> Self {
        MTupleUnionAutomata::default()
    }

    /// Get the initial states for these `MTupleUnionAutomata`.
    pub fn inits(&self) -> MTupleUnionAutomataState {
        let mut inits = Vec::new();

        for m_union_tuple in &self.m_union_tuples {
            let x: Vec<_> = m_union_tuple
                .m_tuples
                .iter()
                .map(|m_tuple| m_tuple.init.clone())
                .collect();

            inits.push(MTupleUnionState(x));
        }

        MTupleUnionAutomataState(inits)
    }

    /// Run these `MTupleUnionAutomata` on the `state` and `letter`, returning the states.
    pub fn trans(
        &self,
        MTupleUnionAutomataState(state): &MTupleUnionAutomataState,
        letter: &PathTuple,
    ) -> MTupleUnionAutomataState {
        let mut states = Vec::new();

        for (state, automaton) in state.iter().zip(&self.m_union_tuples) {
            let to = automaton.trans(state, letter);
            states.push(to);
        }

        MTupleUnionAutomataState(states)
    }

    /// Check whether these `MTupleAutomata` are in a final state.
    pub fn is_final(&self, MTupleUnionAutomataState(state): &MTupleUnionAutomataState) -> bool {
        for (m_tuple_union, tuple_union_state) in self.m_union_tuples.iter().zip(state) {
            let MTupleUnionState(tuple_union_state) = tuple_union_state;
            let mut any_fin = false;

            for (m_tuple, tuple_state) in m_tuple_union.m_tuples.iter().zip(tuple_union_state) {
                any_fin |= m_tuple.fin.contains(tuple_state);
            }

            if !any_fin {
                return false;
            }
        }

        true
    }
}

impl From<Vec<MTupleUnion>> for MTupleUnionAutomata {
    fn from(value: Vec<MTupleUnion>) -> Self {
        MTupleUnionAutomata {
            m_union_tuples: value,
        }
    }
}

/// `NpaM` represents the Parikh automaton encoding a single PL_SUM literal.
struct NpaM {
    init: State,
    pred: CountPredicate,
    i: Vec<PathId>,
    j: Vec<PathId>,
}

/// A state of a single `NpaM`.
#[derive(Eq, Hash, PartialEq, Ord, PartialOrd, Copy, Clone, Debug)]
pub struct ParikhState {
    pub state: State,
    counter: (i32, i32),
}

enum CountPredicate {
    NotEq,
}

impl NpaM {
    /// Construct an `NpaM` for the "count is not equal to" predicate.
    fn count_neq(i: Vec<PathId>, j: Vec<PathId>) -> NpaM {
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
        let mut counter = state.counter;

        for &PathId(dim) in &self.i {
            if let PathSymbol::OutNum(OutputNumber(n)) = l[dim] {
                counter.0 += n;
            }
        }
        for &PathId(dim) in &self.j {
            if let PathSymbol::OutNum(OutputNumber(n)) = l[dim] {
                counter.1 += n;
            }
        }

        vec![ParikhState {
            state: INIT,
            counter,
        }]
    }

    fn count_not_eq_accepts(&self, state: ParikhState) -> bool {
        state.counter.0 != state.counter.1
    }
}

/// `ParikhAutomata` is a container for multiple `NpaM`.
#[derive(Default)]
pub struct ParikhAutomata {
    pas: Vec<NpaM>,
}

/// `ParikhAutomataState` is the state representation of `ParikhAutomata`.
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct ParikhAutomataState(Vec<BTreeSet<ParikhState>>);

impl ParikhAutomataState {
    pub fn is_dead(&self) -> bool {
        self.0.iter().any(|x| x.is_empty() && !self.0.is_empty())
    }
}

/// `ParikhAutomataStateNoOutputs` is the state representation of `ParikhAutomata` without the counters.
#[derive(Eq, Hash, PartialEq, Clone, Debug)]
pub struct ParikhAutomataStateNoOutputs(Vec<BTreeSet<State>>);

impl ParikhAutomataStateNoOutputs {
    pub fn is_dead(&self) -> bool {
        self.0.iter().any(|x| x.is_empty() && !self.0.is_empty())
    }
}

impl From<ParikhAutomataState> for ParikhAutomataStateNoOutputs {
    fn from(value: ParikhAutomataState) -> Self {
        ParikhAutomataStateNoOutputs(
            value
                .0
                .iter()
                .map(|x| x.iter().map(|y| y.state).collect())
                .collect(),
        )
    }
}

impl ParikhAutomata {
    pub fn new() -> Self {
        ParikhAutomata::default()
    }

    /// Get the initial states for these `ParikhAutomata`.
    pub fn inits(&self) -> ParikhAutomataState {
        let inits_pa: Vec<State> = self.pas.iter().map(|x| x.init).collect();

        ParikhAutomataState(
            inits_pa
                .iter()
                .map(|&s| {
                    BTreeSet::from([ParikhState {
                        state: s,
                        counter: (0, 0),
                    }])
                })
                .collect(),
        )
    }

    /// Run these `ParikhAutomata` on the `state` and `letter`, returning the new states.
    pub fn trans(
        &self,
        ParikhAutomataState(state): &ParikhAutomataState,
        letter: &PathTuple,
    ) -> ParikhAutomataState {
        let mut states = Vec::new();

        for (state, automaton) in state.iter().zip(&self.pas) {
            let mut to: BTreeSet<ParikhState> = BTreeSet::new();

            for &s in state {
                let x = automaton.trans(s, letter);
                to.extend(x);
            }
            states.push(to);
        }

        ParikhAutomataState(states)
    }

    /// Check whether these `ParikhAutomata` are in an accepting configuration.
    pub fn accepts(&self, ParikhAutomataState(state): &ParikhAutomataState) -> bool {
        self.pas
            .iter()
            .zip(state)
            .all(|(pa, states)| states.iter().any(|s| pa.accepts(*s)))
    }

    /// Run these `ParikhAutomata` on the `state` and `letter`, returning the new states without the outputs.
    pub fn trans_no_output(
        &self,
        ParikhAutomataStateNoOutputs(state): &ParikhAutomataStateNoOutputs,
        letter: &PathTuple,
    ) -> ParikhAutomataStateNoOutputs {
        let mut states = Vec::new();

        for (state, automaton) in state.iter().zip(&self.pas) {
            let mut to: BTreeSet<State> = BTreeSet::new();

            for &s in state {
                let s = ParikhState {
                    state: s,
                    counter: (0, 0),
                };

                let x = automaton.trans(s, letter);
                to.extend(x.iter().map(|s| s.state));
            }
            states.push(to);
        }

        ParikhAutomataStateNoOutputs(states)
    }

    /// Get the number of `ParikhAutomata`.
    pub fn len(&self) -> usize {
        self.pas.len()
    }

    /// Check whether these `ParikhAutomata` are empty.
    pub fn is_empty(&self) -> bool {
        self.pas.is_empty()
    }
}

/// Take a list of literals (a single conjunction of atoms or negated atoms)
/// and return a list of NfaM and NpaM automata that correspond to these literals.
pub fn literals_to_automata<'a>(
    lits: &Vec<Literal>,
    target_nfa: &'a TargetNfa,
    reach_sets: &'a ReachSets,
    language_automata: &'a HashMap<&str, LangDfa>,
) -> Result<(MAutomata<'a>, ParikhAutomata, MTupleUnionAutomata), String> {
    let mut ms = Vec::new();
    let mut pas = Vec::new();
    let mut m_tuples = Vec::new();

    for tok in lits {
        let pred;
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

        match pred {
            &Atom::StartInit(_)
            | &Atom::StartFinal(_)
            | &Atom::StartReachInit(_)
            | &Atom::StartReachFinal(_) => {
                // Handled by restricting PathsN initial state.
                continue;
            }
            &Atom::EndInit(path_id) => {
                ms.push(NfaM::end_belongs_to(is_neg, path_id, &target_nfa.init))
            }
            &Atom::EndFinal(path_id) => {
                ms.push(NfaM::end_belongs_to(is_neg, path_id, &target_nfa.fin))
            }
            &Atom::EndReachInit(path_id) => {
                ms.push(NfaM::end_belongs_to(is_neg, path_id, &reach_sets.init))
            }
            &Atom::EndReachFinal(path_id) => {
                ms.push(NfaM::end_belongs_to(is_neg, path_id, &reach_sets.fin))
            }
            &Atom::PathEq(path_id1, path_id2) => ms.push(NfaM::path_eq(is_neg, path_id1, path_id2)),
            &Atom::InputEq(path_id1, path_id2) => {
                ms.push(NfaM::input_eq(is_neg, path_id1, path_id2))
            }
            Atom::OutputEq(path_term1, path_term2) => {
                if !is_neg {
                    return Err("no output equality allowed".to_owned());
                }

                match target_nfa.output_type {
                    OutputType::None => {
                        return Err("no output disequality for trivial monoid allowed".to_owned());
                    }
                    OutputType::Number => {
                        pas.push(NpaM::count_neq(path_term1.clone(), path_term2.clone()))
                    }
                    OutputType::Word => {
                        return Err("no output disequality for free monoid allowed".to_owned());
                    }
                }
            }
            &Atom::StartStartEq(path_id1, path_id2) => {
                ms.push(NfaM::start_start_eq(is_neg, path_id1, path_id2))
            }
            &Atom::StartEndEq(path_id1, path_id2) => {
                ms.push(NfaM::start_end_eq(is_neg, path_id1, path_id2))
            }
            &Atom::EndStartEq(path_id1, path_id2) => {
                ms.push(NfaM::end_start_eq(is_neg, path_id1, path_id2))
            }
            &Atom::EndEndEq(path_id1, path_id2) => {
                ms.push(NfaM::end_end_eq(is_neg, path_id1, path_id2))
            }
            &Atom::InputPrefix(path_id1, path_id2) => {
                ms.push(NfaM::prefix(is_neg, path_id1, path_id2))
            }
            &Atom::InputBelongs(path_id, ref lang) => {
                let dfa = language_automata
                    .get(lang.as_str())
                    .ok_or_else(|| format!("undeclared language: {lang}"))
                    .cloned()?;

                let dfa = if is_neg { dfa.complement() } else { dfa };

                ms.push(NfaM::input_lang_belong(path_id, dfa))
            }
            Atom::OutputBelongs(path_term, lang) => {
                let dfa = language_automata
                    .get(lang.as_str())
                    .ok_or_else(|| format!("undeclared language: {lang}"))
                    .cloned()?;
                let dfa = if is_neg { dfa.complement() } else { dfa };

                let m = path_term.len();
                let states = dfa.states();
                let cartesian_states = util::cartesian_power(&states, m - 1);
                let cartesian_states = cartesian_states
                    .into_iter()
                    .map(|s| s.into_iter().copied().collect())
                    .collect();

                m_tuples.push(MTupleUnion::new(
                    path_term.clone(),
                    dfa.clone(),
                    cartesian_states,
                ))
            }
            &Atom::InputLenLessOrEq(path_id1, path_id2) => {
                ms.push(NfaM::length(is_neg, path_id1, path_id2))
            }
        }
    }

    Ok((
        MAutomata { ms },
        ParikhAutomata { pas },
        MTupleUnionAutomata {
            m_union_tuples: m_tuples,
        },
    ))
}
