use crate::{
    atoms::{MAutomata, MAutomataState, MTupleUnionAutomata, MTupleUnionAutomataState},
    paths_n::{NfaPathsN, NfaPathsNState, PathTuple},
};
use std::collections::HashSet;

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
struct ProductState<'a> {
    ms: MAutomataState,
    m_tuples: MTupleUnionAutomataState,
    paths_n: NfaPathsNState<'a>,
}

impl<'a> ProductState<'a> {
    fn new(
        ms: MAutomataState,
        m_tuples: MTupleUnionAutomataState,
        paths_n: NfaPathsNState<'a>,
    ) -> Self {
        Self {
            ms,
            m_tuples,
            paths_n,
        }
    }

    fn is_dead(&self) -> bool {
        self.ms.is_dead() || self.m_tuples.is_dead() || self.paths_n.is_dead()
    }
}

struct ProductAutomaton<'short, 'long> {
    ms: &'short MAutomata<'long>,
    m_tuples: &'short MTupleUnionAutomata,
    paths_n: &'short NfaPathsN<'long>,
}

impl<'short, 'long> ProductAutomaton<'short, 'long> {
    fn new(
        ms: &'short MAutomata<'long>,
        m_tuples: &'short MTupleUnionAutomata,
        paths_n: &'short NfaPathsN<'long>,
    ) -> ProductAutomaton<'short, 'long> {
        ProductAutomaton {
            ms,
            m_tuples,
            paths_n,
        }
    }

    fn next(&'_ self, state: &ProductState, letter: &PathTuple) -> ProductState<'_> {
        let new_current_ms = self.ms.trans(&state.ms, letter);
        let new_current_m_tuples = self.m_tuples.trans(&state.m_tuples, letter);
        let new_current_paths_n = self.paths_n.trans(&state.paths_n, letter);

        ProductState {
            ms: new_current_ms,
            m_tuples: new_current_m_tuples,
            paths_n: new_current_paths_n,
        }
    }

    fn is_final(&self, state: &ProductState) -> bool {
        let is_final_ms = self.ms.is_final(&state.ms);
        let is_final_m_tuples = self.m_tuples.is_final(&state.m_tuples);
        let is_final_paths_n = state.paths_n.is_final();

        is_final_ms && is_final_m_tuples && is_final_paths_n
    }
}

/// Run the witness search for a product automaton made of `paths_n` and `ms`.
pub fn run<'a>(
    alphabet: &'a [PathTuple],
    paths_n: &NfaPathsN,
    ms: &MAutomata,
    m_tuples: &MTupleUnionAutomata,
) -> Vec<&'a PathTuple<'a>> {
    let automaton = ProductAutomaton::new(ms, m_tuples, paths_n);
    let initial_state = ProductState::new(ms.inits(), m_tuples.inits(), paths_n.init.clone());

    search_witness(automaton, initial_state, alphabet)
}

fn search_witness<'a>(
    automaton: ProductAutomaton,
    initial_state: ProductState,
    alphabet: &'a [PathTuple],
) -> Vec<&'a PathTuple<'a>> {
    let mut stack = Vec::new();
    stack.push((initial_state, alphabet.iter(), Vec::new()));

    let mut visited = HashSet::new();
    while let Some((current_state, mut rest_alphabet, word)) = stack.pop() {
        while let Some(l) = rest_alphabet.next() {
            let new_state = automaton.next(&current_state, l);

            if new_state.is_dead() || visited.contains(&new_state) {
                continue;
            }
            visited.insert(new_state.clone());

            let mut new_word = word.clone();
            new_word.push(l);

            if automaton.is_final(&new_state) {
                return new_word;
            }

            stack.push((current_state, rest_alphabet, word));
            stack.push((new_state, alphabet.iter(), new_word));
            break;
        }
    }

    Vec::new()
}
