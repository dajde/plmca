use crate::{
    atoms::{
        MAutomata, MAutomataState, ParikhAutomata, ParikhAutomataState,
        ParikhAutomataStateNoOutputs,
    },
    paths_n::{NfaPathsN, NfaPathsNState, PathTuple},
};
use std::collections::{HashMap, HashSet};

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
struct ProductState<'a> {
    ms: MAutomataState,
    pas: ParikhAutomataState,
    paths_n: NfaPathsNState<'a>,
}

impl<'a> ProductState<'a> {
    fn new(ms: MAutomataState, pas: ParikhAutomataState, paths_n: NfaPathsNState<'a>) -> Self {
        Self { ms, pas, paths_n }
    }

    fn is_dead(&self) -> bool {
        self.ms.is_dead() || self.pas.is_dead() || self.paths_n.is_dead()
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
struct ProductStateNoOutput<'a> {
    ms: MAutomataState,
    pas: ParikhAutomataStateNoOutputs,
    paths_n: NfaPathsNState<'a>,
}

impl ProductStateNoOutput<'_> {
    fn is_dead(&self) -> bool {
        self.ms.is_dead() || self.pas.is_dead() || self.paths_n.is_dead()
    }
}

impl<'a> From<ProductState<'a>> for ProductStateNoOutput<'a> {
    fn from(value: ProductState<'a>) -> Self {
        Self {
            ms: value.ms,
            pas: value.pas.into(),
            paths_n: value.paths_n,
        }
    }
}

#[derive(Clone)]
struct ProductAutomaton<'short, 'long> {
    ms: &'short MAutomata<'long>,
    pas: &'short ParikhAutomata,
    paths_n: &'short NfaPathsN<'long>,
}

impl<'short, 'long> ProductAutomaton<'short, 'long> {
    fn new(
        ms: &'short MAutomata<'long>,
        pas: &'short ParikhAutomata,
        paths_n: &'short NfaPathsN<'long>,
    ) -> ProductAutomaton<'short, 'long> {
        Self { ms, pas, paths_n }
    }

    fn next(&'_ self, state: &ProductState, letter: &PathTuple) -> ProductState<'_> {
        let new_current_ms = self.ms.trans(&state.ms, letter);
        let new_current_pas = self.pas.trans(&state.pas, letter);
        let new_current_paths_n = self.paths_n.trans(&state.paths_n, letter);

        ProductState {
            ms: new_current_ms,
            pas: new_current_pas,
            paths_n: new_current_paths_n,
        }
    }

    fn accepts(&self, state: &ProductState) -> bool {
        let is_final_ms = self.ms.is_final(&state.ms);
        let is_final_pas = self.pas.accepts(&state.pas);
        let is_final_paths_n = state.paths_n.is_final();

        is_final_ms && is_final_pas && is_final_paths_n
    }

    fn next_no_output(
        &'_ self,
        state: &ProductStateNoOutput,
        letter: &PathTuple,
    ) -> ProductStateNoOutput<'_> {
        let new_current_ms = self.ms.trans(&state.ms, letter);
        let new_current_pas = self.pas.trans_no_output(&state.pas, letter);
        let new_current_paths_n = self.paths_n.trans(&state.paths_n, letter);

        ProductStateNoOutput {
            ms: new_current_ms,
            pas: new_current_pas,
            paths_n: new_current_paths_n,
        }
    }
}

/// Run the bounded witness search for a product automaton made of `paths_n`, `ms` and `pas`.
pub fn run(
    alphabet: &[PathTuple],
    paths_n: &NfaPathsN,
    ms: &MAutomata,
    pas: &ParikhAutomata,
) -> bool {
    let automaton = ProductAutomaton::new(ms, pas, paths_n);
    let initial_state = ProductState::new(ms.inits(), pas.inits(), paths_n.init.clone());
    let d = pas.len() * 2; // each WPA has counters of the form `c1 != c2`, i.e. 2 dimensions
    let upper_bound = upper_bound(alphabet, &automaton, &initial_state, d);

    bounded_search_witness(&automaton, &initial_state, alphabet, upper_bound)
}

fn bounded_search_witness(
    automaton: &ProductAutomaton,
    initial_state: &ProductState,
    alphabet: &[PathTuple],
    upper_bound: usize,
) -> bool {
    let mut stack = Vec::new();
    stack.push((initial_state.clone(), alphabet.iter(), 0));

    let mut visited = HashSet::new();
    while let Some((current_state, mut rest_alphabet, counter)) = stack.pop() {
        if counter > upper_bound {
            continue;
        }

        while let Some(letter) = rest_alphabet.next() {
            let new_state = automaton.next(&current_state, letter);

            if new_state.is_dead() {
                continue;
            }

            let combined = (new_state, counter);
            if visited.contains(&combined) {
                continue;
            }
            let (new_state, counter) = combined;

            visited.insert((new_state.clone(), counter));

            if automaton.accepts(&new_state) {
                return true;
            }

            let new_counter = counter + 1;

            stack.push((current_state, rest_alphabet, counter));
            stack.push((new_state, alphabet.iter(), new_counter));
            break;
        }
    }

    false
}

/// Get the upper bound for the nonemptiness check.
fn upper_bound(
    alphabet: &[PathTuple],
    automaton: &ProductAutomaton,
    initial_state: &ProductState,
    d: usize,
) -> usize {
    let initial_state = ProductStateNoOutput::from(initial_state.clone());

    let (state_table, nt) = analyze_automaton(automaton, &initial_state, alphabet);

    let (p, c) = longest_path_cycle_approx(automaton, alphabet, &initial_state, &state_table);

    (nt * (1 + p)) + (c * (d * d))
}

fn longest_path_cycle_approx(
    automaton: &ProductAutomaton,
    alphabet: &[PathTuple],
    initial_state: &ProductStateNoOutput,
    state_table: &StateTable,
) -> (usize, usize) {
    let sccs = kosaraju_sccs(automaton, state_table, alphabet);

    // Map nodes to component IDs.
    let mut node_map = vec![usize::MAX; state_table.id_to_state.len()];
    for (id, component) in sccs.iter().enumerate() {
        for &node in component {
            node_map[node] = id;
        }
    }

    // Create SCC graph. componentID -> nextComponentIDs
    let mut scc_graph: HashMap<_, HashSet<_>> = HashMap::new();
    for state_id in 0..state_table.id_to_state.len() {
        let state = &state_table.id_to_state[state_id];
        let curr_scc_id = node_map[state_id];

        for l in alphabet {
            let next = automaton.next_no_output(state, l);
            if next.is_dead() {
                continue;
            }

            let next_id = state_table.state_to_id.get(&next).copied().unwrap();

            let next_scc_id = node_map[next_id];

            if curr_scc_id != next_scc_id {
                scc_graph
                    .entry(curr_scc_id)
                    .or_default()
                    .insert(next_scc_id);
            }
        }
    }

    let n = sccs.len();
    let mut d = vec![0; n];
    let init_id = state_table.state_to_id[initial_state];
    let s = node_map[init_id];
    d[s] = sccs[s].len();

    for u in 0..n {
        if d[u] == 0 {
            continue;
        }

        let Some(neighbours) = scc_graph.get(&u) else {
            continue;
        };

        for &v in neighbours {
            let w = sccs[v].len();

            if d[u] + w > d[v] {
                d[v] = d[u] + w;
            }
        }
    }

    let longest_simple_cycle = sccs.iter().map(HashSet::len).max().unwrap();
    let longest_simple_path = *d.iter().max().unwrap();

    (longest_simple_path, longest_simple_cycle)
}

struct StateTable<'a> {
    id_to_state: Vec<ProductStateNoOutput<'a>>,
    state_to_id: HashMap<ProductStateNoOutput<'a>, usize>,
}

fn analyze_automaton<'a>(
    automaton: &'a ProductAutomaton<'_, 'a>,
    initial_state: &ProductStateNoOutput<'a>,
    alphabet: &[PathTuple],
) -> (StateTable<'a>, usize) {
    let mut id_to_state = vec![];
    let mut state_to_id = HashMap::new();

    let id = id_to_state.len();
    state_to_id.insert(initial_state.clone(), id);
    id_to_state.push(initial_state.clone());

    let mut stack = Vec::new();
    stack.push((initial_state.clone(), alphabet.iter()));

    let mut visited_trans = HashSet::new();

    while let Some((current_state, mut rest_alphabet)) = stack.pop() {
        while let Some(l) = rest_alphabet.next() {
            let new_state = automaton.next_no_output(&current_state, l);
            if new_state.is_dead() {
                continue;
            }

            visited_trans.insert((current_state.clone(), l.output(), new_state.clone()));

            if state_to_id.contains_key(&new_state) {
                continue;
            }
            let id = id_to_state.len();
            state_to_id.insert(new_state.clone(), id);
            id_to_state.push(new_state.clone());

            stack.push((current_state, rest_alphabet));
            stack.push((new_state, alphabet.iter()));
            break;
        }
    }

    (
        StateTable {
            id_to_state,
            state_to_id,
        },
        visited_trans.len(),
    )
}

// Get the strongly connected components for `automaton`.
fn kosaraju_sccs(
    automaton: &ProductAutomaton,
    state_table: &StateTable,
    alphabet: &[PathTuple],
) -> Vec<HashSet<usize>> {
    let mut stack = Vec::new();
    let mut visited = HashSet::new();
    let mut transpose_automaton = HashMap::new();

    for u in 0..state_table.id_to_state.len() {
        if visited.contains(&u) {
            continue;
        }

        kosaraju_dfs(
            u,
            state_table,
            &mut stack,
            &mut visited,
            automaton,
            &mut transpose_automaton,
            alphabet,
        );
    }

    let mut visited = HashSet::new();
    let mut components = vec![];

    for u in stack.into_iter().rev() {
        if visited.contains(&u) {
            continue;
        }

        let mut comp = HashSet::new();
        kosaraju_transpose_dfs(&transpose_automaton, u, &mut comp, &mut visited);
        components.push(comp);
    }

    components
}

// Perform DFS on the automaton, record finishing times for states in `stack`.
// Also construct `transpose_automaton` for second phase.
fn kosaraju_dfs(
    state_id: usize,
    state_table: &StateTable,
    stack: &mut Vec<usize>,
    visited: &mut HashSet<usize>,
    automaton: &ProductAutomaton,
    transpose_automaton: &mut HashMap<usize, HashSet<usize>>,
    alphabet: &[PathTuple],
) {
    if visited.contains(&state_id) {
        return;
    }
    visited.insert(state_id);

    let state = &state_table.id_to_state[state_id];

    for l in alphabet {
        let out = automaton.next_no_output(state, l);
        if out.is_dead() {
            continue;
        }

        let out_id = state_table.state_to_id.get(&out).copied().unwrap();

        transpose_automaton
            .entry(out_id)
            .or_default()
            .insert(state_id);

        kosaraju_dfs(
            out_id,
            state_table,
            stack,
            visited,
            automaton,
            transpose_automaton,
            alphabet,
        );
    }

    stack.push(state_id);
}

// Perform the DFS on the transpose automaton, assign states to component.
fn kosaraju_transpose_dfs(
    transpose_automaton: &HashMap<usize, HashSet<usize>>,
    state: usize,
    component: &mut HashSet<usize>,
    visited: &mut HashSet<usize>,
) {
    if visited.contains(&state) {
        return;
    }
    visited.insert(state);
    component.insert(state);

    for &s in transpose_automaton.get(&state).into_iter().flatten() {
        kosaraju_transpose_dfs(transpose_automaton, s, component, visited);
    }
}
