//! Evaluation of the PL with input automata, entrypoint to the program.

use std::collections::{BTreeSet, HashMap, HashSet};

use crate::atoms::{self, MAutomata, ParikhAutomata, ParikhState};
use crate::automaton::{LangDfa, Letter, OutputNumber, State, TargetNfa};
use crate::formula::simplify::NNFBooleanFormula;
use crate::paths_n::{self, NfaPathsN, PathSymbol, PathTuple, PathsAState};
use crate::util::IdMap;
use crate::{eval, formula};

fn decode_path_tuples(
    model: &Vec<&PathTuple>,
    state_to_id: &IdMap<String>,
    letter_to_id: &IdMap<String>,
    n: usize,
) -> Vec<Vec<String>> {
    let mut result_vec = Vec::new();
    for _ in 0..n {
        result_vec.push(Vec::new());
    }

    for PathTuple(path_tuple) in model {
        for (s, v) in path_tuple.iter().zip(&mut result_vec) {
            match s {
                PathSymbol::State(State(x)) => {
                    let decoded = state_to_id.object(*x);
                    v.push(
                        decoded
                            .map(|x| x.to_owned())
                            .unwrap_or("Undefined State".to_owned()),
                    );
                }
                PathSymbol::Letter(Letter(x)) => {
                    let decoded = letter_to_id.object(*x);
                    v.push(
                        decoded
                            .map(|x| x.to_owned())
                            .unwrap_or("Undefined Letter".to_owned()),
                    );
                }
                PathSymbol::OutNum(OutputNumber(x)) => {
                    v.push(x.to_string());
                }
                PathSymbol::Bottom => {
                    v.push("⊥".to_owned());
                }
            }
        }
    }

    result_vec
}

/// Run the model-checking program with the PL formmula in `fml_str` and the target NFA in `fa_str`.
///
/// The FA defining languages for the language inclusion predicate are in `lang_automata_str`, which is
/// a map of the variable name to the finite automaton string.
pub fn run(
    fml_str: String,
    fa_str: String,
    lang_automata_str: Vec<(String, String)>,
) -> Result<String, Box<dyn std::error::Error>> {
    let target_nfa = TargetNfa::parse(fa_str.as_str());

    let reach_init = target_nfa.reach_init();
    let reach_final = target_nfa.reach_final();

    let fml = formula::parse_fml(&fml_str)?;
    let nnf_fml = NNFBooleanFormula::from(fml.constraints);
    let conjs = formula::simplify::split_ors(nnf_fml);

    let language_automata: HashMap<String, LangDfa> = {
        let mut automata = HashMap::new();

        for (name, lang_fa_str) in lang_automata_str {
            let lang_dfa = LangDfa::parse(&lang_fa_str, &target_nfa.letter_to_id);
            automata.insert(name, lang_dfa);
        }

        automata
    };

    let n = fml.declarations.len();
    let implicit_equalities = fml.declarations.implicit_equalities();

    let paths_n_alphabet = paths_n::paths_n_alphabet(&target_nfa, n);

    let nfa_paths_n = paths_n::NfaPathsN::new(&target_nfa, n);

    if conjs.is_empty() {
        let (model, sat) = eval::eval(
            &paths_n_alphabet,
            &nfa_paths_n,
            &implicit_equalities,
            &ParikhAutomata::empty(),
            0,
        );

        if sat {
            println!("satisfied");
            let result_vec =
                decode_path_tuples(&model, &target_nfa.state_to_id, &target_nfa.letter_to_id, n);
            return Ok(format!("{result_vec:?}"));
        }
    }

    for conj in conjs {
        eprintln!("evaluating conjunction {conj:?}");

        let (mut ms, pas) = atoms::literals_to_automata(
            conj,
            &fml.declarations,
            &target_nfa,
            &reach_init,
            &reach_final,
            &language_automata,
        );

        ms.extend(&implicit_equalities);

        let trans_state = TransitionCounterState {
            current_ms: ms.inits(),
            current_pas: pas.inits(),
            current_paths_n: nfa_paths_n.init.clone(),
            ms: &ms,
            pas: &pas,
            paths_n: &nfa_paths_n,
        };

        let upper_bound = if pas.is_empty() {
            0
        } else {
            let num_ts = num_trans(trans_state, &paths_n_alphabet);
            let d = pas.len() * 2;
            (2 * d * num_ts).pow(2)
        };

        dbg!(upper_bound);

        let (model, sat) = eval::eval(&paths_n_alphabet, &nfa_paths_n, &ms, &pas, upper_bound);
        if sat {
            println!("satisfied");
            let result_vec =
                decode_path_tuples(&model, &target_nfa.state_to_id, &target_nfa.letter_to_id, n);
            return Ok(format!("{result_vec:?}"));
        }
    }
    println!("not satisfied");

    Ok("".to_owned())
}

fn eval<'a>(
    alphabet: &'a [PathTuple],
    paths_n: &'a NfaPathsN,
    ms: &'a MAutomata,
    pas: &ParikhAutomata,
    upper_bound: usize,
) -> (Vec<&'a PathTuple>, bool) {
    let inits_ms = ms.inits();
    let inits_pa = pas.inits();

    let search_state_iter = SearchState {
        current_ms: inits_ms,
        current_pas: inits_pa,
        current_paths_n: paths_n.init.clone(),
        ms,
        pas,
        paths_n,
        counter: 0,
        upper_bound,
        word: Vec::new(),
    };

    eprintln!("starting non emptiness check");
    search_witness(search_state_iter, alphabet)
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
struct States {
    ms: Vec<BTreeSet<State>>,
    pas: Vec<BTreeSet<State>>,
    paths_n: Vec<BTreeSet<PathsAState>>,
}

impl States {
    fn new(
        ms: Vec<BTreeSet<State>>,
        pas: &[BTreeSet<ParikhState>],
        paths_n: Vec<BTreeSet<PathsAState>>,
    ) -> Self {
        let pas = pas
            .iter()
            .map(|x| x.iter().map(|x| x.state).collect())
            .collect();

        States { ms, pas, paths_n }
    }

    fn is_dead(&self) -> bool {
        self.ms.iter().any(|x| x.is_empty())
            || self.pas.iter().any(|x| x.is_empty())
            || self.paths_n.iter().any(|x| x.is_empty())
    }
}

#[derive(Eq, Hash, PartialEq, Clone, Debug)]
struct StatesCounter {
    ms: Vec<BTreeSet<State>>,
    pas: Vec<BTreeSet<ParikhState>>,
    paths_n: Vec<BTreeSet<PathsAState>>,
    counter: usize,
}

impl StatesCounter {
    fn is_dead(&self) -> bool {
        (self.ms.iter().any(|x| x.is_empty()) && !self.ms.is_empty())
            || self
                .pas
                .iter()
                .any(|x| x.is_empty() && !self.pas.is_empty())
            || self.paths_n.iter().any(|x| x.is_empty())
    }
}

struct SearchState<'short, 'long> {
    current_ms: Vec<BTreeSet<State>>,
    current_pas: Vec<BTreeSet<ParikhState>>,
    current_paths_n: Vec<BTreeSet<PathsAState>>,
    ms: &'short MAutomata<'long>,
    pas: &'short ParikhAutomata,
    paths_n: &'short NfaPathsN<'long>,
    counter: usize,
    upper_bound: usize,
    word: Vec<&'long PathTuple>,
}

fn search_witness<'a>(
    search_state: SearchState<'_, 'a>,
    alphabet: &'a [PathTuple],
) -> (Vec<&'a PathTuple>, bool) {
    let mut stack = Vec::new();
    stack.push((search_state, alphabet.iter()));

    let mut visited = HashSet::new();
    while let Some((search_state, mut rest_alphabet)) = stack.pop() {
        if !search_state.current_pas.is_empty() && search_state.counter > search_state.upper_bound {
            continue;
        }

        while let Some(l) = rest_alphabet.next() {
            let new_current_ms = search_state.ms.trans(&search_state.current_ms, l);
            let new_current_pas = search_state.pas.trans(&search_state.current_pas, l);
            let new_current_paths_n = search_state.paths_n.trans(&search_state.current_paths_n, l);

            let new_state = StatesCounter {
                ms: new_current_ms,
                pas: new_current_pas,
                paths_n: new_current_paths_n,
                counter: search_state.counter,
            };

            if new_state.is_dead() {
                continue;
            }

            if visited.contains(&new_state) {
                continue;
            }
            visited.insert(new_state.clone());

            let is_final_ms = search_state.ms.is_final(&new_state.ms);
            let is_final_pas = search_state.pas.is_final(&new_state.pas);
            let is_final_paths_n = new_state
                .paths_n
                .iter()
                .all(|set| set.iter().any(|state| state.accepting()));

            let new_word = if search_state.upper_bound != 0 {
                Vec::new()
            } else {
                let mut w = search_state.word.clone();
                w.push(l);
                w
            };

            if is_final_ms && is_final_pas && is_final_paths_n {
                return (new_word, true);
            }

            let new_counter = if search_state.pas.is_empty() {
                0
            } else {
                search_state.counter + 1
            };

            let next_search_state = SearchState {
                current_ms: new_state.ms,
                current_pas: new_state.pas,
                current_paths_n: new_state.paths_n,
                ms: search_state.ms,
                pas: search_state.pas,
                paths_n: search_state.paths_n,
                counter: new_counter,
                upper_bound: search_state.upper_bound,
                word: new_word,
            };

            stack.push((search_state, rest_alphabet));
            stack.push((next_search_state, alphabet.iter()));
            break;
        }
    }

    (Vec::new(), false)
}

struct TransitionCounterState<'short, 'long> {
    current_ms: Vec<BTreeSet<State>>,
    current_pas: Vec<BTreeSet<ParikhState>>,
    current_paths_n: Vec<BTreeSet<PathsAState>>,
    ms: &'short MAutomata<'long>,
    pas: &'short ParikhAutomata,
    paths_n: &'short NfaPathsN<'long>,
}

fn num_trans(search_state: TransitionCounterState, alphabet: &[PathTuple]) -> usize {
    let mut stack = Vec::new();
    stack.push(search_state);

    let mut visited_state = HashSet::new();
    let mut visited_trans = HashSet::new();

    while let Some(search_state) = stack.pop() {
        let old_state = States::new(
            search_state.current_ms,
            &search_state.current_pas,
            search_state.current_paths_n,
        );

        if visited_state.contains(&old_state) {
            continue;
        }
        visited_state.insert(old_state.clone());

        for l in alphabet {
            let new_current_ms = search_state.ms.trans(&old_state.ms, l);
            let new_current_pas = search_state.pas.trans(&search_state.current_pas, l);
            let new_current_paths_n = search_state.paths_n.trans(&old_state.paths_n, l);

            let new_state = States::new(new_current_ms, &new_current_pas, new_current_paths_n);

            if new_state.is_dead() {
                continue;
            }

            let old_state = (
                old_state.ms.clone(),
                search_state.current_pas.clone(),
                old_state.paths_n.clone(),
            );

            visited_trans.insert((old_state, l.output(), new_state.clone()));

            let next_search_state = TransitionCounterState {
                current_ms: new_state.ms,
                current_pas: new_current_pas,
                current_paths_n: new_state.paths_n,
                ms: search_state.ms,
                pas: search_state.pas,
                paths_n: search_state.paths_n,
            };

            stack.push(next_search_state);
        }
    }

    visited_trans.len()
}
