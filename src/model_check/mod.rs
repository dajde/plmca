//! Model-checking of the PL formula with input automata, entrypoint to the program.

mod bounded_search_witness;
mod search_witness;

use crate::atoms::{MAutomata, MTupleUnionAutomata, ParikhAutomata};
use crate::automaton::{LangDfa, Letter, State, TargetNfa};
use crate::formula::simplify::NNFBooleanFormula;
use crate::formula::{self, Declarations, ForallStates, PathId, Vars};
use crate::paths_n::{self, NfaPathsN, PathSymbol, PathTuple, StartStateProp};
use crate::util::IdMap;
use crate::{atoms, util};
use std::collections::HashMap;

fn decode_path_tuples(
    model: &Vec<&PathTuple>,
    state_to_id: &IdMap<String, usize>,
    letter_to_id: &IdMap<String, usize>,
    vars_mapping: &Vars,
    n: usize,
) -> Vec<Vec<String>> {
    let mut result_vec = Vec::new();
    for i in 0..n {
        result_vec.push(Vec::from([vars_mapping.get_path_name(&PathId(i))]));
    }

    for PathTuple(path_tuple) in model {
        for (s, v) in path_tuple.iter().zip(&mut result_vec) {
            match s {
                PathSymbol::State(State(x)) => {
                    let decoded = state_to_id.object(*x).unwrap().to_owned();
                    v.push(decoded);
                }
                PathSymbol::Letter(Letter(x)) => {
                    let decoded = letter_to_id.object(*x).unwrap().to_owned();
                    v.push(decoded);
                }
                PathSymbol::Bottom => {
                    v.push("⊥".to_owned());
                }
                _ => {}
            }
        }
    }

    result_vec
}

fn decode_state_tuple(
    concrete_states: &Vec<&State>,
    state_to_id: &IdMap<String, usize>,
    ForallStates(forall_states): &ForallStates,
    vars_mapping: &Vars,
) -> Vec<Vec<String>> {
    let mut result_vec = Vec::new();

    for (state_var_id, State(state)) in forall_states.iter().zip(concrete_states) {
        let decoded_state_var = vars_mapping.get_state_name(state_var_id);
        let decoded_concrete_state = state_to_id.object(*state).unwrap().to_owned();
        result_vec.push(vec![decoded_state_var, decoded_concrete_state]);
    }

    result_vec
}

/// Run the model-checking program with the PL formula in `fml_str` and the target NFA in `fa_str`.
///
/// The FA defining languages for the language inclusion predicate are in `lang_automata_str`, which is
/// a map of the variable name to the finite automaton string.
pub fn run(
    fml_str: &str,
    fa_str: &str,
    lang_automata_str: &[(&str, &str)],
) -> Result<(bool, Vec<Vec<String>>), String> {
    let target_nfa = TargetNfa::parse(fa_str)?;

    let reach_sets = target_nfa.reach_sets();

    let fml = formula::parse_fml(fml_str)?;
    let nnf_fml = NNFBooleanFormula::from(fml.constraints);
    let conjs = formula::simplify::decompose_into_conjunctions(nnf_fml);

    let language_automata: HashMap<&str, LangDfa> = {
        let mut automata = HashMap::new();

        for &(name, lang_fa_str) in lang_automata_str {
            let lang_dfa = LangDfa::parse(lang_fa_str, &target_nfa.letter_to_id)
                .map_err(|e| format!("error in {name} language automaton: {e}"))?;
            automata.insert(name, lang_dfa);
        }

        automata
    };

    let implicit_equalities = fml.declarations.implicit_equalities();

    let constraints = {
        let mut cs = Vec::new();

        for conj in &conjs {
            let restrictions = fml.declarations.start_state_restrictions(conj);

            let (mut ms, pas, m_tuples) =
                atoms::literals_to_automata(conj, &target_nfa, &reach_sets, &language_automata)?;
            ms.extend(&implicit_equalities);

            cs.push((ms, pas, m_tuples, restrictions));
        }

        cs
    };

    let is_universally_quantified = fml.forall_states.num_vars() > 0;

    if is_universally_quantified {
        model_check_universal(
            &fml.declarations,
            &fml.forall_states,
            &target_nfa,
            constraints,
            &fml.vars_mapping,
        )
    } else {
        model_check_existential(
            &fml.declarations,
            &target_nfa,
            constraints,
            &fml.vars_mapping,
        )
    }
}

fn model_check_existential(
    declarations: &Declarations,
    target_nfa: &TargetNfa,
    constraints: Vec<(
        MAutomata,
        ParikhAutomata,
        MTupleUnionAutomata,
        Vec<Vec<StartStateProp>>,
    )>,
    vars_mapping: &Vars,
) -> Result<(bool, Vec<Vec<String>>), String> {
    if constraints.is_empty() {
        return Err(
            "an existentially quantified formula with no constraints is meaningless".into(),
        );
    }

    let n = declarations.len();

    let paths_n_alphabet = paths_n::paths_n_alphabet(target_nfa, n);

    for (ms, pas, m_tuples, restrictions) in constraints {
        let nfa_paths_n = NfaPathsN::new(target_nfa, n, restrictions);

        let (satisfied, model) = model_check(
            target_nfa,
            &paths_n_alphabet,
            &nfa_paths_n,
            &ms,
            &pas,
            &m_tuples,
            vars_mapping,
            n,
        );

        if satisfied {
            return Ok((satisfied, model));
        }
    }

    Ok((false, Vec::new()))
}

fn model_check_universal(
    declarations: &Declarations,
    forall_states: &ForallStates,
    target_nfa: &TargetNfa,
    constraints: Vec<(
        MAutomata,
        ParikhAutomata,
        MTupleUnionAutomata,
        Vec<Vec<StartStateProp>>,
    )>,
    vars_mapping: &Vars,
) -> Result<(bool, Vec<Vec<String>>), String> {
    let n = declarations.len();

    let paths_n_alphabet = paths_n::paths_n_alphabet(target_nfa, n);

    let states = target_nfa.states();
    let state_combinations = util::cartesian_power(&states, forall_states.num_vars());

    // If the formula is universally quantified forall q1 ... forall qm,
    // it has to hold for all combinations of states q1 ... qm.
    'combinations: for state_combination in &state_combinations {
        let (uq_restrictions, uq_ms) =
            forall_states.universally_quantified_constraints(declarations, state_combination);

        // Special case: no boolean formula given, we only have forall q_1 ... q_n exists pi_1 ... pi_m
        if constraints.is_empty() {
            let nfa_paths_n = NfaPathsN::new(target_nfa, n, uq_restrictions);

            let (satisfied, _) = model_check(
                target_nfa,
                &paths_n_alphabet,
                &nfa_paths_n,
                &uq_ms,
                &ParikhAutomata::new(),
                &MTupleUnionAutomata::new(),
                vars_mapping,
                n,
            );

            if satisfied {
                continue 'combinations;
            }
        } else {
            for (ms, pas, m_tuples, restrictions) in &constraints {
                let mut restrictions = restrictions.clone();

                for (r, uq_r) in restrictions.iter_mut().zip(&uq_restrictions) {
                    r.extend(uq_r);
                }

                let mut ms = ms.clone();
                ms.extend(&uq_ms);

                let nfa_paths_n = NfaPathsN::new(target_nfa, n, restrictions);

                let (satisfied, _) = model_check(
                    target_nfa,
                    &paths_n_alphabet,
                    &nfa_paths_n,
                    &ms,
                    pas,
                    m_tuples,
                    vars_mapping,
                    n,
                );

                if satisfied {
                    continue 'combinations;
                }
            }
        }

        // We cannot satisfy the formula for this state combination.
        let decoded_states = decode_state_tuple(
            state_combination,
            &target_nfa.state_to_id,
            forall_states,
            vars_mapping,
        );
        return Ok((false, decoded_states));
    }

    // The formula can be satisfied for every state combination.
    Ok((true, Vec::new()))
}

fn model_check(
    target_nfa: &TargetNfa,
    alphabet: &Vec<PathTuple>,
    paths_n: &NfaPathsN,
    ms: &MAutomata,
    pas: &ParikhAutomata,
    m_tuples: &MTupleUnionAutomata,
    vars_mapping: &Vars,
    n: usize,
) -> (bool, Vec<Vec<String>>) {
    let has_wpa = !pas.is_empty();

    if has_wpa {
        let satisfied = bounded_search_witness::run(alphabet, paths_n, ms, pas);

        if satisfied {
            return (satisfied, Vec::new());
        }
    } else {
        let model = search_witness::run(alphabet, paths_n, ms, m_tuples);
        let satisfied = !model.is_empty();

        if satisfied {
            let decoded_letters = decode_path_tuples(
                &model,
                &target_nfa.state_to_id,
                &target_nfa.letter_to_id,
                vars_mapping,
                n,
            );

            return (satisfied, decoded_letters);
        }
    }

    (false, Vec::new())
}
