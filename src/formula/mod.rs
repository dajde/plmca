//! PL formula definitions.

use crate::{
    atoms::{MAutomata, NfaM},
    automaton::State,
    formula::simplify::Literal,
    paths_n::StartStateProp,
    util::{self, IdMap, parse::RawToken},
};
use std::{collections::HashMap, iter::Peekable};

pub mod simplify;

/// Whole PL formula.
pub struct PatternFormula {
    pub forall_states: ForallStates,
    pub declarations: Declarations,
    pub constraints: BooleanFormula,
    pub vars_mapping: Vars,
}

macro_rules! derive_from {
    ($name:ident) => {
        impl From<usize> for $name {
            fn from(v: usize) -> Self {
                Self(v)
            }
        }
    };
}

#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug, Default)]
pub struct PathId(pub usize);
derive_from!(PathId);

#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug, Default)]
pub struct StateId(pub usize);
derive_from!(StateId);

#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug, Default)]
pub struct InputId(usize);
derive_from!(InputId);

#[derive(Eq, Hash, PartialEq, Clone, Copy, Ord, PartialOrd, Debug, Default)]
pub struct OutputId(usize);
derive_from!(OutputId);

struct Path {
    id: PathId,
    start_id: StateId,
    end_id: StateId,
    input_id: InputId,
    output_id: Option<OutputId>,
}

/// Path declarations in the PL formula.
pub struct Declarations {
    declarations: Vec<Path>,
}

impl Declarations {
    /// Get the id of the path by the start state id.
    pub fn path_id_by_start_state(&self, id: StateId) -> Option<PathId> {
        self.declarations
            .iter()
            .find(|x| x.start_id == id)
            .map(|x| x.id)
    }

    /// Get the id of the path by the end state id.
    pub fn path_id_by_end_state(&self, id: StateId) -> Option<PathId> {
        self.declarations
            .iter()
            .find(|x| x.end_id == id)
            .map(|x| x.id)
    }

    /// Get the id of the path by the input id.
    pub fn path_id_by_input_var(&self, id: InputId) -> PathId {
        self.declarations
            .iter()
            .find(|x| x.input_id == id)
            .expect("unknown input word variable")
            .id
    }
    /// Get the id of the path by the output id.
    pub fn path_id_by_output_var(&self, id: OutputId) -> PathId {
        self.declarations
            .iter()
            .find(|x| x.output_id == Some(id))
            .expect("unknown output word variable")
            .id
    }

    /// Get the number of path declarations.
    pub fn len(&self) -> usize {
        self.declarations.len()
    }

    /// Get the implicit equalities from the path declarations.
    pub fn implicit_equalities(&self) -> MAutomata<'_> {
        let declarations = &self.declarations;

        let mut equivalences_inputs: HashMap<InputId, Vec<PathId>> = HashMap::new();

        #[derive(Clone, Copy)]
        enum StateType {
            Start(PathId),
            End(PathId),
        }

        let mut equivalences_states: HashMap<StateId, Vec<StateType>> = HashMap::new();

        for decl in declarations {
            equivalences_inputs
                .entry(decl.input_id)
                .or_default()
                .push(decl.id);

            equivalences_states
                .entry(decl.start_id)
                .or_default()
                .push(StateType::Start(decl.id));

            equivalences_states
                .entry(decl.end_id)
                .or_default()
                .push(StateType::End(decl.id));
        }

        let mut ms = Vec::new();
        for eq_class in equivalences_inputs.values() {
            for (i, &path_id) in eq_class.iter().enumerate() {
                let Some(&next_path_id) = eq_class.get(i + 1) else {
                    break;
                };

                let m = NfaM::input_eq(false, path_id, next_path_id);
                ms.push(m);
            }
        }

        for eq_class in equivalences_states.values() {
            for (i, &path) in eq_class.iter().enumerate() {
                let Some(&next_path) = eq_class.get(i + 1) else {
                    break;
                };

                let m = match (path, next_path) {
                    (StateType::Start(i), StateType::Start(j)) => NfaM::start_start_eq(false, i, j),
                    (StateType::Start(i), StateType::End(j)) => NfaM::start_end_eq(false, i, j),
                    (StateType::End(i), StateType::Start(j)) => NfaM::end_start_eq(false, i, j),
                    (StateType::End(i), StateType::End(j)) => NfaM::end_end_eq(false, i, j),
                };

                ms.push(m);
            }
        }

        ms.into()
    }

    pub fn start_state_restrictions(&self, conjunction: &Vec<Literal>) -> Vec<Vec<StartStateProp>> {
        let mut restrictions = Vec::new();

        for declaration in &self.declarations {
            let mut prop_set = Vec::new();

            let path_id = declaration.id;

            for literal in conjunction {
                match literal {
                    Literal::Predicate(Atom::StartInit(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::Init)
                    }
                    Literal::Predicate(Atom::StartFinal(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::Final)
                    }
                    Literal::Predicate(Atom::StartReachInit(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::ReachInit)
                    }
                    Literal::Predicate(Atom::StartReachFinal(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::ReachFinal);
                    }
                    Literal::NotPredicate(Atom::StartInit(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::NotInit);
                    }
                    Literal::NotPredicate(Atom::StartFinal(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::NotFinal);
                    }
                    Literal::NotPredicate(Atom::StartReachInit(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::NotReachInit)
                    }
                    Literal::NotPredicate(Atom::StartReachFinal(id)) if *id == path_id => {
                        prop_set.push(StartStateProp::NotReachFinal);
                    }
                    _ => {}
                }
            }

            restrictions.push(prop_set);
        }

        restrictions
    }
}

pub struct ForallStates(pub Vec<StateId>);

impl ForallStates {
    pub fn num_vars(&self) -> usize {
        self.0.len()
    }

    pub fn universally_quantified_constraints<'a>(
        &self,
        Declarations { declarations }: &Declarations,
        state_combination: &Vec<&State>,
    ) -> (Vec<Vec<StartStateProp>>, MAutomata<'a>) {
        let n = declarations.len();

        let mut uq_restrictions = vec![vec![]; n];
        let mut uq_ms = MAutomata::new();

        let zipped = self.0.iter().zip(state_combination);

        for (&universally_quantified_state, &&state) in zipped {
            for (i, path) in declarations.iter().enumerate() {
                if path.start_id == universally_quantified_state {
                    uq_restrictions[i].push(StartStateProp::EqualTo(state));
                }
                if path.end_id == universally_quantified_state {
                    uq_ms.push(NfaM::end_equal_to(path.id, state));
                }
            }
        }

        (uq_restrictions, uq_ms)
    }
}

/// Parsed boolean logic formula tree.
pub enum BooleanFormula {
    Atom(Atom),
    BinOp(BinOp, Box<BooleanFormula>, Box<BooleanFormula>),
    Neg(Box<BooleanFormula>),
    Empty,
}

/// Atomic formulas (predicates), the leaves of the boolean logic formula.
#[derive(Debug, Clone)]
pub enum Atom {
    StartInit(PathId),
    StartFinal(PathId),
    EndInit(PathId),
    EndFinal(PathId),

    StartReachInit(PathId),
    StartReachFinal(PathId),
    EndReachInit(PathId),
    EndReachFinal(PathId),

    PathEq(PathId, PathId),
    InputEq(PathId, PathId),
    OutputEq(Vec<PathId>, Vec<PathId>),
    StartStartEq(PathId, PathId),
    StartEndEq(PathId, PathId),
    EndStartEq(PathId, PathId),
    EndEndEq(PathId, PathId),

    InputPrefix(PathId, PathId),

    InputBelongs(PathId, String),
    OutputBelongs(Vec<PathId>, String),

    InputLenLessOrEq(PathId, PathId),
}

/// Binary operators.
pub enum BinOp {
    And,
    Or,
}

impl From<FormulaToken> for Option<BinOp> {
    fn from(token: FormulaToken) -> Self {
        match token {
            FormulaToken::And => Some(BinOp::And),
            FormulaToken::Or => Some(BinOp::Or),
            _ => None,
        }
    }
}

/// Variable types in a path declaration.
#[derive(Copy, Clone, Debug)]
pub enum Var {
    Path(PathId),
    State(StateId),
    Input(InputId),
    Output(OutputId),
}

#[derive(Default)]
pub struct Vars {
    path: IdMap<String, PathId>,
    state: IdMap<String, StateId>,
    input: IdMap<String, InputId>,
    output: IdMap<String, OutputId>,
}

impl Vars {
    fn new() -> Self {
        Self::default()
    }

    fn get_var(&self, name: &String) -> Option<Var> {
        if let Some(x) = self.state.id(name) {
            return Some(Var::State(x));
        }
        if let Some(x) = self.path.id(name) {
            return Some(Var::Path(x));
        }
        if let Some(x) = self.input.id(name) {
            return Some(Var::Input(x));
        }
        if let Some(x) = self.output.id(name) {
            return Some(Var::Output(x));
        }

        None
    }

    pub fn get_path_name(&self, path_id: &PathId) -> String {
        self.path
            .object(*path_id)
            .expect("invalid path_id")
            .to_owned()
    }

    pub fn get_state_name(&self, state_id: &StateId) -> String {
        self.state
            .object(*state_id)
            .expect("invalid state_id")
            .to_owned()
    }
}

#[derive(Clone, Debug)]
enum FormulaToken {
    // Connectives.
    And,    // /\, priority 3
    Or,     // \/, priority 2
    Neg,    // !, priority 4
    LParen, // (, priority 0
    RParen, // ), priority 1

    Atom(Atom),
}

impl FormulaToken {
    fn is_connective_or_paren(&self) -> bool {
        matches!(
            self,
            FormulaToken::And
                | FormulaToken::Or
                | FormulaToken::Neg
                | FormulaToken::LParen
                | FormulaToken::RParen
        )
    }

    fn priority(&self) -> usize {
        match self {
            FormulaToken::And => 3,
            FormulaToken::Or => 2,
            FormulaToken::Neg => 4,
            FormulaToken::LParen => 0,
            FormulaToken::RParen => 1,
            _ => usize::MAX,
        }
    }
}

/// Parse the input string into a PL formula.
pub fn parse_fml(input: &str) -> Result<PatternFormula, String> {
    let mut declarations = Vec::new();
    let mut vars = Vars::new();
    let mut tokens = util::parse::tokens(input)?.into_iter().peekable();

    let mut forall_states = Vec::new();

    while let Some(tok) = tokens.peek()
        && RawToken::Forall == *tok
    {
        tokens.next();

        let Some(RawToken::Name(state_name)) = tokens.next() else {
            return Err("expected a universally quantified state".to_owned());
        };

        forall_states.push(state_name);
    }

    let path_no_outputs: Vec<(RawToken, &str)> = vec![
        (RawToken::Name(String::new()), "path identifier"),
        (RawToken::Colon, "colon `:`"),
        (RawToken::Name(String::new()), "start state identifier"),
        (RawToken::DoubleMinus, "double minus `--`"),
        (RawToken::Name(String::new()), "input word identifier"),
        (RawToken::Arrow, "arrow `->`"),
        (RawToken::Name(String::new()), "end state identifier"),
    ];

    let path_outputs: Vec<(RawToken, &str)> = vec![
        (RawToken::Name(String::new()), "path identifier"),
        (RawToken::Colon, "colon `:`"),
        (RawToken::Name(String::new()), "start state identifier"),
        (RawToken::DoubleMinus, "double minus `--`"),
        (RawToken::Name(String::new()), "input word identifier"),
        (RawToken::Comma, "comma `,`"),
        (RawToken::Name(String::new()), "output word identifier"),
        (RawToken::Arrow, "arrow `->`"),
        (RawToken::Name(String::new()), "end state identifier"),
    ];

    while let Some(tok) = tokens.peek()
        && RawToken::Exists == *tok
    {
        tokens.next();

        let formats = vec![&path_no_outputs[..], &path_outputs[..]];
        let idents = util::parse::parse_line(&mut tokens, &formats)?;

        let path = match idents.as_slice() {
            [path, start, input, end] => {
                if vars.path.contains(path) {
                    return Err("no implicit path equality allowed".to_owned());
                }

                Path {
                    id: vars.path.insert(path.to_owned()),
                    start_id: vars.state.insert(start.to_owned()),
                    end_id: vars.state.insert(end.to_owned()),
                    input_id: vars.input.insert(input.to_owned()),
                    output_id: None,
                }
            }
            [path, start, input, output, end] => {
                if vars.path.contains(path) {
                    return Err("no implicit path equality allowed".to_owned());
                }
                if vars.output.contains(output) {
                    return Err("no implicit output equality allowed".to_owned());
                }

                Path {
                    id: vars.path.insert(path.to_owned()),
                    start_id: vars.state.insert(start.to_owned()),
                    end_id: vars.state.insert(end.to_owned()),
                    input_id: vars.input.insert(input.to_owned()),
                    output_id: Some(vars.output.insert(output.to_owned())),
                }
            }
            _ => return Err("invalid line format".to_owned()),
        };

        declarations.push(path);

        // Eat comma
        tokens.next();
    }

    if declarations.is_empty() {
        return Err("expected atleast 1 existentially quantified path declaration".to_owned());
    }

    let declarations = Declarations { declarations };

    let mut forall_state_ids = Vec::new();

    for name in forall_states {
        let Some(state_id) = vars.state.id(&name) else {
            return Err(format!(
                "universally quantified variable {name} is not in any path declaration"
            ));
        };

        forall_state_ids.push(state_id);
    }

    let toks = merge_raw_tokens(tokens, &vars, &declarations)?;
    let constraints = construct_tree(toks)?;

    Ok(PatternFormula {
        forall_states: ForallStates(forall_state_ids),
        declarations,
        constraints,
        vars_mapping: vars,
    })
}

fn merge_raw_tokens(
    mut it: Peekable<impl Iterator<Item = RawToken>>,
    vars: &Vars,
    declarations: &Declarations,
) -> Result<Vec<FormulaToken>, String> {
    let mut toks = Vec::new();

    while let Some(x) = it.next() {
        match x {
            RawToken::And => toks.push(FormulaToken::And),
            RawToken::Or => toks.push(FormulaToken::Or),
            RawToken::Neg => toks.push(FormulaToken::Neg),
            RawToken::LParen => toks.push(FormulaToken::LParen),
            RawToken::RParen => toks.push(FormulaToken::RParen),
            RawToken::Init => parse_state_predicate(
                &mut it,
                &mut toks,
                vars,
                declarations,
                Atom::StartInit,
                Atom::EndInit,
            )?,
            RawToken::Final => parse_state_predicate(
                &mut it,
                &mut toks,
                vars,
                declarations,
                Atom::StartFinal,
                Atom::EndFinal,
            )?,
            RawToken::ReachInit => parse_state_predicate(
                &mut it,
                &mut toks,
                vars,
                declarations,
                Atom::StartReachInit,
                Atom::EndReachInit,
            )?,
            RawToken::ReachFinal => parse_state_predicate(
                &mut it,
                &mut toks,
                vars,
                declarations,
                Atom::StartReachFinal,
                Atom::EndReachFinal,
            )?,
            RawToken::Name(var1_name) => {
                let term1 = parse_term(&mut it, var1_name)?;

                let Some(op) = it.next() else {
                    return Err("expected binary operator".to_owned());
                };

                let Some(RawToken::Name(var2_name)) = it.next() else {
                    return Err("expected identifier after binary operator".to_owned());
                };
                let term2 = parse_term(&mut it, var2_name)?;

                let atom: FormulaToken = match op {
                    RawToken::Eq => parse_eq(term1, term2, vars, declarations)?,
                    RawToken::Prefix => parse_prefix(term1, term2, vars, declarations)?,
                    RawToken::LangBelong => parse_lang_belong(term1, term2, vars, declarations)?,
                    RawToken::LessEq => parse_less_or_eq(term1, term2, vars, declarations)?,
                    _ => return Err(format!("unknown binary operator {op:?}")),
                };

                toks.push(atom);
            }
            _ => (),
        }
    }

    Ok(toks)
}

enum Term {
    Name(String),
    Plus(Vec<String>),
    Concat(Vec<String>),
}

fn parse_term(
    it: &mut Peekable<impl Iterator<Item = RawToken>>,
    first_var: String,
) -> Result<Term, String> {
    match it.peek() {
        Some(RawToken::Plus) => {
            let mut term = vec![first_var];

            while let Some(RawToken::Plus) = it.peek() {
                it.next();

                let Some(RawToken::Name(var)) = it.next() else {
                    return Err("expected variable name after `+`".to_owned());
                };
                term.push(var);
            }

            Ok(Term::Plus(term))
        }
        Some(RawToken::Dot) => {
            let mut term = vec![first_var];

            while let Some(RawToken::Dot) = it.peek() {
                it.next();

                let Some(RawToken::Name(var)) = it.next() else {
                    return Err("expected variable name after `.`".to_owned());
                };
                term.push(var);
            }

            Ok(Term::Concat(term))
        }
        _ => Ok(Term::Name(first_var)),
    }
}

fn parse_state_predicate(
    it: &mut impl Iterator<Item = RawToken>,
    toks: &mut Vec<FormulaToken>,
    vars: &Vars,
    declarations: &Declarations,
    start_atom: fn(PathId) -> Atom,
    end_atom: fn(PathId) -> Atom,
) -> Result<(), String> {
    let Some(RawToken::Name(var_name)) = it.next() else {
        return Err("expected identifier".to_owned());
    };
    let state_id = vars
        .state
        .id(&var_name)
        .ok_or(format!("undeclared state variable {var_name}"))?;

    if let Some(pi) = declarations.path_id_by_start_state(state_id) {
        toks.push(FormulaToken::Atom(start_atom(pi)));
    } else if let Some(pi) = declarations.path_id_by_end_state(state_id) {
        toks.push(FormulaToken::Atom(end_atom(pi)))
    } else {
        return Err("unknown state variable".into());
    }
    Ok(())
}

fn extract_output_pis(
    vars: &Vars,
    declarations: &Declarations,
    term: Vec<String>,
) -> Result<Vec<PathId>, String> {
    let term_vars: Vec<_> = term
        .iter()
        .map(|v| vars.get_var(v).ok_or(format!("undeclared variable {v}")))
        .collect::<Result<_, _>>()?;

    let output_ids: Vec<_> = term_vars
        .iter()
        .map(|v| match v {
            &Var::Output(id) => Ok(id),
            _ => Err("only output variable terms allowed".to_owned()),
        })
        .collect::<Result<_, _>>()?;

    let pis = output_ids
        .iter()
        .map(|&id| declarations.path_id_by_output_var(id))
        .collect();

    Ok(pis)
}

fn parse_out_eq(
    term1: Term,
    term2: Term,
    vars: &Vars,
    declarations: &Declarations,
) -> Result<FormulaToken, String> {
    match (term1, term2) {
        (Term::Plus(term1), Term::Plus(term2)) => {
            let pis1 = extract_output_pis(vars, declarations, term1)?;
            let pis2 = extract_output_pis(vars, declarations, term2)?;

            Ok(FormulaToken::Atom(Atom::OutputEq(pis1, pis2)))
        }
        (Term::Name(term1), Term::Plus(term2)) => {
            let pis1 = extract_output_pis(vars, declarations, vec![term1])?;
            let pis2 = extract_output_pis(vars, declarations, term2)?;

            Ok(FormulaToken::Atom(Atom::OutputEq(pis1, pis2)))
        }
        (Term::Plus(term1), Term::Name(term2)) => {
            let pis1 = extract_output_pis(vars, declarations, term1)?;
            let pis2 = extract_output_pis(vars, declarations, vec![term2])?;

            Ok(FormulaToken::Atom(Atom::OutputEq(pis1, pis2)))
        }
        _ => Err("wrong type in '<=' (no concat terms allowed)".to_owned()),
    }
}

fn parse_eq(
    term1: Term,
    term2: Term,
    vars: &Vars,
    declarations: &Declarations,
) -> Result<FormulaToken, String> {
    let (Term::Name(var1_name), Term::Name(var2_name)) = (&term1, &term2) else {
        return parse_out_eq(term1, term2, vars, declarations);
    };

    let var1 = vars
        .get_var(var1_name)
        .ok_or(format!("undeclared variable {var1_name}"))?;
    let var2 = vars
        .get_var(var2_name)
        .ok_or(format!("undeclared variable {var2_name}"))?;

    match (var1, var2) {
        (Var::State(var1), Var::State(var2)) => {
            if let Some(pi1) = declarations.path_id_by_start_state(var1) {
                if let Some(pi2) = declarations.path_id_by_start_state(var2) {
                    Ok(FormulaToken::Atom(Atom::StartStartEq(pi1, pi2)))
                } else if let Some(path2) = declarations.path_id_by_end_state(var2) {
                    Ok(FormulaToken::Atom(Atom::StartEndEq(pi1, path2)))
                } else {
                    Err(format!("unknown state variable {var2_name}"))
                }
            } else if let Some(path1) = declarations.path_id_by_end_state(var1) {
                if let Some(path2) = declarations.path_id_by_start_state(var2) {
                    Ok(FormulaToken::Atom(Atom::EndStartEq(path1, path2)))
                } else if let Some(path2) = declarations.path_id_by_end_state(var2) {
                    Ok(FormulaToken::Atom(Atom::EndEndEq(path1, path2)))
                } else {
                    Err(format!("unknown state variable {var2_name}"))
                }
            } else {
                Err(format!("unknown state variable {var1_name}"))
            }
        }
        (Var::Path(var1), Var::Path(var2)) => Ok(FormulaToken::Atom(Atom::PathEq(var1, var2))),
        (Var::Input(var1), Var::Input(var2)) => {
            let pi1 = declarations.path_id_by_input_var(var1);
            let pi2 = declarations.path_id_by_input_var(var2);

            Ok(FormulaToken::Atom(Atom::InputEq(pi1, pi2)))
        }
        (Var::Output(var1), Var::Output(var2)) => {
            let pi1 = declarations.path_id_by_output_var(var1);
            let pi2 = declarations.path_id_by_output_var(var2);

            Ok(FormulaToken::Atom(Atom::OutputEq(vec![pi1], vec![pi2])))
        }
        _ => Err(format!(
            "mismatched types in '=' ({var1_name} vs {var2_name})"
        )),
    }
}

fn parse_prefix(
    term1: Term,
    term2: Term,
    vars: &Vars,
    declarations: &Declarations,
) -> Result<FormulaToken, String> {
    let (Term::Name(var1_name), Term::Name(var2_name)) = (term1, term2) else {
        return Err("expected a single variable name, found term in '#>".to_owned());
    };

    let var1 = vars
        .get_var(&var1_name)
        .ok_or(format!("undeclared input word variable {var1_name}"))?;
    let var2 = vars
        .get_var(&var2_name)
        .ok_or(format!("undeclared input word variable {var2_name}"))?;

    match (var1, var2) {
        (Var::Input(var1), Var::Input(var2)) => {
            let pi1 = declarations.path_id_by_input_var(var1);
            let pi2 = declarations.path_id_by_input_var(var2);

            Ok(FormulaToken::Atom(Atom::InputPrefix(pi1, pi2)))
        }
        _ => Err(format!("wrong types in '#>' ({var1_name}, {var2_name})")),
    }
}

fn parse_lang_belong(
    term1: Term,
    term2: Term,
    vars: &Vars,
    declarations: &Declarations,
) -> Result<FormulaToken, String> {
    let Term::Name(lang_var) = term2 else {
        return Err("found term, expected language variable".to_owned());
    };

    match term1 {
        Term::Name(var_name) => {
            let var = vars
                .get_var(&var_name)
                .ok_or(format!("undeclared input/output word variable {var_name}"))?;

            match var {
                Var::Input(var) => {
                    let pi = declarations.path_id_by_input_var(var);
                    Ok(FormulaToken::Atom(Atom::InputBelongs(pi, lang_var)))
                }
                Var::Output(var) => {
                    let pi = declarations.path_id_by_output_var(var);
                    Ok(FormulaToken::Atom(Atom::OutputBelongs(vec![pi], lang_var)))
                }
                _ => Err(format!(
                    "wrong type in '$>' ({var_name} is not an input/output word variable)"
                )),
            }
        }
        Term::Concat(term) => {
            let term_vars: Vec<_> = term
                .iter()
                .map(|v| {
                    vars.get_var(v)
                        .ok_or(format!("undeclared input/output word variable {v}"))
                })
                .collect::<Result<_, _>>()?;

            let output_ids: Vec<_> = term_vars
                .iter()
                .map(|v| match v {
                    &Var::Output(id) => Ok(id),
                    _ => Err("only output variable terms in '$>' allowed".to_owned()),
                })
                .collect::<Result<_, _>>()?;

            let pis: Vec<_> = output_ids
                .iter()
                .map(|&id| declarations.path_id_by_output_var(id))
                .collect();

            Ok(FormulaToken::Atom(Atom::OutputBelongs(pis, lang_var)))
        }
        Term::Plus(_) => Err("wrong type in '$>' (no sum terms allowed)".to_owned()),
    }
}

fn parse_less_or_eq(
    term1: Term,
    term2: Term,
    vars: &Vars,
    declarations: &Declarations,
) -> Result<FormulaToken, String> {
    let (Term::Name(var1_name), Term::Name(var2_name)) = (term1, term2) else {
        return Err("expected a single variable name, found term in '<='".to_owned());
    };

    let var1 = vars
        .get_var(&var1_name)
        .ok_or(format!("undeclared input word variable {var1_name}"))?;
    let var2 = vars
        .get_var(&var2_name)
        .ok_or(format!("undeclared input word variable {var2_name}"))?;

    match (var1, var2) {
        (Var::Input(var1), Var::Input(var2)) => {
            let pi1 = declarations.path_id_by_input_var(var1);
            let pi2 = declarations.path_id_by_input_var(var2);

            Ok(FormulaToken::Atom(Atom::InputLenLessOrEq(pi1, pi2)))
        }
        _ => Err(format!("wrong types in '<=' ({var1_name} vs {var2_name})")),
    }
}

// Shunting Yard Algorithm by E.W. Dijkstra.
fn construct_tree(tokens: Vec<FormulaToken>) -> Result<BooleanFormula, &'static str> {
    if tokens.is_empty() {
        return Ok(BooleanFormula::Empty);
    }

    let mut output_stack: Vec<BooleanFormula> = Vec::new();
    let mut operator_stack: Vec<FormulaToken> = Vec::new();

    for incoming in tokens {
        if incoming.is_connective_or_paren() {
            if let FormulaToken::LParen = incoming {
                operator_stack.push(incoming);
                continue;
            }

            while let Some(top) = operator_stack.last()
                && top.priority() > incoming.priority()
                && !output_stack.is_empty()
            {
                let top = operator_stack.pop().unwrap();

                if let FormulaToken::Neg = top {
                    apply_neg(&mut output_stack)?;
                } else {
                    apply_bin_op(top, &mut output_stack)?;
                }
            }

            if let FormulaToken::RParen = incoming {
                let Some(FormulaToken::LParen) = operator_stack.pop() else {
                    return Err("invalid formula, no matching bracket found");
                };
                continue;
            }

            operator_stack.push(incoming);
        } else {
            let FormulaToken::Atom(n) = incoming else {
                return Err("expected atom, got something else");
            };

            let node = BooleanFormula::Atom(n);
            output_stack.push(node);
        }
    }

    while let Some(op) = operator_stack.pop() {
        match op {
            FormulaToken::Neg => apply_neg(&mut output_stack)?,
            _ => apply_bin_op(op, &mut output_stack)?,
        }
    }

    if output_stack.len() != 1 {
        return Err("invalid formula");
    }
    let tree = output_stack
        .pop()
        .ok_or("failed to finish parsing formula")?;

    Ok(tree)
}

fn apply_neg(stack: &mut Vec<BooleanFormula>) -> Result<(), &'static str> {
    let l = stack.pop().ok_or("invalid formula")?;
    let node = BooleanFormula::Neg(Box::new(l));
    stack.push(node);
    Ok(())
}

fn apply_bin_op(op: FormulaToken, stack: &mut Vec<BooleanFormula>) -> Result<(), &'static str> {
    let r = stack.pop().ok_or("invalid formula")?;
    let l = stack.pop().ok_or("invalid formula")?;

    let Some(n) = Option::<BinOp>::from(op) else {
        return Err("expected binary operator, got something else");
    };

    let node = BooleanFormula::BinOp(n, Box::new(l), Box::new(r));
    stack.push(node);
    Ok(())
}
