//! PL formula definitions.

use crate::{
    atoms::{MAutomata, NfaM},
    util::{self, IdMap, parse::RawToken},
};
use std::collections::HashMap;

pub mod simplify;

/// Whole PL formula.
pub struct PatternFormula {
    pub declarations: Declarations,
    pub constraints: BooleanFormula,
}

struct Path {
    id: usize,
    start_id: usize,
    end_id: usize,
    input_id: usize,
    output_id: Option<usize>,
}

/// Path declarations in the PL formula.
pub struct Declarations {
    declarations: Vec<Path>,
}

impl Declarations {
    /// Get the id of the path by the start state id.
    pub fn path_id_by_start_state(&self, id: usize) -> Option<usize> {
        self.declarations
            .iter()
            .find(|x| x.start_id == id)
            .map(|x| x.id)
    }

    /// Get the id of the path by the end state id.
    pub fn path_id_by_end_state(&self, id: usize) -> Option<usize> {
        self.declarations
            .iter()
            .find(|x| x.end_id == id)
            .map(|x| x.id)
    }

    /// Get the id of the path by the input id.
    pub fn path_id_by_input_var(&self, id: usize) -> usize {
        self.declarations
            .iter()
            .find(|x| x.input_id == id)
            .expect("unknown input word variable")
            .id
    }
    /// Get the id of the path by the output id.
    pub fn path_id_by_output_var(&self, id: usize) -> usize {
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

        let mut equivalences_inputs: HashMap<usize, Vec<usize>> = HashMap::new();

        #[derive(Clone, Copy)]
        enum StateType {
            Start(usize),
            End(usize),
        }

        let mut equivalences_states: HashMap<usize, Vec<StateType>> = HashMap::new();

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
    Eq(Var, Var),
    Prefix(Var, Var),
    Belongs(Var, String),
    LessOrEq(Var, Var),
    Init(usize),
    Final(usize),
    ReachInit(usize),
    ReachFinal(usize),
}

impl From<FormulaToken> for Option<Atom> {
    fn from(token: FormulaToken) -> Self {
        match token {
            FormulaToken::Eq(x, y) => Some(Atom::Eq(x, y)),
            FormulaToken::Prefix(x, y) => Some(Atom::Prefix(x, y)),
            FormulaToken::Belongs(x, y) => Some(Atom::Belongs(x, y)),
            FormulaToken::LessOrEq(x, y) => Some(Atom::LessOrEq(x, y)),
            FormulaToken::Init(x) => Some(Atom::Init(x)),
            FormulaToken::Final(x) => Some(Atom::Final(x)),
            FormulaToken::ReachInit(x) => Some(Atom::ReachInit(x)),
            FormulaToken::ReachFinal(x) => Some(Atom::ReachFinal(x)),
            _ => None,
        }
    }
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
    Path(usize),
    State(usize),
    Input(usize),
    Output(usize),
}

struct Vars {
    path: IdMap<String>,
    state: IdMap<String>,
    input: IdMap<String>,
    output: IdMap<String>,
}

impl Vars {
    fn new() -> Self {
        Self {
            path: IdMap::new(),
            state: IdMap::new(),
            input: IdMap::new(),
            output: IdMap::new(),
        }
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
}

#[derive(Clone, Debug)]
enum FormulaToken {
    // Connectives.
    And,    // /\, priority 3
    Or,     // \/, priority 2
    Neg,    // !, priority 4
    LParen, // (, priority 0
    RParen, // ), priority 1
    // Predicates.
    Eq(Var, Var),         // x = y
    Prefix(Var, Var),     // x #> y
    Belongs(Var, String), // x $> L
    LessOrEq(Var, Var),   // x <= y
    Init(usize),          // init x
    Final(usize),         // final x
    ReachInit(usize),     // reach_init x
    ReachFinal(usize),    // reach_final x
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
    let it = input.chars().filter(|c| !c.is_whitespace()).peekable();
    let mut tokens = util::parse::tokens(it)?.into_iter().peekable();

    let path_no_outputs: Vec<(RawToken, &str)> = vec![
        (RawToken::Name(String::new()), "path identifier"),
        (RawToken::Colon, "colon `:`"),
        (RawToken::Name(String::new()), "start state identifier"),
        (RawToken::DoubleMinus, "double minus `--`"),
        (RawToken::Name(String::new()), "input word identifier"),
        (RawToken::Arrow, "arrow `->`"),
        (RawToken::Name(String::new()), "end state identifier"),
        (RawToken::Comma, "comma `,`"),
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
        (RawToken::Comma, "comma `,`"),
    ];

    while let Some(tok) = tokens.peek()
        && RawToken::Exists == *tok
    {
        tokens.next();

        let formats = vec![&path_no_outputs[..], &path_outputs[..]];
        let idents = util::parse::parse_line(&mut tokens, &formats)?;

        let path = match idents.as_slice() {
            [path, start, input, end] => Path {
                id: vars.path.insert(path.to_owned()),
                start_id: vars.state.insert(start.to_owned()),
                end_id: vars.state.insert(end.to_owned()),
                input_id: vars.input.insert(input.to_owned()),
                output_id: None,
            },
            [path, start, input, output, end] => Path {
                id: vars.path.insert(path.to_owned()),
                start_id: vars.state.insert(start.to_owned()),
                end_id: vars.state.insert(end.to_owned()),
                input_id: vars.input.insert(input.to_owned()),
                output_id: Some(vars.output.insert(output.to_owned())),
            },
            _ => return Err("invalid line format".to_owned()),
        };

        declarations.push(path);
    }

    let toks = merge_raw_tokens(tokens, &vars)?;
    let constraints = construct_tree(toks)?;

    Ok(PatternFormula {
        declarations: Declarations { declarations },
        constraints,
    })
}

fn merge_raw_tokens(
    mut it: impl Iterator<Item = RawToken>,
    vars: &Vars,
) -> Result<Vec<FormulaToken>, String> {
    let mut toks = Vec::new();
    // TODO: refactor, error handling
    while let Some(x) = it.next() {
        match x {
            RawToken::And => toks.push(FormulaToken::And),
            RawToken::Or => toks.push(FormulaToken::Or),
            RawToken::Neg => toks.push(FormulaToken::Neg),
            RawToken::LParen => toks.push(FormulaToken::LParen),
            RawToken::RParen => toks.push(FormulaToken::RParen),
            RawToken::Init => {
                let Some(RawToken::Name(state)) = it.next() else {
                    return Err("expected identifier".to_owned());
                };
                let id = vars
                    .state
                    .id(&state)
                    .ok_or(format!("undeclared state variable {state}"))?;

                toks.push(FormulaToken::Init(id));
            }
            RawToken::Final => {
                let Some(RawToken::Name(state)) = it.next() else {
                    return Err("expected identifier".to_owned());
                };
                let id = vars
                    .state
                    .id(&state)
                    .ok_or(format!("undeclared state variable {state}"))?;

                toks.push(FormulaToken::Final(id));
            }
            RawToken::ReachInit => {
                let Some(RawToken::Name(state)) = it.next() else {
                    return Err("expected identifier".to_owned());
                };
                let id = vars
                    .state
                    .id(&state)
                    .ok_or(format!("undeclared state variable {state}"))?;

                toks.push(FormulaToken::ReachInit(id));
            }
            RawToken::ReachFinal => {
                let Some(RawToken::Name(state)) = it.next() else {
                    return Err("expected identifier".to_owned());
                };
                let id = vars
                    .state
                    .id(&state)
                    .ok_or(format!("undeclared state variable {state}"))?;

                toks.push(FormulaToken::ReachFinal(id));
            }
            RawToken::Name(first_op) => {
                let Some(op) = it.next() else {
                    return Err("expected binary operator".to_owned());
                };

                let Some(RawToken::Name(second_op)) = it.next() else {
                    return Err("expected identifier after binary operator".to_owned());
                };

                let atom: FormulaToken = match op {
                    RawToken::Eq => {
                        let var1 = vars
                            .get_var(&first_op)
                            .ok_or(format!("undeclared variable {first_op}"))?;
                        let var2 = vars
                            .get_var(&second_op)
                            .ok_or(format!("undeclared variable {second_op}"))?;

                        match (&var1, &var2) {
                            (Var::State(_), Var::State(_))
                            | (Var::Path(_), Var::Path(_))
                            | (Var::Input(_), Var::Input(_))
                            | (Var::Output(_), Var::Output(_)) => FormulaToken::Eq(var1, var2),
                            _ => {
                                return Err(format!(
                                    "wrong types in '=' ({first_op} vs {second_op})"
                                ));
                            }
                        }
                    }
                    RawToken::Prefix => {
                        let var1 = vars
                            .get_var(&first_op)
                            .ok_or(format!("undeclared input word variable {first_op}"))?;
                        let var2 = vars
                            .get_var(&second_op)
                            .ok_or(format!("undeclared input word variable {second_op}"))?;

                        match (&var1, &var2) {
                            (Var::Input(_), Var::Input(_)) | (Var::Output(_), Var::Output(_)) => {
                                FormulaToken::Prefix(var1, var2)
                            }
                            _ => {
                                return Err(format!(
                                    "wrong types in '#>' ({first_op} vs {second_op})"
                                ));
                            }
                        }
                    }
                    RawToken::LangBelong => {
                        let var = vars
                            .get_var(&first_op)
                            .ok_or(format!("undeclared input word variable {first_op}"))?;

                        match &var {
                            Var::Input(_) | Var::Output(_) => FormulaToken::Belongs(var, second_op),
                            _ => {
                                return Err(format!(
                                    "wrong type in '$>' ({first_op} is not an input/output word variable)"
                                ));
                            }
                        }
                    }
                    RawToken::LessEq => {
                        let var1 = vars
                            .get_var(&first_op)
                            .ok_or(format!("undeclared input word variable {first_op}"))?;
                        let var2 = vars
                            .get_var(&second_op)
                            .ok_or(format!("undeclared input word variable {second_op}"))?;

                        match (&var1, &var2) {
                            (Var::Input(_), Var::Input(_)) | (Var::Output(_), Var::Output(_)) => {
                                FormulaToken::LessOrEq(var1, var2)
                            }
                            _ => {
                                return Err(format!(
                                    "wrong types in '<=' ({first_op} vs {second_op})"
                                ));
                            }
                        }
                    }
                    _ => return Err(format!("unknown binary operator {op:?}")),
                };

                toks.push(atom);
            }
            RawToken::Arrow
            | RawToken::Colon
            | RawToken::Comma
            | RawToken::DoubleMinus
            | RawToken::Exists
            | RawToken::Eq
            | RawToken::LangBelong
            | RawToken::LessEq
            | RawToken::Prefix => (),
        }
    }

    Ok(toks)
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
            let Some(n) = Option::<Atom>::from(incoming) else {
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

    assert!(output_stack.len() == 1, "output stack malformed");

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
