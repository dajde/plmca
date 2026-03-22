//! Formula simplification algorithms.

use crate::formula::{Atom, BinOp, BooleanFormula};

/// `BooleanFormula` in Negation Normal Form (NNF).
pub enum NNFBooleanFormula {
    Atom(Atom),
    BinOp(BinOp, Box<NNFBooleanFormula>, Box<NNFBooleanFormula>),
    Neg(Atom),
    Empty,
}

impl From<BooleanFormula> for NNFBooleanFormula {
    /// Returns a `BooleanFormula` in negation normal form (NNF).
    /// It uses De Morgan's rewriting rules to push negations to the atoms.
    fn from(tree: BooleanFormula) -> Self {
        match tree {
            BooleanFormula::Empty => NNFBooleanFormula::Empty,
            BooleanFormula::Neg(subtree) => {
                match *subtree {
                    BooleanFormula::Empty => NNFBooleanFormula::Empty,
                    BooleanFormula::BinOp(op, left, right) => {
                        match op {
                            BinOp::And => {
                                // Neg (f1 And f2) => Neg f1 Or Neg f2
                                let neg_left = BooleanFormula::Neg(Box::new(*left));
                                let neg_right = BooleanFormula::Neg(Box::new(*right));

                                NNFBooleanFormula::BinOp(
                                    BinOp::Or,
                                    Box::new(NNFBooleanFormula::from(neg_left)),
                                    Box::new(NNFBooleanFormula::from(neg_right)),
                                )
                            }
                            BinOp::Or => {
                                // Neg (f1 Or f2) => Neg f1 And Neg f2
                                let neg_left = BooleanFormula::Neg(Box::new(*left));
                                let neg_right = BooleanFormula::Neg(Box::new(*right));

                                NNFBooleanFormula::BinOp(
                                    BinOp::And,
                                    Box::new(NNFBooleanFormula::from(neg_left)),
                                    Box::new(NNFBooleanFormula::from(neg_right)),
                                )
                            }
                        }
                    }
                    BooleanFormula::Neg(x) => {
                        // Two negations in a row, we skip both.
                        NNFBooleanFormula::from(*x)
                    }
                    BooleanFormula::Atom(x) => NNFBooleanFormula::Neg(x),
                }
            }
            BooleanFormula::BinOp(op, left, right) => NNFBooleanFormula::BinOp(
                op,
                Box::new(NNFBooleanFormula::from(*left)),
                Box::new(NNFBooleanFormula::from(*right)),
            ),
            BooleanFormula::Atom(x) => NNFBooleanFormula::Atom(x),
        }
    }
}

/// An atom which is either plain or negated.
#[derive(Debug, Clone)]
pub enum Literal {
    Predicate(Atom),
    NotPredicate(Atom),
}

/// Returns the set of all the possible conjunctions of literals from a formula,
/// such that there exists a satisfiable conjunction in this set if and only if
/// the original formula is satisfiable.
pub fn split_ors(tree: NNFBooleanFormula) -> Vec<Vec<Literal>> {
    match tree {
        NNFBooleanFormula::Empty => Vec::new(),
        NNFBooleanFormula::BinOp(op, left, right) => match op {
            BinOp::Or => {
                let mut vec1 = split_ors(*left);
                let mut vec2 = split_ors(*right);

                vec1.append(&mut vec2);

                vec1
            }
            BinOp::And => {
                let mut vec1 = split_ors(*left);
                let vec2 = split_ors(*right);

                for subvec1 in &mut vec1 {
                    for subvec2 in &vec2 {
                        subvec1.extend(subvec2.iter().cloned())
                    }
                }

                vec1
            }
        },
        NNFBooleanFormula::Neg(x) => match x {
            Atom::Eq(var1, var2) => vec![vec![Literal::NotPredicate(Atom::Eq(var1, var2))]],
            Atom::Prefix(var1, var2) => {
                vec![vec![Literal::NotPredicate(Atom::Prefix(var1, var2))]]
            }
            Atom::Belongs(var, lang) => {
                vec![vec![Literal::NotPredicate(Atom::Belongs(var, lang))]]
            }
            Atom::LessOrEq(var1, var2) => {
                vec![vec![Literal::NotPredicate(Atom::LessOrEq(var1, var2))]]
            }
            Atom::Init(var) => vec![vec![Literal::NotPredicate(Atom::Init(var))]],
            Atom::Final(var) => vec![vec![Literal::NotPredicate(Atom::Final(var))]],
            Atom::ReachInit(var) => vec![vec![Literal::NotPredicate(Atom::ReachInit(var))]],
            Atom::ReachFinal(var) => vec![vec![Literal::NotPredicate(Atom::ReachFinal(var))]],
        },
        NNFBooleanFormula::Atom(x) => match x {
            Atom::Eq(var1, var2) => vec![vec![Literal::Predicate(Atom::Eq(var1, var2))]],
            Atom::Prefix(var1, var2) => vec![vec![Literal::Predicate(Atom::Prefix(var1, var2))]],
            Atom::Belongs(var, lang) => vec![vec![Literal::Predicate(Atom::Belongs(var, lang))]],
            Atom::LessOrEq(var1, var2) => {
                vec![vec![Literal::Predicate(Atom::LessOrEq(var1, var2))]]
            }
            Atom::Init(var) => vec![vec![Literal::Predicate(Atom::Init(var))]],
            Atom::Final(var) => vec![vec![Literal::Predicate(Atom::Final(var))]],
            Atom::ReachInit(var) => vec![vec![Literal::Predicate(Atom::ReachInit(var))]],
            Atom::ReachFinal(var) => vec![vec![Literal::Predicate(Atom::ReachFinal(var))]],
        },
    }
}
