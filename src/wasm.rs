use wasm_bindgen::prelude::*;

use crate::model_check;

#[wasm_bindgen]
pub struct Result {
    ok: bool,
    satisfied: bool,
    witness: String,
    error: String,
}

#[wasm_bindgen]
impl Result {
    pub fn ok(&self) -> bool {
        self.ok
    }

    pub fn satisfied(&self) -> bool {
        self.satisfied
    }

    pub fn witness(&self) -> String {
        self.witness.clone()
    }

    pub fn error(&self) -> String {
        self.error.clone()
    }
}

#[wasm_bindgen]
pub fn run(fml_str: &str, fa_str: &str, lang_automata_str: Vec<String>) -> Result {
    let (chunks, []) = lang_automata_str.as_chunks::<2>() else {
        return Result {
            ok: false,
            satisfied: false,
            witness: String::new(),
            error: "invalid language automata input".to_owned(),
        };
    };

    let mut lang_automata_str = Vec::new();
    for [variable, lang] in chunks {
        lang_automata_str.push((variable.as_str(), lang.as_str()));
    }

    match model_check::run(fml_str, fa_str, &lang_automata_str) {
        Ok((satisfied, witness)) => Result {
            ok: true,
            satisfied,
            witness: format!("{witness:?}"),
            error: String::new(),
        },
        Err(err) => Result {
            ok: false,
            satisfied: false,
            witness: String::new(),
            error: err,
        },
    }
}
