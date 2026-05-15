use std::{env, fs};

mod atoms;
mod automaton;
mod formula;
mod model_check;
mod paths_n;
mod util;

const USAGE: &str = r#"Usage: plmca <automaton_file> <formula_file> <language_automata_files>

Model-checks the given pattern logic formula against the given finite automaton.

Arguments:
  <automaton_file>            Path to a file containing a finite automaton
  <formula_file>              Path to a file containing a pattern logic formula
  <language_automata_files>   Paths to files containing language automata in VAR=FILE format

Output:
  Prints SATISFIED or NOT SATISFIED.

  If the formula is existentially quantified, there is a witness printed if it is satisfied.
  If the formula is universally quantified, there is a counterexample printed if it is not satisfied."#;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Load command line parameters.
    let args: Vec<String> = env::args().collect();
    if args.len() < 3 {
        println!("{USAGE}");
        return Ok(());
    }

    let fa_str = fs::read_to_string(&args[1])?;
    let fml_str = fs::read_to_string(&args[2])?;

    // Load language automata with their variable names.
    let other_args = &args[3..];
    let lang_automata_str: Vec<(&str, String)> = {
        let mut m = Vec::new();
        for arg in other_args {
            let mut split = arg.split('=');
            let Some(lang_name) = split.next() else {
                return Err("invalid language declaration".into());
            };
            let Some(filename) = split.next() else {
                return Err("no `=` in language declaration".into());
            };
            if filename.is_empty() {
                return Err("no filename in language declaration".into());
            }

            let fa_str = fs::read_to_string(filename)?;

            m.push((lang_name, fa_str));
        }
        m
    };

    let lang_automata_str: Vec<(&str, &str)> = lang_automata_str
        .iter()
        .map(|x| (x.0, x.1.as_str()))
        .collect();

    // Run the main program.
    let (satisfied, model) = model_check::run(&fml_str, &fa_str, &lang_automata_str)?;

    if satisfied {
        println!("SATISFIED");
        if !model.is_empty() {
            println!("PATH WITNESSES:");
            for p in model {
                println!("{}: {}", p[0], p[1..].join(" -> "));
            }
        }
    } else {
        println!("NOT SATISFIED");
        if !model.is_empty() {
            println!("COUNTEREXAMPLE STATES:");
            for p in model {
                println!("{}: {}", p[0], p[1]);
            }
        }
    }

    Ok(())
}
