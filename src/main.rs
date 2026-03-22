use std::{env, fs};

mod atoms;
mod automaton;
mod eval;
mod formula;
mod paths_n;
mod util;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 3 {
        panic!("expected at least 2 file names");
    }

    let fa_str = fs::read_to_string(&args[1])?;
    let fml_str = fs::read_to_string(&args[2])?;

    let other_args = &args[3..];
    let lang_automata_str: Vec<(String, String)> = {
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

            m.push((lang_name.to_owned(), fa_str));
        }
        m
    };

    println!("{}", eval::run(fml_str, fa_str, lang_automata_str).unwrap());

    Ok(())
}
