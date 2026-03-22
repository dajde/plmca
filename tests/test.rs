use plmca::eval;
use std::fs;
use std::path::Path;

#[test]
fn examples() {
    let dir = Path::new("tests/cases");

    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();

        let mut formula_path = path.clone();
        formula_path.push("fml.txt");
        let formula_string = fs::read_to_string(&formula_path).unwrap();

        let mut lang_path = path.clone();
        lang_path.push("lang.txt");
        let lang_string = fs::read_to_string(&lang_path).unwrap_or(String::new());
        let langs = if lang_string.is_empty() {
            vec![]
        } else {
            vec![("L".to_owned(), lang_string)]
        };

        for file in fs::read_dir(path).unwrap() {
            let path = file.unwrap().path();

            if path.ends_with("fml.txt") || path.ends_with("lang.txt") {
                continue;
            }

            let expect = path.to_str().map(|x| x.contains("true")).unwrap_or(false);

            let fa_string = fs::read_to_string(&path).unwrap();

            println!("testing formula {formula_path:?} with automaton {path:?}");

            let result = eval::run(formula_string.clone(), fa_string, langs.clone()).unwrap();
            println!("result={result}");
            let satisfied = !result.is_empty();

            assert!(
                expect == satisfied,
                "FAILED:\n  formula: {:?}\n  automaton: {:?}\n  expected: {}\n  got: {}",
                formula_path,
                path,
                expect,
                satisfied
            );
        }
    }
}
