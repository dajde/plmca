import random
import os
from enum import Enum, auto
import shutil
from fa_generator import OutputMonoid

random.seed(42)

FORMULAS_PATH = "formulas"
N_PRED = 4

class VarType(Enum):
    STATE = auto()
    PATH = auto()
    WORD = auto()

def _random_var_id(fml_size: int) -> int:
    return random.randint(1, fml_size)

def _single_random_state_var(fml_size: int) -> str:
    state = random.choice(["p","q"])
    n = _random_var_id(fml_size)

    return f"{state}{n}"

def _single_random_input_word_var(fml_size: int) -> str:
    n = _random_var_id(fml_size)
    return f"u{n}"

def _single_random_output_word_var(fml_size: int) -> str:
    n = _random_var_id(fml_size)
    return f"v{n}"

def _two_random_state_vars(fml_size: int) -> list[str]:
    state1 = random.choice(["p", "q"])
    state2 = random.choice(["p", "q"])

    n1 = _random_var_id(fml_size)
    n2 = _random_var_id(fml_size)

    if state1 == state2 and n1 == n2:
        if state1 == "p":
            state1 = "q"
        else:
            state1 = "p" 

    return [f"{state1}{n1}", f"{state2}{n2}"]

def _two_random_path_vars(fml_size: int) -> list[str]:
    n1 = _random_var_id(fml_size)
    n2 = _random_var_id(fml_size)

    while n1 == n2:
        n2 = _random_var_id(fml_size)

    return [f"pi{n1}", f"pi{n2}"]

def _two_random_input_word_vars(fml_size: int) -> list[str]:
    n1 = _random_var_id(fml_size)
    n2 = _random_var_id(fml_size)

    while n1 == n2:
        n2 = _random_var_id(fml_size)

    return [f"u{n1}", f"u{n2}"]

def _two_random_output_word_vars(fml_size: int) -> list[str]:
    n1 = _random_var_id(fml_size)
    n2 = _random_var_id(fml_size)

    while n1 == n2:
        n2 = _random_var_id(fml_size)

    return [f"v{n1}", f"v{n2}"]

def _init_pred(fml_size: int) -> str:
    return f"init {_single_random_state_var(fml_size)}"

def _final_pred(fml_size: int) -> str:
    return f"final {_single_random_state_var(fml_size)}"

def _reach_init_pred(fml_size: int) -> str:
    return f"reach_init {_single_random_state_var(fml_size)}"

def _reach_final_pred(fml_size: int) -> str:
    return f"reach_final {_single_random_state_var(fml_size)}"

def _eq_pred(fml_size: int) -> str:
    var_type = random.choice(list(VarType))
    match var_type:
        case VarType.STATE:
            [a, b] = _two_random_state_vars(fml_size)
            return f"{a} = {b}"
        case VarType.PATH:
            [a, b] = _two_random_path_vars(fml_size)
            return f"{a} = {b}"
        case VarType.WORD:
            [a, b] = _two_random_input_word_vars(fml_size)
            return f"{a} = {b}"
        
def _prefix_pred(fml_size: int) -> str:
    [a, b] = _two_random_input_word_vars(fml_size)
    return f"{a} #> {b}"

def _length_pred(fml_size: int) -> str:
    [a, b] = _two_random_input_word_vars(fml_size)
    return f"{a} <= {b}"

def _lang_belong_pred(fml_size: int) -> str:
    a = _single_random_input_word_var(fml_size)
    return f"{a} $> L"

def _output_lang_belong_pred(fml_size: int) -> str:
    a = _single_random_output_word_var(fml_size)
    return f"{a} $> O"

def _output_neq_pred(fml_size: int) -> str:
    [a, b] = _two_random_output_word_vars(fml_size)
    return f"! {a} = {b}"

PREDICATES = {
    0: _init_pred,
    1: _final_pred,
    2: _reach_init_pred,
    3: _reach_final_pred,
    4: _eq_pred,
    5: _prefix_pred,
    6: _length_pred,
    7: _lang_belong_pred,
}

def _path_decl(i: int) -> str:
    return f"exists pi{i}: p{i} -- u{i} -> q{i}" 

def _path_decl_output(i: int) -> str:
    return f"exists pi{i}: p{i} -- u{i}, v{i} -> q{i}"   

def _gen_formula(fml_size: int, output_monoid: OutputMonoid) -> str:
    prefix: list[str] = []

    for i in range(fml_size):
        prefix.append(_path_decl(i+1) if output_monoid == OutputMonoid.TRIVIAL else _path_decl_output(i + 1))

    prefix_str = ", ".join(prefix) + ", "

    predicates: list[str] = []

    match output_monoid:
        case OutputMonoid.FREE:
            predicates.append(_output_lang_belong_pred(fml_size))
        case OutputMonoid.NUMBER:
            predicates.append(_output_neq_pred(fml_size))
        case OutputMonoid.TRIVIAL:
            pass

    while len(predicates) != N_PRED:
        choice = random.randint(0,len(PREDICATES) - 1)
        predicate = PREDICATES[choice](fml_size)
        if predicate not in predicates:
            predicates.append(predicate)

    predicates_str = " /\\ ".join(predicates)

    return prefix_str + predicates_str

def _generate_formulas(fml_size: int, fmls_per_size: int, output_monoid: OutputMonoid) -> list[str]:
    formulas: list[str] = []

    while len(formulas) != fmls_per_size:
        f = _gen_formula(fml_size, output_monoid)
        if f not in formulas:
            formulas.append(f)

    return formulas

def generate_formulas(min_fml_size: int, max_fml_size: int, fmls_per_size: int, output_monoid: OutputMonoid):
    os.makedirs(f"{FORMULAS_PATH}/{output_monoid.value}")

    for size in range(min_fml_size, max_fml_size + 1):
        formulas = _generate_formulas(size, fmls_per_size, output_monoid)

        size_dir = f"{FORMULAS_PATH}/{output_monoid.value}/{size}"
        os.mkdir(size_dir)
        for [i,f] in enumerate(formulas):
            with open(f"{size_dir}/fml{i}.txt", "w") as file:
                file.write(f)
