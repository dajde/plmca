import random
import os
from enum import Enum, auto
import shutil

AUTOMATA_PATH = "automata"
ALPHABET_SIZE = 10
OUTPUT_ALPHABET_SIZE = 10

random.seed(42)

class OutputMonoid(Enum):
    TRIVIAL = "trivial"
    FREE = "free"
    NUMBER = "sum"

def _generate_transition(states: list[str], output_monoid: OutputMonoid):
    from_id = random.randint(0, len(states) - 1)
    from_state = states[from_id]

    to_id = random.randint(0, len(states) - 1)
    to_state = states[to_id]

    letter_id = random.randint(0, ALPHABET_SIZE - 1)
    letter = "l" + str(letter_id+1)

    transition = from_state + " -> " + to_state + " : " + letter

    match output_monoid:
        case OutputMonoid.TRIVIAL:
            pass
        case OutputMonoid.FREE:
            count = random.randint(1,3)

            output_word = []
            for _ in range(count):
                output_letter_id = random.randint(0, OUTPUT_ALPHABET_SIZE - 1)
                output_letter = "o" + str(output_letter_id+1)
                output_word.append(output_letter)

            transition += ", " + "|".join(output_word)
        case OutputMonoid.NUMBER:
            number = 0 if random.random() < 0.8 else 1
            transition += ", " + str(number)

    return transition

def _generate_automaton(n_states: int, n_trans: int, n_init: int, n_final: int, output_monoid: OutputMonoid) -> str:
    states: list[str] = []
    for i in range(n_states):
        states.append("q" + str(i + 1))

    for _ in range(n_init):
        checked = 0
        while checked != n_states:
            checked = checked + 1

            state_id = random.randint(0, len(states) - 1)
            state_name = states[state_id]

            if state_name.startswith("_"):
                continue

            state_name = "_" + state_name
            states[state_id] = state_name
            break

    for _ in range(n_final):
        checked = 0
        while checked != n_states:
            checked = checked + 1

            state_id = random.randint(0, len(states) - 1)
            state_name = states[state_id]

            if state_name.endswith("*"):
                continue

            state_name = state_name + "*"
            states[state_id] = state_name
            break

    transitions: set[str] = set()

    while len(transitions) != n_trans:
        transition = _generate_transition(states, output_monoid)
        transitions.add(transition)

    transitions_list: list[str] = list(transitions)
    transitions_list.sort()

    return "\n".join(transitions_list)

def _generate_automata(n_states: int, n_trans: int, n_automata: int, n_init: int, n_final: int, output_monoid: OutputMonoid) -> list[str]:
    automata: list[str] = []

    while len(automata) != n_automata:
        f = _generate_automaton(n_states, n_trans, n_init, n_final, output_monoid)
        if f not in automata:
            automata.append(f)

    return automata

def generate_automata(num_states: list[int], n_automata: int, output_monoid: OutputMonoid):
    os.makedirs(f"{AUTOMATA_PATH}/{output_monoid.value}")

    for n_states in num_states:
        n_trans = n_states * 2
        n_init = max(1,n_states // 10)
        n_final = max(1,n_states // 10)

        automata = _generate_automata(n_states, n_trans, n_automata, n_init, n_final, output_monoid)

        size_dir = f"{AUTOMATA_PATH}/{output_monoid.value}/{n_states}"
        os.mkdir(size_dir)
        for [i,f] in enumerate(automata):
            with open(f"{size_dir}/fa{i}.txt", "w") as file:
                file.write(f)