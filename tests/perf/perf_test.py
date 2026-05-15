import fa_generator
import fml_generator
from fa_generator import AUTOMATA_PATH, OutputMonoid
from fml_generator import FORMULAS_PATH
from pathlib import Path
import time
import subprocess
from collections import defaultdict
import statistics
import os
import signal
import shutil
import sys

PATH_TO_BINARY = sys.argv[1]
TIMEOUT = 10.0

if os.path.exists(FORMULAS_PATH):
    shutil.rmtree(FORMULAS_PATH)

if os.path.exists(AUTOMATA_PATH):
    shutil.rmtree(AUTOMATA_PATH)

# Generate data
fml_generator.generate_formulas(min_fml_size=2, max_fml_size=4, fmls_per_size=10, output_monoid=OutputMonoid.TRIVIAL)
fml_generator.generate_formulas(min_fml_size=2, max_fml_size=4, fmls_per_size=10, output_monoid=OutputMonoid.FREE)
fml_generator.generate_formulas(min_fml_size=2, max_fml_size=4, fmls_per_size=10, output_monoid=OutputMonoid.NUMBER)

fa_generator.generate_automata(num_states=[3,5,10,15,20], n_automata=10, output_monoid=OutputMonoid.TRIVIAL)
fa_generator.generate_automata(num_states=[3,5,10,15,20], n_automata=10, output_monoid=OutputMonoid.FREE)
fa_generator.generate_automata(num_states=[2,3,4,5,6], n_automata=10, output_monoid=OutputMonoid.NUMBER)

def run(automaton_path: str, formula_path: str):
    cmd = [
        '/usr/bin/time',
        "-f",
        "%M",
        PATH_TO_BINARY,
        automaton_path,
        formula_path,
        "L=input_lang.txt",
        "O=output_lang.txt"
    ]
    print(f"{automaton_path}|{formula_path}")

    start = time.perf_counter()

    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True
    )

    try:
        _, stderr = proc.communicate(timeout=TIMEOUT)
        mrss = int(stderr)
    except subprocess.TimeoutExpired:
        print("timeout")
        os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        _, _ = proc.communicate()

        return TIMEOUT, None

    end = time.perf_counter()
    total_time = end - start

    return total_time, mrss

def print_results(time_results, mem_results, timeouts):
    for (formula, automaton_size), times in sorted(time_results.items()):
        average = sum(times) / len(times)
        minimum = min(times)
        maximum = max(times)
        median = statistics.median(times)

        sorted_times = sorted(times)
        p90 = sorted_times[int(0.90 * len(times))]
        max_mem = mem_results[(formula, automaton_size)]
        timeout = timeouts[(formula, automaton_size)]

        print(f"[{formula}], [{automaton_size}], [{average:.6f}], [{median:.6f}], [{minimum:.6f}], [{maximum:.6f}], [{p90:.6f}], [{max_mem}], [{timeout}/{len(times)}]")

def run_all_generated(output_monoid: OutputMonoid):
    automata_dir = Path(f"{AUTOMATA_PATH}/{output_monoid.value}")
    formulas_dir = Path(f"{FORMULAS_PATH}/{output_monoid.value}")

    time_results = defaultdict(list)
    mem_results = defaultdict(int)
    timeouts = defaultdict(int)

    for formula_size in formulas_dir.iterdir():
        for automaton_size in automata_dir.iterdir():
            key = (int(formula_size.name), int(automaton_size.name))

            for automaton in automaton_size.iterdir():
                for formula in formula_size.iterdir():
                    total_time, mrss = run(
                        f"{AUTOMATA_PATH}/{output_monoid.value}/{automaton_size.name}/{automaton.name}",
                        f"{FORMULAS_PATH}/{output_monoid.value}/{formula_size.name}/{formula.name}",
                    )

                    time_results[key].append(total_time)

                    if mrss is None:
                        timeouts[key] += 1
                        continue

                    curr_mrss = mem_results[key]
                    if mrss > curr_mrss:
                        mem_results[key] = mrss

    return time_results, mem_results, timeouts

def classic_test():
    return run_all_generated(OutputMonoid.TRIVIAL)

def transducers_test():
    return run_all_generated(OutputMonoid.FREE)

def sum_automata_test():
    return run_all_generated(OutputMonoid.NUMBER)

def handwritten_test():
    HANDWRITTEN_FORMULAS_PATH = "handwritten_formulas"

    time_results = defaultdict(list)
    mem_results = defaultdict(int)
    timeouts = defaultdict(int)

    for monoid in OutputMonoid:
        automata_dir = Path(f"{AUTOMATA_PATH}/{monoid.value}")
        handwritten_formulas_dir = Path(f"{HANDWRITTEN_FORMULAS_PATH}/{monoid.value}")

        for formula in handwritten_formulas_dir.iterdir():
            for automaton_size in automata_dir.iterdir():
                key = (formula.name, int(automaton_size.name))

                for automaton in automaton_size.iterdir():
                        total_time, mrss = run(
                            f"{AUTOMATA_PATH}/{monoid.value}/{automaton_size.name}/{automaton.name}",
                            f"{HANDWRITTEN_FORMULAS_PATH}/{monoid.value}/{formula.name}",
                        )

                        time_results[key].append(total_time)

                        if mrss is None:
                            timeouts[key] += 1
                            continue

                        curr_mrss = mem_results[key]
                        if mrss > curr_mrss:
                            mem_results[key] = mrss
    
    return time_results, mem_results, timeouts

total_start = time.perf_counter()

classic_time_results, classic_mem_results, classic_timeouts =  classic_test()
transducers_time_results, transducers_mem_results, transducers_timeouts = transducers_test()
sum_time_results, sum_mem_results, sum_timeouts = sum_automata_test()
handwritten_time_results, handwritten_mem_results, handwritten_timeouts = handwritten_test()

total_end = time.perf_counter()

print("RESULTS FOR GENERATED FORMULAS")
print("FORMULA SIZE | AUTOMATON SIZE | AVERAGE TIME (s) | MEDIAN TIME (s) | MINIMUM TIME (s) | MAXIMUM TIME (s) | P90 TIME (s) | MAX MEMORY (KB) | TIMEOUTS")
print_results(classic_time_results, classic_mem_results, classic_timeouts)
print("RESULTS FOR TRANSDUCERS")
print("FORMULA SIZE | AUTOMATON SIZE | AVERAGE TIME (s) | MEDIAN TIME (s) | MINIMUM TIME (s) | MAXIMUM TIME (s) | P90 TIME (s) | MAX MEMORY (KB) | TIMEOUTS")
print_results(transducers_time_results, transducers_mem_results, transducers_timeouts)
print("RESULTS FOR SUM AUTOMATA")
print("FORMULA SIZE | AUTOMATON SIZE | AVERAGE TIME (s) | MEDIAN TIME (s) | MINIMUM TIME (s) | MAXIMUM TIME (s) | P90 TIME (s) | MAX MEMORY (KB) | TIMEOUTS")
print_results(sum_time_results, sum_mem_results, sum_timeouts)
print("RESULTS FOR HANDWRITTEN FORMULAS")
print("FORMULA | AUTOMATON SIZE | AVERAGE TIME (s) | MEDIAN TIME (s) | MINIMUM TIME (s) | MAXIMUM TIME (s) | P90 TIME (s) | MAX MEMORY (KB) | TIMEOUTS")
print_results(handwritten_time_results, handwritten_mem_results, handwritten_timeouts)

total_time = total_end - total_start
print(f"TOTAL TIME: {total_time:.6f}")