# algebraplop
Algebraic Position Plop

This repository now contains a minimal SWI-Prolog implementation of **Complex Detlog PLOP** in `/home/runner/work/algebraplop/algebraplop/complex_detlog_plop.pl`.

## Provided API

- `complex_optimise_file/2`
- `complex_optimise_program/4`
- `discover_position_algorithm/3`
- `splice_index_optimise/3`
- `program_to_r_spec/2`

The implementation focuses on exact positional formula discovery, exact Gaussian elimination for linear bases, recursive closed-form detection for arithmetic recurrences, address discovery, splice-index-loop planning, safety classification, cost comparison, and `r(...)` specification emission.

## Complete command showcase

This section gives a complete, copy-paste-ready command set for the repository.

### 1) Run the focused test suite

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/tests/test_complex_detlog_plop.pl -g run_tests -t halt
```

Runs all `plunit` tests in `/home/runner/work/algebraplop/algebraplop/tests/test_complex_detlog_plop.pl` and exits.

### 2) Open an interactive Prolog session with the module loaded

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/complex_detlog_plop.pl
```

Starts a REPL so you can run API predicates manually.

### 3) Discover a positional formula from samples (one-shot command)

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/complex_detlog_plop.pl \
  -g "discover_position_formula([sample([i-1],3),sample([i-2],5),sample([i-3],7),sample([i-4],9)], Formula), writeln(Formula)" \
  -t halt
```

Infers and prints a formula that matches the given sample mapping.

### 4) Discover and print a full optimisation result from an in-memory program term

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/complex_detlog_plop.pl \
  -g "Program=position_program(transform,[sample([i-1],3),sample([i-2],5),sample([i-3],7),sample([i-4],9)],[verify_samples([sample([i-5],11)]),original_cost(plan(quadratic,20))]), complex_optimise_program(Program, Optimised, RSpec, Report), portray_clause(Optimised), portray_clause(RSpec), portray_clause(Report)" \
  -t halt
```

Builds a program term, optimises it, and pretty-prints the optimised IR, emitted `r_spec`, and optimisation report.

### 5) Optimise from an input file and write output artifacts

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/complex_detlog_plop.pl \
  -g "complex_optimise_file('/home/runner/work/algebraplop/algebraplop/input.pl','/home/runner/work/algebraplop/algebraplop/out/output.pl')" \
  -t halt
```

Reads one Prolog term from `input.pl`, optimises it, and writes:

- `/home/runner/work/algebraplop/algebraplop/out/output.pl` (optimised IR term)
- `/home/runner/work/algebraplop/algebraplop/out/output.r.pl` (generated `r_spec` term)
- `/home/runner/work/algebraplop/algebraplop/out/output.report.txt` (optimisation report term)

### 6) Pretty-print generated artifacts for inspection

```sh
swipl -q -g "read_term_from_file('/home/runner/work/algebraplop/algebraplop/out/output.pl', T1, []), portray_clause(T1), read_term_from_file('/home/runner/work/algebraplop/algebraplop/out/output.r.pl', T2, []), portray_clause(T2), read_term_from_file('/home/runner/work/algebraplop/algebraplop/out/output.report.txt', T3, []), portray_clause(T3)" -t halt
```

Loads each output term and prints it in an easy-to-read clause layout.
