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

## Test file

Run the focused plunit suite in `/home/runner/work/algebraplop/algebraplop/tests/test_complex_detlog_plop.pl` with SWI-Prolog:

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/tests/test_complex_detlog_plop.pl -g run_tests -t halt
```

## Example CLI usage

```sh
swipl -q -s /home/runner/work/algebraplop/algebraplop/complex_detlog_plop.pl \
  -g "complex_optimise_file('input.pl','out/output.pl')" \
  -t halt
```
