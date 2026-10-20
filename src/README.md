# Computational checks

Run commands from the repository root. These programs use exact counts and exact
rational arithmetic. Their finite bounds are evidence for the argument, rather
than a proof for arbitrary length or number of blocks.

Requires Python 3.10 or newer, a C++17 compiler with OpenMP, python-flint 0.9.0,
and SymPy for the separate symbolic implementation. No GPU is required.

| Program | Input and output |
|---|---|
| `verification/literal.cpp` | Modes `selftest`, `A n output.csv`, `G n output.csv`, `B n output.csv`; enumerates objects and counts by pattern, length, and transpositions. |
| `verification/check_series.py` | `--directory results/literal`; compares complete A/B/G CSV domains with integer bivariate series and writes combined CSV and JSON summary. |
| `verification/run.sh` | Optional output directory (default `./results/literal`); compiles the enumerator and runs the full literal pipeline with 16 OpenMP threads. |
| `verification/algebra_flint.py` | `--max-k 6 --workers 16 --output results/exact-k6.json`; exact generic matrix, interpolation, symmetry, denominator and specialization checks. |
| `review/review_independent.py` | `--n 10 --weight 7 --workers 16 --output results/independent-literal.json`; literal subsequences against the original piecewise source recurrence. |
| `review/review_symbolic.py` | `--max-k 4 --output results/independent-symbolic.json`; separate SymPy rational-function backend. |
| `review/review_general_components.py` | `--n 10 --output results/general-components.json`; 25 patterns formed from arbitrary indecomposable blocks, literal subsequences and all involutions. |
| `general/blocks_all.py` | `10 results/blocks_symmetry_n10.json`; 18 indecomposable blocks, 171 unordered pairs and 35 triples, all block orders. |
| `general/blocks.py` | `n` (default 8); reusable literal generator and pattern routines, and 12 illustrative groups printed to standard output. Imported by `blocks_all.py`, which also runs these illustrative checks. |

Create output parent directories first for `blocks_all.py`. The independent
literal oracle parallelizes by length; the two symbolic implementations
parallelize their independent sizes or permutation groups. The small general
component oracle is sequential and retained as a simple independent control.
The general block sweep uses 16 worker processes.

`run.sh` places a compiled executable in the requested results directory; this
executable is a local build product and is not part of the distributed evidence.
See [verification](../docs/VERIFICATION.md) and
[reproduction instructions](../docs/REPRODUCING.md) for scope and expected hashes.
