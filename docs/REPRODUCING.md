# Reproducing

This document gives per-component requirements, commands and expected outputs. The short version with measured run times is [`reproduce.md`](../reproduce.md). All commands are run from the repository root unless stated otherwise, and write new results under `results/` (ignored by Git) so that the distributed `data/` and `evidence/` stay untouched.

Reference machine for the recorded times: AMD Ryzen 7 8845HS (8 cores, 16 hardware threads), 48 GB RAM, Linux (x86_64). Everything is CPU-only.

## 1. Manuscript

`paper/manuscript.tex` is a single self-contained `amsart` file (packages `geometry`, `amsmath`, `amssymb`, `amsthm`, `xcolor`, `hyperref`; no external bibliography file). Any standard LaTeX distribution compiles it, for example

```sh
mkdir -p results/paper
pdflatex -interaction=nonstopmode -halt-on-error -output-directory results/paper paper/manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory results/paper paper/manuscript.tex
```

The distributed manuscript is version 4. The PDF is the reference; a recompiled PDF need not be byte-identical. Its current hashes are recorded in [`MANIFEST.json`](../MANIFEST.json). Print the distributed hashes with

```sh
sha256sum paper/manuscript.tex paper/manuscript.pdf
```

## 2. Lean formalization

Requirements: [Elan](https://github.com/leanprover/elan) (installs the toolchain pinned in `lean/lean-toolchain`, Lean `v4.36.0-rc1`), Git, network access for the first run. Mathlib is pinned at revision `533bd7c0a49acce520ee20b6ccc3a2f34e76be61` by `lean/lake-manifest.json`.

```sh
cd lean
lake exe cache get              # download prebuilt Mathlib
lake build                      # builds the EggeMansour library; must exit 0
lake env lean EggeMansour/Audit.lean
cd ..
```

Expected: `lake build` exits 0 with no `sorry` warnings (advisory module-system and linter warnings are normal); the audit prints the types of the final theorems and one axiom report per audited declaration, each exactly `[propext, Classical.choice, Quot.sound]`. Reference logs: [`evidence/lean/build.log`](../evidence/lean/build.log), [`evidence/lean/axioms.log`](../evidence/lean/axioms.log); source hashes: [`evidence/lean/SOURCE_SHA256SUMS`](../evidence/lean/SOURCE_SHA256SUMS).

The source scan and axiom audit can also be run by the driver

```sh
python3 src/verification/audit_lean.py --help
```

which hashes every Lean source, rejects `sorry`, `admit`, `axiom` and `native_decide` outside comments and strings, builds the requested modules, and checks one standard-axiom report per requested declaration; `--selftest` exercises its failure detection.

The executable small-length enumerations from the formal definitions and the kernel-checked examples are in three modules that the default build does not import; compile them with

```sh
lake build EggeMansour.CombinatoricsChecks EggeMansour.WrapChecks EggeMansour.ReductionChecks
```

(the `#eval` output of `CombinatoricsChecks` is execution evidence, not a kernel proof; the `example` declarations are checked by the kernel). The recorded output is `evidence/lean/checks.log`.

The recorded build reused matching pinned prebuilt dependency objects rather than testing a fresh network bootstrap. No machine-specific setup script is distributed. The normal reproduction commands above use the public Mathlib cache. Wall times of the recorded build and audit are in [`evidence/lean/timings.json`](../evidence/lean/timings.json) and in [`reproduce.md`](../reproduce.md).

## 3. Computational verification

Use Linux, Python 3.10 or newer, g++ with OpenMP/C++17, and 16 logical CPUs.
Install `python-flint==0.9.0` and SymPy in a virtual environment:

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install -r src/verification/requirements-algebra.txt sympy==1.14.0
export OMP_NUM_THREADS=16 OPENBLAS_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
mkdir -p results/review results/algebra
bash src/verification/run.sh results/literal
python3 src/verification/algebra_flint.py --max-k 6 --workers 16 --output results/algebra/exact-k6.json
python3 src/review/review_independent.py --n 10 --weight 7 --workers 16 --output results/review/independent-literal-n10.json
python3 src/review/review_symbolic.py --max-k 4 --output results/review/independent-symbolic-k4.json
python3 src/review/review_general_components.py --n 10 --output results/review/general-components-n10.json
python3 src/general/blocks_all.py 10 results/blocks_symmetry_n10.json
results/literal/literal A 12 results/review/counts-A-n12.csv
results/literal/literal G 12 results/review/counts-G-n12.csv
sha256sum results/literal/counts.csv results/blocks_symmetry_n10.json
sha256sum -c evidence/SHA256SUMS
```

Run from the repository root. The final checksum command verifies distributed
data; the preceding one hashes newly generated deterministic results. The
packaging rerun used the same commands, with outputs under `data/` and logs
under `evidence/`, except that the literal script wrote `results/literal`
and its CSV/JSON/log files were then copied into their distributed locations.
See `evidence/computation-timings.json` for the exact command arguments used.

Expected counts hash:
`ea54221c3af7705e1cb8ad51544d9485af9abcc588521a127850b2c34393e603`.
Expected block-summary hash:
`8d286eaba85389041318ca511d4cedf9aeca18b5e01038539e99a67a298b56f9`.
The algebra and oracle JSON files embed timing fields, and the summary also
records source-file hashes. Their full byte hashes differ on new runs.
To compare mathematical content, recursively remove dictionary keys
`seconds`, `elapsed_seconds`, `timings`, `source_hashes`, `script_sha256`,
and `generator_sha256`, then compare the JSON values. Stable hashes in
`evidence/data-comparison.json` serialize this normalized value with sorted
keys, compact comma/colon separators, and no trailing newline. All other
fields must agree. Historical supplemental `small.json` and
`factored-small.json` are not required for reproduction.

The literal comparator asserts domain completeness, zero discrepancies,
A=G, and detection of a marking mutation. The independent literal and
component scripts assert zero mismatches. Both algebra scripts fail an
assertion if an identity check fails. The broad block sweep reports failure
lists in JSON: verify both `pair_failures` and `triple_failures` are empty;
it does not signal mathematical failures through its process exit status.
Compare A/G n≤12 CSV rows after ignoring the initial mode field. No benchmark
or test should be interpreted as a proof beyond its declared scope.

Measured wall times on AMD Ryzen 7 8845HS w/ Radeon 780M Graphics (8 cores / 16 logical CPUs), 2026-10-19:

| Command group | Wall seconds | Exit code |
|---|---:|---:|
| literal | 118.689 | 0 |
| algebra | 142.097 | 0 |
| independent-literal | 2.113 | 0 |
| independent-symbolic | 2.811 | 0 |
| general-components | 1.544 | 0 |
| blocks | 14.975 | 0 |
| review-A12 | 0.112 | 0 |
| review-G12 | 0.097 | 0 |

Build products and rerun outputs stay under `results/`. The compiled literal
executable is not redistributed. See [VERIFICATION.md](VERIFICATION.md) for
independence, controls and limits, and the root `reproduce.md` for the full
repository workflow.

## 4. Integrity of distributed files

```sh
sha256sum -c evidence/SHA256SUMS
```

[`MANIFEST.json`](../MANIFEST.json) lists the SHA-256 and byte size of every distributed file except itself, including the manuscript, sources, documentation, data and evidence. The exact generation and verification commands appear in [`reproduce.md`](../reproduce.md).
