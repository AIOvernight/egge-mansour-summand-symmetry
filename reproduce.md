# Reproducing the proof and finite checks

Run the commands below from the repository root unless a `cd` is shown. Detailed scope, expected outputs and limitations are in [docs/REPRODUCING.md](docs/REPRODUCING.md), [docs/VERIFICATION.md](docs/VERIFICATION.md) and [docs/FORMALIZATION.md](docs/FORMALIZATION.md).

## Requirements

- Linux or a compatible environment, Python 3.10+, and a C++17 compiler with OpenMP.
- Python packages `python-flint==0.9.0` and `sympy==1.14.0`.
- [Elan](https://github.com/leanprover/elan) with `lake` on PATH. The Lean project pins Lean `v4.36.0-rc1`, Mathlib `533bd7c0a49acce520ee20b6ccc3a2f34e76be61` and all transitive dependencies.
- Network access for the initial Lean toolchain, source and cache downloads. No GPU is required.

```sh
python3 -m venv .venv
. .venv/bin/activate
python3 -m pip install python-flint==0.9.0 sympy==1.14.0
```

## Lean proof

```sh
cd lean
lake exe cache get
lake build EggeMansour EggeMansour.Audit EggeMansour.CombinatoricsChecks \
  EggeMansour.WrapChecks EggeMansour.ReductionChecks
lake env lean EggeMansour/Audit.lean
cd ..
```

The audit must print the final theorem types and one report per audited declaration, each containing only `[propext, Classical.choice, Quot.sound]`. The recorded build used matching pinned prebuilt dependency objects; a clean network bootstrap was not measured. Advisory module-system and linter warnings in the recorded build do not affect its successful exit status. The theorem is proved from the combinatorial definitions; see [docs/FORMALIZATION.md](docs/FORMALIZATION.md). `python3 src/verification/audit_lean.py --help` describes the source-scan and axiom-audit driver.

## Computational checks

Local outputs go under the ignored `results/` directory. They do not overwrite the distributed evidence.

```sh
mkdir -p results/algebra results/review
bash src/verification/run.sh results/literal
python3 src/verification/algebra_flint.py --max-k 6 --workers 16 --output results/algebra/exact-k6.json
python3 src/review/review_independent.py --n 10 --weight 7 --workers 16 --output results/review/independent-literal-n10.json
python3 src/review/review_symbolic.py --max-k 4 --output results/review/independent-symbolic-k4.json
python3 src/review/review_general_components.py --n 10 --output results/review/general-components-n10.json
python3 src/general/blocks_all.py 10 results/blocks_symmetry_n10.json
results/literal/literal A 12 results/review/counts-A-n12.csv
results/literal/literal G 12 results/review/counts-G-n12.csv
```

The literal pipeline includes its self-test, two object generators through length 16, the selected-pattern run through length 22, and comparison against an integer series implementation. JSON files containing timings or source metadata will not be byte-identical across runs. [evidence/data-comparison.json](evidence/data-comparison.json) lists the changed fields and the precise normalization used to compare mathematical content with the preserved reference run. The CSV and block-summary files reproduce their reference bytes exactly.

```sh
cmp results/literal/counts.csv data/literal/counts.csv
cmp results/blocks_symmetry_n10.json data/blocks_symmetry_n10.json
sha256sum -c evidence/SHA256SUMS
sha256sum -c evidence/lean/SOURCE_SHA256SUMS
```

## Measured wall times

The recorded machine has an AMD Ryzen 7 8845HS CPU, 8 physical cores and 16 hardware threads, with 50,514,145,280 bytes of RAM. Parallel programs used 16 workers or OpenMP threads. The separate small general-component oracle is sequential. The GPU was not used. These measurements are environment-dependent and exclude downloading dependencies.

| Check | Wall seconds |
| --- | ---: |
| Release 2.0.0: fresh build of all 42 Lean modules, pinned dependency objects reused | 53.515 |
| Release 2.0.0: exact types and axiom dependencies for 30 declarations | 3.635 |
| Release 2.0.0: default 29-declaration axiom audit | 3.708 |
| Release 2.0.0: two explicit semantic-expansion checks | 3.682 |
| Literal pipeline, A/G through n = 16 and B through n = 22, compilation and comparison included | 118.689 |
| Exact FLINT algebra through k = 6 | 142.097 |
| Independent literal oracle, n ≤ 10 and layer sum ≤ 7 | 2.113 |
| Independent SymPy algebra through k = 4 | 2.811 |
| General-component oracle, 25 patterns through n = 10 | 1.544 |
| All general-block pairs/triples through n = 10 | 14.975 |
| Additional A / G run through n = 12 | 0.112 / 0.097 |

The computational timings above are retained from the preceding release; the Lean timings were measured afresh for version 2.0.0. The clean Lean clone had no preexisting project build objects. Attaching and checking the nine pinned prebuilt dependencies took 30.637 seconds, and replaying the executable checks took 4.296 seconds. The exact commands and full timing precision are in [evidence/lean/timings.json](evidence/lean/timings.json); they exclude downloading dependencies. Complete environment and timing records: [evidence/lean](evidence/lean/), [computation environment](evidence/computation-environment.json), [computation timings](evidence/computation-timings.json).

## File integrity and manifest generation

`MANIFEST.json` records the SHA-256 digest and byte size of every distributed file except itself. To check the catalog without regenerating it:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
for row in json.loads(Path('MANIFEST.json').read_text())['files']:
    content = Path(row['path']).read_bytes()
    assert len(content) == row['bytes'], row['path']
    assert hashlib.sha256(content).hexdigest() == row['sha256'], row['path']
print('All manifest entries match.')
PY
```

The manifest is generated by this command, run from a clean distribution tree with no `.git`, `.lake`, virtual environment or local reproduction outputs present:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
files = []
for path in sorted(Path('.').rglob('*')):
    if not path.is_file() or path.as_posix() == 'MANIFEST.json':
        continue
    content = path.read_bytes()
    files.append({'path': path.as_posix(), 'bytes': len(content),
                  'sha256': hashlib.sha256(content).hexdigest()})
Path('MANIFEST.json').write_text(json.dumps(
    {'algorithm': 'SHA-256', 'files': files}, indent=2) + '\n')
PY
```

Only regenerate the manifest after intentional changes to the distributed files. Generating it before verification would replace the reference digests.
