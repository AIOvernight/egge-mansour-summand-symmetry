# Computational verification

All checks use exact arithmetic. The enumerative checks cover finite lengths;
the rational-function checks cover finitely many matrix sizes with symbolic
parameters. They support the mathematical argument and do not prove its
unbounded form or establish priority. The formal proof of the theorem from the
definitions is described in [FORMALIZATION.md](FORMALIZATION.md); its own
verification record is summarized first.

## Formal verification

For version 2.0.0, a new ordinary source clone with no project build objects
compiled all 42 Lean modules in 53.515 seconds and exited 0 with no `sorry`
(`evidence/lean/build.log`). The nine dependency revisions were checked against
the pinned manifest; matching prebuilt dependency objects were reused, with
writable Lake metadata. A dependency download or full dependency rebuild was
not part of this measurement.

The generated type audit prints the actual types and axiom dependencies of 30
requested declarations, including `patternSeries_reorder`,
`avoiderCount_reorder`, `layeredSeries_reorder`, `layeredCount_reorder`,
`combinatorialWeightedRecurrence` and `reducedWeightedRecurrence`
(`evidence/lean/types-axioms.log`). The default `EggeMansour/Audit.lean` also
passes all 29 of its expected axiom reports (`evidence/lean/axioms.log`). Two
explicit semantic expansions restate general and layered symmetry directly in
terms of `avoiderSeries` and actual finite permutations
(`evidence/lean/expanded-types-axioms.log`). Every requested report is present
and contains only `propext`, `Classical.choice` and `Quot.sound` (or a subset).
The script `src/verification/audit_lean.py`
rejects `sorry`, `admit`, `axiom` and `native_decide` tokens outside comments
and strings in every Lean source file, rebuilds the requested modules, requires
exactly one axiom report per requested declaration, and records source and
compiler hashes; its self-test contains deliberately malformed reports,
unexpected axioms, forbidden tokens and a failing compiler command, all of
which it rejects. Source hashes of every Lean file are in
`evidence/lean/SOURCE_SHA256SUMS`. All 42 modules retain identical proof-code
tokens relative to version 1.1.0; five have explanatory-comment revisions.
The exact comparison and before/after hashes are in
`evidence/lean/source-preservation.json`.

Two kinds of checks tie the formal definitions to the intended objects.
Kernel-checked examples (`decide`, evaluated by the Lean kernel at compile
time) confirm the one-line words of the wrapper 1 ⊖ u ⊖ 1 for small u, of the
Guibert constructors, of list direct sums and layered patterns, the reductions
of 312, 231, 21, 12, 321 and 3412, and small containment instances. Executable
enumerations (`#eval`, execution evidence rather than kernel proofs) list all
permutations of each length n ≤ 5 and apply the literal predicates: the number
of 3412-avoiding involutions by number of two-cycles is 1; 1; 1, 1; 1, 3;
1, 6, 2; 1, 10, 10 (row sums 1, 1, 2, 4, 9, 21, the Motzkin numbers), and the
avoidance counts for the patterns 12 and 21 (only the decreasing involution of
each length avoids 12; only the identity avoids 21). The recorded output is
`evidence/lean/checks.log`.

The kernel checks the proof of the formal statement; it does not check that the
formal statement is the intended one. That correspondence rests on the
definitions being short and standard, on the reading of them against the
manuscript, and on the enumerations above.

## Literal bivariate counts

A layered pattern is specified by a positive composition: decreasing blocks
combined by direct sum. Counts are indexed by pattern, permutation length n,
and number r of transpositions. Fixed points do not contribute to r.

- A: all 255 positive compositions of total weight at most 8, n=0,...,16;
  explicit noncrossing partial matchings (Motzkin words).
- G: the same patterns and lengths; all involutions generated as fixed points
  and pairs, followed by literal four-index 3412 filtering. At n=16 this visits
  46,206,736 involutions, of which 853,467 avoid 3412.
- B: 34 distinct orders of the multisets (1,2,3), (1,1,3), (1,3,3), (2,3,4),
  (1,2,2,3), (1,1,1,2), n=0,...,22. At n=22 the generator enumerates
  400,763,223 noncrossing partial matchings, interpreted as 3412-avoiding
  involutions.

There are 46,206 CSV rows excluding the header and 23,283 distinct
(pattern,n,r) cells after domain overlaps. All agree with an independent
integer sparse bivariate-series implementation of the pole-free interval
recurrence. A and G agree on all 20,655 cells. The complete domain sizes are
asserted by the comparator. Directly comparing all orders in each multiset
also gives equality. Outputs: `data/literal/counts*.csv`, `summary.json`;
complete logs: `evidence/literal/`.

The generators do not use the generating-function recurrence. The larger
runs use a structural layer detector: direct sum composes transition maps,
and wrapping by a pair increases the longest decreasing subsequence by two.
`selftest` compares this detector against literal subsequence pair
comparisons for 261 vectors on all 3412-avoiding involutions through n=10.
It also checks telephone and Motzkin totals. Counts by r in noncrossing modes
are checked against binomial(n,2r) Catalan(r).

A negative control erases the y marking, replacing q=x²y by x². It must
produce a discrepancy; for pattern (1,1), n=2, r=0, the true count is 0
and the mutated value is 1. The comparator records the counterexample.

## Separate small-case implementations

`src/review/review_independent.py` generates all involutions, filters 3412
with four indices, and constructs patterns by ranking literal subsequences.
It compares against the unrearranged, piecewise source recurrence, rather
than the pole-free recurrence used by `check_series.py`. Scope: all 127
positive compositions of weight at most 7, n≤10. There are 4,572 compared
cells; no recurrence or order-symmetry discrepancies occur. Two mutation
controls detect erased pair weight and incorrect initial-singleton handling.
The separate C++ A/G rechecks through n=12 also agree. Outputs and full logs
are in `data/review/` and `evidence/review/`.

`src/review/review_general_components.py` tests 25 distinct patterns from six
groups of arbitrary direct-sum indecomposable blocks through n=10, using
literal ranked subsequences and the all-involution generator. No block-order
mismatches occur. `src/general/blocks_all.py` independently enumerates the 18
indecomposable permutations of sizes at most 4, tests their 171 unordered
pairs including repeats, and tests the 35 triples with replacement formed
from the five blocks of size at most 3. Every triple is compared over all
six position orders, including repeated orders where blocks repeat. No pair
or triple failures occur through n=10. Importing `blocks.py` additionally
prints 12 illustrative group checks; these pass too.

These checks are independent in implementation, with shared mathematical
definitions. The component oracle
shares its all-involution generator with the separate small-case oracle;
the broad pair/triple sweep uses the implementation in `general/blocks.py`.

## Exact generic algebra

`src/verification/algebra_flint.py` works over Q(q,s,c₀,...,cₖ₋₁), with
independent variables, using integer multivariate polynomial GCD reduction,
exact division and positive leading denominator coefficient (python-flint
0.9.0). For k=1,...,6 it verifies entrywise:

- AR−qRER=E⁻¹, AW−qW²=I, AW=WA, where W=RE;
- the full Lagrange matrix identity W=p(A) and scalar identity R₁ₖ=p(s);
- moments e₁ᵀAᵗ1=sᵗ for 0≤t<k;
- every reduced nonconstant denominator factor is ±(1−q cᵢcⱼ), i<j;
- all k! parameter orders, 873 orders in total.

The moment at t=k is required to be a nonidentity (negative control).
For k=3,4, the reduced expressions with c₁=c₀ agree with a fresh recurrence
with that repeated parameter. Individual singular Lagrange summands are
not evaluated at coincident nodes. The full k=6 numerator and denominator
have 16,083 and 6,944 terms. No floating point is used in algebraic tests.
`src/review/review_symbolic.py` repeats matrix, interpolation, moment,
denominator and permutation checks with a separate SymPy field backend
through k=4 (33 orders). Its scope does not include the t=k negative control
or repeated-node check; those are checked by the FLINT implementation.

`data/algebra/small.json` and `factored-small.json` preserve supplementary
historical k≤4 outputs, including their original timing/source-hash metadata.
The packaged source does not reproduce those older source hashes; the current
full `exact-k6.json` is the reproduced result. These supplements are not needed
for any claimed scope.

## Rerun, resources and hashes

The packaged computational commands completed with return code zero on 2026-10-19 for the earlier packaged release; their outputs and logs are retained unchanged in version 2.0.0. The formal build and audit evidence above is regenerated for this theorem release. Hardware:
AMD Ryzen 7 8845HS w/ Radeon 780M Graphics, 8 physical cores / 16 logical CPUs, 47.0 GiB RAM visible.
The enumeration uses 16 OpenMP threads and full algebra uses 16 worker
processes; the block sweep uses 16 processes. The independent layered oracle
parallelizes by length; the small component oracle remains sequential.
GPU suitability was assessed: the retained exact polynomial GCD backend and
irregular branching enumerators already reach the required bounds on CPU.
No GPU was used and no GPU performance claim is made.

Measured wall times include process startup, compilation for the literal
pipeline, and complete output writing. Concurrent work may affect these times.
Machine/compiler versions are in `evidence/computation-environment.json`;
exact commands and return codes are in `evidence/computation-timings.json`.

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

The combined counts and block-summary hashes reproduce the preserved
reference bytes exactly. Algebra and oracle JSON timings change by run;
`evidence/data-comparison.json` lists every differing JSON path, reference
and new byte hashes, and a stable-content hash. Its normalization removes
only timing and source-hash metadata; all mathematical content agrees.
Source hashes change only where the packaging edits listed in
`evidence/CHANGES.md` apply. `evidence/SHA256SUMS` covers every data file.

| File | SHA-256 |
|---|---|
| `data/literal/counts.csv` | `ea54221c3af7705e1cb8ad51544d9485af9abcc588521a127850b2c34393e603` |
| `data/algebra/exact-k6.json` | `ab02abc40db150c88619fa05f59e394b3bc3de0b4a5305b5028b35335858a625` |
| `data/blocks_symmetry_n10.json` | `8d286eaba85389041318ca511d4cedf9aeca18b5e01038539e99a67a298b56f9` |

## Scope limits

Generic literal subsequence validation stops at n=10; unrestricted-involution
cross-checking stops at n=16. Lengths 17–22 use only the noncrossing generator
and structural layer detector. Symbolic checks stop at k=6; repeated-node
checks here cover only k=3,4. None of these finite checks substitutes for the unbounded proof, which is
the Lean theorem. The broad block-order checks are finite evidence that the
formal and informal statements agree for arbitrary indecomposable blocks.

| Check | Result |
|---|---|
| Lean proof from the definitions | Builds; every audited declaration uses only the three standard axioms |
| Lean source scan | No `sorry`, `admit`, `axiom`, `native_decide` |
| Executable Lean enumeration n ≤ 5 | Motzkin totals and two-cycle rows from the formal definitions |
| Literal counts vs bivariate recurrence | 46,206 rows / 23,283 distinct cells; zero discrepancies |
| Noncrossing vs unrestricted generators | All 255 patterns through n=16 agree |
| Literal detector control | 261 vectors through n=10; pass |
| Bounded large enumeration | 34 orders through n=22; 400,763,223 objects at n=22 |
| Separate source-recurrence oracle | 127 patterns through n=10; zero discrepancies |
| Separate C++ generator rerun | A/G through n=12; agree |
| Generic exact algebra | k≤6; 873 orders; all identities pass |
| Separate SymPy algebra | k≤4; 33 orders; pass |
| Mutation and moment controls | Marking/singleton mutations detected; t=k nonidentity confirmed |
| Repeated parameter checks | k=3,4, c₁=c₀; pass |
| Arbitrary block literal oracle | 25 patterns through n=10; zero mismatches |
| Broad arbitrary block sweep | 18 blocks, 171 pairs, 35 triples through n=10; zero failures |
