# Summand symmetry of 3412-avoiding involutions, from the definitions

**Theorem — proved, and machine-checked in Lean 4 from the definitions.** Release 2.0.0.

This Lean project defines permutations of `Fin n`, pattern containment, involutions, two-cycles, direct and skew sums, indecomposability and the bivariate avoidance series in ℤ[y][[x]], and proves that the series of involutions avoiding 3412 and τ₁ ⊕ ⋯ ⊕ τ_k, for nonempty indecomposable τ_i, is invariant under every reordering of the summands. The proof goes through Guibert's decomposition, the containment lemmas, the Egge–Mansour weighted recurrence and the algebraic recurrence-to-symmetry theorem; no combinatorial fact is assumed.

The final declarations are `patternSeries_reorder`, `avoiderCount_reorder`, `layeredSeries_reorder` and `layeredCount_reorder` in `EggeMansour/FromDefinitions.lean` (namespace `EggeMansour.Combinatorics`), with `definitionBasedSymmetry`, `combinatorialWeightedRecurrence` (`CombinatorialMain.lean`) and `reducedWeightedRecurrence` (`FromDefinitions.lean`) as the main intermediate theorems. Their only hypotheses are the indecomposability of the summands, respectively the positivity of the layer lengths.

See [the formalization map](../docs/FORMALIZATION.md) for the exact statements, every definition, the manuscript correspondence and the proof route.

## Build

Install [Elan](https://github.com/leanprover/elan) and make `lake` available on PATH. The committed toolchain selects Lean `v4.36.0-rc1`; the manifest pins Mathlib `533bd7c0a49acce520ee20b6ccc3a2f34e76be61` and its dependencies. Run from this directory:

```sh
lake exe cache get
lake build
lake env lean EggeMansour/Audit.lean
```

Network access is needed for the initial toolchain, source and cache downloads. `lake build` compiles every proof module (`EggeMansour.lean` imports `FromDefinitions`, which imports the rest); the example modules `CombinatoricsChecks`, `WrapChecks` and `ReductionChecks` are built by naming them: `lake build EggeMansour.CombinatoricsChecks EggeMansour.WrapChecks EggeMansour.ReductionChecks`. The audit prints the final theorem types and one dependency report per audited declaration, each containing only `[propext, Classical.choice, Quot.sound]`. Timing records and source hashes are in [evidence/lean](../evidence/lean/). The recorded build reused pinned prebuilt dependency objects; a fresh network bootstrap was not measured.

## Source map

Combinatorial definitions and lemmas (namespace `EggeMansour.Combinatorics`):

| Module | Content |
| --- | --- |
| Combinatorics | Permutations of `Fin n`, containment, involutions, two-cycles, direct and skew sums, indecomposability, 3412, counts and the series |
| CombinatoricsCounts | Coefficients of the series are the counts; two-cycle statistics; singleton containment; sums and two-cycles |
| CombinatoricsChecks | Executable small-length enumerations from the definitions |
| PermutationCast | Transport of permutations along length equalities; `Pattern` equalities |
| Wrap, WrapChecks | The wrapper 1 ⊖ u ⊖ 1 as a permutation of length n + 2, its involution, cycle and containment properties; kernel-checked examples |
| ContainmentCut | Two-map characterisation of containment; general cut of an occurrence in a direct sum |
| DirectSumContainment | Indecomposable occurrences stay in one summand; leading summand equal to 1 |
| PatternSums, ListContainment | Direct sums of lists of patterns; ordered cuts lie at block boundaries; containment in σ ⊕ v of a list of indecomposable blocks |
| Reduction, ReductionChecks, ReductionSeries | Deletion of a maximal first or minimal last entry; the reduction τ̄; 1 ⊖ u ⊖ 1 contains τ iff u contains τ̄; the wrapped series equals F_{τ̄} |
| WrapContainment | Wrapping is invisible for nontrivial direct sums |
| Guibert, GuibertBijection, GuibertPair | Non-crossing of arcs in 3412-avoiding involutions; restrictions; the fixed-point and paired constructors as bijections; `guibert_split` |
| WeightedSeries | Series of graded families of permutations: unions, differences, direct-sum products, shifts |
| WrappedSeries | The recurrence parameter: series of u with 1 ⊖ u ⊖ 1 avoiding a pattern |
| ConstructorSeries | Series of the images of the two constructors: x·U and x²y·U·V |
| PrefixCells | Partition of direct-sum avoidance by the maximal contained prefix |
| CellSeries | Series of prefix cells and of the fixed-point class |
| AvoiderPartition | The avoidance class as a disjoint union of constructor images |
| CombinatorialTarget, CombinatorialBridge | The combinatorial target statement; block reordering as the algebra's parameter action; bridge from a recurrence to the target |
| IntervalRecurrence | The list form of the recurrence and its conversion to the interval interface |
| CombinatorialMain | The list identity, the weighted recurrence and `definitionBasedSymmetry` |
| Corollaries, FromDefinitions | Decreasing and layered patterns; count extraction; the four public theorems and the reduced-pattern recurrence |

Algebra (namespace `EggeMansour`):

| Module | Content |
| --- | --- |
| Interfaces | Recurrence structures, parameter permutation, target power-series ring |
| Recurrence | Weighted-to-uniform conversion and interval uniqueness |
| Canonical | Canonical interval family and transport through ring homomorphisms |
| MatrixAdapter | Finite interval matrices and their Riccati equation |
| Centralizer | Uniqueness from triangular commutation and diagonal entries |
| Bidiagonal | Bidiagonal moments and bounded-degree polynomial evaluation |
| Generic | Interpolation, commutation and generic matrix symmetry |
| GenericRecurrence | Generic full-interval formula and permutation invariance |
| Localization | Universal rings, denominator units and specialization |
| Specialization | Descent and recurrence-to-symmetry transfer |
| Main | Recurrence ⇒ symmetry with all generic premises discharged |
| Audit | Types and axiom dependencies of the principal declarations |

The [repository reproduction guide](../reproduce.md) covers all components.
