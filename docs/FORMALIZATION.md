# Formalization from the definitions

The Lean project proves the summand symmetry theorem from the combinatorial definitions. Its target ring is `PowerSeries (Polynomial ℤ)`, namely ℤ[y][[x]]; the polynomial variable is y and the outer power-series variable is x. Every object is an actual finite permutation, a bijection of `Fin n` = {0, …, n−1}. No combinatorial statement is assumed: the Egge–Mansour weighted recurrence is a proved theorem (`combinatorialWeightedRecurrence`), to which the algebraic recurrence-to-symmetry theorem is applied.

All names belong to the namespace `EggeMansour` (algebra) or `EggeMansour.Combinatorics` (combinatorics). Manuscript indices start at 1; Lean indices start at 0.

## Exact final statements

Module `lean/EggeMansour/FromDefinitions.lean`:

```lean
theorem patternSeries_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) :
    patternSeries (sumPatterns (List.ofFn blocks)) =
      patternSeries (sumPatterns (List.ofFn (blocks ∘ ρ)))

theorem avoiderCount_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) (n t : ℕ) :
    avoiderCount (sumPatterns (List.ofFn blocks)).2 n t =
      avoiderCount (sumPatterns (List.ofFn (blocks ∘ ρ))).2 n t

theorem layeredSeries_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (lengths : Fin r → ℕ)
    (hpositive : ∀ i, 0 < lengths i) :
    patternSeries (layeredPattern lengths) =
      patternSeries (layeredPattern (lengths ∘ ρ))

theorem layeredCount_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (lengths : Fin r → ℕ)
    (hpositive : ∀ i, 0 < lengths i) (n t : ℕ) :
    avoiderCount (layeredPattern lengths).2 n t =
      avoiderCount (layeredPattern (lengths ∘ ρ)).2 n t
```

`r` is the number of summands (any natural number, including 0; the manuscript's k ≥ 1), `ρ` any permutation of the index set, `blocks ∘ ρ` the reordered family. The first two theorems are the main theorem (manuscript Theorem 1.1) for arbitrary indecomposable summands; the last two are Egge–Mansour 2006, Conjecture 3.14 (manuscript Corollary 1.2) as a series identity and as the equality of the counts by length n and number t of two-cycles; the ordinary (y = 1) statement is the sum over t. There is no distinctness, nonzero-series or invertibility hypothesis.

The frozen intermediate target is `DefinitionBasedSymmetry` in `CombinatorialTarget.lean` (families indexed by `Fin (k+1)`); it is proved by `definitionBasedSymmetry` in `CombinatorialMain.lean`, and the four public theorems are its instances through `Corollaries.lean`.

The recurrence itself is a theorem (`CombinatorialMain.lean`):

```lean
theorem combinatorialWeightedRecurrence {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) :
    WeightedRecurrence n seriesX seriesQ
      (fun i => patternSeries (blockAt blocks i))
      (fun i => wrappedSeries (blockAt blocks i))
      (fun i => (blockAt blocks i).1 == 1) (intervalSeries blocks)
```

with `WeightedRecurrence` the structure of `Interfaces.lean` described below, `seriesX = x`, `seriesQ = x²y`, `intervalSeries blocks i j = F_{τ_i ⊕ ⋯ ⊕ τ_j}`, and `wrappedSeries p` the series of the u ∈ 𝓘 such that 1 ⊖ u ⊖ 1 avoids p. By `wrappedSeries_eq_reducedSeries` this parameter equals `patternSeries (reduce p)` = F_{p̄}, which gives `reducedWeightedRecurrence` (`FromDefinitions.lean`): Egge–Mansour 2006, Theorem 3.3 with its literal block parameters h_i = F_{τ̄_i}.

## Definitions

Module `Combinatorics.lean` unless stated otherwise.

| Notion | Declaration | Definition |
|---|---|---|
| Permutation of length n | `Perm n := Equiv.Perm (Fin n)` | bijection of {0, …, n−1} |
| Pattern of varying length | `Pattern := Σ n, Perm n` | a length together with a permutation |
| Containment | `Contains σ τ` | `∃ f : Fin k → Fin n, StrictMono f ∧ ∀ i j, σ (f i) < σ (f j) ↔ τ i < τ j` |
| Avoidance | `Avoids σ τ := ¬ Contains σ τ` | |
| Involution | `IsInvolution σ := ∀ i, σ (σ i) = i` | |
| Two-cycles | `twoCycles σ := #{i | i < σ i}` | one index per transposition |
| Direct sum | `directSum σ τ : Perm (m + n)` | first block unchanged, second block shifted by m in positions and values |
| Skew sum | `skewSum σ τ : Perm (m + n)` | first block values shifted by n, second block unchanged |
| Wrapper 1 ⊖ u ⊖ 1 | `wrap u : Perm (n + 2)` (`Wrap.lean`) | 0 ↦ n+1, n+1 ↦ 0, i+1 ↦ u(i)+1 |
| Indecomposable | `IsIndecomposable σ` | `0 < n ∧ ∀ k : Fin n, 0 < k → ∃ i, i < k ∧ k ≤ σ i` (no proper invariant initial segment) |
| `IndecomposablePattern p` (`CombinatorialTarget.lean`) | `IsIndecomposable p.2` | nonempty and indecomposable |
| 3412 | `pattern3412 : Perm 4` | `skewSum 12 12`, the word [2, 3, 0, 1] |
| Direct sum of a list | `sumPatterns : List Pattern → Pattern` (`CombinatorialTarget.lean`) | `[] ↦ ∅`, `[p] ↦ p`, `p :: q :: ps ↦ p ⊕ sumPatterns (q :: ps)` |
| Decreasing pattern [a] | `decreasingPattern a` (`Corollaries.lean`) | `Fin.revPerm`, the word [a−1, …, 0] |
| Layered pattern [a₁,…,a_k] | `layeredPattern lengths` | `sumPatterns` of the decreasing patterns |
| 3412-avoiding involution | `IsAvoidingInvolution σ := IsInvolution σ ∧ Avoids σ pattern3412` | |
| Count | `avoiderCount τ n t` | number of `σ : Perm n` with `IsAvoidingInvolution σ`, `Avoids σ τ`, `twoCycles σ = t` |
| Coefficient of xⁿ | `avoiderPolynomial τ n := ∑ σ : Perm n, if IsAvoidingInvolution σ ∧ Avoids σ τ then X ^ twoCycles σ else 0` | polynomial in y |
| Series F_τ | `avoiderSeries τ := PowerSeries.mk (avoiderPolynomial τ)`; `patternSeries p := avoiderSeries p.2` | element of ℤ[y][[x]] |
| Reduction τ̄ | `reduce : Pattern → Pattern` (`Reduction.lean`) | delete the first entry if maximal and the last entry if minimal, standardize (Egge–Mansour 2006, Definition 3.2) |
| Wrapped series | `wrappedSeries p` (`WrappedSeries.lean`) | Σ_{u ∈ 𝓘, 1 ⊖ u ⊖ 1 avoids p} x^{|u|} y^{tc(u)} |

`coeff_coeff_avoiderSeries` (`CombinatoricsCounts.lean`) identifies the coefficient of xⁿ yᵗ of `avoiderSeries τ` with `avoiderCount τ n t`, so the series statements and the count statements are equivalent by construction. `Contains`, `Avoids`, `IsInvolution`, `IsIndecomposable`, `IsAvoidingInvolution` and `avoiderCount` are decidable and executable; `CombinatoricsChecks.lean` evaluates them for small lengths.

## Manuscript-to-source map

Labels refer to [the manuscript source](../paper/manuscript.tex). Declarations are in `EggeMansour.Combinatorics` unless they carry the prefix `EggeMansour.`.

| Manuscript item | Formal declarations | Module |
| --- | --- | --- |
| Definitions of §1 | table above | Combinatorics, Wrap, CombinatorialTarget, Corollaries |
| Coefficient extraction, F_∅ = 0 | `coeff_coeff_avoiderSeries`, `avoiderSeries_empty`, `two_mul_twoCycles`, `twoCycles_le_half` | CombinatoricsCounts, Combinatorics |
| Guibert decomposition, `lem:decomp`, confinement argument | `contains3412_of_crossing`, `no_crossing`, `first_arc_interior`, `first_arc_suffix`, `exists_unique_restriction` | Guibert |
| `lem:decomp`, form 1 ⊕ v as a bijection, weight x | `fixedConstructor`, `fixedFirstEquiv`, `twoCycles_fixedConstructor` | GuibertBijection |
| `lem:decomp`, form (1 ⊖ u ⊖ 1) ⊕ v as a bijection, weight x²y; the two forms as alternatives | `pairedConstructor`, `pairedFirstEquiv`, `guibert_split` | GuibertPair |
| 3412 is indecomposable; converse of `lem:decomp` | `pattern3412_indecomposable`, `avoids_directSum_iff_of_indecomposable`, `contains_wrap_3412_iff` | DirectSumContainment, GuibertBijection |
| `lem:layers`(a), indecomposable summands do not split | `indecomposable_occurrence_one_side`, `contains_directSum_iff_of_indecomposable`, `Contains.directSum` | DirectSumContainment |
| `lem:layers`(a), list form | `orderedCut_is_block_boundary`, `contains_directSum_sumPatterns_iff` | PatternSums, ListContainment |
| `lem:layers`(a), general cut without indecomposability | `contains_directSum_iff` (split at an invariant initial segment) | ContainmentCut |
| Reduction (`red`) and `lem:layers`(b) | `stripFirst`, `stripLast`, `reduce`, `contains_wrap_iff` (all τ, including ∅ and 1) | Reduction |
| `lem:layers`(c) | `reduce_directSum`, `contains_wrap_iff_of_not_max_not_min`, `contains_wrap_directSum_iff`, `avoids_wrap_directSum_iff` | Reduction, WrapContainment |
| `lem:layers`(d), leading summand equal to 1 | `contains_singleton_directSum_iff`, `contains_singleton_directSum_iff_of_prefix` | DirectSumContainment |
| h_i: the series of u with 1 ⊖ u ⊖ 1 avoiding τ_i; h_i = F_{τ̄_i} | `wrappedSeries`, `wrappedSeries_singleton`, `wrappedSeries_sumPatterns`, `wrappedSeries_eq_reducedSeries` | WrappedSeries, ReductionSeries |
| Partition of (1 ⊖ u ⊖ 1) ⊕ v by the maximal contained prefix t(u) | `prefixCell`, `avoids_directSum_iff_prefixCell`, `prefixCell_iff_avoidance_difference` | PrefixCells |
| Three classes of 𝓘(π) as disjoint images | `avoiderClass_iff_partition`, disjointness lemmas | AvoiderPartition |
| Weights of unions, differences, products, the shifts x and x²y | `weightSeries_add`, `weightSeries_sub`, `weightSeries_sum`, `weightSeries_mul`, `weightSeries_shift` | WeightedSeries |
| Images of the two constructors: x·U, x²y·U·V | `weightSeries_fixedImage`, `weightSeries_pairedImage` | ConstructorSeries |
| Cell series G_{t+1} − G_t and the class 1 ⊕ v | `weightSeries_prefixCell`, `weightSeries_fixedInner` | CellSeries |
| `prop:rec`, `eq:rec`, list form | `ListWeightedIdentity`, `listWeightedIdentity` | IntervalRecurrence, CombinatorialMain |
| `prop:rec`, `eq:rec`, interval form with the conventions of `WeightedRecurrence` | `weightedRecurrence_of_list_identity`, `combinatorialWeightedRecurrence`, `reducedWeightedRecurrence` | IntervalRecurrence, CombinatorialMain, FromDefinitions |
| Reordering of blocks as the parameter action of the algebra | `blockAt_reorder`, `blockParameter_reorder`, `definitionBasedSymmetry_of_weightedRecurrence` | CombinatorialTarget, CombinatorialBridge |
| Theorem 1.1 (`thm:main`) | `definitionBasedSymmetry`, `patternSeries_reorder`, `avoiderCount_reorder` | CombinatorialMain, FromDefinitions |
| Corollary 1.2 (`cor:EM`) | `layeredSeries_reorder`, `layeredCount_reorder` | FromDefinitions |

The algebraic modules are unchanged from the earlier version of the project and keep their map:

| Manuscript item | Formal declarations | Module |
| --- | --- | --- |
| Weighted recurrence, `prop:rec`, `eq:rec` (as an interface) | `EggeMansour.WeightedRecurrence` | Interfaces |
| Single-block elimination, `eq:single`, `eq:qh` | `ordinary_to_uniform`, `singleton_to_uniform` | Recurrence |
| Uniform recurrence, `prop:unif`, `eq:unif`, `eq:unif2` | `weighted_sum_eq`, `weighted_sum_endpoint`, `extract_endpoint`, `WeightedRecurrence.toUniform` | Recurrence |
| Interval uniqueness | `UniformRecurrence.eq_of_units` | Recurrence |
| Canonical recurrence, `def:R`, `eq:Rrec`, `lem:inL` | `canonical`, `canonical_step`, `canonical_uniform`, `Universal.local_endpoint_unit` | Canonical, Specialization |
| Shift, difference and interval matrices | `shiftMatrix`, `differenceMatrix`, `upperOnes`, `intervalMatrix`, `riccatiMatrix` | MatrixAdapter |
| Matrix identity, `lem:matrix`; Riccati equation, `eq:riccati` | `UniformRecurrence.matrix_identity`, `UniformRecurrence.matrix_riccati` | MatrixAdapter |
| Commutation, `eq:commute`; interpolation, `eq:interp` | `commute_of_riccati`, `interpolant`, `interpolant_eval`, `interpolant_degree_lt`, `interpolant_perm` | Generic |
| Centralizer and evaluation steps of `lem:WpA` | `centralizer_eq_zero_of_diag_zero`, `centralizer_eq_of_diag_eq`, `aeval_upper`, `diagonal_aeval`, `riccati_eq_aeval_interpolant` | Centralizer, Generic |
| Bidiagonal moments, `lem:moments` | `bidiagonal_first_moment`, `bidiagonal_aeval_first_row` | Bidiagonal |
| Generic endpoint formula and invariance, `thm:generic`, `eq:genericsym` | `UniformRecurrence.eq_interpolant`, `UniformRecurrence.generic_symmetry`, `generic_symmetry_of_pos` | GenericRecurrence |
| Localization, fraction field, specialization `eq:phi`, `lem:specialize` | `Universal.Base`, `Universal.Local`, `Universal.Field`, `Universal.toField_injective`, `Universal.specialize`, `canonical_map`, `UniformRecurrence.map`, `Universal.uniform_symmetry_of_generic` | Localization, Canonical, Specialization |
| Recurrence ⇒ symmetry | `EggeMansour.recurrenceImpliesSymmetry`, `EggeMansour.weighted_recurrence_symmetry` | Main |

## The recurrence interface

`WeightedRecurrence n x q c h singleton F` (`Interfaces.lean`) has five fields, with zero-based indices and entries constrained only below n:

1. `lower`: j < i < n ⇒ F i j = 0.
2. `empty`: i < n ⇒ F (i+1) i = 0.
3. `diagonal`: i < n ⇒ F i i = c i.
4. `singleton_reduction`: i < n and the flag is true ⇒ h i = 0.
5. `step`: for i ≤ j < n, `F i j = 1 + x * (if singleton i then F (i+1) j else F i j) + q * h i * F i j + q * (F i (i+1) - h i) * F (i+1) j + q * ∑ r ∈ Finset.Icc (i+2) j, (F i r - F i (r-1)) * F r j`.

`combinatorialWeightedRecurrence` proves all five for `F = intervalSeries blocks`, `c i = F_{τ_i}`, `h i = wrappedSeries τ_i`, and the flag `(blocks i).1 == 1`. The step is the manuscript's `eq:rec`; its i = j case is the single-block relation.

## How the recurrence is proved

1. **Guibert's decomposition as two bijections.** For an involution σ avoiding 3412 with σ(0) = m > 0, no arc crosses the arc (0, m): a crossing a < b < σ(a) < σ(b) yields the 3412 occurrence σ(a) σ(b) a b (`contains3412_of_crossing`). Hence positions 1, …, m−1 are mapped among themselves and positions after m among themselves, giving the unique restrictions u and v. `fixedFirstEquiv` is the resulting bijection v ↦ 1 ⊕ v onto the avoiding involutions with first value 0, and `pairedFirstEquiv` the bijection (u, v) ↦ (1 ⊖ u ⊖ 1) ⊕ v onto those with first value m; `guibert_split` states that every avoiding involution is empty, or 1 ⊕ v, or (1 ⊖ u ⊖ 1) ⊕ v, as an equality of patterns.
2. **Containment.** An occurrence of an indecomposable pattern in σ ⊕ v lies entirely in σ or entirely in v (ordered cut ⇒ invariant initial segment ⇒ decomposable). For a list of indecomposable blocks the cut therefore lies at a block boundary, which gives `contains_directSum_sumPatterns_iff`: σ ⊕ v contains τ₁ ⊕ ⋯ ⊕ τ_m iff for some t, σ contains the first t blocks and v the remaining ones. `contains_wrap_iff` is Lemma 2.2(b): wrap u contains τ iff u contains τ̄; it is proved through four endpoint lemmas (host beginning with its maximum, pattern beginning or not with its maximum; and the mirror statements for a final minimum, obtained by inverting both permutations).
3. **Partition.** For (1 ⊖ u ⊖ 1) ⊕ v, let t(u) be the largest t such that 1 ⊖ u ⊖ 1 contains τ_i ⊕ ⋯ ⊕ τ_{i+t−1} (containment of prefixes is downward closed, so the boundary is unique). The pattern is avoided iff v avoids the remaining suffix (`avoids_directSum_iff_prefixCell`). `avoiderClass_iff_partition` writes 𝓘(π) as the disjoint union of {∅}, the image of the fixed-point constructor on the u with 1 ⊕ u avoiding π, and the images of the paired constructor on the cells t(u) = t with v avoiding the suffix.
4. **Weights.** `WeightedSeries.lean` turns disjoint unions, differences, products (unique direct-sum splitting) and the two injective shifts into identities of series: the fixed class contributes x times the inner series, each paired cell contributes x²y times (G_{t+1} − G_t) times the suffix series, where G_t is the wrapped series of the first t blocks (`wrappedSeries_sumPatterns` gives G_t = F_{i,i+t−1} for t ≥ 2, `wrappedSeries_empty` gives G_0 = 0, and `wrappedSeries_singleton` the case τ_i = 1). This is `listWeightedIdentity`; re-indexing r = i + t and the boundary conventions give `combinatorialWeightedRecurrence`.
5. **Algebra.** `definitionBasedSymmetry_of_weightedRecurrence` applies `weighted_recurrence_symmetry` to the recurrences of a block family and of its reordering (`blockAt_reorder` identifies the reordering with the algebra's `permuteParams`).

## Implementation choices

Permutations of different lengths are related through `Pattern` equalities and a single transport `castPerm` along length equalities (`PermutationCast.lean`); `Guibert.lean` uses the equivalent `permCast`. Containment is used in the equivalent form "strictly increasing positions f and strictly increasing values g with σ ∘ f = g ∘ τ" (`contains_iff_exists_strictMono`). The recurrence parameter is first defined as the wrapped series, which makes `singleton_reduction` immediate (1 ⊖ u ⊖ 1 contains 1), and only then identified with F_{τ̄}. The formal algebra uses `MvPolynomial (ℕ ⊕ Bool) ℤ` for the block parameters and localizes at all factors 1 − q cᵢ cⱼ, including i = j, which still specializes to ℤ[y][[x]] because every such factor has constant coefficient 1. Parameter differences are never inverted.

## Trust and reproduction

The project pins Lean `v4.36.0-rc1` and Mathlib commit `533bd7c0a49acce520ee20b6ccc3a2f34e76be61`, with transitive revisions in `lean/lake-manifest.json`. From an ordinary checkout with Elan and network access:

```sh
cd lean
lake exe cache get
lake build
lake env lean EggeMansour/Audit.lean
```

`EggeMansour.lean` imports `FromDefinitions` and the other principal modules, so `lake build` compiles every proof module; the three modules of executable and kernel-checked examples are built by `lake build EggeMansour.CombinatoricsChecks EggeMansour.WrapChecks EggeMansour.ReductionChecks`. `Audit.lean` prints the types of the final theorems and the axiom dependencies of the final theorems and of the principal intermediate declarations; every report must contain only `propext`, `Classical.choice` and `Quot.sound`. The script `src/verification/audit_lean.py` additionally rejects `sorry`, `admit`, `axiom` and `native_decide` tokens outside comments and strings and records source hashes. Commands, timings, environment, source hashes and audit output are preserved in [`evidence/lean`](../evidence/lean/). The recorded validation reused matching pinned prebuilt dependency objects; it is not a clean network bootstrap test. The build emits module-system advisory warnings from Mathlib imports and linter warnings; they do not indicate proof holes. No new axioms are declared anywhere in the project.

## Scope outside the formal proof

The formal objects are defined explicitly in the modules mapped above. Supplementary executable examples in `CombinatoricsChecks.lean`, `WrapChecks.lean` and `ReductionChecks.lean` test these definitions against small combinatorial instances. The manuscript's Corollaries 5.3 (y = −1) and 5.4 (Lagrange form), Proposition 5.5 (even layers), the Chebyshev and Opitz formulas and the discussion of what was previously known are not formal declarations. Computational finite checks and claims about historical novelty are outside the kernel proof. A formal proof establishes neither priority nor peer review.
