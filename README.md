# Reordering the indecomposable summands of a forbidden pattern does not change the bivariate generating function of 3412-avoiding involutions: a proof of the Egge–Mansour symmetry conjecture, formalized in Lean 4 from the definitions

Let τ₁, …, τ_k be direct-sum indecomposable permutations and let F_{τ₁⊕⋯⊕τ_k}(x, y) be the generating function of involutions avoiding both 3412 and τ₁ ⊕ ⋯ ⊕ τ_k, with x marking the length and y the number of two-cycles. The manuscript in [`paper/`](paper/manuscript.pdf) proves that this series is invariant under every permutation of τ₁, …, τ_k, as an identity in ℤ[y][[x]], for every k ≥ 1. For decreasing summands τ_i = [a_i] this is **Conjecture 3.14 of Egge and Mansour (2006)**; its specialization y = 1 is **Conjecture 6.9 of Egge (2004)**; and the theorem contains the 3412 half of a conjecture stated by Burstein, Egge and Elizalde in July 2026. Before this work the published cases were k ≤ 2 (Egge 2004; Egge–Mansour 2006), k = 3 with all layers of even length (Egge 2004; Egge–Mansour 2006), and — by a deduction from Albert–Bouvel (2015) and Egge (2007) that is spelled out in the manuscript and does not seem to have been written down before — all layered patterns whose layers all have even length. The whole proof is formalized in Lean 4 with Mathlib, starting from the definitions of permutations of {0, …, n−1}, pattern containment, involutions, two-cycles, direct and skew sums, indecomposability and the coefficient-defined bivariate series: Guibert's decomposition, the containment lemmas, the Egge–Mansour weighted recurrence and the algebraic step from the recurrence to the symmetry are all machine-checked, and the main formal theorem has no hypothesis other than the indecomposability of the summands.

**Status: Theorem — proved, and machine-checked in Lean 4 from the definitions.** Release 2.0.0 includes manuscript v4 and the complete Lean 4 / Mathlib proof, with no `sorry` and only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. The final declarations are `patternSeries_reorder`, `avoiderCount_reorder`, `layeredSeries_reorder` and `layeredCount_reorder` in `EggeMansour.Combinatorics`. The recurrence is a proved theorem, not an assumption. **Priority is not established:** a March 2026 AMS abstract by Burstein and Egge announces a proof of the ordinary (y = 1) layered symmetry, while the abstract and slides of a July 2026 talk by the same group (with Elizalde) list it as a conjecture with special cases proved; no paper or preprint by them was found as of 2026-10-19. See [`docs/STATUS.md`](docs/STATUS.md), [`docs/BIBLIOGRAPHY.md`](docs/BIBLIOGRAPHY.md) and [`docs/AI_AND_PROVENANCE.md`](docs/AI_AND_PROVENANCE.md).

## The statement and the conventions

- **Permutations and patterns.** A permutation σ ∈ S_n *contains* τ ∈ S_m if some length-m subsequence of σ(1)⋯σ(n) has the same relative order as τ(1)⋯τ(m); otherwise σ *avoids* τ. Every permutation contains the empty permutation ∅.
- **Sums.** For π ∈ S_m, σ ∈ S_n: (π ⊕ σ)(i) = π(i) for i ≤ m and σ(i−m)+m for i > m (direct sum); (π ⊖ σ)(i) = π(i)+n for i ≤ m and σ(i−m) for i > m (skew sum).
- **Indecomposable.** A nonempty permutation is (direct-sum) indecomposable if it is not π ⊕ σ with π, σ nonempty. Every permutation is uniquely τ₁ ⊕ ⋯ ⊕ τ_k with indecomposable *summands* τ_i. The theorem permutes these summands; it says nothing about other decompositions.
- **Layered patterns.** [a] = a(a−1)⋯1 (decreasing, indecomposable) and [a₁,…,a_k] = [a₁] ⊕ ⋯ ⊕ [a_k], a_i ≥ 1. Repeated layers and layers of length 1 are allowed.
- **Involutions and weights.** An involution has cycles of length 1 (fixed points) and 2 (two-cycles); tc(σ) is the number of two-cycles. 𝓘 is the set of 3412-avoiding involutions of all lengths n ≥ 0, **including the empty involution**.
- **The series.** F_τ(x, y) = Σ_{σ ∈ 𝓘, σ avoids τ} x^{|σ|} y^{tc(σ)} ∈ ℤ[y][[x]]. The empty involution contributes 1 whenever τ ≠ ∅, and F_∅ = 0. The coefficient of xⁿ is a polynomial in y of degree ≤ ⌊n/2⌋.
- **Abbreviations.** q = x²y and s = 1 − x; c_i = F_{τ_i} (single-summand series).
- **Equality** is equality of formal power series in ℤ[y][[x]]: for every n and r, the number of 3412-avoiding involutions of length n with exactly r two-cycles that avoid the pattern is the same for every ordering of the summands. In particular it holds after the substitutions y = 1 (ordinary counts), y = −1 (signed counts) and y = 0.
- **In Lean** a permutation of length n is a bijection of `Fin n` = {0, …, n−1} (`Equiv.Perm (Fin n)`); containment is the existence of a strictly increasing map of positions that preserves and reflects the order of values; tc(σ) is the number of i with i < σ(i); the direct sum of a list [τ₁, …, τ_k] of patterns is τ₁ ⊕ (τ₂ ⊕ (⋯ ⊕ τ_k)); the series is `PowerSeries.mk` of the polynomials Σ_{σ} y^{tc(σ)} over the finitely many permutations of each length. [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md) lists every definition.

## Result

**Theorem.** Let k ≥ 1, let τ₁, …, τ_k be indecomposable permutations and let ρ be a permutation of {1, …, k}. Then F_{τ₁⊕⋯⊕τ_k}(x, y) = F_{τ_{ρ(1)}⊕⋯⊕τ_{ρ(k)}}(x, y) in ℤ[y][[x]]. ([manuscript](paper/manuscript.pdf), Theorem 1.1)

**Formal statements** (module `lean/EggeMansour/FromDefinitions.lean`, namespace `EggeMansour.Combinatorics`; `Pattern` is a permutation together with its length, `IndecomposablePattern` means nonempty and indecomposable, `sumPatterns` is the direct sum of a list, `patternSeries` is F_τ, `avoiderCount τ n t` is the number of 3412-avoiding involutions of length n with t two-cycles avoiding τ, `layeredPattern lengths` is [a₁,…,a_k], and `blocks ∘ ρ` is the reordered family):

| Theorem | Statement | Hypotheses |
|---|---|---|
| `patternSeries_reorder` | `patternSeries (sumPatterns (List.ofFn blocks)) = patternSeries (sumPatterns (List.ofFn (blocks ∘ ρ)))` | `∀ i, IndecomposablePattern (blocks i)` |
| `avoiderCount_reorder` | the same for `avoiderCount (…).2 n t`, for every n and t | same |
| `layeredSeries_reorder` | `patternSeries (layeredPattern lengths) = patternSeries (layeredPattern (lengths ∘ ρ))` | `∀ i, 0 < lengths i` |
| `layeredCount_reorder` | the same for `avoiderCount (…).2 n t`, for every n and t | same |
| `combinatorialWeightedRecurrence` (module `CombinatorialMain`) | the Egge–Mansour weighted recurrence for the actual interval series, with the wrapped-avoidance block parameters | indecomposability of the blocks |
| `reducedWeightedRecurrence` | the same recurrence with h_i = F_{τ̄_i} (the reduced pattern), i.e. Egge–Mansour 2006, Theorem 3.3 literally | same |

The family `blocks : Fin r → Pattern` may have any size r ≥ 0 and `ρ` is any element of `Equiv.Perm (Fin r)`; repeated summands and summands equal to the permutation 1 are allowed.

Corollaries (manuscript, Corollary 1.2 and Corollaries 5.1–5.4):

| Statement | Source of the conjecture | Obtained by |
|---|---|---|
| F_{[a₁,…,a_k]}(x, y) is symmetric in (a₁, …, a_k) | Egge–Mansour 2006, Conjecture 3.14 | τ_i = [a_i]; formal: `layeredSeries_reorder` |
| \|{σ ∈ 𝓘_n : σ avoids [a₁,…,a_k]}\| is symmetric in (a₁, …, a_k) | Egge 2004, Conjecture 6.9 (= Egge 2007, Conjecture 3.8) | y = 1; formal: `layeredCount_reorder` summed over t |
| Signed, even and odd counts are symmetric | Egge–Mansour arXiv:math/0401217v1, Conjectures 4.17–4.18 | y = −1 |
| F_{[m₁,…,m_k]⊕(π⊖1)}(x, y) is symmetric in (m₁, …, m_k) for every π | Burstein–Egge–Elizalde, July 2026 (3412 half; stated there at y = 1 and for π ∈ Av(3412)) | π ⊖ 1 is indecomposable |
| F_{τ₁⊕⋯⊕τ_k} = Σ_i c_i Π_{j≠i} (1 − x − α_j)/(α_i − α_j), α_i = c_i⁻¹ + x²y c_i, when the c_i are pairwise distinct | — | Lagrange form of the main identity |

The substitutions y = −1 and the Lagrange form are not separate formal declarations; they follow from the formal series identity by ring homomorphisms and by the manuscript's Corollary 5.4.

Sample coefficients from [`data/literal/counts.csv`](data/literal/counts.csv) (coefficient of xⁿ, as a polynomial in y). All rows in a block are different orderings of the same summands and agree, as the theorem predicts; the last block shows that the multiset of summands matters ([1,1] and [2] agree at y = 1 but not as bivariate series).

| Pattern(s) | n | Coefficient of xⁿ | Value at y = 1 |
|---|---|---|---|
| [1,2,3], [2,3,1], [3,1,2], [3,2,1] | 8 | 1 + 28y + 125y² + 121y³ + 13y⁴ | 288 |
| [1,3,3], [3,1,3], [3,3,1] | 8 | 1 + 28y + 135y² + 137y³ + 14y⁴ | 315 |
| [1,2,3], [2,1,3], [3,2,1] | 22 | 1 + 231y + 9785y² + 152133y³ + 1127814y⁴ + 4461990y⁵ + 9851452y⁶ + 12133995y⁷ + 7968444y⁸ + 2492459y⁹ + 285762y¹⁰ + 5121y¹¹ | 38 489 187 |
| [1,1,1,2], [1,2,1,1], [2,1,1,1] | 22 | 1 + 60y + 1115y² + 10087y³ + 52272y⁴ + 166464y⁵ + 333900y⁶ + 418665y⁷ + 315029y⁸ + 129844y⁹ + 23793y¹⁰ + 881y¹¹ | 1 452 111 |
| [1,1] vs. [2] | 6 | y³ vs. 1 | 1 vs. 1 |

**What is new and what matches published work.** The cases k ≤ 2 recover Egge 2004, Theorem 6.7 and Egge–Mansour 2006, Theorems 3.12–3.13 (the explicit two-summand formula is F_{τ₁⊕τ₂} = (c₁ + c₂ − s c₁c₂)/(1 − q c₁c₂)). The all-even layered case was already a consequence of the literature (see Prior work). Not covered by any published source we found: the layered case with at least one odd layer and k ≥ 3 (ordinary and bivariate), and the statement for arbitrary indecomposable summands. Whether these are new depends on the unresolved status of the 2026 announcements by Burstein, Egge and Elizalde (see [`docs/BIBLIOGRAPHY.md`](docs/BIBLIOGRAPHY.md)). The 312-avoiding analogue of the theorem is a case of Albert–Bouvel 2015 and is not claimed here. The formalization adds a machine-checked proof of the full statement, including the combinatorial part (Guibert's decomposition and the Egge–Mansour recurrence), which had been proved only on paper; a search on 2026-10-19 found no earlier formalization of permutation pattern containment, of 3412-avoiding involutions or of these conjectures in Lean, Isabelle or Coq (see Prior work).

## Prior work

- **O. Guibert (1995)**, PhD thesis, Université Bordeaux I, Remark 4.28: the decomposition of a nonempty 3412-avoiding involution as 1 ⊕ v or (1 ⊖ u ⊖ 1) ⊕ v (not consulted directly; cited through Egge–Mansour 2006).
- **E. S. Egge (2004)**, *Restricted 3412-avoiding involutions, continued fractions, and Chebyshev polynomials*, Adv. in Appl. Math. 33, 451–475, [doi:10.1016/j.aam.2003.09.006](https://doi.org/10.1016/j.aam.2003.09.006). The ordinary recurrence (Cor. 5.6), the two-layer theorem (Thm. 6.7), the three even layers case (Eq. (44)) and **Conjecture 6.9** (ordinary symmetry).
- **E. S. Egge and T. Mansour (2006)**, *Bivariate generating functions for involutions restricted by 3412*, Adv. in Appl. Math. 36, 118–137, [doi:10.1016/j.aam.2005.01.005](https://doi.org/10.1016/j.aam.2005.01.005). The weighted recurrence for an arbitrary direct sum of indecomposables (**Theorem 3.3**, with the reduction of Definition 3.2), the bivariate two-layer theorems (3.12–3.13), three even layers (Eq. (18)) and **Conjecture 3.14** (bivariate symmetry). The recurrence is the starting point of the proof here, and is re-proved in the manuscript and in Lean.
- **E. S. Egge (2007)**, *Restricted colored permutations and Chebyshev polynomials*, Discrete Math. 307, 1792–1800, [doi:10.1016/j.disc.2006.09.027](https://doi.org/10.1016/j.disc.2006.09.027). Transfer formula (Thm. 3.3) between 312-avoiding (colored) permutations with layered pattern [l₁,…,l_m] and 3412-avoiding involutions with [2l₁,…,2l_m]; Conjectures 3.7–3.10.
- **M. Albert and M. Bouvel (2015)**, *A general theory of Wilf-equivalence for Catalan structures*, Electron. J. Combin. 22(4), P4.45, [doi:10.37236/5629](https://doi.org/10.37236/5629). Rule (3) of Definition 7 and Theorem 8: adjacent atoms of a forbidden arch system may be exchanged. This settles the 312 analogue, and with Egge 2007 and the manuscript's Proposition 5.5 it gives the all-even-layers case of Conjecture 3.14. Their framework does not apply directly to 3412-avoiding involutions.
- **E. S. Egge (January 2026)**, talk at the Joint Mathematics Meetings, [slides](https://www.ericegge.net/slides/AMS_Perm_Patterns_Jan_2026_slides.pdf): presents the ordinary conjecture as open, checked for k ≤ 7.
- **A. Burstein and E. S. Egge (March 2026)**, AMS Spring Eastern Sectional Meeting, abstract 1215-05-60699, [meeting page](https://meetings.ams.org/math/spring2026e/meetingapp.cgi/Paper/60699): states "We prove that both F_[ℓ₁,…,ℓ_m] and G_[ℓ₁,…,ℓ_m] are symmetric", with generalizations and refinements by statistics. No written proof is available.
- **A. Burstein, with E. S. Egge and S. Elizalde (July 2026)**, Permutation Patterns 2026, abstract and slides linked from the [conference site](https://sites.google.com/view/permutationpatterns2026): list both symmetries as "Conjecture (Egge, 2004)", checked for k ≤ 7, prove special cases, and conjecture the generalization with a final summand π ⊖ 1 (covered here, in its 3412 half).
- **C. de Boor (2005)**, *Divided differences*, Surv. Approx. Theory 1, 46–69, [arXiv:math/0502036](https://arxiv.org/abs/math/0502036) (Opitz's formula for functions of bidiagonal matrices) and **C. B. Collins, I. P. Goulden, D. M. Jackson, O. M. Nierstrasz (1981)**, *A combinatorial application of matrix Riccati equations and their q-analogue*, Discrete Math. 36, 139–153, [doi:10.1016/0012-365X(81)90234-X](https://doi.org/10.1016/0012-365X(81)90234-X): classical tools; neither treats pattern avoidance.
- **Formalizations.** Mathlib at the pinned revision has no definition of pattern containment or avoidance for permutations. Web searches on 2026-10-19 for formalizations of permutation pattern avoidance, of 3412-avoiding involutions, of the Egge or Egge–Mansour conjectures, or of related results (stack sorting, Stanley–Wilf) in Lean 4 / Mathlib, in the Isabelle Archive of Formal Proofs and in Coq/Rocq found none; the closest hit is a Lean 4 formalization of a permutation of the positive integers without four-term arithmetic progressions, which is a different notion. The search combined general web searches with inspection of the pinned Mathlib/Combinatorics source tree; the AFP source index was not searched directly. It is not a guarantee of absence. Details: [`docs/BIBLIOGRAPHY.md`](docs/BIBLIOGRAPHY.md).

**What this adds:** a proof of the full bivariate symmetry for all k, including odd layers, repeated layers and layers of length 1, and its extension to arbitrary indecomposable summands; and a machine-checked proof of the whole statement from the combinatorial definitions, including Guibert's decomposition and the Egge–Mansour weighted recurrence. Full references, versions examined and dated searches: [`docs/BIBLIOGRAPHY.md`](docs/BIBLIOGRAPHY.md).

## Method

Detailed summary in [`docs/METHOD.md`](docs/METHOD.md); full proofs in the manuscript; the formal route and the names of all declarations in [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md).

1. **Decomposition and recurrence.** Every nonempty σ ∈ 𝓘 is uniquely 1 ⊕ v or (1 ⊖ u ⊖ 1) ⊕ v with u, v ∈ 𝓘 (Guibert). An indecomposable summand of the forbidden pattern cannot be split across a direct sum, and 1 ⊖ u ⊖ 1 contains τ iff u contains the reduction τ̄ of τ. Partitioning the class (1 ⊖ u ⊖ 1) ⊕ v by the longest prefix τ_i ⊕ ⋯ ⊕ τ_{i+t−1} contained in 1 ⊖ u ⊖ 1 gives the Egge–Mansour weighted recurrence for the interval series F_ij = F_{τ_i⊕⋯⊕τ_j}. In Lean the two forms of the decomposition are explicit bijections, the partition is by "maximal prefix cells", and the recurrence is first proved in a list form and then re-indexed to intervals.
2. **Uniform pole-free recurrence.** For i < j,
   (1 − q c_i c_j) F_ij = c_i + (1 − s c_i) F_{i+1,j} + q c_i Σ_{r=i+1}^{j−1} F_ir (F_rj − F_{r+1,j}),
   whose only coefficients are x, x²y and the single-summand series c_i. The case distinction τ_i = 1 / τ_i ≠ 1 of the published recurrence disappears.
3. **Generic Riccati identity and interpolation.** With q, s, c_i indeterminates, the solution matrix R satisfies AR − qRER = E⁻¹, where E = I − (superdiagonal shift) and A is upper bidiagonal with A_ii = α_i = 1/c_i + q c_i and A_{i,i+1} = s − α_i. Then W = RE satisfies the matrix Riccati equation AW − qW² = I, hence commutes with A, hence W = p(A) for the polynomial p of degree < k with p(α_i) = c_i. Since e₁ᵀ Aᵗ 𝟙 = sᵗ for t < k, R_1k = p(s) = p(1 − x). The interpolation data {(α_i, c_i)} form an unordered set, so R_1k is symmetric in c₁, …, c_k.
4. **Specialization.** R_1k lies in L = ℤ[q, s, c][(1 − q c_i c_j)⁻¹], and q ↦ x²y, s ↦ 1 − x, c_i ↦ F_{τ_i} extends to L → ℤ[y][[x]] because each 1 − x²y F_{τ_i} F_{τ_j} is a unit. Differences c_i − c_j are never inverted, so repeated summands, summands equal to 1, and y = 0, 1, −1 need no separate argument.

The computational checks are exact (integer counts, exact rational-function arithmetic); no GPU kernels are involved.

## Verification

Details, commands and hashes: [`docs/VERIFICATION.md`](docs/VERIFICATION.md) and [`docs/FORMALIZATION.md`](docs/FORMALIZATION.md); logs under [`evidence/lean/`](evidence/lean/).

| Check | Result |
|---|---|
| Lean 4 / Mathlib proof of the theorem from the definitions: `patternSeries_reorder`, `avoiderCount_reorder`, `layeredSeries_reorder`, `layeredCount_reorder`, the recurrence `combinatorialWeightedRecurrence` and its reduced-pattern form `reducedWeightedRecurrence` | `lake build` exits 0 with no `sorry` ([`evidence/lean/build.log`](evidence/lean/build.log)) |
| Axiom audit of the final theorems and of the principal intermediate declarations (foundation, Guibert bijections, containment lemmas, reduction, series identities, algebraic core) | Every audited declaration depends only on `propext`, `Classical.choice`, `Quot.sound` ([`evidence/lean/axioms.log`](evidence/lean/axioms.log)) |
| Source audit of every Lean file for `sorry`, `admit`, `axiom` and `native_decide` outside comments and strings | None present |
| Executable Lean enumeration from the formal definitions, all permutations of length ≤ 5 (`CombinatoricsChecks`): distribution of two-cycles over 3412-avoiding involutions, and the avoidance counts for the patterns 12 and 21 | Two-cycle rows 1; 1; 1, 1; 1, 3; 1, 6, 2; 1, 10, 10 (totals 1, 1, 2, 4, 9, 21, the Motzkin numbers); for 12 only the decreasing involution of each length survives, for 21 only the identity; recorded in [`evidence/lean/checks.log`](evidence/lean/checks.log) |
| Kernel-checked (`decide`) examples: one-line words of `wrap`, of the Guibert constructors and of list direct sums; reductions of 312, 231, 21, 12, 321 and 3412; small containment instances | All checked at compile time |
| Exact enumeration, layered: all 255 compositions with a₁+⋯+a_k ≤ 8, n ≤ 16, two independent object generators (non-crossing partial matchings; all involutions with a literal four-entry 3412 filter) | Identical counts by (n, r) across all orderings and between generators ([`evidence/literal/`](evidence/literal/)) |
| Exact enumeration, layered, odd layers: 34 orderings of (1,2,3), (1,1,3), (1,3,3), (2,3,4), (1,2,2,3), (1,1,1,2), n ≤ 22 (400 763 223 3412-avoiding involutions of length 22) | Identical counts by (n, r) across orderings; n = 22 alone took 67.9 s on 16 threads ([`evidence/literal/B.log`](evidence/literal/B.log)) |
| Counts vs. an independent integer implementation of the pole-free recurrence (46 206 coefficient rows, 23 283 distinct cells) | No discrepancy; negative control (weight x² instead of x²y) detected |
| Layered-pattern detector for n > 10 vs. literal subsequence tests on all 3412-avoiding involutions of length ≤ 10 | Agree |
| Independent enumerator, all compositions with sum ≤ 7, n ≤ 10 | Agrees |
| General indecomposable summands, brute force from the definitions, n ≤ 10: all 171 unordered pairs of the 18 indecomposables of length ≤ 4; all 35 multisets of three of length ≤ 3, all orderings | 0 failures ([`data/blocks_symmetry_n10.json`](data/blocks_symmetry_n10.json)) |
| Independent program, 25 patterns with general summands, n ≤ 10 (the manuscript reports the earlier run to n ≤ 9) | 0 discrepancies |
| Exact symbolic identities (AR − qRER = E⁻¹, AW − qW² = I, AW = WA, W = p(A), moments, R_1k = p(s), symmetry under all k! orders, denominators only 1 − q c_a c_b), FLINT backend, k ≤ 6 (873 orderings) | PASS, 142.1 s with 16 workers ([`evidence/algebra/exact-k6.log`](evidence/algebra/exact-k6.log)) |
| Core matrix, interpolation, valid-range moment, denominator and symmetry checks with an independent SymPy backend, k ≤ 4 (33 orders) | PASS |
| FLINT negative control at moment t = k and repeated-node specialization for k = 3, 4 | PASS |
| SHA-256 and byte size of the manuscript source and compiled PDF | Recorded in [`MANIFEST.json`](MANIFEST.json) |

The finite checks do not prove anything for arbitrary n or k; they test the recurrence, the algebra and the generalization to non-layered summands at small sizes, and they test that the formal definitions enumerate the intended objects.


## Reproducing

Exact commands with measured run times: [`reproduce.md`](reproduce.md); per-component requirements and expected outputs: [`docs/REPRODUCING.md`](docs/REPRODUCING.md).

```sh
# Lean (from lean/): builds the formal proof and prints the axiom audit
cd lean && lake exe cache get && lake build && lake env lean EggeMansour/Audit.lean && cd ..
# Enumeration (domains A, G to n = 16; B to n = 22) and recurrence comparison
bash src/verification/run.sh results/literal
# Exact generic identities, k <= 6 (needs python-flint==0.9.0)
python3 src/verification/algebra_flint.py --max-k 6 --workers 16 --output results/algebra/exact-k6.json
# Integrity of the distributed data
sha256sum -c evidence/SHA256SUMS
```

| Step | Measured wall time |
|---|---|
| `lake build` and the axiom audit (Mathlib dependencies prebuilt) | recorded in [`reproduce.md`](reproduce.md) and [`evidence/lean/timings.json`](evidence/lean/timings.json) |
| `run.sh`: compile, self-test, A and G to n = 16, B to n = 22, comparison | 118.7 s |
| `algebra_flint.py --max-k 6` (16 workers) | 142.1 s |
| Independent checks in `src/review/` and `src/general/blocks_all.py 10` | 21.6 s in total |

Times were measured on an AMD Ryzen 7 8845HS (8 cores, 16 hardware threads, 48 GB RAM) under Linux; the computations are CPU-only (an RTX 5090 was available but is not used). The time to download the Mathlib cache depends on the network and was not measured.

## Citation, licence, provenance

- Cite with [`CITATION.cff`](CITATION.cff); please also cite Egge–Mansour 2006 and Egge 2004.
- Code (`src/`, `lean/`): MIT, see [`LICENSE`](LICENSE). Manuscript, documentation, data and logs: CC BY 4.0, see [`LICENSE-DATA.md`](LICENSE-DATA.md).
- How this was produced and what is independent: [`docs/AI_AND_PROVENANCE.md`](docs/AI_AND_PROVENANCE.md). Status: [`docs/STATUS.md`](docs/STATUS.md).
- Errors, missing hypotheses or equivalent earlier results can be reported with the [mathematical review issue template](.github/ISSUE_TEMPLATE/mathematical_review.md).

## Project credit

Project initiation and coordination: **[@AIOvernight](https://x.com/AIOvernight)**.

*A night full of tokens + RTX 5090*
