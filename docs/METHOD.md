# Method

This is a self-contained summary of the proof in [`paper/manuscript.pdf`](../paper/manuscript.pdf) (Sections 2–5). Numbers in brackets refer to the manuscript. Conventions are those of the README: 𝓘 is the set of 3412-avoiding involutions (empty one included), F_τ = Σ_{σ∈𝓘, σ avoids τ} x^{|σ|} y^{tc(σ)} ∈ ℤ[y][[x]], F_∅ = 0, and throughout

  q = x²y,  s = 1 − x.

## 1. Decomposition and containment

**Guibert's decomposition** [Lemma 2.1]. Every nonempty σ ∈ 𝓘 is uniquely either 1 ⊕ v or (1 ⊖ u ⊖ 1) ⊕ v with u, v ∈ 𝓘, and every such permutation lies in 𝓘. The outer two-cycle of the second form contributes the weight q = x²y; the fixed point of the first form contributes x.

*Reason.* If σ(1) = m ≥ 2, then σ(m) = 1; an index 1 < i < m with σ(i) = j > m would give the entries m, j, 1, i at positions 1 < i < m < j, an occurrence of 3412. So σ maps {2, …, m−1} to itself.

**Reduction** [Egge–Mansour 2006, Definition 3.2]. For a permutation τ, the reduction τ̄ deletes the first entry if it is the maximum and the last entry if it is the minimum, then standardizes. For example 1̄ = ∅, [a]‾ = [a−2] for a ≥ 2 (with [0] = ∅), and (312)‾ = 12.

**Containment lemma** [Lemma 2.2]. Let π = τ₁ ⊕ ⋯ ⊕ τ_m with indecomposable τ_i.

- (a) τ ⊕ v contains π iff for some t, τ contains τ₁ ⊕ ⋯ ⊕ τ_t and v contains τ_{t+1} ⊕ ⋯ ⊕ τ_m (an indecomposable summand cannot be split across a direct sum).
- (b) 1 ⊖ u ⊖ 1 contains τ iff u contains τ̄.
- (c) If m ≥ 2 then π̄ = π.
- (d) If τ₁ ≠ 1, 1 ⊕ v contains π iff v contains π; if τ₁ = 1, iff v contains τ₂ ⊕ ⋯ ⊕ τ_m.

## 2. The weighted recurrence

Fix indecomposable τ₁, …, τ_k and write F_ij = F_{τ_i⊕⋯⊕τ_j} for i ≤ j, c_i = F_ii = F_{τ_i}, h_i = F_{τ̄_i}, and F_{i+1,i} = 0 (empty interval).

**Egge–Mansour recurrence** [Proposition 2.3 = Egge–Mansour 2006, Theorem 3.3]. For 1 ≤ i ≤ j ≤ k,

  F_ij = 1 + x B_ij + q h_i F_ij + q (F_{i,i+1} − h_i) F_{i+1,j} + q Σ_{r=i+2}^{j} (F_ir − F_{i,r−1}) F_rj,

where B_ij = F_ij if τ_i ≠ 1 and B_ij = F_{i+1,j} if τ_i = 1. The constant 1 counts the empty involution, x B_ij counts the class 1 ⊕ v, and the q-weighted terms partition the class (1 ⊖ u ⊖ 1) ⊕ v by the longest prefix τ_i ⊕ ⋯ ⊕ τ_{i+t−1} contained in 1 ⊖ u ⊖ 1.

**Single summand** [(3), (4)]. c_i = 1 if τ_i = 1, and c_i = 1/(s − q h_i) otherwise; every c_i has constant term 1, and q h_i = s − c_i⁻¹ when τ_i ≠ 1.

**Uniform pole-free form** [Proposition 2.4]. Solving for the leading occurrence of F_ij removes the case distinction τ_i = 1 / τ_i ≠ 1: for i < j,

  (1 − q c_i c_j) F_ij = c_i + (1 − s c_i) F_{i+1,j} + q c_i Σ_{r=i+1}^{j−1} F_ir (F_rj − F_{r+1,j}).    (U)

Since 1 − q c_i c_j has constant term 1, (U) determines every F_ij from c₁, …, c_k alone. For k = 2,

  F_{τ₁⊕τ₂} = (c₁ + c₂ − s c₁c₂) / (1 − q c₁c₂),

which is visibly symmetric. (For τ₁ = τ₂ = 1 this is (1 + x)/(1 − x²y), the decreasing involutions; note F_{[1,1]} ≠ F_{[2]} = 1/(1−x) as bivariate series although they agree at y = 1.)

## 3. The generic problem: Riccati identity and interpolation

Now let q, s, c₁, …, c_k be independent indeterminates, K = ℚ(q, s, c₁, …, c_k), and

  L = ℤ[q, s, c₁, …, c_k][(1 − q c_i c_j)⁻¹ : i < j] ⊂ K.

Define R_ii = c_i, R_{i+1,i} = 0, and R_ij for i < j by (U) with R in place of F [Definition 3.1]. By induction every R_ij lies in L [Lemma 3.2].

**Matrices.** R is the upper triangular k × k matrix (R_ij); S is the superdiagonal shift; E = I − S, so E⁻¹ is the upper triangular all-ones matrix. Put

  α_i = c_i⁻¹ + q c_i,  A = upper bidiagonal with A_ii = α_i, A_{i,i+1} = s − α_i.

**Riccati identity** [Lemma 3.3, (10), (11)]. AR − qRER = E⁻¹. With W = RE (so W_ii = c_i) this becomes

  AW − qW² = I,

hence A = qW + W⁻¹ and AW = WA.

**Interpolation** [(12), (13), Lemma 3.4]. For i ≠ j,

  α_i − α_j = (c_j − c_i)(1 − q c_i c_j) / (c_i c_j) ≠ 0 in K,

so there is a unique p ∈ K[z] of degree ≤ k − 1 with p(α_i) = c_i. Both W and p(A) are upper triangular with diagonal (c_i) and commute with A; their difference is strictly upper triangular and commutes with a bidiagonal matrix with distinct diagonal entries, hence vanishes (induction on the distance from the diagonal). So **W = p(A)**.

**Moments** [Lemma 3.5]. Every row of A except the last sums to s, so A𝟙 = s𝟙 + (α_k − s)e_k, and since Aᵘe_k is supported on rows k−u, …, k, one gets e₁ᵀ Aᵗ 𝟙 = sᵗ for 0 ≤ t ≤ k − 1. The bound is sharp.

**Generic theorem** [Theorem 3.6]. Since the last column of E⁻¹ is 𝟙,

  R_1k = e₁ᵀ W 𝟙 = e₁ᵀ p(A) 𝟙 = p(s).

The interpolation data {(α_i, c_i)} form an unordered set, so the permutation automorphism c_i ↦ c_{ρ(i)} of K fixes p, hence fixes R_1k = p(s). As both sides lie in L, the identity ρ*(R_1k) = R_1k holds in L.

In Lagrange form R_1k = Σ_i c_i Π_{j≠i} (s − α_j)/(α_i − α_j). This has denominators α_i − α_j, which is why membership of R_1k in L (denominators only 1 − q c_i c_j) is the essential point for the next step.

## 4. Specialization

The homomorphism q ↦ x²y, s ↦ 1 − x, c_i ↦ F_{τ_i} from ℤ[q, s, c] to ℤ[y][[x]] sends each 1 − q c_i c_j to a series with constant term 1, hence to a unit; by the universal property of localization it extends uniquely to φ : L → ℤ[y][[x]] [(15)]. Applying φ to the defining recurrence and using uniqueness of solutions of (U) gives φ(R_ij) = F_ij [Lemma 4.1]. For the reordered sequence the corresponding map is φ ∘ ρ*, so

  F_{τ_{ρ(1)}⊕⋯⊕τ_{ρ(k)}} = φ(ρ* R_1k) = φ(R_1k) = F_{τ₁⊕⋯⊕τ_k}.

**Why nothing else is needed** [Remark 4.2]. No distinctness hypothesis α_i ≠ α_j or c_i ≠ c_j is used after the generic theorem: it is an identity in L, and φ is defined on all of L. Repeated summands, summands with equal series, and summands equal to 1 (where c_i = 1 and h_i = 0) need no separate argument. The substitutions y = 0, 1, −1 are ring homomorphisms ℤ[y][[x]] → ℤ[[x]] applied afterwards. (Check at y = 0: R_1k collapses to (1 − Π_i (1 − s c_i))/s, giving (1 − x^k)/(1 − x) when all layers are 1 and 1/(1 − x) otherwise, as it should.)

The Lean formalization follows the same route with two implementation choices that do not weaken the conclusion: commutation of W and A is obtained from the one-sided-inverse theorem for square matrices, and the universal ring has countably many block variables with all factors 1 − q c_i c_j inverted. See [`docs/FORMALIZATION.md`](FORMALIZATION.md).

## 4a. How Sections 1–2 are formalized

The combinatorial part (Sections 1–2 above) is formalized as follows; the declaration names are in [`docs/FORMALIZATION.md`](FORMALIZATION.md).

- **Decomposition.** For σ ∈ 𝓘 with σ(1) = m > 1, a crossing arc a < b < σ(a) < σ(b) would give the occurrence σ(a) σ(b) a b of 3412; hence positions strictly between 1 and m are mapped among themselves. The two forms of Lemma 2.1 are realized as explicit bijections v ↦ 1 ⊕ v and (u, v) ↦ (1 ⊖ u ⊖ 1) ⊕ v onto the involutions whose first value is 1, respectively m, and every nonempty σ ∈ 𝓘 is in exactly one image.
- **Containment.** An occurrence of an indecomposable pattern in σ ⊕ v lies entirely in one summand, so for a direct sum of indecomposable blocks the occurrence is cut at a block boundary (Lemma 2.2(a)). Lemma 2.2(b) is proved for every pattern τ through four lemmas about a host beginning with its maximum or ending with its minimum; the last-entry lemmas are obtained from the first-entry ones by inverting both permutations.
- **Partition.** Containment of the prefixes τ_i ⊕ ⋯ ⊕ τ_{i+t−1} in 1 ⊖ u ⊖ 1 is downward closed in t, so the largest such t is well defined; the cells t(u) = t are disjoint, and (1 ⊖ u ⊖ 1) ⊕ v avoids the pattern iff v avoids the suffix from t on. This writes 𝓘(π) as the disjoint union of {∅}, the fixed-point class and the paired cells.
- **Weights.** Generic lemmas turn disjoint unions, differences and direct-sum products of families of permutations, and the two injective constructors (length +1, weight unchanged; length +2, one more two-cycle), into identities between coefficient-defined series. The result is the recurrence of Proposition 2.3 in a list form; re-indexing gives the interval form that the algebraic development takes as its interface. The block parameter is first defined as the series of the u with 1 ⊖ u ⊖ 1 avoiding τ_i (so that h_i = 0 for τ_i = 1 is immediate) and then identified with F_{τ̄_i} by Lemma 2.2(b).

## 5. Consequences and the even-layer case

- y = 1 gives the ordinary symmetry (Egge 2004, Conjecture 6.9) [Corollary 5.1]; y = −1 gives the signed and parity-refined versions (Egge–Mansour arXiv:math/0401217v1, Conjectures 4.17–4.18) [Corollary 5.3].
- π ⊖ 1 ends with its minimum, hence is indecomposable, so F_{[m₁,…,m_k]⊕(π⊖1)} is symmetric in the m_i for every π (the 3412 half of the July 2026 conjecture of Burstein, Egge and Elizalde, bivariate and with π unrestricted) [Corollary 5.2].
- When c₁, …, c_k are pairwise distinct, the Lagrange formula holds in the fraction field of ℤ[y][[x]] [Corollary 5.4]; with coincidences, the value is still φ(R_1k).

**All layers even** [Proposition 5.5, Remark 5.6]. If all a_i are even, then F_{[a₁,…,a_k]}(x, y) = (1 − x)⁻¹ H_a(x²y/(1 − x)²) for a series H_a ∈ ℤ[[z]] counting fixed-point-free members by two-cycles, so the bivariate series is determined by its value at y = 1. Egge's transfer theorem (2007, Theorem 3.3) relates the y = 1 series for [2l₁, …, 2l_m] to 312-avoiding permutations avoiding [l₁, …, l_m], and Albert–Bouvel (2015, Definition 7 rule (3) and Theorem 8) shows that reordering atoms of a forbidden arch system preserves the enumeration of 231-avoiders (equivalently, after inversion, 312-avoiders). Together these imply the all-even case of Conjecture 3.14. The content not covered by these sources is the case with at least one odd layer and k ≥ 3, and the extension to non-layered summands.

## What the proof does not give

No bijection between the avoidance classes, and no information on statistics beyond length and number of two-cycles (which determine the number of fixed points and the sign).
