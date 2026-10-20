import EggeMansour.WrapContainment
import EggeMansour.PatternSums

/-!
# Actual wrapped-avoidance series

The recurrence parameter attached to a pattern counts the interior permutations
whose wraps avoid that pattern. The weight belongs to the interior; multiplication
by `seriesQ = x²y` accounts for the two new outer positions and their transposition.
No reduction map and no recurrence hypothesis occurs in these definitions.
-/

namespace EggeMansour.Combinatorics

open scoped BigOperators

noncomputable def wrappedPolynomial (p : Pattern) (n : ℕ) : Polynomial ℤ :=
  ∑ u : Perm n, if IsAvoidingInvolution u ∧ Avoids (wrap u) p.2 then
    Polynomial.X ^ twoCycles u else 0

noncomputable def wrappedSeries (p : Pattern) : EggeMansour.Series :=
  PowerSeries.mk (wrappedPolynomial p)

@[simp] theorem coeff_wrappedSeries (p : Pattern) (n : ℕ) :
    PowerSeries.coeff n (wrappedSeries p) = wrappedPolynomial p n := by
  simp [wrappedSeries]

@[simp] theorem wrappedSeries_empty : wrappedSeries ⟨0, empty⟩ = 0 := by
  ext n
  simp [wrappedPolynomial]

@[simp] theorem wrappedSeries_singleton : wrappedSeries ⟨1, singleton⟩ = 0 := by
  ext n
  simp [wrappedPolynomial, Avoids, contains_singleton_iff]

theorem wrappedSeries_directSum {a b : ℕ} (α : Perm a) (β : Perm b)
    (ha : 0 < a) (hb : 0 < b) :
    wrappedSeries ⟨a + b, directSum α β⟩ = avoiderSeries (directSum α β) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_wrappedSeries, coeff_avoiderSeries, wrappedPolynomial, avoiderPolynomial]
  apply Finset.sum_congr rfl
  intro u _
  simp only [avoids_wrap_directSum_iff u α β ha hb]

theorem wrappedSeries_patternSum (p q : Pattern) (hp : 0 < p.1) (hq : 0 < q.1) :
    wrappedSeries (patternSum p q) = patternSeries (patternSum p q) :=
  wrappedSeries_directSum p.2 q.2 hp hq

theorem wrappedSeries_of_size_one (p : Pattern) (hp : p.1 = 1) : wrappedSeries p = 0 := by
  rcases p with ⟨n, τ⟩
  dsimp only at hp
  subst n
  have hτ : τ = singleton := Subsingleton.elim _ _
  subst τ
  exact wrappedSeries_singleton

theorem sumPatterns_pos_of_head (p : Pattern) (ps : List Pattern) (hp : 0 < p.1) :
    0 < (sumPatterns (p :: ps)).1 := by
  rw [sumPatterns_cons]
  change 0 < p.1 + (sumPatterns ps).1
  omega

theorem wrappedSeries_sumPatterns_cons_cons (p q : Pattern) (ps : List Pattern)
    (hp : 0 < p.1) (hq : 0 < q.1) :
    wrappedSeries (sumPatterns (p :: q :: ps)) = patternSeries (sumPatterns (p :: q :: ps)) := by
  rw [sumPatterns_cons]
  exact wrappedSeries_directSum p.2 (sumPatterns (q :: ps)).2 hp
    (sumPatterns_pos_of_head q ps hq)

theorem wrappedSeries_sumPatterns (ps : List Pattern) (hlen : 2 ≤ ps.length)
    (hps : ∀ p ∈ ps, 0 < p.1) :
    wrappedSeries (sumPatterns ps) = patternSeries (sumPatterns ps) := by
  cases ps with
  | nil => simp at hlen
  | cons p ps =>
    cases ps with
    | nil => simp at hlen
    | cons q qs =>
      exact wrappedSeries_sumPatterns_cons_cons p q qs (hps p (by simp)) (hps q (by simp))

theorem avoids_of_length_lt {n k : ℕ} (σ : Perm n) (τ : Perm k) (h : n < k) :
    Avoids σ τ := by
  intro hc
  exact (Nat.not_le_of_gt h) (contains_length_le hc)

@[simp] theorem isAvoidingInvolution_empty : IsAvoidingInvolution empty := by
  constructor
  · intro i; exact Fin.elim0 i
  · exact avoids_of_length_lt _ _ (by decide)

@[simp] theorem twoCycles_empty : twoCycles empty = 0 := by
  simp [twoCycles]

theorem avoiderPolynomial_zero {k : ℕ} (τ : Perm k) (hk : 0 < k) :
    avoiderPolynomial τ 0 = 1 := by
  unfold avoiderPolynomial
  rw [Finset.sum_eq_single empty]
  · simp [avoids_of_length_lt empty τ hk]
  · intro σ _ hσ
    exact (hσ (Subsingleton.elim σ empty)).elim
  · intro h
    exact (h (Finset.mem_univ empty)).elim

theorem coeff_zero_avoiderSeries {k : ℕ} (τ : Perm k) (hk : 0 < k) :
    PowerSeries.coeff 0 (avoiderSeries τ) = 1 := by
  rw [coeff_avoiderSeries, avoiderPolynomial_zero τ hk]

theorem constantCoeff_avoiderSeries {k : ℕ} (τ : Perm k) (hk : 0 < k) :
    PowerSeries.constantCoeff (avoiderSeries τ) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_avoiderSeries τ hk

@[simp] theorem avoiderSeries_singleton : avoiderSeries singleton = 1 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [avoiderPolynomial_zero singleton (by decide)]
  · rw [coeff_avoiderSeries]
    simp [avoiderPolynomial, Avoids, contains_singleton_iff, hn]

end EggeMansour.Combinatorics
