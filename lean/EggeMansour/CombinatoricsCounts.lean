import EggeMansour.Combinatorics

namespace EggeMansour.Combinatorics

open scoped BigOperators

theorem coeff_avoiderPolynomial {k : ℕ} (τ : Perm k) (n t : ℕ) :
    (avoiderPolynomial τ n).coeff t = (avoiderCount τ n t : ℤ) := by
  classical
  simp only [avoiderPolynomial, Polynomial.finsetSum_coeff,
    avoiderCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : IsAvoidingInvolution σ ∧ Avoids σ τ
  · simp only [ite_eq_left h, Polynomial.coeff_X_pow]
    simp [h.1, h.2, eq_comm]
  · simp only [ite_eq_right h, Polynomial.coeff_zero]
    simp only [show ¬ (IsAvoidingInvolution σ ∧ Avoids σ τ ∧ twoCycles σ = t) from
      fun h' => h ⟨h'.1, h'.2.1⟩, ↓reduceIte]

/-- The coefficient of `x^n y^t` is the finite count on actual permutations. -/
theorem coeff_coeff_avoiderSeries {k : ℕ} (τ : Perm k) (n t : ℕ) :
    (PowerSeries.coeff n (avoiderSeries τ)).coeff t = (avoiderCount τ n t : ℤ) := by
  rw [coeff_avoiderSeries, coeff_avoiderPolynomial]

@[simp] theorem contains_singleton_iff {n : ℕ} (σ : Perm n) :
    Contains σ singleton ↔ 0 < n := by
  constructor
  · intro h
    exact contains_length_le h
  · intro hn
    refine ⟨fun _ => ⟨0, hn⟩, ?_, ?_⟩
    · intro i j hij
      exact (not_lt_of_ge (Subsingleton.elim j i).le hij).elim
    · intro i j
      have hij : i = j := Subsingleton.elim _ _
      simp [hij]

theorem contains_directSum_left {m n : ℕ} (σ : Perm m) (τ : Perm n) :
    Contains (directSum σ τ) σ := by
  refine ⟨Fin.castAdd n, ?_, ?_⟩
  · intro i j hij
    exact hij
  · intro i j
    simp only [directSum_castAdd]
    rfl

theorem contains_directSum_right {m n : ℕ} (σ : Perm m) (τ : Perm n) :
    Contains (directSum σ τ) τ := by
  refine ⟨Fin.natAdd m, ?_, ?_⟩
  · intro i j hij
    simpa using hij
  · intro i j
    simp

theorem directSum_not_isIndecomposable {m n : ℕ} (σ : Perm m) (τ : Perm n)
    (hm : 0 < m) (hn : 0 < n) : ¬ IsIndecomposable (directSum σ τ) := by
  intro h
  obtain ⟨i, hi, hv⟩ := h.2 ⟨m, by omega⟩ hm
  have heq : i = Fin.castAdd n ⟨i.val, hi⟩ := Fin.ext rfl
  rw [heq, directSum_castAdd] at hv
  exact (Nat.not_le_of_gt (σ ⟨i.val, hi⟩).isLt) hv

@[simp] theorem twoCycles_directSum {m n : ℕ} (σ : Perm m) (τ : Perm n) :
    twoCycles (directSum σ τ) = twoCycles σ + twoCycles τ := by
  simp only [twoCycles, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [directSum_castAdd]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    simp

/-- The lower-endpoint definition is exactly half the moved-point count. -/
theorem two_mul_twoCycles {n : ℕ} (σ : Perm n) (hσ : IsInvolution σ) :
    2 * twoCycles σ = (Finset.univ.filter (fun i => σ i ≠ i)).card := by
  let lo := Finset.univ.filter (fun i => i < σ i)
  let hi := Finset.univ.filter (fun i => σ i < i)
  have hcard : lo.card = hi.card := by
    apply Finset.card_equiv σ
    intro i
    simp only [lo, hi, Finset.mem_filter, Finset.mem_univ, true_and, hσ i]
  have hdisj : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro i hli hhi
    exact (not_lt_of_ge (Finset.mem_filter.mp hli).2.le) (Finset.mem_filter.mp hhi).2
  have hunion : lo ∪ hi = Finset.univ.filter (fun i => σ i ≠ i) := by
    ext i
    simp only [lo, hi, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [← hunion, Finset.card_union_of_disjoint hdisj, ← hcard]
  simp only [lo, twoCycles, two_mul]

theorem twoCycles_le_half {n : ℕ} (σ : Perm n) (hσ : IsInvolution σ) :
    twoCycles σ ≤ n / 2 := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => σ i ≠ i)
  rw [← two_mul_twoCycles σ hσ] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

end EggeMansour.Combinatorics
