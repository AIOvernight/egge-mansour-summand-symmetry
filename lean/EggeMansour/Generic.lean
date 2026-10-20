import EggeMansour.Centralizer
import EggeMansour.Bidiagonal

noncomputable section

namespace EggeMansour

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The matrix Riccati identity forces commutation. Finite square matrices admit
no proper one-sided inverses, so no diagonal nonvanishing hypothesis is needed. -/
theorem commute_of_riccati (A W : Matrix (Fin n) (Fin n) K) (q : K)
    (h : A * W - q • (W * W) = 1) : Commute A W := by
  have hleft : (A - q • W) * W = 1 := by
    simpa only [sub_mul, smul_mul_assoc] using h
  have hright : W * (A - q • W) = 1 := mul_eq_one_comm.mp hleft
  have hr : W * A - q • (W * W) = 1 := by
    simpa only [mul_sub, mul_smul_comm] using hright
  exact sub_left_inj.mp (h.trans hr.symm)

/-- The diagonal of a product of two upper triangular matrices is the product
of the diagonals. -/
theorem diagonal_mul_of_upper {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hij
    · rw [hA hji, zero_mul]
    · rw [hB hij, mul_zero]
  · simp

/-- Polynomial evaluation preserves upper triangularity. -/
theorem aeval_upper {A : Matrix (Fin n) (Fin n) K}
    (hA : A.IsUpperTriangular) (p : K[X]) :
    (aeval A p).IsUpperTriangular := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simpa only [map_add] using hp.add hr
  | monomial k a =>
    simpa only [aeval_monomial] using (Matrix.blockTriangular_algebraMap a).mul (hA.pow k)

/-- Polynomial evaluation acts entrywise on the diagonal of a triangular matrix. -/
theorem diagonal_aeval {A : Matrix (Fin n) (Fin n) K}
    (hA : A.IsUpperTriangular) (p : K[X]) (i : Fin n) :
    (aeval A p) i i = p.eval (A i i) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simp only [map_add, Matrix.add_apply, eval_add, hp, hr]
  | monomial k a =>
    have hpow : ∀ k : ℕ, (A ^ k) i i = A i i ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k hk =>
        rw [pow_succ, diagonal_mul_of_upper (hA.pow k) hA, hk, pow_succ]
    simp [aeval_monomial, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul, hpow]

/-- The unique interpolation polynomial on the unordered node-value data. -/
def interpolant (α c : Fin n → K) : K[X] :=
  Lagrange.interpolate Finset.univ α c

theorem interpolant_eval (α c : Fin n → K) (hα : Function.Injective α) (i : Fin n) :
    (interpolant α c).eval (α i) = c i := by
  exact Lagrange.eval_interpolate_at_node c (fun _ _ _ _ h => hα h) (Finset.mem_univ i)

theorem interpolant_degree_lt (α c : Fin n → K) (hα : Function.Injective α) :
    (interpolant α c).degree < n := by
  simpa only [interpolant, Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt c (s := Finset.univ) (fun _ _ _ _ h => hα h)

/-- Simultaneously permuting the nodes and values leaves the interpolant unchanged. -/
theorem interpolant_perm (α c : Fin n → K) (hα : Function.Injective α)
    (ρ : Equiv.Perm (Fin n)) :
    interpolant (α ∘ ρ) (c ∘ ρ) = interpolant α c := by
  apply Lagrange.eq_interpolate_of_eval_eq
  · exact fun _ _ _ _ h => hα h
  · simpa only [Finset.card_univ, Fintype.card_fin] using
      interpolant_degree_lt (α ∘ ρ) (c ∘ ρ) (hα.comp ρ.injective)
  · intro i _
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      interpolant_eval (α ∘ ρ) (c ∘ ρ) (hα.comp ρ.injective) (ρ.symm i)

/-- A matrix commutes with every polynomial evaluated at that matrix. -/
theorem commute_aeval (A : Matrix (Fin n) (Fin n) K) (p : K[X]) :
    Commute A (aeval A p) := by
  simpa only [aeval_X] using (Commute.all (X : K[X]) p).map (aeval A)

/-- Any finite collection of moment identities gives the corresponding
polynomial endpoint evaluation identity. -/
theorem aeval_mulVec_one_eq_eval (A : Matrix (Fin n) (Fin n) K)
    (s : K) (i : Fin n) (p : K[X]) (hp : p.degree < n)
    (hmoment : ∀ t : ℕ, t < n → (A ^ t *ᵥ (fun _ => 1)) i = s ^ t) :
    (aeval A p *ᵥ (fun _ => 1)) i = p.eval s := by
  classical
  by_cases hp0 : p = 0
  · subst p
    simp
  have hpdeg : p.natDegree < n := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec, Finset.sum_apply,
    Polynomial.eval_eq_sum_range]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
    hmoment t (lt_of_lt_of_le (Finset.mem_range.mp ht) hpdeg)]

/-- The Riccati solution with a prescribed diagonal is the interpolation
polynomial evaluated at the coefficient matrix. -/
theorem riccati_eq_aeval_interpolant (A W : Matrix (Fin n) (Fin n) K)
    (q : K) (c : Fin n → K)
    (hA : A.IsUpperTriangular) (hW : W.IsUpperTriangular)
    (hα : Function.Injective (fun i => A i i))
    (hdiag : ∀ i, W i i = c i)
    (hRic : A * W - q • (W * W) = 1) :
    W = aeval A (interpolant (fun i => A i i) c) := by
  apply centralizer_eq_of_diag_eq hA hW (aeval_upper hA _) hα
    (commute_of_riccati A W q hRic) (commute_aeval A _)
  intro i
  rw [diagonal_aeval hA, interpolant_eval _ _ hα, hdiag]

/-- The generic endpoint theorem, before the recurrence-to-matrix adapter.
All hypotheses here are the exact matrix consequences proved from the uniform
recurrence; distinctness is confined to the generic field. -/
theorem riccati_first_row_eq_interpolant (α c : Fin n → K) (q s : K)
    (W : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (hα : Function.Injective α) (hW : W.IsUpperTriangular)
    (hdiag : ∀ i, W i i = c i)
    (hRic : bidiagonal α s * W - q • (W * W) = 1) :
    (W *ᵥ (fun _ => 1)) ⟨0, hn⟩ = (interpolant α c).eval s := by
  have hA : (bidiagonal α s).IsUpperTriangular := by
    intro i j hji
    have hne : i ≠ j := ne_of_gt hji
    have hnext : i.val + 1 ≠ j.val := by
      have : j.val < i.val := hji
      omega
    simp [bidiagonal, hne, hnext]
  have hAdiag : (fun i => bidiagonal α s i i) = α := by
    funext i
    simp [bidiagonal]
  have hEq := riccati_eq_aeval_interpolant (bidiagonal α s) W q c hA hW
    (by simpa only [hAdiag] using hα) hdiag hRic
  rw [hAdiag] at hEq
  rw [hEq]
  apply aeval_mulVec_one_eq_eval _ _ _ _ (interpolant_degree_lt α c hα)
  intro t ht
  exact bidiagonal_pow_mulVec_one_apply α s t ⟨0, hn⟩ (by simpa using ht)

/-- Simultaneously permuting the diagonal data of two Riccati systems leaves
their full first-row sums unchanged. -/
theorem riccati_first_row_perm (α c : Fin n → K) (q s : K)
    (W V : Matrix (Fin n) (Fin n) K) (hn : 0 < n)
    (ρ : Equiv.Perm (Fin n)) (hα : Function.Injective α)
    (hW : W.IsUpperTriangular) (hV : V.IsUpperTriangular)
    (hdiagW : ∀ i, W i i = c i) (hdiagV : ∀ i, V i i = c (ρ i))
    (hRicW : bidiagonal α s * W - q • (W * W) = 1)
    (hRicV : bidiagonal (α ∘ ρ) s * V - q • (V * V) = 1) :
    (W *ᵥ (fun _ => 1)) ⟨0, hn⟩ = (V *ᵥ (fun _ => 1)) ⟨0, hn⟩ := by
  rw [riccati_first_row_eq_interpolant α c q s W hn hα hW hdiagW hRicW,
    riccati_first_row_eq_interpolant (α ∘ ρ) (c ∘ ρ) q s V hn
      (hα.comp ρ.injective) hV hdiagV hRicV,
    interpolant_perm α c hα ρ]

end EggeMansour
