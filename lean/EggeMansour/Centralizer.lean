import Mathlib.LinearAlgebra.Matrix.Block

namespace EggeMansour

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}

/-- An upper triangular matrix with zero diagonal which commutes with an upper
triangular matrix having distinct diagonal entries must vanish.  The proof is
induction on the distance above the diagonal. -/
theorem centralizer_eq_zero_of_diag_zero
    {A X : Matrix (Fin n) (Fin n) R}
    (hA : A.IsUpperTriangular) (hX : X.IsUpperTriangular)
    (hdiag : Function.Injective (fun i => A i i))
    (hcomm : Commute A X) (hzero : ∀ i, X i i = 0) : X = 0 := by
  classical
  have hentry : ∀ d : ℕ, ∀ i j : Fin n, j.val - i.val = d → X i j = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hd
      by_cases hij : i = j
      · subst j
        exact hzero i
      by_cases hji : j < i
      · exact hX hji
      have hijlt : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
      have hleft : (A * X) i j = A i i * X i j := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_single i
        · intro k _ hki
          by_cases hki' : k < i
          · rw [hA hki', zero_mul]
          have hik : i < k := lt_of_le_of_ne (le_of_not_gt hki') (Ne.symm hki)
          have hsmall : j.val - k.val < d := by
            have : i.val < j.val := hijlt
            have : i.val < k.val := hik
            omega
          rw [ih (j.val - k.val) hsmall k j rfl, mul_zero]
        · simp
      have hright : (X * A) i j = X i j * A j j := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_single j
        · intro k _ hkj
          by_cases hjk : j < k
          · rw [hA hjk, mul_zero]
          have hkj' : k < j := lt_of_le_of_ne (le_of_not_gt hjk) hkj
          have hsmall : k.val - i.val < d := by
            have : i.val < j.val := hijlt
            have : k.val < j.val := hkj'
            omega
          rw [ih (k.val - i.val) hsmall i k rfl, zero_mul]
        · simp
      have heq : A i i * X i j = X i j * A j j := by
        rw [← hleft, ← hright]
        exact congrArg (fun M : Matrix (Fin n) (Fin n) R => M i j) hcomm.eq
      have hprod : (A i i - A j j) * X i j = 0 := by
        rw [sub_mul, heq, mul_comm (X i j), sub_self]
      exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (fun h => hij (hdiag h)))
  ext i j
  exact hentry (j.val - i.val) i j rfl

/-- Among upper triangular matrices commuting with a fixed upper triangular
matrix with distinct diagonal entries, the diagonal determines the matrix. -/
theorem centralizer_eq_of_diag_eq
    {A W V : Matrix (Fin n) (Fin n) R}
    (hA : A.IsUpperTriangular) (hW : W.IsUpperTriangular) (hV : V.IsUpperTriangular)
    (hdiag : Function.Injective (fun i => A i i))
    (hAW : Commute A W) (hAV : Commute A V)
    (hWV : ∀ i, W i i = V i i) : W = V := by
  apply sub_eq_zero.mp
  apply centralizer_eq_zero_of_diag_zero hA (hW.sub hV) hdiag
  · change A * (W - V) = (W - V) * A
    rw [mul_sub, sub_mul, hAW.eq, hAV.eq]
  · intro i
    simp only [Matrix.sub_apply, hWV i, sub_self]

end EggeMansour
