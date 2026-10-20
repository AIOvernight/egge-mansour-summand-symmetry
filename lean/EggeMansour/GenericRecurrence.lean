import EggeMansour.Generic
import EggeMansour.MatrixAdapter

noncomputable section
namespace EggeMansour
open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

/-- The factorized coefficient matrix of the interval recurrence is the
bidiagonal matrix used for interpolation. -/
theorem riccatiMatrix_eq_bidiagonal (q s : K) (c : ℕ → K) :
    riccatiMatrix n q s c =
      bidiagonal (fun i : Fin n => (c i.val)⁻¹ + q * c i.val) s := by
  classical
  ext i j
  simp only [riccatiMatrix, Matrix.add_apply, Matrix.diagonal_mul,
    differenceMatrix, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, shiftMatrix, bidiagonal]
  split_ifs with hij hnext <;> simp_all; ring

/-- Right multiplication by the difference matrix keeps the diagonal of an
upper triangular interval matrix. -/
theorem interval_difference_diagonal {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (i : Fin n) :
    (intervalMatrix n F * differenceMatrix (K := K) n) i i = c i.val := by
  rw [diagonal_mul_of_upper (intervalMatrix_upper hF) differenceMatrix_upper]
  simp only [intervalMatrix, hF.diagonal i.val i.isLt]
  simp [differenceMatrix, shiftMatrix]

/-- The full first-row sum of the difference matrix representation is the
full interval endpoint. -/
theorem interval_difference_first_row (k : ℕ) (F : ℕ → ℕ → K) :
    ((intervalMatrix (k + 1) F * differenceMatrix (K := K) (k + 1)) *ᵥ
      (fun _ => 1)) (0 : Fin (k + 1)) = F 0 k := by
  let W := intervalMatrix (k + 1) F * differenceMatrix (K := K) (k + 1)
  have hWU : W * upperOnes (K := K) (k + 1) = intervalMatrix (k + 1) F := by
    dsimp [W]
    rw [mul_assoc, differenceMatrix_upperOnes, mul_one]
  have hend := congrArg (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) K =>
    M 0 (Fin.last k)) hWU
  change (W *ᵥ (fun _ => 1)) 0 = F 0 k
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, upperOnes, intervalMatrix, Fin.le_last] using hend

/-- In the generic field, the uniform interval recurrence has the interpolation
value prescribed in manuscript Theorem 3.5. -/
theorem UniformRecurrence.eq_interpolant {k : ℕ} {q s : K} {c : ℕ → K}
    {F : ℕ → ℕ → K} (hF : UniformRecurrence (k + 1) q s c F)
    (hc : ∀ i, i < k + 1 → c i ≠ 0)
    (hα : Function.Injective (fun i : Fin (k + 1) => (c i.val)⁻¹ + q * c i.val)) :
    F 0 k = (interpolant (fun i : Fin (k + 1) => (c i.val)⁻¹ + q * c i.val)
      (fun i => c i.val)).eval s := by
  rw [← interval_difference_first_row k F]
  apply riccati_first_row_eq_interpolant _ _ q s _ (by omega) hα
  · exact (intervalMatrix_upper hF).mul differenceMatrix_upper
  · exact interval_difference_diagonal hF
  · rw [← riccatiMatrix_eq_bidiagonal]
    exact hF.matrix_riccati hc

/-- Generic symmetry: the uniform recurrence alone implies invariance under
all permutations, provided the generic interpolation nodes are distinct.
The localization module removes these generic-field restrictions. -/
theorem UniformRecurrence.generic_symmetry {k : ℕ} {q s : K} {c : ℕ → K}
    {F G : ℕ → ℕ → K} (ρ : Equiv.Perm (Fin (k + 1)))
    (hF : UniformRecurrence (k + 1) q s c F)
    (hG : UniformRecurrence (k + 1) q s (permuteParams ρ c) G)
    (hc : ∀ i, i < k + 1 → c i ≠ 0)
    (hα : Function.Injective (fun i : Fin (k + 1) => (c i.val)⁻¹ + q * c i.val)) :
    F 0 k = G 0 k := by
  let α : Fin (k + 1) → K := fun i => (c i.val)⁻¹ + q * c i.val
  let cv : Fin (k + 1) → K := fun i => c i.val
  have hcp : ∀ i, i < k + 1 → permuteParams ρ c i ≠ 0 := by
    intro i hi
    simpa only [permuteParams, dite_eq_left hi] using hc (ρ ⟨i, hi⟩).val (ρ ⟨i, hi⟩).isLt
  have hαp : (fun i : Fin (k + 1) =>
      (permuteParams ρ c i.val)⁻¹ + q * permuteParams ρ c i.val) = α ∘ ρ := by
    funext i
    simp only [permuteParams_apply, Function.comp_apply, α]
  have hcvp : (fun i : Fin (k + 1) => permuteParams ρ c i.val) = cv ∘ ρ := by
    funext i
    simp only [permuteParams_apply, Function.comp_apply, cv]
  have hαinj : Function.Injective α := hα
  rw [hF.eq_interpolant hc hα,
    hG.eq_interpolant hcp (by rw [hαp]; exact hαinj.comp ρ.injective),
    hαp, hcvp, interpolant_perm α cv hαinj ρ]

/-- Positive-size version convenient for localization transfer. -/
theorem UniformRecurrence.generic_symmetry_of_pos {q s : K} {c : ℕ → K}
    {F G : ℕ → ℕ → K} (hn : 0 < n) (ρ : Equiv.Perm (Fin n))
    (hF : UniformRecurrence n q s c F)
    (hG : UniformRecurrence n q s (permuteParams ρ c) G)
    (hc : ∀ i, i < n → c i ≠ 0)
    (hα : Function.Injective (fun i : Fin n => (c i.val)⁻¹ + q * c i.val)) :
    F 0 (n - 1) = G 0 (n - 1) := by
  cases n with
  | zero => omega
  | succ k => exact hF.generic_symmetry ρ hG hc hα

end EggeMansour
