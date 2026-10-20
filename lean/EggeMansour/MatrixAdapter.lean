import EggeMansour.Interfaces

noncomputable section
namespace EggeMansour
open scoped BigOperators
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

/-- The finite shift matrix, with ones just above the diagonal. -/
def shiftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i.val + 1 = j.val then 1 else 0

/-- Discrete first-difference matrix. -/
def differenceMatrix (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  1 - shiftMatrix (K := K) n

/-- The upper triangular matrix of ones. -/
def upperOnes (n : ℕ) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i ≤ j then 1 else 0

/-- Restrict an interval family to finite matrix indices. -/
def intervalMatrix (n : ℕ) (F : ℕ → ℕ → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => F i.val j.val

theorem shiftMatrix_mul (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (shiftMatrix (K := K) n * M) i j =
      if hi : i.val + 1 < n then M ⟨i.val + 1, hi⟩ j else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hi : i.val + 1 < n
  · rw [dite_eq_left hi]
    rw [Finset.sum_eq_single (⟨i.val + 1, hi⟩ : Fin n)]
    · simp [shiftMatrix]
    · intro k _ hk
      have hne : i.val + 1 ≠ k.val := by
        intro h
        apply hk
        exact Fin.ext h.symm
      simp [shiftMatrix, hne]
    · simp
  · rw [dite_eq_right hi]
    apply Finset.sum_eq_zero
    intro k _
    have hne : i.val + 1 ≠ k.val := by
      intro h
      exact hi (h ▸ k.isLt)
    simp [shiftMatrix, hne]

theorem mul_shiftMatrix (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (M * shiftMatrix (K := K) n) i j =
      if hj : 0 < j.val then M i ⟨j.val - 1, by omega⟩ else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hj : 0 < j.val
  · rw [dite_eq_left hj]
    rw [Finset.sum_eq_single (⟨j.val - 1, by omega⟩ : Fin n)]
    · simp [shiftMatrix, Nat.sub_add_cancel (by omega : 1 ≤ j.val)]
    · intro k _ hk
      have hne : k.val + 1 ≠ j.val := by
        intro h
        apply hk
        apply Fin.ext
        change k.val = j.val - 1
        omega
      simp [shiftMatrix, hne]
    · simp
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro k _
    have hne : k.val + 1 ≠ j.val := by omega
    simp [shiftMatrix, hne]

theorem differenceMatrix_mul (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (differenceMatrix (K := K) n * M) i j = M i j -
      (if hi : i.val + 1 < n then M ⟨i.val + 1, hi⟩ j else 0) := by
  simp only [differenceMatrix, sub_mul, one_mul, Matrix.sub_apply, shiftMatrix_mul]

theorem mul_differenceMatrix (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (M * differenceMatrix (K := K) n) i j = M i j -
      (if hj : 0 < j.val then M i ⟨j.val - 1, by omega⟩ else 0) := by
  simp only [differenceMatrix, mul_sub, mul_one, Matrix.sub_apply, mul_shiftMatrix]

theorem differenceMatrix_upperOnes :
    (differenceMatrix (K := K) n : Matrix (Fin n) (Fin n) K) * upperOnes (K := K) n = 1 := by
  ext i j
  rw [differenceMatrix_mul]
  simp only [upperOnes, Matrix.one_apply]
  split_ifs <;> simp_all only [Fin.le_def, Fin.ext_iff] <;> first | omega | ring

theorem upperOnes_differenceMatrix :
    (upperOnes (K := K) n : Matrix (Fin n) (Fin n) K) * differenceMatrix (K := K) n = 1 := by
  exact mul_eq_one_comm.mp differenceMatrix_upperOnes

/-- The bidiagonal matrix in the Riccati identity, in factorized form. -/
def riccatiMatrix (n : ℕ) (q s : K) (c : ℕ → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal (fun i => (c i.val)⁻¹ + q * c i.val) * differenceMatrix (K := K) n +
    s • shiftMatrix (K := K) n

theorem riccatiMatrix_mul (q s : K) (c : ℕ → K)
    (M : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    (riccatiMatrix n q s c * M) i j =
      ((c i.val)⁻¹ + q * c i.val) * M i j +
      (s - ((c i.val)⁻¹ + q * c i.val)) *
        (if hi : i.val + 1 < n then M ⟨i.val + 1, hi⟩ j else 0) := by
  simp only [riccatiMatrix, add_mul, Matrix.add_apply, mul_assoc,
    Matrix.diagonal_mul, differenceMatrix_mul, smul_mul_assoc,
    Matrix.smul_apply, smul_eq_mul, shiftMatrix_mul]
  ring

theorem intervalMatrix_upper {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) : (intervalMatrix n F).IsUpperTriangular := by
  intro i j hji
  exact hF.lower i.val j.val hji i.isLt

theorem shiftMatrix_upper : (shiftMatrix (K := K) n : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
  intro i j hji
  have hn : i.val + 1 ≠ j.val := by change j.val < i.val at hji; omega
  simp [shiftMatrix, hn]

theorem differenceMatrix_upper :
    (differenceMatrix (K := K) n : Matrix (Fin n) (Fin n) K).IsUpperTriangular := by
  exact Matrix.blockTriangular_one.sub shiftMatrix_upper

theorem riccatiMatrix_upper (q s : K) (c : ℕ → K) :
    (riccatiMatrix n q s c).IsUpperTriangular := by
  apply ((Matrix.blockTriangular_diagonal _).mul differenceMatrix_upper).add
  intro i j hji
  simp only [Matrix.smul_apply, shiftMatrix_upper hji, smul_zero]

/-- The successor row is zero at and below the current diagonal. -/
theorem intervalMatrix_next_zero {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (i j : Fin n) (hji : j ≤ i) :
    (if i.val + 1 < n then F (i.val + 1) j.val else 0) = 0 := by
  split_ifs with hi
  · exact hF.lower (i.val+1) j.val (by have := Fin.le_iff_val_le_val.mp hji; omega) hi
  · rfl

/-- Multiplication by the first-difference matrix expands the middle factor. -/
theorem intervalMatrix_product_sum (F : ℕ → ℕ → K) (i j : Fin n) :
    (intervalMatrix n F * differenceMatrix (K := K) n * intervalMatrix n F) i j =
      ∑ r ∈ Finset.range n, F i.val r *
        (F r j.val - if r + 1 < n then F (r + 1) j.val else 0) := by
  rw [mul_assoc, Matrix.mul_apply]
  simp only [differenceMatrix_mul, intervalMatrix]
  exact Fin.sum_univ_eq_sum_range
    (fun r => F i.val r * (F r j.val - if r + 1 < n then F (r+1) j.val else 0)) n

theorem intervalMatrix_product_sum_Icc {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (i j : Fin n) (_hij : i ≤ j) :
    (intervalMatrix n F * differenceMatrix (K := K) n * intervalMatrix n F) i j =
      ∑ r ∈ Finset.Icc i.val j.val, F i.val r *
        (F r j.val - if r + 1 < n then F (r + 1) j.val else 0) := by
  rw [intervalMatrix_product_sum]
  symm
  apply Finset.sum_subset
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    simp only [Finset.mem_range]
    omega
  · intro r hr hnot
    have hrn : r < n := Finset.mem_range.mp hr
    have hnot' : ¬ (i.val ≤ r ∧ r ≤ j.val) := by simpa only [Finset.mem_Icc] using hnot
    by_cases hri : r < i.val
    · rw [hF.lower i.val r hri i.isLt, zero_mul]
    · have hjr : j.val < r := by omega
      rw [hF.lower r j.val hjr hrn]
      split_ifs with hr1
      · rw [hF.lower (r+1) j.val (by omega) hr1]
        ring
      · ring

theorem intervalMatrix_product_offdiag {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (i j : Fin n) (hij : i < j) :
    (intervalMatrix n F * differenceMatrix (K := K) n * intervalMatrix n F) i j =
      c i.val * (F i.val j.val - F (i.val+1) j.val) +
      F i.val j.val * c j.val +
      ∑ r ∈ Finset.Ioo i.val j.val, F i.val r * (F r j.val - F (r+1) j.val) := by
  classical
  rw [intervalMatrix_product_sum_Icc hF i j hij.le]
  have hij' : i.val < j.val := hij
  have hi1 : i.val + 1 < n := by omega
  rw [← Finset.Ico_insert_right hij'.le, Finset.sum_insert (by simp),
    ← Finset.Ioo_insert_left hij', Finset.sum_insert (by simp)]
  have hjzero := intervalMatrix_next_zero hF j j le_rfl
  simp only [hF.diagonal i.val i.isLt, hF.diagonal j.val j.isLt,
    ite_eq_left hi1, hjzero, sub_zero]
  have hsum : (∑ r ∈ Finset.Ioo i.val j.val, F i.val r *
      (F r j.val - if r+1<n then F (r+1) j.val else 0)) =
      ∑ r ∈ Finset.Ioo i.val j.val, F i.val r * (F r j.val - F (r+1) j.val) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hrj := (Finset.mem_Ioo.mp hr).2
    rw [ite_eq_left (by omega : r+1<n)]
  rw [hsum]
  ring

theorem intervalMatrix_product_diag {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (i : Fin n) :
    (intervalMatrix n F * differenceMatrix (K := K) n * intervalMatrix n F) i i =
      c i.val * c i.val := by
  rw [intervalMatrix_product_sum_Icc hF i i le_rfl]
  simp only [Finset.Icc_self, Finset.sum_singleton, hF.diagonal i.val i.isLt]
  rw [intervalMatrix_next_zero hF i i le_rfl, sub_zero]

/-- The pole-free scalar recurrence is exactly the upper-triangular matrix identity. -/
theorem UniformRecurrence.matrix_identity {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (hc : ∀ i, i < n → c i ≠ 0) :
    riccatiMatrix n q s c * intervalMatrix n F -
      q • (intervalMatrix n F * differenceMatrix (K := K) n * intervalMatrix n F) =
      upperOnes (K := K) n := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      riccatiMatrix_mul, intervalMatrix, upperOnes, ite_eq_left hij.le]
    rw [intervalMatrix_product_offdiag hF i j hij]
    have hi1 : i.val+1<n := by have := j.isLt; change i.val<j.val at hij; omega
    rw [dite_eq_left hi1]
    have heq := hF.step i.val j.val hij j.isLt
    have hc' := hc i.val i.isLt
    field_simp
    linear_combination heq
  · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      riccatiMatrix_mul, intervalMatrix, upperOnes, ite_eq_left le_rfl, dite_eq_ite]
    rw [intervalMatrix_product_diag hF i, intervalMatrix_next_zero hF i i le_rfl,
      mul_zero, add_zero, hF.diagonal i.val i.isLt]
    have hc' := hc i.val i.isLt
    field_simp
    ring
  · have hR := intervalMatrix_upper hF
    have hA := riccatiMatrix_upper (n := n) q s c
    have hP := (hR.mul differenceMatrix_upper).mul hR
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      (hA.mul hR) hji, hP hji, mul_zero, sub_self,
      upperOnes, ite_eq_right (not_le_of_gt hji)]

/-- The matrix Riccati equation is a consequence of the explicit scalar recurrence. -/
theorem UniformRecurrence.matrix_riccati {q s : K} {c : ℕ → K} {F : ℕ → ℕ → K}
    (hF : UniformRecurrence n q s c F) (hc : ∀ i, i < n → c i ≠ 0) :
    riccatiMatrix n q s c * (intervalMatrix n F * differenceMatrix (K := K) n) -
      q • ((intervalMatrix n F * differenceMatrix (K := K) n) *
        (intervalMatrix n F * differenceMatrix (K := K) n)) = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M * differenceMatrix (K := K) n)
    (hF.matrix_identity hc)
  simpa only [sub_mul, smul_mul_assoc, mul_assoc, upperOnes_differenceMatrix] using h

end EggeMansour
