import Mathlib

/-!
# Bidiagonal matrices: finite propagation and the moment identity

This file formalizes Lemma `lem:moments` of the manuscript (`paper/manuscript.tex`):
for the upper bidiagonal matrix `A` with `A i i = α i` and `A i (i+1) = s - α i`,
the first entry of `A ^ t *ᵥ 1` equals `s ^ t` for `t < n`.

The proof is by finite propagation: the entry `i` of `A ^ t *ᵥ v` depends only on the
entries `i, …, i + t` of `v`. Since `A *ᵥ 1` agrees with `s • 1` on every row `i` with
`i + 1 < n`, induction gives `(A ^ t *ᵥ 1) i = s ^ t` whenever `i + t < n`.
-/

noncomputable section

namespace EggeMansour

open Matrix

variable {K : Type*} [CommRing K] {n : ℕ}

/-- Upper bidiagonal matrix with diagonal `α` and superdiagonal `s - α`. -/
def bidiagonal (α : Fin n → K) (s : K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then α i else if i.val + 1 = j.val then s - α i else 0

theorem bidiagonal_apply (α : Fin n → K) (s : K) (i j : Fin n) :
    bidiagonal α s i j =
      if i = j then α i else if i.val + 1 = j.val then s - α i else 0 := rfl

/-- The entries of `bidiagonal α s` vanish outside the diagonal and superdiagonal. -/
theorem bidiagonal_apply_of_ne (α : Fin n → K) (s : K) {i j : Fin n}
    (h1 : i ≠ j) (h2 : i.val + 1 ≠ j.val) : bidiagonal α s i j = 0 := by
  simp [bidiagonal, h1, h2]

@[simp] theorem bidiagonal_apply_self (α : Fin n → K) (s : K) (i : Fin n) :
    bidiagonal α s i i = α i := by
  simp [bidiagonal]

/-- The diagonal of `bidiagonal α s` is `α`. -/
@[simp] theorem diag_bidiagonal (α : Fin n → K) (s : K) :
    Matrix.diag (bidiagonal α s) = α := by
  ext i
  simp [Matrix.diag]

theorem bidiagonal_apply_succ (α : Fin n → K) (s : K) (i j : Fin n)
    (h : i.val + 1 = j.val) : bidiagonal α s i j = s - α i := by
  have : i ≠ j := fun hij => by subst hij; omega
  simp [bidiagonal, this, h]

/-- Entries below the diagonal vanish. -/
theorem bidiagonal_apply_of_lt (α : Fin n → K) (s : K) {i j : Fin n} (h : j < i) :
    bidiagonal α s i j = 0 := by
  apply bidiagonal_apply_of_ne
  · exact fun hij => by subst hij; exact lt_irrefl _ h
  · have := Fin.lt_def.mp h; omega

/-- `bidiagonal α s` is upper triangular (Mathlib's `Matrix.IsUpperTriangular`). -/
theorem bidiagonal_isUpperTriangular (α : Fin n → K) (s : K) :
    (bidiagonal α s).IsUpperTriangular := by
  intro i j hij
  exact bidiagonal_apply_of_lt α s hij

/-- Row `i` of `bidiagonal α s *ᵥ v`: a sum of at most two terms. -/
theorem bidiagonal_mulVec_apply (α : Fin n → K) (s : K) (v : Fin n → K) (i : Fin n) :
    (bidiagonal α s *ᵥ v) i =
      α i * v i + ∑ j : Fin n, (if i.val + 1 = j.val then (s - α i) * v j else 0) := by
  classical
  simp only [mulVec, dotProduct, bidiagonal]
  have : ∀ j : Fin n,
      (if i = j then α i else if i.val + 1 = j.val then s - α i else 0) * v j =
        (if i = j then α i * v j else 0) +
          (if i.val + 1 = j.val then (s - α i) * v j else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Row `i` of `bidiagonal α s *ᵥ v` when `i + 1 < n`. -/
theorem bidiagonal_mulVec_apply_of_lt (α : Fin n → K) (s : K) (v : Fin n → K) (i : Fin n)
    (hi : i.val + 1 < n) :
    (bidiagonal α s *ᵥ v) i = α i * v i + (s - α i) * v ⟨i.val + 1, hi⟩ := by
  classical
  rw [bidiagonal_mulVec_apply]
  congr 1
  rw [Finset.sum_eq_single ⟨i.val + 1, hi⟩]
  · simp
  · intro j _ hj
    have : i.val + 1 ≠ j.val := fun h => hj (Fin.ext h.symm)
    simp [this]
  · simp

/-- Row `i` of `bidiagonal α s *ᵥ v` when `i` is the last row. -/
theorem bidiagonal_mulVec_apply_last (α : Fin n → K) (s : K) (v : Fin n → K) (i : Fin n)
    (hi : i.val + 1 = n) :
    (bidiagonal α s *ᵥ v) i = α i * v i := by
  classical
  rw [bidiagonal_mulVec_apply]
  have : ∀ j : Fin n, (if i.val + 1 = j.val then (s - α i) * v j else 0) = 0 := by
    intro j
    have : i.val + 1 ≠ j.val := by omega
    simp [this]
  simp [this]

/-- **Finite propagation.** If two vectors agree on all rows `j` with `j < i + t + 1`
(when those exist), then `A ^ t *ᵥ v` and `A ^ t *ᵥ w` agree on row `i`.
More precisely: entry `i` of `A ^ t *ᵥ v` depends only on entries `i, …, i + t` of `v`. -/
theorem bidiagonal_pow_mulVec_apply_congr (α : Fin n → K) (s : K) (t : ℕ) :
    ∀ (v w : Fin n → K) (i : Fin n),
      (∀ j : Fin n, i.val ≤ j.val → j.val ≤ i.val + t → v j = w j) →
      ((bidiagonal α s) ^ t *ᵥ v) i = ((bidiagonal α s) ^ t *ᵥ w) i := by
  induction t with
  | zero =>
    intro v w i h
    simp only [pow_zero, one_mulVec]
    exact h i le_rfl (by simp)
  | succ t ih =>
    intro v w i h
    rw [pow_succ', ← mulVec_mulVec, ← mulVec_mulVec]
    -- now `(A *ᵥ (A^t *ᵥ v)) i`
    by_cases hi : i.val + 1 < n
    · rw [bidiagonal_mulVec_apply_of_lt _ _ _ _ hi, bidiagonal_mulVec_apply_of_lt _ _ _ _ hi]
      have e1 := ih v w i (fun j h1 h2 => h j h1 (by omega))
      have e2 := ih v w ⟨i.val + 1, hi⟩ (fun j h1 h2 => h j (by simp at h1; omega)
        (by simp at h2; omega))
      rw [e1, e2]
    · have hlast : i.val + 1 = n := by have := i.isLt; omega
      rw [bidiagonal_mulVec_apply_last _ _ _ _ hlast, bidiagonal_mulVec_apply_last _ _ _ _ hlast]
      have e1 := ih v w i (fun j h1 h2 => h j h1 (by omega))
      rw [e1]

/-- **Moment identity, strong form.** For `i + t < n`, the entry `i` of
`A ^ t *ᵥ 1` equals `s ^ t`. -/
theorem bidiagonal_pow_mulVec_one_apply (α : Fin n → K) (s : K) (t : ℕ) :
    ∀ (i : Fin n), i.val + t < n →
      ((bidiagonal α s) ^ t *ᵥ (fun _ => (1 : K))) i = s ^ t := by
  induction t with
  | zero =>
    intro i _
    simp
  | succ t ih =>
    intro i hi
    rw [pow_succ', ← mulVec_mulVec]
    have hi1 : i.val + 1 < n := by omega
    rw [bidiagonal_mulVec_apply_of_lt _ _ _ _ hi1]
    rw [ih i (by omega), ih ⟨i.val + 1, hi1⟩ (by simp; omega)]
    ring

/-- **Lemma `lem:moments` of the manuscript.** `e₁ᵀ Aᵗ 𝟙 = sᵗ` for `t < n`, where the
first row is indexed by `⟨0, _⟩`. -/
theorem bidiagonal_first_moment (α : Fin n → K) (s : K) (t : ℕ) (ht : t < n) :
    ((bidiagonal α s) ^ t *ᵥ (fun _ => (1 : K))) ⟨0, by omega⟩ = s ^ t :=
  bidiagonal_pow_mulVec_one_apply α s t ⟨0, by omega⟩ (by simpa using ht)

/-- Polynomial-evaluation form: for a polynomial `p` of degree `< n`,
`e₁ᵀ p(A) 𝟙 = p(s)`. -/
theorem bidiagonal_aeval_first_row (α : Fin n → K) (s : K) (p : Polynomial K)
    (hp : p.natDegree < n) (hn : 0 < n) :
    ((Polynomial.aeval (bidiagonal α s) p) *ᵥ (fun _ => (1 : K))) ⟨0, hn⟩ = p.eval s := by
  classical
  rw [Polynomial.aeval_eq_sum_range, Polynomial.eval_eq_sum_range]
  simp only [sum_mulVec, Finset.sum_apply, smul_mulVec, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [Finset.mem_range] at ht
  rw [bidiagonal_pow_mulVec_one_apply α s t ⟨0, hn⟩ (by simp; omega)]

end EggeMansour
