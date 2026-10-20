import Mathlib

/-!
# Shared recurrence interfaces

Indices are zero-based natural numbers. Only entries with both indices below `n`
are constrained; entries below the diagonal are zero. This convention lets matrix
modules restrict to `Fin n` without introducing partial successor operations.
-/

noncomputable section

namespace EggeMansour

open scoped BigOperators

/-- The pole-free recurrence of manuscript equation (3.2), with `s = 1-x`
in its power-series application. -/
structure UniformRecurrence {R : Type*} [CommRing R] (n : ℕ) (q s : R)
    (c : ℕ → R) (F : ℕ → ℕ → R) : Prop where
  lower : ∀ i j, j < i → i < n → F i j = 0
  diagonal : ∀ i, i < n → F i i = c i
  step : ∀ i j, i < j → j < n →
    (1 - q * c i * c j) * F i j =
      c i + (1 - s * c i) * F (i + 1) j +
        q * c i * ∑ r ∈ Finset.Ioo i j, F i r * (F r j - F (r + 1) j)

/-- The published weighted recurrence, used as the premise of the algebraic
recurrence-to-symmetry theorem and proved for actual avoidance series by
`combinatorialWeightedRecurrence` in `CombinatorialMain.lean`.
`singleton i = true` means the block is the permutation `1`.
The reduced singleton has series zero, recorded in `singleton_reduction`. -/
structure WeightedRecurrence {R : Type*} [CommRing R] (n : ℕ) (x q : R)
    (c h : ℕ → R) (singleton : ℕ → Bool) (F : ℕ → ℕ → R) : Prop where
  lower : ∀ i j, j < i → i < n → F i j = 0
  empty : ∀ i, i < n → F (i + 1) i = 0
  diagonal : ∀ i, i < n → F i i = c i
  singleton_reduction : ∀ i, i < n → singleton i = true → h i = 0
  step : ∀ i j, i ≤ j → j < n →
    F i j = 1 + x * (if singleton i then F (i + 1) j else F i j) +
      q * h i * F i j + q * (F i (i + 1) - h i) * F (i + 1) j +
        q * ∑ r ∈ Finset.Icc (i + 2) j, (F i r - F i (r - 1)) * F r j

/-- Reorder the first `n` parameters; values outside the interval are unchanged
and irrelevant to the recurrence. -/
def permuteParams {α : Type*} {n : ℕ} (ρ : Equiv.Perm (Fin n)) (c : ℕ → α) : ℕ → α :=
  fun i => if hi : i < n then c (ρ ⟨i, hi⟩).val else c i

@[simp] theorem permuteParams_apply {α : Type*} {n : ℕ}
    (ρ : Equiv.Perm (Fin n)) (c : ℕ → α) (i : Fin n) :
    permuteParams ρ c i.val = c (ρ i).val := by
  simp [permuteParams]

abbrev Series := PowerSeries (Polynomial ℤ)

def seriesX : Series := PowerSeries.X

def seriesQ : Series := PowerSeries.X ^ 2 * PowerSeries.C Polynomial.X

def seriesS : Series := 1 - seriesX

/-- The universally quantified recurrence-to-symmetry proposition, proved by
`recurrenceImpliesSymmetry` in `Main.lean`. -/
def RecurrenceImpliesSymmetry : Prop :=
  ∀ (k : ℕ) (ρ : Equiv.Perm (Fin (k + 1)))
    (c h : ℕ → Series) (singleton : ℕ → Bool) (F G : ℕ → ℕ → Series),
    WeightedRecurrence (k + 1) seriesX seriesQ c h singleton F →
    WeightedRecurrence (k + 1) seriesX seriesQ
      (permuteParams ρ c) (permuteParams ρ h) (permuteParams ρ singleton) G →
    F 0 k = G 0 k

end EggeMansour
