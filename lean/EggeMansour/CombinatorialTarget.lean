import EggeMansour.Combinatorics
import EggeMansour.Interfaces

/-!
# Exact definition-based symmetry target

This file fixes the statement to be proved, independently of the algebraic
recurrence interface. Merely defining this proposition proves no symmetry.
-/

namespace EggeMansour.Combinatorics

/-- Direct sum of a finite list of actual finite permutations. -/
def sumPatterns : List Pattern → Pattern
  | [] => ⟨0, empty⟩
  | [p] => p
  | p :: q :: ps =>
    let rest := sumPatterns (q :: ps)
    ⟨p.1 + rest.1, directSum p.2 rest.2⟩

/-- The actual coefficient-defined avoidance series of a varying-length pattern. -/
noncomputable def patternSeries (p : Pattern) : EggeMansour.Series :=
  avoiderSeries p.2

/-- A varying-length pattern is nonempty and direct-sum indecomposable. -/
def IndecomposablePattern (p : Pattern) : Prop := IsIndecomposable p.2

/-- Extend a finite block family by the empty pattern outside its index range. -/
def blockAt {n : ℕ} (blocks : Fin n → Pattern) (i : ℕ) : Pattern :=
  if hi : i < n then blocks ⟨i, hi⟩ else ⟨0, empty⟩

@[simp] theorem blockAt_apply {n : ℕ} (blocks : Fin n → Pattern) (i : Fin n) :
    blockAt blocks i.val = blocks i := by simp [blockAt]

/-- Reordering blocks induces precisely the existing algebra's parameter action. -/
theorem blockAt_reorder {n : ℕ} (ρ : Equiv.Perm (Fin n))
    (blocks : Fin n → Pattern) :
    blockAt (blocks ∘ ρ) = EggeMansour.permuteParams ρ (blockAt blocks) := by
  funext i
  by_cases hi : i < n
  · simp [blockAt, EggeMansour.permuteParams, hi]
  · simp [blockAt, EggeMansour.permuteParams, hi]

/-- Any parameter computed from a block respects the same parameter action. -/
theorem blockParameter_reorder {α : Type*} {n : ℕ}
    (ρ : Equiv.Perm (Fin n)) (blocks : Fin n → Pattern) (f : Pattern → α) :
    (fun i => f (blockAt (blocks ∘ ρ) i)) =
      EggeMansour.permuteParams ρ (fun i => f (blockAt blocks i)) := by
  funext i
  by_cases hi : i < n
  · simp [blockAt, EggeMansour.permuteParams, hi]
  · simp [blockAt, EggeMansour.permuteParams, hi]

/-- The actual series for an inclusive interval of blocks; reversed intervals
have the empty pattern and hence, after the foundation lemma, series zero. -/
noncomputable def intervalSeries {n : ℕ} (blocks : Fin n → Pattern)
    (i j : ℕ) : EggeMansour.Series :=
  patternSeries (sumPatterns (((List.ofFn blocks).drop i).take (j + 1 - i)))

@[simp] theorem intervalSeries_full (k : ℕ) (blocks : Fin (k + 1) → Pattern) :
    intervalSeries blocks 0 k = patternSeries (sumPatterns (List.ofFn blocks)) := by
  unfold intervalSeries
  rw [Nat.sub_zero, List.drop_zero, List.take_of_length_le (by simp)]

@[simp] theorem intervalSeries_lower {n : ℕ} (blocks : Fin n → Pattern)
    (i j : ℕ) (hji : j < i) : intervalSeries blocks i j = 0 := by
  have hlen : j + 1 - i = 0 := by omega
  unfold intervalSeries
  rw [hlen, List.take_zero]
  exact avoiderSeries_empty

@[simp] theorem intervalSeries_diagonal {n : ℕ} (blocks : Fin n → Pattern)
    (i : Fin n) : intervalSeries blocks i.val i.val = patternSeries (blocks i) := by
  have hi : i.val < (List.ofFn blocks).length := by simp
  simp [intervalSeries, List.take_one_drop_eq_of_lt_length hi, sumPatterns]

/-- Egge–Mansour symmetry for arbitrary nonempty indecomposable summands.

The only premises describe the summands themselves. In particular this statement
has no recurrence, decomposition, generic-symmetry or series-equality hypothesis.
The empty pattern and the avoidance weights are supplied by `Combinatorics.lean`.
-/
def DefinitionBasedSymmetry : Prop :=
  ∀ (k : ℕ) (ρ : Equiv.Perm (Fin (k + 1)))
    (blocks : Fin (k + 1) → Pattern),
    (∀ i, IndecomposablePattern (blocks i)) →
    patternSeries (sumPatterns (List.ofFn blocks)) =
      patternSeries (sumPatterns (List.ofFn (blocks ∘ ρ)))

end EggeMansour.Combinatorics
