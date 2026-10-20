import EggeMansour.Reduction

/-! # Kernel sanity checks for the reduction

Lengths of reductions of small concrete patterns, checked by kernel `decide`.
Zero-based one-line notation: `[2,0,1]` is `312`, `[1,2,0]` is `231`, `[1,0]` is `21`. -/

namespace EggeMansour.Combinatorics

/-- `312`: begins with its maximum, so one entry is deleted (`red 312 = 12`). -/
def perm312 : Perm 3 := ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩

/-- `231`: ends with its minimum (`red 231 = 12`). -/
def perm231 : Perm 3 := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

/-- `21 = [2]`: both deletions apply (`red [2] = ∅`). -/
def perm21 : Perm 2 := ⟨![1, 0], ![1, 0], by decide, by decide⟩

/-- `12`: neither (`red 12 = 12`). -/
def perm12 : Perm 2 := ⟨![0, 1], ![0, 1], by decide, by decide⟩

/-- `321 = [3]`: both deletions (`red [3] = [1]`). -/
def perm321 : Perm 3 := ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩

example : (reduce ⟨3, perm312⟩).1 = 2 := by decide
example : (reduce ⟨3, perm231⟩).1 = 2 := by decide
example : (reduce ⟨2, perm21⟩).1 = 0 := by decide
example : (reduce ⟨2, perm12⟩).1 = 2 := by decide
example : (reduce ⟨3, perm321⟩).1 = 1 := by decide
example : (reduce ⟨4, pattern3412⟩).1 = 4 := by decide

-- Value tables of the reductions, via the case equations.
example : ∀ a : Fin 2, (stripFirst perm312 (by decide) a).val = a.val := by decide
example : ∀ a : Fin 2, (stripLast perm231 (by decide) a).val = a.val := by decide

-- Instances of the main theorem decided on both sides, for `u = 12` and `u = 21`.
-- `red 312 = 12` as a Pattern equality, through the case equation.
example : reduce ⟨3, perm312⟩ = ⟨2, perm12⟩ := by
  rw [reduce_of_max_of_not_min _ (by decide) (by decide)]
  congr 1
  exact Equiv.ext (fun a => Fin.ext (by revert a; decide))

-- `red [2] = ∅`.
example : reduce ⟨2, perm21⟩ = ⟨0, empty⟩ := by
  rw [reduce_of_max_of_min _ (by decide) (by decide)]
  congr 1
  exact Subsingleton.elim _ _
example : Contains (wrap perm12) perm312 := by decide
example : ¬ Contains (wrap perm21) perm312 := by decide
example : Contains (wrap perm21) perm321 := by decide
example : Contains (wrap perm12) pattern3412 ↔ Contains perm12 pattern3412 :=
  contains_wrap_pattern3412_iff _

end EggeMansour.Combinatorics
