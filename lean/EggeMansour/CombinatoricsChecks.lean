import EggeMansour.CombinatoricsCounts

/-!
# Executable small-count checks

These evaluations enumerate the actual `Equiv.Perm (Fin n)` type and use the
literal containment predicate. They are independent of the Guibert recurrence.
The first examples are kernel-checked equalities; the larger `#eval` outputs are
execution evidence, not additional formal theorems.
-/

namespace EggeMansour.Combinatorics

example : List.ofFn pattern3412 = [2, 3, 0, 1] := by decide

example : involutionCount 0 0 = 1 := by decide
example : involutionCount 1 0 = 1 := by decide
example : involutionCount 2 0 = 1 := by decide
example : involutionCount 2 1 = 1 := by decide

def increasing (n : ℕ) : Perm n := Equiv.refl _

def decreasing (n : ℕ) : Perm n := Fin.revPerm

#eval (List.range 6).map (fun n =>
  (n, (List.range (n / 2 + 1)).map (involutionCount n)))

#eval (List.range 6).map (fun n =>
  (n, (List.range (n / 2 + 1)).map (avoiderCount (increasing 2) n)))

#eval (List.range 6).map (fun n =>
  (n, (List.range (n / 2 + 1)).map (avoiderCount (decreasing 2) n)))

#print axioms coeff_coeff_avoiderSeries
#print axioms twoCycles_directSum
#print axioms two_mul_twoCycles
#print axioms twoCycles_le_half
#print axioms contains_singleton_iff
#print axioms directSum_not_isIndecomposable

end EggeMansour.Combinatorics
