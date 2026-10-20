import EggeMansour.GenericRecurrence
import EggeMansour.Specialization

/-!
# Egge–Mansour: the weighted recurrence implies block symmetry

This module proves the algebraic implication from the weighted recurrence to
permutation invariance, including repeated block parameters in integer-polynomial
power series. `CombinatorialMain.lean` proves the recurrence from the
combinatorial definitions; `FromDefinitions.lean` gives the unconditional
series and finite-count symmetry theorems.
-/

noncomputable section
namespace EggeMansour

/-- The exact recurrence-to-symmetry target from `Interfaces.lean`.

The proof uses the generic interpolation theorem only at universal fraction-field
parameters, proves its nonvanishing and distinctness hypotheses there, and then
transports the resulting identity through the endpoint-only localization.
No distinctness or nonvanishing hypothesis remains in this statement. -/
theorem recurrenceImpliesSymmetry : RecurrenceImpliesSymmetry := by
  apply Universal.recurrenceImpliesSymmetry_of_generic
  intro n hn ρ F G hF hG
  apply UniformRecurrence.generic_symmetry_of_pos hn ρ hF hG
  · intro i _
    exact Universal.fieldC_ne_zero i
  · intro i j hij
    apply Fin.ext
    exact Universal.fieldNode_injective hij

/-- Manuscript-comparable expanded statement: two interval families obeying the
published recurrence for an ordered block list and any permutation have equal
full-interval series in `ℤ[y][[x]]`. The Boolean flags identify singleton blocks,
and `h` gives their reduced-pattern series. -/
theorem weighted_recurrence_symmetry
    (k : ℕ) (ρ : Equiv.Perm (Fin (k + 1)))
    (c h : ℕ → Series) (singleton : ℕ → Bool) (F G : ℕ → ℕ → Series)
    (hF : WeightedRecurrence (k + 1) seriesX seriesQ c h singleton F)
    (hG : WeightedRecurrence (k + 1) seriesX seriesQ
      (permuteParams ρ c) (permuteParams ρ h) (permuteParams ρ singleton) G) :
    F 0 k = G 0 k :=
  recurrenceImpliesSymmetry k ρ c h singleton F G hF hG

end EggeMansour
