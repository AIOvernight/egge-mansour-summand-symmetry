import EggeMansour.CombinatorialTarget
import EggeMansour.Main

/-!
# Concrete-series bridge to the existing algebra

This conditional integration lemma connects the weighted recurrence to the
algebraic symmetry theorem. Its `hRec` premise is discharged by
`combinatorialWeightedRecurrence` in `CombinatorialMain.lean`, which proves
`definitionBasedSymmetry` from the combinatorial definitions.
-/

namespace EggeMansour.Combinatorics

/-- The weighted recurrence for actual interval avoidance series implies the
definition-based symmetry target. `CombinatorialMain.lean` proves the recurrence
and applies this lemma.

`blockH` is any blockwise series parameter; in the direct combinatorial
application it is the series for interiors whose wrap avoids the block. The singleton flag is the actual length-one
predicate. All block parameters respect reordering by the proved adapter lemma.
-/
theorem definitionBasedSymmetry_of_weightedRecurrence
    (blockH : Pattern → Series)
    (hRec : ∀ (k : ℕ) (blocks : Fin (k + 1) → Pattern),
      (∀ i, IndecomposablePattern (blocks i)) →
      WeightedRecurrence (k + 1) seriesX seriesQ
        (fun i => patternSeries (blockAt blocks i))
        (fun i => blockH (blockAt blocks i))
        (fun i => (blockAt blocks i).1 == 1)
        (intervalSeries blocks)) : DefinitionBasedSymmetry := by
  intro k ρ blocks hblocks
  have hF := hRec k blocks hblocks
  have hG := hRec k (blocks ∘ ρ) (fun i => hblocks (ρ i))
  have hc := blockParameter_reorder ρ blocks patternSeries
  have hh := blockParameter_reorder ρ blocks blockH
  have hs := blockParameter_reorder ρ blocks (fun p => p.1 == 1)
  rw [hc, hh, hs] at hG
  have h := weighted_recurrence_symmetry k ρ _ _ _ _ _ hF hG
  simpa only [intervalSeries_full] using h

end EggeMansour.Combinatorics
