import EggeMansour.CombinatorialMain
import EggeMansour.Corollaries
import EggeMansour.ReductionSeries

/-!
# Symmetry from the finite-permutation definitions

These theorems apply the proved combinatorial recurrence to the existing
algebraic symmetry theorem. Their only hypotheses concern the input patterns
or the positive lengths of decreasing layers.
-/

namespace EggeMansour.Combinatorics

/-- Egge--Mansour Theorem 3.3 with the literal reduced-pattern avoidance series
as its block parameter. Only nonempty indecomposable blocks are assumed. -/
theorem reducedWeightedRecurrence {r : ℕ} (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) :
    WeightedRecurrence r seriesX seriesQ
      (fun i => patternSeries (blockAt blocks i))
      (fun i => patternSeries (reduce (blockAt blocks i)))
      (fun i => (blockAt blocks i).1 == 1) (intervalSeries blocks) := by
  simpa only [wrappedSeries_eq_reducedSeries] using
    combinatorialWeightedRecurrence blocks hblocks

/-- General summand symmetry for actual avoidance series, including an empty family. -/
theorem patternSeries_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) :
    patternSeries (sumPatterns (List.ofFn blocks)) =
      patternSeries (sumPatterns (List.ofFn (blocks ∘ ρ))) :=
  patternSeries_reorder_of_definitionBasedSymmetry
    definitionBasedSymmetry ρ blocks hblocks

/-- The number of actual avoiding involutions with each length and 2-cycle count
is invariant under arbitrary reordering of nonempty indecomposable summands. -/
theorem avoiderCount_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) (n t : ℕ) :
    avoiderCount (sumPatterns (List.ofFn blocks)).2 n t =
      avoiderCount (sumPatterns (List.ofFn (blocks ∘ ρ))).2 n t :=
  avoiderCount_reorder_of_definitionBasedSymmetry
    definitionBasedSymmetry ρ blocks hblocks n t

/-- Egge--Mansour Conjecture 3.14 for positive decreasing-layer lengths,
refined by the number of 2-cycles. Repeated layer lengths are allowed. -/
theorem layeredSeries_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (lengths : Fin r → ℕ)
    (hpositive : ∀ i, 0 < lengths i) :
    patternSeries (layeredPattern lengths) =
      patternSeries (layeredPattern (lengths ∘ ρ)) :=
  layeredSeries_reorder_of_definitionBasedSymmetry
    definitionBasedSymmetry ρ lengths hpositive

/-- Literal finite-count form of Egge--Mansour Conjecture 3.14, refined by 2-cycles. -/
theorem layeredCount_reorder {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (lengths : Fin r → ℕ)
    (hpositive : ∀ i, 0 < lengths i) (n t : ℕ) :
    avoiderCount (layeredPattern lengths).2 n t =
      avoiderCount (layeredPattern (lengths ∘ ρ)).2 n t :=
  layeredCount_reorder_of_definitionBasedSymmetry
    definitionBasedSymmetry ρ lengths hpositive n t

end EggeMansour.Combinatorics
