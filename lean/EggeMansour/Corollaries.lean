import EggeMansour.CombinatorialTarget
import EggeMansour.CombinatoricsCounts

/-!
# Layered-pattern and finite-count consequences

The decreasing pattern of length `n` is the actual permutation `Fin.revPerm`.
Positive decreasing patterns are direct-sum indecomposable. The symmetry
consequences in this module take `DefinitionBasedSymmetry` as a premise.
`CombinatorialMain.lean` proves that premise from the combinatorial definitions;
`FromDefinitions.lean` applies these lemmas to give unconditional corollaries.
-/

namespace EggeMansour.Combinatorics

/-- The decreasing permutation `[n, n-1, ..., 1]`, in zero-based coordinates. -/
def decreasingPerm (n : ℕ) : Perm n := Fin.revPerm

/-- A decreasing permutation together with its length. -/
def decreasingPattern (n : ℕ) : Pattern := ⟨n, decreasingPerm n⟩

/-- Every positive decreasing pattern crosses every nontrivial initial cut. -/
theorem decreasingPerm_isIndecomposable {n : ℕ} (hn : 0 < n) :
    IsIndecomposable (decreasingPerm n) := by
  refine ⟨hn, fun k hk => ⟨⟨0, hn⟩, hk, ?_⟩⟩
  change k.val ≤ n - (0 + 1)
  omega

theorem decreasingPattern_indecomposable {n : ℕ} (hn : 0 < n) :
    IndecomposablePattern (decreasingPattern n) :=
  decreasingPerm_isIndecomposable hn

/-- The direct sum of the decreasing layers with the given lengths. -/
def layeredPattern {r : ℕ} (lengths : Fin r → ℕ) : Pattern :=
  sumPatterns (List.ofFn (decreasingPattern ∘ lengths))

/-- Extend the frozen target to an arbitrary number of summands, including zero. -/
theorem patternSeries_reorder_of_definitionBasedSymmetry
    (hsym : DefinitionBasedSymmetry) {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) :
    patternSeries (sumPatterns (List.ofFn blocks)) =
      patternSeries (sumPatterns (List.ofFn (blocks ∘ ρ))) := by
  cases r with
  | zero => simp
  | succ k => exact hsym k ρ blocks hblocks

/-- Equality of the actual series implies equality of literal finite counts. -/
theorem avoiderCount_eq_of_patternSeries_eq {p q : Pattern}
    (h : patternSeries p = patternSeries q) (n t : ℕ) :
    avoiderCount p.2 n t = avoiderCount q.2 n t := by
  have hc := congrArg (fun f : EggeMansour.Series =>
    (PowerSeries.coeff n f).coeff t) h
  simp only [patternSeries, coeff_coeff_avoiderSeries] at hc
  exact_mod_cast hc

/-- The arbitrary-indecomposable-block theorem at each exact length and 2-cycle count. -/
theorem avoiderCount_reorder_of_definitionBasedSymmetry
    (hsym : DefinitionBasedSymmetry) {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (blocks : Fin r → Pattern)
    (hblocks : ∀ i, IndecomposablePattern (blocks i)) (n t : ℕ) :
    avoiderCount (sumPatterns (List.ofFn blocks)).2 n t =
      avoiderCount (sumPatterns (List.ofFn (blocks ∘ ρ))).2 n t :=
  avoiderCount_eq_of_patternSeries_eq
    (patternSeries_reorder_of_definitionBasedSymmetry hsym ρ blocks hblocks) n t

/-- Egge--Mansour's layered-pattern symmetry, conditional on the frozen target. -/
theorem layeredSeries_reorder_of_definitionBasedSymmetry
    (hsym : DefinitionBasedSymmetry) {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (lengths : Fin r → ℕ)
    (hpositive : ∀ i, 0 < lengths i) :
    patternSeries (layeredPattern lengths) =
      patternSeries (layeredPattern (lengths ∘ ρ)) := by
  exact patternSeries_reorder_of_definitionBasedSymmetry hsym ρ
    (decreasingPattern ∘ lengths)
    (fun i => decreasingPattern_indecomposable (hpositive i))

/-- Layer order does not affect the actual count at any fixed length and 2-cycle count,
conditional on the frozen target. Repeated layer lengths are allowed. -/
theorem layeredCount_reorder_of_definitionBasedSymmetry
    (hsym : DefinitionBasedSymmetry) {r : ℕ}
    (ρ : Equiv.Perm (Fin r)) (lengths : Fin r → ℕ)
    (hpositive : ∀ i, 0 < lengths i) (n t : ℕ) :
    avoiderCount (layeredPattern lengths).2 n t =
      avoiderCount (layeredPattern (lengths ∘ ρ)).2 n t :=
  avoiderCount_eq_of_patternSeries_eq
    (layeredSeries_reorder_of_definitionBasedSymmetry hsym ρ lengths hpositive) n t

end EggeMansour.Combinatorics
