import EggeMansour

open EggeMansour.Combinatorics

namespace PublicationAudit

/-- The target with its actual finite-permutation series and sole input premise. -/
theorem generalSymmetry :
    ∀ (k : ℕ) (ρ : Equiv.Perm (Fin (k + 1))) (blocks : Fin (k + 1) → Pattern),
    (∀ i, IsIndecomposable (blocks i).2) →
    avoiderSeries (sumPatterns (List.ofFn blocks)).2 =
      avoiderSeries (sumPatterns (List.ofFn (blocks ∘ ρ))).2 :=
  definitionBasedSymmetry

/-- Positive decreasing layers, written as actual reversing permutations. -/
theorem layeredSymmetry (k : ℕ) (a : Fin k → ℕ)
    (ha : ∀ i, 0 < a i) (ρ : Equiv.Perm (Fin k)) :
    avoiderSeries (sumPatterns (List.ofFn (fun i => (⟨a i, Fin.revPerm⟩ : Pattern)))).2 =
    avoiderSeries (sumPatterns (List.ofFn (fun i => (⟨a (ρ i), Fin.revPerm⟩ : Pattern)))).2 :=
  layeredSeries_reorder ρ a ha

end PublicationAudit

set_option pp.universes true in
#check @PublicationAudit.generalSymmetry
#print axioms PublicationAudit.generalSymmetry
#check @PublicationAudit.layeredSymmetry
#print axioms PublicationAudit.layeredSymmetry
#print EggeMansour.Combinatorics.DefinitionBasedSymmetry
#print EggeMansour.Combinatorics.IndecomposablePattern
#print EggeMansour.Combinatorics.patternSeries
#print EggeMansour.Combinatorics.avoiderSeries
#print EggeMansour.Combinatorics.avoiderPolynomial
#print EggeMansour.Combinatorics.IsAvoidingInvolution
#check @EggeMansour.Combinatorics.contains_wrap_iff
#check @EggeMansour.Combinatorics.reducedWeightedRecurrence
#check @EggeMansour.Combinatorics.avoiderCount_reorder
#check @EggeMansour.Combinatorics.layeredCount_reorder
