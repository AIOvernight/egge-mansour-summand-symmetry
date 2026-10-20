import EggeMansour.AvoiderPartition
import EggeMansour.CellSeries
import EggeMansour.IntervalRecurrence
import EggeMansour.CombinatorialBridge

/-!
# Actual combinatorial recurrence and summand symmetry

The list identity below is proved from actual finite-permutation classes. No
recurrence or counting identity is assumed. The final theorem proves the exact
definition-based symmetry target from actual permutation avoidance definitions.
-/

namespace EggeMansour.Combinatorics

open scoped BigOperators

noncomputable section

/-- The actual list counting identity, derived from disjoint finite permutation classes. -/
theorem listWeightedIdentity : ListWeightedIdentity := by
  intro p ps hps
  let blocks := p :: ps
  let F := fixedImage (fixedAvoidingInterior blocks)
  let P := fun t => pairedImage (pairedAvoidingInterior blocks t) (avoidingSuffix blocks t)
  let pairs := fun n (σ : Perm n) => ∃ t ∈ Finset.range blocks.length, P t n σ
  have hclass : patternSeries (sumPatterns blocks) = weightSeries (avoiderClass blocks) :=
    avoiderSeries_eq_weightSeries _
  have hsum : weightSeries pairs = ∑ t ∈ Finset.range blocks.length, weightSeries (P t) := by
    apply weightSeries_sum
    · intro n σ
      rfl
    · intro s _ t _ n σ hs ht
      exact pairedAvoidingImages_unique blocks s t n σ hs ht
  have hfixedPairs : weightSeries (fun n σ => F n σ ∨ pairs n σ) =
      weightSeries F + weightSeries pairs := by
    apply weightSeries_add
    · intro n σ
      rfl
    · intro n σ
      rintro ⟨hf, t, _, ht⟩
      exact fixedImage_not_pairedImage _ _ _ n σ ⟨hf, ht⟩
  have hpartition : weightSeries (avoiderClass blocks) =
      weightSeries (fun n _ => n = 0) + weightSeries (fun n σ => F n σ ∨ pairs n σ) := by
    apply weightSeries_add
    · intro n σ
      have h := avoiderClass_iff_partition_nat blocks (by simp [blocks]) hps n σ
      simpa only [F, pairs, P, Finset.mem_range] using h
    · intro n σ
      rintro ⟨hn, hf | ⟨t, _, ht⟩⟩
      · exact fixedImage_ne_zero hf hn
      · exact pairedImage_ne_zero ht hn
  have hfixed : weightSeries F = seriesX *
      (if p.1 = 1 then patternSeries (sumPatterns ps)
       else patternSeries (sumPatterns blocks)) := by
    rw [weightSeries_fixedImage]
    have hinner : weightSeries (fixedAvoidingInterior blocks) =
        if p.1 == 1 then patternSeries (sumPatterns ps)
        else patternSeries (sumPatterns blocks) :=
      weightSeries_fixedInner p ps (hps p (by simp))
    rw [hinner]
    by_cases hp : p.1 = 1 <;> simp [hp]
  have hpaired (t : ℕ) : weightSeries (P t) =
      seriesQ * (wrappedSeries (sumPatterns (blocks.take (t + 1))) -
        wrappedSeries (sumPatterns (blocks.take t))) *
        patternSeries (sumPatterns (blocks.drop t)) := by
    change weightSeries (pairedImage (pairedAvoidingInterior blocks t) (avoidingSuffix blocks t)) = _
    rw [weightSeries_pairedImage]
    have hu : weightSeries (pairedAvoidingInterior blocks t) =
        wrappedSeries (sumPatterns (blocks.take (t + 1))) -
          wrappedSeries (sumPatterns (blocks.take t)) := weightSeries_prefixCell blocks t
    have hv : weightSeries (avoidingSuffix blocks t) =
        patternSeries (sumPatterns (blocks.drop t)) := (avoiderSeries_eq_weightSeries _).symm
    rw [hu, hv]
  calc
    _ = weightSeries (avoiderClass blocks) := hclass
    _ = 1 + (weightSeries F + weightSeries pairs) := by
      rw [hpartition, weightSeries_length_zero, hfixedPairs]
    _ = _ := by
      rw [hfixed, hsum]
      simp_rw [hpaired]
      simp only [Finset.mul_sum, mul_assoc, add_assoc]
      rfl

/-- The exact weighted interval recurrence for actual avoidance generating series. -/
theorem combinatorialWeightedRecurrence {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) :
    WeightedRecurrence n seriesX seriesQ
      (fun i => patternSeries (blockAt blocks i))
      (fun i => wrappedSeries (blockAt blocks i))
      (fun i => (blockAt blocks i).1 == 1) (intervalSeries blocks) :=
  weightedRecurrence_of_list_identity listWeightedIdentity blocks hb

/-- The exact frozen symmetry target, with all combinatorial recurrence hypotheses discharged. -/
theorem definitionBasedSymmetry : DefinitionBasedSymmetry := by
  apply definitionBasedSymmetry_of_weightedRecurrence wrappedSeries
  intro k blocks hb
  exact combinatorialWeightedRecurrence blocks hb

end
end EggeMansour.Combinatorics
