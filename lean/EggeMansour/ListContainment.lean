import EggeMansour.PatternSums

namespace EggeMansour.Combinatorics

/-- A monotone occurrence crosses a host boundary at exactly one index cut. -/
theorem strictMono_host_cut {m n p : ℕ} (f : Fin p → Fin (m + n)) (hf : StrictMono f) :
    ∃ k ≤ p, ∀ i, (f i).val < m ↔ i.val < k := by
  classical
  by_cases hleft : ∀ i, (f i).val < m
  · exact ⟨p, le_rfl, fun i => ⟨fun _ => i.isLt, fun _ => hleft i⟩⟩
  push Not at hleft
  obtain ⟨b, hb⟩ := hleft
  let R : Finset (Fin p) := Finset.univ.filter (fun i => m ≤ (f i).val)
  have hR : R.Nonempty := ⟨b, by simp [R]; omega⟩
  let r : Fin p := R.min' hR
  have hr : m ≤ (f r).val := by
    have := Finset.min'_mem R hR
    simpa [R, r] using this
  refine ⟨r.val, Nat.le_of_lt r.isLt, ?_⟩
  intro i
  constructor
  · intro hi
    by_contra h
    have hmon := hf.monotone (show r ≤ i by exact Nat.le_of_not_gt h)
    change (f r).val ≤ (f i).val at hmon
    omega
  · intro hi
    by_contra h
    have hiR : i ∈ R := by simp [R]; omega
    have hmin := Finset.min'_le R i hiR
    change r.val ≤ i.val at hmin
    omega

/-- An occurrence with its original boundary information retained. -/
def CutOccurrence {m n : ℕ} (σ : Perm m) (τ : Perm n) (π : Pattern) (k : ℕ) : Prop :=
  ∃ f : Fin π.1 → Fin (m + n), StrictMono f ∧
    (∀ i j, directSum σ τ (f i) < directSum σ τ (f j) ↔ π.2 i < π.2 j) ∧
    ∀ i, (f i).val < m ↔ i.val < k

theorem cutOccurrence_patternSum {m n : ℕ} (σ : Perm m) (τ : Perm n) (α β : Pattern)
    (h : CutOccurrence σ τ (patternSum α β) α.1) :
    Contains σ α.2 ∧ Contains τ β.2 := by
  obtain ⟨f, hf, hp, hc⟩ := h
  dsimp only [patternSum] at f hf hp hc
  constructor
  · have hl (i : Fin α.1) : (f (Fin.castAdd β.1 i)).val < m :=
      (hc _).mpr i.isLt
    let g : Fin α.1 → Fin m := fun i => ⟨(f (Fin.castAdd β.1 i)).val, hl i⟩
    have hg (i : Fin α.1) : Fin.castAdd n (g i) = f (Fin.castAdd β.1 i) := Fin.ext rfl
    refine ⟨g, ?_, ?_⟩
    · intro i j hij
      exact hf hij
    · intro i j
      have hh := hp (Fin.castAdd β.1 i) (Fin.castAdd β.1 j)
      change directSum σ τ (f (Fin.castAdd β.1 i)) <
        directSum σ τ (f (Fin.castAdd β.1 j)) ↔
        directSum α.2 β.2 (Fin.castAdd β.1 i) < directSum α.2 β.2 (Fin.castAdd β.1 j) at hh
      rw [directSum_castAdd α.2 β.2 i, directSum_castAdd α.2 β.2 j] at hh
      rw [← hg i, ← hg j] at hh
      simpa only [directSum_castAdd, Fin.lt_def, Fin.val_castAdd] using hh
  · let g : Fin β.1 → Fin (m + n) := fun i => f (Fin.natAdd α.1 i)
    apply contains_right_of_occurrence_right σ τ β.2 g
    · intro i j hij
      exact hf (Nat.add_lt_add_left hij α.1)
    · intro i j
      have hh := hp (Fin.natAdd α.1 i) (Fin.natAdd α.1 j)
      change directSum σ τ (f (Fin.natAdd α.1 i)) <
        directSum σ τ (f (Fin.natAdd α.1 j)) ↔
        directSum α.2 β.2 (Fin.natAdd α.1 i) < directSum α.2 β.2 (Fin.natAdd α.1 j) at hh
      rw [directSum_natAdd α.2 β.2 i, directSum_natAdd α.2 β.2 j] at hh
      simpa only [g, directSum_natAdd, Fin.lt_def, Fin.val_natAdd,
        Nat.add_lt_add_iff_left] using hh
    · intro i
      have hi : ¬ (f (Fin.natAdd α.1 i)).val < m := by
        rw [hc]
        simp
      exact Nat.le_of_not_gt hi

/-- Literal direct-sum containment splits at a whole-component boundary.

The forward proof retains the given occurrence map while identifying its cut;
no independently chosen sub-occurrences are concatenated in that direction.
-/
theorem contains_directSum_sumPatterns_iff {m n : ℕ} (σ : Perm m) (τ : Perm n)
    (ps : List Pattern) (hps : ∀ p ∈ ps, IndecomposablePattern p) :
    Contains (directSum σ τ) (sumPatterns ps).2 ↔
      ∃ t ≤ ps.length, Contains σ (sumPatterns (ps.take t)).2 ∧
        Contains τ (sumPatterns (ps.drop t)).2 := by
  constructor
  · rintro ⟨f, hf, hp⟩
    obtain ⟨k, hk, hc⟩ := strictMono_host_cut f hf
    have hcut : HasOrderedCut (sumPatterns ps) k := by
      refine ⟨hk, ?_⟩
      intro i j hi hj
      have hfi := (hc i).mpr hi
      have hfj : m ≤ (f j).val := by
        by_contra h
        have := (hc j).mp (Nat.lt_of_not_ge h)
        omega
      exact (hp i j).mp (directSum_values_separated σ τ (f i) (f j) hfi hfj)
    obtain ⟨t, ht, hlen⟩ := orderedCut_is_block_boundary ps hps k hcut
    refine ⟨t, ht, ?_⟩
    apply cutOccurrence_patternSum σ τ (sumPatterns (ps.take t)) (sumPatterns (ps.drop t))
    rw [sumPatterns_take_drop]
    exact ⟨f, hf, hp, fun i => by rw [hlen]; exact hc i⟩
  · rintro ⟨t, _, hσ, hτ⟩
    change PatternContains ⟨m + n, directSum σ τ⟩ (sumPatterns ps)
    rw [← sumPatterns_take_drop ps t]
    exact hσ.directSum hτ

end EggeMansour.Combinatorics
