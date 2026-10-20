import EggeMansour.DirectSumContainment

namespace EggeMansour.Combinatorics

def patternSum (p q : Pattern) : Pattern := ⟨p.1 + q.1, directSum p.2 q.2⟩

def patternWord (p : Pattern) : List ℕ := List.ofFn (fun i => (p.2 i).val)

theorem pattern_eq_of_word_eq {p q : Pattern} (h : patternWord p = patternWord q) :
    p = q := by
  rcases p with ⟨m, σ⟩
  rcases q with ⟨n, τ⟩
  have hmn : m = n := by simpa [patternWord] using congrArg List.length h
  subst n
  have hστ : σ = τ := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    exact congrFun (List.ofFn_injective h) i
  simp [hστ]

@[simp] theorem patternWord_sum (p q : Pattern) :
    patternWord (patternSum p q) = patternWord p ++ (patternWord q).map (p.1 + ·) := by
  rcases p with ⟨m, σ⟩
  rcases q with ⟨n, τ⟩
  change (List.ofFn fun i => (directSum σ τ i).val) =
    (List.ofFn fun i => (σ i).val) ++ (List.ofFn fun i => (τ i).val).map (m + ·)
  rw [List.ofFn_add, List.map_ofFn]
  congr 1
  · apply congrArg List.ofFn
    funext i
    change (directSum σ τ (Fin.castAdd n i)).val = (σ i).val
    simp
  · apply congrArg List.ofFn
    funext i
    simp

@[simp] theorem patternSum_empty (p : Pattern) : patternSum p ⟨0, empty⟩ = p := by
  apply pattern_eq_of_word_eq
  rw [patternWord_sum]
  simp [patternWord]

@[simp] theorem empty_patternSum (p : Pattern) : patternSum ⟨0, empty⟩ p = p := by
  apply pattern_eq_of_word_eq
  rw [patternWord_sum]
  simp [patternWord, Function.comp_def]

theorem patternSum_assoc (p q r : Pattern) :
    patternSum (patternSum p q) r = patternSum p (patternSum q r) := by
  apply pattern_eq_of_word_eq
  simp only [patternWord_sum, List.map_append, List.map_map, List.append_assoc]
  simp [patternSum, Function.comp_def, Nat.add_assoc]

@[simp] theorem sumPatterns_cons (p : Pattern) (ps : List Pattern) :
    sumPatterns (p :: ps) = patternSum p (sumPatterns ps) := by
  cases ps with
  | nil => simp [sumPatterns]
  | cons q qs => rfl

theorem sumPatterns_append (ps qs : List Pattern) :
    sumPatterns (ps ++ qs) = patternSum (sumPatterns ps) (sumPatterns qs) := by
  induction ps with
  | nil => simp [sumPatterns]
  | cons p ps ih =>
    simp only [List.cons_append, sumPatterns_cons, ih, patternSum_assoc]

theorem sumPatterns_take_drop (ps : List Pattern) (t : ℕ) :
    patternSum (sumPatterns (ps.take t)) (sumPatterns (ps.drop t)) = sumPatterns ps := by
  rw [← sumPatterns_append, List.take_append_drop]

/-- An ordered cut separates every value before the cut from every value after it. -/
def HasOrderedCut (p : Pattern) (k : ℕ) : Prop :=
  k ≤ p.1 ∧ ∀ i j : Fin p.1, i.val < k → k ≤ j.val → p.2 i < p.2 j

/-- Every ordered cut through indecomposable blocks is a component boundary. -/
theorem orderedCut_is_block_boundary (ps : List Pattern)
    (hps : ∀ p ∈ ps, IndecomposablePattern p) (k : ℕ)
    (hcut : HasOrderedCut (sumPatterns ps) k) :
    ∃ t ≤ ps.length, (sumPatterns (ps.take t)).1 = k := by
  induction ps generalizing k with
  | nil =>
    have hk : k = 0 := by have := hcut.1; simp [sumPatterns] at this; omega
    exact ⟨0, by simp, by simp [hk, sumPatterns]⟩
  | cons p ps ih =>
    by_cases hk0 : k = 0
    · exact ⟨0, by simp, by simp [hk0, sumPatterns]⟩
    rw [sumPatterns_cons] at hcut
    have hp : IsIndecomposable p.2 := hps p (by simp)
    have hpk : p.1 ≤ k := by
      by_contra h
      have hk : k < p.1 := by omega
      apply indecomposable_not_separated hp ⟨k, hk⟩ (show 0 < k by omega)
      intro i j hi hj
      have hs := hcut.2 (Fin.castAdd (sumPatterns ps).1 i)
        (Fin.castAdd (sumPatterns ps).1 j) hi hj
      change directSum p.2 (sumPatterns ps).2 (Fin.castAdd (sumPatterns ps).1 i) <
        directSum p.2 (sumPatterns ps).2 (Fin.castAdd (sumPatterns ps).1 j) at hs
      rw [directSum_castAdd, directSum_castAdd] at hs
      exact hs
    have htail : HasOrderedCut (sumPatterns ps) (k - p.1) := by
      constructor
      · have hk := hcut.1
        change k ≤ p.1 + (sumPatterns ps).1 at hk
        omega
      · intro i j hi hj
        have hs := hcut.2 (Fin.natAdd p.1 i) (Fin.natAdd p.1 j)
          (by simp only [Fin.val_natAdd]; omega) (by simp only [Fin.val_natAdd]; omega)
        change directSum p.2 (sumPatterns ps).2 (Fin.natAdd p.1 i) <
          directSum p.2 (sumPatterns ps).2 (Fin.natAdd p.1 j) at hs
        rw [directSum_natAdd, directSum_natAdd] at hs
        exact Nat.lt_of_add_lt_add_left hs
    obtain ⟨t, ht, hlen⟩ := ih (fun q hq => hps q (by simp [hq])) (k - p.1) htail
    refine ⟨t + 1, by simp; omega, ?_⟩
    rw [List.take_succ_cons, sumPatterns_cons]
    change p.1 + (sumPatterns (ps.take t)).1 = k
    rw [hlen]
    omega

end EggeMansour.Combinatorics
