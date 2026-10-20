import EggeMansour.ListContainment

/-!
# Disjoint maximal-prefix cells

The combinatorial partition is stated independently of weights and generating
series. Prefix containment is downward closed. Its unique true-to-false
boundary determines the suffix that the right host must avoid.
-/

namespace EggeMansour.Combinatorics

/-- The transition between contained and absent prefixes. -/
def BoundaryCell (P : ℕ → Prop) (t : ℕ) : Prop := P t ∧ ¬ P (t+1)

theorem boundaryCell_unique {P : ℕ → Prop}
    (hdown : ∀ i j, i ≤ j → P j → P i) {s t : ℕ}
    (hs : BoundaryCell P s) (ht : BoundaryCell P t) : s = t := by
  rcases lt_trichotomy s t with h | h | h
  · exact False.elim (hs.2 (hdown (s+1) t h ht.1))
  · exact h
  · exact False.elim (ht.2 (hdown (t+1) s h hs.1))

theorem exists_boundaryCell {P : ℕ → Prop} (hzero : P 0) (N : ℕ) (hN : ¬ P N) :
    ∃ t, t < N ∧ BoundaryCell P t := by
  classical
  induction N with
  | zero => exact False.elim (hN hzero)
  | succ N ih =>
    by_cases h : P N
    · exact ⟨N, Nat.lt_succ_self _, h, hN⟩
    · obtain ⟨t,ht,hcell⟩ := ih h
      exact ⟨t,Nat.lt_succ_of_lt ht,hcell⟩

theorem boundaryCell_true_iff {P : ℕ → Prop}
    (hdown : ∀ i j, i ≤ j → P j → P i) {t : ℕ}
    (ht : BoundaryCell P t) (s : ℕ) : P s ↔ s ≤ t := by
  constructor
  · intro hs
    by_contra h
    exact ht.2 (hdown (t+1) s (by omega) hs)
  · intro h
    exact hdown s t h ht.1

/-- A monotone prefix/suffix split has a unique avoidance cell. -/
theorem monotone_split_avoidance {P Q : ℕ → Prop} (N : ℕ)
    (hP : ∀ i j, i ≤ j → P j → P i)
    (hQ : ∀ i j, i ≤ j → Q i → Q j) (hP0 : P 0) (hQN : Q N) :
    ¬ (∃ s, s ≤ N ∧ P s ∧ Q s) ↔
      ∃! t, t < N ∧ BoundaryCell P t ∧ ¬ Q t := by
  constructor
  · intro h
    have hPN : ¬ P N := fun hPN => h ⟨N,le_rfl,hPN,hQN⟩
    obtain ⟨t,ht,hcell⟩ := exists_boundaryCell hP0 N hPN
    refine ⟨t, ⟨ht,hcell,?_⟩, ?_⟩
    · intro hQt
      exact h ⟨t,le_of_lt ht,hcell.1,hQt⟩
    · intro s hs
      exact boundaryCell_unique hP hs.2.1 hcell
  · rintro ⟨t,⟨ht,hcell,hQt⟩,_⟩ ⟨s,_,hPs,hQs⟩
    exact hQt (hQ s t ((boundaryCell_true_iff hP hcell s).mp hPs) hQs)

/-- The left host contains exactly `t` initial pattern blocks, stopping at the
next one. Valid for every pattern list, including empty lists. -/
def prefixCell {n : ℕ} (σ : Perm n) (ps : List Pattern) (t : ℕ) : Prop :=
  Contains σ (sumPatterns (ps.take t)).2 ∧
    Avoids σ (sumPatterns (ps.take (t+1))).2

theorem contains_prefix_antitone {n : ℕ} (σ : Perm n) (ps : List Pattern)
    {s t : ℕ} (hst : s ≤ t)
    (ht : Contains σ (sumPatterns (ps.take t)).2) :
    Contains σ (sumPatterns (ps.take s)).2 :=
  ht.trans (sumPatterns_prefix_monotone ps hst)

theorem prefixCell_unique {n : ℕ} (σ : Perm n) (ps : List Pattern) {s t : ℕ}
    (hs : prefixCell σ ps s) (ht : prefixCell σ ps t) : s = t :=
  boundaryCell_unique (fun _ _ hij => contains_prefix_antitone σ ps hij) hs ht

theorem prefixCell_disjoint {n : ℕ} (ps : List Pattern) {s t : ℕ} (hst : s ≠ t) :
    Disjoint {σ : Perm n | prefixCell σ ps s} {σ : Perm n | prefixCell σ ps t} := by
  apply Set.disjoint_left.mpr
  intro σ hs ht
  exact hst (prefixCell_unique σ ps hs ht)

theorem prefixCell_lt_length {n : ℕ} (σ : Perm n) (ps : List Pattern) {t : ℕ}
    (ht : prefixCell σ ps t) : t < ps.length := by
  by_contra h
  have hle : ps.length ≤ t := le_of_not_gt h
  have ht' := ht.1
  have hnot := ht.2
  rw [List.take_of_length_le hle] at ht'
  rw [List.take_of_length_le (by omega : ps.length ≤ t+1)] at hnot
  exact hnot ht'

@[simp] theorem not_prefixCell_nil {n : ℕ} (σ : Perm n) (t : ℕ) :
    ¬ prefixCell σ [] t := by
  intro h
  have := prefixCell_lt_length σ [] h
  simp at this

theorem prefixCell_contains_iff {n : ℕ} (σ : Perm n) (ps : List Pattern) {t : ℕ}
    (ht : prefixCell σ ps t) (s : ℕ) :
    Contains σ (sumPatterns (ps.take s)).2 ↔ s ≤ t :=
  boundaryCell_true_iff (fun _ _ hij => contains_prefix_antitone σ ps hij) ht s

/-- Cell membership is the difference of two nested avoidance classes. -/
theorem prefixCell_iff_avoidance_difference {n : ℕ} (σ : Perm n) (ps : List Pattern) (t : ℕ) :
    prefixCell σ ps t ↔ Avoids σ (sumPatterns (ps.take (t+1))).2 ∧
      ¬ Avoids σ (sumPatterns (ps.take t)).2 := by
  unfold prefixCell Avoids
  tauto

theorem avoids_prefix_mono {n : ℕ} (σ : Perm n) (ps : List Pattern) {s t : ℕ}
    (hst : s ≤ t) (hs : Avoids σ (sumPatterns (ps.take s)).2) :
    Avoids σ (sumPatterns (ps.take t)).2 := by
  intro ht
  exact hs (contains_prefix_antitone σ ps hst ht)

/-- Later suffixes are contained patterns of earlier suffixes. -/
theorem sumPatterns_suffix_monotone (ps : List Pattern) {s t : ℕ} (hst : s ≤ t) :
    PatternContains (sumPatterns (ps.drop s)) (sumPatterns (ps.drop t)) := by
  have h := sumPatterns_contains_drop (ps.drop s) (t-s)
  have heq : s + (t-s) = t := Nat.add_sub_of_le hst
  simpa only [List.drop_drop, heq] using h

/-- Full-list avoidance has a unique maximal contained prefix. -/
theorem avoids_iff_exists_prefixCell {n : ℕ} (σ : Perm n) (ps : List Pattern) :
    Avoids σ (sumPatterns ps).2 ↔ ∃! t, t < ps.length ∧ prefixCell σ ps t := by
  constructor
  · intro h
    have hzero : Contains σ (sumPatterns (ps.take 0)).2 := by simp [sumPatterns]
    have hN : ¬ Contains σ (sumPatterns (ps.take ps.length)).2 := by
      rw [List.take_of_length_le le_rfl]
      exact h
    obtain ⟨t,ht,hcell⟩ := exists_boundaryCell (P := fun t => Contains σ (sumPatterns (ps.take t)).2) hzero ps.length hN
    exact ⟨t,⟨ht,hcell⟩,fun s hs => prefixCell_unique σ ps hs.2 hcell⟩
  · rintro ⟨t,⟨ht,hcell⟩,_⟩ h
    have hfull : Contains σ (sumPatterns (ps.take ps.length)).2 := by
      rw [List.take_of_length_le le_rfl]
      exact h
    have hle := (prefixCell_contains_iff σ ps hcell ps.length).mp hfull
    omega

/-- Modular combinatorial partition: the only hypothesis is the full component
cut equivalence, to be supplied by the independently proved list-split theorem. -/
theorem avoids_directSum_iff_prefixCell_of_split {m n : ℕ} (α : Perm m) (β : Perm n)
    (ps : List Pattern)
    (hsplit : Contains (directSum α β) (sumPatterns ps).2 ↔
      ∃ s, s ≤ ps.length ∧ Contains α (sumPatterns (ps.take s)).2 ∧
        Contains β (sumPatterns (ps.drop s)).2) :
    Avoids (directSum α β) (sumPatterns ps).2 ↔
      ∃! t, t < ps.length ∧ prefixCell α ps t ∧
        Avoids β (sumPatterns (ps.drop t)).2 := by
  unfold Avoids
  rw [hsplit]
  apply monotone_split_avoidance
  · intro i j hij
    exact contains_prefix_antitone α ps hij
  · intro i j hij h
    exact h.trans (sumPatterns_suffix_monotone ps hij)
  · simp [sumPatterns]
  · rw [List.drop_eq_nil_of_le le_rfl]
    exact contains_empty β

/-- Actual avoidance partition at the unique maximal contained block prefix.
No decomposition or recurrence hypothesis is assumed. -/
theorem avoids_directSum_iff_prefixCell {m n : ℕ} (α : Perm m) (β : Perm n)
    (ps : List Pattern) (hps : ∀ p ∈ ps, IndecomposablePattern p) :
    Avoids (directSum α β) (sumPatterns ps).2 ↔
      ∃! t, t < ps.length ∧ prefixCell α ps t ∧
        Avoids β (sumPatterns (ps.drop t)).2 :=
  avoids_directSum_iff_prefixCell_of_split α β ps
    (contains_directSum_sumPatterns_iff α β ps hps)

/-- Existence-only version for finite unions of the disjoint prefix cells. -/
theorem avoids_directSum_iff_exists_prefixCell {m n : ℕ} (α : Perm m) (β : Perm n)
    (ps : List Pattern) (hps : ∀ p ∈ ps, IndecomposablePattern p) :
    Avoids (directSum α β) (sumPatterns ps).2 ↔
      ∃ t, t < ps.length ∧ prefixCell α ps t ∧
        Avoids β (sumPatterns (ps.drop t)).2 := by
  rw [avoids_directSum_iff_prefixCell α β ps hps]
  constructor
  · exact ExistsUnique.exists
  · rintro ⟨t,ht⟩
    exact ⟨t,ht,fun s hs => prefixCell_unique α ps hs.2.1 ht.2.1⟩

/-- On a fixed prefix cell, only the corresponding suffix avoidance remains. -/
theorem prefixCell_avoids_directSum_iff {m n : ℕ} (α : Perm m) (β : Perm n)
    (ps : List Pattern) (hps : ∀ p ∈ ps, IndecomposablePattern p) {t : ℕ}
    (ht : prefixCell α ps t) :
    Avoids (directSum α β) (sumPatterns ps).2 ↔
      Avoids β (sumPatterns (ps.drop t)).2 := by
  rw [avoids_directSum_iff_exists_prefixCell α β ps hps]
  constructor
  · rintro ⟨s,_,hs,havoid⟩
    have heq := prefixCell_unique α ps hs ht
    subst s
    exact havoid
  · intro h
    exact ⟨t,prefixCell_lt_length α ps ht,ht,h⟩

end EggeMansour.Combinatorics
