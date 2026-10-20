import EggeMansour.CombinatorialTarget

namespace EggeMansour.Combinatorics

/-- If every entry in an initial block is smaller than every entry outside it,
that initial block is invariant under the permutation. -/
theorem initial_invariant_of_separated {n : ℕ} (τ : Perm n) (k : ℕ)
    (hsep : ∀ i j : Fin n, i.val < k → k ≤ j.val → τ i < τ j) :
    ∀ i : Fin n, i.val < k → (τ i).val < k := by
  intro i hi
  let g : Fin ((τ i).val + 1) → Fin k := fun a =>
    ⟨(τ.symm ⟨a.val, by omega⟩).val, by
      by_contra h
      have hx := hsep i (τ.symm ⟨a.val, by omega⟩) hi (by omega)
      simp only [Equiv.apply_symm_apply] at hx
      have ha := a.isLt
      change (τ i).val < a.val at hx
      omega⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply Fin.ext
    have hp : τ.symm ⟨a.val, by omega⟩ = τ.symm ⟨b.val, by omega⟩ :=
      Fin.ext (congrArg (fun z : Fin k => z.val) hab)
    exact congrArg (fun z : Fin n => z.val) (τ.symm.injective hp)
  have hc := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin] at hc
  omega

/-- An indecomposable permutation has no nontrivial ordered separation. -/
theorem indecomposable_not_separated {n : ℕ} {τ : Perm n}
    (hτ : IsIndecomposable τ) (k : Fin n) (hk : 0 < k.val) :
    ¬ (∀ i j : Fin n, i.val < k.val → k.val ≤ j.val → τ i < τ j) := by
  intro hsep
  obtain ⟨i, hi, hcross⟩ := hτ.2 k hk
  have := initial_invariant_of_separated τ k.val hsep i hi
  omega

@[simp] theorem directSum_left_value_lt {m n : ℕ} (σ : Perm m) (τ : Perm n)
    (i : Fin (m + n)) (hi : i.val < m) : (directSum σ τ i).val < m := by
  refine Fin.addCases (fun a ha => ?_) (fun b hb => ?_) i hi
  · simp
  · simp only [Fin.val_natAdd] at hb
    omega

theorem directSum_right_value_ge {m n : ℕ} (σ : Perm m) (τ : Perm n)
    (i : Fin (m + n)) (hi : m ≤ i.val) : m ≤ (directSum σ τ i).val := by
  refine Fin.addCases (fun a ha => ?_) (fun b hb => ?_) i hi
  · simp only [Fin.val_castAdd] at ha
    have := a.isLt
    omega
  · simp

/-- Every value in the left direct summand is smaller than every value in the right. -/
theorem directSum_values_separated {m n : ℕ} (σ : Perm m) (τ : Perm n)
    (i j : Fin (m + n)) (hi : i.val < m) (hj : m ≤ j.val) :
    directSum σ τ i < directSum σ τ j := by
  have hl := directSum_left_value_lt σ τ i hi
  have hr := directSum_right_value_ge σ τ j hj
  exact Nat.lt_of_lt_of_le hl hr

/-- An occurrence of an indecomposable pattern cannot straddle a direct sum. -/
theorem indecomposable_occurrence_one_side {m n p : ℕ}
    (σ : Perm m) (τ : Perm n) (υ : Perm p) (hυ : IsIndecomposable υ)
    (f : Fin p → Fin (m + n)) (hf : StrictMono f)
    (hpat : ∀ i j, directSum σ τ (f i) < directSum σ τ (f j) ↔ υ i < υ j) :
    (∀ i, (f i).val < m) ∨ (∀ i, m ≤ (f i).val) := by
  classical
  by_cases hleft : ∀ i, (f i).val < m
  · exact Or.inl hleft
  right
  by_contra hright
  push Not at hleft hright
  obtain ⟨b, hb⟩ := hleft
  obtain ⟨a, ha⟩ := hright
  let R : Finset (Fin p) := Finset.univ.filter (fun i => m ≤ (f i).val)
  have hR : R.Nonempty := ⟨b, by simp [R]; omega⟩
  let r : Fin p := R.min' hR
  have hr : m ≤ (f r).val := by
    have := Finset.min'_mem R hR
    simpa [R, r] using this
  have har : a < r := by
    by_contra h
    have hmon := hf.monotone (le_of_not_gt h)
    change (f r).val ≤ (f a).val at hmon
    omega
  have hrpos : 0 < r.val := by have := a.isLt; change a.val < r.val at har; omega
  apply indecomposable_not_separated hυ r hrpos
  intro i j hi hj
  have hfi : (f i).val < m := by
    by_contra h
    have hiR : i ∈ R := by simp [R]; omega
    have hmin := Finset.min'_le R i hiR
    change r.val ≤ i.val at hmin
    omega
  have hfj : m ≤ (f j).val := by
    have hmon := hf.monotone hj
    change (f r).val ≤ (f j).val at hmon
    omega
  exact (hpat i j).mp (directSum_values_separated σ τ (f i) (f j) hfi hfj)

theorem contains_directSum_of_left {m n p : ℕ} (σ : Perm m) (τ : Perm n)
    {υ : Perm p} (h : Contains σ υ) : Contains (directSum σ τ) υ := by
  obtain ⟨f, hf, hp⟩ := h
  refine ⟨fun i => Fin.castAdd n (f i), ?_, ?_⟩
  · intro i j hij
    exact hf hij
  · intro i j
    simpa only [directSum_castAdd, directSum_natAdd, Fin.lt_def,
      Fin.val_castAdd, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hp i j

theorem contains_directSum_of_right {m n p : ℕ} (σ : Perm m) (τ : Perm n)
    {υ : Perm p} (h : Contains τ υ) : Contains (directSum σ τ) υ := by
  obtain ⟨f, hf, hp⟩ := h
  refine ⟨fun i => Fin.natAdd m (f i), ?_, ?_⟩
  · intro i j hij
    exact Nat.add_lt_add_left (hf hij) m
  · intro i j
    simpa only [directSum_castAdd, directSum_natAdd, Fin.lt_def,
      Fin.val_castAdd, Fin.val_natAdd, Nat.add_lt_add_iff_left] using hp i j

/-- Containment of an indecomposable pattern in a sum is containment on one side. -/
theorem contains_directSum_iff_of_indecomposable {m n p : ℕ}
    (σ : Perm m) (τ : Perm n) (υ : Perm p) (hυ : IsIndecomposable υ) :
    Contains (directSum σ τ) υ ↔ Contains σ υ ∨ Contains τ υ := by
  constructor
  · rintro ⟨f, hf, hp⟩
    rcases indecomposable_occurrence_one_side σ τ υ hυ f hf hp with hl | hr
    · left
      let g : Fin p → Fin m := fun i => ⟨(f i).val, hl i⟩
      have hg : ∀ i, Fin.castAdd n (g i) = f i := fun i => Fin.ext rfl
      refine ⟨g, ?_, ?_⟩
      · intro i j hij
        exact hf hij
      · intro i j
        have h := hp i j
        rw [← hg i, ← hg j] at h
        simpa only [directSum_castAdd, directSum_natAdd, Fin.lt_def,
          Fin.val_castAdd, Fin.val_natAdd, Nat.add_lt_add_iff_left] using h
    · right
      let g : Fin p → Fin n := fun i => ⟨(f i).val - m, by have := (f i).isLt; have := hr i; omega⟩
      have hg : ∀ i, Fin.natAdd m (g i) = f i := by
        intro i
        apply Fin.ext
        simp only [Fin.val_natAdd]
        dsimp [g]
        have := hr i
        omega
      refine ⟨g, ?_, ?_⟩
      · intro i j hij
        have h := hf hij
        change (f i).val - m < (f j).val - m
        have := hr i
        have := hr j
        change (f i).val < (f j).val at h
        omega
      · intro i j
        have h := hp i j
        rw [← hg i, ← hg j] at h
        simpa only [directSum_castAdd, directSum_natAdd, Fin.lt_def,
          Fin.val_castAdd, Fin.val_natAdd, Nat.add_lt_add_iff_left] using h
  · rintro (h | h)
    · exact contains_directSum_of_left σ τ h
    · exact contains_directSum_of_right σ τ h

/-- Restrict an occurrence whose positions all lie in the right summand. -/
theorem contains_right_of_occurrence_right {m n p : ℕ} (σ : Perm m) (τ : Perm n)
    (υ : Perm p) (f : Fin p → Fin (m + n)) (hf : StrictMono f)
    (hp : ∀ i j, directSum σ τ (f i) < directSum σ τ (f j) ↔ υ i < υ j)
    (hr : ∀ i, m ≤ (f i).val) : Contains τ υ := by
  let g : Fin p → Fin n := fun i => ⟨(f i).val - m, by have := (f i).isLt; have := hr i; omega⟩
  have hg : ∀ i, Fin.natAdd m (g i) = f i := by
    intro i
    apply Fin.ext
    simp only [Fin.val_natAdd]
    dsimp [g]
    have := hr i
    omega
  refine ⟨g, ?_, ?_⟩
  · intro i j hij
    have h := hf hij
    change (f i).val - m < (f j).val - m
    have := hr i
    have := hr j
    change (f i).val < (f j).val at h
    omega
  · intro i j
    have h := hp i j
    rw [← hg i, ← hg j] at h
    simpa only [directSum_natAdd, Fin.lt_def, Fin.val_natAdd,
      Nat.add_lt_add_iff_left] using h

/-- An indecomposable leading pattern too large to fit the left host forces the
entire occurrence, including all later pattern entries, into the right host. -/
theorem contains_directSum_right_of_large_prefix {m n a b : ℕ}
    (σ : Perm m) (τ : Perm n) (α : Perm a) (β : Perm b)
    (hα : IsIndecomposable α) (hma : m < a)
    (h : Contains (directSum σ τ) (directSum α β)) :
    Contains τ (directSum α β) := by
  obtain ⟨f, hf, hp⟩ := h
  let g : Fin a → Fin (m + n) := fun i => f (Fin.castAdd b i)
  have hg : StrictMono g := by
    intro i j hij
    exact hf hij
  have hgp : ∀ i j, directSum σ τ (g i) < directSum σ τ (g j) ↔ α i < α j := by
    intro i j
    simpa only [directSum_castAdd, Fin.lt_def, Fin.val_castAdd] using
      hp (Fin.castAdd b i) (Fin.castAdd b j)
  rcases indecomposable_occurrence_one_side σ τ α hα g hg hgp with hl | hr
  · have hinj : Function.Injective (fun i : Fin a => (⟨(g i).val, hl i⟩ : Fin m)) := by
      intro i j hij
      apply hg.injective
      exact Fin.ext (congrArg (fun z : Fin m => z.val) hij)
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hc
    omega
  · apply contains_right_of_occurrence_right σ τ (directSum α β) f hf hp
    have ha : 0 < a := by omega
    let z : Fin a := ⟨0, ha⟩
    intro i
    have hz := hr z
    have hmon := hf.monotone (show Fin.castAdd b z ≤ i by simp [z, Fin.le_def])
    change (f (Fin.castAdd b z)).val ≤ (f i).val at hmon
    change m ≤ (f (Fin.castAdd b z)).val at hz
    omega

/-- Leading a host by a singleton has no effect when the first indecomposable
pattern component has length greater than one. -/
theorem contains_singleton_directSum_iff_of_prefix {n a b : ℕ}
    (τ : Perm n) (α : Perm a) (β : Perm b) (hα : IsIndecomposable α) (ha : 1 < a) :
    Contains (directSum singleton τ) (directSum α β) ↔
      Contains τ (directSum α β) := by
  constructor
  · exact contains_directSum_right_of_large_prefix singleton τ α β hα ha
  · exact contains_directSum_of_right singleton τ

/-- Direct sum preserves two simultaneous pattern occurrences. -/
theorem Contains.directSum {m n a b : ℕ} {σ : Perm m} {τ : Perm n}
    {α : Perm a} {β : Perm b} (hσ : Contains σ α) (hτ : Contains τ β) :
    Contains (directSum σ τ) (directSum α β) := by
  obtain ⟨f, hf, hp⟩ := hσ
  obtain ⟨g, hg, hq⟩ := hτ
  let F : Fin (a + b) → Fin (m + n) :=
    Fin.addCases (fun i => Fin.castAdd n (f i)) (fun j => Fin.natAdd m (g j))
  refine ⟨F, ?_, ?_⟩
  · intro i j hij
    revert hij
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij
      simp only [F, Fin.addCases_left, Fin.lt_def, Fin.val_castAdd]
      apply hf
      exact hij
    · intro hij
      simp only [F, Fin.addCases_left, Fin.addCases_right, Fin.lt_def,
        Fin.val_castAdd, Fin.val_natAdd]
      have := (f i).isLt
      omega
    · intro hij
      have := j.isLt
      change a + i.val < j.val at hij
      omega
    · intro hij
      simp only [F, Fin.addCases_right, Fin.lt_def, Fin.val_natAdd]
      apply Nat.add_lt_add_left
      apply hg
      change a + i.val < a + j.val at hij
      omega
  · intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [F, Fin.addCases_left, directSum_castAdd, Fin.lt_def,
        Fin.val_castAdd] using hp i j
    · simp only [F, Fin.addCases_left, Fin.addCases_right, directSum_castAdd,
        directSum_natAdd, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      have := (σ (f i)).isLt
      have := (α i).isLt
      omega
    · simp only [F, Fin.addCases_left, Fin.addCases_right, directSum_castAdd,
        directSum_natAdd, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
      have := (σ (f j)).isLt
      have := (α j).isLt
      omega
    · simpa only [F, Fin.addCases_right, directSum_natAdd, Fin.lt_def,
        Fin.val_natAdd, Nat.add_lt_add_iff_left] using hq i j

/-- If both host and pattern begin with a singleton, these singleton entries
may be removed for containment, even when the remaining pattern is empty. -/
theorem contains_singleton_directSum_iff {n b : ℕ} (τ : Perm n) (β : Perm b) :
    Contains (directSum singleton τ) (directSum singleton β) ↔ Contains τ β := by
  constructor
  · rintro ⟨f, hf, hp⟩
    let g : Fin b → Fin (1 + n) := fun i => f (Fin.natAdd 1 i)
    have hg : StrictMono g := by
      intro i j hij
      apply hf
      exact Nat.add_lt_add_left hij 1
    have hgp : ∀ i j, directSum singleton τ (g i) < directSum singleton τ (g j) ↔
        β i < β j := by
      intro i j
      simpa only [directSum_natAdd, Fin.lt_def, Fin.val_natAdd,
        Nat.add_lt_add_iff_left] using hp (Fin.natAdd 1 i) (Fin.natAdd 1 j)
    apply contains_right_of_occurrence_right singleton τ β g hg hgp
    intro i
    have hx := hf (show (⟨0, by omega⟩ : Fin (1 + b)) < Fin.natAdd 1 i by
      simp [Fin.lt_def])
    change 1 ≤ (f (Fin.natAdd 1 i)).val
    change (f ⟨0, by omega⟩).val < (f (Fin.natAdd 1 i)).val at hx
    omega
  · intro h
    exact (contains_refl singleton).directSum h

/-- Avoidance of an indecomposable pattern is stable under direct sums. -/
theorem avoids_directSum_iff_of_indecomposable {m n p : ℕ}
    (σ : Perm m) (τ : Perm n) (υ : Perm p) (hυ : IsIndecomposable υ) :
    Avoids (directSum σ τ) υ ↔ Avoids σ υ ∧ Avoids τ υ := by
  simp only [Avoids, contains_directSum_iff_of_indecomposable σ τ υ hυ, not_or]

/-- Singleton cancellation, expressed as the avoidance equivalence in the recurrence. -/
theorem avoids_singleton_directSum_iff {n b : ℕ} (τ : Perm n) (β : Perm b) :
    Avoids (directSum singleton τ) (directSum singleton β) ↔ Avoids τ β := by
  simp only [Avoids, contains_singleton_directSum_iff]

/-- Non-singleton leading indecomposable component, in avoidance form. -/
theorem avoids_singleton_directSum_iff_of_prefix {n a b : ℕ}
    (τ : Perm n) (α : Perm a) (β : Perm b) (hα : IsIndecomposable α) (ha : 1 < a) :
    Avoids (directSum singleton τ) (directSum α β) ↔
      Avoids τ (directSum α β) := by
  simp only [Avoids, contains_singleton_directSum_iff_of_prefix τ α β hα ha]

/-- The literal 3412 pattern is sum indecomposable (kernel computation). -/
theorem pattern3412_indecomposable : IsIndecomposable pattern3412 := by decide

/-- Containment for varying-length patterns. -/
def PatternContains (σ τ : Pattern) : Prop := Contains σ.2 τ.2

/-- A list sum contains its tail sum, including the empty tail. -/
theorem sumPatterns_contains_tail (p : Pattern) (ps : List Pattern) :
    PatternContains (sumPatterns (p :: ps)) (sumPatterns ps) := by
  cases ps with
  | nil => exact contains_empty p.2
  | cons q qs =>
    exact contains_directSum_of_right p.2 (sumPatterns (q :: qs)).2
      (contains_refl _)

/-- Prefix sums are genuine patterns of the full direct sum. -/
theorem sumPatterns_contains_take (ps : List Pattern) (t : ℕ) :
    PatternContains (sumPatterns ps) (sumPatterns (ps.take t)) := by
  induction ps generalizing t with
  | nil =>
    rw [List.take_nil]
    exact contains_refl empty
  | cons p ps ih =>
    cases t with
    | zero => exact contains_empty _
    | succ t =>
      cases ps with
      | nil =>
        rw [List.take_succ_cons, List.take_nil]
        exact contains_refl p.2
      | cons q qs =>
        cases t with
        | zero =>
          exact contains_directSum_of_left p.2 (sumPatterns (q :: qs)).2 (contains_refl _)
        | succ t =>
          exact (contains_refl p.2).directSum (ih (t + 1))

/-- Suffix sums are genuine patterns of the full direct sum. -/
theorem sumPatterns_contains_drop (ps : List Pattern) (t : ℕ) :
    PatternContains (sumPatterns ps) (sumPatterns (ps.drop t)) := by
  induction t generalizing ps with
  | zero => exact contains_refl _
  | succ t ih =>
    cases ps with
    | nil => exact contains_refl empty
    | cons p ps =>
      exact (sumPatterns_contains_tail p ps).trans (ih ps)

/-- Containment of longer prefixes implies containment of shorter ones. -/
theorem sumPatterns_prefix_monotone (ps : List Pattern) {a b : ℕ} (hab : a ≤ b) :
    PatternContains (sumPatterns (ps.take b)) (sumPatterns (ps.take a)) := by
  have h := sumPatterns_contains_take (ps.take b) a
  simpa only [List.take_take, Nat.min_eq_left hab] using h

end EggeMansour.Combinatorics
