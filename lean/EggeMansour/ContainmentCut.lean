import EggeMansour.CombinatoricsCounts
import EggeMansour.PermutationCast

/-! # Containment cut lemmas

Value-level evaluation lemmas for the sums, the two-map (commuting square) characterisation of
containment, and the general cut theorem: an occurrence of
`π` in `σ ⊕ v` is a split `π ≅ α ⊕ β` with `σ ⊇ α` and `v ⊇ β`, for arbitrary `π`
(no indecomposability). -/

namespace EggeMansour.Combinatorics

open Function

/-! ## Evaluation lemmas -/

theorem directSum_val_left {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin (m + n))
    (hi : i.val < m) : (directSum σ τ i).val = (σ ⟨i, hi⟩).val := by
  have h := directSum_castAdd σ τ ⟨i.val, hi⟩
  have e : Fin.castAdd n ⟨i.val, hi⟩ = i := Fin.ext rfl
  rw [e] at h
  rw [h]; simp

theorem directSum_val_right {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin (m + n))
    (hi : m ≤ i.val) : (directSum σ τ i).val = m + (τ ⟨i - m, by omega⟩).val := by
  have h := directSum_natAdd σ τ ⟨i.val - m, by omega⟩
  have e : Fin.natAdd m ⟨i.val - m, by omega⟩ = i := by ext; simp; omega
  rw [e] at h
  rw [h]; simp

theorem skewSum_val_left {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin (m + n))
    (hi : i.val < m) : (skewSum σ τ i).val = n + (σ ⟨i, hi⟩).val := by
  have h := skewSum_castAdd_val σ τ ⟨i.val, hi⟩
  have e : Fin.castAdd n ⟨i.val, hi⟩ = i := Fin.ext rfl
  rwa [e] at h

theorem skewSum_val_right {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin (m + n))
    (hi : m ≤ i.val) : (skewSum σ τ i).val = (τ ⟨i - m, by omega⟩).val := by
  have h := skewSum_natAdd_val σ τ ⟨i.val - m, by omega⟩
  have e : Fin.natAdd m ⟨i.val - m, by omega⟩ = i := by ext; simp; omega
  rwa [e] at h

/-! ## Two-map characterisation of containment -/

/-- An occurrence as a commuting square: increasing positions `f`, increasing values `g`,
with `σ ∘ f = g ∘ τ`. -/
theorem contains_iff_exists_strictMono {n k : ℕ} (σ : Perm n) (τ : Perm k) :
    Contains σ τ ↔ ∃ f g : Fin k → Fin n, StrictMono f ∧ StrictMono g ∧ ∀ a, σ (f a) = g (τ a) := by
  constructor
  · rintro ⟨f, hf, hfτ⟩
    refine ⟨f, fun b => σ (f (τ.symm b)), hf, ?_, ?_⟩
    · intro b b' hb
      rw [hfτ]
      simpa using hb
    · intro a; simp
  · rintro ⟨f, g, hf, hg, h⟩
    refine ⟨f, hf, fun a b => ?_⟩
    rw [h a, h b, hg.lt_iff_lt]

/-- Containment only depends on the value table. -/
theorem contains_congr {n k k' : ℕ} (σ : Perm n) {τ : Perm k} {τ' : Perm k'} (e : k = k')
    (h : ∀ a : Fin k, (τ a).val = (τ' ⟨a, e ▸ a.isLt⟩).val) : Contains σ τ ↔ Contains σ τ' := by
  subst e
  have : τ = τ' := by ext a; exact h a
  rw [this]

theorem congr_contains {n n' k : ℕ} {σ : Perm n} {σ' : Perm n'} (τ : Perm k) (e : n = n')
    (h : ∀ a : Fin n, (σ a).val = (σ' ⟨a, e ▸ a.isLt⟩).val) : Contains σ τ ↔ Contains σ' τ := by
  subst e
  have : σ = σ' := by ext a; exact h a
  rw [this]


/-! # Direct-sum cut -/

/-! ## Thresholds of downward-closed predicates -/

/-- A downward-closed predicate on `Fin n` is an initial segment. -/
theorem exists_threshold {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (hdown : ∀ a b : Fin n, a ≤ b → P b → P a) :
    ∃ t, t ≤ n ∧ ∀ a : Fin n, P a ↔ a.val < t := by
  classical
  let Q : ℕ → Prop := fun k => ∀ hk : k < n, ¬ P ⟨k, hk⟩
  have hQ : ∃ k, Q k := ⟨n, fun hk => absurd hk (lt_irrefl n)⟩
  refine ⟨Nat.find hQ, Nat.find_min' hQ (fun hk => absurd hk (lt_irrefl n)), fun a => ?_⟩
  constructor
  · intro hPa
    by_contra hlt
    rw [not_lt] at hlt
    have hspec := Nat.find_spec hQ
    have hkn : Nat.find hQ < n := lt_of_le_of_lt hlt a.isLt
    exact hspec hkn (hdown ⟨Nat.find hQ, hkn⟩ a hlt hPa)
  · intro hlt
    have := Nat.find_min hQ hlt
    simp only [Q, not_forall, not_not] at this
    obtain ⟨_, h⟩ := this
    exact h

/-- Cardinality of an initial segment of `Fin n`. -/
theorem card_filter_lt {n t : ℕ} (ht : t ≤ n) :
    (Finset.univ.filter fun a : Fin n => a.val < t).card = t := by
  rw [Fin.card_filter_val_lt]; omega

/-! ## Splits -/

/-- `{0,…,t-1}` is mapped into itself. -/
def SplitsAt {n : ℕ} (π : Perm n) (t : ℕ) : Prop := ∀ a : Fin n, a.val < t → (π a).val < t

theorem SplitsAt.zero {n : ℕ} (π : Perm n) : SplitsAt π 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem SplitsAt.of_le {n t : ℕ} (π : Perm n) (h : n ≤ t) : SplitsAt π t :=
  fun a _ => lt_of_lt_of_le (π a).isLt h

/-- Bijectivity upgrades the one-sided invariance to an equivalence. -/
theorem SplitsAt.iff {n t : ℕ} {π : Perm n} (h : SplitsAt π t) (a : Fin n) :
    (π a).val < t ↔ a.val < t := by
  classical
  refine ⟨fun hπa => ?_, h a⟩
  by_cases ht : t ≤ n
  · -- `π` restricts to an injection of the `t`-element initial segment into itself, hence a surjection.
    set S : Finset (Fin n) := Finset.univ.filter fun a : Fin n => a.val < t with hS
    have hmaps : ∀ b ∈ S, π b ∈ S := by
      intro b hb; simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢; exact h b hb
    have hsurj := Finset.surj_on_of_inj_on_of_card_le (s := S) (t := S) (fun b _ => π b) hmaps
      (fun _ _ _ _ e => π.injective e) le_rfl
    obtain ⟨a', ha', e⟩ := hsurj (π a) (by simpa [hS] using hπa)
    have : a' = a := π.injective e.symm
    subst this
    simpa [hS] using ha'
  · rw [not_le] at ht; exact lt_of_lt_of_le a.isLt ht.le

theorem SplitsAt.ge {n t : ℕ} {π : Perm n} (h : SplitsAt π t) (a : Fin n) (ha : t ≤ a.val) :
    t ≤ (π a).val := by
  have := h.iff a; omega

/-- The restriction of `π` to an invariant initial segment. -/
noncomputable def splitLeft {n : ℕ} (π : Perm n) (t : ℕ) (ht : t ≤ n) (h : SplitsAt π t) : Perm t :=
  Equiv.ofBijective (fun a : Fin t => ⟨(π ⟨a.val, lt_of_lt_of_le a.isLt ht⟩).val, h _ a.isLt⟩)
    (Finite.injective_iff_bijective.mp (fun a b e => by
      have := congrArg Fin.val e
      simp only at this
      exact Fin.ext (Fin.mk.inj_iff.mp (π.injective (Fin.ext this)))))

@[simp] theorem splitLeft_val {n : ℕ} (π : Perm n) (t : ℕ) (ht : t ≤ n) (h : SplitsAt π t)
    (a : Fin t) : (splitLeft π t ht h a).val = (π ⟨a.val, lt_of_lt_of_le a.isLt ht⟩).val := rfl

/-- The standardised restriction of `π` to the complement of an invariant initial segment. -/
noncomputable def splitRight {n : ℕ} (π : Perm n) (t : ℕ) (ht : t ≤ n) (h : SplitsAt π t) : Perm (n - t) :=
  Equiv.ofBijective (fun a : Fin (n - t) =>
      ⟨(π ⟨t + a.val, by omega⟩).val - t, by
        have := (π ⟨t + a.val, by omega⟩).isLt; have := a.isLt; omega⟩)
    (Finite.injective_iff_bijective.mp (fun a b e => by
      have e' := congrArg Fin.val e
      simp only at e'
      have ha := h.ge ⟨t + a.val, by omega⟩ (by simp)
      have hb := h.ge ⟨t + b.val, by omega⟩ (by simp)
      have : (π ⟨t + a.val, by omega⟩).val = (π ⟨t + b.val, by omega⟩).val := by omega
      have := Fin.mk.inj_iff.mp (π.injective (Fin.ext this))
      exact Fin.ext (by omega)))

@[simp] theorem splitRight_val {n : ℕ} (π : Perm n) (t : ℕ) (ht : t ≤ n) (h : SplitsAt π t)
    (a : Fin (n - t)) :
    (splitRight π t ht h a).val = (π ⟨t + a.val, by omega⟩).val - t := rfl

/-- A permutation is the direct sum of its two restrictions at a split. -/
theorem directSum_splitLeft_splitRight {n : ℕ} (π : Perm n) (t : ℕ) (ht : t ≤ n)
    (h : SplitsAt π t) :
    castPerm (by omega) (directSum (splitLeft π t ht h) (splitRight π t ht h)) = π := by
  ext a
  rw [castPerm_val]
  by_cases ha : a.val < t
  · rw [directSum_val_left _ _ _ ha]; simp
  · rw [not_lt] at ha
    rw [directSum_val_right _ _ _ ha]
    simp only [splitRight_val]
    have := h.ge a ha
    have e : (⟨t + (a.val - t), by omega⟩ : Fin n) = a := Fin.ext (by simp; omega)
    rw [e]; omega

/-! ## Containment and direct sums -/

/-- Occurrences in both summands combine. -/
theorem contains_directSum_of_contains {p q a b : ℕ} {σ : Perm p} {v : Perm q} {α : Perm a} {β : Perm b}
    (h₁ : Contains σ α) (h₂ : Contains v β) : Contains (directSum σ v) (directSum α β) := by
  rw [contains_iff_exists_strictMono] at h₁ h₂ ⊢
  obtain ⟨f₁, g₁, hf₁, hg₁, e₁⟩ := h₁
  obtain ⟨f₂, g₂, hf₂, hg₂, e₂⟩ := h₂
  let F : Fin (a + b) → Fin (p + q) := fun i =>
    if hi : i.val < a then ⟨(f₁ ⟨i.val, hi⟩).val, by have := (f₁ ⟨i.val, hi⟩).isLt; omega⟩
    else ⟨p + (f₂ ⟨i.val - a, by omega⟩).val, by have := (f₂ ⟨i.val - a, by omega⟩).isLt; omega⟩
  let G : Fin (a + b) → Fin (p + q) := fun i =>
    if hi : i.val < a then ⟨(g₁ ⟨i.val, hi⟩).val, by have := (g₁ ⟨i.val, hi⟩).isLt; omega⟩
    else ⟨p + (g₂ ⟨i.val - a, by omega⟩).val, by have := (g₂ ⟨i.val - a, by omega⟩).isLt; omega⟩
  have hmono : ∀ (f₁ : Fin a → Fin p) (f₂ : Fin b → Fin q), StrictMono f₁ → StrictMono f₂ →
      StrictMono (fun i : Fin (a + b) =>
        if hi : i.val < a then (⟨(f₁ ⟨i.val, hi⟩).val, by have := (f₁ ⟨i.val, hi⟩).isLt; omega⟩ : Fin (p + q))
        else ⟨p + (f₂ ⟨i.val - a, by omega⟩).val, by have := (f₂ ⟨i.val - a, by omega⟩).isLt; omega⟩) := by
    intro f₁ f₂ hf₁ hf₂ i j hij
    simp only [Fin.lt_def] at hij ⊢
    by_cases hi : i.val < a
    · by_cases hj : j.val < a
      · simp only [hi, hj, dite_true]
        exact hf₁ (show (⟨i.val, hi⟩ : Fin a) < ⟨j.val, hj⟩ from hij)
      · simp only [hi, hj, dite_true, dite_false]
        have := (f₁ ⟨i.val, hi⟩).isLt; omega
    · have hj : ¬ j.val < a := by omega
      simp only [hi, hj, dite_false]
      have := hf₂ (show (⟨i.val - a, by omega⟩ : Fin b) < ⟨j.val - a, by omega⟩ from by
        simp only [Fin.lt_def]; omega)
      simp only [Fin.lt_def] at this; omega
  refine ⟨F, G, hmono f₁ f₂ hf₁ hf₂, hmono g₁ g₂ hg₁ hg₂, fun i => ?_⟩
  have hG₁ : ∀ (j : Fin (a + b)) (hj : j.val < a), (G j).val = (g₁ ⟨j.val, hj⟩).val :=
    fun j hj => by simp [G, hj]
  have hG₂ : ∀ (j : Fin (a + b)) (hj : ¬ j.val < a),
      (G j).val = p + (g₂ ⟨j.val - a, by omega⟩).val :=
    fun j hj => by simp [G, hj]
  apply Fin.ext
  by_cases hi : i.val < a
  · have hF : (F i).val = (f₁ ⟨i.val, hi⟩).val := by simp [F, hi]
    have hv : (directSum α β i).val = (α ⟨i.val, hi⟩).val := directSum_val_left _ _ _ hi
    have hlt : (directSum α β i).val < a := by rw [hv]; exact (α _).isLt
    have hFp : (F i).val < p := by rw [hF]; exact (f₁ _).isLt
    rw [hG₁ _ hlt, directSum_val_left _ _ _ hFp]
    have e : (⟨(directSum α β i).val, hlt⟩ : Fin a) = α ⟨i.val, hi⟩ := Fin.ext hv
    have e2 : (⟨(F i).val, hFp⟩ : Fin p) = f₁ ⟨i.val, hi⟩ := Fin.ext hF
    rw [e, e2, e₁]
  · have hF : (F i).val = p + (f₂ ⟨i.val - a, by omega⟩).val := by simp [F, hi]
    have hv : (directSum α β i).val = a + (β ⟨i.val - a, by omega⟩).val :=
      directSum_val_right _ _ _ (by omega)
    have hlt : ¬ (directSum α β i).val < a := by rw [hv]; omega
    have hFp : p ≤ (F i).val := by rw [hF]; omega
    rw [hG₂ _ hlt, directSum_val_right _ _ _ hFp]
    have e : (⟨(directSum α β i).val - a, by omega⟩ : Fin b) = β ⟨i.val - a, by omega⟩ :=
      Fin.ext (by dsimp only; omega)
    have e2 : (⟨(F i).val - p, by omega⟩ : Fin q) = f₂ ⟨i.val - a, by omega⟩ :=
      Fin.ext (by dsimp only; omega)
    rw [e, e2, e₂]

/-- Main splitting theorem: containment in a direct sum is a split of the pattern with
containment in each summand. -/
theorem contains_directSum_iff {p q n : ℕ} (σ : Perm p) (v : Perm q) (π : Perm n) :
    Contains (directSum σ v) π ↔
      ∃ (t : ℕ) (ht : t ≤ n) (h : SplitsAt π t),
        Contains σ (splitLeft π t ht h) ∧ Contains v (splitRight π t ht h) := by
  constructor
  · intro hc
    rw [contains_iff_exists_strictMono] at hc
    obtain ⟨f, g, hf, hg, e⟩ := hc
    classical
    -- positions in the left block form an initial segment of indices
    obtain ⟨t, ht, hPt⟩ := exists_threshold (fun a : Fin n => (f a).val < p)
      (fun a b hab hb => lt_of_le_of_lt (hf.monotone hab) hb)
    -- values in the left block form an initial segment of values
    obtain ⟨t', ht', hQt⟩ := exists_threshold (fun b : Fin n => (g b).val < p)
      (fun a b hab hb => lt_of_le_of_lt (hg.monotone hab) hb)
    -- the two segments correspond under `π`
    have key : ∀ a : Fin n, (π a).val < t' ↔ a.val < t := by
      intro a
      rw [← hQt, ← hPt, ← e]
      by_cases hfa : (f a).val < p
      · rw [directSum_val_left _ _ _ hfa]; simp [hfa]
      · rw [not_lt] at hfa; rw [directSum_val_right _ _ _ hfa]; omega
    have htt : t = t' := by
      have h1 : (Finset.univ.filter fun a : Fin n => a.val < t).card ≤
          (Finset.univ.filter fun b : Fin n => b.val < t').card :=
        Finset.card_le_card_of_injOn π (fun a ha => by
          have ha' : a.val < t := by simpa using ha
          simpa using (key a).2 ha') (fun a _ b _ hab => π.injective hab)
      have h2 : (Finset.univ.filter fun b : Fin n => b.val < t').card ≤
          (Finset.univ.filter fun a : Fin n => a.val < t).card :=
        Finset.card_le_card_of_injOn π.symm (fun b hb => by
          have hb' : b.val < t' := by simpa using hb
          have := key (π.symm b); simp only [Equiv.apply_symm_apply] at this
          simpa using this.1 hb') (fun a _ b _ hab => π.symm.injective hab)
      rw [card_filter_lt ht, card_filter_lt ht'] at h1 h2
      omega
    subst htt
    have hsplit : SplitsAt π t := fun a ha => (key a).2 ha
    refine ⟨t, ht, hsplit, ?_, ?_⟩
    · rw [contains_iff_exists_strictMono]
      refine ⟨fun a => ⟨(f ⟨a.val, by omega⟩).val, (hPt _).2 a.isLt⟩,
        fun b => ⟨(g ⟨b.val, by omega⟩).val, (hQt _).2 b.isLt⟩, ?_, ?_, ?_⟩
      · intro a b hab
        simp only [Fin.lt_def] at hab ⊢
        exact hf (show (⟨a.val, _⟩ : Fin n) < ⟨b.val, _⟩ from hab)
      · intro a b hab
        simp only [Fin.lt_def] at hab ⊢
        exact hg (show (⟨a.val, _⟩ : Fin n) < ⟨b.val, _⟩ from hab)
      · intro a
        apply Fin.ext
        simp only [splitLeft_val]
        have := congrArg Fin.val (e ⟨a.val, by omega⟩)
        rw [directSum_val_left _ _ _ ((hPt _).2 a.isLt)] at this
        simpa using this
    · rw [contains_iff_exists_strictMono]
      refine ⟨fun a => ⟨(f ⟨t + a.val, by omega⟩).val - p, by
          have h1 := (f ⟨t + a.val, by omega⟩).isLt
          have h2 : ¬ (f ⟨t + a.val, by omega⟩).val < p := by rw [hPt]; simp
          omega⟩,
        fun b => ⟨(g ⟨t + b.val, by omega⟩).val - p, by
          have h1 := (g ⟨t + b.val, by omega⟩).isLt
          have h2 : ¬ (g ⟨t + b.val, by omega⟩).val < p := by rw [hQt]; simp
          omega⟩, ?_, ?_, ?_⟩
      · intro a b hab
        simp only [Fin.lt_def] at hab ⊢
        have h1 := hf (show (⟨t + a.val, by omega⟩ : Fin n) < ⟨t + b.val, by omega⟩ from by
          simp only [Fin.lt_def]; omega)
        have h2 : ¬ (f ⟨t + a.val, by omega⟩).val < p := by rw [hPt]; simp
        simp only [Fin.lt_def] at h1; omega
      · intro a b hab
        simp only [Fin.lt_def] at hab ⊢
        have h1 := hg (show (⟨t + a.val, by omega⟩ : Fin n) < ⟨t + b.val, by omega⟩ from by
          simp only [Fin.lt_def]; omega)
        have h2 : ¬ (g ⟨t + a.val, by omega⟩).val < p := by rw [hQt]; simp
        simp only [Fin.lt_def] at h1; omega
      · intro a
        apply Fin.ext
        simp only [splitRight_val]
        have hfa : ¬ (f ⟨t + a.val, by omega⟩).val < p := by rw [hPt]; simp
        have := congrArg Fin.val (e ⟨t + a.val, by omega⟩)
        rw [directSum_val_right _ _ _ (by omega)] at this
        have hπ := hsplit.ge ⟨t + a.val, by omega⟩ (by simp)
        have hga : ¬ (g (π ⟨t + a.val, by omega⟩)).val < p := by rw [hQt]; omega
        have e2 : (⟨t + ((π ⟨t + a.val, by omega⟩).val - t), by omega⟩ : Fin n) =
            π ⟨t + a.val, by omega⟩ := Fin.ext (by simp; omega)
        rw [e2]
        omega
  · rintro ⟨t, ht, h, h₁, h₂⟩
    have := contains_directSum_of_contains h₁ h₂
    rwa [← directSum_splitLeft_splitRight π t ht h, contains_castPerm_iff]

end EggeMansour.Combinatorics
