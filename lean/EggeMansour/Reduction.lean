import EggeMansour.Wrap
import EggeMansour.ContainmentCut

/-! # Reduction of a pattern and containment in `1 ⊖ u ⊖ 1`

Manuscript Lemma `lem:layers`(b),(c) and Egge–Mansour 2006, Definition 3.2.

`stripFirst τ h` deletes the first entry of `τ` when it is the maximum; `stripLast τ h` deletes
the last entry when it is the minimum (standardised).  `reduce` applies both deletions when
possible.  The main theorem `contains_wrap_iff` says `wrap u` contains `τ` iff `u` contains
`reduce τ`, for every `τ` (including the empty and singleton patterns).
-/

namespace EggeMansour.Combinatorics

open Function

/-! ## Stripping the first (maximal) or last (minimal) entry -/

/-- Delete the first entry of `τ`, assumed to be its maximum. -/
noncomputable def stripFirst {n : ℕ} (τ : Perm (n + 1)) (h : (τ 0).val = n) : Perm n :=
  Equiv.ofBijective (fun a : Fin n => ⟨(τ a.succ).val, by
      have h1 := (τ a.succ).isLt
      have h2 : τ a.succ ≠ τ 0 := fun e => Fin.succ_ne_zero a (τ.injective e)
      have h3 : (τ a.succ).val ≠ n := fun e => h2 (Fin.ext (by rw [e, h]))
      omega⟩)
    (Finite.injective_iff_bijective.mp (fun a b e => by
      have := congrArg Fin.val e
      simp only at this
      exact Fin.succ_injective _ (τ.injective (Fin.ext this))))

@[simp] theorem stripFirst_val {n : ℕ} (τ : Perm (n + 1)) (h : (τ 0).val = n) (a : Fin n) :
    (stripFirst τ h a).val = (τ a.succ).val := rfl

/-- Delete the last entry of `τ`, assumed to be its minimum. -/
noncomputable def stripLast {n : ℕ} (τ : Perm (n + 1)) (h : (τ (Fin.last n)).val = 0) : Perm n :=
  Equiv.ofBijective (fun a : Fin n => ⟨(τ a.castSucc).val - 1, by
      have h1 := (τ a.castSucc).isLt
      have h2 : τ a.castSucc ≠ τ (Fin.last n) := fun e =>
        (Fin.castSucc_lt_last a).ne (τ.injective e)
      have h3 : (τ a.castSucc).val ≠ 0 := fun e => h2 (Fin.ext (by rw [e, h]))
      omega⟩)
    (Finite.injective_iff_bijective.mp (fun a b e => by
      have e' := congrArg Fin.val e
      simp only at e'
      have ha : τ a.castSucc ≠ τ (Fin.last n) := fun e =>
        (Fin.castSucc_lt_last a).ne (τ.injective e)
      have hb : τ b.castSucc ≠ τ (Fin.last n) := fun e =>
        (Fin.castSucc_lt_last b).ne (τ.injective e)
      have ha' : (τ a.castSucc).val ≠ 0 := fun e => ha (Fin.ext (by rw [e, h]))
      have hb' : (τ b.castSucc).val ≠ 0 := fun e => hb (Fin.ext (by rw [e, h]))
      exact Fin.castSucc_injective _ (τ.injective (Fin.ext (by omega)))))

@[simp] theorem stripLast_val {n : ℕ} (τ : Perm (n + 1)) (h : (τ (Fin.last n)).val = 0)
    (a : Fin n) : (stripLast τ h a).val = (τ a.castSucc).val - 1 := rfl

theorem stripLast_val_add_one {n : ℕ} (τ : Perm (n + 1)) (h : (τ (Fin.last n)).val = 0)
    (a : Fin n) : (stripLast τ h a).val + 1 = (τ a.castSucc).val := by
  have h2 : τ a.castSucc ≠ τ (Fin.last n) := fun e => (Fin.castSucc_lt_last a).ne (τ.injective e)
  have h3 : (τ a.castSucc).val ≠ 0 := fun e => h2 (Fin.ext (by rw [e, h]))
  simp only [stripLast_val]; omega

/-- The stripped pattern is contained in the original. -/
theorem contains_stripFirst {n : ℕ} (τ : Perm (n + 1)) (h : (τ 0).val = n) :
    Contains τ (stripFirst τ h) :=
  ⟨Fin.succ, Fin.strictMono_succ, fun a b => by
    simp only [Fin.lt_def, stripFirst_val]⟩

theorem contains_stripLast {n : ℕ} (τ : Perm (n + 1)) (h : (τ (Fin.last n)).val = 0) :
    Contains τ (stripLast τ h) :=
  ⟨Fin.castSucc, Fin.strictMono_castSucc, fun a b => by
    simp only [Fin.lt_def]
    rw [← stripLast_val_add_one τ h a, ← stripLast_val_add_one τ h b]; omega⟩

/-! ## Inverses -/

/-- Containment is symmetric under inversion (positions and values swap roles). -/
theorem contains_symm_iff {n k : ℕ} (σ : Perm n) (τ : Perm k) :
    Contains σ.symm τ.symm ↔ Contains σ τ := by
  rw [contains_iff_exists_strictMono, contains_iff_exists_strictMono]
  constructor
  · rintro ⟨f, g, hf, hg, e⟩
    refine ⟨g, f, hg, hf, fun a => ?_⟩
    have := e (τ a)
    simp only [Equiv.symm_apply_apply] at this
    rw [← this, Equiv.apply_symm_apply]
  · rintro ⟨f, g, hf, hg, e⟩
    refine ⟨g, f, hg, hf, fun a => ?_⟩
    have := e (τ.symm a)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this, Equiv.symm_apply_apply]

theorem symm_zero_val_iff {n : ℕ} (τ : Perm (n + 1)) :
    (τ.symm 0).val = n ↔ (τ (Fin.last n)).val = 0 := by
  constructor
  · intro h
    have : τ.symm 0 = Fin.last n := Fin.ext (by simpa using h)
    rw [← this, Equiv.apply_symm_apply]; rfl
  · intro h
    have : τ (Fin.last n) = 0 := Fin.ext (by simpa using h)
    rw [← this, Equiv.symm_apply_apply]; rfl

theorem stripFirst_symm {n : ℕ} (τ : Perm (n + 1)) (h : (τ (Fin.last n)).val = 0) :
    stripFirst τ.symm ((symm_zero_val_iff τ).2 h) = (stripLast τ h).symm := by
  apply Equiv.ext
  intro b
  apply (stripLast τ h).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  rw [← Nat.add_right_cancel_iff (n := 1), stripLast_val_add_one]
  have key : ((stripFirst τ.symm ((symm_zero_val_iff τ).2 h) b).castSucc : Fin (n + 1)) =
      τ.symm b.succ := Fin.ext (by simp)
  rw [key, Equiv.apply_symm_apply]
  simp

/-! ## Prepending a maximum -/

/-- `σ'` begins with its maximum and so does `τ'`: containment reduces to the stripped
permutations. -/
theorem contains_iff_stripFirst_of_max {p n : ℕ} (σ' : Perm (p + 1)) (hσ : (σ' 0).val = p)
    (τ' : Perm (n + 1)) (hτ : (τ' 0).val = n) :
    Contains σ' τ' ↔ Contains (stripFirst σ' hσ) (stripFirst τ' hτ) := by
  constructor
  · intro hc
    rw [contains_iff_exists_strictMono] at hc
    obtain ⟨f, g, hf, hg, e⟩ := hc
    -- every used value is at most the value used for the maximal entry `τ' 0`
    have hgmax : ∀ b, (g b).val ≤ (g (τ' 0)).val := by
      intro b
      apply hg.monotone
      rw [Fin.le_def, hτ]; exact Nat.lt_succ_iff.mp b.isLt
    by_cases hf0 : (f 0).val = 0
    · -- the occurrence uses the first entry; drop it
      rw [contains_iff_exists_strictMono]
      have hgb : ∀ b : Fin n, (g b.castSucc).val < p := by
        intro b
        have h1 : g b.castSucc < g (τ' 0) := hg (by
          rw [Fin.lt_def, hτ]; simp)
        have h2 : g (τ' 0) = σ' (f 0) := (e 0).symm
        have h3 : f 0 = 0 := Fin.ext hf0
        rw [h3] at h2
        rw [Fin.lt_def, h2, hσ] at h1
        exact h1
      have hfa : ∀ a : Fin n, 0 < (f a.succ).val := by
        intro a
        have := hf (Fin.succ_pos a)
        rw [Fin.lt_def] at this; omega
      refine ⟨fun a => ⟨(f a.succ).val - 1, by have := (f a.succ).isLt; have := hfa a; omega⟩,
        fun b => ⟨(g b.castSucc).val, hgb b⟩, ?_, ?_, ?_⟩
      · intro a b hab
        simp only [Fin.lt_def]
        have := hf (Fin.succ_lt_succ_iff.mpr hab)
        rw [Fin.lt_def] at this
        have := hfa a; omega
      · intro a b hab
        simp only [Fin.lt_def]
        have := hg (Fin.castSucc_lt_castSucc_iff.mpr hab)
        rwa [Fin.lt_def] at this
      · intro a
        apply Fin.ext
        simp only [stripFirst_val]
        have e1 : ((⟨(f a.succ).val - 1, by have := (f a.succ).isLt; have := hfa a; omega⟩ :
            Fin p).succ) = f a.succ := Fin.ext (by simp; have := hfa a; omega)
        rw [e1, e a.succ]
        have e2 : (stripFirst τ' hτ a).castSucc = τ' a.succ := Fin.ext (by simp)
        rw [e2]
    · -- the occurrence avoids position 0: it lies in `stripFirst σ'`, which then contains `τ'`
      have hpos : ∀ a, 0 < (f a).val := by
        intro a
        have := hf.monotone (Fin.zero_le a)
        rw [Fin.le_def] at this; omega
      have hlt : ∀ b, (g b).val < p := by
        intro b
        have h1 := hgmax b
        have h2 : (g (τ' 0)).val = (σ' (f 0)).val := by rw [e 0]
        have h3 : σ' (f 0) ≠ σ' 0 := fun h => hf0 (by rw [σ'.injective h]; rfl)
        have h4 : (σ' (f 0)).val ≠ p := fun h => h3 (Fin.ext (by rw [h, hσ]))
        have h5 := (σ' (f 0)).isLt
        omega
      have hστ' : Contains (stripFirst σ' hσ) τ' := by
        rw [contains_iff_exists_strictMono]
        refine ⟨fun a => ⟨(f a).val - 1, by have := (f a).isLt; have := hpos a; omega⟩,
          fun b => ⟨(g b).val, hlt b⟩, ?_, ?_, ?_⟩
        · intro a b hab
          simp only [Fin.lt_def]
          have := hf hab; rw [Fin.lt_def] at this
          have := hpos a; omega
        · intro a b hab
          simp only [Fin.lt_def]
          have := hg hab; rwa [Fin.lt_def] at this
        · intro a
          apply Fin.ext
          simp only [stripFirst_val]
          have e1 : ((⟨(f a).val - 1, by have := (f a).isLt; have := hpos a; omega⟩ :
              Fin p).succ) = f a := Fin.ext (by simp; have := hpos a; omega)
          rw [e1, e a]
      exact hστ'.trans (contains_stripFirst τ' hτ)
  · intro hc
    rw [contains_iff_exists_strictMono] at hc ⊢
    obtain ⟨f, g, hf, hg, e⟩ := hc
    refine ⟨Fin.cases 0 (fun a => (f a).succ), Fin.lastCases (Fin.last p) (fun b => (g b).castSucc),
      ?_, ?_, ?_⟩
    · intro a b hab
      revert hab
      refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b <;> intro hab
      · exact absurd hab (lt_irrefl _)
      · simp
      · exact absurd hab (not_lt.mpr (Fin.zero_le _))
      · simp only [Fin.cases_succ]
        exact Fin.succ_lt_succ_iff.mpr (hf (Fin.succ_lt_succ_iff.mp hab))
    · intro a b hab
      revert hab
      refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;>
        intro hab
      · exact absurd hab (lt_irrefl _)
      · exact absurd hab (not_lt.mpr (Fin.le_last _))
      · simp [Fin.castSucc_lt_last]
      · simp only [Fin.lastCases_castSucc]
        exact Fin.castSucc_lt_castSucc_iff.mpr (hg (Fin.castSucc_lt_castSucc_iff.mp hab))
    · intro a
      refine Fin.cases ?_ (fun a' => ?_) a
      · simp only [Fin.cases_zero]
        have h1 : τ' 0 = Fin.last n := Fin.ext (by simpa using hτ)
        have h2 : σ' 0 = Fin.last p := Fin.ext (by simpa using hσ)
        rw [h1, h2, Fin.lastCases_last]
      · simp only [Fin.cases_succ]
        have h1 : τ' a'.succ = (stripFirst τ' hτ a').castSucc := Fin.ext (by simp)
        rw [h1, Fin.lastCases_castSucc]
        apply Fin.ext
        have := congrArg Fin.val (e a')
        simp only [stripFirst_val] at this
        simpa using this

/-- `σ'` begins with its maximum and `τ` does not (or is empty): containment is unchanged. -/
theorem contains_iff_stripFirst_of_not_max {p n : ℕ} (σ' : Perm (p + 1)) (hσ : (σ' 0).val = p)
    (τ : Perm n) (hτ : ∀ h : 0 < n, (τ ⟨0, h⟩).val ≠ n - 1) :
    Contains σ' τ ↔ Contains (stripFirst σ' hσ) τ := by
  constructor
  · intro hc
    rw [contains_iff_exists_strictMono] at hc ⊢
    obtain ⟨f, g, hf, hg, e⟩ := hc
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩
    -- position 0 of `σ'` is not used: otherwise `τ` would begin with its maximum
    have hf0 : (f ⟨0, hn⟩).val ≠ 0 := by
      intro h0
      apply hτ hn
      have h1 : f ⟨0, hn⟩ = 0 := Fin.ext h0
      have h2 : (g (τ ⟨0, hn⟩)).val = p := by rw [← e, h1, hσ]
      -- all values of `g` are `< p + 1`, so `τ ⟨0, hn⟩` is the largest element of `Fin n`
      by_contra hne
      have hlt : (τ ⟨0, hn⟩).val < n - 1 := by have := (τ ⟨0, hn⟩).isLt; omega
      have := hg (show τ ⟨0, hn⟩ < ⟨n - 1, by omega⟩ from hlt)
      rw [Fin.lt_def, h2] at this
      have := (g ⟨n - 1, by omega⟩).isLt
      omega
    have hpos : ∀ a, 0 < (f a).val := by
      intro a
      have := hf.monotone (show (⟨0, hn⟩ : Fin n) ≤ a from Nat.zero_le _)
      rw [Fin.le_def] at this; omega
    have hlt : ∀ b, (g b).val < p := by
      intro b
      have h1 : (g b).val = (σ' (f (τ.symm b))).val := by rw [e, Equiv.apply_symm_apply]
      have h2 : σ' (f (τ.symm b)) ≠ σ' 0 := fun h => by
        have := hpos (τ.symm b); rw [σ'.injective h] at this; exact lt_irrefl _ this
      have h3 : (σ' (f (τ.symm b))).val ≠ p := fun h => h2 (Fin.ext (by rw [h, hσ]))
      have h4 := (σ' (f (τ.symm b))).isLt
      omega
    refine ⟨fun a => ⟨(f a).val - 1, by have := (f a).isLt; have := hpos a; omega⟩,
      fun b => ⟨(g b).val, hlt b⟩, ?_, ?_, ?_⟩
    · intro a b hab
      simp only [Fin.lt_def]
      have := hf hab; rw [Fin.lt_def] at this
      have := hpos a; omega
    · intro a b hab
      simp only [Fin.lt_def]
      have := hg hab; rwa [Fin.lt_def] at this
    · intro a
      apply Fin.ext
      simp only [stripFirst_val]
      have e1 : ((⟨(f a).val - 1, by have := (f a).isLt; have := hpos a; omega⟩ :
          Fin p).succ) = f a := Fin.ext (by simp; have := hpos a; omega)
      rw [e1, e a]
  · intro hc
    exact (contains_stripFirst σ' hσ).trans hc

/-! ## Appending a minimum (by inversion) -/

theorem contains_iff_stripLast_of_min {p n : ℕ} (σ' : Perm (p + 1))
    (hσ : (σ' (Fin.last p)).val = 0) (τ' : Perm (n + 1)) (hτ : (τ' (Fin.last n)).val = 0) :
    Contains σ' τ' ↔ Contains (stripLast σ' hσ) (stripLast τ' hτ) := by
  rw [← contains_symm_iff σ' τ',
    contains_iff_stripFirst_of_max σ'.symm ((symm_zero_val_iff σ').2 hσ) τ'.symm
      ((symm_zero_val_iff τ').2 hτ),
    stripFirst_symm, stripFirst_symm, contains_symm_iff]

theorem contains_iff_stripLast_of_not_min {p n : ℕ} (σ' : Perm (p + 1))
    (hσ : (σ' (Fin.last p)).val = 0) (τ : Perm n)
    (hτ : ∀ h : 0 < n, (τ ⟨n - 1, by omega⟩).val ≠ 0) :
    Contains σ' τ ↔ Contains (stripLast σ' hσ) τ := by
  have hτ' : ∀ h : 0 < n, (τ.symm ⟨0, h⟩).val ≠ n - 1 := by
    intro h e
    apply hτ h
    have : τ.symm ⟨0, h⟩ = ⟨n - 1, by omega⟩ := Fin.ext e
    rw [← this, Equiv.apply_symm_apply]
  rw [← contains_symm_iff σ' τ,
    contains_iff_stripFirst_of_not_max σ'.symm ((symm_zero_val_iff σ').2 hσ) τ.symm hτ',
    stripFirst_symm, contains_symm_iff]

/-! ## The wrapper `1 ⊖ u ⊖ 1` -/

theorem stripFirst_wrap_last_val {k : ℕ} (u : Perm k) :
    (stripFirst (wrap u) (wrap_zero_val u) (Fin.last k)).val = 0 := by
  simp [stripFirst_val, Fin.succ_last]

/-- Stripping both outer entries of `wrap u` recovers `u`. -/
theorem stripLast_stripFirst_wrap {k : ℕ} (u : Perm k) :
    stripLast (stripFirst (wrap u) (wrap_zero_val u)) (stripFirst_wrap_last_val u) = u := by
  apply Equiv.ext
  intro a
  apply Fin.ext
  rw [← Nat.add_right_cancel_iff (n := 1), stripLast_val_add_one]
  simp

/-! ## Reduction -/

/-- The reduction of a pattern (Egge–Mansour 2006, Definition 3.2): delete the first entry when
it is the maximum and the last entry when it is the minimum, then standardise. -/
noncomputable def reducePerm : (n : ℕ) → Perm n → Pattern
  | 0, _ => ⟨0, empty⟩
  | 1, _ => ⟨0, empty⟩
  | m + 2, τ =>
    if hb : (τ 0).val = m + 1 then
      if he : (τ (Fin.last (m + 1))).val = 0 then
        ⟨m, stripLast (stripFirst τ hb) (by simp [stripFirst_val, Fin.succ_last, he])⟩
      else ⟨m + 1, stripFirst τ hb⟩
    else if he : (τ (Fin.last (m + 1))).val = 0 then ⟨m + 1, stripLast τ he⟩
    else ⟨m + 2, τ⟩

noncomputable def reduce (p : Pattern) : Pattern := reducePerm p.1 p.2

@[simp] theorem reduce_empty : reduce ⟨0, empty⟩ = ⟨0, empty⟩ := rfl

@[simp] theorem reduce_singleton : reduce ⟨1, singleton⟩ = ⟨0, empty⟩ := rfl

theorem reduce_length_zero {n : ℕ} (τ : Perm n) (hn : n ≤ 1) : reduce ⟨n, τ⟩ = ⟨0, empty⟩ := by
  interval_cases n <;> rfl

/-- The four cases of the reduction for patterns of length at least two. -/
theorem reduce_of_max_of_min {m : ℕ} (τ : Perm (m + 2)) (hb : (τ 0).val = m + 1)
    (he : (τ (Fin.last (m + 1))).val = 0) :
    reduce ⟨m + 2, τ⟩ =
      ⟨m, stripLast (stripFirst τ hb) (by simp [stripFirst_val, Fin.succ_last, he])⟩ := by
  simp [reduce, reducePerm, hb, he]

theorem reduce_of_max_of_not_min {m : ℕ} (τ : Perm (m + 2)) (hb : (τ 0).val = m + 1)
    (he : ¬ (τ (Fin.last (m + 1))).val = 0) :
    reduce ⟨m + 2, τ⟩ = ⟨m + 1, stripFirst τ hb⟩ := by
  simp [reduce, reducePerm, hb, he]

theorem reduce_of_not_max_of_min {m : ℕ} (τ : Perm (m + 2)) (hb : ¬ (τ 0).val = m + 1)
    (he : (τ (Fin.last (m + 1))).val = 0) :
    reduce ⟨m + 2, τ⟩ = ⟨m + 1, stripLast τ he⟩ := by
  simp [reduce, reducePerm, hb, he]

theorem reduce_of_not_max_of_not_min {m : ℕ} (τ : Perm (m + 2)) (hb : ¬ (τ 0).val = m + 1)
    (he : ¬ (τ (Fin.last (m + 1))).val = 0) :
    reduce ⟨m + 2, τ⟩ = ⟨m + 2, τ⟩ := by
  simp [reduce, reducePerm, hb, he]

theorem contains_of_length_zero {n : ℕ} (σ : Perm n) (τ : Perm 0) : Contains σ τ := by
  rw [Subsingleton.elim τ empty]; exact contains_empty σ

/-- Manuscript Lemma `lem:layers`(b): `1 ⊖ u ⊖ 1` contains `τ` iff `u` contains the reduction
of `τ`.  Includes `τ = ∅` (both sides hold) and `τ = 1` (both sides hold). -/
theorem contains_wrap_iff {k n : ℕ} (u : Perm k) (τ : Perm n) :
    Contains (wrap u) τ ↔ Contains u (reduce ⟨n, τ⟩).2 := by
  match n, τ with
  | 0, τ =>
    simp only [reduce, reducePerm]
    exact ⟨fun _ => contains_empty u, fun _ => contains_of_length_zero _ τ⟩
  | 1, τ =>
    simp only [reduce, reducePerm]
    rw [Subsingleton.elim τ singleton, contains_singleton_iff]
    exact ⟨fun _ => contains_empty u, fun _ => by omega⟩
  | m + 2, τ =>
    by_cases hb : (τ 0).val = m + 1
    · by_cases he : (τ (Fin.last (m + 1))).val = 0
      · rw [reduce_of_max_of_min τ hb he,
          contains_iff_stripFirst_of_max (wrap u) (wrap_zero_val u) τ hb,
          contains_iff_stripLast_of_min _ (stripFirst_wrap_last_val u) _
            (by simp [stripFirst_val, Fin.succ_last, he]),
          stripLast_stripFirst_wrap]
      · rw [reduce_of_max_of_not_min τ hb he,
          contains_iff_stripFirst_of_max (wrap u) (wrap_zero_val u) τ hb,
          contains_iff_stripLast_of_not_min _ (stripFirst_wrap_last_val u) (stripFirst τ hb)
            (fun _ e => he (by
              have : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)).succ = Fin.last (m + 1) :=
                Fin.ext (by simp)
              rwa [stripFirst_val, this] at e)),
          stripLast_stripFirst_wrap]
    · by_cases he : (τ (Fin.last (m + 1))).val = 0
      · rw [reduce_of_not_max_of_min τ hb he,
          contains_iff_stripFirst_of_not_max (wrap u) (wrap_zero_val u) τ (fun _ => hb),
          contains_iff_stripLast_of_min _ (stripFirst_wrap_last_val u) τ he,
          stripLast_stripFirst_wrap]
      · rw [reduce_of_not_max_of_not_min τ hb he,
          contains_iff_stripFirst_of_not_max (wrap u) (wrap_zero_val u) τ (fun _ => hb),
          contains_iff_stripLast_of_not_min _ (stripFirst_wrap_last_val u) τ (fun _ => he),
          stripLast_stripFirst_wrap]

/-- When `τ` neither begins with its maximum nor ends with its minimum, wrapping is invisible. -/
theorem contains_wrap_iff_of_not_max_not_min {k n : ℕ} (u : Perm k) (τ : Perm n)
    (h1 : ∀ h : 0 < n, (τ ⟨0, h⟩).val ≠ n - 1) (h2 : ∀ h : 0 < n, (τ ⟨n - 1, by omega⟩).val ≠ 0) :
    Contains (wrap u) τ ↔ Contains u τ := by
  rw [contains_iff_stripFirst_of_not_max (wrap u) (wrap_zero_val u) τ h1,
    contains_iff_stripLast_of_not_min _ (stripFirst_wrap_last_val u) τ h2,
    stripLast_stripFirst_wrap]

theorem reduce_eq_self_of_not_max_not_min {n : ℕ} (τ : Perm n)
    (h1 : ∀ h : 0 < n, (τ ⟨0, h⟩).val ≠ n - 1) (h2 : ∀ h : 0 < n, (τ ⟨n - 1, by omega⟩).val ≠ 0) :
    reduce ⟨n, τ⟩ = ⟨n, τ⟩ := by
  match n, τ with
  | 0, τ => simp only [reduce, reducePerm]; rw [Subsingleton.elim τ empty]
  | 1, τ => exact absurd (by have := (τ ⟨0, by omega⟩).isLt; omega) (h1 (by omega))
  | m + 2, τ =>
    have hb : ¬ (τ 0).val = m + 1 := h1 (by omega)
    have he : ¬ (τ (Fin.last (m + 1))).val = 0 := by
      intro e
      apply h2 (by omega)
      have : (⟨m + 2 - 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp)
      rw [this]; exact e
    exact reduce_of_not_max_of_not_min τ hb he

/-- Manuscript Lemma `lem:layers`(c): a direct sum of two nonempty permutations neither begins
with its maximum nor ends with its minimum. -/
theorem directSum_zero_val_ne {a b : ℕ} (α : Perm a) (β : Perm b) (ha : 0 < a) (hb : 0 < b) :
    ∀ h : 0 < a + b, (directSum α β ⟨0, h⟩).val ≠ a + b - 1 := by
  intro h
  rw [directSum_val_left _ _ _ ha]
  have := (α ⟨0, ha⟩).isLt; omega

theorem directSum_last_val_ne {a b : ℕ} (α : Perm a) (β : Perm b) (ha : 0 < a) (hb : 0 < b) :
    ∀ h : 0 < a + b, (directSum α β ⟨a + b - 1, by omega⟩).val ≠ 0 := by
  intro h
  rw [directSum_val_right _ _ _ (by simp; omega)]
  omega

theorem reduce_directSum {a b : ℕ} (α : Perm a) (β : Perm b) (ha : 0 < a) (hb : 0 < b) :
    reduce ⟨a + b, directSum α β⟩ = ⟨a + b, directSum α β⟩ :=
  reduce_eq_self_of_not_max_not_min _ (directSum_zero_val_ne α β ha hb)
    (directSum_last_val_ne α β ha hb)

/-- The nontrivial direct-sum case follows from `reduce_directSum` and
`contains_wrap_iff`; the shared statement `contains_wrap_directSum_iff` lives in
`WrapContainment.lean` and is not duplicated here. -/
theorem contains_wrap_directSum_iff_of_reduce {k a b : ℕ} (u : Perm k) (α : Perm a) (β : Perm b)
    (ha : 0 < a) (hb : 0 < b) :
    Contains (wrap u) (directSum α β) ↔ Contains u (directSum α β) := by
  rw [contains_wrap_iff, reduce_directSum α β ha hb]

/-- `3412` is unchanged by reduction, so wrapping preserves `3412`-avoidance. -/
theorem reduce_pattern3412 : reduce ⟨4, pattern3412⟩ = ⟨4, pattern3412⟩ :=
  reduce_eq_self_of_not_max_not_min _ (by decide) (by decide)

theorem contains_wrap_pattern3412_iff {k : ℕ} (u : Perm k) :
    Contains (wrap u) pattern3412 ↔ Contains u pattern3412 :=
  contains_wrap_iff_of_not_max_not_min u _ (by decide) (by decide)

theorem avoids_wrap_pattern3412_iff {k : ℕ} (u : Perm k) :
    Avoids (wrap u) pattern3412 ↔ Avoids u pattern3412 := by
  unfold Avoids; rw [contains_wrap_pattern3412_iff]

/-- The reduced singleton is empty, so its avoidance series vanishes (`singleton_reduction`). -/
theorem avoiderSeries_reduce_singleton : avoiderSeries (reduce ⟨1, singleton⟩).2 = 0 := by
  simp

end EggeMansour.Combinatorics
