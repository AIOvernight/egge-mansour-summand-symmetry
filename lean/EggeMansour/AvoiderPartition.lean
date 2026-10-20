import EggeMansour.ConstructorSeries
import EggeMansour.GuibertPair
import EggeMansour.PrefixCells
import EggeMansour.WrappedSeries

/-!
# Actual avoider classes as disjoint constructor images

This module supplies the predicate-level classification. It uses the proved
Guibert decomposition and maximal-prefix cells, and assumes no series identity.
-/

namespace EggeMansour.Combinatorics

def avoiderClass (ps : List Pattern) (n : ℕ) (σ : Perm n) : Prop :=
  IsAvoidingInvolution σ ∧ Avoids σ (sumPatterns ps).2

def fixedAvoidingInterior (ps : List Pattern) (n : ℕ) (u : Perm n) : Prop :=
  IsAvoidingInvolution u ∧ Avoids (fixedConstructor u) (sumPatterns ps).2

def pairedAvoidingInterior (ps : List Pattern) (t n : ℕ) (u : Perm n) : Prop :=
  IsAvoidingInvolution u ∧ prefixCell (wrap u) ps t

def avoidingSuffix (ps : List Pattern) (t n : ℕ) (v : Perm n) : Prop :=
  IsAvoidingInvolution v ∧ Avoids v (sumPatterns (ps.drop t)).2

private theorem pattern_prop_iff {m n : ℕ} {π : Perm m} {σ : Perm n}
    (P : ∀ k, Perm k → Prop) (h : (⟨m, π⟩ : Pattern) = ⟨n, σ⟩) :
    P m π ↔ P n σ :=
  Iff.of_eq (congrArg (fun p : Pattern => P p.1 p.2) h)

theorem avoiderClass_iff_partition_nat (ps : List Pattern) (hne : ps ≠ [])
    (hps : ∀ p ∈ ps, IndecomposablePattern p) (n : ℕ) (σ : Perm n) :
    avoiderClass ps n σ ↔ n = 0 ∨ fixedImage (fixedAvoidingInterior ps) n σ ∨
      ∃ t < ps.length, pairedImage (pairedAvoidingInterior ps t) (avoidingSuffix ps t) n σ := by
  have hsize : 0 < (sumPatterns ps).1 := by
    cases ps with
    | nil => exact (hne rfl).elim
    | cons p ps => exact sumPatterns_pos_of_head p ps (hps p (by simp)).1
  constructor
  · rintro ⟨hσ, hav⟩
    rcases guibert_split σ hσ with hn | hf | hp
    · exact Or.inl hn
    · rcases hf with ⟨b, u, hu, heq⟩
      have heq' := (pattern_fixedConstructor u).trans heq
      have hav' : Avoids (fixedConstructor u) (sumPatterns ps).2 :=
        (pattern_prop_iff (fun _ v => Avoids v (sumPatterns ps).2) heq').mpr hav
      exact Or.inr (Or.inl ⟨b, u, ⟨hu, hav'⟩, heq'⟩)
    · rcases hp with ⟨a, b, u, v, hu, hv, heq⟩
      have hav' : Avoids (directSum (wrap u) v) (sumPatterns ps).2 :=
        (pattern_prop_iff (fun _ w => Avoids w (sumPatterns ps).2) heq).mpr hav
      obtain ⟨t, ht, hc, hsuf⟩ :=
        (avoids_directSum_iff_exists_prefixCell (wrap u) v ps hps).mp hav'
      exact Or.inr (Or.inr ⟨t, ht, a, b, u, v, ⟨hu, hc⟩, ⟨hv, hsuf⟩, heq⟩)
  · rintro (hn | hf | hp)
    · subst n
      have heq : σ = empty := Subsingleton.elim _ _
      subst σ
      exact ⟨isAvoidingInvolution_empty, avoids_of_length_lt empty _ hsize⟩
    · rcases hf with ⟨b, u, ⟨hu, hav⟩, heq⟩
      apply (pattern_prop_iff (avoiderClass ps) heq).mp
      exact ⟨(fixedConstructor_isAvoidingInvolution u).mpr hu, hav⟩
    · rcases hp with ⟨t, ht, a, b, u, v, ⟨hu, hc⟩, ⟨hv, hsuf⟩, heq⟩
      apply (pattern_prop_iff (avoiderClass ps) heq).mp
      refine ⟨?_, ?_⟩
      · exact (isAvoidingInvolution_directSum_iff (wrap u) v).mpr
          ⟨(isAvoidingInvolution_wrap_iff u).mpr hu, hv⟩
      · exact (avoids_directSum_iff_exists_prefixCell (wrap u) v ps hps).mpr
          ⟨t, ht, hc, hsuf⟩

/-- Finite-index form for a finite sum of the paired constructor classes. -/
theorem avoiderClass_iff_partition (ps : List Pattern) (hne : ps ≠ [])
    (hps : ∀ p ∈ ps, IndecomposablePattern p) (n : ℕ) (σ : Perm n) :
    avoiderClass ps n σ ↔ n = 0 ∨ fixedImage (fixedAvoidingInterior ps) n σ ∨
      ∃ t : Fin ps.length,
        pairedImage (pairedAvoidingInterior ps t.val) (avoidingSuffix ps t.val) n σ := by
  rw [avoiderClass_iff_partition_nat ps hne hps]
  constructor
  · rintro (h | h | ⟨t, ht, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨⟨t, ht⟩, h⟩)
  · rintro (h | h | ⟨t, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨t.val, t.isLt, h⟩)

theorem fixedImage_ne_zero {U : ∀ n, Perm n → Prop} {n : ℕ} {σ : Perm n}
    (h : fixedImage U n σ) : n ≠ 0 := by
  obtain ⟨m, u, _, heq⟩ := h
  have hlen := congrArg Sigma.fst heq
  dsimp only at hlen
  omega

theorem pairedImage_ne_zero {U V : ∀ n, Perm n → Prop} {n : ℕ} {σ : Perm n}
    (h : pairedImage U V n σ) : n ≠ 0 := by
  obtain ⟨a, b, u, v, _, _, heq⟩ := h
  have hlen := congrArg Sigma.fst heq
  dsimp only at hlen
  omega

/-- First value of a varying-length permutation, with value zero for the empty case. -/
def patternFirstValue (p : Pattern) : ℕ :=
  if h : 0 < p.1 then (p.2 ⟨0, h⟩).val else 0

@[simp] theorem patternFirstValue_fixed {m : ℕ} (u : Perm m) :
    patternFirstValue ⟨m + 1, fixedConstructor u⟩ = 0 := by
  unfold patternFirstValue
  split_ifs with h
  · change (fixedConstructor u 0).val = 0
    simp
  · rfl

@[simp] theorem patternFirstValue_paired {a b : ℕ} (u : Perm a) (v : Perm b) :
    patternFirstValue ⟨a + 2 + b, directSum (wrap u) v⟩ = a + 1 := by
  unfold patternFirstValue
  split_ifs with h
  · change (directSum (wrap u) v (Fin.castAdd b 0)).val = a + 1
    rw [directSum_castAdd]
    exact wrap_zero_val u
  · simp only at h
    omega

/-- The fixed and paired constructor classes cannot intersect. -/
theorem fixedImage_not_pairedImage (U V W : ∀ n, Perm n → Prop) (n : ℕ) (σ : Perm n) :
    ¬ (fixedImage U n σ ∧ pairedImage V W n σ) := by
  rintro ⟨⟨m, u, _, heq⟩, ⟨a, b, v, w, _, _, heq'⟩⟩
  have hfirst := congrArg patternFirstValue (heq.trans heq'.symm)
  rw [patternFirstValue_fixed, patternFirstValue_paired] at hfirst
  omega

/-- The first partner determines the interior length; the actual permutation
then determines the interior and suffix separately. -/
theorem pairedPattern_left_eq {a b a' b' : ℕ}
    (u : Perm a) (v : Perm b) (u' : Perm a') (v' : Perm b')
    (heq : (⟨a + 2 + b, directSum (wrap u) v⟩ : Pattern) =
      ⟨a' + 2 + b', directSum (wrap u') v'⟩) :
    (⟨a, u⟩ : Pattern) = ⟨a', u'⟩ := by
  have hfirst := congrArg patternFirstValue heq
  rw [patternFirstValue_paired, patternFirstValue_paired] at hfirst
  have ha : a = a' := by omega
  subst a'
  have hlen := congrArg Sigma.fst heq
  dsimp only at hlen
  have hb : b = b' := by omega
  subst b'
  have hperm : directSum (wrap u) v = directSum (wrap u') v' :=
    eq_of_heq (Sigma.mk.inj_iff.mp heq).2
  have hu : u = u' := wrap_injective (directSum_injective hperm).1
  subst u'
  rfl

/-- Distinct prefix cells remain disjoint after applying the paired constructor. -/
theorem pairedAvoidingImages_unique (ps : List Pattern) (s t n : ℕ) (σ : Perm n)
    (hs : pairedImage (pairedAvoidingInterior ps s) (avoidingSuffix ps s) n σ)
    (ht : pairedImage (pairedAvoidingInterior ps t) (avoidingSuffix ps t) n σ) : s = t := by
  obtain ⟨a, b, u, v, ⟨_, hcell⟩, _, heq⟩ := hs
  obtain ⟨a', b', u', v', ⟨_, hcell'⟩, _, heq'⟩ := ht
  have hleft := pairedPattern_left_eq u v u' v' (heq.trans heq'.symm)
  have hc : prefixCell (wrap u) ps t := by
    change (fun p : Pattern => prefixCell (wrap p.2) ps t) ⟨a, u⟩
    rw [hleft]
    exact hcell'
  exact prefixCell_unique (wrap u) ps hcell hc

theorem pairedAvoidingImages_fin_unique (ps : List Pattern) (s t : Fin ps.length)
    (n : ℕ) (σ : Perm n)
    (hs : pairedImage (pairedAvoidingInterior ps s.val) (avoidingSuffix ps s.val) n σ)
    (ht : pairedImage (pairedAvoidingInterior ps t.val) (avoidingSuffix ps t.val) n σ) : s = t :=
  Fin.ext (pairedAvoidingImages_unique ps s.val t.val n σ hs ht)

theorem empty_partitionImages_disjoint (ps : List Pattern) (n : ℕ) (σ : Perm n) :
    ¬ (n = 0 ∧ (fixedImage (fixedAvoidingInterior ps) n σ ∨
      ∃ t : Fin ps.length,
        pairedImage (pairedAvoidingInterior ps t.val) (avoidingSuffix ps t.val) n σ)) := by
  rintro ⟨hn, h | ⟨t, h⟩⟩
  · exact fixedImage_ne_zero h hn
  · exact pairedImage_ne_zero h hn

theorem fixed_pairedPartitionImages_disjoint (ps : List Pattern) (n : ℕ) (σ : Perm n) :
    ¬ (fixedImage (fixedAvoidingInterior ps) n σ ∧
      ∃ t : Fin ps.length,
        pairedImage (pairedAvoidingInterior ps t.val) (avoidingSuffix ps t.val) n σ) := by
  rintro ⟨hfixed, t, hpaired⟩
  exact fixedImage_not_pairedImage _ _ _ n σ ⟨hfixed, hpaired⟩

end EggeMansour.Combinatorics
