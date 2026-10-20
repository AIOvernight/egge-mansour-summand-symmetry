import EggeMansour.Combinatorics

/-!
# Guibert decomposition: confinement and canonical restrictions

The crossing witness and restrictions below use actual permutations of `Fin n`.
A 3412 occurrence is explicitly constructed from crossing involution arcs.
The fixed-point and paired-point branches restrict to smaller avoiding
involutions. Constructor reconstruction and its converse are separate results.
-/

namespace EggeMansour.Combinatorics

theorem contains3412_of_crossing {n : ℕ} (σ : Perm n) (hσ : IsInvolution σ)
    (a b : Fin n) (hab : a < b) (hba : b < σ a) (hp : σ a < σ b) :
    Contains σ pattern3412 := by
  have hpat : ∀ i, pattern3412 i = ![2,3,0,1] i := by decide
  let f : Fin 4 → Fin n := ![a, b, σ a, σ b]
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, Fin.reduceFinMk]
    all_goals omega
  · intro i j
    fin_cases i <;> fin_cases j <;> simp_all [f, IsInvolution]
    all_goals omega

/-- In an involution avoiding 3412, paired arcs cannot cross. -/
theorem no_crossing {n : ℕ} (σ : Perm n) (hσ : IsInvolution σ)
    (hav : Avoids σ pattern3412) (a b : Fin n)
    (hab : a < b) (hba : b < σ a) : σ b < σ a := by
  by_contra h
  have he : σ a ≠ σ b := fun h => (ne_of_lt hab) (σ.injective h)
  have hp : σ a < σ b := lt_of_le_of_ne (le_of_not_gt h) he
  exact hav (contains3412_of_crossing σ hσ a b hab hba hp)

/-- Every index strictly inside the first paired arc remains inside it. -/
theorem first_arc_interior {n : ℕ} (σ : Perm (n+1)) (hσ : IsInvolution σ)
    (hav : Avoids σ pattern3412) (i : Fin (n+1))
    (hi0 : 0 < i) (him : i < σ 0) : 0 < σ i ∧ σ i < σ 0 := by
  refine ⟨?_, no_crossing σ hσ hav 0 i hi0 him⟩
  have he : σ i ≠ 0 := by
    intro h
    have h' := congrArg σ h
    rw [hσ i] at h'
    exact (ne_of_lt him) h'
  exact Fin.pos_iff_ne_zero.mpr he

/-- Every index after the first paired arc remains after it. -/
theorem first_arc_suffix {n : ℕ} (σ : Perm (n+1)) (hσ : IsInvolution σ)
    (hav : Avoids σ pattern3412) (i : Fin (n+1))
    (hmi : σ 0 < i) : σ 0 < σ i := by
  by_contra h
  have hi0 : i ≠ 0 := by intro h; subst i; exact (not_lt_of_ge (Fin.zero_le _)) hmi
  have hpm : σ i ≠ σ 0 := fun h => hi0 (σ.injective h)
  have hpi : σ i < σ 0 := lt_of_le_of_ne (le_of_not_gt h) hpm
  have hp0 : 0 < σ i := by
    apply Fin.pos_iff_ne_zero.mpr
    intro hz
    have hz' := congrArg σ hz
    rw [hσ i] at hz'
    exact (ne_of_gt hmi) hz'
  have hc := (first_arc_interior σ hσ hav (σ i) hp0 hpi).2
  rw [hσ i] at hc
  exact (not_lt_of_gt hmi) hc

/-- Restrict an involution to any closed, increasingly embedded set of indices.
The result is unique, is an involution, and occurs as a pattern in the original. -/
theorem exists_unique_restriction {n k : ℕ} (σ : Perm n) (hσ : IsInvolution σ)
    (e : Fin k → Fin n) (he : StrictMono e)
    (hclosed : ∀ i, ∃ j, e j = σ (e i)) :
    ∃! τ : Perm k, (∀ i, e (τ i) = σ (e i)) ∧
      IsInvolution τ ∧ Contains σ τ := by
  classical
  let f : Fin k → Fin k := fun i => Classical.choose (hclosed i)
  have hf (i) : e (f i) = σ (e i) := Classical.choose_spec (hclosed i)
  have hff (i) : f (f i) = i := by
    apply he.injective
    rw [hf, hf, hσ]
  let τ : Perm k := { toFun := f, invFun := f, left_inv := hff, right_inv := hff }
  have hcompat (i) : e (τ i) = σ (e i) := hf i
  refine ⟨τ, ⟨hcompat, hff, ?_⟩, ?_⟩
  · refine ⟨e, he, ?_⟩
    intro i j
    rw [← hcompat, ← hcompat]
    exact he.lt_iff_lt
  · intro υ hυ
    apply Equiv.ext
    intro i
    apply he.injective
    rw [hυ.1, hcompat]

/-- Restrictions of a 3412-avoiding involution inherit both properties. -/
theorem exists_avoiding_restriction {n k : ℕ} (σ : Perm n)
    (hσ : IsAvoidingInvolution σ) (e : Fin k → Fin n) (he : StrictMono e)
    (hclosed : ∀ i, ∃ j, e j = σ (e i)) :
    ∃ τ : Perm k, IsAvoidingInvolution τ ∧ (∀ i, e (τ i) = σ (e i)) := by
  obtain ⟨τ, hτ, _⟩ := exists_unique_restriction σ hσ.1 e he hclosed
  refine ⟨τ, ⟨hτ.2.1, ?_⟩, hτ.1⟩
  intro h
  exact hσ.2 (hτ.2.2.trans h)

/-- The fixed-first-point branch of the Guibert decomposition, in coordinates. -/
theorem fixed_first_decomposition {n : ℕ} (σ : Perm (n+1))
    (hσ : IsAvoidingInvolution σ) (hzero : σ 0 = 0) :
    ∃ τ : Perm n, IsAvoidingInvolution τ ∧
      ∀ i : Fin n, (τ i).succ = σ i.succ := by
  apply exists_avoiding_restriction σ hσ Fin.succ
  · intro i j hij
    exact Fin.succ_lt_succ_iff.mpr hij
  · intro i
    have hne : σ i.succ ≠ 0 := by
      rw [← hzero]
      exact fun h => Fin.succ_ne_zero i (σ.injective h)
    exact ⟨(σ i.succ).pred hne, Fin.succ_pred _ _⟩

/-- Increasing coordinates for a contiguous interval of positions. -/
def intervalIndex {n : ℕ} (start len : ℕ) (bound : start + len ≤ n)
    (i : Fin len) : Fin n := ⟨start + i.val, by omega⟩

@[simp] theorem intervalIndex_val {n start len : ℕ} (bound : start + len ≤ n)
    (i : Fin len) : (intervalIndex start len bound i).val = start + i.val := rfl

theorem strictMono_intervalIndex {n start len : ℕ} (bound : start + len ≤ n) :
    StrictMono (intervalIndex start len bound) := by
  intro i j hij
  change start + i.val < start + j.val
  exact Nat.add_lt_add_left hij start

/-- A closed interval in an avoiding involution has a standardized avoiding
involution as its unique restriction. -/
theorem exists_interval_restriction {n start len : ℕ} (σ : Perm n)
    (hσ : IsAvoidingInvolution σ) (bound : start + len ≤ n)
    (hclosed : ∀ i : Fin n, start ≤ i.val → i.val < start + len →
      start ≤ (σ i).val ∧ (σ i).val < start + len) :
    ∃ τ : Perm len, IsAvoidingInvolution τ ∧ ∀ i,
      intervalIndex start len bound (τ i) = σ (intervalIndex start len bound i) := by
  apply exists_avoiding_restriction σ hσ _ (strictMono_intervalIndex bound)
  intro i
  have hci := hclosed (intervalIndex start len bound i) (by simp) (by simp)
  refine ⟨⟨(σ (intervalIndex start len bound i)).val - start, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [intervalIndex_val]
  omega

/-- The paired-first-point branch: the open interval inside the first arc and
its suffix both standardize to actual 3412-avoiding involutions. -/
theorem paired_first_decomposition {n : ℕ} (σ : Perm (n+1))
    (hσ : IsAvoidingInvolution σ) (hm : 0 < (σ 0).val) :
    ∃ (u : Perm ((σ 0).val - 1)) (v : Perm (n - (σ 0).val)),
      IsAvoidingInvolution u ∧ IsAvoidingInvolution v ∧
      (∀ i, intervalIndex 1 ((σ 0).val - 1) (by omega) (u i) =
        σ (intervalIndex 1 ((σ 0).val - 1) (by omega) i)) ∧
      (∀ i, intervalIndex ((σ 0).val + 1) (n - (σ 0).val) (by omega) (v i) =
        σ (intervalIndex ((σ 0).val + 1) (n - (σ 0).val) (by omega) i)) := by
  have hm_bound := (σ 0).isLt
  obtain ⟨u, hu, heu⟩ := exists_interval_restriction σ hσ
    (start := 1) (len := (σ 0).val - 1) (by omega) (by
      intro i hi0 him
      have h := first_arc_interior σ hσ.1 hσ.2 i (by change 0 < i.val; omega) (by
        change i.val < (σ 0).val
        omega)
      constructor
      · have := h.1
        change 0 < (σ i).val at this
        omega
      · have := h.2
        change (σ i).val < (σ 0).val at this
        omega)
  obtain ⟨v, hv, hev⟩ := exists_interval_restriction σ hσ
    (start := (σ 0).val + 1) (len := n - (σ 0).val) (by omega) (by
      intro i hi _
      have h := first_arc_suffix σ hσ.1 hσ.2 i (by
        change (σ 0).val < i.val
        omega)
      constructor
      · exact h
      · have := (σ i).isLt
        omega)
  exact ⟨u, v, hu, hv, heu, hev⟩

/-- Coordinate compatibility determines a restriction uniquely. -/
theorem restriction_unique {n k : ℕ} (σ : Perm n) (e : Fin k → Fin n)
    (he : Function.Injective e) (u v : Perm k)
    (hu : ∀ i, e (u i) = σ (e i)) (hv : ∀ i, e (v i) = σ (e i)) : u = v := by
  apply Equiv.ext
  intro i
  exact he ((hu i).trans (hv i).symm)

/-- The fixed-point branch has a unique smaller avoiding involution. -/
theorem fixed_first_decomposition_unique {n : ℕ} (σ : Perm (n+1))
    (hσ : IsAvoidingInvolution σ) (hzero : σ 0 = 0) :
    ∃! τ : Perm n, IsAvoidingInvolution τ ∧
      ∀ i : Fin n, (τ i).succ = σ i.succ := by
  obtain ⟨τ, hτ⟩ := fixed_first_decomposition σ hσ hzero
  refine ⟨τ, hτ, ?_⟩
  intro υ hυ
  exact restriction_unique σ Fin.succ (Fin.succ_injective n) υ τ hυ.2 hτ.2

/-- The paired-point branch has a unique ordered pair of smaller avoiding
involutions, once its first partner is fixed. -/
theorem paired_first_decomposition_unique {n : ℕ} (σ : Perm (n+1))
    (hσ : IsAvoidingInvolution σ) (hm : 0 < (σ 0).val) :
    ∃! uv : Perm ((σ 0).val - 1) × Perm (n - (σ 0).val),
      IsAvoidingInvolution uv.1 ∧ IsAvoidingInvolution uv.2 ∧
      (∀ i, intervalIndex 1 ((σ 0).val - 1) (by omega) (uv.1 i) =
        σ (intervalIndex 1 ((σ 0).val - 1) (by omega) i)) ∧
      (∀ i, intervalIndex ((σ 0).val + 1) (n - (σ 0).val) (by omega) (uv.2 i) =
        σ (intervalIndex ((σ 0).val + 1) (n - (σ 0).val) (by omega) i)) := by
  obtain ⟨u, v, hu, hv, heu, hev⟩ := paired_first_decomposition σ hσ hm
  refine ⟨(u,v), ⟨hu,hv,heu,hev⟩, ?_⟩
  rintro ⟨u',v'⟩ ⟨_,_,heu',hev'⟩
  apply Prod.ext
  · exact restriction_unique σ _ (strictMono_intervalIndex _).injective u' u heu' heu
  · exact restriction_unique σ _ (strictMono_intervalIndex _).injective v' v hev' hev

/-- First partner plus interior and suffix values determine an involution. -/
theorem first_arc_ext {n : ℕ} (σ τ : Perm (n+1))
    (hσ : IsInvolution σ) (hτ : IsInvolution τ) (hzero : σ 0 = τ 0)
    (hinterior : ∀ i, 0 < i → i < σ 0 → σ i = τ i)
    (hsuffix : ∀ i, σ 0 < i → σ i = τ i) : σ = τ := by
  apply Equiv.ext
  intro i
  by_cases hi0 : i = 0
  · simpa [hi0] using hzero
  by_cases him : i = σ 0
  · subst i
    rw [hσ, hzero, hτ]
  rcases lt_or_gt_of_ne him with hi | hi
  · exact hinterior i (Fin.pos_iff_ne_zero.mpr hi0) hi
  · exact hsuffix i hi

/-- Transport a permutation along equality of its finite length. -/
def permCast {n m : ℕ} (h : n = m) (σ : Perm n) : Perm m := h ▸ σ

@[simp] theorem permCast_apply {n m : ℕ} (h : n = m) (σ : Perm n) (i : Fin m) :
    (permCast h σ i).val = (σ (Fin.cast h.symm i)).val := by
  subst m
  rfl

@[simp] theorem permCast_apply_cast {n m : ℕ} (h : n = m) (σ : Perm n) (i : Fin n) :
    permCast h σ (Fin.cast h i) = Fin.cast h (σ i) := by
  subst m
  rfl

@[simp] theorem isInvolution_permCast {n m : ℕ} (h : n = m) (σ : Perm n) :
    IsInvolution (permCast h σ) ↔ IsInvolution σ := by
  subst m
  rfl

@[simp] theorem contains_permCast {n m k : ℕ} (h : n = m) (σ : Perm n) (τ : Perm k) :
    Contains (permCast h σ) τ ↔ Contains σ τ := by
  subst m
  rfl

@[simp] theorem isAvoidingInvolution_permCast {n m : ℕ} (h : n = m) (σ : Perm n) :
    IsAvoidingInvolution (permCast h σ) ↔ IsAvoidingInvolution σ := by
  subst m
  rfl

@[simp] theorem twoCycles_permCast {n m : ℕ} (h : n = m) (σ : Perm n) :
    twoCycles (permCast h σ) = twoCycles σ := by
  subst m
  rfl

/-- Add a fixed first point, using length `n+1` for the resulting permutation. -/
def fixedConstructor {n : ℕ} (τ : Perm n) : Perm (n+1) :=
  permCast (Nat.add_comm 1 n) (directSum singleton τ)

@[simp] theorem fixedConstructor_zero {n : ℕ} (τ : Perm n) :
    fixedConstructor τ 0 = 0 := by
  apply Fin.ext
  simp only [fixedConstructor, permCast_apply]
  change (directSum singleton τ (Fin.castAdd n (0 : Fin 1))).val = 0
  simp [singleton]

@[simp] theorem fixedConstructor_succ {n : ℕ} (τ : Perm n) (i : Fin n) :
    fixedConstructor τ i.succ = (τ i).succ := by
  apply Fin.ext
  simp only [fixedConstructor, permCast_apply]
  have hi : Fin.cast (Nat.add_comm 1 n).symm i.succ = Fin.natAdd 1 i := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hi, directSum_natAdd]
  simp [Nat.add_comm]

/-- Exact reconstruction of the fixed-point branch in direct-sum notation. -/
theorem fixed_first_reconstruction {n : ℕ} (σ : Perm (n+1))
    (hσ : IsAvoidingInvolution σ) (hzero : σ 0 = 0) :
    ∃! τ : Perm n, IsAvoidingInvolution τ ∧ σ = fixedConstructor τ := by
  obtain ⟨τ, hτ, huniq⟩ := fixed_first_decomposition_unique σ hσ hzero
  have heq : σ = fixedConstructor τ := by
    apply Equiv.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hzero
    · simpa using (hτ.2 j).symm
  refine ⟨τ, ⟨hτ.1, heq⟩, ?_⟩
  intro υ hυ
  apply huniq
  refine ⟨hυ.1, ?_⟩
  intro i
  rw [hυ.2, fixedConstructor_succ]

end EggeMansour.Combinatorics
