import EggeMansour.GuibertBijection

/-!
# Complete paired branch of Guibert's decomposition

For every nonzero first partner `m`, `pairedFirstEquiv` is the bijection
between the interior/suffix pair and actual avoiding involutions with that
first partner. The construction adds one two-cycle. `guibert_split` packages
the empty, fixed and paired alternatives as equality of varying-length patterns.
-/

namespace EggeMansour.Combinatorics

/-- Assemble the paired branch with prescribed first partner `m`.
The component lengths are forced by the first partner and total size. -/
def pairedConstructor {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) : Perm (n+1) :=
  permCast (by have := m.isLt; omega) (directSum (wrap u) v)

@[simp] theorem pairedConstructor_zero {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) : pairedConstructor m hm u v 0 = m := by
  apply Fin.ext
  simp only [pairedConstructor, permCast_apply]
  change (directSum (wrap u) v (Fin.castAdd _ 0)).val = m.val
  simp only [directSum_castAdd, Fin.val_castAdd, wrap_zero_val]
  omega

@[simp] theorem pairedConstructor_partner {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) : pairedConstructor m hm u v m = 0 := by
  apply Fin.ext
  simp only [pairedConstructor, permCast_apply]
  have hi : Fin.cast (show m.val-1+2+(n-m.val)=n+1 by have := m.isLt; omega).symm m =
      Fin.castAdd (n-m.val) (Fin.last (m.val-1+1)) := by
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_last]
    omega
  rw [hi, directSum_castAdd, wrap_last]
  rfl

@[simp] theorem pairedConstructor_interior {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) (i : Fin (m.val-1)) :
    pairedConstructor m hm u v (intervalIndex 1 (m.val-1) (by omega) i) =
      intervalIndex 1 (m.val-1) (by omega) (u i) := by
  apply Fin.ext
  simp only [pairedConstructor, permCast_apply, intervalIndex_val]
  have hi : Fin.cast (show m.val-1+2+(n-m.val)=n+1 by have := m.isLt; omega).symm
      (intervalIndex 1 (m.val-1) (by omega) i) = Fin.castAdd (n-m.val) i.castSucc.succ := by
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hi, directSum_castAdd]
  simp [Nat.add_comm]

@[simp] theorem pairedConstructor_suffix {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) (i : Fin (n-m.val)) :
    pairedConstructor m hm u v (intervalIndex (m.val+1) (n-m.val) (by omega) i) =
      intervalIndex (m.val+1) (n-m.val) (by omega) (v i) := by
  apply Fin.ext
  simp only [pairedConstructor, permCast_apply, intervalIndex_val]
  have hi : Fin.cast (show m.val-1+2+(n-m.val)=n+1 by have := m.isLt; omega).symm
      (intervalIndex (m.val+1) (n-m.val) (by omega) i) = Fin.natAdd (m.val-1+2) i := by
    apply Fin.ext
    simp only [Fin.val_cast, intervalIndex_val, Fin.val_natAdd]
    omega
  rw [hi, directSum_natAdd]
  simp only [Fin.val_natAdd]
  omega

@[simp] theorem pairedConstructor_isAvoidingInvolution {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) :
    IsAvoidingInvolution (pairedConstructor m hm u v) ↔
      IsAvoidingInvolution u ∧ IsAvoidingInvolution v := by
  rw [pairedConstructor, isAvoidingInvolution_permCast,
    isAvoidingInvolution_directSum_iff, isAvoidingInvolution_wrap_iff]

@[simp] theorem twoCycles_pairedConstructor {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (u : Perm (m.val-1)) (v : Perm (n-m.val)) :
    twoCycles (pairedConstructor m hm u v) = twoCycles u + twoCycles v + 1 := by
  simp only [pairedConstructor, twoCycles_permCast, twoCycles_directSum, twoCycles_wrap]
  omega

theorem pairedConstructor_injective {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val) :
    Function.Injective (fun uv : Perm (m.val-1) × Perm (n-m.val) =>
      pairedConstructor m hm uv.1 uv.2) := by
  rintro ⟨u,v⟩ ⟨u',v'⟩ h
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have hi := congrArg (fun p => p (intervalIndex 1 (m.val-1) (by omega) i)) h
    simp only [pairedConstructor_interior] at hi
    exact (strictMono_intervalIndex _).injective hi
  · apply Equiv.ext
    intro i
    have hi := congrArg (fun p => p (intervalIndex (m.val+1) (n-m.val) (by omega) i)) h
    simp only [pairedConstructor_suffix] at hi
    exact (strictMono_intervalIndex _).injective hi

/-- Guibert's exact unique reconstruction when the first point is paired. -/
theorem paired_first_reconstruction {n : ℕ} (σ : Perm (n+1))
    (hσ : IsAvoidingInvolution σ) (hm : 0 < (σ 0).val) :
    ∃! uv : Perm ((σ 0).val-1) × Perm (n-(σ 0).val),
      IsAvoidingInvolution uv.1 ∧ IsAvoidingInvolution uv.2 ∧
        σ = pairedConstructor (σ 0) hm uv.1 uv.2 := by
  obtain ⟨u,v,hu,hv,heu,hev⟩ := paired_first_decomposition σ hσ hm
  have hp : IsAvoidingInvolution (pairedConstructor (σ 0) hm u v) :=
    (pairedConstructor_isAvoidingInvolution _ _ _ _).mpr ⟨hu,hv⟩
  have heq : σ = pairedConstructor (σ 0) hm u v := by
    apply first_arc_ext σ _ hσ.1 hp.1
    · simp
    · intro i hi0 him
      let j : Fin ((σ 0).val-1) := ⟨i.val-1, by change 0 < i.val at hi0; change i.val < (σ 0).val at him; omega⟩
      have hj : intervalIndex 1 ((σ 0).val-1) (by omega) j = i := by
        apply Fin.ext
        simp only [intervalIndex_val]
        dsimp [j]
        change 0 < i.val at hi0
        omega
      rw [← hj, pairedConstructor_interior]
      exact (heu j).symm
    · intro i hmi
      let j : Fin (n-(σ 0).val) := ⟨i.val-((σ 0).val+1), by
        change (σ 0).val < i.val at hmi
        have := i.isLt
        omega⟩
      have hj : intervalIndex ((σ 0).val+1) (n-(σ 0).val) (by omega) j = i := by
        apply Fin.ext
        simp only [intervalIndex_val]
        dsimp [j]
        change (σ 0).val < i.val at hmi
        omega
      rw [← hj, pairedConstructor_suffix]
      exact (hev j).symm
  refine ⟨(u,v), ⟨hu,hv,heq⟩, ?_⟩
  rintro ⟨u',v'⟩ ⟨_,_,heq'⟩
  apply pairedConstructor_injective (σ 0) hm
  exact heq'.symm.trans heq

/-- Permutation transport does not change the varying-length pattern. -/
theorem pattern_permCast {n m : ℕ} (h : n = m) (σ : Perm n) :
    (⟨m, permCast h σ⟩ : Pattern) = ⟨n, σ⟩ := by
  subst m
  rfl

/-- Guibert's decomposition in varying-length pattern notation, ready for
weighted generating-function partitions. Every component is an actual
3412-avoiding finite involution. -/
theorem guibert_split {n : ℕ} (σ : Perm n) (hσ : IsAvoidingInvolution σ) :
    n = 0 ∨
    (∃ (b : ℕ) (β : Perm b), IsAvoidingInvolution β ∧
      (⟨1+b, directSum singleton β⟩ : Pattern) = ⟨n, σ⟩) ∨
    (∃ (a b : ℕ) (u : Perm a) (β : Perm b), IsAvoidingInvolution u ∧ IsAvoidingInvolution β ∧
      (⟨a+2+b, directSum (wrap u) β⟩ : Pattern) = ⟨n, σ⟩) := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    right
    by_cases hm : (σ 0).val = 0
    · left
      have hzero : σ 0 = 0 := Fin.ext hm
      obtain ⟨β, hβ, _⟩ := fixed_first_reconstruction σ hσ hzero
      refine ⟨n,β,hβ.1,?_⟩
      rw [hβ.2]
      exact (pattern_permCast _ _).symm
    · right
      have hmpos : 0 < (σ 0).val := Nat.pos_of_ne_zero hm
      obtain ⟨⟨u,β⟩, ⟨hu, hβ, heq⟩, _⟩ := paired_first_reconstruction σ hσ hmpos
      refine ⟨(σ 0).val-1,n-(σ 0).val,u,β,hu,hβ,?_⟩
      have heqP : (⟨n+1, pairedConstructor (σ 0) hmpos u β⟩ : Pattern) = ⟨n+1, σ⟩ :=
        congrArg (fun p : Perm (n+1) => (⟨n+1,p⟩ : Pattern)) heq.symm
      exact (pattern_permCast _ _).symm.trans heqP

/-- Avoiding involutions with prescribed first partner. -/
abbrev PairedFirstInvolutions {n : ℕ} (m : Fin (n+1)) :=
  {σ : Perm (n+1) // IsAvoidingInvolution σ ∧ σ 0 = m}

/-- Guibert's paired-point branch as a bijection of actual finite permutations. -/
noncomputable def pairedFirstEquiv {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val) :
    (AvoidingInvolutions (m.val-1) × AvoidingInvolutions (n-m.val)) ≃
      PairedFirstInvolutions m :=
  Equiv.ofBijective
    (fun uv => ⟨pairedConstructor m hm uv.1.val uv.2.val,
      (pairedConstructor_isAvoidingInvolution m hm _ _).mpr ⟨uv.1.property,uv.2.property⟩,
      pairedConstructor_zero m hm _ _⟩)
    (by
      constructor
      · rintro ⟨u,v⟩ ⟨u',v'⟩ h
        have heq : pairedConstructor m hm u.val v.val = pairedConstructor m hm u'.val v'.val :=
          congrArg Subtype.val h
        have hp : (u.val,v.val) = (u'.val,v'.val) := pairedConstructor_injective m hm heq
        apply Prod.ext
        · exact Subtype.ext (congrArg Prod.fst hp)
        · exact Subtype.ext (congrArg Prod.snd hp)
      · rintro ⟨σ,hσ,hσ0⟩
        subst m
        obtain ⟨⟨u,v⟩, ⟨hu, hv, heq⟩, _⟩ := paired_first_reconstruction σ hσ hm
        refine ⟨(⟨u,hu⟩,⟨v,hv⟩), ?_⟩
        apply Subtype.ext
        exact heq.symm)

@[simp] theorem pairedFirstEquiv_apply {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (uv : AvoidingInvolutions (m.val-1) × AvoidingInvolutions (n-m.val)) :
    (pairedFirstEquiv m hm uv).val = pairedConstructor m hm uv.1.val uv.2.val := rfl

@[simp] theorem twoCycles_pairedFirstEquiv {n : ℕ} (m : Fin (n+1)) (hm : 0 < m.val)
    (uv : AvoidingInvolutions (m.val-1) × AvoidingInvolutions (n-m.val)) :
    twoCycles (pairedFirstEquiv m hm uv).val = twoCycles uv.1.val + twoCycles uv.2.val + 1 := by
  simp

end EggeMansour.Combinatorics
