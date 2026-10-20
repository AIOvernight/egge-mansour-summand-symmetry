import EggeMansour.CombinatoricsCounts

/-!
# Outer transposition constructor

`wrap u` is the actual permutation `1 ⊖ u ⊖ 1`, with a fixed public
length `n + 2`. The constructor swaps the two outer positions and transports
the interior permutation by adding one to both coordinates.
-/

namespace EggeMansour.Combinatorics

private def wrapFun {n : ℕ} (u : Fin n → Fin n) : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases (Fin.last (n + 1)) (Fin.lastCases 0 (fun i => (u i).castSucc.succ))

private theorem wrapFun_comp {n : ℕ} (u v : Fin n → Fin n)
    (h : ∀ i, u (v i) = i) (i : Fin (n + 2)) : wrapFun u (wrapFun v i) = i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [wrapFun, ← Fin.succ_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [wrapFun, ← Fin.succ_last]
    · simp [wrapFun, h k]

def wrap {n : ℕ} (u : Perm n) : Perm (n + 2) where
  toFun := wrapFun u
  invFun := wrapFun u.symm
  left_inv := wrapFun_comp _ _ u.symm_apply_apply
  right_inv := wrapFun_comp _ _ u.apply_symm_apply

@[simp] theorem wrap_zero {n : ℕ} (u : Perm n) :
    wrap u 0 = Fin.last (n + 1) := by
  simp [wrap, wrapFun, ← Fin.succ_last]

@[simp] theorem wrap_last {n : ℕ} (u : Perm n) :
    wrap u (Fin.last (n + 1)) = 0 := by
  simp [wrap, wrapFun, ← Fin.succ_last]

@[simp] theorem wrap_interior {n : ℕ} (u : Perm n) (i : Fin n) :
    wrap u i.castSucc.succ = (u i).castSucc.succ := by
  simp [wrap, wrapFun]

@[simp] theorem wrap_zero_val {n : ℕ} (u : Perm n) : (wrap u 0).val = n + 1 := by
  simp

@[simp] theorem wrap_last_val {n : ℕ} (u : Perm n) :
    (wrap u (Fin.last (n + 1))).val = 0 := by
  simp

@[simp] theorem wrap_interior_val {n : ℕ} (u : Perm n) (i : Fin n) :
    (wrap u i.castSucc.succ).val = (u i).val + 1 := by
  simp

theorem wrap_apply_interior_val {n : ℕ} (u : Perm n) (i : Fin (n + 2))
    (h0 : 0 < i.val) (hlast : i.val < n + 1) :
    (wrap u i).val = (u ⟨i.val - 1, by omega⟩).val + 1 := by
  have heq : i = (⟨i.val - 1, by omega⟩ : Fin n).castSucc.succ := by
    apply Fin.ext
    simp
    omega
  conv_lhs => rw [heq]
  exact wrap_interior_val _ _

@[simp] theorem isInvolution_wrap_iff {n : ℕ} (u : Perm n) :
    IsInvolution (wrap u) ↔ IsInvolution u := by
  constructor
  · intro h i
    have hi := h i.castSucc.succ
    simpa using hi
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp [h k]

theorem wrap_injective {n : ℕ} : Function.Injective (@wrap n) := by
  intro u v h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun p : Perm (n + 2) => p i.castSucc.succ) h
  simpa using hi

@[simp] theorem wrap_inj {n : ℕ} {u v : Perm n} : wrap u = wrap v ↔ u = v :=
  wrap_injective.eq_iff

theorem contains_wrap {n : ℕ} (u : Perm n) : Contains (wrap u) u := by
  refine ⟨fun i => i.castSucc.succ, ?_, ?_⟩
  · intro i j hij
    exact Nat.succ_lt_succ hij
  · intro i j
    simp only [wrap_interior]
    exact Nat.succ_lt_succ_iff

@[simp] theorem twoCycles_wrap {n : ℕ} (u : Perm n) :
    twoCycles (wrap u) = twoCycles u + 1 := by
  have hmid (i : Fin n) : i.castSucc.succ < wrap u i.castSucc.succ ↔ i < u i := by
    simp only [wrap_interior]
    exact Nat.succ_lt_succ_iff
  simp only [twoCycles, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [wrap_zero, hmid, Fin.succ_last, wrap_last]
  have hfirst : (0 : Fin (n + 2)) < Fin.last (n + 1) := by
    change 0 < n + 1
    omega
  have hlast : ¬ Fin.last (n + 1) < (0 : Fin (n + 2)) := by
    simp
  simp only [hfirst, hlast, ↓reduceIte, add_zero]
  omega

@[simp] theorem isIndecomposable_wrap {n : ℕ} (u : Perm n) :
    IsIndecomposable (wrap u) := by
  refine ⟨by omega, ?_⟩
  intro k hk
  refine ⟨0, hk, ?_⟩
  simp only [wrap_zero_val]
  omega

end EggeMansour.Combinatorics
