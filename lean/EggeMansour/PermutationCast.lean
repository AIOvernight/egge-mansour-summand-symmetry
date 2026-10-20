import EggeMansour.Combinatorics

/-!
# Shared transport of actual finite permutations

One definition serves containment, splitting, and weighted-series modules.
Its application rule is definitionally the conjugation by `finCongr`.
Guibert's already-reviewed `permCast` remains a separate API; both agree
with equality transport by `castPerm_eq_transport`.
-/

namespace EggeMansour.Combinatorics

/-- Transport a permutation along an equality of lengths. -/
def castPerm {m n : ℕ} (h : m = n) (σ : Perm m) : Perm n :=
  (finCongr h).symm.trans (σ.trans (finCongr h))

@[simp] theorem castPerm_rfl {m : ℕ} (σ : Perm m) : castPerm rfl σ = σ := by
  ext i
  simp [castPerm]

theorem castPerm_apply {m n : ℕ} (h : m = n) (σ : Perm m) (i : Fin n) :
    castPerm h σ i = Fin.cast h (σ (Fin.cast h.symm i)) := rfl

theorem castPerm_injective {m n : ℕ} (h : m = n) {σ τ : Perm m}
    (e : castPerm h σ = castPerm h τ) : σ = τ := by
  subst h
  simpa using e

/-- Equality in `Pattern` is exactly a length equality with a cast. -/
theorem pattern_mk_eq_iff {m n : ℕ} (π : Perm m) (σ : Perm n) :
    (⟨m, π⟩ : Pattern) = ⟨n, σ⟩ ↔ ∃ h : m = n, castPerm h π = σ := by
  constructor
  · intro e
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp e
    subst h1
    exact ⟨rfl, by simpa using eq_of_heq h2⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- Any graded property transports along casts. -/
theorem castPerm_prop {m n : ℕ} (h : m = n) (π : Perm m)
    (P : ∀ k, Perm k → Prop) (hP : P m π) : P n (castPerm h π) := by
  subst h
  simpa using hP

theorem castPerm_prop_iff {m n : ℕ} (h : m = n) (π : Perm m)
    (P : ∀ k, Perm k → Prop) : P n (castPerm h π) ↔ P m π := by
  subst h
  simp

@[simp] theorem twoCycles_castPerm {m n : ℕ} (h : m = n) (σ : Perm m) :
    twoCycles (castPerm h σ) = twoCycles σ := by
  subst h
  simp

@[simp] theorem contains_castPerm {m n k : ℕ} (h : m = n) (σ : Perm m) (τ : Perm k) :
    Contains (castPerm h σ) τ ↔ Contains σ τ := by
  subst h
  simp

@[simp] theorem isInvolution_castPerm {m n : ℕ} (h : m = n) (σ : Perm m) :
    IsInvolution (castPerm h σ) ↔ IsInvolution σ := by
  subst h
  simp

/-- Coordinate rule retained for the containment/splitting API. -/
@[simp] theorem castPerm_val {n m : ℕ} (e : n = m) (σ : Perm n) (i : Fin m) :
    (castPerm e σ i).val = (σ ⟨i, e ▸ i.isLt⟩).val := by
  subst e
  simp [castPerm]

/-- Transport of the forbidden pattern preserves containment. -/
theorem contains_castPerm_iff {n k k' : ℕ} (σ : Perm n) (e : k = k') (τ : Perm k) :
    Contains σ (castPerm e τ) ↔ Contains σ τ := by
  subst e
  simp

/-- Host-transport alias retained for the containment/splitting API. -/
theorem castPerm_contains_iff {n n' k : ℕ} (e : n = n') (σ : Perm n) (τ : Perm k) :
    Contains (castPerm e σ) τ ↔ Contains σ τ := contains_castPerm e σ τ

/-- The conjugation implementation agrees with ordinary equality transport. -/
theorem castPerm_eq_transport {m n : ℕ} (h : m = n) (σ : Perm m) :
    castPerm h σ = h ▸ σ := by
  subst h
  simp

@[simp] theorem castPerm_trans {a b c : ℕ} (hab : a = b) (hbc : b = c) (σ : Perm a) :
    castPerm hbc (castPerm hab σ) = castPerm (hab.trans hbc) σ := by
  subst hab
  subst hbc
  simp

theorem castPerm_apply_cast {m n : ℕ} (h : m = n) (σ : Perm m) (i : Fin m) :
    castPerm h σ (Fin.cast h i) = Fin.cast h (σ i) := by
  subst h
  simp

end EggeMansour.Combinatorics
