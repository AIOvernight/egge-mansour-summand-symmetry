import EggeMansour.Guibert
import EggeMansour.CombinatoricsCounts
import EggeMansour.DirectSumContainment
import EggeMansour.Wrap

/-!
# Guibert constructors preserve avoidance

The fixed-point constructor is bijective onto the fixed-first-point class.
The outer endpoints of `wrap` cannot occur in a 3412 witness, so wrapping
preserves 3412 avoidance in both directions. All counts refer to the actual
finite permutations from `Combinatorics`.
-/

namespace EggeMansour.Combinatorics

@[simp] theorem fixedConstructor_isAvoidingInvolution {n : ℕ} (τ : Perm n) :
    IsAvoidingInvolution (fixedConstructor τ) ↔ IsAvoidingInvolution τ := by
  have hsingle : IsInvolution singleton := by decide
  have hav : ¬ Contains singleton pattern3412 := by decide
  rw [fixedConstructor, isAvoidingInvolution_permCast]
  simp only [IsAvoidingInvolution, isInvolution_directSum_iff, Avoids,
    contains_directSum_iff_of_indecomposable singleton τ pattern3412 (by decide),
    hsingle, hav]
  tauto

@[simp] theorem twoCycles_fixedConstructor {n : ℕ} (τ : Perm n) :
    twoCycles (fixedConstructor τ) = twoCycles τ := by
  have hsingle : twoCycles singleton = 0 := by decide
  simp [fixedConstructor, twoCycles_directSum, hsingle]

theorem fixedConstructor_injective {n : ℕ} :
    Function.Injective (fixedConstructor (n := n)) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have hi := congrArg (fun p : Perm (n+1) => p i.succ) h
  simpa using hi

/-- Actual avoiding involutions of a fixed length. -/
abbrev AvoidingInvolutions (n : ℕ) := {σ : Perm n // IsAvoidingInvolution σ}

/-- Avoiding involutions with fixed first point. -/
abbrev FixedFirstInvolutions (n : ℕ) :=
  {σ : Perm (n+1) // IsAvoidingInvolution σ ∧ σ 0 = 0}

/-- Guibert's fixed-point branch as an equivalence of actual finite permutations. -/
noncomputable def fixedFirstEquiv (n : ℕ) :
    AvoidingInvolutions n ≃ FixedFirstInvolutions n :=
  Equiv.ofBijective
    (fun τ => ⟨fixedConstructor τ.val,
      (fixedConstructor_isAvoidingInvolution τ.val).mpr τ.property,
      fixedConstructor_zero τ.val⟩)
    (by
      constructor
      · intro σ τ h
        apply Subtype.ext
        apply fixedConstructor_injective
        exact congrArg Subtype.val h
      · intro σ
        obtain ⟨τ, hτ, _⟩ := fixed_first_reconstruction σ.val σ.property.1 σ.property.2
        refine ⟨⟨τ,hτ.1⟩, ?_⟩
        apply Subtype.ext
        exact hτ.2.symm)

@[simp] theorem fixedFirstEquiv_apply {n : ℕ} (τ : AvoidingInvolutions n) :
    (fixedFirstEquiv n τ).val = fixedConstructor τ.val := rfl

@[simp] theorem twoCycles_fixedFirstEquiv {n : ℕ} (τ : AvoidingInvolutions n) :
    twoCycles (fixedFirstEquiv n τ).val = twoCycles τ.val := by
  simp

/-- Neither outer endpoint of a wrapped permutation can participate in 3412.
The first selected value must have a larger later value; the last selected
value must have a smaller earlier value. -/
theorem contains_wrap_3412_iff {n : ℕ} (u : Perm n) :
    Contains (wrap u) pattern3412 ↔ Contains u pattern3412 := by
  constructor
  · rintro ⟨f, hf, hp⟩
    have h01 : wrap u (f 0) < wrap u (f 1) := (hp 0 1).mpr (by decide)
    have h23 : wrap u (f 2) < wrap u (f 3) := (hp 2 3).mpr (by decide)
    have hfirst : 0 < (f 0).val := by
      by_contra h
      have he : f 0 = 0 := Fin.ext (show (f 0).val = 0 from by omega)
      rw [he, wrap_zero] at h01
      have := (wrap u (f 1)).isLt
      change n + 1 < (wrap u (f 1)).val at h01
      omega
    have hlast : (f 3).val < n + 1 := by
      by_contra h
      have he : f 3 = Fin.last (n+1) := by
        apply Fin.ext
        have := (f 3).isLt
        simp only [Fin.val_last]
        omega
      rw [he, wrap_last] at h23
      exact (not_lt_of_ge (Fin.zero_le _)) h23
    have hpos (i : Fin 4) : 0 < (f i).val := by
      have h := hf.monotone (Fin.zero_le i)
      change (f 0).val ≤ (f i).val at h
      omega
    have htop (i : Fin 4) : (f i).val < n + 1 := by
      have h := hf.monotone (show i ≤ 3 from by omega)
      change (f i).val ≤ (f 3).val at h
      omega
    let g : Fin 4 → Fin n := fun i => ⟨(f i).val - 1, by have := hpos i; have := htop i; omega⟩
    have heg (i : Fin 4) : (g i).castSucc.succ = f i := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
      dsimp [g]
      have := hpos i
      omega
    refine ⟨g, ?_, ?_⟩
    · intro i j hij
      have h := hf hij
      change (g i).val < (g j).val
      dsimp [g]
      have := hpos i
      have := hpos j
      change (f i).val < (f j).val at h
      omega
    · intro i j
      have h := hp i j
      rw [← heg i, ← heg j, wrap_interior, wrap_interior] at h
      simpa only [Fin.lt_def, Fin.val_succ, Fin.val_castSucc,
        Nat.add_lt_add_iff_right] using h
  · intro h
    exact (contains_wrap u).trans h

@[simp] theorem isAvoidingInvolution_wrap_iff {n : ℕ} (u : Perm n) :
    IsAvoidingInvolution (wrap u) ↔ IsAvoidingInvolution u := by
  simp only [IsAvoidingInvolution, isInvolution_wrap_iff, Avoids, contains_wrap_3412_iff]

/-- Direct sums preserve 3412 avoidance and involutivity in both directions. -/
@[simp] theorem isAvoidingInvolution_directSum_iff {m n : ℕ} (u : Perm m) (v : Perm n) :
    IsAvoidingInvolution (directSum u v) ↔ IsAvoidingInvolution u ∧ IsAvoidingInvolution v := by
  simp only [IsAvoidingInvolution, isInvolution_directSum_iff, Avoids,
    contains_directSum_iff_of_indecomposable u v pattern3412 (by decide), not_or]
  tauto

end EggeMansour.Combinatorics
