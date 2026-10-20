import EggeMansour.WeightedSeries
import EggeMansour.GuibertBijection

namespace EggeMansour.Combinatorics

/-- Actual image of an arbitrary graded family under addition of a fixed first point. -/
def fixedImage (U : ∀ n, Perm n → Prop) (n : ℕ) (σ : Perm n) : Prop :=
  ∃ (m : ℕ) (u : Perm m), U m u ∧ (⟨m + 1, fixedConstructor u⟩ : Pattern) = ⟨n, σ⟩

/-- Actual image of an arbitrary graded family under wrapping. -/
def wrapImage (U : ∀ n, Perm n → Prop) (n : ℕ) (σ : Perm n) : Prop :=
  ∃ (m : ℕ) (u : Perm m), U m u ∧ (⟨m + 2, wrap u⟩ : Pattern) = ⟨n, σ⟩

/-- Actual paired-branch image of two arbitrary graded families. -/
def pairedImage (U V : ∀ n, Perm n → Prop) (n : ℕ) (σ : Perm n) : Prop :=
  ∃ (a b : ℕ) (u : Perm a) (v : Perm b), U a u ∧ V b v ∧
    (⟨a + 2 + b, directSum (wrap u) v⟩ : Pattern) = ⟨n, σ⟩

/-- The fixed constructor is the same varying-length pattern as `1 ⊕ u`. -/
theorem pattern_fixedConstructor {m : ℕ} (u : Perm m) :
    (⟨m + 1, fixedConstructor u⟩ : Pattern) = ⟨1 + m, directSum singleton u⟩ := by
  have transport : ∀ {a b : ℕ} (h : a = b) (σ : Perm a),
      (⟨b, permCast h σ⟩ : Pattern) = ⟨a, σ⟩ := by
    intro a b h σ
    subst h
    rfl
  exact transport (Nat.add_comm 1 m) (directSum singleton u)

/-- Direct-sum form of the fixed image, matching `guibert_split`. -/
theorem fixedImage_iff_directSum (U : ∀ n, Perm n → Prop) (n : ℕ) (σ : Perm n) :
    fixedImage U n σ ↔ ∃ (m : ℕ) (u : Perm m), U m u ∧
      (⟨1 + m, directSum singleton u⟩ : Pattern) = ⟨n, σ⟩ := by
  constructor
  · rintro ⟨m, u, hu, heq⟩
    exact ⟨m, u, hu, (pattern_fixedConstructor u).symm.trans heq⟩
  · rintro ⟨m, u, hu, heq⟩
    exact ⟨m, u, hu, (pattern_fixedConstructor u).trans heq⟩

noncomputable section

/-- Adding a fixed first point multiplies the actual weighted series by x. -/
theorem weightSeries_fixedImage (U : ∀ n, Perm n → Prop) :
    weightSeries (fixedImage U) = seriesX * weightSeries U := by
  simpa [seriesX] using weightSeries_shift 1 0 (@fixedConstructor)
    (fun _ _ _ h => fixedConstructor_injective h)
    (by intro m u; simp) U (fixedImage U) (by intro n σ; rfl)

/-- Wrapping multiplies the actual weighted series by x²y. -/
theorem weightSeries_wrapImage (U : ∀ n, Perm n → Prop) :
    weightSeries (wrapImage U) = seriesQ * weightSeries U := by
  simpa [seriesQ] using weightSeries_shift 2 1 (@wrap)
    (fun _ _ _ h => wrap_injective h)
    (fun _ _ => twoCycles_wrap _) U (wrapImage U) (by intro n σ; rfl)

private noncomputable def constructorFirstValue (p : Pattern) : ℕ :=
  if h : 0 < p.1 then (p.2 ⟨0, h⟩).val else 0

private theorem constructorFirstValue_wrapSum {a b : ℕ} (u : Perm a) (v : Perm b) :
    constructorFirstValue ⟨a + 2 + b, directSum (wrap u) v⟩ = a + 1 := by
  unfold constructorFirstValue
  split_ifs with h
  · change (directSum (wrap u) v (Fin.castAdd b 0)).val = a + 1
    rw [directSum_castAdd]
    exact wrap_zero_val u
  · simp only at h
    omega

/-- Pairing the first point around an interior and appending a suffix gives the
product x²y U V. The first selected partner determines the split uniquely. -/
theorem weightSeries_pairedImage (U V : ∀ n, Perm n → Prop) :
    weightSeries (pairedImage U V) = seriesQ * weightSeries U * weightSeries V := by
  have hmul : weightSeries (pairedImage U V) =
      weightSeries (wrapImage U) * weightSeries V := by
    apply weightSeries_mul
    · intro a b α β hα hβ
      obtain ⟨m, u, hu, heq⟩ := hα
      refine ⟨m, b, u, β, hu, hβ, ?_⟩
      exact congrArg (fun p : Pattern => (⟨p.1 + b, directSum p.2 β⟩ : Pattern)) heq
    · intro n σ hσ
      obtain ⟨a, b, u, v, hu, hv, heq⟩ := hσ
      exact ⟨a + 2, b, wrap u, v, ⟨a, u, hu, rfl⟩, hv, heq⟩
    · intro a b a' b' α β α' β' hα hα' heq
      obtain ⟨m, u, hu, heu⟩ := hα
      obtain ⟨m', u', hu', heu'⟩ := hα'
      have e1 := congrArg (fun p : Pattern => (⟨p.1 + b, directSum p.2 β⟩ : Pattern)) heu
      have e2 := congrArg (fun p : Pattern => (⟨p.1 + b', directSum p.2 β'⟩ : Pattern)) heu'
      have ewrap := e1.trans (heq.trans e2.symm)
      have hfirst := congrArg constructorFirstValue ewrap
      rw [constructorFirstValue_wrapSum, constructorFirstValue_wrapSum] at hfirst
      have hlen := congrArg Sigma.fst heu
      have hlen' := congrArg Sigma.fst heu'
      dsimp only at hlen hlen'
      omega
  rw [hmul, weightSeries_wrapImage]

end
end EggeMansour.Combinatorics
