import EggeMansour.Localization
import EggeMansour.Canonical

noncomputable section
namespace EggeMansour

lemma map_permuteParams {R S : Type*} {n : ℕ} (ρ : Equiv.Perm (Fin n))
    (c : ℕ → R) (φ : R → S) (i : ℕ) :
    φ (permuteParams ρ c i) = permuteParams ρ (fun j => φ (c j)) i := by
  simp only [permuteParams]
  split_ifs <;> rfl

lemma permute_endpoint_units {R : Type*} [CommRing R] {n : ℕ}
    (ρ : Equiv.Perm (Fin n)) (q : R) (c : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q * c i * c j)) (i j : ℕ) :
    IsUnit (1 - q * permuteParams ρ c i * permuteParams ρ c j) := by
  unfold permuteParams
  split_ifs <;> exact hu _ _

namespace Universal

noncomputable def localQ : Local := algebraMap Base Local q
noncomputable def localS : Local := algebraMap Base Local s
noncomputable def localC (i : ℕ) : Local := algebraMap Base Local (c i)

lemma local_endpoint_unit (i j : ℕ) : IsUnit (1 - localQ * localC i * localC j) := by
  simpa [localQ, localC, denominator] using
    (IsLocalization.map_units Local ⟨denominator i j, denominator_mem i j⟩)

@[simp] lemma toField_q : toField localQ = fieldQ := toField_base q
@[simp] lemma toField_s : toField localS = fieldS := toField_base s
@[simp] lemma toField_c (i : ℕ) : toField (localC i) = fieldC i := toField_base (c i)

@[simp] lemma specialize_q {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j)) :
    specialize q₀ s₀ c₀ hu localQ = q₀ := by simp [localQ]
@[simp] lemma specialize_s {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j)) :
    specialize q₀ s₀ c₀ hu localS = s₀ := by simp [localS]
@[simp] lemma specialize_c {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j)) (i : ℕ) :
    specialize q₀ s₀ c₀ hu (localC i) = c₀ i := by simp [localC]

/-- The full specialization step. A symmetry theorem proved for the genuinely generic
fraction-field parameters transports to arbitrary repeated parameters. The generic
premise is a dependency to be discharged by the matrix/interpolation theorem. -/
theorem uniform_symmetry_of_generic {R : Type*} [CommRing R]
    (n : ℕ) (hn : 0 < n) (ρ : Equiv.Perm (Fin n))
    (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j))
    (hgeneric : ∀ F G : ℕ → ℕ → Field,
      UniformRecurrence n fieldQ fieldS fieldC F →
      UniformRecurrence n fieldQ fieldS (permuteParams ρ fieldC) G →
      F 0 (n - 1) = G 0 (n - 1))
    {F G : ℕ → ℕ → R}
    (hF : UniformRecurrence n q₀ s₀ c₀ F)
    (hG : UniformRecurrence n q₀ s₀ (permuteParams ρ c₀) G) :
    F 0 (n - 1) = G 0 (n - 1) := by
  let A := canonical localQ localS localC local_endpoint_unit
  let B := canonical localQ localS (permuteParams ρ localC)
    (permute_endpoint_units ρ localQ localC local_endpoint_unit)
  have hA : UniformRecurrence n localQ localS localC A :=
    canonical_uniform n localQ localS localC local_endpoint_unit
  have hB : UniformRecurrence n localQ localS (permuteParams ρ localC) B :=
    canonical_uniform n localQ localS (permuteParams ρ localC) _
  have hAK : UniformRecurrence n fieldQ fieldS fieldC (fun i j => toField (A i j)) := by
    simpa only [toField_q, toField_s, toField_c] using hA.map toField
  have hBK : UniformRecurrence n fieldQ fieldS (permuteParams ρ fieldC)
      (fun i j => toField (B i j)) := by
    simpa only [toField_q, toField_s, map_permuteParams, toField_c] using hB.map toField
  have hAB : A 0 (n-1) = B 0 (n-1) :=
    toField_injective (hgeneric _ _ hAK hBK)
  let φ := specialize q₀ s₀ c₀ hu
  have hAR : UniformRecurrence n q₀ s₀ c₀ (fun i j => φ (A i j)) := by
    simpa only [φ, specialize_q, specialize_s, specialize_c] using hA.map φ
  have hBR : UniformRecurrence n q₀ s₀ (permuteParams ρ c₀)
      (fun i j => φ (B i j)) := by
    simpa only [φ, specialize_q, specialize_s, map_permuteParams, specialize_c] using hB.map φ
  calc
    F 0 (n-1) = φ (A 0 (n-1)) :=
      hF.eq_of_units hAR (fun i j _ _ => hu i j) 0 (n-1) (Nat.zero_le _) (by omega)
    _ = φ (B 0 (n-1)) := congrArg φ hAB
    _ = G 0 (n-1) :=
      hBR.eq_of_units hG (fun i j _ _ => permute_endpoint_units ρ q₀ c₀ hu i j)
        0 (n-1) (Nat.zero_le _) (by omega)

/-- Specialization at q=x²y and s=1-x, followed by the published recurrence reduction. -/
theorem recurrenceImpliesSymmetry_of_generic
    (hgeneric : ∀ (n : ℕ), 0 < n → ∀ (ρ : Equiv.Perm (Fin n)) (F G : ℕ → ℕ → Field),
      UniformRecurrence n fieldQ fieldS fieldC F →
      UniformRecurrence n fieldQ fieldS (permuteParams ρ fieldC) G →
      F 0 (n - 1) = G 0 (n - 1)) : RecurrenceImpliesSymmetry := by
  intro k ρ c₀ h singleton F G hF hG
  exact uniform_symmetry_of_generic (k+1) (by omega) ρ seriesQ seriesS c₀
    (series_endpoint_unit c₀) (hgeneric (k+1) (by omega) ρ)
    hF.toUniform hG.toUniform

end Universal
end EggeMansour
