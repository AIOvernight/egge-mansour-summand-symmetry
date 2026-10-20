import EggeMansour.Recurrence

noncomputable section
namespace EggeMansour

/-- The canonical solution uses only inverses of endpoint factors. -/
def canonical {R : Type*} [CommRing R] (q s : R) (c : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q * c i * c j)) (i j : ℕ) : R :=
  if hij : i < j then
    ↑((hu i j).unit⁻¹) *
      (c i + (1 - s * c i) * canonical q s c hu (i + 1) j +
        q * c i * ∑ r : ↥(Finset.Ioo i j),
          canonical q s c hu i r.val *
            (canonical q s c hu r.val j - canonical q s c hu (r.val + 1) j))
  else if i = j then c i else 0
termination_by j - i
decreasing_by
  all_goals try have hr := Finset.mem_Ioo.mp r.property
  all_goals omega

@[simp] lemma canonical_diagonal {R : Type*} [CommRing R] (q s : R) (c : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q * c i * c j)) (i : ℕ) :
    canonical q s c hu i i = c i := by
  rw [canonical]
  simp

lemma canonical_lower {R : Type*} [CommRing R] (q s : R) (c : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q * c i * c j)) (i j : ℕ) (hji : j < i) :
    canonical q s c hu i j = 0 := by
  rw [canonical]
  simp [Nat.not_lt.mpr (Nat.le_of_lt hji), Nat.ne_of_gt hji]

lemma canonical_step {R : Type*} [CommRing R] (q s : R) (c : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q * c i * c j)) (i j : ℕ) (hij : i < j) :
    (1 - q * c i * c j) * canonical q s c hu i j =
      c i + (1 - s * c i) * canonical q s c hu (i + 1) j +
        q * c i * ∑ r ∈ Finset.Ioo i j,
          canonical q s c hu i r *
            (canonical q s c hu r j - canonical q s c hu (r + 1) j) := by
  rw [canonical, dite_eq_left hij]
  rw [← mul_assoc, (hu i j).mul_val_inv, one_mul]
  congr 2
  exact Finset.sum_coe_sort (Finset.Ioo i j) (fun r =>
    canonical q s c hu i r * (canonical q s c hu r j - canonical q s c hu (r + 1) j))

lemma canonical_uniform {R : Type*} [CommRing R] (n : ℕ) (q s : R) (c : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q * c i * c j)) :
    UniformRecurrence n q s c (canonical q s c hu) where
  lower i j hji _ := canonical_lower q s c hu i j hji
  diagonal i _ := canonical_diagonal q s c hu i
  step i j hij _ := canonical_step q s c hu i j hij

/-- Applying a ring homomorphism preserves the pole-free recurrence. -/
lemma UniformRecurrence.map {R S : Type*} [CommRing R] [CommRing S]
    {n : ℕ} {q s : R} {c : ℕ → R} {F : ℕ → ℕ → R}
    (hF : UniformRecurrence n q s c F) (φ : R →+* S) :
    UniformRecurrence n (φ q) (φ s) (fun i => φ (c i)) (fun i j => φ (F i j)) where
  lower i j hji hi := by rw [hF.lower i j hji hi, map_zero]
  diagonal i hi := congrArg φ (hF.diagonal i hi)
  step i j hij hj := by
    simpa using congrArg φ (hF.step i j hij hj)

/-- Naturality follows from uniqueness; the selected inverse units do not matter. -/
lemma canonical_map {R S : Type*} [CommRing R] [CommRing S]
    (q s : R) (c : ℕ → R) (hu : ∀ i j, IsUnit (1 - q * c i * c j))
    (φ : R →+* S)
    (hv : ∀ i j, IsUnit (1 - φ q * φ (c i) * φ (c j)))
    (i j : ℕ) (hij : i ≤ j) :
    φ (canonical q s c hu i j) =
      canonical (φ q) (φ s) (fun i => φ (c i)) hv i j := by
  apply UniformRecurrence.eq_of_units
    ((canonical_uniform (j+1) q s c hu).map φ)
    (canonical_uniform (j+1) (φ q) (φ s) (fun i => φ (c i)) hv)
  · intro a b _ _
    exact hv a b
  · exact hij
  · omega

end EggeMansour
