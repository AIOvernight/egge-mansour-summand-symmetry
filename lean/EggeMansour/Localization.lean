import EggeMansour.Interfaces

/-! Universal localization used for pole-free specialization. -/
namespace EggeMansour
namespace Universal

abbrev Base := MvPolynomial (ℕ ⊕ Bool) ℤ
noncomputable def q : Base := MvPolynomial.X (.inr false)
noncomputable def s : Base := MvPolynomial.X (.inr true)
noncomputable def c (i : ℕ) : Base := MvPolynomial.X (.inl i)
noncomputable def denominator (i j : ℕ) : Base := 1 - q * c i * c j
noncomputable def denominators : Submonoid Base :=
  Submonoid.closure (Set.range fun ij : ℕ × ℕ => denominator ij.1 ij.2)
abbrev Local := Localization denominators
abbrev Field := FractionRing Base

lemma denominator_mem (i j : ℕ) : denominator i j ∈ denominators :=
  Submonoid.subset_closure ⟨(i,j), rfl⟩

lemma denominator_ne_zero (i j : ℕ) : denominator i j ≠ 0 := by
  intro h
  have := congrArg MvPolynomial.constantCoeff h
  simp [denominator, q, c] at this

lemma denominators_ne_zero (a : denominators) : (a : Base) ≠ 0 := by
  rcases a with ⟨a, ha⟩
  induction ha using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨⟨i,j⟩, rfl⟩ := hz
    exact denominator_ne_zero i j
  | one => exact one_ne_zero
  | mul x y hx hy hx' hy' => exact mul_ne_zero hx' hy'

noncomputable def baseEval {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R) : Base →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R)
    (Sum.elim c₀ fun b => if b then s₀ else q₀)

@[simp] theorem baseEval_q {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R) :
    baseEval q₀ s₀ c₀ q = q₀ := by simp [baseEval, q]
@[simp] theorem baseEval_s {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R) :
    baseEval q₀ s₀ c₀ s = s₀ := by simp [baseEval, s]
@[simp] theorem baseEval_c {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R) (i : ℕ) :
    baseEval q₀ s₀ c₀ (c i) = c₀ i := by simp [baseEval, c]
@[simp] theorem baseEval_denominator {R : Type*} [CommRing R]
    (q₀ s₀ : R) (c₀ : ℕ → R) (i j : ℕ) :
    baseEval q₀ s₀ c₀ (denominator i j) = 1 - q₀ * c₀ i * c₀ j := by
  simp [denominator]

lemma eval_units {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j)) (a : denominators) :
    IsUnit (baseEval q₀ s₀ c₀ a) := by
  rcases a with ⟨a, ha⟩
  induction ha using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨⟨i,j⟩, rfl⟩ := hz
    simpa using hu i j
  | one => simp
  | mul x y hx hy hx' hy' => simpa using hx'.mul hy'

/-- Evaluation exists whenever the endpoint factors are units. No distinctness is required. -/
noncomputable def specialize {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j)) : Local →+* R :=
  IsLocalization.lift (eval_units q₀ s₀ c₀ hu)

@[simp] theorem specialize_base {R : Type*} [CommRing R] (q₀ s₀ : R) (c₀ : ℕ → R)
    (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j)) (a : Base) :
    specialize q₀ s₀ c₀ hu (algebraMap Base Local a) = baseEval q₀ s₀ c₀ a :=
  IsLocalization.lift_eq _ _

lemma field_units (a : denominators) : IsUnit (algebraMap Base Field a) := by
  apply isUnit_iff_ne_zero.mpr
  exact fun h => denominators_ne_zero a (IsFractionRing.injective Base Field (by simpa using h))

/-- Faithful comparison of the denominator localization inside the generic fraction field. -/
noncomputable def toField : Local →+* Field := IsLocalization.lift field_units

@[simp] lemma toField_base (a : Base) :
    toField (algebraMap Base Local a) = algebraMap Base Field a :=
  IsLocalization.lift_eq _ _

lemma toField_injective : Function.Injective toField := by
  apply (IsLocalization.lift_injective_iff field_units).mpr
  intro x y
  constructor
  · intro h
    simpa using congrArg toField h
  · intro h
    exact congrArg (algebraMap Base Local) (IsFractionRing.injective Base Field h)

noncomputable def fieldQ : Field := algebraMap Base Field q
noncomputable def fieldS : Field := algebraMap Base Field s
noncomputable def fieldC (i : ℕ) : Field := algebraMap Base Field (c i)
noncomputable def fieldNode (i : ℕ) : Field := (fieldC i)⁻¹ + fieldQ * fieldC i

lemma fieldC_ne_zero (i : ℕ) : fieldC i ≠ 0 := by
  intro h
  have : c i = 0 := IsFractionRing.injective Base Field (by simpa [fieldC] using h)
  exact MvPolynomial.X_ne_zero (R := ℤ) (σ := ℕ ⊕ Bool) (.inl i) this

lemma fieldC_injective : Function.Injective fieldC := by
  intro i j h
  have h' : c i = c j := IsFractionRing.injective Base Field h
  exact Sum.inl_injective (MvPolynomial.X_injective h')

lemma field_endpoint_ne_zero (i j : ℕ) : 1 - fieldQ * fieldC i * fieldC j ≠ 0 := by
  intro h
  apply denominator_ne_zero i j
  apply IsFractionRing.injective Base Field
  simpa [denominator, fieldQ, fieldC] using h

lemma fieldNode_sub (i j : ℕ) :
    fieldNode i - fieldNode j =
      (fieldC j - fieldC i) * (1 - fieldQ * fieldC i * fieldC j) / (fieldC i * fieldC j) := by
  unfold fieldNode
  field_simp [fieldC_ne_zero]
  ring

lemma fieldNode_injective : Function.Injective fieldNode := by
  intro i j h
  by_contra hij
  have hdiff : fieldC j - fieldC i ≠ 0 := sub_ne_zero.mpr (fun hc => hij (fieldC_injective hc).symm)
  have hne : fieldNode i - fieldNode j ≠ 0 := by
    rw [fieldNode_sub]
    exact div_ne_zero (mul_ne_zero hdiff (field_endpoint_ne_zero i j))
      (mul_ne_zero (fieldC_ne_zero i) (fieldC_ne_zero j))
  exact hne (sub_eq_zero.mpr h)

/-- A generic equality between elements of the smaller localization specializes in every
coefficient ring where the endpoint denominators are units, including coincident parameters. -/
theorem specialize_eq_of_generic_eq {R : Type*} [CommRing R]
    (q₀ s₀ : R) (c₀ : ℕ → R) (hu : ∀ i j, IsUnit (1 - q₀ * c₀ i * c₀ j))
    {a b : Local} (h : toField a = toField b) :
    specialize q₀ s₀ c₀ hu a = specialize q₀ s₀ c₀ hu b :=
  congrArg (specialize q₀ s₀ c₀ hu) (toField_injective h)

/-- The x² factor makes every endpoint denominator a unit, without any condition on c. -/
lemma series_endpoint_unit (c₀ : ℕ → Series) (i j : ℕ) :
    IsUnit (1 - seriesQ * c₀ i * c₀ j) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  simp [seriesQ]

noncomputable def seriesSpecialize (c₀ : ℕ → Series) : Local →+* Series :=
  specialize seriesQ seriesS c₀ (series_endpoint_unit c₀)

@[simp] lemma seriesSpecialize_q (c₀ : ℕ → Series) :
    seriesSpecialize c₀ (algebraMap Base Local q) = seriesQ := by
  simp [seriesSpecialize]
@[simp] lemma seriesSpecialize_s (c₀ : ℕ → Series) :
    seriesSpecialize c₀ (algebraMap Base Local s) = seriesS := by
  simp [seriesSpecialize]
@[simp] lemma seriesSpecialize_c (c₀ : ℕ → Series) (i : ℕ) :
    seriesSpecialize c₀ (algebraMap Base Local (c i)) = c₀ i := by
  simp [seriesSpecialize]

end Universal
end EggeMansour
