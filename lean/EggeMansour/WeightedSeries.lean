import EggeMansour.PermutationCast
import EggeMansour.CombinatoricsCounts
import EggeMansour.CombinatorialTarget

/-!
# Graded weighted sums of finite permutations

Generic lemmas translating finite disjoint unions, differences and direct-sum
products of families of actual finite permutations into identities between
coefficient-defined series in `ℤ[y][[x]]`. Every series here is a finite weighted
sum at each length; no combinatorial recurrence is assumed anywhere.
-/

namespace EggeMansour.Combinatorics

open scoped BigOperators
open Classical

noncomputable section

/-! ### Casting permutations along length equalities -/

/-- Direct sums are injective in both arguments at fixed lengths. -/
theorem directSum_injective {a b : ℕ} {α α' : Perm a} {β β' : Perm b}
    (e : directSum α β = directSum α' β') : α = α' ∧ β = β' := by
  constructor
  · ext i
    have := congrArg (fun π => (π (Fin.castAdd b i)).val) e
    simpa using this
  · ext i
    have := congrArg (fun π => (π (Fin.natAdd a i)).val) e
    simpa using this

/-! ### Weighted sums and their series -/

/-- Weighted count of permutations of length `n` satisfying `P`; each permutation
contributes `y ^ twoCycles`. -/
def weightPoly (n : ℕ) (P : Perm n → Prop) : Polynomial ℤ :=
  ∑ σ : Perm n, if P σ then Polynomial.X ^ twoCycles σ else 0

/-- Generating series of a graded family of predicates: coefficient `n` is the
weighted count at length `n`. -/
def weightSeries (P : ∀ n, Perm n → Prop) : EggeMansour.Series :=
  PowerSeries.mk fun n => weightPoly n (P n)

@[simp] theorem coeff_weightSeries (P : ∀ n, Perm n → Prop) (n : ℕ) :
    PowerSeries.coeff n (weightSeries P) = weightPoly n (P n) :=
  PowerSeries.coeff_mk _ _

theorem weightPoly_congr {n : ℕ} {P Q : Perm n → Prop} (h : ∀ σ, P σ ↔ Q σ) :
    weightPoly n P = weightPoly n Q := by
  have : P = Q := funext fun σ => propext (h σ)
  rw [this]

theorem weightSeries_congr {P Q : ∀ n, Perm n → Prop} (h : ∀ n σ, P n σ ↔ Q n σ) :
    weightSeries P = weightSeries Q := by
  refine PowerSeries.ext fun n => ?_
  simp [weightPoly_congr (h n)]

/-- The coefficient-defined avoidance series is a graded weighted sum. -/
theorem avoiderSeries_eq_weightSeries {k : ℕ} (τ : Perm k) :
    avoiderSeries τ = weightSeries fun n σ => IsAvoidingInvolution σ ∧ Avoids σ τ := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_avoiderSeries, coeff_weightSeries, avoiderPolynomial, weightPoly]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : IsAvoidingInvolution σ ∧ Avoids σ τ <;> simp [h]

theorem weightPoly_of_not {n : ℕ} {P : Perm n → Prop} (h : ∀ σ, ¬ P σ) :
    weightPoly n P = 0 := by
  unfold weightPoly
  exact Finset.sum_eq_zero fun σ _ => by simp [h σ]

theorem weightSeries_of_not {P : ∀ n, Perm n → Prop} (h : ∀ n σ, ¬ P n σ) :
    weightSeries P = 0 := by
  refine PowerSeries.ext fun n => ?_
  simp [weightPoly_of_not (h n)]

/-- Disjoint union at a fixed length. -/
theorem weightPoly_add {n : ℕ} {P Q R : Perm n → Prop}
    (h : ∀ σ, P σ ↔ Q σ ∨ R σ) (hd : ∀ σ, ¬ (Q σ ∧ R σ)) :
    weightPoly n P = weightPoly n Q + weightPoly n R := by
  unfold weightPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hq : Q σ
  · have hr : ¬ R σ := fun hr => hd σ ⟨hq, hr⟩
    simp [h, hq, hr]
  · by_cases hr : R σ <;> simp [h, hq, hr]

theorem weightSeries_add {P Q R : ∀ n, Perm n → Prop}
    (h : ∀ n σ, P n σ ↔ Q n σ ∨ R n σ) (hd : ∀ n σ, ¬ (Q n σ ∧ R n σ)) :
    weightSeries P = weightSeries Q + weightSeries R := by
  refine PowerSeries.ext fun n => ?_
  simp [weightPoly_add (h n) (hd n)]

/-- Set difference of a subfamily. -/
theorem weightPoly_sub {n : ℕ} {P Q : Perm n → Prop} (h : ∀ σ, Q σ → P σ) :
    weightPoly n (fun σ => P σ ∧ ¬ Q σ) = weightPoly n P - weightPoly n Q := by
  have e : weightPoly n P = weightPoly n (fun σ => P σ ∧ ¬ Q σ) + weightPoly n Q := by
    apply weightPoly_add
    · intro σ
      constructor
      · intro hp
        by_cases hq : Q σ
        · exact Or.inr hq
        · exact Or.inl ⟨hp, hq⟩
      · rintro (⟨hp, _⟩ | hq)
        · exact hp
        · exact h σ hq
    · rintro σ ⟨⟨_, hnq⟩, hq⟩
      exact hnq hq
  rw [e]
  ring

theorem weightSeries_sub {P Q : ∀ n, Perm n → Prop} (h : ∀ n σ, Q n σ → P n σ) :
    weightSeries (fun n σ => P n σ ∧ ¬ Q n σ) = weightSeries P - weightSeries Q := by
  refine PowerSeries.ext fun n => ?_
  simp [weightPoly_sub (h n)]

/-- Finite disjoint union indexed by a finset. -/
theorem weightPoly_sum {ι : Type*} (s : Finset ι) {n : ℕ} {P : Perm n → Prop}
    {Q : ι → Perm n → Prop} (h : ∀ σ, P σ ↔ ∃ i ∈ s, Q i σ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, ∀ σ, Q i σ → Q j σ → i = j) :
    weightPoly n P = ∑ i ∈ s, weightPoly n (Q i) := by
  unfold weightPoly
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hp : P σ
  · obtain ⟨i, hi, hqi⟩ := (h σ).mp hp
    rw [Finset.sum_eq_single i]
    · simp [hp, hqi]
    · intro j hj hji
      have : ¬ Q j σ := fun hqj => hji (hd j hj i hi σ hqj hqi)
      simp [this]
    · intro hi'
      exact absurd hi hi'
  · have : ∀ i ∈ s, ¬ Q i σ := fun i hi hqi => hp ((h σ).mpr ⟨i, hi, hqi⟩)
    rw [ite_eq_right hp]
    symm
    exact Finset.sum_eq_zero fun i hi => by simp [this i hi]

theorem weightSeries_sum {ι : Type*} (s : Finset ι) {P : ∀ n, Perm n → Prop}
    {Q : ι → ∀ n, Perm n → Prop} (h : ∀ n σ, P n σ ↔ ∃ i ∈ s, Q i n σ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, ∀ n σ, Q i n σ → Q j n σ → i = j) :
    weightSeries P = ∑ i ∈ s, weightSeries (Q i) := by
  refine PowerSeries.ext fun n => ?_
  simp only [coeff_weightSeries, map_sum]
  exact weightPoly_sum s (h n) fun i hi j hj σ => hd i hi j hj n σ

/-! ### The empty permutation and the singleton -/

theorem weightPoly_zero_true : weightPoly 0 (fun _ => True) = 1 := by
  unfold weightPoly
  rw [Fintype.sum_subsingleton _ (Equiv.refl (Fin 0))]
  simp [twoCycles]

theorem weightPoly_one_true : weightPoly 1 (fun _ => True) = 1 := by
  unfold weightPoly
  rw [Fintype.sum_subsingleton _ (Equiv.refl (Fin 1))]
  simp [twoCycles]

/-- The family consisting only of the empty permutation has series `1`. -/
theorem weightSeries_length_zero : weightSeries (fun n _ => n = 0) = 1 := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | n
  · simp [weightPoly_zero_true]
  · simp [weightPoly_of_not]

/-- The family consisting only of the permutation `1` has series `x`. -/
theorem weightSeries_length_one : weightSeries (fun n _ => n = 1) = seriesX := by
  refine PowerSeries.ext fun n => ?_
  rcases n with _ | _ | n
  · simp [seriesX, weightPoly_of_not]
  · simp [seriesX, weightPoly_one_true]
  · simp only [coeff_weightSeries, seriesX, PowerSeries.coeff_X]
    rw [weightPoly_of_not (by omega)]
    simp

/-! ### Products via direct sums -/

/-- A family partitioned by a unique direct-sum split has the product series.

`hmem`: direct sums of members are members; `hsplit`: every member is a direct sum
of members, as an equality in `Pattern`; `hlen`: the first length is determined by
the permutation. -/
theorem weightSeries_mul (P Q R : ∀ n, Perm n → Prop)
    (hmem : ∀ a b (α : Perm a) (β : Perm b), Q a α → R b β → P (a + b) (directSum α β))
    (hsplit : ∀ n (σ : Perm n), P n σ → ∃ (a b : ℕ) (α : Perm a) (β : Perm b),
      Q a α ∧ R b β ∧ (⟨a + b, directSum α β⟩ : Pattern) = ⟨n, σ⟩)
    (hlen : ∀ a b a' b' (α : Perm a) (β : Perm b) (α' : Perm a') (β' : Perm b'),
      Q a α → Q a' α' →
      (⟨a + b, directSum α β⟩ : Pattern) = ⟨a' + b', directSum α' β'⟩ → a = a') :
    weightSeries P = weightSeries Q * weightSeries R := by
  refine PowerSeries.ext fun n => ?_
  rw [PowerSeries.coeff_mul]
  simp only [coeff_weightSeries]
  -- expand the right-hand side as one sum over a sigma type
  have rhs : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      weightPoly p.1 (Q p.1) * weightPoly p.2 (R p.2) =
        ∑ αβ ∈ (Finset.univ : Finset (Perm p.1 × Perm p.2)).filter
            (fun αβ => Q p.1 αβ.1 ∧ R p.2 αβ.2),
          Polynomial.X ^ (twoCycles αβ.1 + twoCycles αβ.2) := by
    intro p _
    unfold weightPoly
    rw [Finset.sum_mul_sum, Finset.sum_filter, ← Finset.univ_product_univ,
      Finset.sum_product]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [ite_zero_mul_ite_zero, pow_add]
  rw [Finset.sum_congr rfl rhs, Finset.sum_sigma']
  unfold weightPoly
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij
    (fun x hx => castPerm (Finset.HasAntidiagonal.mem_antidiagonal.mp (Finset.mem_sigma.mp hx).1)
      (directSum x.2.1 x.2.2)) ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, α, β⟩ hx
    have hx' := Finset.mem_sigma.mp hx
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.mp hx'.1
    have hqr := (Finset.mem_filter.mp hx'.2).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact castPerm_prop hab _ P (hmem a b α β hqr.1 hqr.2)
  · rintro ⟨⟨a, b⟩, α, β⟩ hx ⟨⟨a', b'⟩, α', β'⟩ hx' e
    have h1 := Finset.mem_sigma.mp hx
    have h2 := Finset.mem_sigma.mp hx'
    have hab := Finset.HasAntidiagonal.mem_antidiagonal.mp h1.1
    have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp h2.1
    have hq := ((Finset.mem_filter.mp h1.2).2).1
    have hq' := ((Finset.mem_filter.mp h2.2).2).1
    simp only at hab hab' hq hq' e
    have hpat : (⟨a + b, directSum α β⟩ : Pattern) = ⟨a' + b', directSum α' β'⟩ := by
      rw [pattern_mk_eq_iff]
      refine ⟨by omega, ?_⟩
      have e' : castPerm hab (directSum α β) = castPerm hab' (directSum α' β') := e
      have : castPerm (by omega : a + b = a' + b') (directSum α β) =
          castPerm (hab'.symm) (castPerm hab (directSum α β)) := by
        ext i
        simp [castPerm_apply]
      rw [this, e']
      ext i
      simp [castPerm_apply]
    have haa : a = a' := hlen a b a' b' α β α' β' hq hq' hpat
    subst haa
    have hbb : b = b' := by omega
    subst hbb
    have e2 : directSum α β = directSum α' β' := castPerm_injective hab e
    obtain ⟨rfl, rfl⟩ := directSum_injective e2
    rfl
  · intro σ hσ
    have hp : P n σ := (Finset.mem_filter.mp hσ).2
    obtain ⟨a, b, α, β, hq, hr, hpat⟩ := hsplit n σ hp
    obtain ⟨hab, hcast⟩ := (pattern_mk_eq_iff _ _).mp hpat
    refine ⟨⟨⟨a, b⟩, α, β⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter]
      exact ⟨hab, Finset.mem_univ _, hq, hr⟩
    · exact hcast
  · rintro ⟨⟨a, b⟩, α, β⟩ hx
    simp

/-! ### Graded shifts -/

/-- The image of a family under a length-`d`, weight-`e` injective constructor has
series `x^d y^e` times the original series. -/
theorem weightSeries_shift (d e : ℕ) (φ : ∀ {m : ℕ}, Perm m → Perm (m + d))
    (hφ : ∀ m (u v : Perm m), φ u = φ v → u = v)
    (hw : ∀ m (u : Perm m), twoCycles (φ u) = twoCycles u + e)
    (R P : ∀ n, Perm n → Prop)
    (hP : ∀ n σ, P n σ ↔ ∃ (m : ℕ) (u : Perm m), R m u ∧ (⟨m + d, φ u⟩ : Pattern) = ⟨n, σ⟩) :
    weightSeries P =
      PowerSeries.X ^ d * PowerSeries.C (Polynomial.X ^ e) * weightSeries R := by
  refine PowerSeries.ext fun n => ?_
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', coeff_weightSeries]
  split_ifs with hdn
  · rw [PowerSeries.coeff_C_mul, coeff_weightSeries]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + d := ⟨n - d, by omega⟩
    rw [Nat.add_sub_cancel]
    unfold weightPoly
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.mul_sum]
    have himg : (Finset.univ.filter (P (m + d))) =
        (Finset.univ.filter (R m)).image (fun u => φ u) := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      rw [hP]
      constructor
      · rintro ⟨m', u, hu, hpat⟩
        obtain ⟨hmm, hcast⟩ := (pattern_mk_eq_iff _ _).mp hpat
        have hm : m' = m := by omega
        subst hm
        exact ⟨u, hu, by simpa using hcast⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨m, u, hu, rfl⟩
    rw [himg, Finset.sum_image]
    · refine Finset.sum_congr rfl fun u _ => ?_
      rw [hw, pow_add, mul_comm]
    · intro u _ v _ e
      exact hφ m u v e
  · apply weightPoly_of_not
    intro σ hσ
    obtain ⟨m, u, _, hpat⟩ := (hP n σ).mp hσ
    obtain ⟨hmm, _⟩ := (pattern_mk_eq_iff _ _).mp hpat
    omega

end

end EggeMansour.Combinatorics
