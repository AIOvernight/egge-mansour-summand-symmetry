import EggeMansour.Interfaces

namespace EggeMansour

variable {R : Type*} [CommRing R]

/-- Eliminate the reduced-block series in the ordinary first-block case. -/
theorem ordinary_to_uniform (x q c h f g σ : R)
    (hc : (1 - x - q * h) * c = 1)
    (hf : f = 1 + x * f + q * h * f - q * h * g + q * σ) :
    f = c + (1 - (1 - x) * c) * g + q * c * σ := by
  linear_combination c * hf - (f - g) * hc

/-- The distinguished block `1` gives the same uniform formula without division. -/
theorem singleton_to_uniform (x q c h f g σ : R)
    (hc : c = 1) (hh : h = 0)
    (hf : f = 1 + x * g + q * h * f - q * h * g + q * σ) :
    f = c + (1 - (1 - x) * c) * g + q * c * σ := by
  subst c
  subst h
  linear_combination hf

/-- Extract the final summand, the only occurrence of the longest interval. -/
theorem extract_endpoint (q s ci cj f g σ : R)
    (hf : f = ci + (1 - s * ci) * g + q * ci * (σ + f * cj)) :
    (1 - q * ci * cj) * f = ci + (1 - s * ci) * g + q * ci * σ := by
  linear_combination hf

/-- Discrete summation by parts for the prefix differences in the published recurrence. -/
theorem weighted_sum_eq (F : ℕ → ℕ → R) (i j : ℕ) (hij : i < j) :
    F i (i + 1) * F (i + 1) j +
      ∑ r ∈ Finset.Icc (i + 2) j, (F i r - F i (r - 1)) * F r j =
    (∑ r ∈ Finset.Icc (i + 1) j, F i r * F r j) -
      ∑ r ∈ Finset.Ioo i j, F i r * F (r + 1) j := by
  have split : (∑ r ∈ Finset.Icc (i + 1) j, F i r * F r j) =
      F i (i + 1) * F (i + 1) j +
        ∑ r ∈ Finset.Icc (i + 2) j, F i r * F r j := by
    have hs : Finset.Icc (i + 1) j = insert (i + 1) (Finset.Icc (i + 2) j) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hs, Finset.sum_insert (by simp)]
  have shift : (∑ r ∈ Finset.Icc (i + 2) j, F i (r - 1) * F r j) =
      ∑ r ∈ Finset.Ioo i j, F i r * F (r + 1) j := by
    apply Finset.sum_bij (fun r _ => r - 1)
    · intro r hr
      simp only [Finset.mem_Icc, Finset.mem_Ioo] at *
      omega
    · intro a ha b hb hab
      simp only [Finset.mem_Icc] at ha hb
      omega
    · intro r hr
      refine ⟨r + 1, ?_, by omega⟩
      simp only [Finset.mem_Ioo] at hr
      simp only [Finset.mem_Icc]
      omega
    · intro r hr
      simp only [Finset.mem_Icc] at hr
      congr 2
      omega
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, shift, split]
  ring

/-- Isolate the diagonal contribution at the right endpoint. -/
theorem weighted_sum_endpoint (F : ℕ → ℕ → R) (i j : ℕ) (hij : i < j) :
    F i (i + 1) * F (i + 1) j +
      ∑ r ∈ Finset.Icc (i + 2) j, (F i r - F i (r - 1)) * F r j =
    (∑ r ∈ Finset.Ioo i j, F i r * (F r j - F (r + 1) j)) + F i j * F j j := by
  rw [weighted_sum_eq F i j hij]
  have hs : Finset.Icc (i + 1) j = insert j (Finset.Ioo i j) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hs, Finset.sum_insert (by simp)]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- The published weighted recurrence implies the uniform pole-free recurrence.
Both possible first blocks are handled explicitly; no inverse of `q` occurs. -/
theorem WeightedRecurrence.toUniform {n : ℕ} {x q : R}
    {c h : ℕ → R} {singleton : ℕ → Bool} {F : ℕ → ℕ → R}
    (H : WeightedRecurrence n x q c h singleton F) :
    UniformRecurrence n q (1 - x) c F := by
  refine ⟨H.lower, H.diagonal, ?_⟩
  intro i j hij hj
  have hi : i < n := lt_trans hij hj
  have raw := H.step i j hij.le hj
  have single := H.step i i le_rfl hi
  rw [H.diagonal i hi, H.empty i hi] at single
  simp only [mul_zero, add_zero, Finset.Icc_eq_empty_of_lt (show i < i + 2 by omega),
    Finset.sum_empty] at single
  have sumid := weighted_sum_endpoint F i j hij
  rw [H.diagonal j hj] at sumid
  have collapsed : F i j = 1 + x * (if singleton i then F (i + 1) j else F i j) +
      q * h i * F i j - q * h i * F (i + 1) j +
        q * ((∑ r ∈ Finset.Ioo i j, F i r * (F r j - F (r + 1) j)) + F i j * c j) := by
    linear_combination raw + q * sumid
  apply extract_endpoint q (1-x) (c i) (c j) (F i j) (F (i+1) j)
  cases hs : singleton i
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at single collapsed
    apply ordinary_to_uniform x q (c i) (h i) (F i j) (F (i+1) j) _ _ collapsed
    linear_combination single
  · have hh := H.singleton_reduction i hi hs
    simp only [hs, ↓reduceIte, hh, zero_mul, mul_zero, add_zero] at single
    exact singleton_to_uniform x q (c i) (h i) (F i j) (F (i+1) j) _ single hh
      (by simpa only [hs, ↓reduceIte] using collapsed)

/-- Unit leading coefficients force uniqueness by induction on interval length. -/
theorem UniformRecurrence.eq_of_units {n : ℕ} {q s : R} {c : ℕ → R}
    {F G : ℕ → ℕ → R} (hF : UniformRecurrence n q s c F)
    (hG : UniformRecurrence n q s c G)
    (hu : ∀ i j, i < j → j < n → IsUnit (1 - q * c i * c j))
    (i j : ℕ) (hij : i ≤ j) (hj : j < n) : F i j = G i j := by
  generalize hd : j - i = d
  induction d using Nat.strong_induction_on generalizing i j with
  | h d ih =>
    by_cases heq : i = j
    · subst j
      rw [hF.diagonal i hj, hG.diagonal i hj]
    have hlt : i < j := by omega
    apply (hu i j hlt hj).mul_left_cancel
    rw [hF.step i j hlt hj, hG.step i j hlt hj]
    have tail : F (i + 1) j = G (i + 1) j :=
      ih (j - (i+1)) (by omega) (i+1) j (by omega) hj rfl
    rw [tail]
    congr 2
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_Ioo.mp hr
    rw [ih (r-i) (by omega) i r (by omega) (by omega) rfl,
      ih (j-r) (by omega) r j (by omega) hj rfl,
      ih (j-(r+1)) (by omega) (r+1) j (by omega) hj rfl]

end EggeMansour
