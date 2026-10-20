import EggeMansour.ConstructorSeries
import EggeMansour.WrappedSeries
import EggeMansour.PrefixCells

namespace EggeMansour.Combinatorics

noncomputable section

/-- The wrapped avoidance parameter is the generic weighted series of the actual
interiors whose wraps avoid the forbidden pattern. -/
theorem wrappedSeries_eq_weightSeries (p : Pattern) :
    wrappedSeries p = weightSeries (fun _n u => IsAvoidingInvolution u ∧ Avoids (wrap u) p.2) := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_wrappedSeries, coeff_weightSeries, wrappedPolynomial, weightPoly]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : IsAvoidingInvolution u ∧ Avoids (wrap u) p.2 <;> simp [h]

/-- A maximal-prefix cell is the difference of its nested wrapped-avoidance classes. -/
theorem weightSeries_prefixCell (ps : List Pattern) (t : ℕ) :
    weightSeries (fun _n u => IsAvoidingInvolution u ∧ prefixCell (wrap u) ps t) =
      wrappedSeries (sumPatterns (ps.take (t + 1))) -
        wrappedSeries (sumPatterns (ps.take t)) := by
  rw [wrappedSeries_eq_weightSeries, wrappedSeries_eq_weightSeries]
  calc
    _ = weightSeries (fun _n u =>
        (IsAvoidingInvolution u ∧ Avoids (wrap u) (sumPatterns (ps.take (t + 1))).2) ∧
        ¬ (IsAvoidingInvolution u ∧ Avoids (wrap u) (sumPatterns (ps.take t)).2)) := by
      apply weightSeries_congr
      intro n u
      rw [prefixCell_iff_avoidance_difference]
      tauto
    _ = _ := by
      apply weightSeries_sub
      intro n u h
      exact ⟨h.1, avoids_prefix_mono (wrap u) ps (by omega) h.2⟩

/-- A length-one head cancels the new fixed first point, including an empty tail. -/
theorem avoids_fixedConstructor_sumPatterns_of_size_one {n : ℕ} (u : Perm n)
    (p : Pattern) (ps : List Pattern) (hp : p.1 = 1) :
    Avoids (fixedConstructor u) (sumPatterns (p :: ps)).2 ↔
      Avoids u (sumPatterns ps).2 := by
  rcases p with ⟨a, α⟩
  change a = 1 at hp
  subst a
  have hα : α = singleton := Subsingleton.elim _ _
  subst α
  cases ps with
  | nil => simp [sumPatterns, Avoids, contains_singleton_iff]
  | cons q qs =>
    change Avoids (fixedConstructor u) (directSum singleton (sumPatterns (q :: qs)).2) ↔ _
    simp only [fixedConstructor, Avoids, contains_permCast, contains_singleton_directSum_iff]

/-- A non-singleton indecomposable head makes the fixed first point irrelevant. -/
theorem avoids_fixedConstructor_sumPatterns_of_not_size_one {n : ℕ} (u : Perm n)
    (p : Pattern) (ps : List Pattern) (hp : IndecomposablePattern p) (hlen : p.1 ≠ 1) :
    Avoids (fixedConstructor u) (sumPatterns (p :: ps)).2 ↔
      Avoids u (sumPatterns (p :: ps)).2 := by
  have hpos := hp.1
  have ha : 1 < p.1 := by omega
  cases ps with
  | nil =>
    have hnot : ¬ Contains singleton p.2 := by
      intro hc
      have := contains_length_le hc
      omega
    change Avoids (fixedConstructor u) p.2 ↔ Avoids u p.2
    simp only [fixedConstructor, Avoids, contains_permCast,
      contains_directSum_iff_of_indecomposable singleton u p.2 hp, hnot, false_or]
  | cons q qs =>
    change Avoids (fixedConstructor u) (directSum p.2 (sumPatterns (q :: qs)).2) ↔
      Avoids u (directSum p.2 (sumPatterns (q :: qs)).2)
    unfold fixedConstructor
    simp only [Avoids, contains_permCast]
    exact avoids_singleton_directSum_iff_of_prefix u p.2 (sumPatterns (q :: qs)).2 hp ha

/-- The exact fixed-inner series in the actual list recurrence. -/
theorem weightSeries_fixedInner (p : Pattern) (ps : List Pattern)
    (hp : IndecomposablePattern p) :
    weightSeries (fun _n u => IsAvoidingInvolution u ∧
      Avoids (fixedConstructor u) (sumPatterns (p :: ps)).2) =
      if p.1 == 1 then patternSeries (sumPatterns ps)
      else patternSeries (sumPatterns (p :: ps)) := by
  by_cases hlen : p.1 = 1
  · simp only [hlen, beq_self_eq_true, ↓reduceIte]
    unfold patternSeries
    rw [avoiderSeries_eq_weightSeries]
    apply weightSeries_congr
    intro n u
    exact and_congr_right fun _ => avoids_fixedConstructor_sumPatterns_of_size_one u p ps hlen
  · have hb : (p.1 == 1) = false := by simp [hlen]
    rw [hb]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold patternSeries
    rw [avoiderSeries_eq_weightSeries]
    apply weightSeries_congr
    intro n u
    exact and_congr_right fun _ =>
      avoids_fixedConstructor_sumPatterns_of_not_size_one u p ps hp hlen

end
end EggeMansour.Combinatorics
