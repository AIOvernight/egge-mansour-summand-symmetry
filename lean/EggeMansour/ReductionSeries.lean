import EggeMansour.Reduction
import EggeMansour.WrappedSeries

/-!
# The actual reduction parameter

The independently defined wrapped-avoidance series is exactly the avoidance
series of the Egge–Mansour reduced pattern, including empty and singleton cases.
-/

namespace EggeMansour.Combinatorics

theorem wrappedSeries_eq_reducedSeries (p : Pattern) :
    wrappedSeries p = patternSeries (reduce p) := by
  rcases p with ⟨k, τ⟩
  apply PowerSeries.ext
  intro n
  simp only [coeff_wrappedSeries, patternSeries, coeff_avoiderSeries,
    wrappedPolynomial, avoiderPolynomial]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Avoids, contains_wrap_iff]
  rfl

end EggeMansour.Combinatorics
