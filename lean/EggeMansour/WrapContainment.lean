import EggeMansour.Wrap
import EggeMansour.DirectSumContainment

namespace EggeMansour.Combinatorics

/-- A pattern whose first entry is not maximal and last entry is not minimal
cannot use either outer endpoint in an occurrence inside a wrap. -/
theorem contains_wrap_iff_of_endpoints {n p : ℕ} (u : Perm n) (υ : Perm p)
    (first last : Fin p) (hfirstpos : first.val = 0) (hlastpos : last.val = p - 1)
    (hfirst : ∃ j, υ first < υ j) (hlast : ∃ j, υ j < υ last) :
    Contains (wrap u) υ ↔ Contains u υ := by
  constructor
  · rintro ⟨f, hf, hp⟩
    have h0 : ∀ i, 0 < (f i).val := by
      intro i
      by_contra h
      have hfi : (f i).val = 0 := by omega
      have hmin := hf.monotone (show first ≤ i by change first.val ≤ i.val; omega)
      have hffirst : f first = 0 := by apply Fin.ext; change (f first).val = 0; omega
      obtain ⟨j, hj⟩ := hfirst
      have hx := (hp first j).mpr hj
      rw [hffirst, wrap_zero] at hx
      have hb := (wrap u (f j)).isLt
      change n + 1 < (wrap u (f j)).val at hx
      omega
    have hlast' : ∀ i, (f i).val < n + 1 := by
      intro i
      by_contra h
      have hfi := (f i).isLt
      have hlastbound := (f last).isLt
      have hmax := hf.monotone (show i ≤ last by
        have hi := i.isLt
        change i.val ≤ last.val
        omega)
      have hflast : f last = Fin.last (n + 1) := by
        apply Fin.ext
        change (f last).val = n + 1
        omega
      obtain ⟨j, hj⟩ := hlast
      have hx := (hp j last).mpr hj
      rw [hflast, wrap_last] at hx
      exact (not_lt_of_ge (Fin.zero_le _)) hx
    let g : Fin p → Fin n := fun i => ⟨(f i).val - 1, by
      have := h0 i
      have := hlast' i
      omega⟩
    refine ⟨g, ?_, ?_⟩
    · intro i j hij
      have h := hf hij
      have := h0 i
      have := h0 j
      change (f i).val - 1 < (f j).val - 1
      change (f i).val < (f j).val at h
      omega
    · intro i j
      have h := hp i j
      have hi := wrap_apply_interior_val u (f i) (h0 i) (hlast' i)
      have hj := wrap_apply_interior_val u (f j) (h0 j) (hlast' j)
      change ((wrap u (f i)).val < (wrap u (f j)).val ↔ υ i < υ j) at h
      rw [hi, hj, Nat.add_lt_add_iff_right] at h
      exact h
  · intro h
    exact (contains_wrap u).trans h

/-- Wrapping preserves containment of a direct sum with two nonempty summands. -/
theorem contains_wrap_directSum_iff {n a b : ℕ} (u : Perm n)
    (α : Perm a) (β : Perm b) (ha : 0 < a) (hb : 0 < b) :
    Contains (wrap u) (directSum α β) ↔ Contains u (directSum α β) := by
  let first : Fin (a + b) := Fin.castAdd b ⟨0, ha⟩
  let last : Fin (a + b) := Fin.natAdd a ⟨b - 1, by omega⟩
  apply contains_wrap_iff_of_endpoints u (directSum α β) first last
  · rfl
  · dsimp [last]
    omega
  · refine ⟨last, ?_⟩
    apply directSum_values_separated α β first last
    · exact ha
    · change a ≤ a + (b - 1)
      omega
  · refine ⟨first, ?_⟩
    apply directSum_values_separated α β first last
    · exact ha
    · change a ≤ a + (b - 1)
      omega

@[simp] theorem avoids_wrap_directSum_iff {n a b : ℕ} (u : Perm n)
    (α : Perm a) (β : Perm b) (ha : 0 < a) (hb : 0 < b) :
    Avoids (wrap u) (directSum α β) ↔ Avoids u (directSum α β) := by
  simp only [Avoids, contains_wrap_directSum_iff u α β ha hb]

end EggeMansour.Combinatorics
