import EggeMansour.WrappedSeries

/-!
# List-to-interval weighted recurrence adapter

This file proves transparent indexing infrastructure. Its final theorem takes
`ListWeightedIdentity` as a premise, proved by `listWeightedIdentity` in
`CombinatorialMain.lean`; that module applies the adapter to obtain the
unconditional combinatorial weighted recurrence.
-/

namespace EggeMansour.Combinatorics

open scoped BigOperators

/-- The list counting identity consumed by the interval adapter and proved as
`listWeightedIdentity` in `CombinatorialMain.lean`. -/
def ListWeightedIdentity : Prop :=
  ∀ (p : Pattern) (ps : List Pattern),
    (∀ q ∈ p :: ps, IndecomposablePattern q) →
    patternSeries (sumPatterns (p :: ps)) =
      1 + seriesX * (if p.1 = 1 then patternSeries (sumPatterns ps)
        else patternSeries (sumPatterns (p :: ps))) +
      seriesQ * ∑ t ∈ Finset.range (p :: ps).length,
        (wrappedSeries (sumPatterns ((p :: ps).take (t+1))) -
         wrappedSeries (sumPatterns ((p :: ps).take t))) *
        patternSeries (sumPatterns ((p :: ps).drop t))

/-- The finite list of blocks in an inclusive interval. -/
def intervalBlocks {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ) : List Pattern :=
  ((List.ofFn blocks).drop i).take (j+1-i)

@[simp] theorem intervalBlocks_length {n : ℕ} (blocks : Fin n → Pattern)
    (i j : ℕ) (hj : j < n) : (intervalBlocks blocks i j).length = j+1-i := by
  simp only [intervalBlocks, List.length_take, List.length_drop, List.length_ofFn]
  omega

theorem intervalBlocks_indec {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) (i j : ℕ) :
    ∀ p ∈ intervalBlocks blocks i j, IndecomposablePattern p := by
  intro p hp
  have hmem := List.mem_of_mem_drop (List.mem_of_mem_take hp)
  obtain ⟨k,hk⟩ := List.mem_ofFn.mp hmem
  subst p
  exact hb k

@[simp] theorem patternSeries_intervalBlocks {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ) :
    patternSeries (sumPatterns (intervalBlocks blocks i j)) = intervalSeries blocks i j := rfl

theorem intervalBlocks_take {n : ℕ} (blocks : Fin n → Pattern) (i j t : ℕ)
    (ht0 : 0 < t) (ht : t ≤ j+1-i) :
    (intervalBlocks blocks i j).take t = intervalBlocks blocks i (i+t-1) := by
  unfold intervalBlocks
  rw [List.take_take, Nat.min_eq_left ht]
  congr 1
  omega

theorem intervalBlocks_drop {n : ℕ} (blocks : Fin n → Pattern) (i j t : ℕ) :
    (intervalBlocks blocks i j).drop t = intervalBlocks blocks (i+t) j := by
  simp only [intervalBlocks, List.drop_take, List.drop_drop]
  congr 1
  omega

theorem intervalBlocks_take_one {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ)
    (hij : i ≤ j) (hj : j < n) :
    (intervalBlocks blocks i j).take 1 = [blockAt blocks i] := by
  unfold intervalBlocks
  rw [List.take_take, Nat.min_eq_left (by omega : 1 ≤ j+1-i)]
  rw [List.take_one_drop_eq_of_lt_length (by simpa using (show i < n by omega))]
  simp [blockAt, show i < n by omega]

theorem intervalBlocks_head_tail {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ)
    (hij : i ≤ j) (hj : j < n) :
    intervalBlocks blocks i j = blockAt blocks i :: intervalBlocks blocks (i+1) j := by
  have h := List.take_append_drop 1 (intervalBlocks blocks i j)
  rw [intervalBlocks_take_one blocks i j hij hj, intervalBlocks_drop] at h
  simpa using h.symm

theorem wrappedSeries_intervalBlocks_take_zero {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ) :
    wrappedSeries (sumPatterns ((intervalBlocks blocks i j).take 0)) = 0 := by
  simp [sumPatterns]

theorem wrappedSeries_intervalBlocks_take_one {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ)
    (hij : i ≤ j) (hj : j < n) :
    wrappedSeries (sumPatterns ((intervalBlocks blocks i j).take 1)) =
      wrappedSeries (blockAt blocks i) := by
  rw [intervalBlocks_take_one blocks i j hij hj]
  rfl

theorem wrappedSeries_intervalBlocks_take {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) (i j t : ℕ)
    (hj : j < n) (ht2 : 2 ≤ t) (ht : t ≤ j+1-i) :
    wrappedSeries (sumPatterns ((intervalBlocks blocks i j).take t)) =
      intervalSeries blocks i (i+t-1) := by
  rw [wrappedSeries_sumPatterns]
  · rw [intervalBlocks_take blocks i j t (by omega) ht]
    rfl
  · simp only [List.length_take, intervalBlocks_length blocks i j hj]
    omega
  · intro p hp
    exact (intervalBlocks_indec blocks hb i j p (List.mem_of_mem_take hp)).1

/-- Separate the first two summands without choosing predecessor conventions. -/
theorem sum_range_first_two {R : Type*} [AddCommMonoid R] (f : ℕ → R) (N : ℕ)
    (hN : 2 ≤ N) :
    ∑ t ∈ Finset.range N, f t = f 0 + f 1 + ∑ t ∈ Finset.Icc 2 (N-1), f t := by
  have hs : Finset.range N = insert 0 (insert 1 (Finset.Icc 2 (N-1))) := by
    ext t
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hs, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
  ac_rfl

noncomputable def intervalPrefixTerm {n : ℕ} (blocks : Fin n → Pattern) (i j t : ℕ) : Series :=
  (wrappedSeries (sumPatterns ((intervalBlocks blocks i j).take (t+1))) -
    wrappedSeries (sumPatterns ((intervalBlocks blocks i j).take t))) *
    patternSeries (sumPatterns ((intervalBlocks blocks i j).drop t))

theorem intervalPrefixTerm_zero {n : ℕ} (blocks : Fin n → Pattern) (i j : ℕ)
    (hij : i ≤ j) (hj : j < n) :
    intervalPrefixTerm blocks i j 0 = wrappedSeries (blockAt blocks i) * intervalSeries blocks i j := by
  simp only [intervalPrefixTerm, zero_add, wrappedSeries_intervalBlocks_take_one blocks i j hij hj,
    wrappedSeries_intervalBlocks_take_zero, sub_zero, List.drop_zero, patternSeries_intervalBlocks]

theorem intervalPrefixTerm_one {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) (i j : ℕ)
    (hij : i < j) (hj : j < n) :
    intervalPrefixTerm blocks i j 1 =
      (intervalSeries blocks i (i+1) - wrappedSeries (blockAt blocks i)) *
        intervalSeries blocks (i+1) j := by
  unfold intervalPrefixTerm
  rw [wrappedSeries_intervalBlocks_take blocks hb i j 2 hj (by omega) (by omega),
    wrappedSeries_intervalBlocks_take_one blocks i j hij.le hj,
    intervalBlocks_drop, patternSeries_intervalBlocks]
  have hidx : i+2-1 = i+1 := by omega
  rw [hidx]

theorem intervalPrefixTerm_ge_two {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) (i j t : ℕ)
    (hj : j < n) (ht2 : 2 ≤ t) (ht : t < j+1-i) :
    intervalPrefixTerm blocks i j t =
      (intervalSeries blocks i (i+t) - intervalSeries blocks i (i+t-1)) *
        intervalSeries blocks (i+t) j := by
  unfold intervalPrefixTerm
  rw [wrappedSeries_intervalBlocks_take blocks hb i j (t+1) hj (by omega) (by omega),
    wrappedSeries_intervalBlocks_take blocks hb i j t hj ht2 (by omega),
    intervalBlocks_drop, patternSeries_intervalBlocks]
  have hidx : i+(t+1)-1 = i+t := by omega
  rw [hidx]

theorem interval_prefix_sum {n : ℕ} (blocks : Fin n → Pattern)
    (hb : ∀ i, IndecomposablePattern (blocks i)) (i j : ℕ)
    (hij : i ≤ j) (hj : j < n) :
    (∑ t ∈ Finset.range (j+1-i), intervalPrefixTerm blocks i j t) =
      wrappedSeries (blockAt blocks i) * intervalSeries blocks i j +
      (intervalSeries blocks i (i+1) - wrappedSeries (blockAt blocks i)) *
        intervalSeries blocks (i+1) j +
      ∑ r ∈ Finset.Icc (i+2) j,
        (intervalSeries blocks i r - intervalSeries blocks i (r-1)) *
          intervalSeries blocks r j := by
  by_cases heq : i = j
  · subst j
    have hempty := intervalSeries_lower blocks (i+1) i (by omega)
    simp only [Nat.add_sub_cancel_left, Finset.sum_range_one,
      intervalPrefixTerm_zero blocks i i le_rfl hj, hempty, mul_zero, add_zero,
      Finset.Icc_eq_empty_of_lt (by omega : i < i+2), Finset.sum_empty]
  · have hlt : i < j := by omega
    rw [sum_range_first_two _ _ (by omega), intervalPrefixTerm_zero blocks i j hij hj,
      intervalPrefixTerm_one blocks hb i j hlt hj]
    congr 1
    apply Finset.sum_bij (fun t _ => i+t)
    · intro t ht
      simp only [Finset.mem_Icc] at *
      omega
    · intro a ha b hb' hab
      omega
    · intro r hr
      refine ⟨r-i, ?_, ?_⟩
      · simp only [Finset.mem_Icc] at *
        omega
      · simp only [Finset.mem_Icc] at hr
        omega
    · intro t ht
      simp only [Finset.mem_Icc] at ht
      exact intervalPrefixTerm_ge_two blocks hb i j t hj ht.1 (by omega)

/-- Pure indexing adapter: the actual finite-list counting identity implies
the precise pre-existing interval recurrence. The counting premise is explicit. -/
theorem weightedRecurrence_of_list_identity (H : ListWeightedIdentity)
    {n : ℕ} (blocks : Fin n → Pattern) (hb : ∀ i, IndecomposablePattern (blocks i)) :
    WeightedRecurrence n seriesX seriesQ
      (fun i => patternSeries (blockAt blocks i))
      (fun i => wrappedSeries (blockAt blocks i))
      (fun i => (blockAt blocks i).1 == 1) (intervalSeries blocks) := by
  constructor
  · intro i j hji _
    exact intervalSeries_lower blocks i j hji
  · intro i _
    exact intervalSeries_lower blocks (i+1) i (by omega)
  · intro i hi
    have hd := intervalSeries_diagonal blocks ⟨i,hi⟩
    simpa only [blockAt, dite_eq_left hi] using hd
  · intro i _ hs
    exact wrappedSeries_of_size_one _ (by simpa only [beq_iff_eq] using hs)
  · intro i j hij hj
    have hlist := intervalBlocks_head_tail blocks i j hij hj
    have hblocks : ∀ p ∈ blockAt blocks i :: intervalBlocks blocks (i+1) j,
        IndecomposablePattern p := by
      rw [← hlist]
      exact intervalBlocks_indec blocks hb i j
    have hid := H (blockAt blocks i) (intervalBlocks blocks (i+1) j) hblocks
    rw [← hlist] at hid
    simp only [patternSeries_intervalBlocks, intervalBlocks_length blocks i j hj] at hid
    change intervalSeries blocks i j =
      1 + seriesX * (if (blockAt blocks i).1 = 1 then intervalSeries blocks (i+1) j
        else intervalSeries blocks i j) +
      seriesQ * ∑ t ∈ Finset.range (j+1-i), intervalPrefixTerm blocks i j t at hid
    rw [interval_prefix_sum blocks hb i j hij hj] at hid
    simpa only [beq_iff_eq, mul_add, mul_assoc, add_assoc] using hid

end EggeMansour.Combinatorics
