import EggeMansour.Interfaces

/-!
# Finite permutation definitions

All permutations are actual bijections of finite ordinals. Pattern containment
is an increasing choice of positions that preserves and reflects value order.
The combinatorial predicates and counts are executable. The generating series
use Mathlib's noncomputable polynomial ring and are finite weighted sums at each
length. No combinatorial recurrence is assumed in this module.
-/

namespace EggeMansour.Combinatorics

open scoped BigOperators

abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

abbrev Pattern := Σ n : ℕ, Perm n

def Contains {n k : ℕ} (σ : Perm n) (τ : Perm k) : Prop :=
  ∃ f : Fin k → Fin n, StrictMono f ∧
    ∀ i j, σ (f i) < σ (f j) ↔ τ i < τ j

instance {n k : ℕ} (σ : Perm n) (τ : Perm k) : Decidable (Contains σ τ) :=
  inferInstanceAs (Decidable (∃ f : Fin k → Fin n, StrictMono f ∧
    ∀ i j, σ (f i) < σ (f j) ↔ τ i < τ j))

def Avoids {n k : ℕ} (σ : Perm n) (τ : Perm k) : Prop := ¬ Contains σ τ

instance {n k : ℕ} (σ : Perm n) (τ : Perm k) : Decidable (Avoids σ τ) :=
  inferInstanceAs (Decidable (¬ Contains σ τ))

def IsInvolution {n : ℕ} (σ : Perm n) : Prop := ∀ i, σ (σ i) = i

instance {n : ℕ} (σ : Perm n) : Decidable (IsInvolution σ) :=
  inferInstanceAs (Decidable (∀ i, σ (σ i) = i))

/-- Each transposition in an involution has exactly one lower endpoint. -/
def twoCycles {n : ℕ} (σ : Perm n) : ℕ :=
  (Finset.univ.filter (fun i => i < σ i)).card

def empty : Perm 0 := Equiv.refl _

def singleton : Perm 1 := Equiv.refl _

def directSum {m n : ℕ} (σ : Perm m) (τ : Perm n) : Perm (m + n) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σ τ)).trans finSumFinEquiv

def skewSum {m n : ℕ} (σ : Perm m) (τ : Perm n) : Perm (m + n) :=
  (((finSumFinEquiv.symm.trans (Equiv.sumCongr σ τ)).trans
    (Equiv.sumComm _ _)).trans finSumFinEquiv).trans (finCongr (Nat.add_comm n m))

/-- Nonempty, with no nontrivial initial segment mapped into itself. -/
def IsIndecomposable {n : ℕ} (σ : Perm n) : Prop :=
  0 < n ∧ ∀ k : Fin n, 0 < k.val → ∃ i : Fin n, i.val < k.val ∧ k.val ≤ (σ i).val

instance {n : ℕ} (σ : Perm n) : Decidable (IsIndecomposable σ) :=
  inferInstanceAs (Decidable (0 < n ∧ ∀ k : Fin n, 0 < k.val →
    ∃ i : Fin n, i.val < k.val ∧ k.val ≤ (σ i).val))

/-- One-line notation 3412 in zero-based coordinates is `[2,3,0,1]`. -/
def pattern3412 : Perm 4 := skewSum (Equiv.refl (Fin 2)) (Equiv.refl (Fin 2))

def IsAvoidingInvolution {n : ℕ} (σ : Perm n) : Prop :=
  IsInvolution σ ∧ Avoids σ pattern3412

instance {n : ℕ} (σ : Perm n) : Decidable (IsAvoidingInvolution σ) :=
  inferInstanceAs (Decidable (IsInvolution σ ∧ Avoids σ pattern3412))

def avoiderCount {k : ℕ} (τ : Perm k) (n t : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Perm n =>
    IsAvoidingInvolution σ ∧ Avoids σ τ ∧ twoCycles σ = t)).card

def involutionCount (n t : ℕ) : ℕ :=
  (Finset.univ.filter (fun σ : Perm n =>
    IsAvoidingInvolution σ ∧ twoCycles σ = t)).card

noncomputable def avoiderPolynomial {k : ℕ} (τ : Perm k) (n : ℕ) : Polynomial ℤ :=
  ∑ σ : Perm n, if IsAvoidingInvolution σ ∧ Avoids σ τ then
    Polynomial.X ^ twoCycles σ else 0

noncomputable def avoiderSeries {k : ℕ} (τ : Perm k) : EggeMansour.Series :=
  PowerSeries.mk (avoiderPolynomial τ)

@[simp] theorem coeff_avoiderSeries {k : ℕ} (τ : Perm k) (n : ℕ) :
    PowerSeries.coeff n (avoiderSeries τ) = avoiderPolynomial τ n := by
  simp [avoiderSeries]

theorem contains_refl {n : ℕ} (σ : Perm n) : Contains σ σ :=
  ⟨id, strictMono_id, fun _ _ => Iff.rfl⟩

theorem Contains.trans {a b c : ℕ} {σ : Perm a} {τ : Perm b} {υ : Perm c}
    (hστ : Contains σ τ) (hτυ : Contains τ υ) : Contains σ υ := by
  obtain ⟨f, hf, hσ⟩ := hστ
  obtain ⟨g, hg, hτ⟩ := hτυ
  exact ⟨f ∘ g, hf.comp hg, fun i j => (hσ (g i) (g j)).trans (hτ i j)⟩

theorem contains_length_le {n k : ℕ} {σ : Perm n} {τ : Perm k}
    (h : Contains σ τ) : k ≤ n := by
  obtain ⟨f, hf, _⟩ := h
  simpa using Fintype.card_le_of_injective f hf.injective

@[simp] theorem contains_empty {n : ℕ} (σ : Perm n) : Contains σ empty := by
  refine ⟨Fin.elim0, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

@[simp] theorem not_avoids_empty {n : ℕ} (σ : Perm n) : ¬ Avoids σ empty := by
  simp [Avoids]

@[simp] theorem avoiderPolynomial_empty (n : ℕ) : avoiderPolynomial empty n = 0 := by
  simp [avoiderPolynomial]

@[simp] theorem avoiderSeries_empty : avoiderSeries empty = 0 := by
  ext n
  simp

@[simp] theorem directSum_castAdd {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin m) :
    directSum σ τ (Fin.castAdd n i) = Fin.castAdd n (σ i) := by
  simp [directSum]

@[simp] theorem directSum_natAdd {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin n) :
    directSum σ τ (Fin.natAdd m i) = Fin.natAdd m (τ i) := by
  simp [directSum]

@[simp] theorem skewSum_castAdd_val {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin m) :
    (skewSum σ τ (Fin.castAdd n i)).val = n + (σ i).val := by
  simp [skewSum, Nat.add_comm]

@[simp] theorem skewSum_natAdd_val {m n : ℕ} (σ : Perm m) (τ : Perm n) (i : Fin n) :
    (skewSum σ τ (Fin.natAdd m i)).val = (τ i).val := by
  simp [skewSum]

@[simp] theorem isInvolution_directSum_iff {m n : ℕ} (σ : Perm m) (τ : Perm n) :
    IsInvolution (directSum σ τ) ↔ IsInvolution σ ∧ IsInvolution τ := by
  constructor
  · intro h
    constructor
    · intro i
      have hi := h (Fin.castAdd n i)
      simpa using hi
    · intro i
      have hi := h (Fin.natAdd m i)
      simpa using hi
  · rintro ⟨hσ, hτ⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [hσ j]
    · simp [hτ j]

@[simp] theorem singleton_isIndecomposable : IsIndecomposable singleton := by
  constructor
  · decide
  · intro k hk
    omega

@[simp] theorem empty_not_isIndecomposable : ¬ IsIndecomposable empty := by
  simp [IsIndecomposable]

end EggeMansour.Combinatorics
