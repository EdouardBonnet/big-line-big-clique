import Lax56Proofs.WeightedPairs
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace Lax56Proofs.HarmonicUpper

open scoped BigOperators
open Lax56.Geometry
open Lax56Proofs.WeightedPairs

/-- All reciprocal-stretch weights on an ordered `n`-vertex set. -/
noncomputable def totalWeight (n : ℕ) : ℝ :=
  ∑ e : OrderedPair n, e.weight

/-- The potential `W` from the paper. -/
noncomputable def potential (P : Finset Point) : ℝ :=
  ∑ e : BadPair P, e.1.weight

private def pairSigmaEquiv (n : ℕ) :
    OrderedPair n ≃ Σ i : Fin n, {j : Fin n // i < j} where
  toFun e := ⟨e.left, ⟨e.right, e.left_lt_right⟩⟩
  invFun e := ⟨(e.1, e.2.1), e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem right_sum_le_harmonic (n : ℕ) (i : Fin n) :
    ∑ j : {j : Fin n // i < j},
        (1 / ((j.1.val - i.val : ℕ) : ℝ)) ≤ (harmonic n : ℝ) := by
  classical
  let d : {j : Fin n // i < j} → ℕ := fun j ↦ j.1.val - i.val
  have hd_inj : Function.Injective d := by
    intro j k hjk
    apply Subtype.ext
    apply Fin.ext
    dsimp [d] at hjk
    omega
  have hd_mem (j : {j : Fin n // i < j}) : d j ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc, d]
    constructor
    · omega
    · omega
  calc
    ∑ j : {j : Fin n // i < j}, (1 / ((j.1.val - i.val : ℕ) : ℝ)) =
        ∑ x ∈ Finset.image d (Finset.univ : Finset {j : Fin n // i < j}),
          (1 / (x : ℝ)) := by
      rw [Finset.sum_image hd_inj.injOn]
    _ ≤ ∑ x ∈ Finset.Icc 1 n, (1 / (x : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
        exact hd_mem j
      · intro x _hx _hnot
        positivity
    _ = (harmonic n : ℝ) := by
      simp [harmonic_eq_sum_Icc, one_div]

theorem totalWeight_le_harmonic (n : ℕ) :
    totalWeight n ≤ n * (harmonic n : ℝ) := by
  classical
  unfold totalWeight
  rw [Fintype.sum_equiv (pairSigmaEquiv n)
    (fun e : OrderedPair n ↦ e.weight)
    (fun e : Σ i : Fin n, {j : Fin n // i < j} ↦
      1 / ((e.2.1.val - e.1.val : ℕ) : ℝ)) (by
        intro e
        rfl)]
  rw [Fintype.sum_sigma]
  calc
    ∑ i : Fin n, ∑ j : {j : Fin n // i < j},
        1 / ((j.1.val - i.val : ℕ) : ℝ) ≤
        ∑ _i : Fin n, (harmonic n : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ right_sum_le_harmonic n i
    _ = n * (harmonic n : ℝ) := by simp

theorem totalWeight_le_log (n : ℕ) :
    totalWeight n ≤ (n : ℝ) * (Real.log n + 1) := by
  calc
    totalWeight n ≤ n * (harmonic n : ℝ) := totalWeight_le_harmonic n
    _ ≤ (n : ℝ) * (1 + Real.log n) := by
      gcongr
      exact harmonic_le_one_add_log n
    _ = (n : ℝ) * (Real.log n + 1) := by ring

private theorem five_inv_add_le (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    5 / ((a + b : ℕ) : ℝ) ≤
      1 / (a : ℝ) + 1 / (b : ℝ) + 1 / ((a + b : ℕ) : ℝ) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  push_cast
  field_simp
  nlinarith [sq_nonneg ((a : ℝ) - b)]

private theorem sum_chargeKind (f : ChargeKind → ℝ) :
    ∑ t, f t = f .left + f .right + f .outer := by
  rw [Fintype.sum_eq_add_sum_compl .left]
  rw [show ({ChargeKind.left}ᶜ : Finset ChargeKind) =
      {ChargeKind.right, ChargeKind.outer} by
    ext t
    cases t <;> simp]
  simp [add_assoc]

theorem five_weight_le_charge_sum (P : Finset Point) (e : BadPair P) :
    5 * e.1.weight ≤ ∑ t : ChargeKind, (chargePair P (e, t)).weight := by
  let a := (blockerIndex P e).val - e.1.1.1.val
  let b := e.1.1.2.val - (blockerIndex P e).val
  have ha : 0 < a := by
    dsimp [a]
    simpa [OrderedPair.left] using Nat.sub_pos_of_lt (left_lt_blockerIndex P e)
  have hb : 0 < b := by
    dsimp [b]
    simpa [OrderedPair.right] using Nat.sub_pos_of_lt (blockerIndex_lt_right P e)
  have hab : e.1.stretch = a + b := by
    simp only [OrderedPair.stretch, OrderedPair.left, OrderedPair.right, a, b]
    omega
  have habNat : a + b = e.1.1.2.val - e.1.1.1.val := by
    simpa [OrderedPair.stretch, OrderedPair.left, OrderedPair.right] using hab.symm
  have h := five_inv_add_le a b ha hb
  calc
    5 * e.1.weight = 5 / ((a + b : ℕ) : ℝ) := by
      rw [OrderedPair.weight, hab]
      ring
    _ ≤ 1 / (a : ℝ) + 1 / (b : ℝ) + 1 / ((a + b : ℕ) : ℝ) := h
    _ = ∑ t : ChargeKind, (chargePair P (e, t)).weight := by
      rw [sum_chargeKind]
      simp [OrderedPair.weight, OrderedPair.stretch, chargePair, mkPair, a, b,
        OrderedPair.left, OrderedPair.right]
      exact_mod_cast habNat

/-- Lemma 4.1: the absence of four collinear points forces the sharp harmonic
upper bound on `W`. -/
theorem potential_le_total_div_five
    (P : Finset Point) (hfour : ¬HasFourCollinear P) :
    potential P ≤ totalWeight P.card / 5 := by
  have hlocal :
      5 * potential P ≤
        ∑ x : BadPair P × ChargeKind, (chargePair P x).weight := by
    rw [potential, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun e _ ↦ five_weight_le_charge_sum P e
  have hcharge :
      (∑ x : BadPair P × ChargeKind, (chargePair P x).weight) ≤
        totalWeight P.card := by
    classical
    rw [← Finset.sum_image (chargePair_injective P hfour).injOn]
    unfold totalWeight
    exact Finset.sum_le_univ_sum_of_nonneg OrderedPair.weight_nonneg
  linarith [hlocal.trans hcharge]

theorem potential_le_log
    (P : Finset Point) (hfour : ¬HasFourCollinear P) :
    potential P ≤ (P.card : ℝ) / 5 * Real.log P.card + P.card / 5 := by
  calc
    potential P ≤ totalWeight P.card / 5 := potential_le_total_div_five P hfour
    _ ≤ ((P.card : ℝ) * (Real.log P.card + 1)) / 5 := by
      gcongr
      exact totalWeight_le_log P.card
    _ = (P.card : ℝ) / 5 * Real.log P.card + P.card / 5 := by ring

end Lax56Proofs.HarmonicUpper
