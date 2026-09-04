import Lax56Proofs.PotentialLower
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

namespace Lax56Proofs.AnalyticBounds

open scoped BigOperators
open Lax56.Geometry
open Lax56Proofs.IntervalDensity
open Lax56Proofs.SlidingWindows
open Lax56Proofs.PotentialLower
open Lax56Proofs.HarmonicUpper

/-- The logarithms of consecutive ratios telescope. -/
theorem sum_log_ratio (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    ∑ m ∈ Finset.Icc M N, Real.log (((m + 1 : ℕ) : ℝ) / m) =
      Real.log (((N + 1 : ℕ) : ℝ) / M) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      rw [← Real.log_mul
        (by positivity : (((N : ℝ) + 1) / M) ≠ 0)
        (by positivity : (((N : ℝ) + 1 + 1) / ((N : ℝ) + 1)) ≠ 0)]
      congr 1
      field_simp

/-- Integral-comparison lower bound for a finite harmonic interval. -/
theorem sum_one_div_lower_log (M N : ℕ) (hM : 0 < M) (hMN : M ≤ N) :
    Real.log (((N + 1 : ℕ) : ℝ) / M) ≤
      ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) := by
  rw [← sum_log_ratio M N hM hMN]
  apply Finset.sum_le_sum
  intro m hm
  simp only [Finset.mem_Icc] at hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le hM hm.1)
  have hlog := Real.log_le_sub_one_of_pos
    (show (0 : ℝ) < (((m + 1 : ℕ) : ℝ) / m) by positivity)
  convert hlog using 1 <;> push_cast <;> field_simp <;> ring

theorem one_div_le_ratio (m : ℕ) (hm : 2 ≤ m) :
    1 / (m : ℝ) ≤ (m : ℝ) / ((m : ℝ) ^ 2 - 1) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hden : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
  apply (div_le_div_iff₀ hm0 hden).2
  nlinarith

theorem sq_ratio_le_two (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) ≤ 2 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Exact finite telescoping formula for `∑ 1/(m²-1)`. -/
theorem sum_inv_sq_sub_one_eq (N : ℕ) (hN : 2 ≤ N) :
    ∑ m ∈ Finset.Icc 2 N, 1 / ((m : ℝ) ^ 2 - 1) =
      3 / 4 - 1 / (2 * (N : ℝ)) - 1 / (2 * ((N : ℝ) + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      push_cast
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
      have hN2 : (N : ℝ) + 2 ≠ 0 := by positivity
      have hsq : ((N : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
        nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast (by omega : 1 ≤ N)]
      field_simp
      ring

theorem sum_inv_sq_sub_one_le (M N : ℕ) (hM : 2 ≤ M) :
    ∑ m ∈ Finset.Icc M N, 1 / ((m : ℝ) ^ 2 - 1) ≤ 3 / 4 := by
  by_cases hMN : M ≤ N
  · have hN : 2 ≤ N := hM.trans hMN
    calc
      ∑ m ∈ Finset.Icc M N, 1 / ((m : ℝ) ^ 2 - 1) ≤
          ∑ m ∈ Finset.Icc 2 N, 1 / ((m : ℝ) ^ 2 - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Icc] at hm ⊢
          omega
        · intro m hm _hnot
          simp only [Finset.mem_Icc] at hm
          have hmR : (1 : ℝ) < m := by exact_mod_cast hm.1
          have hden : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
          exact div_nonneg (by norm_num) hden.le
      _ ≤ 3 / 4 := by
        rw [sum_inv_sq_sub_one_eq N hN]
        have hNR : (0 : ℝ) < N := by positivity
        have hN1R : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have ha : (0 : ℝ) ≤ 1 / (2 * (N : ℝ)) := by positivity
        have hb : (0 : ℝ) ≤ 1 / (2 * ((N : ℝ) + 1)) := by positivity
        linarith
  · rw [Finset.Icc_eq_empty (by omega)]
    norm_num

theorem sum_sq_ratio_le (M N : ℕ) (hM : 2 ≤ M) :
    ∑ m ∈ Finset.Icc M N, (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) ≤
      2 * (N : ℝ) := by
  calc
    ∑ m ∈ Finset.Icc M N, (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1) ≤
        ∑ _m ∈ Finset.Icc M N, (2 : ℝ) := by
      exact Finset.sum_le_sum fun m hm ↦
        sq_ratio_le_two m (hM.trans (Finset.mem_Icc.mp hm).1)
    _ ≤ ∑ _m ∈ Finset.Icc 1 N, (2 : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        simp only [Finset.mem_Icc] at hm ⊢
        omega
      · intro _m _hm _hnot
        norm_num
    _ = 2 * (N : ℝ) := by simp; ring

theorem sum_ratio_lower_log (M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    Real.log (((N + 1 : ℕ) : ℝ) / M) ≤
      ∑ m ∈ Finset.Icc M N, (m : ℝ) / ((m : ℝ) ^ 2 - 1) := by
  calc
    Real.log (((N + 1 : ℕ) : ℝ) / M) ≤
        ∑ m ∈ Finset.Icc M N, 1 / (m : ℝ) :=
      sum_one_div_lower_log M N (by omega) hMN
    _ ≤ ∑ m ∈ Finset.Icc M N,
        (m : ℝ) / ((m : ℝ) ^ 2 - 1) := by
      exact Finset.sum_le_sum fun m hm ↦
        one_div_le_ratio m (hM.trans (Finset.mem_Icc.mp hm).1)

/-- The explicit analytic summand arising from the sliding-window estimate. -/
noncomputable def analyticTerm (n m : ℕ) : ℝ :=
  2 / ((m : ℝ) ^ 2 - 1) *
    (density * (m : ℝ) * n - density * (m : ℝ) ^ 2 - n / 2)

theorem analyticTerm_eq (n m : ℕ) :
    analyticTerm n m =
      2 * density * (n : ℝ) * ((m : ℝ) / ((m : ℝ) ^ 2 - 1)) -
      2 * density * ((m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) -
      (n : ℝ) * (1 / ((m : ℝ) ^ 2 - 1)) := by
  unfold analyticTerm
  ring

theorem sum_analyticTerm_eq (n M N : ℕ) :
    ∑ m ∈ Finset.Icc M N, analyticTerm n m =
      2 * density * (n : ℝ) *
          (∑ m ∈ Finset.Icc M N, (m : ℝ) / ((m : ℝ) ^ 2 - 1)) -
      2 * density *
          (∑ m ∈ Finset.Icc M N, (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) -
      (n : ℝ) *
          (∑ m ∈ Finset.Icc M N, 1 / ((m : ℝ) ^ 2 - 1)) := by
  simp_rw [analyticTerm_eq]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]

theorem analyticTerm_le_scaleContribution
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6) {m : ℕ}
    (hm₀ : m₀ ≤ m) (hm : m ≤ P.card) :
    analyticTerm P.card m ≤ scaleContribution P m := by
  have hmass := deficit_lower P hfour hvisible hm₀ hm
  have hmR : (1 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by unfold m₀; norm_num : 1 < m₀) hm₀)
  have hcoef : (0 : ℝ) ≤ 2 / ((m : ℝ) ^ 2 - 1) := by
    have : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  unfold analyticTerm scaleContribution
  convert mul_le_mul_of_nonneg_left hmass hcoef using 1 <;> ring

theorem analytic_sum_le_potential
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6) {M N : ℕ}
    (hM : m₀ ≤ M) (hN : N ≤ P.card) :
    ∑ m ∈ Finset.Icc M N, analyticTerm P.card m ≤ potential P := by
  calc
    ∑ m ∈ Finset.Icc M N, analyticTerm P.card m ≤
        ∑ m ∈ Finset.Icc M N, scaleContribution P m := by
      exact Finset.sum_le_sum fun m hm ↦
        analyticTerm_le_scaleContribution P hfour hvisible
          (hM.trans (Finset.mem_Icc.mp hm).1)
          ((Finset.mem_Icc.mp hm).2.trans hN)
    _ ≤ potential P := scale_sum_le_potential P M N

theorem analytic_sum_lower (n M N : ℕ) (hM : 2 ≤ M) (hMN : M ≤ N) :
    2 * density * (n : ℝ) * Real.log (((N + 1 : ℕ) : ℝ) / M) -
        4 * density * (N : ℝ) - 3 * (n : ℝ) / 4 ≤
      ∑ m ∈ Finset.Icc M N, analyticTerm n m := by
  rw [sum_analyticTerm_eq]
  have hS₁ := sum_ratio_lower_log M N hM hMN
  have hS₂ := sum_sq_ratio_le M N hM
  have hS₃ := sum_inv_sq_sub_one_le M N hM
  have hc : (0 : ℝ) ≤ density := by norm_num [density, eps₁]
  have hn : (0 : ℝ) ≤ n := by positivity
  have h₁ :
      2 * density * (n : ℝ) * Real.log (((N + 1 : ℕ) : ℝ) / M) ≤
        2 * density * (n : ℝ) *
          (∑ m ∈ Finset.Icc M N, (m : ℝ) / ((m : ℝ) ^ 2 - 1)) :=
    mul_le_mul_of_nonneg_left hS₁ (mul_nonneg (mul_nonneg (by norm_num) hc) hn)
  have h₂ :
      2 * density *
          (∑ m ∈ Finset.Icc M N, (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) ≤
        4 * density * (N : ℝ) := by
    have hraw :
        2 * density *
            (∑ m ∈ Finset.Icc M N, (m : ℝ) ^ 2 / ((m : ℝ) ^ 2 - 1)) ≤
          2 * density * (2 * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hS₂ (mul_nonneg (by norm_num) hc)
    nlinarith
  have h₃ :
      (n : ℝ) * (∑ m ∈ Finset.Icc M N, 1 / ((m : ℝ) ^ 2 - 1)) ≤
        3 * (n : ℝ) / 4 := by
    convert mul_le_mul_of_nonneg_left hS₃ hn using 1 <;> ring
  nlinarith

/-- Section 5 lower bound for `W`, with all sliding windows in place of a
random shifted partition.  This slightly improves the paper's error term. -/
theorem potential_lower_log
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6)
    (hbig : 4 * m₀ ≤ P.card) :
    2 * density * (P.card : ℝ) *
          Real.log ((P.card : ℝ) / (4 * m₀)) -
        density * P.card - 3 * P.card / 4 ≤ potential P := by
  let N := P.card / 4
  have hMN : m₀ ≤ N := by
    dsimp only [N]
    omega
  have hNcard : N ≤ P.card := by
    dsimp only [N]
    omega
  have hMtwo : 2 ≤ m₀ := by unfold m₀; norm_num
  have hratio :
      (P.card : ℝ) / (4 * m₀) ≤
        (((N + 1 : ℕ) : ℝ) / m₀) := by
    have hmR : (0 : ℝ) < m₀ := by unfold m₀; norm_num
    have hnDiv : P.card ≤ 4 * (N + 1) := by
      dsimp only [N]
      omega
    have hnDivR : (P.card : ℝ) ≤ 4 * ((N : ℝ) + 1) := by
      exact_mod_cast hnDiv
    rw [show (4 * (m₀ : ℝ)) = (4 : ℝ) * m₀ by ring]
    rw [div_mul_eq_div_div]
    apply (div_le_div_iff_of_pos_right hmR).2
    push_cast
    nlinarith
  have hargPos : (0 : ℝ) < (P.card : ℝ) / (4 * m₀) := by
    have : 0 < P.card := lt_of_lt_of_le (by unfold m₀; norm_num) hbig
    positivity
  have hlog := Real.log_le_log hargPos hratio
  have hcoefLog : (0 : ℝ) ≤ 2 * density * P.card :=
    mul_nonneg (mul_nonneg (by norm_num)
      (by norm_num [density, eps₁] : (0 : ℝ) ≤ density)) (by positivity)
  have hlogMul :
      2 * density * (P.card : ℝ) * Real.log ((P.card : ℝ) / (4 * m₀)) ≤
        2 * density * (P.card : ℝ) *
          Real.log (((N + 1 : ℕ) : ℝ) / m₀) :=
    mul_le_mul_of_nonneg_left hlog hcoefLog
  have hfloorNat : 4 * N ≤ P.card := by
    dsimp only [N]
    omega
  have hfloorR : (4 : ℝ) * N ≤ P.card := by exact_mod_cast hfloorNat
  have herror : 4 * density * (N : ℝ) ≤ density * P.card := by
    convert mul_le_mul_of_nonneg_left hfloorR
      (by norm_num [density, eps₁] : (0 : ℝ) ≤ density) using 1 <;> ring
  calc
    2 * density * (P.card : ℝ) *
          Real.log ((P.card : ℝ) / (4 * m₀)) -
        density * P.card - 3 * P.card / 4 ≤
      2 * density * (P.card : ℝ) *
          Real.log (((N + 1 : ℕ) : ℝ) / m₀) -
        4 * density * N - 3 * P.card / 4 := by nlinarith
    _ ≤ ∑ m ∈ Finset.Icc m₀ N, analyticTerm P.card m :=
      analytic_sum_lower P.card m₀ N hMtwo hMN
    _ ≤ potential P :=
      analytic_sum_le_potential P hfour hvisible le_rfl hNcard

/-- Combining the upper and lower estimates for `W` gives the sole numerical
inequality needed at the end of the proof. -/
theorem log_card_upper
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6)
    (hbig : 4 * m₀ ≤ P.card) :
    (2 * density - 1 / 5) * Real.log P.card ≤
      2 * density * Real.log (4 * m₀) + density + 3 / 4 + 1 / 5 := by
  have hlower := potential_lower_log P hfour hvisible hbig
  have hupper := potential_le_log P hfour
  have hboth := hlower.trans hupper
  have hnNat : 0 < P.card :=
    lt_of_lt_of_le (by unfold m₀; norm_num) hbig
  have hn : (0 : ℝ) < P.card := by exact_mod_cast hnNat
  have hden : (0 : ℝ) < 4 * m₀ := by unfold m₀; norm_num
  have hlogdiv :
      Real.log ((P.card : ℝ) / (4 * m₀)) =
        Real.log P.card - Real.log (4 * m₀) := by
    rw [Real.log_div hn.ne' hden.ne']
  rw [hlogdiv] at hboth
  have hfactored :
      (P.card : ℝ) *
          (2 * density * (Real.log P.card - Real.log (4 * m₀)) -
            density - 3 / 4) ≤
        (P.card : ℝ) * (1 / 5 * Real.log P.card + 1 / 5) := by
    convert hboth using 1 <;> ring
  have hcancel := (mul_le_mul_iff_of_pos_left hn).mp hfactored
  nlinarith

end Lax56Proofs.AnalyticBounds
