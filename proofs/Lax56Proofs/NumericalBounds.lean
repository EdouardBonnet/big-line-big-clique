import Lax56Proofs.AnalyticBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Lax56Proofs.NumericalBounds

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Lax56.Geometry
open Lax56Proofs.IntervalDensity
open Lax56Proofs.AnalyticBounds

/-- The first power-series term gives `log(5/4) ≥ 2/9`. -/
theorem log_five_four_lower : (2 / 9 : ℝ) ≤ Real.log (5 / 4) := by
  have h := Real.sum_range_le_log_div
    (x := (1 / 9 : ℝ)) (by norm_num) (by norm_num) 1
  norm_num [Finset.sum_range_succ] at h
  nlinarith

/-- A convenient strict lower bound for `log 10`. -/
theorem log_ten_lower : (23 / 10 : ℝ) < Real.log 10 := by
  have hdecomp : Real.log 10 = 3 * Real.log 2 + Real.log (5 / 4) := by
    calc
      Real.log (10 : ℝ) = Real.log (8 * (5 / 4 : ℝ)) := by norm_num
      _ = Real.log 8 + Real.log (5 / 4) :=
        Real.log_mul (by norm_num) (by norm_num)
      _ = 3 * Real.log 2 + Real.log (5 / 4) := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
  rw [hdecomp]
  nlinarith [Real.log_two_gt_d9, log_five_four_lower]

/-- A deliberately coarse logarithmic bound for the enlarged interval scale.
Keeping the exponent symbolic avoids evaluating the enormous final power of ten. -/
theorem log_four_m₀_upper : Real.log (4 * m₀) < (500 : ℝ) := by
  have hsize : (4 * m₀ : ℝ) < 2 ^ 434 := by norm_num [m₀]
  have hlog := Real.log_lt_log (by norm_num [m₀] : (0 : ℝ) < 4 * m₀) hsize
  rw [Real.log_pow] at hlog
  have htwo : Real.log 2 ≤ (1 : ℝ) := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem log_lower_of_power_le {n : ℕ} (hpow : 10 ^ (2 ^ 450) ≤ n) :
    (2 ^ 450 : ℝ) * (23 / 10) < Real.log n := by
  have hpowR : (((10 ^ (2 ^ 450) : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log
    (show (0 : ℝ) < ((10 ^ (2 ^ 450) : ℕ) : ℝ) by positivity) hpowR
  have hlogPow : (2 ^ 450 : ℝ) * Real.log 10 ≤ Real.log n := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlog
    rw [Real.log_pow] at hlog
    convert hlog using 1 <;> norm_num
  have hmul := mul_lt_mul_of_pos_left log_ten_lower
    (by positivity : (0 : ℝ) < 2 ^ 450)
  exact hmul.trans_le hlogPow

/-- The explicit exponent is incompatible with the analytic upper bound for
a point set having neither forbidden configuration. -/
theorem impossible_large_bad_set
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6)
    (hpow : 10 ^ (2 ^ 450) ≤ P.card) : False := by
  have hbig : 4 * m₀ ≤ P.card := by
    calc
      4 * m₀ ≤ 10 ^ 131 := by norm_num [m₀]
      _ ≤ 10 ^ (2 ^ 450) :=
        Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ P.card := hpow
  have hu := log_card_upper P hfour hvisible hbig
  have hl := log_lower_of_power_le hpow
  have hcoef : (0 : ℝ) < 2 * density - 1 / 5 := by
    norm_num [density, eps₁]
  have hleft :
      (2 * density - 1 / 5) * ((2 ^ 450 : ℝ) * (23 / 10)) <
        (2 * density - 1 / 5) * Real.log P.card :=
    mul_lt_mul_of_pos_left hl hcoef
  have hlogCMul :
      2 * density * Real.log (4 * m₀) < 2 * density * 500 := by
    exact mul_lt_mul_of_pos_left log_four_m₀_upper (by norm_num [density, eps₁])
  have hright :
      2 * density * Real.log (4 * m₀) + density + 3 / 4 + 1 / 5 <
        (2 * density - 1 / 5) * ((2 ^ 450 : ℝ) * (23 / 10)) := by
    norm_num [density, eps₁] at hlogCMul ⊢
    nlinarith
  exact (not_lt_of_ge hu) (hright.trans hleft)

end Lax56Proofs.NumericalBounds
