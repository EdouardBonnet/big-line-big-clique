import Mathlib.Tactic

namespace Lax56Proofs.Telescoping

open scoped BigOperators

/-- The coefficient assigned at scale `m` to a pair of stretch `d`. -/
noncomputable def kernel (d m : ℕ) : ℝ :=
  2 / ((m : ℝ) ^ 2 - 1) * (1 - (d : ℝ) / m)

theorem kernel_nonneg {d m : ℕ} (hd0 : 0 < d) (hd : d < m) : 0 ≤ kernel d m := by
  have hm : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
  have hm0 : (0 : ℝ) < m := by positivity
  have hdm : (d : ℝ) ≤ m := by exact_mod_cast hd.le
  have hden : (0 : ℝ) < (m : ℝ) ^ 2 - 1 := by nlinarith
  have hratio : (d : ℝ) / m ≤ 1 := (div_le_one hm0).2 hdm
  unfold kernel
  exact mul_nonneg (div_nonneg (by norm_num) hden.le) (sub_nonneg.2 hratio)

/-- Finite closed form for the telescoping series in Lemma 5.1. Keeping the
upper-end correction makes the subsequent comparison with `1/d` immediate. -/
theorem sum_kernel_eq
    (d N : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    ∑ m ∈ Finset.Icc (d + 1) N, kernel d m =
      1 / (d : ℝ) + ((d : ℝ) - 1) / N - ((d : ℝ) + 1) / (N + 1) := by
  induction N, hdN using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (a := d + 1) (b := d) (by omega)]
      simp only [Finset.sum_empty]
      have hdR : (d : ℝ) ≠ 0 := by positivity
      have hd1R : (d : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  | succ N hdN ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      unfold kernel
      have hdR : (d : ℝ) ≠ 0 := by positivity
      have hNR : (N : ℝ) ≠ 0 := by
        exact_mod_cast (lt_of_lt_of_le hd hdN).ne'
      have hN1R : (N : ℝ) + 1 ≠ 0 := by positivity
      have hN2R : (N : ℝ) + 2 ≠ 0 := by positivity
      have hsquare : ((N : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
        nlinarith [show (0 : ℝ) < N by positivity]
      push_cast
      field_simp
      ring

/-- The finite truncation used in the proof is at most the pair weight. -/
theorem sum_kernel_le_inv
    (d N : ℕ) (hd : 0 < d) (hdN : d ≤ N) :
    ∑ m ∈ Finset.Icc (d + 1) N, kernel d m ≤ 1 / (d : ℝ) := by
  rw [sum_kernel_eq d N hd hdN]
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le hd hdN)
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hdN' : (d : ℝ) ≤ N := by exact_mod_cast hdN
  have : ((d : ℝ) - 1) / N ≤ ((d : ℝ) + 1) / (N + 1) := by
    apply (div_le_div_iff₀ hN hN1).2
    nlinarith
  linarith

end Lax56Proofs.Telescoping
