import Lax56Proofs.SlidingWindows
import Lax56Proofs.Telescoping
import Lax56Proofs.HarmonicUpper
import Mathlib.Tactic

namespace Lax56Proofs.PotentialLower

open scoped BigOperators
open Lax56.Geometry
open Lax56Proofs.WeightedPairs
open Lax56Proofs.Telescoping
open Lax56Proofs.HarmonicUpper
open Lax56Proofs.SlidingWindows

/-- The kernel with its negative tail truncated to zero. -/
noncomputable def truncKernel (d m : ℕ) : ℝ :=
  2 / ((m : ℝ) ^ 2 - 1) * ((m - d : ℕ) : ℝ) / m

theorem truncKernel_eq_kernel_of_lt {d m : ℕ} (h : d < m) :
    truncKernel d m = kernel d m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le d) h))
  rw [truncKernel, kernel, Nat.cast_sub h.le]
  field_simp

theorem truncKernel_eq_zero_of_le {d m : ℕ} (h : m ≤ d) :
    truncKernel d m = 0 := by
  simp [truncKernel, Nat.sub_eq_zero_of_le h]

theorem sum_truncKernel_eq_filter (d M N : ℕ) :
    ∑ m ∈ Finset.Icc M N, truncKernel d m =
      ∑ m ∈ (Finset.Icc M N).filter (d < ·), kernel d m := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _hm
  split_ifs with h
  · exact truncKernel_eq_kernel_of_lt h
  · exact truncKernel_eq_zero_of_le (Nat.le_of_not_gt h)

/-- The telescoping estimate remains valid after restricting the scale range. -/
theorem sum_truncKernel_le_inv (d M N : ℕ) (hd : 0 < d) :
    ∑ m ∈ Finset.Icc M N, truncKernel d m ≤ 1 / (d : ℝ) := by
  rw [sum_truncKernel_eq_filter]
  by_cases hdN : d ≤ N
  · calc
      ∑ m ∈ (Finset.Icc M N).filter (d < ·), kernel d m ≤
          ∑ m ∈ Finset.Icc (d + 1) N, kernel d m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
          omega
        · intro m hm _hnot
          simp only [Finset.mem_Icc] at hm
          exact kernel_nonneg hd (by omega)
      _ ≤ 1 / (d : ℝ) := sum_kernel_le_inv d N hd hdN
  · have hzero :
        ∑ m ∈ (Finset.Icc M N).filter (d < ·), kernel d m = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        omega
    rw [hzero]
    positivity

/-- Contribution at one interval length to the lower bound for `W`. -/
noncomputable def scaleContribution (P : Finset Point) (m : ℕ) : ℝ :=
  2 / ((m : ℝ) ^ 2 - 1) * (deficit P m : ℝ) / m

theorem scaleContribution_eq_sum (P : Finset Point) (m : ℕ) :
    scaleContribution P m =
      ∑ e : BadPair P, truncKernel e.1.stretch m := by
  classical
  unfold scaleContribution deficit
  simp only [Nat.cast_sum]
  rw [Finset.mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _he
  unfold truncKernel
  ring

/-- Lemma 5.1 summed over all bad pairs: every selected scale contribution
is paid for by the reciprocal-stretch potential. -/
theorem scale_sum_le_potential (P : Finset Point) (M N : ℕ) :
    ∑ m ∈ Finset.Icc M N, scaleContribution P m ≤ potential P := by
  classical
  simp_rw [scaleContribution_eq_sum]
  rw [Finset.sum_comm]
  unfold potential OrderedPair.weight
  exact Finset.sum_le_sum fun e _ ↦
    sum_truncKernel_le_inv e.1.stretch M N e.1.stretch_pos

end Lax56Proofs.PotentialLower
