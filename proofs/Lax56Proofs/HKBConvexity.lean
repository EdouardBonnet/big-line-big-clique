import Lax56Proofs.HKBHexGeometry
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

/-!
Supporting-face and affine-functional lemmas used by the direct
Hujter--Kisfaludi-Bak hexagon argument.
-/

namespace Lax56Proofs.HKBConvexity

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.Blockers
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.Orientation

/-- Oriented area commutes with a finite affine combination. -/
theorem turn_sum_smul_of_sum_eq_one
    (a b : Point) (s : Finset Point) (w : Point → ℝ)
    (hw : ∑ p ∈ s, w p = 1) :
    turn a b (∑ p ∈ s, w p • p) = ∑ p ∈ s, w p * turn a b p := by
  classical
  have hcoord (f : Point → ℝ) (c : ℝ) :
      (∑ p ∈ s, w p * (f p - c)) = (∑ p ∈ s, w p * f p) - c := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw, one_mul]
  have hsum :
      (∑ p ∈ s, w p * turn a b p) =
        (b.1 - a.1) * (∑ p ∈ s, w p * (p.2 - a.2)) -
        (b.2 - a.2) * (∑ p ∈ s, w p * (p.1 - a.1)) := by
    calc
      (∑ p ∈ s, w p * turn a b p) =
          ∑ p ∈ s, ((b.1 - a.1) * (w p * (p.2 - a.2)) -
            (b.2 - a.2) * (w p * (p.1 - a.1))) := by
              apply Finset.sum_congr rfl
              intro p _
              simp only [turn]
              ring
      _ = (∑ p ∈ s, (b.1 - a.1) * (w p * (p.2 - a.2))) -
          (∑ p ∈ s, (b.2 - a.2) * (w p * (p.1 - a.1))) := by
            rw [Finset.sum_sub_distrib]
      _ = (b.1 - a.1) * (∑ p ∈ s, w p * (p.2 - a.2)) -
          (b.2 - a.2) * (∑ p ∈ s, w p * (p.1 - a.1)) := by
            rw [Finset.mul_sum, Finset.mul_sum]
  rw [hsum, hcoord, hcoord]
  simp only [turn, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul]

/-- A convex combination of points in a closed supporting half-plane can
lie on its boundary only if every point carrying positive weight lies on the
boundary. -/
theorem weight_eq_zero_of_turn_pos
    (a b x : Point) (s : Finset Point) (w : Point → ℝ)
    (hw0 : ∀ p ∈ s, 0 ≤ w p)
    (hw1 : ∑ p ∈ s, w p = 1)
    (hx : ∑ p ∈ s, w p • p = x)
    (hboundary : turn a b x = 0)
    (hturn0 : ∀ p ∈ s, 0 ≤ turn a b p)
    {p : Point} (hp : p ∈ s) (hpturn : 0 < turn a b p) :
    w p = 0 := by
  have hsum : ∑ q ∈ s, w q * turn a b q = 0 := by
    rw [← turn_sum_smul_of_sum_eq_one a b s w hw1, hx, hboundary]
  have hnonneg : ∀ q ∈ s, 0 ≤ w q * turn a b q := by
    intro q hq
    exact mul_nonneg (hw0 q hq) (hturn0 q hq)
  have hpzero : w p * turn a b p = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum p hp
  exact (mul_eq_zero.mp hpzero).resolve_right hpturn.ne'

/-- On the line supporting side `i`, the selected side blocker is the only
point of `hexBlockers`. -/
theorem edgeTurn_eq_zero_iff_eq_sideBlocker
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    {p : Point} (hp : p ∈ hexBlockers P h) (i : Fin 6) :
    turn (h i) (h (i + 1)) p = 0 ↔ p = sideBlocker hside i := by
  constructor
  · intro hpzero
    let s := sideBlocker hside i
    have hpdata := mem_hexBlockers.mp hp
    have hsB : s ∈ hexBlockers P h := sideBlocker_mem hside i
    have hsdata := mem_hexBlockers.mp hsB
    have hsseg : s ∈ openSegment ℝ (h i) (h (i + 1)) :=
      sideBlocker_between hside i
    have hisucc : h i ≠ h (i + 1) := by
      apply hh.1.ne
      fin_cases i <;> decide
    have hpi : p ≠ h i := fun e ↦ hpdata.2.2 ⟨i, e.symm⟩
    have hpis : p ≠ h (i + 1) := fun e ↦ hpdata.2.2 ⟨i + 1, e.symm⟩
    have hsi : s ≠ h i := by
      intro e
      have hsseg' : h i ∈ openSegment ℝ (h i) (h (i + 1)) := e ▸ hsseg
      exact hisucc ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hsseg')
    have hsis : s ≠ h (i + 1) := by
      intro e
      have hsseg' : h (i + 1) ∈ openSegment ℝ (h i) (h (i + 1)) := e ▸ hsseg
      exact hisucc ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hsseg')
    exact third_point_unique hfour (hhP i) (hhP (i + 1))
      (hexBlockers_subset P h hp) (hexBlockers_subset P h hsB)
      hisucc hpi hpis hsi hsis
      (mem_line_of_turn_eq_zero hisucc hpzero)
      (mem_affineSpan_pair_of_mem_openSegment hsseg)
  · rintro rfl
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment
      (sideBlocker_between hside i), neg_zero]

/-- Supporting-face lemma specialized to a side blocker: whenever a selected
side blocker lies in the convex hull of a subset of all blockers, it already
belongs to that subset. -/
theorem sideBlocker_mem_of_mem_convexHull
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    {A : Finset Point} (hAB : A ⊆ hexBlockers P h)
    (i : Fin 6)
    (hsconv : sideBlocker hside i ∈ convexHull ℝ (A : Set Point)) :
    sideBlocker hside i ∈ A := by
  classical
  by_contra hsA
  obtain ⟨w, hw0, hw1, hwcenter⟩ := (Finset.mem_convexHull').mp hsconv
  have hturn0 : ∀ p ∈ A, 0 ≤ turn (h i) (h (i + 1)) p := by
    intro p hp
    exact edgeTurn_nonneg_of_mem_convexHull hh
      (mem_hexBlockers.mp (hAB hp)).2.1 i
  have hwzero : ∀ p ∈ A, w p = 0 := by
    intro p hp
    have hpne : p ≠ sideBlocker hside i := fun e ↦ hsA (e ▸ hp)
    have hpturn : 0 < turn (h i) (h (i + 1)) p := by
      have hnzero : turn (h i) (h (i + 1)) p ≠ 0 := by
        intro hz
        exact hpne ((edgeTurn_eq_zero_iff_eq_sideBlocker
          hfour hh hhP hside (hAB hp) i).mp hz)
      exact lt_of_le_of_ne (hturn0 p hp) (Ne.symm hnzero)
    apply weight_eq_zero_of_turn_pos (h i) (h (i + 1))
      (sideBlocker hside i) A w hw0 hw1 hwcenter
    · exact (edgeTurn_eq_zero_iff_eq_sideBlocker hfour hh hhP hside
        (sideBlocker_mem hside i) i).mpr rfl
    · exact hturn0
    · exact hp
    · exact hpturn
  have : (∑ p ∈ A, w p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    exact hwzero p hp
  linarith

/-- The open segment between two distinct blockers is strictly inside the
hexagon. This includes the case where both endpoints are side blockers on
different sides. -/
theorem openSegment_between_blockers_strictlyInside
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    {x y r : Point} (hx : x ∈ hexBlockers P h)
    (hy : y ∈ hexBlockers P h) (hxy : x ≠ y)
    (hr : r ∈ openSegment ℝ x y) :
    StrictlyInsideHexagon h r := by
  intro i
  have hx0 : 0 ≤ turn (h i) (h (i + 1)) x :=
    edgeTurn_nonneg_of_mem_convexHull hh (mem_hexBlockers.mp hx).2.1 i
  have hy0 : 0 ≤ turn (h i) (h (i + 1)) y :=
    edgeTurn_nonneg_of_mem_convexHull hh (mem_hexBlockers.mp hy).2.1 i
  apply edgeTurn_pos_of_mem_openSegment hr hx0 hy0
  by_contra hn
  push Not at hn
  have hxz : turn (h i) (h (i + 1)) x = 0 := le_antisymm hn.1 hx0
  have hyz : turn (h i) (h (i + 1)) y = 0 := le_antisymm hn.2 hy0
  have hxeq := (edgeTurn_eq_zero_iff_eq_sideBlocker
    hfour hh hhP hside hx i).mp hxz
  have hyeq := (edgeTurn_eq_zero_iff_eq_sideBlocker
    hfour hh hhP hside hy i).mp hyz
  exact hxy (hxeq.trans hyeq.symm)

end Lax56Proofs.HKBConvexity
