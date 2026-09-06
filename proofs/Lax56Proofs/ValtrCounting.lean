import Lax56Proofs.ValtrReduction

namespace Lax56Proofs.ValtrCounting

open Lax56.Geometry Lax56.ConvexLayers Lax56Proofs.ConvexLayers
open Lax56Proofs.ValtrReduction

/-- The geometric data furnished by disjoint consecutive six-vertex caps.
`ValtrCaps.exists_sixCaps` constructs these data. No emptiness or cardinality
bound is part of this structure. -/
structure SixCaps (Q : Finset Point) where
  block : Fin ((extremeLayer Q).card / 6) → Finset Point
  side : Fin ((extremeLayer Q).card / 6) → Point →ᵃ[ℝ] ℝ
  block_subset : ∀ i, block i ⊆ extremeLayer Q
  block_card : ∀ i, (block i).card = 6
  cap : ∀ i, convexHull ℝ (block i : Set Point) =
    convexHull ℝ (extremeLayer Q : Set Point) ∩ {p | 0 ≤ side i p}
  inner_strict : ∀ i p, p ∈ inner Q → p ∈ convexHull ℝ (block i : Set Point) →
    0 < side i p
  other_negative : ∀ i j, i ≠ j → ∀ p ∈ block j, side i p < 0

/-- Positivity of an affine functional on a hull point forces positivity at
some generating vertex. This avoids choosing convex-combination coefficients. -/
theorem exists_positive_vertex (Y : Finset Point) (f : Point →ᵃ[ℝ] ℝ)
    {p : Point} (hp : p ∈ convexHull ℝ (Y : Set Point)) (hpos : 0 < f p) :
    ∃ y ∈ Y, 0 < f y := by
  by_contra h
  push_neg at h
  have hsub : (Y : Set Point) ⊆ f ⁻¹' Set.Iic 0 := h
  have hle := convexHull_min hsub ((convex_Iic (0 : ℝ)).affine_preimage f) hp
  exact (not_le_of_gt hpos) hle

/-- Every nonempty cap requires a vertex of the next layer, and different caps
require different vertices. This formalizes the affine-function and injection
parts of Lemma 2 once the polygon separation data have been supplied. -/
theorem layer_bound_of_sixCaps {Q : Finset Point} (hno : ¬HasEmptyHexagon Q)
    (caps : SixCaps Q) :
    (extremeLayer Q).card ≤ 6 * (extremeLayer (inner Q)).card + 5 := by
  classical
  have hpoint (i) : ∃ y ∈ extremeLayer (inner Q),
      y ∈ convexHull ℝ (caps.block i : Set Point) ∧ 0 < caps.side i y := by
    have hblockconv := convexPosition_mono (extremeLayer_convexPosition Q) (caps.block_subset i)
    have hextra : ∃ p ∈ Q, p ∈ convexHull ℝ (caps.block i : Set Point) ∧ p ∉ caps.block i := by
      by_contra h
      apply hno
      refine ⟨caps.block i, (caps.block_subset i).trans (extremeLayer_subset Q),
        caps.block_card i, hblockconv, ?_⟩
      intro p hp hh
      by_contra hn
      exact h ⟨p, hp, hh, hn⟩
    obtain ⟨p, hpQ, hpB, hpnot⟩ := hextra
    have hpinner : p ∈ inner Q := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hpQ, ?_⟩
      intro hpext
      exact hpnot ((convexIndependent_set_iff_inter_convexHull_subset.mp
        (extremeLayer_convexPosition Q)) (caps.block i) (caps.block_subset i) ⟨hpext, hpB⟩)
    have hpnext : p ∈ convexHull ℝ (extremeLayer (inner Q) : Set Point) := by
      rw [convexHull_extremeLayer]
      exact subset_convexHull ℝ _ hpinner
    obtain ⟨y, hy, hypos⟩ := exists_positive_vertex _ (caps.side i) hpnext
      (caps.inner_strict i p hpinner hpB)
    refine ⟨y, hy, ?_, hypos⟩
    rw [caps.cap]
    refine ⟨?_, hypos.le⟩
    rw [convexHull_extremeLayer]
    exact subset_convexHull ℝ _ (inner_subset Q (extremeLayer_subset (inner Q) hy))
  choose y hy hycap hypos using hpoint
  let pick : Fin ((extremeLayer Q).card / 6) → extremeLayer (inner Q) := fun i ↦ ⟨y i, hy i⟩
  have hinj : Function.Injective pick := by
    intro i j heq
    by_contra hij
    have hyneg : caps.side i (y j) < 0 :=
      convexHull_min (caps.other_negative i j hij)
        ((convex_Iio (0 : ℝ)).affine_preimage (caps.side i)) (hycap j)
    have hyij : y i = y j := congrArg Subtype.val heq
    rw [← hyij] at hyneg
    exact (not_lt_of_ge (hypos i).le) hyneg
  have hcard := Fintype.card_le_of_injective pick hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hcard
  omega

/-- The exceptional six-vertex outer layer needs no cap construction. -/
theorem layer_bound_of_card_le_six {Q : Finset Point} (hno : ¬HasEmptyHexagon Q)
    (hsmall : (extremeLayer Q).card ≤ 6) :
    (extremeLayer Q).card ≤ 6 * (extremeLayer (inner Q)).card + 5 := by
  by_cases hfive : (extremeLayer Q).card ≤ 5
  · omega
  have hnonempty : extremeLayer (inner Q) ≠ ∅ := by
    intro h
    have hi : inner Q = ∅ := (extremeLayer_eq_empty_iff _).mp h
    have hself : extremeLayer Q = Q :=
      Finset.Subset.antisymm (extremeLayer_subset Q) (Finset.sdiff_eq_empty_iff_subset.mp hi)
    have hc : ConvexPosition Q := hself ▸ extremeLayer_convexPosition Q
    apply hno (hasEmptyHexagon_of_convexPosition hc ?_)
    rw [← hself]
    omega
  have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnonempty)
  omega

/-- Reduces Lemma 2 to constructing the consecutive caps for polygons with
more than six vertices; all counting and small cases are now proved. -/
theorem consecutiveLayerBound_of_caps
    (construct : ∀ Q : Finset Point, ¬HasThreeCollinear Q →
      6 < (extremeLayer Q).card → Nonempty (SixCaps Q)) : ConsecutiveLayerBound := by
  intro Q hgen hno
  by_cases hsmall : (extremeLayer Q).card ≤ 6
  · exact layer_bound_of_card_le_six hno hsmall
  · obtain ⟨caps⟩ := construct Q hgen (by omega)
    exact layer_bound_of_sixCaps hno caps

end Lax56Proofs.ValtrCounting
