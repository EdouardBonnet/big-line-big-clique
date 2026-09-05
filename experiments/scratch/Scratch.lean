import Lax56Proofs.HKBDirectTrianglePatterns

#check openSegment
#check openSegment_subset_segment
#check openSegment_subset_openSegment
#check segment_subset_segment
#check openSegment_subset_iff
#check segment_openSegment_trans
#check openSegment_trans
#check Convex.openSegment_subset
#check Convex.segment_subset
#check Set.OrdConnected.out'
#check convex_openSegment
#check left_mem_segment
#check right_mem_segment
#check segment_subset_affineSpan
#check openSegment_subset_affineSpan
#check mem_openSegment_iff
#check mem_openSegment_iff_div
#check mem_openSegment_iff_exists_pos
#check mem_openSegment_iff_exists_ne
#check mem_segment_iff
#check mem_openSegment

open Lax56.Geometry

theorem test_nested {p q s y : Point}
    (hq : q ∈ openSegment ℝ p s) (hs : s ∈ openSegment ℝ p y) :
    q ∈ openSegment ℝ p y := by
  rw [openSegment_eq_image] at hq hs ⊢
  obtain ⟨t, ht, rfl⟩ := hq
  obtain ⟨u, hu, rfl⟩ := hs
  refine ⟨t * u, ⟨mul_pos ht.1 hu.1, ?_⟩, ?_⟩
  · have htu : t * u < u := by
      nlinarith [mul_pos (sub_pos.mpr ht.2) hu.1]
    exact htu.trans hu.2
  simp [AffineMap.lineMap_apply]
  module
