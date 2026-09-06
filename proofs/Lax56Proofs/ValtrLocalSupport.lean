import Lax56Proofs.ValtrRadialOrder

namespace Lax56Proofs.ValtrLocalSupport

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors Lax56Proofs.ValtrCyclic
open scoped Classical

/-- The intermediate outer vertex is on the outer side of the chord
joining the two selected inner apices. The opposite inequality would
put that outer vertex in the hull of the remaining points. -/
theorem intermediate_vertex_left_of_chord {Q : Finset Point} {d p q b : Point}
    (hb : b ∈ extremeLayer Q) (hd : d ∈ inner Q)
    (hp : p ∈ inner Q) (hq : q ∈ inner Q)
    (hpb : turn d p b < 0) (hbq : turn d b q < 0) : 0 < turn p q b := by
  by_contra hh
  have hh := le_of_not_gt hh
  have h₁ : 0 < turn d q b := by rw [turn_swap_last]; exact neg_pos.mpr hbq
  have h₂ : 0 ≤ turn q p b := by rw [turn_swap_first]; exact neg_nonneg.mpr hh
  have h₃ : 0 < turn p d b := by rw [turn_swap_first]; exact neg_pos.mpr hpb
  have htri : 0 < turn d q p := by
    have h := turn_triangle_decompose d q p b
    linarith
  have hbTri := weaklyInsideTriangle_mem_triangleHull htri ⟨h₁.le, h₂, h₃.le⟩
  apply extreme_not_mem_convexHull_inner hb
  exact triangleHull_subset_of_mem (convex_convexHull ℝ _)
    (subset_convexHull ℝ _ hd) (subset_convexHull ℝ _ hq)
    (subset_convexHull ℝ _ hp) hbTri

/-- Four clockwise neighboring rays surround their common center.
Splitting on one diagonal gives an explicit containing triangle. This
is the local geometric input to the projective maximum principle. -/
theorem mem_neighbor_hull_of_four_clockwise_turns {p a b e f : Point}
    (hab : turn p a b < 0) (hbe : turn p b e < 0)
    (hef : turn p e f < 0) (hfa : turn p f a < 0)
    (hae : turn p a e ≠ 0) :
    p ∈ convexHull ℝ ({a, b, e, f} : Set Point) := by
  rcases lt_or_gt_of_ne hae with hneg | hpos
  · have hstrict : StrictlyInsideTriangle a f e p := by
      refine ⟨?_, ?_, ?_⟩
      · convert neg_pos.mpr hfa using 1 <;> unfold turn <;> ring
      · convert neg_pos.mpr hef using 1 <;> unfold turn <;> ring
      · convert neg_pos.mpr hneg using 1 <;> unfold turn <;> ring
    apply convexHull_mono (show ({a, f, e} : Set Point) ⊆ {a, b, e, f} by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull hstrict
  · have hstrict : StrictlyInsideTriangle a e b p := by
      refine ⟨?_, ?_, ?_⟩
      · convert hpos using 1 <;> unfold turn <;> ring
      · convert neg_pos.mpr hbe using 1 <;> unfold turn <;> ring
      · convert neg_pos.mpr hab using 1 <;> unfold turn <;> ring
    apply convexHull_mono (show ({a, e, b} : Set Point) ⊆ {a, b, e, f} by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull hstrict

/-- The first chain edge supports a selected inner vertex. A wrong-side
vertex would lie strictly inside the empty first base triangle. -/
theorem first_edge_support_of_empty_triangle {u p v q w : Point}
    (hp : StrictlyInsideTriangle u q v p) (hchord : turn p q w ≤ 0)
    (hbase : 0 < turn v u w)
    (hempty : w ∈ triangleHull u p v → w = u ∨ w = p ∨ w = v) :
    turn u p w ≤ 0 := by
  have hA : 0 < turn p u q := by convert hp.1 using 1 <;> unfold turn <;> ring
  have hB : 0 < turn p q v := by convert hp.2.1 using 1 <;> unfold turn <;> ring
  have hC : 0 < turn p v u := by convert hp.2.2 using 1 <;> unfold turn <;> ring
  by_contra hh
  have hleft : 0 < turn u p w := lt_of_not_ge hh
  have hid : turn p u q * turn p v w =
      turn p q v * turn u p w - turn p v u * turn p q w := by
    have h := turn_origin_relation p u q v w
    rw [turn_swap_first u p w] at h
    linarith
  have hright : 0 < turn p v w := by
    apply (mul_pos_iff_of_pos_left hA).mp
    rw [hid]
    exact sub_pos.mpr ((mul_nonpos_of_nonneg_of_nonpos hC.le hchord).trans_lt
      (mul_pos hB hleft))
  have hwTri := strictlyInsideTriangle_mem_triangleHull
    (show StrictlyInsideTriangle u p v w from ⟨hleft, hright, hbase⟩)
  rcases hempty hwTri with rfl | rfl | rfl <;> simp_all

/-- The symmetric empty-triangle argument for the last chain edge. -/
theorem last_edge_support_of_empty_triangle {u p v q w : Point}
    (hp : StrictlyInsideTriangle u q v p) (hchord : turn q p w ≤ 0)
    (hbase : 0 < turn v u w)
    (hempty : w ∈ triangleHull u p v → w = u ∨ w = p ∨ w = v) :
    turn p v w ≤ 0 := by
  have hA : 0 < turn p u q := by convert hp.1 using 1 <;> unfold turn <;> ring
  have hB : 0 < turn p q v := by convert hp.2.1 using 1 <;> unfold turn <;> ring
  have hC : 0 < turn p v u := by convert hp.2.2 using 1 <;> unfold turn <;> ring
  by_contra hh
  have hright : 0 < turn p v w := lt_of_not_ge hh
  have hid : turn p q v * turn u p w =
      turn p u q * turn p v w - turn p v u * turn q p w := by
    have h := turn_origin_relation p u q v w
    rw [turn_swap_first u p w, turn_swap_first q p w] at h
    linarith
  have hleft : 0 < turn u p w := by
    apply (mul_pos_iff_of_pos_left hB).mp
    rw [hid]
    exact sub_pos.mpr ((mul_nonpos_of_nonneg_of_nonpos hC.le hchord).trans_lt
      (mul_pos hA hright))
  have hwTri := strictlyInsideTriangle_mem_triangleHull
    (show StrictlyInsideTriangle u p v w from ⟨hleft, hright, hbase⟩)
  rcases hempty hwTri with rfl | rfl | rfl <;> simp_all

/-- Assemble the local hull relations for the whole run from its
clockwise inner triples, intermediate-vertex signs, supporting base
edges, and the two endpoint containments. -/
theorem local_hulls_of_run_signs (h b : ℕ → Point) {m : ℕ} (_hm : 2 ≤ m)
    (hfirst : StrictlyInsideTriangle (b 1) (h 2) (b 2) (h 1))
    (hlast : StrictlyInsideTriangle (b m) (h (m - 1)) (b (m + 1)) (h m))
    (htri : ∀ i j k, 1 ≤ i → i < j → j < k → k ≤ m → turn (h i) (h j) (h k) < 0)
    (hmiddle : ∀ k, 1 ≤ k → k < m → 0 < turn (h k) (h (k + 1)) (b (k + 1)))
    (hbase : ∀ k, 1 ≤ k → k ≤ m → turn (b k) (b (k + 1)) (h k) < 0)
    (hne : ∀ k, 2 ≤ k → k < m → turn (h k) (h (k - 1)) (b (k + 1)) ≠ 0) :
    ∀ k, 1 ≤ k → k ≤ m → h k ∈ convexHull ℝ
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point) := by
  intro k hk hkm
  by_cases hk1 : k = 1
  · subst k
    apply convexHull_mono (show ({b 1, h 2, b 2} : Set Point) ⊆ {h (1 - 1), b 1, b (1 + 1), h (1 + 1)} by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull hfirst
  by_cases hkLast : k = m
  · subst k
    apply convexHull_mono (show ({b m, h (m - 1), b (m + 1)} : Set Point) ⊆
        {h (m - 1), b m, b (m + 1), h (m + 1)} by
      intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull hlast
  have hprev := hmiddle (k - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hprev
  have hnext := hmiddle k hk (by omega)
  apply mem_neighbor_hull_of_four_clockwise_turns
  · rw [turn_swap_first]; exact neg_neg_of_pos hprev
  · convert hbase k hk hkm using 1 <;> unfold turn <;> ring
  · rw [turn_swap_last]; exact neg_neg_of_pos hnext
  · convert htri (k - 1) k (k + 1) (by omega) (by omega) (by omega) (by omega)
      using 1 <;> unfold turn <;> ring
  · exact hne k (by omega) (by omega)

end Lax56Proofs.ValtrLocalSupport
