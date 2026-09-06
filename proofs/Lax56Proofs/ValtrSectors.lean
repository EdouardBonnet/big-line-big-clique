import Lax56Proofs.ValtrExtension

/-!
Elementary sector geometry for Section 2.3 of Valtr's preprint (Section 3.3
of the published paper). These lemmas use only determinant inequalities and
finite convex hulls, not the four-layer lemma.
-/

namespace Lax56Proofs.ValtrSectors

open Lax56.Geometry Lax56.ConvexLayers Lax56.HujterKisfaludiBak
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry Lax56Proofs.CyclicOrder
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension

theorem convex_sector {n : ℕ} (v : Fin n → Point) : Convex ℝ (sector v) := by
  intro x hx y hy u w hu hw huw i j hij
  rw [turn_convex_combo _ _ _ _ _ _ huw]
  rcases hu.eq_or_lt with rfl | hu
  · have hw1 : w = 1 := by linarith
    simpa [hw1] using hy i j hij
  · exact add_pos_of_pos_of_nonneg (mul_pos hu (hx i j hij))
      (mul_nonneg hw (hy i j hij).le)

/-- A supporting line through one triangle vertex is strict everywhere
else in the triangle when the other two vertices lie strictly on one side. -/
theorem turn_pos_on_triangle_except_vertex {u v a b c p : Point}
    (ha : turn u v a = 0) (hb : 0 < turn u v b) (hc : 0 < turn u v c)
    (hp : p ∈ triangleHull a b c) (hpa : p ≠ a) : 0 < turn u v p := by
  classical
  have hnonneg : ∀ x ∈ ({a, b, c} : Finset Point), 0 ≤ turn u v x := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha.symm ▸ le_refl 0
    · exact hb.le
    · exact hc.le
  have hpHull : p ∈ convexHull ℝ (({a, b, c} : Finset Point) : Set Point) := by
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hp
  apply lt_of_le_of_ne (turn_nonneg_of_mem_convexHull hnonneg hpHull)
  intro hz
  apply hpa
  apply eq_of_mem_convexHull_of_unique_turn_zero (A := {a, b, c}) (by simp)
    hnonneg _ hpHull hz.symm
  intro x hx hxzero
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · rfl
  · exact (hb.ne' hxzero).elim
  · exact (hc.ne' hxzero).elim

/-- The elementary containment used when `c_i` exists: moving the interior
apex `d` to any non-base-vertex point `c` of its triangle enlarges the
exterior sector. The statement holds for every plane point of the sector,
not just the finite ambient set. -/
theorem sector_triangle_mono {a b c d : Point}
    (hc : c ∈ triangleHull d a b) (hca : c ≠ a) (hcb : c ≠ b) :
    sector ![a, d, b] ⊆ sector ![a, c, b] := by
  intro q hq
  have h01 : 0 < turn a d q := hq 0 1 (by decide)
  have h02 : 0 < turn a b q := hq 0 2 (by decide)
  have h12 : 0 < turn d b q := hq 1 2 (by decide)
  have hleft : 0 < turn a c q := by
    rw [turn_rotate q a c]
    apply turn_pos_on_triangle_except_vertex (a := a) (b := d) (c := b)
      (by simp) _ _ _ hca
    · rwa [← turn_rotate q a d]
    · rwa [← turn_rotate q a b]
    · convert hc using 1
      unfold triangleHull
      congr 1
      ext x
      simp [or_comm, or_left_comm]
  have hright : 0 < turn c b q := by
    rw [← turn_rotate c b q]
    apply turn_pos_on_triangle_except_vertex (a := b) (b := d) (c := a)
      (by simp) _ _ _ hcb
    · rwa [turn_rotate d b q]
    · rwa [turn_rotate a b q]
    · simpa only [triangleHull_rotate] using hc
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- A sector is outside the closed hull of its defining triangle. -/
theorem sector_not_mem_triangle {a b c q : Point} (htri : 0 < turn a c b)
    (hq : q ∈ sector ![a, c, b]) : q ∉ triangleHull a c b := by
  intro hqT
  have hpos : 0 < turn a b q := hq 0 2 (by decide)
  have hnonpos : turn a b q ≤ 0 := by
    apply turn_nonpos_of_mem_convexHull (A := {a, c, b}) _ hqT
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · simp
    · rw [turn_swap_last]
      linarith
    · simp
  exact hpos.not_ge hnonpos

/-- Outside the defining triangle, the two non-base inequalities already
imply membership in its exterior sector. -/
theorem mem_sector_of_two_sides {a c b q : Point}
    (htri : 0 < turn a c b) (hq : q ∉ triangleHull a c b)
    (hac : 0 < turn a c q) (hcb : 0 < turn c b q) :
    q ∈ sector ![a, c, b] := by
  have hab : 0 < turn a b q := by
    by_contra h
    apply hq
    apply weaklyInsideTriangle_mem_triangleHull htri
    refine ⟨hac.le, hcb.le, ?_⟩
    rw [turn_swap_first]
    exact neg_nonneg.mpr (le_of_not_gt h)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- The determinant identity for three vectors with a common origin.
This is used below to propagate supporting inequalities across a gap
between adjacent sectors. -/
theorem turn_origin_relation (o a b c q : Point) :
    turn o a b * turn o c q + turn o b c * turn o a q +
      turn o c a * turn o b q = 0 := by
  unfold turn
  ring

/-- In the two-sector nonconvex case, the four vertices of the replacement
chain are strictly clockwise. -/
theorem two_sector_chain_clockwise {a c b e f : Point}
    (hc : StrictlyInsideTriangle a e b c)
    (he : StrictlyInsideTriangle b c f e) :
    ∀ i j k : Fin 4, i < j → j < k →
      turn (![a, c, e, f] i) (![a, c, e, f] j) (![a, c, e, f] k) < 0 := by
  have hace : turn a c e < 0 := by
    have h := hc.1
    rw [turn_swap_last a c e] at h
    linarith
  have hcef : turn c e f < 0 := by
    have h := he.2.1
    rw [turn_swap_last] at h
    linarith
  have hacf : turn a c f < 0 := by
    by_contra h
    have hnonneg : ∀ p ∈ ({b, c, f} : Set Point), 0 ≤ turn a c p := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · have h := hc.2.2
        convert h.le using 1 <;> unfold turn <;> ring
      · simp
      · exact le_of_not_gt h
    exact hace.not_ge (turn_nonneg_of_mem_convexHull hnonneg
      (strictlyInsideTriangle_mem_triangleHull he))
  have haef : turn a e f < 0 := by
    by_contra h
    have hnonneg : ∀ p ∈ ({a, e, b} : Set Point), 0 ≤ turn e f p := by
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · convert le_of_not_gt h using 1 <;> unfold turn <;> ring
      · simp
      · have h := he.2.2
        convert h.le using 1 <;> unfold turn <;> ring
    have hce := turn_nonneg_of_mem_convexHull hnonneg
      (strictlyInsideTriangle_mem_triangleHull hc)
    have hce' : 0 ≤ turn c e f := by convert hce using 1 <;> unfold turn <;> ring
    exact hcef.not_ge hce'
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- The two-sector replacement in the nonconvex endpoint case of Valtr's
run argument. A point outside the inner polygon and both sectors is on
the inner side of every edge of the replacement chain `a,c,e,f`.
Only exclusion from three triangles is needed, so the result also applies
when those triangles lie in a larger inner convex hull. -/
theorem two_sector_chain_support {a c b e f q : Point}
    (hc : StrictlyInsideTriangle a e b c)
    (he : StrictlyInsideTriangle b c f e)
    (hq₁ : q ∉ triangleHull a c b)
    (hq₂ : q ∉ triangleHull b e f)
    (hqgap : q ∉ triangleHull c e b)
    (hs₁ : q ∉ sector ![a, c, b])
    (hs₂ : q ∉ sector ![b, e, f]) :
    turn a c q ≤ 0 ∧ turn c e q ≤ 0 ∧ turn e f q ≤ 0 := by
  have hC : 0 < turn c a e := by convert hc.1 using 1 <;> unfold turn <;> ring
  have hA : 0 < turn c e b := by convert hc.2.1 using 1 <;> unfold turn <;> ring
  have hB : 0 < turn c b a := by convert hc.2.2 using 1 <;> unfold turn <;> ring
  have hU : 0 < turn e b c := by convert he.1 using 1 <;> unfold turn <;> ring
  have hV : 0 < turn e c f := by convert he.2.1 using 1 <;> unfold turn <;> ring
  have hW : 0 < turn e f b := by convert he.2.2 using 1 <;> unfold turn <;> ring
  have htri₁ : 0 < turn a c b := by convert hB using 1 <;> unfold turn <;> ring
  have htri₂ : 0 < turn b e f := by convert hW using 1 <;> unfold turn <;> ring
  have hrel₁ : turn c a e * turn c b q =
      turn c e b * turn a c q - turn c b a * turn c e q := by
    have h := turn_origin_relation c a e b q
    rw [turn_swap_first a c q] at h
    linarith
  have hrel₂ : turn e c f * turn b e q =
      turn e b c * turn e f q - turn e f b * turn c e q := by
    have h := turn_origin_relation e b c f q
    rw [turn_swap_first b e q, turn_swap_first c e q] at h
    linarith
  have hm : turn c e q ≤ 0 := by
    by_contra h
    have hm : 0 < turn c e q := lt_of_not_ge h
    have hsplit : 0 < turn c b q ∨ 0 < turn b e q := by
      by_contra hh
      push Not at hh
      apply hqgap
      apply weaklyInsideTriangle_mem_triangleHull hA
      refine ⟨hm.le, ?_, ?_⟩
      · rw [turn_swap_first]
        exact neg_nonneg.mpr hh.2
      · rw [turn_swap_first]
        exact neg_nonneg.mpr hh.1
    rcases hsplit with hy | hz
    · have hx : 0 < turn a c q := by
        by_contra hx
        have hx := le_of_not_gt hx
        nlinarith [mul_pos hC hy, mul_pos hB hm, mul_nonpos_of_nonneg_of_nonpos hA.le hx]
      exact hs₁ (mem_sector_of_two_sides htri₁ hq₁ hx hy)
    · have hw : 0 < turn e f q := by
        by_contra hw
        have hw := le_of_not_gt hw
        nlinarith [mul_pos hV hz, mul_pos hW hm, mul_nonpos_of_nonneg_of_nonpos hU.le hw]
      exact hs₂ (mem_sector_of_two_sides htri₂ hq₂ hz hw)
  refine ⟨?_, hm, ?_⟩
  · by_contra hx
    have hx := lt_of_not_ge hx
    have hy : 0 < turn c b q := by
      by_contra hy
      have hy := le_of_not_gt hy
      nlinarith [mul_pos hA hx, mul_nonpos_of_nonneg_of_nonpos hB.le hm,
        mul_nonpos_of_nonneg_of_nonpos hC.le hy]
    exact hs₁ (mem_sector_of_two_sides htri₁ hq₁ hx hy)
  · by_contra hw
    have hw := lt_of_not_ge hw
    have hz : 0 < turn b e q := by
      by_contra hz
      have hz := le_of_not_gt hz
      nlinarith [mul_pos hU hw, mul_nonpos_of_nonneg_of_nonpos hW.le hm,
        mul_nonpos_of_nonneg_of_nonpos hV.le hz]
    exact hs₂ (mem_sector_of_two_sides htri₂ hq₂ hz hw)

end Lax56Proofs.ValtrSectors
