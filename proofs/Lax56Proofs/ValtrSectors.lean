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

end Lax56Proofs.ValtrSectors
