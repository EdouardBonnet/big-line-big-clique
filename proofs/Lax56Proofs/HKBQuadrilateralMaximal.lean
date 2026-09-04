import Lax56Proofs.HKBQuadrilateralPattern
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
Maximality of the standard nine-point quadrilateral pattern (Lemma 6.6).
-/

namespace Lax56Proofs.HKBQuadrilateralMaximal

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBQuadrilateral
open Lax56Proofs.HKBQuadrilateralPattern
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- Exact determinant scaling when `z` lies between `a` and `b`. -/
theorem endpointTurns_of_between
    {a b z p : Point} (hz : z ∈ openSegment ℝ a b) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      turn z a p = -t * turn a b p ∧
      turn z b p = (1 - t) * turn a b p := by
  rw [openSegment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨t, ht.1, ht.2, ?_, ?_⟩
  · simp [AffineMap.lineMap_apply, turn]
    ring
  · simp [AffineMap.lineMap_apply, turn]
    ring

theorem endpointTurn_right_neg_of_left_pos
    {a b z p : Point} (hz : z ∈ openSegment ℝ a b)
    (hpos : 0 < turn z a p) :
    turn z b p < 0 := by
  obtain ⟨t, ht, ht1, ha, hb⟩ := endpointTurns_of_between hz
  nlinarith

theorem endpointTurn_right_pos_of_left_neg
    {a b z p : Point} (hz : z ∈ openSegment ℝ a b)
    (hneg : turn z a p < 0) :
    0 < turn z b p := by
  obtain ⟨t, ht, ht1, ha, hb⟩ := endpointTurns_of_between hz
  nlinarith

/-- Moving strictly from a point toward a point of a compact convex set
strictly decreases the distance to that set, as long as the starting point
is outside. -/
theorem infDist_lt_of_mem_openSegment_to_compactConvex
    {Q : Set Point} (hcompact : IsCompact Q) (hconvex : Convex ℝ Q)
    (hne : Q.Nonempty) {p a x : Point}
    (hpOut : p ∉ Q) (ha : a ∈ Q)
    (hx : x ∈ openSegment ℝ p a) :
    Metric.infDist x Q < Metric.infDist p Q := by
  obtain ⟨r, hrQ, hnearest⟩ := hcompact.exists_infDist_eq_dist hne p
  rw [openSegment_eq_image_lineMap] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  let r' : Point := AffineMap.lineMap r a t
  have hr'Q : r' ∈ Q :=
    hconvex.lineMap_mem hrQ ha ⟨ht.1.le, ht.2.le⟩
  have hsub :
      AffineMap.lineMap p a t - AffineMap.lineMap r a t =
        (1 - t) • (p - r) := by
    apply Prod.ext <;> simp [AffineMap.lineMap_apply] <;> ring
  have hdist :
      dist (AffineMap.lineMap p a t) r' = (1 - t) * dist p r := by
    calc
      dist (AffineMap.lineMap p a t) r' =
          ‖AffineMap.lineMap p a t - AffineMap.lineMap r a t‖ := by
            rw [dist_eq_norm, show r' = AffineMap.lineMap r a t from rfl]
      _ = ‖(1 - t) • (p - r)‖ := congrArg norm hsub
      _ = (1 - t) * ‖p - r‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht.2)]
      _ = (1 - t) * dist p r := by rw [dist_eq_norm]
  have hpr : 0 < dist p r := dist_pos.mpr fun h ↦ hpOut (h ▸ hrQ)
  calc
    Metric.infDist (AffineMap.lineMap p a t) Q ≤
        dist (AffineMap.lineMap p a t) r' :=
      Metric.infDist_le_dist_of_mem hr'Q
    _ = (1 - t) * dist p r := hdist
    _ < dist p r := by
      have hprod : 0 < t * dist p r := mul_pos ht.1 hpr
      nlinarith
    _ = Metric.infDist p Q := hnearest.symm

/-- A finite nonempty set of points outside `Q` has a point minimizing its
distance to `Q`. -/
theorem exists_minimal_exterior_point
    {B : Finset Point} {Q : Set Point}
    (hout : ∃ p : B, (p : Point) ∉ Q) :
    ∃ p : B, (p : Point) ∉ Q ∧
      ∀ x : B, (x : Point) ∉ Q →
        Metric.infDist (p : Point) Q ≤ Metric.infDist (x : Point) Q := by
  classical
  let E : Finset B := Finset.univ.filter fun p ↦ (p : Point) ∉ Q
  have hE : E.Nonempty := by
    obtain ⟨p, hp⟩ := hout
    exact ⟨p, by simp [E, hp]⟩
  obtain ⟨p, hpE, hpmin⟩ := E.exists_min_image
    (fun p ↦ Metric.infDist (p : Point) Q) hE
  refine ⟨p, ?_, ?_⟩
  · simpa [E] using hpE
  · intro x hx
    exact hpmin x (by simp [E, hx])

/-- Every blocker on a segment from a nearest exterior point to the
quadrilateral already lies in the quadrilateral. -/
theorem blocker_mem_of_minimal_exterior
    {B : Finset Point} {Q : Set Point}
    (hcompact : IsCompact Q) (hconvex : Convex ℝ Q) (hne : Q.Nonempty)
    {p : B} (hpOut : (p : Point) ∉ Q)
    (hpmin : ∀ x : B, (x : Point) ∉ Q →
      Metric.infDist (p : Point) Q ≤ Metric.infDist (x : Point) Q)
    {a : Point} (ha : a ∈ Q) {x : B}
    (hx : (x : Point) ∈ openSegment ℝ (p : Point) a) :
    (x : Point) ∈ Q := by
  by_contra hxOut
  have hlt := infDist_lt_of_mem_openSegment_to_compactConvex
    hcompact hconvex hne hpOut ha hx
  exact (not_lt_of_ge (hpmin x hxOut)) hlt

private theorem fin4_succ_ne (i : Fin 4) : i + 1 ≠ i := by
  fin_cases i <;> decide

private theorem fin4_add_two_ne (i : Fin 4) : i + 2 ≠ i := by
  fin_cases i <;> decide

private theorem fin4_eq_offset_cases (i j : Fin 4) :
    j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by
  fin_cases i <;> fin_cases j <;> simp <;> decide

/-- The center of a standard pattern lies on either labelled diagonal. -/
theorem pattern_center_between_vertices
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4) :
    (P.z : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 2) : Point) := by
  fin_cases i
  · simpa using P.diagonal₀₂
  · simpa using P.diagonal₁₃
  · change (P.z : Point) ∈
      openSegment ℝ (q 2 : Point) (q 0 : Point)
    simpa only [openSegment_symm] using P.diagonal₀₂
  · change (P.z : Point) ∈
      openSegment ℝ (q 3 : Point) (q 1 : Point)
    simpa only [openSegment_symm] using P.diagonal₁₃

/-- Every point of `B` lying in the quadrilateral is one of its four
vertices or one of the five points in the standard pattern. -/
theorem standardPattern_cases_of_mem_hull
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (P : StandardQuadrilateralPattern B colour q)
    {r : Point} (hrB : r ∈ B)
    (hrQ : r ∈ quadrilateralHull fun i ↦ (q i : Point)) :
    (∃ i, r = (q i : Point)) ∨ r = (P.z : Point) ∨
      ∃ i, r = (P.y i : Point) := by
  classical
  by_cases hrq : r ∈ Set.range (fun i ↦ (q i : Point))
  · rcases hrq with ⟨i, hri⟩
    exact Or.inl ⟨i, hri.symm⟩
  · have hrR : r ∈ quadInteriorPoints B (fun i ↦ (q i : Point)) :=
      mem_quadInteriorPoints.mpr ⟨hrB, hrQ, hrq⟩
    rw [P.cover] at hrR
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
      true_and] at hrR
    rcases hrR with hrz | ⟨i, hri⟩
    · exact Or.inr (Or.inl hrz)
    · exact Or.inr (Or.inr ⟨i, hri.symm⟩)

/-- The two positive coordinate rays of each sector have positive
orientation. -/
theorem center_vertex_next_turn_pos
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4) :
    0 < turn (P.z : Point) (q i : Point) (q (i + 1) : Point) := by
  obtain ⟨t, ht, ht1, ha, -⟩ := endpointTurns_of_between
    (pattern_center_between_vertices P i)
      (p := (q (i + 1) : Point))
  have hquad :
      0 < turn (q i : Point) (q (i + 1) : Point)
        (q (i + 2) : Point) := by
    apply hq.2
    · fin_cases i <;> decide
    · fin_cases i <;> decide
  have hswap :
      turn (q i : Point) (q (i + 2) : Point) (q (i + 1) : Point) =
        -turn (q i : Point) (q (i + 1) : Point) (q (i + 2) : Point) :=
    turn_swap_last _ _ _
  rw [hswap] at ha
  nlinarith [mul_pos ht hquad]

theorem center_axis_opposite_turn_eq_zero
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4) :
    turn (P.z : Point) (q i : Point) (q (i + 2) : Point) = 0 := by
  have hz := turn_eq_zero_of_mem_openSegment
    (pattern_center_between_vertices P i)
  calc
    turn (P.z : Point) (q i : Point) (q (i + 2) : Point) =
        turn (q i : Point) (q (i + 2) : Point) (P.z : Point) := by
          exact (turn_rotate _ _ _).symm
    _ = -turn (q i : Point) (P.z : Point) (q (i + 2) : Point) :=
      turn_swap_last _ _ _
    _ = 0 := by rw [hz, neg_zero]

theorem center_vertex_prev_turn_neg
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4) :
    turn (P.z : Point) (q i : Point) (q (i + 3) : Point) < 0 := by
  have hnext := center_vertex_next_turn_pos hq P i
  have hleft :
      turn (P.z : Point) (q (i + 1) : Point) (q i : Point) < 0 := by
    rw [turn_swap_last]
    linarith
  have hright := endpointTurn_right_pos_of_left_neg
    (pattern_center_between_vertices P (i + 1)) hleft
  rw [turn_swap_last] at hright
  have hadd : (i + 1) + 2 = i + 3 := by fin_cases i <;> decide
  rw [hadd] at hright
  linarith

/-- Relative to the directed axis from the center through vertex `i`, the
next two side points lie on the positive side. -/
theorem center_axis_side_pos
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4) :
    0 < turn (P.z : Point) (q i : Point) (P.y i : Point) ∧
    0 < turn (P.z : Point) (q i : Point) (P.y (i + 1) : Point) := by
  have hnext := center_vertex_next_turn_pos hq P i
  have hopp := center_axis_opposite_turn_eq_zero P i
  constructor
  · obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
      (a := (P.z : Point)) (b := (q i : Point)) (P.side i)
    simp only [turn_self_left, turn_self_right, zero_mul, add_zero] at heq
    nlinarith [mul_pos ht hnext]
  · obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
      (a := (P.z : Point)) (b := (q i : Point)) (P.side (i + 1))
    have hadd : (i + 1) + 1 = i + 2 := by fin_cases i <;> decide
    rw [hadd] at heq
    rw [heq, hopp]
    nlinarith [mul_pos (sub_pos.mpr ht1) hnext]

/-- The two side points preceding the axis lie on its negative side. -/
theorem center_axis_side_neg
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4) :
    turn (P.z : Point) (q i : Point) (P.y (i + 2) : Point) < 0 ∧
    turn (P.z : Point) (q i : Point) (P.y (i + 3) : Point) < 0 := by
  have hnext := center_vertex_next_turn_pos hq P i
  have hprev := center_vertex_prev_turn_neg hq P i
  have hopp := center_axis_opposite_turn_eq_zero P i
  constructor
  · obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
      (a := (P.z : Point)) (b := (q i : Point)) (P.side (i + 2))
    have : turn (P.z : Point) (q i : Point) (P.y (i + 2) : Point) =
        (1 - t) * turn (P.z : Point) (q i : Point) (q (i + 2) : Point) +
          t * turn (P.z : Point) (q i : Point) (q (i + 3) : Point) := by
      simpa only [add_assoc] using heq
    rw [this, hopp]
    nlinarith [mul_neg_of_pos_of_neg ht hprev]
  · obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
      (a := (P.z : Point)) (b := (q i : Point)) (P.side (i + 3))
    have hadd : (i + 3) + 1 = i := by fin_cases i <;> decide
    rw [hadd] at heq
    have : turn (P.z : Point) (q i : Point) (P.y (i + 3) : Point) =
        (1 - t) * turn (P.z : Point) (q i : Point) (q (i + 3) : Point) +
          t * turn (P.z : Point) (q i : Point) (q i : Point) := by
      exact heq
    rw [this, turn_self_right, mul_zero, add_zero]
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hprev]

/-- In a standard pattern, the only points with positive coordinate
relative to the axis `z q_i` are the next vertex and the two intervening
side points. -/
theorem standardPattern_cases_of_axis_pos
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {r : Point} (hrB : r ∈ B)
    (hrQ : r ∈ quadrilateralHull fun i ↦ (q i : Point))
    (i : Fin 4) (hrpos : 0 < turn (P.z : Point) (q i : Point) r) :
    r = (q (i + 1) : Point) ∨ r = (P.y i : Point) ∨
      r = (P.y (i + 1) : Point) := by
  have hnext := center_vertex_next_turn_pos hq P i
  have hopp := center_axis_opposite_turn_eq_zero P i
  have hprev := center_vertex_prev_turn_neg hq P i
  have hypos := center_axis_side_pos hq P i
  have hyneg := center_axis_side_neg hq P i
  rcases standardPattern_cases_of_mem_hull P hrB hrQ with
      ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩
  · rcases fin4_eq_offset_cases i j with rfl | rfl | rfl | rfl
    · simp at hrpos
    · exact Or.inl rfl
    · linarith
    · linarith
  · simp at hrpos
  · rcases fin4_eq_offset_cases i j with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · linarith
    · linarith

/-- The corresponding classification on the negative side of an axis. -/
theorem standardPattern_cases_of_axis_neg
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {r : Point} (hrB : r ∈ B)
    (hrQ : r ∈ quadrilateralHull fun i ↦ (q i : Point))
    (i : Fin 4) (hrneg : turn (P.z : Point) (q i : Point) r < 0) :
    r = (q (i + 3) : Point) ∨ r = (P.y (i + 2) : Point) ∨
      r = (P.y (i + 3) : Point) := by
  have hnext := center_vertex_next_turn_pos hq P i
  have hopp := center_axis_opposite_turn_eq_zero P i
  have hprev := center_vertex_prev_turn_neg hq P i
  have hypos := center_axis_side_pos hq P i
  have hyneg := center_axis_side_neg hq P i
  rcases standardPattern_cases_of_mem_hull P hrB hrQ with
      ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩
  · rcases fin4_eq_offset_cases i j with rfl | rfl | rfl | rfl
    · simp at hrneg
    · linarith
    · linarith
    · exact Or.inl rfl
  · simp at hrneg
  · rcases fin4_eq_offset_cases i j with rfl | rfl | rfl | rfl
    · linarith
    · linarith
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- An exterior point of `B` cannot lie on either diagonal axis of the
standard pattern: that would put it together with the two diagonal
endpoints and the center on one line. -/
theorem exterior_axis_turn_ne_zero
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point)) (i : Fin 4) :
    turn (P.z : Point) (q i : Point) (p : Point) ≠ 0 := by
  let Q := quadrilateralHull fun i ↦ (q i : Point)
  have hzseg := pattern_center_between_vertices P i
  have hqio : (q i : Point) ≠ (q (i + 2) : Point) :=
    hq.1.ne (by fin_cases i <;> decide)
  have hzi : (P.z : Point) ≠ (q i : Point) := by
    intro h
    have : (q i : Point) ∈
        openSegment ℝ (q i : Point) (q (i + 2) : Point) := h ▸ hzseg
    exact hqio ((left_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hzo : (P.z : Point) ≠ (q (i + 2) : Point) := by
    intro h
    have : (q (i + 2) : Point) ∈
        openSegment ℝ (q i : Point) (q (i + 2) : Point) := h ▸ hzseg
    exact hqio ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hqiQ : (q i : Point) ∈ Q :=
    subset_convexHull ℝ (Set.range fun i ↦ (q i : Point))
      (Set.mem_range_self i)
  have hqoQ : (q (i + 2) : Point) ∈ Q :=
    subset_convexHull ℝ (Set.range fun i ↦ (q i : Point))
      (Set.mem_range_self (i + 2))
  have hzQ : (P.z : Point) ∈ Q :=
    (segment_subset_convexHull (Set.mem_range_self i)
      (Set.mem_range_self (i + 2)))
      (openSegment_subset_segment ℝ _ _ hzseg)
  have hpz : (p : Point) ≠ (P.z : Point) := fun h ↦ hpOut (h ▸ hzQ)
  have hpi : (p : Point) ≠ (q i : Point) := fun h ↦ hpOut (h ▸ hqiQ)
  have hpo : (p : Point) ≠ (q (i + 2) : Point) := fun h ↦ hpOut (h ▸ hqoQ)
  have hno := noTwoZero_of_noFour hfour P.z.property (q i).property
    (q (i + 2)).property p.property hzi hzo hpz.symm
      hqio hpi.symm hpo.symm
  intro hpzero
  exact hno.1 ⟨center_axis_opposite_turn_eq_zero P i, hpzero⟩

/-- The two diagonal axes divide the exterior into four open side sectors. -/
theorem exists_side_sector_of_exterior
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point)) :
    ∃ i : Fin 4,
      0 < turn (P.z : Point) (q i : Point) (p : Point) ∧
      0 < turn (P.z : Point) (p : Point) (q (i + 1) : Point) := by
  have hA0 := exterior_axis_turn_ne_zero hfour hq P hpOut 0
  have hB0 := exterior_axis_turn_ne_zero hfour hq P hpOut 1
  rcases lt_or_gt_of_ne hA0.symm with hA | hA <;>
    rcases lt_or_gt_of_ne hB0.symm with hB | hB
  · refine ⟨1, hB, ?_⟩
    have h := endpointTurn_right_neg_of_left_pos P.diagonal₀₂ hA
    rw [turn_swap_last]
    simpa using h
  · refine ⟨0, hA, ?_⟩
    have hi : (0 : Fin 4) + 1 = 1 := by decide
    rw [hi]
    rw [turn_swap_last]
    linarith
  · refine ⟨2, ?_, ?_⟩
    · have h := endpointTurn_right_pos_of_left_neg P.diagonal₀₂ hA
      simpa using h
    · have h := endpointTurn_right_neg_of_left_pos P.diagonal₁₃ hB
      rw [turn_swap_last]
      simpa using h
  · refine ⟨3, ?_, ?_⟩
    · have h := endpointTurn_right_pos_of_left_neg P.diagonal₁₃ hB
      simpa using h
    · have hi : (3 : Fin 4) + 1 = 0 := by decide
      rw [hi, turn_swap_last]
      linarith

/-- A point in the sector beyond side `i` is strictly outside the supporting
line of that side. -/
theorem side_turn_neg_of_mem_sector_exterior
    {B : Finset Point} {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p : Point} (i : Fin 4)
    (hleft : 0 < turn (P.z : Point) (q i : Point) p)
    (hright : 0 < turn (P.z : Point) p (q (i + 1) : Point))
    (hpOut : p ∉ quadrilateralHull fun i ↦ (q i : Point)) :
    turn (q i : Point) (q (i + 1) : Point) p < 0 := by
  by_contra hnot
  push Not at hnot
  have hzQ : (P.z : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    (segment_subset_convexHull (Set.mem_range_self i)
      (Set.mem_range_self (i + 2)))
      (openSegment_subset_segment ℝ _ _
        (pattern_center_between_vertices P i))
  have htri : triangleHull (P.z : Point) (q i : Point)
      (q (i + 1) : Point) ⊆
      quadrilateralHull fun i ↦ (q i : Point) := by
    apply convexHull_min
    · intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl | rfl
      · exact hzQ
      · exact subset_convexHull ℝ
          (Set.range fun i ↦ (q i : Point)) (Set.mem_range_self i)
      · exact subset_convexHull ℝ
          (Set.range fun i ↦ (q i : Point)) (Set.mem_range_self (i + 1))
    · exact convex_convexHull ℝ _
  apply hpOut
  apply htri
  apply weaklyInsideTriangle_mem_triangleHull
  · exact center_vertex_next_turn_pos hq P i
  · refine ⟨hleft.le, hnot, ?_⟩
    rw [← turn_rotate (q (i + 1) : Point) (P.z : Point) p]
    exact hright.le

/-- A nearest exterior point sees every point of the supporting line of the
side beyond which it lies. -/
theorem visible_minimal_exterior_to_sideLine
    {B : Finset Point} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    {p a : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point))
    (hpmin : ∀ x : B, (x : Point) ∉
      quadrilateralHull (fun i ↦ (q i : Point)) →
      Metric.infDist (p : Point)
        (quadrilateralHull fun i ↦ (q i : Point)) ≤
      Metric.infDist (x : Point)
        (quadrilateralHull fun i ↦ (q i : Point)))
    (i : Fin 4)
    (hpneg : turn (q i : Point) (q (i + 1) : Point) (p : Point) < 0)
    (haQ : (a : Point) ∈ quadrilateralHull fun i ↦ (q i : Point))
    (hazero : turn (q i : Point) (q (i + 1) : Point) (a : Point) = 0) :
    Visible B (p : Point) (a : Point) := by
  let Q := quadrilateralHull fun i ↦ (q i : Point)
  have hcompact : IsCompact Q :=
    (Set.finite_range fun i ↦ (q i : Point)).isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty :=
    ⟨(q 0 : Point), subset_convexHull ℝ
      (Set.range fun i ↦ (q i : Point)) (Set.mem_range_self 0)⟩
  refine ⟨fun h ↦ hpOut (h ▸ haQ), ?_⟩
  intro r hrB hrseg
  let rB : B := ⟨r, hrB⟩
  have hrQ : r ∈ Q := blocker_mem_of_minimal_exterior
    hcompact hconvex hne hpOut hpmin haQ (x := rB) hrseg
  have hrnonneg := quad_edgeTurn_nonneg_of_mem_convexHull hq hrQ i
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
    (a := (q i : Point)) (b := (q (i + 1) : Point)) hrseg
  rw [hazero] at heq
  have hmul : (1 - t) *
      turn (q i : Point) (q (i + 1) : Point) (p : Point) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hpneg
  linarith

/-- A side endpoint cannot occur between an exterior point and the
side-interior point: the side's two endpoints would then give four
collinear points. -/
theorem sideEndpoint_not_between_exterior_and_sidePoint
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point))
    (j e : Fin 4) (he : e = j ∨ e = j + 1) :
    (q e : Point) ∉ openSegment ℝ (p : Point) (P.y j : Point) := by
  have hqne : (q j : Point) ≠ (q (j + 1) : Point) :=
    hq.1.ne (fin4_succ_ne j).symm
  have hyj : (P.y j : Point) ≠ (q j : Point) := by
    intro h
    have : (q j : Point) ∈
        openSegment ℝ (q j : Point) (q (j + 1) : Point) := h ▸ P.side j
    exact hqne ((left_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hyjs : (P.y j : Point) ≠ (q (j + 1) : Point) := by
    intro h
    have : (q (j + 1) : Point) ∈
        openSegment ℝ (q j : Point) (q (j + 1) : Point) := h ▸ P.side j
    exact hqne ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hqjQ : (q j : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    subset_convexHull ℝ (Set.range fun i ↦ (q i : Point))
      (Set.mem_range_self j)
  have hqjsQ : (q (j + 1) : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    subset_convexHull ℝ (Set.range fun i ↦ (q i : Point))
      (Set.mem_range_self (j + 1))
  have hyQ : (P.y j : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    (segment_subset_convexHull (Set.mem_range_self j)
      (Set.mem_range_self (j + 1)))
      (openSegment_subset_segment ℝ _ _ (P.side j))
  have hpqj : (p : Point) ≠ (q j : Point) := fun h ↦ hpOut (h ▸ hqjQ)
  have hpqjs : (p : Point) ≠ (q (j + 1) : Point) :=
    fun h ↦ hpOut (h ▸ hqjsQ)
  have hpy : (p : Point) ≠ (P.y j : Point) := fun h ↦ hpOut (h ▸ hyQ)
  have hno := noTwoZero_of_noFour hfour (q j).property
    (q (j + 1)).property (P.y j).property p.property
      hqne hyj.symm hpqj.symm hyjs.symm hpqjs.symm hpy.symm
  have hsidezero :
      turn (q j : Point) (q (j + 1) : Point) (P.y j : Point) = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment (P.side j), neg_zero]
  intro hbetween
  rcases he with he | he
  · have hz := turn_eq_zero_of_mem_openSegment hbetween
    subst e
    have hcol : turn (q j : Point) (P.y j : Point) (p : Point) = 0 := by
      exact (turn_rotate (p : Point) (q j : Point) (P.y j : Point)).trans hz
    exact hno.2.1 ⟨hsidezero, hcol⟩
  · have hz := turn_eq_zero_of_mem_openSegment hbetween
    subst e
    have hcol : turn (q (j + 1) : Point) (P.y j : Point) (p : Point) = 0 := by
      exact (turn_rotate (p : Point) (q (j + 1) : Point) (P.y j : Point)).trans hz
    exact hno.2.2.1 ⟨hsidezero, hcol⟩

/-- If `r` lies between `p,z` and `z` lies between `r,s`, then the four
distinct ambient points are collinear, contradicting the standing
hypothesis. -/
theorem not_nested_openSegments
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {p r z s : B} (hps : p ≠ s) (hpz : p ≠ z) (hrs : r ≠ s)
    (hr : (r : Point) ∈ openSegment ℝ (p : Point) (z : Point))
    (hz : (z : Point) ∈ openSegment ℝ (r : Point) (s : Point)) : False := by
  have hpr : p ≠ r := by
    intro h
    apply hpz
    apply Subtype.ext
    have h' : (p : Point) = (r : Point) := congrArg Subtype.val h
    have : (p : Point) ∈ openSegment ℝ (p : Point) (z : Point) :=
      h' ▸ hr
    exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp this
  have hrz : r ≠ z := by
    intro h
    apply hpz
    apply Subtype.ext
    have h' : (r : Point) = (z : Point) := congrArg Subtype.val h
    have : (z : Point) ∈ openSegment ℝ (p : Point) (z : Point) :=
      h' ▸ hr
    exact (right_mem_openSegment_iff (𝕜 := ℝ)).mp this
  have hzs : z ≠ s := by
    intro h
    apply hrs
    apply Subtype.ext
    have h' : (z : Point) = (s : Point) := congrArg Subtype.val h
    have : (s : Point) ∈ openSegment ℝ (r : Point) (s : Point) :=
      h' ▸ hz
    exact (right_mem_openSegment_iff (𝕜 := ℝ)).mp this
  have hno := noTwoZero_of_noFour hfour p.property r.property z.property s.property
    (Subtype.val_injective.ne hpr) (Subtype.val_injective.ne hpz)
    (Subtype.val_injective.ne hps) (Subtype.val_injective.ne hrz)
    (Subtype.val_injective.ne hrs) (Subtype.val_injective.ne hzs)
  exact hno.2.2.1 ⟨turn_eq_zero_of_mem_openSegment hr,
    turn_eq_zero_of_mem_openSegment hz⟩

/-- A nearest exterior point sees the center of the standard pattern. -/
theorem visible_minimal_exterior_center
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point))
    (hpmin : ∀ x : B, (x : Point) ∉
      quadrilateralHull (fun i ↦ (q i : Point)) →
      Metric.infDist (p : Point)
        (quadrilateralHull fun i ↦ (q i : Point)) ≤
      Metric.infDist (x : Point)
        (quadrilateralHull fun i ↦ (q i : Point))) :
    Visible B (p : Point) (P.z : Point) := by
  let Q := quadrilateralHull fun i ↦ (q i : Point)
  have hcompact : IsCompact Q :=
    (Set.finite_range fun i ↦ (q i : Point)).isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty :=
    ⟨(q 0 : Point), subset_convexHull ℝ
      (Set.range fun i ↦ (q i : Point)) (Set.mem_range_self 0)⟩
  have hzQ : (P.z : Point) ∈ Q :=
    (segment_subset_convexHull (Set.mem_range_self (0 : Fin 4))
      (Set.mem_range_self (2 : Fin 4)))
      (openSegment_subset_segment ℝ _ _ P.diagonal₀₂)
  have hpzPoint : (p : Point) ≠ (P.z : Point) := fun h ↦ hpOut (h ▸ hzQ)
  have hpz : p ≠ P.z := fun h ↦ hpzPoint (congrArg Subtype.val h)
  have hqinj : Function.Injective q := by
    intro i j h
    apply hq.1
    exact congrArg Subtype.val h
  have hyinj : Function.Injective P.y := by
    intro i j h
    apply P.side_injective
    exact congrArg Subtype.val h
  refine ⟨hpzPoint, ?_⟩
  intro r hrB hrseg
  let rB : B := ⟨r, hrB⟩
  have hrQ : r ∈ Q := blocker_mem_of_minimal_exterior
    hcompact hconvex hne hpOut hpmin hzQ (x := rB) hrseg
  rcases standardPattern_cases_of_mem_hull P hrB hrQ with
      ⟨j, hrj⟩ | hrz | ⟨j, hrj⟩
  · have hsQ : (q (j + 2) : Point) ∈ Q :=
      subset_convexHull ℝ (Set.range fun i ↦ (q i : Point))
        (Set.mem_range_self (j + 2))
    have hps : p ≠ q (j + 2) := by
      intro h
      exact hpOut (congrArg Subtype.val h ▸ hsQ)
    have hrs : q j ≠ q (j + 2) :=
      hqinj.ne (by fin_cases j <;> decide)
    apply not_nested_openSegments hfour hps hpz hrs
    · simpa only [hrj] using hrseg
    · exact pattern_center_between_vertices P j
  · have : (P.z : Point) ∈
        openSegment ℝ (p : Point) (P.z : Point) := hrz ▸ hrseg
    exact hpzPoint ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  · have hsQ : (P.y (j + 2) : Point) ∈ Q :=
      (segment_subset_convexHull (Set.mem_range_self (j + 2))
        (Set.mem_range_self ((j + 2) + 1)))
        (openSegment_subset_segment ℝ _ _ (P.side (j + 2)))
    have hps : p ≠ P.y (j + 2) := by
      intro h
      exact hpOut (congrArg Subtype.val h ▸ hsQ)
    have hrs : P.y j ≠ P.y (j + 2) :=
      hyinj.ne (by fin_cases j <;> decide)
    apply not_nested_openSegments hfour hps hpz hrs
    · simpa only [hrj] using hrseg
    · exact P.center_between_opposite j

/-- Any blocker from a point in side sector `i` to the next side point is
the side point `y_i`. -/
theorem next_sidePoint_blocker_eq_current
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p r : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point))
    (hpmin : ∀ x : B, (x : Point) ∉
      quadrilateralHull (fun i ↦ (q i : Point)) →
      Metric.infDist (p : Point)
        (quadrilateralHull fun i ↦ (q i : Point)) ≤
      Metric.infDist (x : Point)
        (quadrilateralHull fun i ↦ (q i : Point)))
    (i : Fin 4)
    (hleft : 0 < turn (P.z : Point) (q i : Point) (p : Point))
    (hr : (r : Point) ∈
      openSegment ℝ (p : Point) (P.y (i + 1) : Point)) :
    (r : Point) = (P.y i : Point) := by
  let Q := quadrilateralHull fun i ↦ (q i : Point)
  have hcompact : IsCompact Q :=
    (Set.finite_range fun i ↦ (q i : Point)).isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty :=
    ⟨(q 0 : Point), subset_convexHull ℝ
      (Set.range fun i ↦ (q i : Point)) (Set.mem_range_self 0)⟩
  have hyQ : (P.y (i + 1) : Point) ∈ Q :=
    (segment_subset_convexHull (Set.mem_range_self (i + 1))
      (Set.mem_range_self ((i + 1) + 1)))
      (openSegment_subset_segment ℝ _ _ (P.side (i + 1)))
  have hrQ : (r : Point) ∈ Q := blocker_mem_of_minimal_exterior
    hcompact hconvex hne hpOut hpmin hyQ hr
  have hypos := (center_axis_side_pos hq P i).2
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
    (a := (P.z : Point)) (b := (q i : Point)) hr
  have hrpos : 0 < turn (P.z : Point) (q i : Point) (r : Point) := by
    rw [heq]
    exact add_pos (mul_pos (sub_pos.mpr ht1) hleft) (mul_pos ht hypos)
  rcases standardPattern_cases_of_axis_pos hq P r.property hrQ i hrpos with
      hrq | hry | hry
  · exact (sideEndpoint_not_between_exterior_and_sidePoint
      hfour hq P hpOut (i + 1) (i + 1) (Or.inl rfl)) (hrq ▸ hr) |>.elim
  · exact hry
  · have hpne : (p : Point) ≠ (P.y (i + 1) : Point) :=
      fun h ↦ hpOut (h ▸ hyQ)
    have : (P.y (i + 1) : Point) ∈
        openSegment ℝ (p : Point) (P.y (i + 1) : Point) := hry ▸ hr
    exact (hpne ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)).elim

/-- Symmetrically, any blocker to the preceding side point is also `y_i`. -/
theorem prev_sidePoint_blocker_eq_current
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p r : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point))
    (hpmin : ∀ x : B, (x : Point) ∉
      quadrilateralHull (fun i ↦ (q i : Point)) →
      Metric.infDist (p : Point)
        (quadrilateralHull fun i ↦ (q i : Point)) ≤
      Metric.infDist (x : Point)
        (quadrilateralHull fun i ↦ (q i : Point)))
    (i : Fin 4)
    (hright : 0 < turn (P.z : Point) (p : Point) (q (i + 1) : Point))
    (hr : (r : Point) ∈
      openSegment ℝ (p : Point) (P.y (i + 3) : Point)) :
    (r : Point) = (P.y i : Point) := by
  let Q := quadrilateralHull fun i ↦ (q i : Point)
  have hcompact : IsCompact Q :=
    (Set.finite_range fun i ↦ (q i : Point)).isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty :=
    ⟨(q 0 : Point), subset_convexHull ℝ
      (Set.range fun i ↦ (q i : Point)) (Set.mem_range_self 0)⟩
  have hyQ : (P.y (i + 3) : Point) ∈ Q :=
    (segment_subset_convexHull (Set.mem_range_self (i + 3))
      (Set.mem_range_self ((i + 3) + 1)))
      (openSegment_subset_segment ℝ _ _ (P.side (i + 3)))
  have hrQ : (r : Point) ∈ Q := blocker_mem_of_minimal_exterior
    hcompact hconvex hne hpOut hpmin hyQ hr
  have hpneg : turn (P.z : Point) (q (i + 1) : Point) (p : Point) < 0 := by
    rw [turn_swap_last] at hright
    linarith
  have hyneg0 := (center_axis_side_neg hq P (i + 1)).1
  have hadd : (i + 1) + 2 = i + 3 := by fin_cases i <;> decide
  rw [hadd] at hyneg0
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment
    (a := (P.z : Point)) (b := (q (i + 1) : Point)) hr
  have hrneg : turn (P.z : Point) (q (i + 1) : Point) (r : Point) < 0 := by
    rw [heq]
    exact add_neg (mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hpneg)
      (mul_neg_of_pos_of_neg ht hyneg0)
  rcases standardPattern_cases_of_axis_neg hq P r.property hrQ (i + 1) hrneg with
      hrq | hry | hry
  · have hqidx : (i + 1) + 3 = i := by fin_cases i <;> decide
    rw [hqidx] at hrq
    exact (sideEndpoint_not_between_exterior_and_sidePoint
      hfour hq P hpOut (i + 3) i (Or.inr (by fin_cases i <;> decide)))
        (hrq ▸ hr) |>.elim
  · have hyidx : (i + 1) + 2 = i + 3 := by fin_cases i <;> decide
    rw [hyidx] at hry
    have hpne : (p : Point) ≠ (P.y (i + 3) : Point) :=
      fun h ↦ hpOut (h ▸ hyQ)
    have : (P.y (i + 3) : Point) ∈
        openSegment ℝ (p : Point) (P.y (i + 3) : Point) := hry ▸ hr
    exact (hpne ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)).elim
  · have hyidx : (i + 1) + 3 = i := by fin_cases i <;> decide
    simpa only [hyidx] using hry

/-- Of the two side points adjacent to `y_i`, at least one sees the nearest
exterior point. -/
theorem visible_next_or_prev_sidePoint
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} {q : Fin 4 → B}
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (P : StandardQuadrilateralPattern B colour q)
    {p : B} (hpOut : (p : Point) ∉
      quadrilateralHull fun i ↦ (q i : Point))
    (hpmin : ∀ x : B, (x : Point) ∉
      quadrilateralHull (fun i ↦ (q i : Point)) →
      Metric.infDist (p : Point)
        (quadrilateralHull fun i ↦ (q i : Point)) ≤
      Metric.infDist (x : Point)
        (quadrilateralHull fun i ↦ (q i : Point)))
    (i : Fin 4)
    (hleft : 0 < turn (P.z : Point) (q i : Point) (p : Point))
    (hright : 0 < turn (P.z : Point) (p : Point) (q (i + 1) : Point)) :
    Visible B (p : Point) (P.y (i + 1) : Point) ∨
      Visible B (p : Point) (P.y (i + 3) : Point) := by
  have hyNextQ : (P.y (i + 1) : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    (segment_subset_convexHull (Set.mem_range_self (i + 1))
      (Set.mem_range_self ((i + 1) + 1)))
      (openSegment_subset_segment ℝ _ _ (P.side (i + 1)))
  have hyPrevQ : (P.y (i + 3) : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    (segment_subset_convexHull (Set.mem_range_self (i + 3))
      (Set.mem_range_self ((i + 3) + 1)))
      (openSegment_subset_segment ℝ _ _ (P.side (i + 3)))
  have hpNext : (p : Point) ≠ (P.y (i + 1) : Point) :=
    fun h ↦ hpOut (h ▸ hyNextQ)
  have hpPrev : (p : Point) ≠ (P.y (i + 3) : Point) :=
    fun h ↦ hpOut (h ▸ hyPrevQ)
  by_cases hnext : Visible B (p : Point) (P.y (i + 1) : Point)
  · exact Or.inl hnext
  right
  by_contra hprev
  obtain ⟨r, hrB, hr⟩ := exists_blocker hpNext hnext
  obtain ⟨s, hsB, hs⟩ := exists_blocker hpPrev hprev
  let rB : B := ⟨r, hrB⟩
  let sB : B := ⟨s, hsB⟩
  have hrEq := next_sidePoint_blocker_eq_current
    hfour hq P hpOut hpmin i hleft (r := rB) hr
  have hsEq := prev_sidePoint_blocker_eq_current
    hfour hq P hpOut hpmin i hright (r := sB) hs
  have hpn : p ≠ P.y (i + 1) := fun h ↦ hpNext (congrArg Subtype.val h)
  have hpp : p ≠ P.y (i + 3) := fun h ↦ hpPrev (congrArg Subtype.val h)
  have hrEq' : r = (P.y i : Point) := hrEq
  have hsEq' : s = (P.y i : Point) := hsEq
  have hcommon := other_endpoint_eq_of_common_blocker hfour hpn hpp
    (z := P.y i)
    (by rw [← hrEq']; exact hr)
    (by rw [← hsEq']; exact hs)
  have hidx := P.side_injective (congrArg Subtype.val hcommon)
  have : i + 1 ≠ i + 3 := by fin_cases i <;> decide
  exact this hidx

theorem colour_ne_of_visible
    {B : Finset Point} {colour : B → Fin 4}
    (hproper : ProperBlocking B colour) {x y : B}
    (hvis : Visible B (x : Point) (y : Point)) :
    colour x ≠ colour y := by
  intro hcolour
  have hxy : x ≠ y := fun h ↦ hvis.1 (congrArg Subtype.val h)
  obtain ⟨r, hr⟩ := hproper x y hxy hcolour
  exact hvis.2 r r.property hr

private theorem fin4_exhaust_of_four_pairwise
    {a b c d x : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  omega

/-- The quadrilateral colour, `y_i`, the center, and the next side point
carry all four colours. -/
theorem standardPattern_four_colours_exhaust
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (P : StandardQuadrilateralPattern B colour q) (i : Fin 4)
    (d : Fin 4) :
    d = c ∨ d = colour (P.y i) ∨ d = colour P.z ∨
      d = colour (P.y (i + 1)) := by
  have hqinj : Function.Injective q := by
    intro j k h
    apply hq.1
    exact congrArg Subtype.val h
  have hcy (j : Fin 4) : c ≠ colour (P.y j) := by
    have hne : q j ≠ q (j + 1) := hqinj.ne (fin4_succ_ne j).symm
    have h := blocker_colour_ne hfour hproper hne
      ((hmono j).trans (hmono (j + 1)).symm) (P.side j)
    simpa only [hmono j, ne_eq] using h.symm
  have hcz : c ≠ colour P.z := by
    have hne : q 0 ≠ q 2 := hqinj.ne (by decide)
    have h := blocker_colour_ne hfour hproper hne
      ((hmono 0).trans (hmono 2).symm) P.diagonal₀₂
    simpa only [hmono 0, ne_eq] using h.symm
  have hzy (j : Fin 4) : colour P.z ≠ colour (P.y j) :=
    colour_ne_of_visible hproper
      (visible_commonDiagonal_sidePoint hfour q hq P.y P.z P.side
        P.diagonal₀₂ P.center_ne_side P.cover j)
  have hadj : colour (P.y i) ≠ colour (P.y (i + 1)) :=
    colour_ne_of_visible hproper
      (visible_adjacent_sidePoints q hq P.y P.z P.side P.diagonal₀₂
        P.diagonal₁₃ P.side_injective P.cover i)
  exact fin4_exhaust_of_four_pairwise (hcy i) hcz (hcy (i + 1))
    (hzy i).symm hadj (hzy (i + 1))

/-- Lemma 6.6: the standard nine-point quadrilateral pattern is maximal.
Every point of the ambient properly four-coloured set lies in the original
quadrilateral. -/
theorem standardQuadrilateralPattern_maximal
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (P : StandardQuadrilateralPattern B colour q) :
    ∀ p : B, (p : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) := by
  by_contra hout
  push Not at hout
  obtain ⟨p, hpOut, hpmin⟩ := exists_minimal_exterior_point
    (B := B) (Q := quadrilateralHull fun i ↦ (q i : Point)) hout
  obtain ⟨i, hleft, hright⟩ :=
    exists_side_sector_of_exterior hfour hq P hpOut
  have hpneg := side_turn_neg_of_mem_sector_exterior
    hq P i hleft hright hpOut
  have hqQ : (q i : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    subset_convexHull ℝ (Set.range fun i ↦ (q i : Point))
      (Set.mem_range_self i)
  have hyQ : (P.y i : Point) ∈
      quadrilateralHull fun i ↦ (q i : Point) :=
    (segment_subset_convexHull (Set.mem_range_self i)
      (Set.mem_range_self (i + 1)))
      (openSegment_subset_segment ℝ _ _ (P.side i))
  have hyzero :
      turn (q i : Point) (q (i + 1) : Point) (P.y i : Point) = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment (P.side i), neg_zero]
  have hvisQ : Visible B (p : Point) (q i : Point) :=
    visible_minimal_exterior_to_sideLine hq hpOut hpmin i hpneg hqQ (by simp)
  have hvisY : Visible B (p : Point) (P.y i : Point) :=
    visible_minimal_exterior_to_sideLine hq hpOut hpmin i hpneg hyQ hyzero
  have hvisZ : Visible B (p : Point) (P.z : Point) :=
    visible_minimal_exterior_center hfour hq P hpOut hpmin
  have hvisAdj := visible_next_or_prev_sidePoint
    hfour hq P hpOut hpmin i hleft hright
  rcases standardPattern_four_colours_exhaust
      hfour colour hproper c q hq hmono P i (colour p) with
      hpc | hpy | hpz | hpnext
  · exact (colour_ne_of_visible hproper hvisQ)
      (hpc.trans (hmono i).symm)
  · exact (colour_ne_of_visible hproper hvisY) hpy
  · exact (colour_ne_of_visible hproper hvisZ) hpz
  · rcases hvisAdj with hnext | hprev
    · exact (colour_ne_of_visible hproper hnext) hpnext
    · have hopp := P.opposite_colour (i + 1)
      have hadd : (i + 1) + 2 = i + 3 := by fin_cases i <;> decide
      rw [hadd] at hopp
      exact (colour_ne_of_visible hproper hprev) (hpnext.trans hopp)

end Lax56Proofs.HKBQuadrilateralMaximal
