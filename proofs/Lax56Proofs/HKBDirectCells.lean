import Lax56Proofs.HKBDirectConcave
import Lax56Proofs.HKBHexFinalGeometry
import Mathlib.Tactic

/-!
The subdivision of the outer triangle in the concave monochromatic
four-point case.  This file contains only geometric classification and
counting facts; the later beam case analysis is kept separate.
-/

namespace Lax56Proofs.HKBDirectCells

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBDirectConcave
open Lax56Proofs.HKBDirectCore
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexFinalGeometry
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

noncomputable def cellPoints
    (P : Finset Point) (a b c : Point) : Finset P := by
  classical
  exact Finset.univ.filter fun p ↦ StrictlyInsideTriangle a b c (p : Point)

@[simp] theorem mem_cellPoints
    {P : Finset Point} {a b c : Point} {p : P} :
    p ∈ cellPoints P a b c ↔ StrictlyInsideTriangle a b c (p : Point) := by
  classical
  simp [cellPoints]

/-- The subtype-valued and ambient-point-valued versions of the open cell
have the same cardinality. -/
theorem cellPoints_card_eq_cellInteriorPoints_card
    {P : Finset Point} {a b c : Point} :
    (cellPoints P a b c).card = (cellInteriorPoints P a b c).card := by
  classical
  apply Finset.card_bij
    (s := cellPoints P a b c) (t := cellInteriorPoints P a b c)
    (fun p _ ↦ (p : Point))
  · intro p hp
    exact mem_cellInteriorPoints.mpr ⟨p.property, mem_cellPoints.mp hp⟩
  · intro p _ q _ hpq
    exact Subtype.ext hpq
  · intro p hp
    refine ⟨⟨p, (mem_cellInteriorPoints.mp hp).1⟩, ?_, rfl⟩
    exact mem_cellPoints.mpr (mem_cellInteriorPoints.mp hp).2

/-- A line containing two fixed points and one known third point contains no
other point of a no-four-collinear finite set. -/
theorem point_eq_of_on_full_line
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {x y z p : P} (hxy : x ≠ y)
    (hz : (z : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hp : turn (x : Point) (y : Point) (p : Point) = 0) :
    p = x ∨ p = y ∨ p = z := by
  by_cases hpx : p = x
  · exact Or.inl hpx
  by_cases hpy : p = y
  · exact Or.inr (Or.inl hpy)
  right
  right
  have hzx : z ≠ x := by
    intro e
    subst z
    apply hxy
    apply Subtype.ext
    exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp hz
  have hzy : z ≠ y := by
    intro e
    subst z
    apply hxy
    apply Subtype.ext
    exact (right_mem_openSegment_iff (𝕜 := ℝ)).mp hz
  apply Subtype.ext
  exact third_point_unique hfour x.property y.property p.property z.property
    (Subtype.val_injective.ne hxy)
    (Subtype.val_injective.ne hpx) (Subtype.val_injective.ne hpy)
    (Subtype.val_injective.ne hzx) (Subtype.val_injective.ne hzy)
    (mem_line_of_turn_eq_zero (Subtype.val_injective.ne hxy) hp)
    (mem_affineSpan_pair_of_mem_openSegment hz)

/-- The three spoke determinants, weighted by the positive barycentric
coordinates of the interior point `d`, sum to zero. -/
theorem spoke_turn_sum_eq_zero (a b c d p : Point) :
    turn b c d * turn a d p +
      turn c a d * turn b d p +
      turn a b d * turn c d p = 0 := by
  simp only [turn]
  ring

/-- A point strictly inside the outer triangle and on none of the three
spoke lines lies strictly inside exactly one of the three cells.  Only the
existence part is needed here. -/
theorem strict_cell_cases
    {a b c d p : Point}
    (hd : StrictlyInsideTriangle a b c d)
    (hp : StrictlyInsideTriangle a b c p)
    (had : turn a d p ≠ 0)
    (hbd : turn b d p ≠ 0)
    (hcd : turn c d p ≠ 0) :
    StrictlyInsideTriangle b c d p ∨
      StrictlyInsideTriangle c a d p ∨
      StrictlyInsideTriangle a b d p := by
  have hsum := spoke_turn_sum_eq_zero a b c d p
  rcases lt_or_gt_of_ne hcd with hcdNeg | hcdPos
  · rcases lt_or_gt_of_ne had with hadNeg | hadPos
    · have hbdPos : 0 < turn b d p := by
        by_contra hnot
        have hbdNeg : turn b d p < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hbd
        have h₁ := mul_neg_of_pos_of_neg hd.2.1 hadNeg
        have h₂ := mul_neg_of_pos_of_neg hd.2.2 hbdNeg
        have h₃ := mul_neg_of_pos_of_neg hd.1 hcdNeg
        linarith
      exact Or.inr (Or.inr ⟨hp.1, hbdPos, by
        rw [turn_swap_first]
        linarith⟩)
    · exact Or.inr (Or.inl ⟨hp.2.2, hadPos, by
        rw [turn_swap_first]
        linarith⟩)
  · rcases lt_or_gt_of_ne hbd with hbdNeg | hbdPos
    · exact Or.inl ⟨hp.2.1, hcdPos, by
        rw [turn_swap_first]
        linarith⟩
    · have hadNeg : turn a d p < 0 := by
        by_contra hnot
        have hadPos : 0 < turn a d p := lt_of_le_of_ne (le_of_not_gt hnot) had.symm
        have h₁ := mul_pos hd.2.1 hadPos
        have h₂ := mul_pos hd.2.2 hbdPos
        have h₃ := mul_pos hd.1 hcdPos
        linarith
      exact Or.inr (Or.inr ⟨hp.1, hbdPos, by
        rw [turn_swap_first]
        linarith⟩)

/-- Every point of the ambient set in the outer triangle is a red skeleton
vertex, a skeleton blocker, or is strictly inside one of the three cells.
The cells are positively oriented as `(b,c,d)`, `(c,a,d)`, `(a,b,d)`.
-/
theorem concave_hull_point_cases
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {a b c d : P}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point))
    (S : ConcaveSkeleton P colour a b c d)
    (p : P)
    (hpHull : (p : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point)) :
    p = a ∨ p = b ∨ p = c ∨ p = d ∨
      p = S.u₁ ∨ p = S.u₂ ∨ p = S.u₃ ∨
      p = S.v₁ ∨ p = S.v₂ ∨ p = S.v₃ ∨
      StrictlyInsideTriangle (b : Point) (c : Point) (d : Point) (p : Point) ∨
      StrictlyInsideTriangle (c : Point) (a : Point) (d : Point) (p : Point) ∨
      StrictlyInsideTriangle (a : Point) (b : Point) (d : Point) (p : Point) := by
  by_cases hpa : p = a
  · exact Or.inl hpa
  by_cases hpb : p = b
  · exact Or.inr (Or.inl hpb)
  by_cases hpc : p = c
  · exact Or.inr (Or.inr (Or.inl hpc))
  by_cases hpd : p = d
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpd)))
  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle hd
  have hedge := triangle_edge_nonneg habc.le hpHull
  by_cases hpab0 : turn (a : Point) (b : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour hab S.hv₃ hpab0 with h | h | h
    · exact (hpa h).elim
    · exact (hpb h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  by_cases hpbc0 : turn (b : Point) (c : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour hbc S.hv₁ hpbc0 with h | h | h
    · exact (hpb h).elim
    · exact (hpc h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl h)))))))
  by_cases hpca0 : turn (c : Point) (a : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour hac.symm
        (by simpa only [openSegment_symm] using S.hv₂) hpca0 with h | h | h
    · exact (hpc h).elim
    · exact (hpa h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
  have hpOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (p : Point) := ⟨lt_of_le_of_ne hedge.1 (Ne.symm hpab0),
        lt_of_le_of_ne hedge.2.1 (Ne.symm hpbc0),
        lt_of_le_of_ne hedge.2.2 (Ne.symm hpca0)⟩
  by_cases hpad0 : turn (a : Point) (d : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour had S.hu₁ hpad0 with h | h | h
    · exact (hpa h).elim
    · exact (hpd h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  by_cases hpbd0 : turn (b : Point) (d : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour hbd S.hu₂ hpbd0 with h | h | h
    · exact (hpb h).elim
    · exact (hpd h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  by_cases hpcd0 : turn (c : Point) (d : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour hcd S.hu₃ hpcd0 with h | h | h
    · exact (hpc h).elim
    · exact (hpd h).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))
  rcases strict_cell_cases hd hpOuter hpad0 hpbd0 hpcd0 with h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))

/-- The three open cells are pairwise disjoint. -/
theorem cellPoints_pairwise_disjoint
    {P : Finset Point} {a b c d : Point} :
    Disjoint (cellPoints P b c d) (cellPoints P c a d) ∧
      Disjoint (cellPoints P b c d) (cellPoints P a b d) ∧
      Disjoint (cellPoints P c a d) (cellPoints P a b d) := by
  classical
  constructor
  · rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have h₁ := mem_cellPoints.mp hp₁
    have h₂ := mem_cellPoints.mp hp₂
    have h₂' := h₂.2.2
    rw [turn_swap_first] at h₂'
    linarith [h₁.2.1, h₂']
  constructor
  · rw [Finset.disjoint_left]
    intro p hp₁ hp₃
    have h₁ := mem_cellPoints.mp hp₁
    have h₃ := mem_cellPoints.mp hp₃
    have h₁' := h₁.2.2
    rw [turn_swap_first] at h₁'
    linarith [h₁', h₃.2.1]
  · rw [Finset.disjoint_left]
    intro p hp₂ hp₃
    have h₂ := mem_cellPoints.mp hp₂
    have h₃ := mem_cellPoints.mp hp₃
    have h₃' := h₃.2.2
    rw [turn_swap_first] at h₃'
    linarith [h₂.2.1, h₃']

/-- Strict membership in any of the three cells implies strict membership
in the outer triangle. -/
theorem strict_cell_strict_outer
    {a b c d p : Point} (hd : StrictlyInsideTriangle a b c d) :
    (StrictlyInsideTriangle b c d p ∨
      StrictlyInsideTriangle c a d p ∨
      StrictlyInsideTriangle a b d p) →
    StrictlyInsideTriangle a b c p := by
  intro hp
  have habc : 0 < turn a b c := turn_pos_of_strictlyInsideTriangle hd
  rcases hp with h₁ | h₂ | h₃
  · refine ⟨?_, h₁.1, ?_⟩
    · apply edgeTurn_pos_of_strictlyInsideTriangle h₁
      · simp
      · exact habc.le
      · exact hd.1.le
      · exact Or.inr (Or.inl habc)
    · apply edgeTurn_pos_of_strictlyInsideTriangle h₁
      · simpa only [turn_rotate] using habc.le
      · simp
      · exact hd.2.2.le
      · exact Or.inl (by simpa only [turn_rotate] using habc)
  · refine ⟨?_, ?_, h₂.1⟩
    · apply edgeTurn_pos_of_strictlyInsideTriangle h₂
      · exact habc.le
      · simp
      · exact hd.1.le
      · exact Or.inl habc
    · apply edgeTurn_pos_of_strictlyInsideTriangle h₂
      · simp
      · simpa only [turn_rotate] using habc.le
      · exact hd.2.1.le
      · exact Or.inr (Or.inl (by simpa only [turn_rotate] using habc))
  · refine ⟨h₃.1, ?_, ?_⟩
    · apply edgeTurn_pos_of_strictlyInsideTriangle h₃
      · simpa only [turn_rotate] using habc.le
      · simp
      · exact hd.2.1.le
      · exact Or.inl (by simpa only [turn_rotate] using habc)
    · apply edgeTurn_pos_of_strictlyInsideTriangle h₃
      · simp
      · simpa only [turn_rotate] using habc.le
      · exact hd.2.2.le
      · exact Or.inr (Or.inl (by simpa only [turn_rotate] using habc))

theorem cell_one_hull_subset_outer
    {a b c d : Point} (hd : StrictlyInsideTriangle a b c d) :
    triangleHull b c d ⊆ triangleHull a b c := by
  apply triangleHull_subset_of_mem (convex_convexHull ℝ _)
  · exact subset_convexHull ℝ _ (by simp [triangleHull])
  · exact subset_convexHull ℝ _ (by simp [triangleHull])
  · exact strictlyInsideTriangle_mem_triangleHull hd

theorem cell_two_hull_subset_outer
    {a b c d : Point} (hd : StrictlyInsideTriangle a b c d) :
    triangleHull c a d ⊆ triangleHull a b c := by
  apply triangleHull_subset_of_mem (convex_convexHull ℝ _)
  · exact subset_convexHull ℝ _ (by simp [triangleHull])
  · exact subset_convexHull ℝ _ (by simp [triangleHull])
  · exact strictlyInsideTriangle_mem_triangleHull hd

theorem cell_three_hull_subset_outer
    {a b c d : Point} (hd : StrictlyInsideTriangle a b c d) :
    triangleHull a b d ⊆ triangleHull a b c := by
  apply triangleHull_subset_of_mem (convex_convexHull ℝ _)
  · exact subset_convexHull ℝ _ (by simp [triangleHull])
  · exact subset_convexHull ℝ _ (by simp [triangleHull])
  · exact strictlyInsideTriangle_mem_triangleHull hd

/-- A strict cell point lies in the outer closed triangle. -/
theorem cell_point_mem_outer
    {a b c d p : Point} (hd : StrictlyInsideTriangle a b c d) :
    (StrictlyInsideTriangle b c d p ∨
      StrictlyInsideTriangle c a d p ∨
      StrictlyInsideTriangle a b d p) →
    p ∈ triangleHull a b c := by
  intro hp
  rcases hp with h₁ | h₂ | h₃
  · exact cell_one_hull_subset_outer hd
      (strictlyInsideTriangle_mem_triangleHull h₁)
  · exact cell_two_hull_subset_outer hd
      (strictlyInsideTriangle_mem_triangleHull h₂)
  · exact cell_three_hull_subset_outer hd
      (strictlyInsideTriangle_mem_triangleHull h₃)

noncomputable def allCellPoints
    (P : Finset Point) (a b c d : Point) : Finset P :=
  cellPoints P b c d ∪ cellPoints P c a d ∪ cellPoints P a b d

@[simp] theorem mem_allCellPoints
    {P : Finset Point} {a b c d : Point} {p : P} :
    p ∈ allCellPoints P a b c d ↔
      StrictlyInsideTriangle b c d (p : Point) ∨
      StrictlyInsideTriangle c a d (p : Point) ∨
      StrictlyInsideTriangle a b d (p : Point) := by
  classical
  simp [allCellPoints]

theorem allCellPoints_card_eq_sum
    {P : Finset Point} {a b c d : Point} :
    (allCellPoints P a b c d).card =
      (cellPoints P b c d).card + (cellPoints P c a d).card +
        (cellPoints P a b d).card := by
  classical
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ :=
    cellPoints_pairwise_disjoint (P := P) (a := a) (b := b) (c := c) (d := d)
  rw [allCellPoints, Finset.card_union_of_disjoint]
  · rw [Finset.card_union_of_disjoint h₁₂]
  · rw [Finset.disjoint_left]
    intro p hp₁₂ hp₃
    rcases Finset.mem_union.mp hp₁₂ with hp₁ | hp₂
    · exact (Finset.disjoint_left.mp h₁₃) hp₁ hp₃
    · exact (Finset.disjoint_left.mp h₂₃) hp₂ hp₃

noncomputable def skeletonPoints
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (S : ConcaveSkeleton P colour a b c d) : Finset P :=
  (Finset.univ : Finset (Fin 6)).image
    (![S.u₁, S.u₂, S.u₃, S.v₁, S.v₂, S.v₃] : Fin 6 → P)

@[simp] theorem mem_skeletonPoints
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    {S : ConcaveSkeleton P colour a b c d} {p : P} :
    p ∈ skeletonPoints S ↔
      ∃ i : Fin 6,
        (![S.u₁, S.u₂, S.u₃, S.v₁, S.v₂, S.v₃] : Fin 6 → P) i = p := by
  classical
  simp [skeletonPoints]

theorem skeletonPoints_card
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (S : ConcaveSkeleton P colour a b c d) :
    (skeletonPoints S).card = 6 := by
  classical
  rw [skeletonPoints, Finset.card_image_of_injective]
  · simp
  · exact S.blockers_injective

theorem turn_neg_of_between_of_neg_zero
    {l r x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : turn l r x < 0) (hy : turn l r y = 0) :
    turn l r z < 0 := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := l) (b := r) hz
  rw [heq, hy, mul_zero, add_zero]
  exact mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hx

/-- None of the six skeleton blockers lies strictly inside a cell. -/
theorem skeleton_point_not_mem_allCellPoints
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point))
    (S : ConcaveSkeleton P colour a b c d) (i : Fin 6) :
    (![S.u₁, S.u₂, S.u₃, S.v₁, S.v₂, S.v₃] : Fin 6 → P) i ∉
      allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point) := by
  have hu₁ad : turn (a : Point) (d : Point) (S.u₁ : Point) = 0 :=
    turn_eq_zero_of_between S.hu₁
  have hu₂bd : turn (b : Point) (d : Point) (S.u₂ : Point) = 0 :=
    turn_eq_zero_of_between S.hu₂
  have hu₃cd : turn (c : Point) (d : Point) (S.u₃ : Point) = 0 :=
    turn_eq_zero_of_between S.hu₃
  have hu₁cd : turn (c : Point) (d : Point) (S.u₁ : Point) < 0 := by
    apply turn_neg_of_between_of_neg_zero S.hu₁
    · rw [turn_swap_last]
      linarith [hd.2.2]
    · simp
  have hu₂ad : turn (a : Point) (d : Point) (S.u₂ : Point) < 0 := by
    apply turn_neg_of_between_of_neg_zero S.hu₂
    · rw [turn_swap_last]
      linarith [hd.1]
    · simp
  have hu₃bd : turn (b : Point) (d : Point) (S.u₃ : Point) < 0 := by
    apply turn_neg_of_between_of_neg_zero S.hu₃
    · rw [turn_swap_last]
      linarith [hd.2.1]
    · simp
  have hv₁bc : turn (b : Point) (c : Point) (S.v₁ : Point) = 0 :=
    turn_eq_zero_of_between S.hv₁
  have hv₂ca : turn (c : Point) (a : Point) (S.v₂ : Point) = 0 := by
    rw [turn_swap_first, turn_eq_zero_of_between S.hv₂, neg_zero]
  have hv₃ab : turn (a : Point) (b : Point) (S.v₃ : Point) = 0 :=
    turn_eq_zero_of_between S.hv₃
  fin_cases i
  · change S.u₁ ∉ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
    rw [mem_allCellPoints]
    rintro (h₁ | h₂ | h₃)
    · linarith [h₁.2.1, hu₁cd]
    · linarith [h₂.2.1, hu₁ad]
    · have h := h₃.2.2
      rw [turn_swap_first] at h
      linarith [h, hu₁ad]
  · change S.u₂ ∉ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
    rw [mem_allCellPoints]
    rintro (h₁ | h₂ | h₃)
    · have h := h₁.2.2
      rw [turn_swap_first] at h
      linarith [h, hu₂bd]
    · linarith [h₂.2.1, hu₂ad]
    · linarith [h₃.2.1, hu₂bd]
  · change S.u₃ ∉ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
    rw [mem_allCellPoints]
    rintro (h₁ | h₂ | h₃)
    · linarith [h₁.2.1, hu₃cd]
    · have h := h₂.2.2
      rw [turn_swap_first] at h
      linarith [h, hu₃cd]
    · linarith [h₃.2.1, hu₃bd]
  · change S.v₁ ∉ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
    rw [mem_allCellPoints]
    intro h
    have hout := strict_cell_strict_outer hd h
    linarith [hout.2.1, hv₁bc]
  · change S.v₂ ∉ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
    rw [mem_allCellPoints]
    intro h
    have hout := strict_cell_strict_outer hd h
    linarith [hout.2.2, hv₂ca]
  · change S.v₃ ∉ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
    rw [mem_allCellPoints]
    intro h
    have hout := strict_cell_strict_outer hd h
    linarith [hout.1, hv₃ab]

theorem skeletonPoints_disjoint_allCellPoints
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point))
    (S : ConcaveSkeleton P colour a b c d) :
    Disjoint (skeletonPoints S)
      (allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpS hpE
  obtain ⟨i, hi⟩ := mem_skeletonPoints.mp hpS
  rw [← hi] at hpE
  exact skeleton_point_not_mem_allCellPoints hd S i hpE

noncomputable def nonredTrianglePoints
    (P : Finset Point) (colour : P → Fin 4)
    (a b c : Point) (red : Fin 4) : Finset P := by
  classical
  exact Finset.univ.filter fun p ↦
    (p : Point) ∈ triangleHull a b c ∧ colour p ≠ red

@[simp] theorem mem_nonredTrianglePoints
    {P : Finset Point} {colour : P → Fin 4}
    {a b c : Point} {red : Fin 4} {p : P} :
    p ∈ nonredTrianglePoints P colour a b c red ↔
      (p : Point) ∈ triangleHull a b c ∧ colour p ≠ red := by
  classical
  simp [nonredTrianglePoints]

/-- Three nonred colours, each occurring at most three times in the outer
triangle, account for at most nine points. -/
theorem nonredTrianglePoints_card_le_nine
    {P : Finset Point} {colour : P → Fin 4}
    {a b c : Point} {red : Fin 4}
    (hbound : ∀ e : Fin 4, e ≠ red →
      (pointsOfColourInTriangle P colour a b c e).card ≤ 3) :
    (nonredTrianglePoints P colour a b c red).card ≤ 9 := by
  classical
  let N := nonredTrianglePoints P colour a b c red
  have hfiber (e : Fin 4) :
      (N.filter fun p ↦ colour p = e).card ≤ if e = red then 0 else 3 := by
    by_cases her : e = red
    · subst e
      simp [N, nonredTrianglePoints]
    · simp only [her, ↓reduceIte]
      apply le_trans (Finset.card_le_card ?_) (hbound e her)
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpN := mem_nonredTrianglePoints.mp hp'.1
      exact mem_pointsOfColourInTriangle.mpr ⟨hpN.1, hp'.2⟩
  have hcard : N.card =
      ∑ e ∈ (Finset.univ : Finset (Fin 4)),
        (N.filter fun p ↦ colour p = e).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro p hp
    simp
  rw [hcard]
  calc
    ∑ e ∈ (Finset.univ : Finset (Fin 4)),
        (N.filter fun p ↦ colour p = e).card ≤
        ∑ e ∈ (Finset.univ : Finset (Fin 4)), if e = red then 0 else 3 :=
      Finset.sum_le_sum fun e _ ↦ hfiber e
    _ = 9 := by
      fin_cases red <;> decide

/-- A point strictly inside one of the cells cannot have the red colour if
the only red points in the outer triangle are `a,b,c,d`. -/
theorem allCellPoint_colour_ne_red
    {P : Finset Point} {colour : P → Fin 4} {a b c d p : P}
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point))
    (hred : ∀ z : P,
      (z : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) →
      colour z = colour a → z = a ∨ z = b ∨ z = c ∨ z = d)
    (hp : p ∈ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)) :
    colour p ≠ colour a := by
  intro hc
  have hcell := mem_allCellPoints.mp hp
  have houterStrict := strict_cell_strict_outer hd hcell
  have houterHull := strictlyInsideTriangle_mem_triangleHull houterStrict
  rcases hred p houterHull hc with h | h | h | h
  · exact (strictlyInsideTriangle_ne_vertices houterStrict).1
      (congrArg Subtype.val h)
  · exact (strictlyInsideTriangle_ne_vertices houterStrict).2.1
      (congrArg Subtype.val h)
  · exact (strictlyInsideTriangle_ne_vertices houterStrict).2.2
      (congrArg Subtype.val h)
  · subst p
    rcases hcell with h₁ | h₂ | h₃
    · exact (strictlyInsideTriangle_ne_vertices h₁).2.2 rfl
    · exact (strictlyInsideTriangle_ne_vertices h₂).2.2 rfl
    · exact (strictlyInsideTriangle_ne_vertices h₃).2.2 rfl

/-- The six skeleton blockers leave room for at most three strict cell
points among the nine available nonred positions. -/
theorem allCellPoints_card_le_three
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point))
    (S : ConcaveSkeleton P colour a b c d)
    (hred : ∀ z : P,
      (z : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) →
      colour z = colour a → z = a ∨ z = b ∨ z = c ∨ z = d)
    (hbound : ∀ e : Fin 4, e ≠ colour a →
      (pointsOfColourInTriangle P colour (a : Point) (b : Point)
        (c : Point) e).card ≤ 3) :
    (allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)).card ≤ 3 := by
  classical
  let E := allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point)
  let N := nonredTrianglePoints P colour (a : Point) (b : Point) (c : Point)
    (colour a)
  have hsub : skeletonPoints S ∪ E ⊆ N := by
    intro p hp
    rcases Finset.mem_union.mp hp with hpS | hpE
    · obtain ⟨i, hi⟩ := mem_skeletonPoints.mp hpS
      have hcol : colour p ≠ colour a := by
        rw [← hi]
        exact S.blocker_colour_ne i
      have hpHull : (p : Point) ∈
          triangleHull (a : Point) (b : Point) (c : Point) := by
        fin_cases i
        · rw [← hi]
          exact openSegment_mem_triangleHull_of_mem
            (vertex_mem_triangleHull _ _ _)
            (strictlyInsideTriangle_mem_triangleHull hd) S.hu₁
        · rw [← hi]
          exact openSegment_mem_triangleHull_of_mem
            (subset_convexHull ℝ _ (by simp [triangleHull]))
            (strictlyInsideTriangle_mem_triangleHull hd) S.hu₂
        · rw [← hi]
          exact openSegment_mem_triangleHull_of_mem
            (subset_convexHull ℝ _ (by simp [triangleHull]))
            (strictlyInsideTriangle_mem_triangleHull hd) S.hu₃
        · rw [← hi]
          have h := openSegment_subset_triangleHull_left
            (c := (a : Point)) S.hv₁
          simpa only [triangleHull_rotate] using h
        · rw [← hi]
          have h := openSegment_subset_triangleHull_left
            (c := (b : Point)) S.hv₂
          simpa only [triangleHull_swap_last] using h
        · rw [← hi]
          exact openSegment_subset_triangleHull_left S.hv₃
      exact mem_nonredTrianglePoints.mpr ⟨hpHull, hcol⟩
    · exact mem_nonredTrianglePoints.mpr
        ⟨cell_point_mem_outer hd (mem_allCellPoints.mp hpE),
          allCellPoint_colour_ne_red hd hred hpE⟩
  have hdisj := skeletonPoints_disjoint_allCellPoints hd S
  have hcardUnion : (skeletonPoints S ∪ E).card = 6 + E.card := by
    rw [Finset.card_union_of_disjoint hdisj, skeletonPoints_card]
  have hleN : (skeletonPoints S ∪ E).card ≤ N.card := Finset.card_le_card hsub
  have hN : N.card ≤ 9 := nonredTrianglePoints_card_le_nine hbound
  change E.card ≤ 3
  rw [hcardUnion] at hleN
  omega

end Lax56Proofs.HKBDirectCells
