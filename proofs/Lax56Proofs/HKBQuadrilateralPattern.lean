import Lax56Proofs.HKBQuadrilateral
import Mathlib.Tactic

/-!
The visibility and colouring part of the standard nine-point quadrilateral
pattern (Lemma 6.5 in the direct HKB proof).
-/

namespace Lax56Proofs.HKBQuadrilateralPattern

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBQuadrilateral
open Lax56Proofs.Orientation

private theorem fin4_succ_ne (i : Fin 4) : i + 1 ≠ i := by
  fin_cases i <;> decide

private theorem fin4_add_two_ne (i : Fin 4) : i + 2 ≠ i := by
  fin_cases i <;> decide

private theorem fin4_two_remaining_alternate
    {c z a b d : Fin 4}
    (hzc : z ≠ c)
    (hac : a ≠ c) (hbc : b ≠ c) (hdc : d ≠ c)
    (hza : z ≠ a) (hzb : z ≠ b) (hzd : z ≠ d)
    (hab : a ≠ b) (hbd : b ≠ d) :
    a = d := by
  apply Fin.ext
  omega

/-- The intersection of the two diagonals does not lie between two adjacent
side-interior points. -/
theorem commonDiagonal_not_between_adjacent_sidePoints
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {y : Fin 4 → Point} {z : Point}
    (hyseg : ∀ i, y i ∈ openSegment ℝ (q i) (q (i + 1)))
    (hz₀₂ : z ∈ openSegment ℝ (q 0) (q 2))
    (hz₁₃ : z ∈ openSegment ℝ (q 1) (q 3))
    (i : Fin 4) :
    z ∉ openSegment ℝ (y i) (y (i + 1)) := by
  have hmid (j : Fin 4) :
      turn (q j) (q (j + 2)) (q (j + 1)) < 0 := by
    rw [turn_swap_last]
    have hpos := hq.2 j (j + 2)
      (by fin_cases j <;> decide) (by fin_cases j <;> decide)
    linarith
  have hy₀ : turn (q i) (q (i + 2)) (y i) < 0 := by
    obtain ⟨t, ht, ht1, heq⟩ :=
      turn_of_mem_openSegment
        (a := q i) (b := q (i + 2)) (hyseg i)
    have hleft : turn (q i) (q (i + 2)) (q i) = 0 := by simp
    rw [hleft] at heq
    nlinarith [hmid i]
  have hy₁ : turn (q i) (q (i + 2)) (y (i + 1)) < 0 := by
    obtain ⟨t, ht, ht1, heq⟩ :=
      turn_of_mem_openSegment
        (a := q i) (b := q (i + 2)) (hyseg (i + 1))
    have hright :
        turn (q i) (q (i + 2)) (q ((i + 1) + 1)) = 0 := by
      simp only [add_assoc]
      simp
    rw [hright] at heq
    nlinarith [hmid i]
  have hzzero : turn (q i) (q (i + 2)) z = 0 := by
    have endpointZero {a b : Point}
        (hz : z ∈ openSegment ℝ a b) : turn a b z = 0 := by
      rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hz, neg_zero]
    fin_cases i
    · simpa using endpointZero hz₀₂
    · simpa using endpointZero hz₁₃
    · apply endpointZero (a := q 2) (b := q 0)
      simpa only [openSegment_symm] using hz₀₂
    · apply endpointZero (a := q 3) (b := q 1)
      simpa only [openSegment_symm] using hz₁₃
  intro hzbetween
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment
      (a := q i) (b := q (i + 2)) hzbetween
  rw [hzzero] at heq
  nlinarith

/-- In the five-point pattern, the common diagonal point sees every side
blocker. -/
theorem visible_commonDiagonal_sidePoint
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (y : Fin 4 → B) (z : B)
    (hyseg : ∀ i, (y i : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 1) : Point))
    (hzseg : (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point))
    (hzy : ∀ i, (z : Point) ≠ (y i : Point))
    (hpattern : quadInteriorPoints B (fun i ↦ (q i : Point)) =
      insert (z : Point)
        ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)))
    (i : Fin 4) :
    Visible B (z : Point) (y i : Point) := by
  refine ⟨hzy i, ?_⟩
  intro p hpB hpbetween
  have hzHull : (z : Point) ∈
      quadrilateralHull (fun i ↦ (q i : Point)) :=
    (segment_subset_convexHull
      (Set.mem_range_self (0 : Fin 4)) (Set.mem_range_self (2 : Fin 4)))
      (openSegment_subset_segment ℝ _ _ hzseg)
  have hyHull : (y i : Point) ∈
      quadrilateralHull (fun i ↦ (q i : Point)) :=
    (segment_subset_convexHull
      (Set.mem_range_self i) (Set.mem_range_self (i + 1)))
      (openSegment_subset_segment ℝ _ _ (hyseg i))
  have hpHull : p ∈ quadrilateralHull (fun i ↦ (q i : Point)) :=
    (convex_convexHull ℝ
      (Set.range fun i ↦ (q i : Point))).openSegment_subset
      hzHull hyHull hpbetween
  have hpPos (j : Fin 4) :
      0 < turn (q j : Point) (q (j + 1) : Point) p := by
    have hzPos := quad_diagonalPoint_edgeTurn_pos hq
      (by decide : (0 : Fin 4) ≠ 2) (by decide) (by decide) hzseg j
    have hyNonneg := quad_edgeTurn_nonneg_of_mem_convexHull hq hyHull j
    exact edgeTurn_pos_of_mem_openSegment hpbetween hzPos.le hyNonneg
      (Or.inl hzPos)
  have hpNot : p ∉ Set.range (fun i ↦ (q i : Point)) := by
    rintro ⟨j, rfl⟩
    have := hpPos j
    simp at this
  have hpR : p ∈ quadInteriorPoints B (fun i ↦ (q i : Point)) :=
    mem_quadInteriorPoints.mpr ⟨hpB, hpHull, hpNot⟩
  rw [hpattern] at hpR
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hpR
  rcases hpR with hpz | ⟨j, hpj⟩
  · subst p
    exact (hzy i) ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hpbetween)
  · subst p
    have hzero :
        turn (q j : Point) (q (j + 1) : Point) (y j : Point) = 0 := by
      rw [turn_swap_last, turn_eq_zero_of_mem_openSegment (hyseg j), neg_zero]
    linarith [hpPos j]

/-- Adjacent side blockers see one another in the five-point pattern. -/
theorem visible_adjacent_sidePoints
    {B : Finset Point}
    (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (y : Fin 4 → B) (z : B)
    (hyseg : ∀ i, (y i : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 1) : Point))
    (hz₀₂ : (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point))
    (hz₁₃ : (z : Point) ∈ openSegment ℝ (q 1 : Point) (q 3 : Point))
    (hyinj : Function.Injective (fun i ↦ (y i : Point)))
    (hpattern : quadInteriorPoints B (fun i ↦ (q i : Point)) =
      insert (z : Point)
        ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)))
    (i : Fin 4) :
    Visible B (y i : Point) (y (i + 1) : Point) := by
  have hyne : (y i : Point) ≠ (y (i + 1) : Point) :=
    hyinj.ne (fin4_succ_ne i).symm
  refine ⟨hyne, ?_⟩
  intro p hpB hpbetween
  have hyHull (j : Fin 4) : (y j : Point) ∈
      quadrilateralHull (fun i ↦ (q i : Point)) :=
    (segment_subset_convexHull
      (Set.mem_range_self j) (Set.mem_range_self (j + 1)))
      (openSegment_subset_segment ℝ _ _ (hyseg j))
  have hpHull : p ∈ quadrilateralHull (fun i ↦ (q i : Point)) :=
    (convex_convexHull ℝ
      (Set.range fun i ↦ (q i : Point))).openSegment_subset
      (hyHull i) (hyHull (i + 1)) hpbetween
  have hpPos (j : Fin 4) :
      0 < turn (q j : Point) (q (j + 1) : Point) p := by
    have hi0 := quad_edgeTurn_nonneg_of_mem_convexHull hq (hyHull i) j
    have his0 :=
      quad_edgeTurn_nonneg_of_mem_convexHull hq (hyHull (i + 1)) j
    have hstrict :
        0 < turn (q j : Point) (q (j + 1) : Point) (y i : Point) ∨
        0 < turn (q j : Point) (q (j + 1) : Point) (y (i + 1) : Point) := by
      by_cases hij : i = j
      · right
        subst j
        exact quad_sidePoint_other_edgeTurn_pos hq (fin4_succ_ne i)
          (hyseg (i + 1))
      · left
        exact quad_sidePoint_other_edgeTurn_pos hq hij (hyseg i)
    exact edgeTurn_pos_of_mem_openSegment hpbetween hi0 his0 hstrict
  have hpNot : p ∉ Set.range (fun i ↦ (q i : Point)) := by
    rintro ⟨j, rfl⟩
    have := hpPos j
    simp at this
  have hpR : p ∈ quadInteriorPoints B (fun i ↦ (q i : Point)) :=
    mem_quadInteriorPoints.mpr ⟨hpB, hpHull, hpNot⟩
  rw [hpattern] at hpR
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hpR
  rcases hpR with hpz | ⟨j, hpj⟩
  · subst p
    exact commonDiagonal_not_between_adjacent_sidePoints hq hyseg
      hz₀₂ hz₁₃ i hpbetween
  · subst p
    have hzero :
        turn (q j : Point) (q (j + 1) : Point) (y j : Point) = 0 := by
      rw [turn_swap_last, turn_eq_zero_of_mem_openSegment (hyseg j), neg_zero]
    linarith [hpPos j]

/-- In the five-point pattern, any point of `B` between opposite side
blockers is the common diagonal blocker. -/
theorem eq_commonDiagonal_of_between_opposite_sidePoints
    {B : Finset Point}
    (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (y : Fin 4 → B) (z : B)
    (hyseg : ∀ i, (y i : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 1) : Point))
    (hpattern : quadInteriorPoints B (fun i ↦ (q i : Point)) =
      insert (z : Point)
        ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)))
    (i : Fin 4) {p : Point} (hpB : p ∈ B)
    (hpbetween : p ∈ openSegment ℝ (y i : Point) (y (i + 2) : Point)) :
    p = (z : Point) := by
  have hyHull (j : Fin 4) : (y j : Point) ∈
      quadrilateralHull (fun i ↦ (q i : Point)) :=
    (segment_subset_convexHull
      (Set.mem_range_self j) (Set.mem_range_self (j + 1)))
      (openSegment_subset_segment ℝ _ _ (hyseg j))
  have hpHull : p ∈ quadrilateralHull (fun i ↦ (q i : Point)) :=
    (convex_convexHull ℝ
      (Set.range fun i ↦ (q i : Point))).openSegment_subset
      (hyHull i) (hyHull (i + 2)) hpbetween
  have hpPos (j : Fin 4) :
      0 < turn (q j : Point) (q (j + 1) : Point) p := by
    have hi0 := quad_edgeTurn_nonneg_of_mem_convexHull hq (hyHull i) j
    have hi20 :=
      quad_edgeTurn_nonneg_of_mem_convexHull hq (hyHull (i + 2)) j
    have hstrict :
        0 < turn (q j : Point) (q (j + 1) : Point) (y i : Point) ∨
        0 < turn (q j : Point) (q (j + 1) : Point) (y (i + 2) : Point) := by
      by_cases hij : i = j
      · right
        subst j
        exact quad_sidePoint_other_edgeTurn_pos hq (fin4_add_two_ne i)
          (hyseg (i + 2))
      · left
        exact quad_sidePoint_other_edgeTurn_pos hq hij (hyseg i)
    exact edgeTurn_pos_of_mem_openSegment hpbetween hi0 hi20 hstrict
  have hpNot : p ∉ Set.range (fun i ↦ (q i : Point)) := by
    rintro ⟨j, rfl⟩
    have := hpPos j
    simp at this
  have hpR : p ∈ quadInteriorPoints B (fun i ↦ (q i : Point)) :=
    mem_quadInteriorPoints.mpr ⟨hpB, hpHull, hpNot⟩
  rw [hpattern] at hpR
  simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
    true_and] at hpR
  rcases hpR with hpz | ⟨j, hpj⟩
  · exact hpz
  · subst p
    have hzero :
        turn (q j : Point) (q (j + 1) : Point) (y j : Point) = 0 := by
      rw [turn_swap_last, turn_eq_zero_of_mem_openSegment (hyseg j), neg_zero]
    linarith [hpPos j]

/-- The four side-blocker colours alternate between the two colours other
than the quadrilateral colour and the diagonal-blocker colour. -/
theorem opposite_sidePoint_colours_eq
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (y : Fin 4 → B) (z : B)
    (hyseg : ∀ i, (y i : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 1) : Point))
    (hz₀₂ : (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point))
    (hz₁₃ : (z : Point) ∈ openSegment ℝ (q 1 : Point) (q 3 : Point))
    (hyinj : Function.Injective (fun i ↦ (y i : Point)))
    (hzy : ∀ i, (z : Point) ≠ (y i : Point))
    (hpattern : quadInteriorPoints B (fun i ↦ (q i : Point)) =
      insert (z : Point)
        ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point))) :
    ∀ i, colour (y i) = colour (y (i + 2)) := by
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hq.1
    exact congrArg Subtype.val hij
  have hyc (i : Fin 4) : colour (y i) ≠ c := by
    have hne : q i ≠ q (i + 1) :=
      hqinj.ne (fin4_succ_ne i).symm
    have h := blocker_colour_ne hfour hproper hne
      ((hmono i).trans (hmono (i + 1)).symm) (hyseg i)
    simpa only [hmono i] using h
  have hzc : colour z ≠ c := by
    have hne : q 0 ≠ q 2 := hqinj.ne (by decide)
    have h := blocker_colour_ne hfour hproper hne
      ((hmono 0).trans (hmono 2).symm) hz₀₂
    simpa only [hmono 0] using h
  have hzColour (i : Fin 4) : colour z ≠ colour (y i) := by
    intro heq
    have hne : z ≠ y i := by
      intro h
      exact hzy i (congrArg Subtype.val h)
    obtain ⟨p, hp⟩ := hproper z (y i) hne heq
    exact (visible_commonDiagonal_sidePoint hfour q hq y z hyseg
      hz₀₂ hzy hpattern i).2 p p.property hp
  have hadj (i : Fin 4) : colour (y i) ≠ colour (y (i + 1)) := by
    intro heq
    have hne : y i ≠ y (i + 1) := by
      intro h
      exact hyinj.ne (fin4_succ_ne i).symm (congrArg Subtype.val h)
    obtain ⟨p, hp⟩ := hproper (y i) (y (i + 1)) hne heq
    exact (visible_adjacent_sidePoints q hq y z hyseg hz₀₂ hz₁₃
      hyinj hpattern i).2 p p.property hp
  intro i
  exact fin4_two_remaining_alternate hzc
    (hyc i) (hyc (i + 1)) (hyc (i + 2))
    (hzColour i) (hzColour (i + 1)) (hzColour (i + 2))
    (hadj i) (by simpa only [add_assoc] using hadj (i + 1))

/-- The common diagonal point blocks each pair of opposite side blockers. -/
theorem commonDiagonal_between_opposite_sidePoints
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (y : Fin 4 → B) (z : B)
    (hyseg : ∀ i, (y i : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 1) : Point))
    (hz₀₂ : (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point))
    (hz₁₃ : (z : Point) ∈ openSegment ℝ (q 1 : Point) (q 3 : Point))
    (hyinj : Function.Injective (fun i ↦ (y i : Point)))
    (hzy : ∀ i, (z : Point) ≠ (y i : Point))
    (hpattern : quadInteriorPoints B (fun i ↦ (q i : Point)) =
      insert (z : Point)
        ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point))) :
    ∀ i, (z : Point) ∈ openSegment ℝ (y i : Point) (y (i + 2) : Point) := by
  have hopp := opposite_sidePoint_colours_eq hfour colour hproper c q hq
    hmono y z hyseg hz₀₂ hz₁₃ hyinj hzy hpattern
  intro i
  have hyne : y i ≠ y (i + 2) := by
    intro h
    exact hyinj.ne (fin4_add_two_ne i).symm (congrArg Subtype.val h)
  obtain ⟨p, hp⟩ := hproper (y i) (y (i + 2)) hyne (hopp i)
  have hpz : (p : Point) = (z : Point) :=
    eq_commonDiagonal_of_between_opposite_sidePoints q hq y z hyseg
      hpattern i p.property hp
  simpa only [hpz] using hp

/-- The complete standard five-point pattern associated with a
monochromatic convex quadrilateral. -/
structure StandardQuadrilateralPattern
    (B : Finset Point) (colour : B → Fin 4) (q : Fin 4 → B) where
  y : Fin 4 → B
  z : B
  side : ∀ i, (y i : Point) ∈
    openSegment ℝ (q i : Point) (q (i + 1) : Point)
  diagonal₀₂ : (z : Point) ∈
    openSegment ℝ (q 0 : Point) (q 2 : Point)
  diagonal₁₃ : (z : Point) ∈
    openSegment ℝ (q 1 : Point) (q 3 : Point)
  side_injective : Function.Injective (fun i ↦ (y i : Point))
  center_ne_side : ∀ i, (z : Point) ≠ (y i : Point)
  cover : quadInteriorPoints B (fun i ↦ (q i : Point)) =
    insert (z : Point)
      ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point))
  opposite_colour : ∀ i, colour (y i) = colour (y (i + 2))
  center_between_opposite : ∀ i, (z : Point) ∈
    openSegment ℝ (y i : Point) (y (i + 2) : Point)

/-- Lemma 6.5, packaged for reuse in the maximality argument. -/
theorem exists_standardQuadrilateralPattern
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i) :
    Nonempty (StandardQuadrilateralPattern B colour q) := by
  classical
  obtain ⟨y, z, hyseg, hz₀₂, hz₁₃, hyinj, hzy⟩ :=
    exists_quad_sideBlockers_and_common_diagonalBlocker
      hfour colour hproper c q hq hmono hclass
  have hpattern := quadInteriorPoints_eq_five_pattern
    hfour colour hproper c q hq hmono hclass y z hyseg hz₀₂ hyinj hzy
  have hopp := opposite_sidePoint_colours_eq hfour colour hproper c q hq
    hmono y z hyseg hz₀₂ hz₁₃ hyinj hzy hpattern
  have hzopp := commonDiagonal_between_opposite_sidePoints
    hfour colour hproper c q hq hmono y z hyseg hz₀₂ hz₁₃
      hyinj hzy hpattern
  exact ⟨⟨y, z, hyseg, hz₀₂, hz₁₃, hyinj, hzy,
    hpattern, hopp, hzopp⟩⟩

end Lax56Proofs.HKBQuadrilateralPattern
