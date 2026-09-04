import Lax56Proofs.HKBColourBound
import Mathlib.Tactic

/-!
The convex four-point part of the HKB colour-class bound.
-/

namespace Lax56Proofs.HKBQuadrilateral

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBConvexity
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBSixStructure
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- Four labelled points in strict counterclockwise cyclic order. -/
def StrictConvexQuadrilateral (q : Fin 4 → Point) : Prop :=
  Function.Injective q ∧
    ∀ i j : Fin 4, j ≠ i → j ≠ i + 1 →
      0 < turn (q i) (q (i + 1)) (q j)

noncomputable def quadrilateralHull (q : Fin 4 → Point) : Set Point :=
  convexHull ℝ (Set.range q)

private theorem fin4_succ_ne (i : Fin 4) : i + 1 ≠ i := by
  fin_cases i <;> decide

theorem quad_edgeTurn_nonneg_of_mem_convexHull
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {p : Point} (hp : p ∈ quadrilateralHull q) (i : Fin 4) :
    0 ≤ turn (q i) (q (i + 1)) p := by
  let S : Set Point := {r | 0 ≤ turn (q i) (q (i + 1)) r}
  have hconv : Convex ℝ S := by
    intro x hx y hy u v hu hv huv
    change 0 ≤ turn (q i) (q (i + 1)) (u • x + v • y)
    rw [turn_convex_combo _ _ _ _ _ _ huv]
    exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)
  apply convexHull_min (s := Set.range q) (t := S) _ hconv hp
  rintro _ ⟨j, rfl⟩
  by_cases hji : j = i
  · subst j
    simp [S]
  by_cases hjs : j = i + 1
  · subst j
    simp [S]
  exact (hq.2 i j hji hjs).le

/-- Conversely, the four oriented side inequalities characterize the closed
quadrilateral. -/
theorem mem_quadrilateralHull_of_edgeTurns_nonneg
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {p : Point}
    (hp : ∀ i, 0 ≤ turn (q i) (q (i + 1)) p) :
    p ∈ quadrilateralHull q := by
  have htri₀₁₂ : triangleHull (q 0) (q 1) (q 2) ⊆ quadrilateralHull q := by
    apply convexHull_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_range_self 0
    · exact Set.mem_range_self 1
    · exact Set.mem_range_self 2
  have htri₀₂₃ : triangleHull (q 0) (q 2) (q 3) ⊆ quadrilateralHull q := by
    apply convexHull_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact Set.mem_range_self 0
    · exact Set.mem_range_self 2
    · exact Set.mem_range_self 3
  by_cases hdiag : 0 ≤ turn (q 0) (q 2) p
  · apply htri₀₂₃
    apply weaklyInsideTriangle_mem_triangleHull
    · have h := hq.2 2 0 (by decide) (by decide)
      simpa only [turn_rotate] using h
    · refine ⟨hdiag, hp 2, ?_⟩
      simpa using hp 3
  · apply htri₀₁₂
    apply weaklyInsideTriangle_mem_triangleHull
    · exact hq.2 0 2 (by decide) (by decide)
    · refine ⟨hp 0, hp 1, ?_⟩
      rw [turn_swap_first]
      have := lt_of_not_ge hdiag
      linarith

theorem quad_diagonalPoint_edgeTurn_pos
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {j k : Fin 4} (hjk : j ≠ k)
    (hnbr : k ≠ j + 1) (hnbr' : j ≠ k + 1)
    {p : Point} (hp : p ∈ openSegment ℝ (q j) (q k)) (i : Fin 4) :
    0 < turn (q i) (q (i + 1)) p := by
  have hj0 : 0 ≤ turn (q i) (q (i + 1)) (q j) := by
    by_cases hji : j = i
    · subst j; simp
    by_cases hjs : j = i + 1
    · subst j; simp
    exact (hq.2 i j hji hjs).le
  have hk0 : 0 ≤ turn (q i) (q (i + 1)) (q k) := by
    by_cases hki : k = i
    · subst k; simp
    by_cases hks : k = i + 1
    · subst k; simp
    exact (hq.2 i k hki hks).le
  apply edgeTurn_pos_of_mem_openSegment hp hj0 hk0
  by_contra hnot
  push Not at hnot
  have hjz : turn (q i) (q (i + 1)) (q j) = 0 :=
    le_antisymm hnot.1 hj0
  have hkz : turn (q i) (q (i + 1)) (q k) = 0 :=
    le_antisymm hnot.2 hk0
  have hjend : j = i ∨ j = i + 1 := by
    by_contra hj
    push Not at hj
    exact (ne_of_gt (hq.2 i j hj.1 hj.2)) hjz
  have hkend : k = i ∨ k = i + 1 := by
    by_contra hk
    push Not at hk
    exact (ne_of_gt (hq.2 i k hk.1 hk.2)) hkz
  rcases hjend with rfl | rfl <;> rcases hkend with rfl | rfl
  · exact hjk rfl
  · exact hnbr rfl
  · exact hnbr' rfl
  · exact hjk rfl

theorem quadVertex_not_between_quadVertices
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {i j : Fin 4} (hij : i ≠ j) (k : Fin 4) :
    q k ∉ openSegment ℝ (q i) (q j) := by
  intro hk
  have hi0 : 0 ≤ turn (q k) (q (k + 1)) (q i) := by
    by_cases hik : i = k
    · subst i; simp
    by_cases his : i = k + 1
    · subst i; simp
    exact (hq.2 k i hik his).le
  have hj0 : 0 ≤ turn (q k) (q (k + 1)) (q j) := by
    by_cases hjk : j = k
    · subst j; simp
    by_cases hjs : j = k + 1
    · subst j; simp
    exact (hq.2 k j hjk hjs).le
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := q k) (b := q (k + 1)) hk
  have hiz : turn (q k) (q (k + 1)) (q i) = 0 := by
    have : turn (q k) (q (k + 1)) (q k) = 0 := by simp
    rw [this] at heq
    nlinarith
  have hjz : turn (q k) (q (k + 1)) (q j) = 0 := by
    have : turn (q k) (q (k + 1)) (q k) = 0 := by simp
    rw [this] at heq
    nlinarith
  have hiend : i = k ∨ i = k + 1 := by
    by_contra hi
    push Not at hi
    exact (ne_of_gt (hq.2 k i hi.1 hi.2)) hiz
  have hjend : j = k ∨ j = k + 1 := by
    by_contra hj
    push Not at hj
    exact (ne_of_gt (hq.2 k j hj.1 hj.2)) hjz
  rcases hiend with hik | his
  · rcases hjend with hjk | hjs
    · exact hij (hik.trans hjk.symm)
    · have hk' : q k ∈ openSegment ℝ (q k) (q (k + 1)) := by
        simpa [hik, hjs] using hk
      exact (hq.1.ne (fin4_succ_ne k).symm)
        ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hk')
  · rcases hjend with hjk | hjs
    · have hk' : q k ∈ openSegment ℝ (q (k + 1)) (q k) := by
        simpa [his, hjk] using hk
      exact (hq.1.ne (fin4_succ_ne k).symm)
        ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hk').symm
    · exact hij (his.trans hjs.symm)

theorem quad_side_openSegments_disjoint
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {i j : Fin 4} (hij : i ≠ j) :
    Disjoint (openSegment ℝ (q i) (q (i + 1)))
      (openSegment ℝ (q j) (q (j + 1))) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have hj0 : 0 ≤ turn (q i) (q (i + 1)) (q j) := by
    by_cases hji : j = i
    · exact (hij hji.symm).elim
    by_cases hjs : j = i + 1
    · subst j; simp
    exact (hq.2 i j hji hjs).le
  have hjs0 : 0 ≤ turn (q i) (q (i + 1)) (q (j + 1)) := by
    by_cases hji : j + 1 = i
    · subst i; simp
    by_cases hjs : j + 1 = i + 1
    · exact (hij (add_right_cancel hjs).symm).elim
    exact (hq.2 i (j + 1) hji hjs).le
  have hstrict : 0 < turn (q i) (q (i + 1)) (q j) ∨
      0 < turn (q i) (q (i + 1)) (q (j + 1)) := by
    by_cases hji : j = i
    · exact (hij hji.symm).elim
    by_cases hjs : j = i + 1
    · right
      apply hq.2
      · subst j
        fin_cases i <;> decide
      · subst j
        exact fin4_succ_ne (i + 1)
    exact Or.inl (hq.2 i j hji hjs)
  have hpPos := edgeTurn_pos_of_mem_openSegment hpj hj0 hjs0 hstrict
  have hpZero : turn (q i) (q (i + 1)) p = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hpi, neg_zero]
  linarith

/-- A point in the relative interior of one side is strictly inside every
other supporting half-plane of a strict convex quadrilateral. -/
theorem quad_sidePoint_other_edgeTurn_pos
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {i j : Fin 4} (hij : i ≠ j) {p : Point}
    (hp : p ∈ openSegment ℝ (q i) (q (i + 1))) :
    0 < turn (q j) (q (j + 1)) p := by
  have hi0 : 0 ≤ turn (q j) (q (j + 1)) (q i) := by
    by_cases hij' : i = j
    · exact (hij hij').elim
    by_cases his : i = j + 1
    · subst i
      simp
    exact (hq.2 j i hij' his).le
  have his0 : 0 ≤ turn (q j) (q (j + 1)) (q (i + 1)) := by
    by_cases hisj : i + 1 = j
    · subst j
      simp
    by_cases hiss : i + 1 = j + 1
    · exact (hij (add_right_cancel hiss)).elim
    exact (hq.2 j (i + 1) hisj hiss).le
  apply edgeTurn_pos_of_mem_openSegment hp hi0 his0
  by_cases his : i = j + 1
  · right
    apply hq.2
    · subst i
      fin_cases j <;> decide
    · subst i
      exact fin4_succ_ne (j + 1)
  · left
    exact hq.2 j i hij his

/-- Points of `B` in the quadrilateral, excluding its four vertices. -/
noncomputable def quadInteriorPoints
    (B : Finset Point) (q : Fin 4 → Point) : Finset Point := by
  classical
  exact B.filter fun p ↦ p ∈ quadrilateralHull q ∧ p ∉ Set.range q

@[simp] theorem mem_quadInteriorPoints
    {B : Finset Point} {q : Fin 4 → Point} {p : Point} :
    p ∈ quadInteriorPoints B q ↔
      p ∈ B ∧ p ∈ quadrilateralHull q ∧ p ∉ Set.range q := by
  classical
  simp [quadInteriorPoints, and_assoc]

theorem quadInteriorPoints_subset (B : Finset Point) (q : Fin 4 → Point) :
    quadInteriorPoints B q ⊆ B := by
  intro p hp
  exact (mem_quadInteriorPoints.mp hp).1

/-- A quadrilateral vertex cannot lie between two nonvertex points of its
hull in a set with no four collinear points. -/
theorem quadVertex_not_between_hull_points
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    (hqB : ∀ i, q i ∈ B) {x y : Point}
    (hxB : x ∈ B) (hyB : y ∈ B)
    (hxHull : x ∈ quadrilateralHull q)
    (hyHull : y ∈ quadrilateralHull q)
    (hxNot : x ∉ Set.range q) (hyNot : y ∉ Set.range q)
    (hxy : x ≠ y) (i : Fin 4) :
    q i ∉ openSegment ℝ x y := by
  intro hi
  have hx0 := quad_edgeTurn_nonneg_of_mem_convexHull hq hxHull i
  have hy0 := quad_edgeTurn_nonneg_of_mem_convexHull hq hyHull i
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := q i) (b := q (i + 1)) hi
  have hz : turn (q i) (q (i + 1)) (q i) = 0 := by simp
  have hxz : turn (q i) (q (i + 1)) x = 0 := by
    rw [hz] at heq
    nlinarith
  have hyz : turn (q i) (q (i + 1)) y = 0 := by
    rw [hz] at heq
    nlinarith
  have hisucc : q i ≠ q (i + 1) := hq.1.ne (fin4_succ_ne i).symm
  have hxi : x ≠ q i := fun e ↦ hxNot ⟨i, e.symm⟩
  have hxis : x ≠ q (i + 1) := fun e ↦ hxNot ⟨i + 1, e.symm⟩
  have hyi : y ≠ q i := fun e ↦ hyNot ⟨i, e.symm⟩
  have hyis : y ≠ q (i + 1) := fun e ↦ hyNot ⟨i + 1, e.symm⟩
  have hno := noTwoZero_of_noFour hfour (hqB i) (hqB (i + 1)) hxB hyB
    hisucc hxi.symm hyi.symm hxis.symm hyis.symm hxy
  exact hno.1 ⟨hxz, hyz⟩

/-- The four side blockers and one diagonal blocker give five distinct
nonvertex points in a monochromatic convex quadrilateral. -/
theorem five_le_quadInteriorPoints_card
    {k : ℕ} {B : Finset Point} (colour : B → Fin k)
    (hproper : ProperBlocking B colour) (c : Fin k)
    (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c) :
    5 ≤ (quadInteriorPoints B fun i ↦ (q i : Point)).card := by
  classical
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hq.1
    exact congrArg Subtype.val hij
  have hblock : ∀ i j : Fin 4, i ≠ j →
      ∃ r : B, (r : Point) ∈ openSegment ℝ (q i : Point) (q j : Point) := by
    intro i j hij
    apply hproper (q i) (q j) (hqinj.ne hij)
    exact (hmono i).trans (hmono j).symm
  choose r hr using hblock
  let y : Fin 4 → B := fun i ↦ r i (i + 1) (fin4_succ_ne i).symm
  let z : B := r 0 2 (by decide)
  let R := quadInteriorPoints B fun i ↦ (q i : Point)
  have hyseg (i : Fin 4) :
      (y i : Point) ∈ openSegment ℝ (q i : Point) (q (i + 1) : Point) :=
    hr i (i + 1) (fin4_succ_ne i).symm
  have hzseg : (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point) :=
    hr 0 2 (by decide)
  have hyR (i : Fin 4) : (y i : Point) ∈ R := by
    apply mem_quadInteriorPoints.mpr
    refine ⟨(y i).property, ?_, ?_⟩
    · exact (segment_subset_convexHull
        (Set.mem_range_self i) (Set.mem_range_self (i + 1)))
        (openSegment_subset_segment ℝ _ _ (hyseg i))
    · rintro ⟨j, hj⟩
      exact quadVertex_not_between_quadVertices hq (fin4_succ_ne i).symm j
        (by simpa only [hj] using hyseg i)
  have hzR : (z : Point) ∈ R := by
    apply mem_quadInteriorPoints.mpr
    refine ⟨z.property, ?_, ?_⟩
    · exact (segment_subset_convexHull
        (Set.mem_range_self (0 : Fin 4)) (Set.mem_range_self (2 : Fin 4)))
        (openSegment_subset_segment ℝ _ _ hzseg)
    · rintro ⟨j, hj⟩
      exact quadVertex_not_between_quadVertices hq (by decide : (0 : Fin 4) ≠ 2) j
        (by simpa only [hj] using hzseg)
  have hyinj : Function.Injective y := by
    intro i j hij
    by_contra hne
    exact (Set.disjoint_left.mp (quad_side_openSegments_disjoint hq hne))
      (hyseg i) (by simpa only [hij] using hyseg j)
  have hzy (i : Fin 4) : z ≠ y i := by
    intro hzy
    have hzero : turn (q i : Point) (q (i + 1) : Point) (z : Point) = 0 := by
      rw [hzy, turn_swap_last,
        turn_eq_zero_of_mem_openSegment (hyseg i), neg_zero]
    have hpos := quad_diagonalPoint_edgeTurn_pos hq
      (by decide : (0 : Fin 4) ≠ 2) (by decide) (by decide) hzseg i
    linarith
  let f : Sum (Fin 4) (Fin 1) → R
    | .inl i => ⟨y i, hyR i⟩
    | .inr _ => ⟨z, hzR⟩
  have hf : Function.Injective f := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · have hval : (y i : Point) = (y j : Point) := by
        simpa [f] using congrArg Subtype.val hij
      exact congrArg Sum.inl (hyinj (Subtype.ext hval))
    · have hval : (y i : Point) = (z : Point) := by
        simpa [f] using congrArg Subtype.val hij
      exact (hzy i (Subtype.ext hval.symm)).elim
    · have hval : (z : Point) = (y j : Point) := by
        simpa [f] using congrArg Subtype.val hij
      exact (hzy j (Subtype.ext hval)).elim
    · exact congrArg Sum.inr (Subsingleton.elim i j)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [R] using hcard

private theorem other_quad_colours_card (c : Fin 4) :
    Fintype.card {d : Fin 4 // d ≠ c} = 3 := by
  classical
  change Fintype.card {d : Fin 4 // ¬d = c} = 3
  rw [Fintype.card_subtype_compl (fun d : Fin 4 ↦ d = c),
    Fintype.card_subtype_eq]
  simp

noncomputable def otherQuadColourEquiv (c : Fin 4) :
    {d : Fin 4 // d ≠ c} ≃ Fin 3 :=
  (Fintype.equivFin {d : Fin 4 // d ≠ c}).trans
    (finCongr (other_quad_colours_card c))

/-- Removing a monochromatic quadrilateral from its hull leaves a blocking
configuration using the other three colours. -/
theorem quadInteriorPoints_proper_three_colouring
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i) :
    ∃ colR : (quadInteriorPoints B fun i ↦ (q i : Point)) → Fin 3,
      ProperBlocking (quadInteriorPoints B fun i ↦ (q i : Point)) colR := by
  classical
  let R := quadInteriorPoints B fun i ↦ (q i : Point)
  let lift : R → B := fun p ↦
    ⟨p, quadInteriorPoints_subset B (fun i ↦ (q i : Point)) p.property⟩
  have hlift_val (p : R) : (lift p : Point) = (p : Point) := rfl
  have hnotc (p : R) : colour (lift p) ≠ c := by
    intro hp
    obtain ⟨i, hi⟩ := hclass (lift p)
      (mem_quadInteriorPoints.mp p.property).2.1 hp
    have hrange : (p : Point) ∈ Set.range (fun i ↦ (q i : Point)) := by
      exact ⟨i, (congrArg Subtype.val hi).symm⟩
    exact (mem_quadInteriorPoints.mp p.property).2.2 hrange
  let colR : R → Fin 3 := fun p ↦
    otherQuadColourEquiv c ⟨colour (lift p), hnotc p⟩
  refine ⟨colR, ?_⟩
  intro x y hxy hcol
  have hliftxy : lift x ≠ lift y := by
    intro h
    apply hxy
    apply Subtype.ext
    simpa [lift] using congrArg Subtype.val h
  have hsame : colour (lift x) = colour (lift y) := by
    have hsub :
        (⟨colour (lift x), hnotc x⟩ : {d : Fin 4 // d ≠ c}) =
        ⟨colour (lift y), hnotc y⟩ := by
      apply (otherQuadColourEquiv c).injective
      exact hcol
    exact congrArg Subtype.val hsub
  obtain ⟨z, hz⟩ := hproper (lift x) (lift y) hliftxy hsame
  have hxdata := mem_quadInteriorPoints.mp x.property
  have hydata := mem_quadInteriorPoints.mp y.property
  have hzHull : (z : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) :=
    (convex_convexHull ℝ (Set.range fun i ↦ (q i : Point))).openSegment_subset
      hxdata.2.1 hydata.2.1 hz
  have hzNot : (z : Point) ∉ Set.range (fun i ↦ (q i : Point)) := by
    rintro ⟨i, hi⟩
    apply quadVertex_not_between_hull_points hfour hq (fun i ↦ (q i).property)
      hxdata.1 hydata.1 hxdata.2.1 hydata.2.1 hxdata.2.2 hydata.2.2
      (Subtype.val_injective.ne hxy) i
    simpa only [hi, hlift_val] using hz
  let zR : R :=
    ⟨z, mem_quadInteriorPoints.mpr ⟨z.property, hzHull, hzNot⟩⟩
  refine ⟨zR, ?_⟩
  simpa [zR, lift] using hz

/-- If the displayed quadrilateral is exactly one colour class, the points
inside it form a properly three-coloured blocking set. -/
theorem quadInteriorPoints_card_le_six
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i) :
    (quadInteriorPoints B fun i ↦ (q i : Point)).card ≤ 6 := by
  classical
  let R := quadInteriorPoints B fun i ↦ (q i : Point)
  let lift : R → B := fun p ↦
    ⟨p, quadInteriorPoints_subset B (fun i ↦ (q i : Point)) p.property⟩
  have hlift_val (p : R) : (lift p : Point) = (p : Point) := rfl
  have hnotc (p : R) : colour (lift p) ≠ c := by
    intro hp
    obtain ⟨i, hi⟩ := hclass (lift p)
      (mem_quadInteriorPoints.mp p.property).2.1 hp
    have hrange : (p : Point) ∈ Set.range (fun i ↦ (q i : Point)) := by
      exact ⟨i, (congrArg Subtype.val hi).symm⟩
    exact (mem_quadInteriorPoints.mp p.property).2.2 hrange
  let colR : R → Fin 3 := fun p ↦
    otherQuadColourEquiv c ⟨colour (lift p), hnotc p⟩
  have hfourR : ¬HasFourCollinear R := by
    intro h4
    apply hfour
    exact Lax56Proofs.HKBHexGeometry.hasFourCollinear_mono
      (quadInteriorPoints_subset B (fun i ↦ (q i : Point))) h4
  apply card_le_six_of_three_coloured_blocking R hfourR colR
  intro x y hxy hcol
  have hliftxy : lift x ≠ lift y := by
    intro h
    apply hxy
    apply Subtype.ext
    simpa [lift] using congrArg Subtype.val h
  have hsame : colour (lift x) = colour (lift y) := by
    have hsub :
        (⟨colour (lift x), hnotc x⟩ : {d : Fin 4 // d ≠ c}) =
        ⟨colour (lift y), hnotc y⟩ := by
      apply (otherQuadColourEquiv c).injective
      exact hcol
    exact congrArg Subtype.val hsub
  obtain ⟨z, hz⟩ := hproper (lift x) (lift y) hliftxy hsame
  have hxdata := mem_quadInteriorPoints.mp x.property
  have hydata := mem_quadInteriorPoints.mp y.property
  have hzHull : (z : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) :=
    (convex_convexHull ℝ (Set.range fun i ↦ (q i : Point))).openSegment_subset
      hxdata.2.1 hydata.2.1 hz
  have hzNot : (z : Point) ∉ Set.range (fun i ↦ (q i : Point)) := by
    rintro ⟨i, hi⟩
    apply quadVertex_not_between_hull_points hfour hq (fun i ↦ (q i).property)
      hxdata.1 hydata.1 hxdata.2.1 hydata.2.1 hxdata.2.2 hydata.2.2
      (Subtype.val_injective.ne hxy) i
    simpa only [hi, hlift_val] using hz
  let zR : R :=
    ⟨z, mem_quadInteriorPoints.mpr ⟨z.property, hzHull, hzNot⟩⟩
  refine ⟨zR, ?_⟩
  simpa [zR, lift] using hz

/-- A selected point on a quadrilateral side is the only nonvertex point of
the ambient no-four-collinear set on that supporting line. -/
theorem quad_edgeTurn_eq_zero_iff_eq_sidePoint
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    (hqB : ∀ i, q i ∈ B) {i : Fin 4} {y p : Point}
    (hyR : y ∈ quadInteriorPoints B q)
    (hyseg : y ∈ openSegment ℝ (q i) (q (i + 1)))
    (hpR : p ∈ quadInteriorPoints B q) :
    turn (q i) (q (i + 1)) p = 0 ↔ p = y := by
  have hydata := mem_quadInteriorPoints.mp hyR
  have hpdata := mem_quadInteriorPoints.mp hpR
  have hisucc : q i ≠ q (i + 1) := hq.1.ne (fin4_succ_ne i).symm
  have hpi : p ≠ q i := fun e ↦ hpdata.2.2 ⟨i, e.symm⟩
  have hpis : p ≠ q (i + 1) := fun e ↦ hpdata.2.2 ⟨i + 1, e.symm⟩
  have hyi : y ≠ q i := fun e ↦ hydata.2.2 ⟨i, e.symm⟩
  have hyis : y ≠ q (i + 1) := fun e ↦ hydata.2.2 ⟨i + 1, e.symm⟩
  constructor
  · intro hpzero
    exact third_point_unique hfour (hqB i) (hqB (i + 1))
      hpdata.1 hydata.1 hisucc hpi hpis hyi hyis
      (mem_line_of_turn_eq_zero hisucc hpzero)
      (mem_affineSpan_pair_of_mem_openSegment hyseg)
  · rintro rfl
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hyseg, neg_zero]

/-- The exposed side point is the entire zero face of the hull of the
nonvertex points. -/
theorem eq_sidePoint_of_mem_convexHull_turn_zero
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    (hqB : ∀ i, q i ∈ B) {i : Fin 4} {y x : Point}
    (hyR : y ∈ quadInteriorPoints B q)
    (hyseg : y ∈ openSegment ℝ (q i) (q (i + 1)))
    (hx : x ∈ convexHull ℝ
      (quadInteriorPoints B q : Set Point))
    (hxzero : turn (q i) (q (i + 1)) x = 0) :
    x = y := by
  classical
  let R := quadInteriorPoints B q
  obtain ⟨w, hw0, hw1, hwcenter⟩ := (Finset.mem_convexHull').mp hx
  have hturn0 : ∀ p ∈ R, 0 ≤ turn (q i) (q (i + 1)) p := by
    intro p hp
    exact quad_edgeTurn_nonneg_of_mem_convexHull hq
      (mem_quadInteriorPoints.mp hp).2.1 i
  have hwzero : ∀ p ∈ R, p ≠ y → w p = 0 := by
    intro p hp hpne
    have hpturn : 0 < turn (q i) (q (i + 1)) p := by
      have hnzero : turn (q i) (q (i + 1)) p ≠ 0 := by
        intro hz
        exact hpne ((quad_edgeTurn_eq_zero_iff_eq_sidePoint
          hfour hq hqB hyR hyseg hp).mp hz)
      exact lt_of_le_of_ne (hturn0 p hp) (Ne.symm hnzero)
    exact weight_eq_zero_of_turn_pos (q i) (q (i + 1)) x R w
      hw0 hw1 hwcenter hxzero hturn0 hp hpturn
  have hwy : w y = 1 := by
    have hsum := hw1
    rw [Finset.sum_eq_single y] at hsum
    · exact hsum
    · intro p hp hpne
      exact hwzero p hp hpne
    · exact fun hy ↦ (hy hyR).elim
  rw [← hwcenter]
  calc
    (∑ p ∈ R, w p • p) = w y • y := by
      apply Finset.sum_eq_single y
      · intro p hp hpne
        rw [hwzero p hp hpne, zero_smul]
      · intro hy
        exact (hy hyR).elim
    _ = y := by rw [hwy, one_smul]

/-- Each selected side blocker is an extreme point of the convex hull of all
nonvertex points in the quadrilateral. -/
theorem quad_sidePoint_mem_extremePoints
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    (hqB : ∀ i, q i ∈ B) {i : Fin 4} {y : Point}
    (hyR : y ∈ quadInteriorPoints B q)
    (hyseg : y ∈ openSegment ℝ (q i) (q (i + 1))) :
    y ∈ (convexHull ℝ
      (quadInteriorPoints B q : Set Point)).extremePoints ℝ := by
  let R := quadInteriorPoints B q
  refine ⟨subset_convexHull ℝ (R : Set Point) hyR, ?_⟩
  intro a ha b hb hyab
  have hRquad : (R : Set Point) ⊆ quadrilateralHull q := by
    intro p hp
    exact (mem_quadInteriorPoints.mp hp).2.1
  have hquadConv : Convex ℝ (quadrilateralHull q) :=
    convex_convexHull ℝ (Set.range q)
  have haQuad : a ∈ quadrilateralHull q :=
    convexHull_min hRquad hquadConv ha
  have hbQuad : b ∈ quadrilateralHull q :=
    convexHull_min hRquad hquadConv hb
  have ha0 : 0 ≤ turn (q i) (q (i + 1)) a :=
    quad_edgeTurn_nonneg_of_mem_convexHull hq haQuad i
  have hb0 : 0 ≤ turn (q i) (q (i + 1)) b :=
    quad_edgeTurn_nonneg_of_mem_convexHull hq hbQuad i
  have hy0 : turn (q i) (q (i + 1)) y = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hyseg, neg_zero]
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := q i) (b := q (i + 1)) hyab
  have haZero : turn (q i) (q (i + 1)) a = 0 := by
    rw [hy0] at heq
    nlinarith
  exact eq_sidePoint_of_mem_convexHull_turn_zero
    hfour hq hqB hyR hyseg ha haZero

/-- The six-point alternative in Lemma 6.4 is impossible: its four side
blockers would be four distinct extreme points, whereas a properly
three-coloured six-point blocking set has at most three. -/
theorem quadInteriorPoints_card_ne_six
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i) :
    (quadInteriorPoints B fun i ↦ (q i : Point)).card ≠ 6 := by
  classical
  let R := quadInteriorPoints B fun i ↦ (q i : Point)
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hq.1
    exact congrArg Subtype.val hij
  have hblock : ∀ i : Fin 4,
      ∃ r : B,
        (r : Point) ∈ openSegment ℝ (q i : Point) (q (i + 1) : Point) := by
    intro i
    apply hproper (q i) (q (i + 1))
      (hqinj.ne (fin4_succ_ne i).symm)
    exact (hmono i).trans (hmono (i + 1)).symm
  choose y hyseg using hblock
  have hyR (i : Fin 4) : (y i : Point) ∈ R := by
    apply mem_quadInteriorPoints.mpr
    refine ⟨(y i).property, ?_, ?_⟩
    · exact (segment_subset_convexHull
        (Set.mem_range_self i) (Set.mem_range_self (i + 1)))
        (openSegment_subset_segment ℝ _ _ (hyseg i))
    · rintro ⟨j, hj⟩
      exact quadVertex_not_between_quadVertices hq (fin4_succ_ne i).symm j
        (by simpa only [hj] using hyseg i)
  have hyinjPoint : Function.Injective (fun i ↦ (y i : Point)) := by
    intro i j hij
    by_contra hne
    exact (Set.disjoint_left.mp (quad_side_openSegments_disjoint hq hne))
      (hyseg i) (by simpa only [hij] using hyseg j)
  have hfourR : ¬HasFourCollinear R := by
    intro h4
    apply hfour
    exact Lax56Proofs.HKBHexGeometry.hasFourCollinear_mono
      (quadInteriorPoints_subset B (fun i ↦ (q i : Point))) h4
  obtain ⟨colR, hproperR⟩ :=
    quadInteriorPoints_proper_three_colouring
      hfour colour hproper c q hq hclass
  intro hcard
  obtain ⟨x₀, x₁, x₂, hext⟩ :=
    extremePoints_subset_three_of_card_eq_six R hcard hfourR colR hproperR
  have hyext (i : Fin 4) :
      (y i : Point) ∈ (convexHull ℝ (R : Set Point)).extremePoints ℝ := by
    exact quad_sidePoint_mem_extremePoints hfour hq
      (fun i ↦ (q i).property) (hyR i) (hyseg i)
  let Y : Finset Point :=
    (Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)
  have hYcard : Y.card = 4 := by
    change ((Finset.univ : Finset (Fin 4)).image
      (fun i ↦ (y i : Point))).card = 4
    rw [Finset.card_image_of_injective _ hyinjPoint]
    simp
  let X : Finset Point := {(x₀ : Point), (x₁ : Point), (x₂ : Point)}
  have hYX : Y ⊆ X := by
    intro p hp
    change p ∈ (Finset.univ : Finset (Fin 4)).image
      (fun i ↦ (y i : Point)) at hp
    rw [Finset.mem_image] at hp
    obtain ⟨i, -, rfl⟩ := hp
    have hi := hext (hyext i)
    simpa [X] using hi
  have hXcard : X.card ≤ 3 := by
    dsimp [X]
    have h₀ := Finset.card_insert_le (x₀ : Point)
      ({(x₁ : Point), (x₂ : Point)} : Finset Point)
    have h₁ := Finset.card_insert_le (x₁ : Point)
      ({(x₂ : Point)} : Finset Point)
    simp only [Finset.card_singleton] at h₁
    omega
  have := Finset.card_le_card hYX
  omega

/-- Lemma 6.4: a monochromatic convex quadrilateral contains exactly its
four side blockers and one further nonvertex point. -/
theorem quadInteriorPoints_card_eq_five
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i) :
    (quadInteriorPoints B fun i ↦ (q i : Point)).card = 5 := by
  have hlo := five_le_quadInteriorPoints_card colour hproper c q hq hmono
  have hhi := quadInteriorPoints_card_le_six
    hfour colour hproper c q hq hclass
  have hne := quadInteriorPoints_card_ne_six
    hfour colour hproper c q hq hmono hclass
  omega

/-- Incidence core of Lemma 6.5: the unique fifth nonvertex point blocks
both diagonals. -/
theorem exists_quad_sideBlockers_and_common_diagonalBlocker
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i) :
    ∃ y : Fin 4 → B, ∃ z : B,
      (∀ i, (y i : Point) ∈
        openSegment ℝ (q i : Point) (q (i + 1) : Point)) ∧
      (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point) ∧
      (z : Point) ∈ openSegment ℝ (q 1 : Point) (q 3 : Point) ∧
      Function.Injective (fun i ↦ (y i : Point)) ∧
      ∀ i, (z : Point) ≠ (y i : Point) := by
  classical
  let R := quadInteriorPoints B fun i ↦ (q i : Point)
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hq.1
    exact congrArg Subtype.val hij
  have hblock : ∀ i j : Fin 4, i ≠ j →
      ∃ r : B,
        (r : Point) ∈ openSegment ℝ (q i : Point) (q j : Point) := by
    intro i j hij
    apply hproper (q i) (q j) (hqinj.ne hij)
    exact (hmono i).trans (hmono j).symm
  choose r hr using hblock
  let y : Fin 4 → B := fun i ↦ r i (i + 1) (fin4_succ_ne i).symm
  let z₀ : B := r 0 2 (by decide)
  let z₁ : B := r 1 3 (by decide)
  have hyseg (i : Fin 4) :
      (y i : Point) ∈ openSegment ℝ (q i : Point) (q (i + 1) : Point) :=
    hr i (i + 1) (fin4_succ_ne i).symm
  have hz₀seg : (z₀ : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point) :=
    hr 0 2 (by decide)
  have hz₁seg : (z₁ : Point) ∈ openSegment ℝ (q 1 : Point) (q 3 : Point) :=
    hr 1 3 (by decide)
  have pointInR {i j : Fin 4} (hij : i ≠ j) {p : B}
      (hp : (p : Point) ∈ openSegment ℝ (q i : Point) (q j : Point)) :
      (p : Point) ∈ R := by
    apply mem_quadInteriorPoints.mpr
    refine ⟨p.property, ?_, ?_⟩
    · exact (segment_subset_convexHull
        (Set.mem_range_self i) (Set.mem_range_self j))
        (openSegment_subset_segment ℝ _ _ hp)
    · rintro ⟨k, hk⟩
      exact quadVertex_not_between_quadVertices hq hij k
        (by simpa only [hk] using hp)
  have hyR (i : Fin 4) : (y i : Point) ∈ R :=
    pointInR (fin4_succ_ne i).symm (hyseg i)
  have hz₀R : (z₀ : Point) ∈ R := pointInR (by decide) hz₀seg
  have hz₁R : (z₁ : Point) ∈ R := pointInR (by decide) hz₁seg
  have hyinj : Function.Injective (fun i ↦ (y i : Point)) := by
    intro i j hij
    by_contra hne
    exact (Set.disjoint_left.mp (quad_side_openSegments_disjoint hq hne))
      (hyseg i) (by simpa only [hij] using hyseg j)
  have hz₀y (i : Fin 4) : (z₀ : Point) ≠ (y i : Point) := by
    intro heq
    have hzero : turn (q i : Point) (q (i + 1) : Point) (z₀ : Point) = 0 := by
      rw [heq, turn_swap_last,
        turn_eq_zero_of_mem_openSegment (hyseg i), neg_zero]
    have hpos := quad_diagonalPoint_edgeTurn_pos hq
      (by decide : (0 : Fin 4) ≠ 2) (by decide) (by decide) hz₀seg i
    linarith
  have hz₁y (i : Fin 4) : (z₁ : Point) ≠ (y i : Point) := by
    intro heq
    have hzero : turn (q i : Point) (q (i + 1) : Point) (z₁ : Point) = 0 := by
      rw [heq, turn_swap_last,
        turn_eq_zero_of_mem_openSegment (hyseg i), neg_zero]
    have hpos := quad_diagonalPoint_edgeTurn_pos hq
      (by decide : (1 : Fin 4) ≠ 3) (by decide) (by decide) hz₁seg i
    linarith
  have hz : z₀ = z₁ := by
    apply Subtype.ext
    by_contra hne
    let Y : Finset Point :=
      (Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)
    have hYcard : Y.card = 4 := by
      change ((Finset.univ : Finset (Fin 4)).image
        (fun i ↦ (y i : Point))).card = 4
      rw [Finset.card_image_of_injective _ hyinj]
      simp
    have hz₀Y : (z₀ : Point) ∉ Y := by
      intro hzmem
      change (z₀ : Point) ∈ (Finset.univ : Finset (Fin 4)).image
        (fun i ↦ (y i : Point)) at hzmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzmem
      exact hz₀y i hi.symm
    have hz₁Y : (z₁ : Point) ∉ Y := by
      intro hzmem
      change (z₁ : Point) ∈ (Finset.univ : Finset (Fin 4)).image
        (fun i ↦ (y i : Point)) at hzmem
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzmem
      exact hz₁y i hi.symm
    have hz₀insert : (z₀ : Point) ∉ insert (z₁ : Point) Y := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne, hz₀Y⟩
    let Z : Finset Point := insert (z₀ : Point) (insert (z₁ : Point) Y)
    have hZcard : Z.card = 6 := by
      change (insert (z₀ : Point) (insert (z₁ : Point) Y)).card = 6
      rw [Finset.card_insert_of_notMem hz₀insert,
        Finset.card_insert_of_notMem hz₁Y, hYcard]
    have hZR : Z ⊆ R := by
      intro p hp
      change p ∈ insert (z₀ : Point) (insert (z₁ : Point) Y) at hp
      simp only [Finset.mem_insert] at hp
      rcases hp with rfl | rfl | hp
      · exact hz₀R
      · exact hz₁R
      · change p ∈ (Finset.univ : Finset (Fin 4)).image
          (fun i ↦ (y i : Point)) at hp
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
        exact hyR i
    have hle := Finset.card_le_card hZR
    have hRcard := quadInteriorPoints_card_eq_five
      hfour colour hproper c q hq hmono hclass
    change R.card = 5 at hRcard
    omega
  refine ⟨y, z₀, hyseg, hz₀seg, ?_, hyinj, hz₀y⟩
  simpa only [hz] using hz₁seg

/-- The four side blockers together with the common diagonal blocker are all
the nonvertex points of the monochromatic quadrilateral. -/
theorem quadInteriorPoints_eq_five_pattern
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (c : Fin 4) (q : Fin 4 → B)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (hmono : ∀ i, colour (q i) = c)
    (hclass : ∀ p : B,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (q i : Point)) →
      colour p = c → ∃ i, p = q i)
    (y : Fin 4 → B) (z : B)
    (hyseg : ∀ i, (y i : Point) ∈
      openSegment ℝ (q i : Point) (q (i + 1) : Point))
    (hzseg : (z : Point) ∈ openSegment ℝ (q 0 : Point) (q 2 : Point))
    (hyinj : Function.Injective (fun i ↦ (y i : Point)))
    (hzy : ∀ i, (z : Point) ≠ (y i : Point)) :
    quadInteriorPoints B (fun i ↦ (q i : Point)) =
      insert (z : Point)
        ((Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)) := by
  classical
  let R := quadInteriorPoints B fun i ↦ (q i : Point)
  let Y : Finset Point :=
    (Finset.univ : Finset (Fin 4)).image fun i ↦ (y i : Point)
  let W : Finset Point := insert (z : Point) Y
  have pointInR {i j : Fin 4} (hij : i ≠ j) {p : B}
      (hp : (p : Point) ∈ openSegment ℝ (q i : Point) (q j : Point)) :
      (p : Point) ∈ R := by
    apply mem_quadInteriorPoints.mpr
    refine ⟨p.property, ?_, ?_⟩
    · exact (segment_subset_convexHull
        (Set.mem_range_self i) (Set.mem_range_self j))
        (openSegment_subset_segment ℝ _ _ hp)
    · rintro ⟨k, hk⟩
      exact quadVertex_not_between_quadVertices hq hij k
        (by simpa only [hk] using hp)
  have hyR (i : Fin 4) : (y i : Point) ∈ R :=
    pointInR (fin4_succ_ne i).symm (hyseg i)
  have hzR : (z : Point) ∈ R := pointInR (by decide) hzseg
  have hzY : (z : Point) ∉ Y := by
    intro hzmem
    change (z : Point) ∈ (Finset.univ : Finset (Fin 4)).image
      (fun i ↦ (y i : Point)) at hzmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hzmem
    exact hzy i hi.symm
  have hWcard : W.card = 5 := by
    change (insert (z : Point)
      ((Finset.univ : Finset (Fin 4)).image
        fun i ↦ (y i : Point))).card = 5
    rw [Finset.card_insert_of_notMem hzY,
      Finset.card_image_of_injective _ hyinj]
    simp
  have hWR : W ⊆ R := by
    intro p hp
    change p ∈ insert (z : Point)
      ((Finset.univ : Finset (Fin 4)).image
        fun i ↦ (y i : Point)) at hp
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact hzR
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact hyR i
  have hRcard := quadInteriorPoints_card_eq_five
    hfour colour hproper c q hq hmono hclass
  change R.card = 5 at hRcard
  have hWR_eq : W = R := by
    apply Finset.eq_of_subset_of_card_le hWR
    omega
  exact hWR_eq.symm

end Lax56Proofs.HKBQuadrilateral
