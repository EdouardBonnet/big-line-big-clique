import Lax56.HujterKisfaludiBak
import Lax56Proofs.Orientation
import Mathlib.Tactic

/-!
Elementary convexity facts used to pass from an empty convex hexagon to the
finite sign certificates in the Hujter--Kisfaludi-Bak argument.
-/

namespace Lax56Proofs.HKBGeometry

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.OrderGeometry
open Lax56Proofs.Orientation

@[simp] theorem turn_self_left (a b : Point) : turn a b a = 0 := by
  simp [turn]

@[simp] theorem turn_self_right (a b : Point) : turn a b b = 0 := by
  simp [turn]
  ring_nf

theorem turn_convex_combo (a b x y : Point) (u v : ℝ) (huv : u + v = 1) :
    turn a b (u • x + v • y) = u * turn a b x + v * turn a b y := by
  have hv : v = 1 - u := by linarith
  subst v
  simp [turn]
  ring

/-- Every point of the convex hull is in each of the six closed half-planes
cut out by the oriented sides of a strict convex hexagon. -/
theorem edgeTurn_nonneg_of_mem_convexHull
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {p : Point} (hp : p ∈ convexHull ℝ (Set.range h)) (i : Fin 6) :
    0 ≤ turn (h i) (h (i + 1)) p := by
  let S : Set Point := {q | 0 ≤ turn (h i) (h (i + 1)) q}
  have hconv : Convex ℝ S := by
    intro x hx y hy u v hu hv huv
    change 0 ≤ turn (h i) (h (i + 1)) (u • x + v • y)
    rw [turn_convex_combo _ _ _ _ _ _ huv]
    exact add_nonneg (mul_nonneg hu hx) (mul_nonneg hv hy)
  have hrange : Set.range h ⊆ S := by
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · subst j
      simp [S]
    by_cases hjs : j = i + 1
    · subst j
      simp [S]
    exact (hh.2.1 i j hji hjs).le
  exact convexHull_min hrange hconv hp

/-- An open-segment point is the strict convex combination used below. -/
theorem turn_of_mem_openSegment
    {a b x y p : Point} (hp : p ∈ openSegment ℝ x y) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      turn a b p = (1 - t) * turn a b x + t * turn a b y := by
  rw [openSegment_eq_image] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  refine ⟨t, ht.1, ht.2, ?_⟩
  simp [AffineMap.lineMap_apply, turn]
  ring

/-- A point strictly between two points of the closed hexagon is strictly
inside every side half-plane as soon as one endpoint is strict there. -/
theorem edgeTurn_pos_of_mem_openSegment
    {a b x y p : Point} (hp : p ∈ openSegment ℝ x y)
    (hx : 0 ≤ turn a b x) (hy : 0 ≤ turn a b y)
    (hstrict : 0 < turn a b x ∨ 0 < turn a b y) :
    0 < turn a b p := by
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment hp
  rw [heq]
  rcases hstrict with hx' | hy'
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr ht1) hx') (mul_nonneg ht.le hy)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr ht1.le) hx) (mul_pos ht hy')

/-- Every point on a non-side chord of a strict convex hexagon is strict in
all six side half-planes. -/
theorem diagonalPoint_edgeTurn_pos
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {j k : Fin 6} (hjk : j ≠ k)
    (hnbr : k ≠ j + 1) (hnbr' : j ≠ k + 1)
    {p : Point} (hp : p ∈ openSegment ℝ (h j) (h k)) (i : Fin 6) :
    0 < turn (h i) (h (i + 1)) p := by
  have hj0 : 0 ≤ turn (h i) (h (i + 1)) (h j) := by
    by_cases hji : j = i
    · subst j
      simp
    by_cases hjs : j = i + 1
    · subst j
      simp
    exact (hh.2.1 i j hji hjs).le
  have hk0 : 0 ≤ turn (h i) (h (i + 1)) (h k) := by
    by_cases hki : k = i
    · subst k
      simp
    by_cases hks : k = i + 1
    · subst k
      simp
    exact (hh.2.1 i k hki hks).le
  apply edgeTurn_pos_of_mem_openSegment hp hj0 hk0
  by_contra hnot
  push_neg at hnot
  have hjz : turn (h i) (h (i + 1)) (h j) = 0 := le_antisymm hnot.1 hj0
  have hkz : turn (h i) (h (i + 1)) (h k) = 0 := le_antisymm hnot.2 hk0
  have hjend : j = i ∨ j = i + 1 := by
    by_contra hj
    push_neg at hj
    exact (ne_of_gt (hh.2.1 i j hj.1 hj.2)) hjz
  have hkend : k = i ∨ k = i + 1 := by
    by_contra hk
    push_neg at hk
    exact (ne_of_gt (hh.2.1 i k hk.1 hk.2)) hkz
  rcases hjend with rfl | rfl <;> rcases hkend with rfl | rfl
  · exact hjk rfl
  · exact hnbr rfl
  · exact hnbr' rfl
  · exact hjk rfl

private theorem fin6_succ_ne (i : Fin 6) : i + 1 ≠ i := by
  fin_cases i <;> decide

/-- No vertex of a strict convex hexagon lies in the open segment between
two other vertices. -/
theorem hexVertex_not_between_hexVertices
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {i j : Fin 6} (hij : i ≠ j) (k : Fin 6) :
    h k ∉ openSegment ℝ (h i) (h j) := by
  intro hk
  have hi0 : 0 ≤ turn (h k) (h (k + 1)) (h i) := by
    by_cases hik : i = k
    · subst i; simp
    by_cases his : i = k + 1
    · subst i; simp
    exact (hh.2.1 k i hik his).le
  have hj0 : 0 ≤ turn (h k) (h (k + 1)) (h j) := by
    by_cases hjk : j = k
    · subst j; simp
    by_cases hjs : j = k + 1
    · subst j; simp
    exact (hh.2.1 k j hjk hjs).le
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := h k) (b := h (k + 1)) hk
  have hiz : turn (h k) (h (k + 1)) (h i) = 0 := by
    have : turn (h k) (h (k + 1)) (h k) = 0 := by simp
    rw [this] at heq
    nlinarith
  have hjz : turn (h k) (h (k + 1)) (h j) = 0 := by
    have : turn (h k) (h (k + 1)) (h k) = 0 := by simp
    rw [this] at heq
    nlinarith
  have hiend : i = k ∨ i = k + 1 := by
    by_contra hi
    push Not at hi
    exact (ne_of_gt (hh.2.1 k i hi.1 hi.2)) hiz
  have hjend : j = k ∨ j = k + 1 := by
    by_contra hj
    push Not at hj
    exact (ne_of_gt (hh.2.1 k j hj.1 hj.2)) hjz
  rcases hiend with hik | his
  · rcases hjend with hjk | hjs
    · exact hij (hik.trans hjk.symm)
    · have hk' : h k ∈ openSegment ℝ (h k) (h (k + 1)) := by
        simpa [hik, hjs] using hk
      exact (hh.1.ne (fin6_succ_ne k).symm)
        ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hk')
  · rcases hjend with hjk | hjs
    · have hk' : h k ∈ openSegment ℝ (h (k + 1)) (h k) := by
        simpa [his, hjk] using hk
      exact (hh.1.ne (fin6_succ_ne k).symm)
        ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hk').symm
    · exact hij (his.trans hjs.symm)

/-- The relative interiors of two distinct sides of a strict convex hexagon
are disjoint. -/
theorem side_openSegments_disjoint
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (openSegment ℝ (h i) (h (i + 1)))
      (openSegment ℝ (h j) (h (j + 1))) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have hj0 : 0 ≤ turn (h i) (h (i + 1)) (h j) := by
    by_cases hji : j = i
    · exact (hij hji.symm).elim
    by_cases hjs : j = i + 1
    · subst j; simp
    exact (hh.2.1 i j hji hjs).le
  have hjs0 : 0 ≤ turn (h i) (h (i + 1)) (h (j + 1)) := by
    by_cases hji : j + 1 = i
    · subst i; simp
    by_cases hjs : j + 1 = i + 1
    · exact (hij (add_right_cancel hjs).symm).elim
    exact (hh.2.1 i (j + 1) hji hjs).le
  have hstrict : 0 < turn (h i) (h (i + 1)) (h j) ∨
      0 < turn (h i) (h (i + 1)) (h (j + 1)) := by
    by_cases hji : j = i
    · exact (hij hji.symm).elim
    by_cases hjs : j = i + 1
    · right
      apply hh.2.1
      · subst j
        fin_cases i <;> decide
      · subst j
        exact fin6_succ_ne (i + 1)
    exact Or.inl (hh.2.1 i j hji hjs)
  have hpPos := edgeTurn_pos_of_mem_openSegment hpj hj0 hjs0 hstrict
  have hpZero : turn (h i) (h (i + 1)) p = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hpi, neg_zero]
  linarith

/-- A vertex of a strict convex hexagon cannot lie strictly between two
other points of its convex hull which, together with the hexagon, belong to a
set having no four collinear points. -/
theorem hexVertex_not_between_hull_points
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P) {x y : Point}
    (hxP : x ∈ P) (hyP : y ∈ P)
    (hxHull : x ∈ convexHull ℝ (Set.range h))
    (hyHull : y ∈ convexHull ℝ (Set.range h))
    (hxNot : x ∉ Set.range h) (hyNot : y ∉ Set.range h)
    (hxy : x ≠ y) (i : Fin 6) :
    h i ∉ openSegment ℝ x y := by
  intro hi
  have hx0 := edgeTurn_nonneg_of_mem_convexHull hh hxHull i
  have hy0 := edgeTurn_nonneg_of_mem_convexHull hh hyHull i
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := h i) (b := h (i + 1)) hi
  have hz : turn (h i) (h (i + 1)) (h i) = 0 := by simp
  have hxz : turn (h i) (h (i + 1)) x = 0 := by
    rw [hz] at heq
    nlinarith
  have hyz : turn (h i) (h (i + 1)) y = 0 := by
    rw [hz] at heq
    nlinarith
  have hisucc : h i ≠ h (i + 1) :=
    hh.1.ne (fin6_succ_ne i).symm
  have hxi : x ≠ h i := fun e => hxNot ⟨i, e.symm⟩
  have hxis : x ≠ h (i + 1) := fun e => hxNot ⟨i + 1, e.symm⟩
  have hyi : y ≠ h i := fun e => hyNot ⟨i, e.symm⟩
  have hyis : y ≠ h (i + 1) := fun e => hyNot ⟨i + 1, e.symm⟩
  have hno := noTwoZero_of_noFour hfour (hhP i) (hhP (i + 1)) hxP hyP
    hisucc hxi.symm hyi.symm hxis.symm hyis.symm hxy
  exact hno.1 ⟨hxz, hyz⟩

/-- Two distinct points cannot each lie strictly between the other and a
fixed third point.  The lexicographic order turns this into a one-line order
contradiction. -/
theorem not_two_mutual_openSegments {a b c : Point} (hab : a ≠ b) :
    ¬(c ∈ openSegment ℝ a b ∧ b ∈ openSegment ℝ a c) := by
  rintro ⟨hc, hb⟩
  rcases lt_or_gt_of_ne (toLex.injective.ne hab) with hab' | hba'
  · have hac := (lex_between_of_mem_openSegment hab' hc).1
    have hcb := (lex_between_of_mem_openSegment hab' hc).2
    have hbc := (lex_between_of_mem_openSegment hac hb).2
    exact lt_asymm hbc hcb
  · have hbc := (lex_between_of_mem_openSegment hba' (by
      simpa only [openSegment_symm] using hc)).1
    have hca := (lex_between_of_mem_openSegment hba' (by
      simpa only [openSegment_symm] using hc)).2
    have hcb := (lex_between_of_mem_openSegment hca (by
      simpa only [openSegment_symm] using hb)).1
    exact lt_asymm hbc hcb

end Lax56Proofs.HKBGeometry
