import Lax56Proofs.HKBColourClasses
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-!
The minimum-hull monochromatic four-set used in the direct proof of
`mc₃(4) ≤ 12`.
-/

namespace Lax56Proofs.HKBDirectCore

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBColourClasses
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBQuadrilateral
open Lax56Proofs.HKBQuadrilateralMaximal
open Lax56Proofs.HKBQuadrilateralPattern
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- Four distinct points of a finite set carrying one colour. -/
structure MonoFour (P : Finset Point) (colour : P → Fin 4) where
  point : Fin 4 → P
  injective : Function.Injective point
  mono : ∀ i, colour (point i) = colour (point 0)

noncomputable instance monoFourFintype
    (P : Finset Point) (colour : P → Fin 4) :
    Fintype (MonoFour P colour) :=
  Fintype.ofInjective MonoFour.point (by
    intro X Y h
    cases X
    cases Y
    cases h
    rfl)

noncomputable def MonoFour.hull
    {P : Finset Point} {colour : P → Fin 4}
    (X : MonoFour P colour) : Set Point :=
  convexHull ℝ (Set.range fun i ↦ (X.point i : Point))

noncomputable def MonoFour.count
    {P : Finset Point} {colour : P → Fin 4}
    (X : MonoFour P colour) : ℕ := by
  classical
  exact (P.filter fun p ↦ p ∈ X.hull).card

theorem MonoFour.vertex_mem_hull
    {P : Finset Point} {colour : P → Fin 4}
    (X : MonoFour P colour) (i : Fin 4) :
    (X.point i : Point) ∈ X.hull :=
  subset_convexHull ℝ _ (Set.mem_range_self i)

/-- Thirteen points in four colours contain a monochromatic four-set. -/
theorem exists_monoFour_of_card_eq_thirteen
    (P : Finset Point) (colour : P → Fin 4) (hcard : P.card = 13) :
    Nonempty (MonoFour P colour) := by
  classical
  have hpigeon : Fintype.card (Fin 4) * 3 < Fintype.card P := by
    simpa [hcard]
  obtain ⟨d, hd⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card colour hpigeon
  rw [Finset.three_lt_card] at hd
  obtain ⟨a, ha, b, hb, c, hc, e, he,
    hab, hac, hae, hbc, hbe, hce⟩ := hd
  have hca : colour a = d := (Finset.mem_filter.mp ha).2
  have hcb : colour b = d := (Finset.mem_filter.mp hb).2
  have hcc : colour c = d := (Finset.mem_filter.mp hc).2
  have hce' : colour e = d := (Finset.mem_filter.mp he).2
  clear ha hb hc he
  let x : Fin 4 → P := ![a, b, c, e]
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x]
  refine ⟨⟨x, hx, ?_⟩⟩
  intro i
  fin_cases i <;> simp [x, hca, hcb, hcc, hce']

/-- Choose a monochromatic four-set whose closed hull contains as few
ambient points as possible. -/
theorem exists_minimal_monoFour
    (P : Finset Point) (colour : P → Fin 4)
    (hX : Nonempty (MonoFour P colour)) :
    ∃ X : MonoFour P colour,
      ∀ Y : MonoFour P colour, X.count ≤ Y.count := by
  classical
  let counts : Finset ℕ :=
    (Finset.univ : Finset (MonoFour P colour)).image MonoFour.count
  have hcounts : counts.Nonempty := by
    obtain ⟨X⟩ := hX
    exact ⟨X.count, Finset.mem_image.mpr ⟨X, Finset.mem_univ _, rfl⟩⟩
  let n := counts.min' hcounts
  have hnmem : n ∈ counts := Finset.min'_mem counts hcounts
  obtain ⟨X, -, hXn⟩ := Finset.mem_image.mp hnmem
  refine ⟨X, ?_⟩
  intro Y
  rw [hXn]
  exact Finset.min'_le counts Y.count
    (Finset.mem_image.mpr ⟨Y, Finset.mem_univ _, rfl⟩)

/-- Strict containment of the filtered ambient points strictly lowers the
minimum-hull measure. -/
theorem MonoFour.count_lt_of_hull_subset_of_point
    {P : Finset Point} {colour : P → Fin 4}
    {X Y : MonoFour P colour} (hsub : Y.hull ⊆ X.hull)
    (p : P) (hpX : (p : Point) ∈ X.hull)
    (hpY : (p : Point) ∉ Y.hull) :
    Y.count < X.count := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hsub hz.2⟩
  · intro heq
    have hpLeft : (p : Point) ∈ P.filter (fun z ↦ z ∈ X.hull) :=
      Finset.mem_filter.mpr ⟨p.property, hpX⟩
    rw [← heq] at hpLeft
    exact hpY (Finset.mem_filter.mp hpLeft).2

/-- Minimality forbids a monochromatic four-set in a proper subhull that
omits one ambient point of the chosen hull. -/
theorem no_smaller_monoFour
    {P : Finset Point} {colour : P → Fin 4}
    {X : MonoFour P colour}
    (hmin : ∀ Y : MonoFour P colour, X.count ≤ Y.count)
    (Y : MonoFour P colour) (hsub : Y.hull ⊆ X.hull)
    (p : P) (hpX : (p : Point) ∈ X.hull)
    (hpY : (p : Point) ∉ Y.hull) : False := by
  have hlt := MonoFour.count_lt_of_hull_subset_of_point
    (X := X) (Y := Y) hsub p hpX hpY
  exact (not_lt_of_ge (hmin Y)) hlt

/-- A strict half-plane cut out by the sum of two oriented-area affine
functionals is convex. -/
theorem convex_twoTurns_pos (a b c d : Point) :
    Convex ℝ {p | 0 < turn a b p + turn c d p} := by
  intro x hx y hy u v hu hv huv
  change 0 < turn a b x + turn c d x at hx
  change 0 < turn a b y + turn c d y at hy
  change 0 < turn a b (u • x + v • y) + turn c d (u • x + v • y)
  rw [turn_convex_combo _ _ _ _ _ _ huv,
    turn_convex_combo _ _ _ _ _ _ huv]
  have hrearrange :
      u * turn a b x + v * turn a b y +
          (u * turn c d x + v * turn c d y) =
        u * (turn a b x + turn c d x) +
          v * (turn a b y + turn c d y) := by ring
  rw [hrearrange]
  by_cases hu0 : u = 0
  · have hv1 : v = 1 := by linarith
    simp [hu0, hv1, hy]
  · have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    exact add_pos_of_pos_of_nonneg (mul_pos huPos hx) (mul_nonneg hv hy.le)

/-- If every generator has positive value for a sum of two turn
functionals, their convex hull cannot contain a point where the sum is
zero. -/
theorem not_mem_convexHull_range_of_twoTurns_pos
    (a b c d q : Point) (y : Fin 4 → Point)
    (hpos : ∀ i, 0 < turn a b (y i) + turn c d (y i))
    (hqzero : turn a b q + turn c d q = 0) :
    q ∉ convexHull ℝ (Set.range y) := by
  intro hq
  have hsub : Set.range y ⊆ {p | 0 < turn a b p + turn c d p} := by
    rintro _ ⟨i, rfl⟩
    exact hpos i
  have hstrict := convexHull_min hsub (convex_twoTurns_pos a b c d) hq
  change 0 < turn a b q + turn c d q at hstrict
  linarith

/-- The sum of the two supporting edge functionals at a vertex of a strict
convex quadrilateral is strictly positive at every other ambient point of
the quadrilateral. -/
theorem quad_vertex_exposing_sum_pos
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    (q : Fin 4 → P)
    (hq : StrictConvexQuadrilateral fun i ↦ (q i : Point))
    (p : P)
    (hp : (p : Point) ∈ quadrilateralHull fun i ↦ (q i : Point))
    (hp0 : p ≠ q 0) :
    0 < turn (q 0 : Point) (q 1 : Point) (p : Point) +
      turn (q 3 : Point) (q 0 : Point) (p : Point) := by
  by_cases hp1 : p = q 1
  · subst p
    have h := hq.2 3 1 (by decide) (by decide)
    simpa using h
  by_cases hp2 : p = q 2
  · subst p
    have h1 := hq.2 0 2 (by decide) (by decide)
    have h2 := hq.2 3 2 (by decide) (by decide)
    simpa using add_pos h1 h2
  by_cases hp3 : p = q 3
  · subst p
    have h := hq.2 0 3 (by decide) (by decide)
    simpa using h
  have hleft := quad_edgeTurn_nonneg_of_mem_convexHull hq hp 0
  have hright := quad_edgeTurn_nonneg_of_mem_convexHull hq hp 3
  have hleft' : 0 ≤ turn (q 0 : Point) (q 1 : Point) (p : Point) := by
    simpa using hleft
  have hright' : 0 ≤ turn (q 3 : Point) (q 0 : Point) (p : Point) := by
    simpa using hright
  have hzero : ¬(turn (q 3 : Point) (q 0 : Point) (p : Point) = 0 ∧
      turn (q 0 : Point) (q 1 : Point) (p : Point) = 0) := by
    have hn := noTwoZero_of_noFour hfour
      (q 3).property (q 0).property (q 1).property p.property
      (hq.1.ne (by decide : (3 : Fin 4) ≠ 0))
      (hq.1.ne (by decide : (3 : Fin 4) ≠ 1))
      (Subtype.val_injective.ne hp3).symm
      (hq.1.ne (by decide : (0 : Fin 4) ≠ 1))
      (Subtype.val_injective.ne hp0).symm
      (Subtype.val_injective.ne hp1).symm
    exact hn.2.2.2.2.1
  by_contra hnot
  push Not at hnot
  apply hzero
  constructor <;> linarith [hleft', hright']

/-- The analogous exposing functional at the first vertex of a positively
oriented triangle. -/
theorem triangle_vertex_exposing_sum_pos
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    (a b c p : P) (habc : 0 < turn (a : Point) (b : Point) (c : Point))
    (hp : (p : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
    (hpa : p ≠ a) :
    0 < turn (a : Point) (b : Point) (p : Point) +
      turn (c : Point) (a : Point) (p : Point) := by
  by_cases hpb : p = b
  · subst p
    simpa [turn_rotate] using habc
  by_cases hpc : p = c
  · subst p
    simpa using habc
  have hedges := triangle_edge_nonneg habc.le hp
  have hab : (a : Point) ≠ (b : Point) := by
    intro e
    rw [e] at habc
    have hz : turn (b : Point) (b : Point) (c : Point) = 0 := by
      simp [turn]
    linarith
  have hac : (a : Point) ≠ (c : Point) := by
    intro e
    rw [e] at habc
    have hz : turn (c : Point) (b : Point) (c : Point) = 0 := by
      simp [turn]
    linarith
  have hbc : (b : Point) ≠ (c : Point) := by
    intro e
    rw [e] at habc
    have hz : turn (a : Point) (c : Point) (c : Point) = 0 := by
      simp [turn]
      ring
    linarith
  have hzero : ¬(turn (c : Point) (a : Point) (p : Point) = 0 ∧
      turn (a : Point) (b : Point) (p : Point) = 0) := by
    have hn := noTwoZero_of_noFour hfour c.property a.property b.property p.property
      hac.symm hbc.symm (Subtype.val_injective.ne hpc).symm
      hab (Subtype.val_injective.ne hpa).symm
      (Subtype.val_injective.ne hpb).symm
    exact hn.2.2.2.2.1
  by_contra hnot
  push Not at hnot
  apply hzero
  constructor <;> linarith [hedges.1, hedges.2.2]

theorem MonoFour.hull_eq_of_reordering
    {P : Finset Point} {colour : P → Fin 4}
    (X : MonoFour P colour) (R : FourReordering X.point) :
    X.hull = convexHull ℝ (Set.range fun i ↦ (R.q i : Point)) := by
  apply congrArg (convexHull ℝ)
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    have hi : X.point i ∈ Set.range R.q := by
      rw [R.range_eq]
      exact Set.mem_range_self i
    obtain ⟨j, hj⟩ := hi
    exact ⟨j, congrArg Subtype.val hj⟩
  · rintro ⟨i, rfl⟩
    have hi : R.q i ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self i
    obtain ⟨j, hj⟩ := hi
    exact ⟨j, congrArg Subtype.val hj⟩

/-- No further point of the quadrilateral colour can lie in the chosen
minimum hull. -/
theorem same_colour_eq_quadVertex_of_minimal
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {X : MonoFour P colour}
    (hmin : ∀ Y : MonoFour P colour, X.count ≤ Y.count)
    (R : FourReordering X.point)
    (hq : StrictConvexQuadrilateral fun i ↦ (R.q i : Point))
    (p : P)
    (hpHull : (p : Point) ∈ quadrilateralHull fun i ↦ (R.q i : Point))
    (hpcolour : colour p = colour (R.q 0)) :
    ∃ i, p = R.q i := by
  classical
  by_contra hnot
  push Not at hnot
  have hpq (i : Fin 4) : p ≠ R.q i := fun h ↦ hnot i h
  have hqp (i : Fin 4) : R.q i ≠ p := Ne.symm (hpq i)
  have hRmono (i : Fin 4) : colour (R.q i) = colour (R.q 0) := by
    have hi : R.q i ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self i
    have hzero : R.q 0 ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self 0
    obtain ⟨j, hj⟩ := hi
    obtain ⟨k, hk⟩ := hzero
    rw [← hj, ← hk, X.mono j, X.mono k]
  let y : Fin 4 → P := ![p, R.q 1, R.q 2, R.q 3]
  have hR12 : R.q 1 ≠ R.q 2 := R.injective.ne (by decide)
  have hR13 : R.q 1 ≠ R.q 3 := R.injective.ne (by decide)
  have hR23 : R.q 2 ≠ R.q 3 := R.injective.ne (by decide)
  have hyinj : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [y, hpq, hqp, hR12, hR13, hR23]
  let Y : MonoFour P colour := ⟨y, hyinj, by
    intro i
    fin_cases i <;> simp [y, hpcolour, hRmono]⟩
  have hHullEq := X.hull_eq_of_reordering R
  have hsub : Y.hull ⊆ X.hull := by
    rw [hHullEq]
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hpHull
      · exact subset_convexHull ℝ _ (Set.mem_range_self 1)
      · exact subset_convexHull ℝ _ (Set.mem_range_self 2)
      · exact subset_convexHull ℝ _ (Set.mem_range_self 3)
    · exact convex_convexHull ℝ _
  have hy0 (i : Fin 4) : Y.point i ≠ R.q 0 := by
    fin_cases i
    · simpa [Y, y] using hpq 0
    · simpa [Y, y] using R.injective.ne (by decide : (1 : Fin 4) ≠ 0)
    · simpa [Y, y] using R.injective.ne (by decide : (2 : Fin 4) ≠ 0)
    · simpa [Y, y] using R.injective.ne (by decide : (3 : Fin 4) ≠ 0)
  have hpos (i : Fin 4) :
      0 < turn (R.q 0 : Point) (R.q 1 : Point) (Y.point i : Point) +
        turn (R.q 3 : Point) (R.q 0 : Point) (Y.point i : Point) := by
    apply quad_vertex_exposing_sum_pos hfour R.q hq
    · fin_cases i
      · exact hpHull
      · exact subset_convexHull ℝ _ (Set.mem_range_self 1)
      · exact subset_convexHull ℝ _ (Set.mem_range_self 2)
      · exact subset_convexHull ℝ _ (Set.mem_range_self 3)
    · exact hy0 i
  have hq0not : (R.q 0 : Point) ∉ Y.hull := by
    apply not_mem_convexHull_range_of_twoTurns_pos
      (R.q 0 : Point) (R.q 1 : Point) (R.q 3 : Point) (R.q 0 : Point)
      (R.q 0 : Point) (fun i ↦ (Y.point i : Point)) hpos
    simp
  exact no_smaller_monoFour hmin Y hsub (R.q 0)
    (hHullEq.symm ▸ subset_convexHull ℝ _ (Set.mem_range_self 0)) hq0not

/-- The convex alternative for the minimum monochromatic four-set is the
standard nine-point configuration and therefore cannot occur in a
thirteen-point set. -/
theorem no_thirteen_of_minimal_convex
    {P : Finset Point} (hcard : P.card = 13)
    (hfour : ¬HasFourCollinear P)
    (colour : P → Fin 4) (hproper : ProperBlocking P colour)
    (X : MonoFour P colour)
    (hmin : ∀ Y : MonoFour P colour, X.count ≤ Y.count)
    (R : FourReordering X.point)
    (hq : StrictConvexQuadrilateral fun i ↦ (R.q i : Point)) : False := by
  classical
  have hRmono (i : Fin 4) : colour (R.q i) = colour (R.q 0) := by
    have hi : R.q i ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self i
    have hzero : R.q 0 ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self 0
    obtain ⟨j, hj⟩ := hi
    obtain ⟨k, hk⟩ := hzero
    rw [← hj, ← hk, X.mono j, X.mono k]
  have hclass : ∀ p : P,
      (p : Point) ∈ quadrilateralHull (fun i ↦ (R.q i : Point)) →
      colour p = colour (R.q 0) → ∃ i, p = R.q i := by
    intro p hp hc
    exact same_colour_eq_quadVertex_of_minimal hfour hmin R hq p hp hc
  obtain ⟨pattern⟩ := exists_standardQuadrilateralPattern
    hfour colour hproper (colour (R.q 0)) R.q hq hRmono hclass
  have hmax := standardQuadrilateralPattern_maximal
    hfour colour hproper (colour (R.q 0)) R.q hq hRmono pattern
  let V : Finset Point :=
    (Finset.univ : Finset (Fin 4)).image fun i ↦ (R.q i : Point)
  let I := quadInteriorPoints P fun i ↦ (R.q i : Point)
  have hVI : P ⊆ V ∪ I := by
    intro p hp
    by_cases hpV : p ∈ Set.range (fun i ↦ (R.q i : Point))
    · apply Finset.mem_union.mpr
      left
      obtain ⟨i, rfl⟩ := hpV
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union.mpr
      right
      exact mem_quadInteriorPoints.mpr
        ⟨hp, hmax ⟨p, hp⟩, hpV⟩
  have hVcard : V.card = 4 := by
    rw [Finset.card_image_of_injective]
    · simp [V]
    · exact fun i j h ↦ R.injective (Subtype.val_injective h)
  have hIcard : I.card = 5 := by
    exact quadInteriorPoints_card_eq_five hfour colour hproper
      (colour (R.q 0)) R.q hq hRmono hclass
  have hle : P.card ≤ (V ∪ I).card := Finset.card_le_card hVI
  have hunion : (V ∪ I).card ≤ V.card + I.card := Finset.card_union_le V I
  omega

/-- In the concave alternative, the hull of the four-set is exactly the
outer triangle. -/
theorem MonoFour.hull_eq_triangle_of_reordering_inside
    {P : Finset Point} {colour : P → Fin 4}
    (X : MonoFour P colour) (R : FourReordering X.point)
    (hinside : StrictlyInsideTriangle (R.q 0 : Point) (R.q 1 : Point)
      (R.q 2 : Point) (R.q 3 : Point)) :
    X.hull = triangleHull (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point) := by
  rw [X.hull_eq_of_reordering R]
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact vertex_mem_triangleHull _ _ _
      · exact subset_convexHull ℝ _ (by simp [triangleHull])
      · exact subset_convexHull ℝ _ (by simp [triangleHull])
      · exact strictlyInsideTriangle_mem_triangleHull hinside
    · exact convex_convexHull ℝ _
  · apply convexHull_mono
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact Set.mem_range_self 0
    · exact Set.mem_range_self 1
    · exact Set.mem_range_self 2

/-- A minimum monochromatic four-hull admits no second monochromatic
four-set inside its concave outer triangle if that second set omits an outer
vertex. -/
theorem no_monoFour_in_minimal_triangle_avoiding_first
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {X : MonoFour P colour}
    (hmin : ∀ Y : MonoFour P colour, X.count ≤ Y.count)
    (R : FourReordering X.point)
    (hinside : StrictlyInsideTriangle (R.q 0 : Point) (R.q 1 : Point)
      (R.q 2 : Point) (R.q 3 : Point))
    (Y : MonoFour P colour)
    (hyHull : ∀ i, (Y.point i : Point) ∈
      triangleHull (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point))
    (hyne : ∀ i, Y.point i ≠ R.q 0) : False := by
  have hHullEq := X.hull_eq_triangle_of_reordering_inside R hinside
  have hsub : Y.hull ⊆ X.hull := by
    rw [hHullEq]
    apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact hyHull i
    · exact convex_convexHull ℝ _
  have hpos (i : Fin 4) :
      0 < turn (R.q 0 : Point) (R.q 1 : Point) (Y.point i : Point) +
        turn (R.q 2 : Point) (R.q 0 : Point) (Y.point i : Point) :=
    triangle_vertex_exposing_sum_pos hfour (R.q 0) (R.q 1) (R.q 2)
      (Y.point i) (turn_pos_of_strictlyInsideTriangle hinside) (hyHull i) (hyne i)
  have hq0not : (R.q 0 : Point) ∉ Y.hull := by
    apply not_mem_convexHull_range_of_twoTurns_pos
      (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point) (R.q 0 : Point)
      (R.q 0 : Point) (fun i ↦ (Y.point i : Point)) hpos
    simp
  exact no_smaller_monoFour hmin Y hsub (R.q 0)
    (hHullEq.symm ▸ vertex_mem_triangleHull _ _ _) hq0not

/-- The chosen concave four-set has no further point of its own colour in
its outer triangle. -/
theorem same_colour_eq_concaveVertex_of_minimal
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {X : MonoFour P colour}
    (hmin : ∀ Y : MonoFour P colour, X.count ≤ Y.count)
    (R : FourReordering X.point)
    (hinside : StrictlyInsideTriangle (R.q 0 : Point) (R.q 1 : Point)
      (R.q 2 : Point) (R.q 3 : Point))
    (p : P)
    (hpHull : (p : Point) ∈
      triangleHull (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point))
    (hpcolour : colour p = colour (R.q 0)) :
    ∃ i, p = R.q i := by
  classical
  by_contra hnot
  push Not at hnot
  have hpq (i : Fin 4) : p ≠ R.q i := fun h ↦ hnot i h
  have hqp (i : Fin 4) : R.q i ≠ p := Ne.symm (hpq i)
  have hRmono (i : Fin 4) : colour (R.q i) = colour (R.q 0) := by
    have hi : R.q i ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self i
    have hzero : R.q 0 ∈ Set.range X.point := by
      rw [← R.range_eq]
      exact Set.mem_range_self 0
    obtain ⟨j, hj⟩ := hi
    obtain ⟨k, hk⟩ := hzero
    rw [← hj, ← hk, X.mono j, X.mono k]
  let y : Fin 4 → P := ![p, R.q 1, R.q 2, R.q 3]
  have hR12 : R.q 1 ≠ R.q 2 := R.injective.ne (by decide)
  have hR13 : R.q 1 ≠ R.q 3 := R.injective.ne (by decide)
  have hR23 : R.q 2 ≠ R.q 3 := R.injective.ne (by decide)
  have hyinj : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [y, hpq, hqp, hR12, hR13, hR23]
  let Y : MonoFour P colour := ⟨y, hyinj, by
    intro i
    fin_cases i <;> simp [y, hpcolour, hRmono]⟩
  apply no_monoFour_in_minimal_triangle_avoiding_first
    hfour hmin R hinside Y
  · intro i
    fin_cases i
    · exact hpHull
    · simpa [Y, y] using
        (subset_convexHull ℝ
          ({(R.q 0 : Point), (R.q 1 : Point), (R.q 2 : Point)} : Set Point)
          (by simp) : (R.q 1 : Point) ∈
            triangleHull (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point))
    · simpa [Y, y] using
        (subset_convexHull ℝ
          ({(R.q 0 : Point), (R.q 1 : Point), (R.q 2 : Point)} : Set Point)
          (by simp) : (R.q 2 : Point) ∈
            triangleHull (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point))
    · simpa [Y, y] using strictlyInsideTriangle_mem_triangleHull hinside
  · intro i
    fin_cases i
    · simpa [Y, y] using hpq 0
    · simpa [Y, y] using R.injective.ne (by decide : (1 : Fin 4) ≠ 0)
    · simpa [Y, y] using R.injective.ne (by decide : (2 : Fin 4) ≠ 0)
    · simpa [Y, y] using R.injective.ne (by decide : (3 : Fin 4) ≠ 0)

noncomputable def pointsOfColourInTriangle
    (P : Finset Point) (colour : P → Fin 4) (a b c : Point) (e : Fin 4) :
    Finset P := by
  classical
  exact (Finset.univ : Finset P).filter fun p ↦
    (p : Point) ∈ triangleHull a b c ∧ colour p = e

@[simp] theorem mem_pointsOfColourInTriangle
    {P : Finset Point} {colour : P → Fin 4} {a b c : Point} {e : Fin 4}
    {p : P} :
    p ∈ pointsOfColourInTriangle P colour a b c e ↔
      (p : Point) ∈ triangleHull a b c ∧ colour p = e := by
  classical
  simp [pointsOfColourInTriangle]

/-- Inside the outer triangle of the minimum concave four-set, every other
colour occurs at most three times. -/
theorem other_colour_card_le_three_in_concave_hull
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {X : MonoFour P colour}
    (hmin : ∀ Y : MonoFour P colour, X.count ≤ Y.count)
    (R : FourReordering X.point)
    (hinside : StrictlyInsideTriangle (R.q 0 : Point) (R.q 1 : Point)
      (R.q 2 : Point) (R.q 3 : Point))
    (e : Fin 4) (he : e ≠ colour (R.q 0)) :
    (pointsOfColourInTriangle P colour (R.q 0 : Point) (R.q 1 : Point)
      (R.q 2 : Point) e).card ≤ 3 := by
  classical
  let C : Finset P := pointsOfColourInTriangle P colour
    (R.q 0 : Point) (R.q 1 : Point) (R.q 2 : Point) e
  change C.card ≤ 3
  by_contra hle
  have hlt : 3 < C.card := Nat.lt_of_not_ge hle
  rw [Finset.three_lt_card] at hlt
  obtain ⟨a, ha, b, hb, c, hc, d, hd,
    hab, hac, had, hbc, hbd, hcd⟩ := hlt
  have haData := (Finset.mem_filter.mp ha).2
  have hbData := (Finset.mem_filter.mp hb).2
  have hcData := (Finset.mem_filter.mp hc).2
  have hdData := (Finset.mem_filter.mp hd).2
  let y : Fin 4 → P := ![a, b, c, d]
  have hyinj : Function.Injective y := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [y]
  let Y : MonoFour P colour := ⟨y, hyinj, by
    intro i
    fin_cases i <;> simp [y, haData.2, hbData.2, hcData.2, hdData.2]⟩
  apply no_monoFour_in_minimal_triangle_avoiding_first
    hfour hmin R hinside Y
  · intro i
    fin_cases i
    · exact haData.1
    · exact hbData.1
    · exact hcData.1
    · exact hdData.1
  · intro i hi
    have hcol : colour (Y.point i) = e := by
      fin_cases i <;> simp [Y, y, haData.2, hbData.2, hcData.2, hdData.2]
    have := congrArg colour hi
    exact he (hcol.symm.trans this)

end Lax56Proofs.HKBDirectCore
