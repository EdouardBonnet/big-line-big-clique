import Lax56Proofs.HKBColourClasses
import Mathlib.Tactic

/-!
Geometric and finite-cardinality preparation for the final `10,11,12`
blocker cases of the Hujter--Kisfaludi--Bak argument.
-/

namespace Lax56Proofs.HKBHexFinalGeometry

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.HKBColourClasses
open Lax56Proofs.HKBColourCoverage
open Lax56Proofs.HKBConcavity
open Lax56Proofs.HKBConvexity
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBDiagonals
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBQuadrilateral
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

private def colourClass {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) (c : Fin 4) : Finset X :=
  Finset.univ.filter fun p ↦ colour p = c

@[simp] private theorem mem_colourClass
    {X : Type*} [Fintype X] [DecidableEq X]
    {colour : X → Fin 4} {c : Fin 4} {p : X} :
    p ∈ colourClass colour c ↔ colour p = c := by
  simp [colourClass]

private theorem card_eq_sum_colourClasses
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) :
    Fintype.card X = ∑ c : Fin 4, (colourClass colour c).card := by
  simpa [colourClass] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset X))
      (t := (Finset.univ : Finset (Fin 4)))
      (f := colour) (by simp))

/-- If four classes have size at most three, a ten-point set with one full
class has a second full class. -/
theorem exists_other_colourClass_card_three
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4)
    (hle : ∀ d, (colourClass colour d).card ≤ 3)
    (hten : 10 ≤ Fintype.card X) {c : Fin 4}
    (hc : (colourClass colour c).card = 3) :
    ∃ d, d ≠ c ∧ (colourClass colour d).card = 3 := by
  have hsum := card_eq_sum_colourClasses colour
  by_contra hn
  push Not at hn
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  simp only [Fin.sum_univ_four] at hsum
  fin_cases c
  · have hn1 := hn 1 (by decide)
    have hn2 := hn 2 (by decide)
    have hn3 := hn 3 (by decide)
    omega
  · have hn0 := hn 0 (by decide)
    have hn2 := hn 2 (by decide)
    have hn3 := hn 3 (by decide)
    omega
  · have hn0 := hn 0 (by decide)
    have hn1 := hn 1 (by decide)
    have hn3 := hn 3 (by decide)
    omega
  · have hn0 := hn 0 (by decide)
    have hn1 := hn 1 (by decide)
    have hn2 := hn 2 (by decide)
    omega

/-- With the same upper bound, any ten-point set has a full colour class. -/
theorem exists_colourClass_card_three
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4)
    (hle : ∀ d, (colourClass colour d).card ≤ 3)
    (hten : 10 ≤ Fintype.card X) :
    ∃ c, (colourClass colour c).card = 3 := by
  have hsum := card_eq_sum_colourClasses colour
  by_contra hn
  push Not at hn
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  have hn0 := hn 0
  have hn1 := hn 1
  have hn2 := hn 2
  have hn3 := hn 3
  simp only [Fin.sum_univ_four] at hsum
  omega

/-- Enumerate a colour class of cardinality three. -/
theorem enumerate_colourClass_three
    {B : Finset Point} (colour : B → Fin 4) (c : Fin 4)
    (hc : (colourClass colour c).card = 3) :
    ∃ q : Fin 3 → B,
      Function.Injective q ∧
      (∀ i, colour (q i) = c) ∧
      ∀ p : B, colour p = c → ∃ i, p = q i := by
  classical
  let C := colourClass colour c
  let e : Fin 3 ≃ C := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe, hc])
  let q : Fin 3 → B := fun i ↦ ((e i : C) : B)
  have hq : Function.Injective q := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  refine ⟨q, hq, ?_, ?_⟩
  · intro i
    exact mem_colourClass.mp (e i).property
  · intro p hp
    let pc : C := ⟨p, mem_colourClass.mpr hp⟩
    obtain ⟨i, hi⟩ := e.surjective pc
    refine ⟨i, ?_⟩
    exact congrArg Subtype.val hi.symm

private theorem monoTriple_of_enumeration
    {B : Finset Point} {colour : B → Fin 4} {c : Fin 4}
    {q : Fin 3 → B} (hq : Function.Injective q)
    (hmono : ∀ i, colour (q i) = c) :
    MonoTriple colour (q 0) (q 1) (q 2) := by
  exact ⟨hq.ne (by decide), hq.ne (by decide), hq.ne (by decide),
    (hmono 0).trans (hmono 1).symm,
    (hmono 1).trans (hmono 2).symm⟩

/-- A triangle vertex together with one point from the relative interior of
each side is a strict convex quadrilateral. -/
theorem vertex_and_sidePoints_strictConvex
    {a b c r s t : Point} (habc : 0 < turn a b c)
    (hr : r ∈ openSegment ℝ a b)
    (hs : s ∈ openSegment ℝ b c)
    (ht : t ∈ openSegment ℝ c a) :
    StrictConvexQuadrilateral ![a, r, s, t] := by
  have habs : 0 < turn a b s := turn_pos_of_mem_next_side habc hs
  have habt : 0 < turn a b t := by
    apply edgeTurn_pos_of_mem_openSegment ht habc.le (by simp)
    exact Or.inl habc
  have hars : 0 < turn a r s := by
    obtain ⟨u, hu0, hu1, hu⟩ :=
      turn_of_mem_openSegment (a := a) (b := s) hr
    have hasb : turn a s b < 0 := by
      rw [turn_swap_last]
      linarith
    have hasr : turn a s r < 0 := by
      simp only [turn_self_left, mul_zero, zero_add] at hu
      rw [hu]
      exact mul_neg_of_pos_of_neg hu0 hasb
    rw [turn_swap_last]
    linarith
  have hart : 0 < turn a r t := by
    obtain ⟨u, hu0, hu1, hu⟩ :=
      turn_of_mem_openSegment (a := a) (b := t) hr
    have hatb : turn a t b < 0 := by
      rw [turn_swap_last]
      linarith
    have hatr : turn a t r < 0 := by
      simp only [turn_self_left, mul_zero, zero_add] at hu
      rw [hu]
      exact mul_neg_of_pos_of_neg hu0 hatb
    rw [turn_swap_last]
    linarith
  have hast : 0 < turn a s t := by
    have hasc : 0 < turn a s c := by
      obtain ⟨u, hu0, hu1, hu⟩ :=
        turn_of_mem_openSegment (a := a) (b := c) hs
      have hacb : turn a c b < 0 := by
        rw [turn_swap_last]
        linarith
      have hacs : turn a c s < 0 := by
        simp only [turn_self_right, mul_zero, add_zero] at hu
        rw [hu]
        exact mul_neg_of_pos_of_neg (sub_pos.mpr hu1) hacb
      rw [turn_swap_last]
      linarith
    obtain ⟨u, hu0, hu1, hu⟩ :=
      turn_of_mem_openSegment (a := a) (b := s) ht
    simp only [turn_self_left, mul_zero, add_zero] at hu
    rw [hu]
    exact mul_pos (sub_pos.mpr hu1) hasc
  have hrst : 0 < turn r s t :=
    turn_side_points_pos habc hr hs ht
  have hpair := triangle_side_points_pairwise habc hr hs ht
  have hab : a ≠ b := by
    intro e
    subst b
    simpa [turn] using habc.ne'
  have hca : c ≠ a := by
    intro e
    subst c
    simpa [turn] using habc.ne'
  have har : a ≠ r := by
    intro e
    have haopen : a ∈ openSegment ℝ a b := by simpa [e] using hr
    exact hab ((left_mem_openSegment_iff (𝕜 := ℝ)).mp haopen)
  have has : a ≠ s := by
    intro e
    simpa [e, turn] using habs.ne'
  have hat : a ≠ t := by
    intro e
    have haopen : a ∈ openSegment ℝ c a := by simpa [e] using ht
    exact hca ((right_mem_openSegment_iff (𝕜 := ℝ)).mp haopen)
  have hinj : Function.Injective (![a, r, s, t] : Fin 4 → Point) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact strictConvexQuadrilateral_of_four_turns_pos hinj hars hart hast hrst

/-- Applying an oriented-line functional to the barycentric decomposition
of a point inside a triangle.  The identity is polynomial, so it is valid
without any nondegeneracy assumptions. -/
theorem turn_barycentric_identity
    (x y a b c p : Point) :
    turn x y p * turn a b c =
      turn b c p * turn x y a +
      turn c a p * turn x y b +
      turn a b p * turn x y c := by
  simp only [turn]
  ring

/-- A strict interior point of a triangle is strictly on the positive side
of every oriented line on whose nonnegative side the three vertices lie,
provided at least one vertex is strictly on that side. -/
theorem edgeTurn_pos_of_strictlyInsideTriangle
    {x y a b c p : Point}
    (hp : StrictlyInsideTriangle a b c p)
    (ha : 0 ≤ turn x y a) (hb : 0 ≤ turn x y b)
    (hc : 0 ≤ turn x y c)
    (hpos : 0 < turn x y a ∨ 0 < turn x y b ∨ 0 < turn x y c) :
    0 < turn x y p := by
  have habc : 0 < turn a b c := turn_pos_of_strictlyInsideTriangle hp
  have hbc : 0 < turn b c p := hp.2.1
  have hca : 0 < turn c a p := hp.2.2
  have hab : 0 < turn a b p := hp.1
  have hrhs : 0 <
      turn b c p * turn x y a +
      turn c a p * turn x y b +
      turn a b p * turn x y c := by
    rcases hpos with ha' | hb' | hc'
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg (mul_pos hbc ha') (mul_nonneg hca.le hb))
        (mul_nonneg hab.le hc)
    · exact add_pos_of_pos_of_nonneg
        (add_pos_of_nonneg_of_pos (mul_nonneg hbc.le ha) (mul_pos hca hb'))
        (mul_nonneg hab.le hc)
    · exact add_pos_of_nonneg_of_pos
        (add_nonneg (mul_nonneg hbc.le ha) (mul_nonneg hca.le hb))
        (mul_pos hab hc')
  rw [← turn_barycentric_identity] at hrhs
  rcases mul_pos_iff.mp hrhs with hsame | hsame
  · exact hsame.1
  · exact (not_lt_of_ge habc.le hsame.2).elim

/-- No vertex of a strict convex quadrilateral is strictly inside a
triangle formed by the other three vertices.  This supporting-line proof
is independent of the order in which those three vertices are listed. -/
theorem strictConvexQuadrilateral_vertex_not_strictlyInside
    {q : Fin 4 → Point} (hq : StrictConvexQuadrilateral q)
    {i j k l : Fin 4}
    (hil : i ≠ l) (hjl : j ≠ l) (hkl : k ≠ l)
    (hij : i ≠ j) :
    ¬StrictlyInsideTriangle (q i) (q j) (q k) (q l) := by
  intro hp
  have hi0 : 0 ≤ turn (q l) (q (l + 1)) (q i) := by
    by_cases his : i = l + 1
    · subst i
      simp
    · exact (hq.2 l i hil his).le
  have hj0 : 0 ≤ turn (q l) (q (l + 1)) (q j) := by
    by_cases hjs : j = l + 1
    · subst j
      simp
    · exact (hq.2 l j hjl hjs).le
  have hk0 : 0 ≤ turn (q l) (q (l + 1)) (q k) := by
    by_cases hks : k = l + 1
    · subst k
      simp
    · exact (hq.2 l k hkl hks).le
  have hpositive :
      0 < turn (q l) (q (l + 1)) (q i) ∨
      0 < turn (q l) (q (l + 1)) (q j) ∨
      0 < turn (q l) (q (l + 1)) (q k) := by
    by_cases his : i = l + 1
    · right
      left
      apply hq.2 l j hjl
      intro hjs
      exact hij (his.trans hjs.symm)
    · exact Or.inl (hq.2 l i hil his)
  have hstrict := edgeTurn_pos_of_strictlyInsideTriangle hp hi0 hj0 hk0 hpositive
  simpa using hstrict

/-- The geometric contradiction in the ten-blocker case.  Once an oriented
monochromatic triangle has one strict-interior vertex, its three blockers
are the other three strict-interior points.  They form a strict convex
quadrilateral, contradicting Lemma 5.4. -/
theorem no_ten_blockers_of_oriented_monoTriangle
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (hdiag : ∀ i : Fin 9, ∃ r ∈ hexBlockers P h,
      r ∈ openSegment ℝ
        (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (hcard : (hexBlockers P h).card = 10)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    {a b c : hexBlockers P h}
    (hmono : MonoTriple colour a b c)
    (habc : 0 < turn (a : Point) (b : Point) (c : Point))
    (ha : StrictlyInsideHexagon h a) : False := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  obtain ⟨r, hr⟩ := hproper a b hmono.1 hmono.2.2.2.1
  obtain ⟨s, hs⟩ := hproper b c hmono.2.1 hmono.2.2.2.2
  obtain ⟨t, ht⟩ := hproper c a hmono.2.2.1
    (hmono.2.2.2.2.symm.trans hmono.2.2.2.1.symm)
  have hrInside : StrictlyInsideHexagon h r :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      a.property b.property (Subtype.val_injective.ne hmono.1) hr
  have hsInside : StrictlyInsideHexagon h s :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      b.property c.property (Subtype.val_injective.ne hmono.2.1) hs
  have htInside : StrictlyInsideHexagon h t :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      c.property a.property (Subtype.val_injective.ne hmono.2.2.1) ht
  have hIcard : I.card = 4 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  have haI : (a : Point) ∈ I := Finset.mem_filter.mpr ⟨a.property, ha⟩
  have hrI : (r : Point) ∈ I := Finset.mem_filter.mpr ⟨r.property, hrInside⟩
  have hsI : (s : Point) ∈ I := Finset.mem_filter.mpr ⟨s.property, hsInside⟩
  have htI : (t : Point) ∈ I := Finset.mem_filter.mpr ⟨t.property, htInside⟩
  let A : I := ⟨a, haI⟩
  let R : I := ⟨r, hrI⟩
  let S : I := ⟨s, hsI⟩
  let T : I := ⟨t, htI⟩
  let F : Fin 4 → I := ![A, R, S, T]
  have hFval : (fun i ↦ (F i : Point)) =
      (![a, r, s, t] : Fin 4 → Point) := by
    funext i
    fin_cases i <;> rfl
  have hq : StrictConvexQuadrilateral (fun i ↦ (F i : Point)) := by
    rw [hFval]
    exact vertex_and_sidePoints_strictConvex habc hr hs ht
  have hFinj : Function.Injective F := by
    intro i j hij
    exact hq.1 (congrArg Subtype.val hij)
  have hFsurj : Function.Surjective F := by
    apply ((Fintype.bijective_iff_injective_and_card F).2 ⟨hFinj, ?_⟩).2
    simpa [hIcard]
  have hIP : I ⊆ P := by
    intro x hx
    exact hexBlockers_subset P h (Finset.mem_filter.mp hx).1
  have hdiagI : ∀ i : Fin 9, ∃ r ∈ I,
      r ∈ openSegment ℝ
        (h (diagonalEnds i).1) (h (diagonalEnds i).2) := by
    intro i
    obtain ⟨x, hxB, hxseg⟩ := hdiag i
    have hxInside : StrictlyInsideHexagon h x := by
      intro side
      exact diagonalPoint_edgeTurn_pos hh (diagonalEnds_ne i)
        (diagonalEnds_nonadjacent i).1 (diagonalEnds_nonadjacent i).2
        hxseg side
    exact ⟨x, Finset.mem_filter.mpr ⟨hxB, hxInside⟩, hxseg⟩
  obtain ⟨p, q₀, q₁, q₂, hp⟩ :=
    four_diagonal_blockers_are_concave hfour hh hhP hIP hIcard hdiagI
  obtain ⟨ip, hip⟩ := hFsurj p
  obtain ⟨i₀, hi₀⟩ := hFsurj q₀
  obtain ⟨i₁, hi₁⟩ := hFsurj q₁
  obtain ⟨i₂, hi₂⟩ := hFsurj q₂
  rw [← hip, ← hi₀, ← hi₁, ← hi₂] at hp
  have hne := strictlyInsideTriangle_ne_vertices hp
  have hi₀p : i₀ ≠ ip := by
    intro e
    subst i₀
    exact hne.1 rfl
  have hi₁p : i₁ ≠ ip := by
    intro e
    subst i₁
    exact hne.2.1 rfl
  have hi₂p : i₂ ≠ ip := by
    intro e
    subst i₂
    exact hne.2.2 rfl
  have hi₀i₁ : i₀ ≠ i₁ := by
    intro e
    subst i₁
    have hz := hp.1
    have : (0 : ℝ) < 0 := by simpa [turn] using hz
    exact (lt_irrefl 0 this)
  exact strictConvexQuadrilateral_vertex_not_strictlyInside hq
    hi₀p hi₁p hi₂p hi₀i₁ hp

/-- Lemma 3.1 in the form needed later: a monochromatic triangle cannot
consist entirely of the six side blockers. -/
theorem monoTriangle_has_strictInterior_vertex
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d,
      ((Finset.univ : Finset (hexBlockers P h)).filter
        fun p ↦ colour p = d).card ≤ 3)
    (hten : 10 ≤ (hexBlockers P h).card)
    {a b c : hexBlockers P h} (hmono : MonoTriple colour a b c) :
    StrictlyInsideHexagon h a ∨ StrictlyInsideHexagon h b ∨
      StrictlyInsideHexagon h c := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  by_contra hn
  push Not at hn
  let ca := colour a
  let A : Finset B := {a, b, c}
  have hac : a ≠ c := hmono.2.2.1.symm
  have hAcard : A.card = 3 := by
    simp [A, hmono.1, hmono.2.1, hac]
  have hAsub : A ⊆ colourClass colour ca := by
    intro p hp
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact mem_colourClass.mpr rfl
    · exact mem_colourClass.mpr hmono.2.2.2.1.symm
    · exact mem_colourClass.mpr
        (hmono.2.2.2.1.trans hmono.2.2.2.2).symm
  have hclassle : (colourClass colour ca).card ≤ 3 := by
    simpa [B, colourClass] using hle ca
  have hcacard : (colourClass colour ca).card = 3 := by
    have := Finset.card_le_card hAsub
    omega
  have hclassEq : A = colourClass colour ca :=
    Finset.eq_of_subset_of_card_le hAsub (by omega)
  have hle' : ∀ d, (colourClass colour d).card ≤ 3 := by
    intro d
    simpa [B, colourClass] using hle d
  obtain ⟨d, hdca, hdcard⟩ :=
    exists_other_colourClass_card_three colour hle'
      (by simpa [B] using hten) hcacard
  obtain ⟨q, hqinj, hqmono, -⟩ :=
    enumerate_colourClass_three colour d hdcard
  have hqtri : MonoTriple colour (q 0) (q 1) (q 2) :=
    monoTriple_of_enumeration hqinj hqmono
  obtain ⟨p, hpHull, hpcolour⟩ :=
    exists_colour_in_triangleHull hfourB hproper hqtri ca (by
      rw [hqmono 0]
      exact hdca.symm)
  have hpA : p ∈ A := by
    rw [hclassEq]
    exact mem_colourClass.mpr hpcolour
  have hpnot : ¬StrictlyInsideHexagon h (p : Point) := by
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hpA
    rcases hpA with rfl | rfl | rfl
    · exact hn.1
    · exact hn.2.1
    · exact hn.2.2
  obtain ⟨i, hpi⟩ :=
    (not_strictlyInside_iff_sideBlocker hfour hh hhP hside p.property).mp hpnot
  let Q : Finset Point := {(q 0 : Point), (q 1 : Point), (q 2 : Point)}
  have hQB : Q ⊆ B := by
    intro x hx
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact (q _).property
  have hsHull : sideBlocker hside i ∈ convexHull ℝ (Q : Set Point) := by
    rw [← hpi]
    simpa [Q, triangleHull] using hpHull
  have hsQ := sideBlocker_mem_of_mem_convexHull
    hfour hh hhP hside hQB i hsHull
  have hpQ : (p : Point) ∈ Q := by simpa [hpi] using hsQ
  simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hpQ
  rcases hpQ with hpq | hpq | hpq
  · have heq : p = q 0 := Subtype.ext hpq
    exact hdca ((hqmono 0).symm.trans
      ((congrArg colour heq).symm.trans hpcolour))
  · have heq : p = q 1 := Subtype.ext hpq
    exact hdca ((hqmono 1).symm.trans
      ((congrArg colour heq).symm.trans hpcolour))
  · have heq : p = q 2 := Subtype.ext hpq
    exact hdca ((hqmono 2).symm.trans
      ((congrArg colour heq).symm.trans hpcolour))

private theorem monoTriple_rotate
    {B : Finset Point} {colour : B → Fin 4} {a b c : B}
    (h : MonoTriple colour a b c) : MonoTriple colour b c a := by
  exact ⟨h.2.1, h.2.2.1, h.1,
    h.2.2.2.2, (h.2.2.2.1.trans h.2.2.2.2).symm⟩

private theorem monoTriple_swap_last
    {B : Finset Point} {colour : B → Fin 4} {a b c : B}
    (h : MonoTriple colour a b c) : MonoTriple colour a c b := by
  exact ⟨h.2.2.1.symm, h.2.1.symm, h.1.symm,
    h.2.2.2.1.trans h.2.2.2.2, h.2.2.2.2.symm⟩

/-- The complete `|B| = 10` case, with no finite search: a full colour
class supplies a monochromatic triangle, Lemma 3.1 supplies its interior
vertex, and `no_ten_blockers_of_oriented_monoTriangle` gives the geometric
contradiction. -/
theorem no_ten_hexBlockers
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (hdiag : ∀ i : Fin 9, ∃ r ∈ hexBlockers P h,
      r ∈ openSegment ℝ
        (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (hcard : (hexBlockers P h).card = 10)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour) : False := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hle : ∀ d,
      ((Finset.univ : Finset B).filter fun p ↦ colour p = d).card ≤ 3 := by
    intro d
    exact colour_class_card_le_three hfour hh hhP hside
      (by simpa [B, hcard]) colour hproper d
  have hle' : ∀ d, (colourClass colour d).card ≤ 3 := by
    intro d
    simpa [B, colourClass] using hle d
  obtain ⟨d, hd⟩ := exists_colourClass_card_three colour hle'
    (by simpa [B, hcard])
  obtain ⟨q, hqinj, hqcolour, -⟩ :=
    enumerate_colourClass_three colour d hd
  have hmono : MonoTriple colour (q 0) (q 1) (q 2) :=
    monoTriple_of_enumeration hqinj hqcolour
  have hinside := monoTriangle_has_strictInterior_vertex
    hfour hh hhP hside colour hproper hle (by simpa [B, hcard]) hmono
  have hturnne : turn (q 0 : Point) (q 1 : Point) (q 2 : Point) ≠ 0 :=
    turn_ne_zero_of_same_colour hfourB hproper
      hmono.1 hmono.2.1 hmono.2.2.1
      hmono.2.2.2.1 hmono.2.2.2.2
  by_cases hpos : 0 < turn (q 0 : Point) (q 1 : Point) (q 2 : Point)
  · rcases hinside with h₀ | h₁ | h₂
    · exact no_ten_blockers_of_oriented_monoTriangle
        hfour hh hhP hside hdiag hcard colour hproper hmono hpos h₀
    · exact no_ten_blockers_of_oriented_monoTriangle
        hfour hh hhP hside hdiag hcard colour hproper
        (monoTriple_rotate hmono)
        (by simpa only [turn_rotate] using hpos) h₁
    · exact no_ten_blockers_of_oriented_monoTriangle
        hfour hh hhP hside hdiag hcard colour hproper
        (monoTriple_rotate (monoTriple_rotate hmono))
        (by simpa only [turn_rotate] using hpos) h₂
  · have hneg : turn (q 0 : Point) (q 1 : Point) (q 2 : Point) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hturnne
    have hswapPos : 0 < turn (q 0 : Point) (q 2 : Point) (q 1 : Point) := by
      rw [turn_swap_last]
      linarith
    let hs := monoTriple_swap_last hmono
    rcases hinside with h₀ | h₁ | h₂
    · exact no_ten_blockers_of_oriented_monoTriangle
        hfour hh hhP hside hdiag hcard colour hproper hs hswapPos h₀
    · exact no_ten_blockers_of_oriented_monoTriangle
        hfour hh hhP hside hdiag hcard colour hproper
        (monoTriple_rotate (monoTriple_rotate hs))
        (by
          rw [turn_rotate (q 2 : Point) (q 1 : Point) (q 0 : Point),
            turn_rotate (q 0 : Point) (q 2 : Point) (q 1 : Point)]
          exact hswapPos) h₁
    · exact no_ten_blockers_of_oriented_monoTriangle
        hfour hh hhP hside hdiag hcard colour hproper
        (monoTriple_rotate hs)
        (by simpa only [turn_rotate] using hswapPos) h₂

end Lax56Proofs.HKBHexFinalGeometry
