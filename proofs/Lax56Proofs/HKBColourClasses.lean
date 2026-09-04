import Lax56Proofs.HKBQuadrilateralMaximal
import Lax56Proofs.HKBConcaveColour
import Mathlib.Tactic

/-!
Corollary 6.7: every colour class has at most three points.
-/

namespace Lax56Proofs.HKBColourClasses

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBColourBound
open Lax56Proofs.HKBConcaveColour
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBHullCount
open Lax56Proofs.HKBQuadrilateral
open Lax56Proofs.HKBQuadrilateralMaximal
open Lax56Proofs.HKBQuadrilateralPattern
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- A relabelling of four points which preserves their range. -/
structure FourReordering {X : Type*} (x : Fin 4 → X) where
  q : Fin 4 → X
  injective : Function.Injective q
  range_eq : Set.range q = Set.range x

def mkFourReordering {X : Type*} (x : Fin 4 → X)
    (hx : Function.Injective x) (s : Fin 4 → Fin 4)
    (hs : Function.Injective s) : FourReordering x where
  q := fun i ↦ x (s i)
  injective := hx.comp hs
  range_eq := by
    apply Set.Subset.antisymm
    · rintro _ ⟨i, rfl⟩
      exact ⟨s i, rfl⟩
    · rintro _ ⟨j, rfl⟩
      have hsurj : Function.Surjective s :=
        ((Fintype.bijective_iff_injective_and_card s).2 ⟨hs, rfl⟩).2
      obtain ⟨i, rfl⟩ := hsurj j
      exact ⟨i, rfl⟩

private theorem perm0123_injective :
    Function.Injective (![0, 1, 2, 3] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm0132_injective :
    Function.Injective (![0, 1, 3, 2] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm1230_injective :
    Function.Injective (![1, 2, 3, 0] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm0312_injective :
    Function.Injective (![0, 3, 1, 2] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm0321_injective :
    Function.Injective (![0, 3, 2, 1] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm0231_injective :
    Function.Injective (![0, 2, 3, 1] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm0213_injective :
    Function.Injective (![0, 2, 1, 3] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

private theorem perm1320_injective :
    Function.Injective (![1, 3, 2, 0] : Fin 4 → Fin 4) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem strictConvexQuadrilateral_of_four_turns_pos
    {q : Fin 4 → Point} (hq : Function.Injective q)
    (h₀₁₂ : 0 < turn (q 0) (q 1) (q 2))
    (h₀₁₃ : 0 < turn (q 0) (q 1) (q 3))
    (h₀₂₃ : 0 < turn (q 0) (q 2) (q 3))
    (h₁₂₃ : 0 < turn (q 1) (q 2) (q 3)) :
    StrictConvexQuadrilateral q := by
  refine ⟨hq, ?_⟩
  intro i j hji hjs
  fin_cases i <;> fin_cases j <;>
    simp_all [turn] <;> nlinarith

/-- Four distinct points with no collinear triple are either a concave
quadruple (after relabelling) or a strict convex quadrilateral (after
cyclic relabelling). -/
theorem four_point_dichotomy
    {X : Type*} (pt : X → Point) (hpt : Function.Injective pt)
    (x : Fin 4 → X) (hx : Function.Injective x)
    (hgp : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      turn (pt (x i)) (pt (x j)) (pt (x k)) ≠ 0) :
    (∃ R : FourReordering x,
      StrictlyInsideTriangle (pt (R.q 0)) (pt (R.q 1))
        (pt (R.q 2)) (pt (R.q 3))) ∨
    (∃ R : FourReordering x,
      StrictConvexQuadrilateral fun i ↦ pt (R.q i)) := by
  let A := turn (pt (x 0)) (pt (x 1)) (pt (x 2))
  let B := turn (pt (x 0)) (pt (x 1)) (pt (x 3))
  let C := turn (pt (x 0)) (pt (x 2)) (pt (x 3))
  let D := turn (pt (x 1)) (pt (x 2)) (pt (x 3))
  have hA0 : A ≠ 0 := hgp 0 1 2 (by decide) (by decide) (by decide)
  have hB0 : B ≠ 0 := hgp 0 1 3 (by decide) (by decide) (by decide)
  have hC0 : C ≠ 0 := hgp 0 2 3 (by decide) (by decide) (by decide)
  have hD0 : D ≠ 0 := hgp 1 2 3 (by decide) (by decide) (by decide)
  have hdecomp : A = B + D - C := by
    dsimp [A, B, C, D]
    rw [turn_triangle_decompose (pt (x 0)) (pt (x 1)) (pt (x 2)) (pt (x 3))]
    rw [turn_swap_first (pt (x 0)) (pt (x 2)) (pt (x 3))]
    ring
  by_cases hA : 0 < A
  · by_cases hB : 0 < B
    · by_cases hC : 0 < C
      · by_cases hD : 0 < D
        · right
          let s : Fin 4 → Fin 4 := ![0, 1, 2, 3]
          have hs : Function.Injective s := by
            simpa [s] using perm0123_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, strictConvexQuadrilateral_of_four_turns_pos
            (hpt.comp R.injective) ?_ ?_ ?_ ?_⟩
          · simpa [R, s, mkFourReordering, A] using hA
          · simpa [R, s, mkFourReordering, B] using hB
          · simpa [R, s, mkFourReordering, C] using hC
          · simpa [R, s, mkFourReordering, D] using hD
        · left
          have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          let s : Fin 4 → Fin 4 := ![0, 1, 3, 2]
          have hs : Function.Injective s := by
            simpa [s] using perm0132_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · exact hA
          · rw [turn_swap_last]; simpa [D] using hDn
          · simpa only [turn_rotate] using hC
      · have hCn : C < 0 := lt_of_le_of_ne (le_of_not_gt hC) hC0
        by_cases hD : 0 < D
        · left
          let s : Fin 4 → Fin 4 := ![0, 1, 2, 3]
          have hs : Function.Injective s := by
            simpa [s] using perm0123_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨hB, hD, ?_⟩
          rw [turn_swap_first]
          simpa [C] using hCn
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          right
          let s : Fin 4 → Fin 4 := ![0, 1, 3, 2]
          have hs : Function.Injective s := by
            simpa [s] using perm0132_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, strictConvexQuadrilateral_of_four_turns_pos
            (hpt.comp R.injective) ?_ ?_ ?_ ?_⟩
          all_goals dsimp [R, mkFourReordering, s]
          · exact hB
          · exact hA
          · rw [turn_swap_last]; simpa [C] using hCn
          · rw [turn_swap_last]; simpa [D] using hDn
    · have hBn : B < 0 := lt_of_le_of_ne (le_of_not_gt hB) hB0
      by_cases hC : 0 < C
      · by_cases hD : 0 < D
        · left
          let s : Fin 4 → Fin 4 := ![1, 2, 3, 0]
          have hs : Function.Injective s := by
            simpa [s] using perm1230_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · simpa only [turn_rotate] using hA
          · simpa only [turn_rotate] using hC
          · rw [turn_reverse]; simpa [B] using hBn
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          exfalso
          linarith
      · have hCn : C < 0 := lt_of_le_of_ne (le_of_not_gt hC) hC0
        by_cases hD : 0 < D
        · right
          let s : Fin 4 → Fin 4 := ![0, 3, 1, 2]
          have hs : Function.Injective s := by
            simpa [s] using perm0312_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, strictConvexQuadrilateral_of_four_turns_pos
            (hpt.comp R.injective) ?_ ?_ ?_ ?_⟩
          all_goals dsimp [R, mkFourReordering, s]
          · rw [turn_swap_last]; simpa [B] using hBn
          · rw [turn_swap_last]; simpa [C] using hCn
          · exact hA
          · simpa only [turn_rotate] using hD
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          left
          let s : Fin 4 → Fin 4 := ![0, 3, 2, 1]
          have hs : Function.Injective s := by
            simpa [s] using perm0321_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · rw [turn_swap_last]; simpa [B] using hBn
          · rw [turn_reverse]; simpa [D] using hDn
          · rw [turn_rotate, turn_rotate]; exact hA
  · have hAn : A < 0 := lt_of_le_of_ne (le_of_not_gt hA) hA0
    by_cases hB : 0 < B
    · by_cases hC : 0 < C
      · by_cases hD : 0 < D
        · left
          let s : Fin 4 → Fin 4 := ![0, 2, 3, 1]
          have hs : Function.Injective s := by
            simpa [s] using perm0231_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · rw [turn_swap_last]; simpa [A] using hAn
          · simpa only [turn_rotate] using hD
          · simpa only [turn_rotate] using hB
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          right
          let s : Fin 4 → Fin 4 := ![0, 2, 1, 3]
          have hs : Function.Injective s := by
            simpa [s] using perm0213_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, strictConvexQuadrilateral_of_four_turns_pos
            (hpt.comp R.injective) ?_ ?_ ?_ ?_⟩
          all_goals dsimp [R, mkFourReordering, s]
          · rw [turn_swap_last]; simpa [A] using hAn
          · exact hC
          · exact hB
          · rw [turn_swap_first]; simpa [D] using hDn
      · have hCn : C < 0 := lt_of_le_of_ne (le_of_not_gt hC) hC0
        by_cases hD : 0 < D
        · exfalso
          linarith
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          left
          let s : Fin 4 → Fin 4 := ![1, 3, 2, 0]
          have hs : Function.Injective s := by
            simpa [s] using perm1320_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · simpa only [turn_rotate] using hB
          · rw [turn_reverse]; simpa [C] using hCn
          · rw [turn_reverse]; simpa [A] using hAn
    · have hBn : B < 0 := lt_of_le_of_ne (le_of_not_gt hB) hB0
      by_cases hC : 0 < C
      · by_cases hD : 0 < D
        · right
          let s : Fin 4 → Fin 4 := ![0, 2, 3, 1]
          have hs : Function.Injective s := by
            simpa [s] using perm0231_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, strictConvexQuadrilateral_of_four_turns_pos
            (hpt.comp R.injective) ?_ ?_ ?_ ?_⟩
          all_goals dsimp [R, mkFourReordering, s]
          · exact hC
          · rw [turn_swap_last]; simpa [A] using hAn
          · rw [turn_swap_last]; simpa [B] using hBn
          · simpa only [turn_rotate] using hD
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          left
          let s : Fin 4 → Fin 4 := ![0, 2, 1, 3]
          have hs : Function.Injective s := by
            simpa [s] using perm0213_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · exact hC
          · rw [turn_swap_first]; simpa [D] using hDn
          · rw [turn_swap_first]; simpa [B] using hBn
      · have hCn : C < 0 := lt_of_le_of_ne (le_of_not_gt hC) hC0
        by_cases hD : 0 < D
        · left
          let s : Fin 4 → Fin 4 := ![0, 3, 1, 2]
          have hs : Function.Injective s := by
            simpa [s] using perm0312_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, ?_⟩
          simp only [StrictlyInsideTriangle]
          dsimp [R, mkFourReordering, s]
          refine ⟨?_, ?_, ?_⟩
          · rw [turn_swap_last]; simpa [C] using hCn
          · simpa only [turn_rotate] using hD
          · rw [turn_swap_first]; simpa [A] using hAn
        · have hDn : D < 0 := lt_of_le_of_ne (le_of_not_gt hD) hD0
          right
          let s : Fin 4 → Fin 4 := ![0, 3, 2, 1]
          have hs : Function.Injective s := by
            simpa [s] using perm0321_injective
          let R := mkFourReordering x hx s hs
          refine ⟨R, strictConvexQuadrilateral_of_four_turns_pos
            (hpt.comp R.injective) ?_ ?_ ?_ ?_⟩
          all_goals dsimp [R, mkFourReordering, s]
          · rw [turn_swap_last]; simpa [C] using hCn
          · rw [turn_swap_last]; simpa [B] using hBn
          · rw [turn_swap_last]; simpa [A] using hAn
          · rw [turn_reverse]; simpa [D] using hDn

/-- Corollary 6.7: every colour class in a twelve-point hexagon-blocker
configuration has at most three points. -/
theorem colour_class_card_le_three
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card ≤ 12)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (c : Fin 4) :
    ((Finset.univ : Finset (hexBlockers P h)).filter
      fun p ↦ colour p = c).card ≤ 3 := by
  classical
  let B := hexBlockers P h
  let C : Finset B := Finset.univ.filter fun p ↦ colour p = c
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hle4 : C.card ≤ 4 := by
    simpa [B, C] using
      colour_class_card_le_four hfour hh hhP hside hcard colour hproper c
  change C.card ≤ 3
  by_contra hnot
  have hCcard : C.card = 4 := by omega
  let e : Fin 4 ≃ C := Fintype.equivOfCardEq (by simpa [hCcard])
  let x : Fin 4 → B := fun i ↦ ((e i : C) : B)
  have hx : Function.Injective x := by
    intro i j hij
    apply e.injective
    exact Subtype.ext hij
  have hxC (i : Fin 4) : x i ∈ C := (e i).property
  have hxmono (i : Fin 4) : colour (x i) = c :=
    (Finset.mem_filter.mp (hxC i)).2
  have hxsurj {p : B} (hp : p ∈ C) : ∃ i, x i = p := by
    let pc : C := ⟨p, hp⟩
    obtain ⟨i, hi⟩ := e.surjective pc
    refine ⟨i, ?_⟩
    exact congrArg Subtype.val hi
  have hgp : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      turn (x i : Point) (x j : Point) (x k : Point) ≠ 0 := by
    intro i j k hij hik hjk
    apply turn_ne_zero_of_same_colour hfourB hproper
    · exact hx.ne hij
    · exact hx.ne hjk
    · exact hx.ne hik.symm
    · exact (hxmono i).trans (hxmono j).symm
    · exact (hxmono j).trans (hxmono k).symm
  rcases four_point_dichotomy (fun p : B ↦ (p : Point))
      Subtype.val_injective x hx hgp with hconcave | hconvex
  · obtain ⟨R, hinside⟩ := hconcave
    have hRmono (i : Fin 4) : colour (R.q i) = c := by
      have hi : R.q i ∈ Set.range x := by
        rw [← R.range_eq]
        exact Set.mem_range_self i
      obtain ⟨j, hj⟩ := hi
      rw [← hj]
      exact hxmono j
    exact no_concave_mono_quad_in_hexBlockers
      hfour hh hhP hside hcard colour hproper
      (R.injective.ne (by decide))
      (R.injective.ne (by decide))
      (R.injective.ne (by decide))
      (R.injective.ne (by decide))
      (R.injective.ne (by decide))
      (R.injective.ne (by decide))
      ((hRmono 0).trans (hRmono 1).symm)
      ((hRmono 0).trans (hRmono 2).symm)
      ((hRmono 0).trans (hRmono 3).symm)
      hinside
  · obtain ⟨R, hq⟩ := hconvex
    have hRmono (i : Fin 4) : colour (R.q i) = c := by
      have hi : R.q i ∈ Set.range x := by
        rw [← R.range_eq]
        exact Set.mem_range_self i
      obtain ⟨j, hj⟩ := hi
      rw [← hj]
      exact hxmono j
    have hclass : ∀ p : B, colour p = c → ∃ i, p = R.q i := by
      intro p hp
      have hpC : p ∈ C := by simp [C, hp]
      obtain ⟨j, hj⟩ := hxsurj hpC
      have hjrange : x j ∈ Set.range R.q := by
        rw [R.range_eq]
        exact Set.mem_range_self j
      obtain ⟨i, hi⟩ := hjrange
      exact ⟨i, hj.symm.trans hi.symm⟩
    obtain ⟨pattern⟩ :=
      exists_standardQuadrilateralPattern hfourB colour hproper c R.q hq hRmono
        (fun p _ hp ↦ hclass p hp)
    have hmax := standardQuadrilateralPattern_maximal
      hfourB colour hproper c R.q hq hRmono pattern
    let A : Finset Point :=
      (Finset.univ : Finset (Fin 4)).image fun i ↦ (R.q i : Point)
    have hAB : A ⊆ B := by
      intro p hp
      simp only [A, Finset.mem_image] at hp
      obtain ⟨i, -, rfl⟩ := hp
      exact (R.q i).property
    have hAcard : A.card ≤ 5 := by
      calc
        A.card ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
        _ = 4 := by simp
        _ ≤ 5 := by omega
    have hAset : (A : Set Point) =
        Set.range (fun i ↦ (R.q i : Point)) := by
      ext p
      simp [A]
    have hcontained : ∀ p ∈ B, p ∈ convexHull ℝ (A : Set Point) := by
      intro p hp
      have hpq := hmax ⟨p, hp⟩
      rw [hAset]
      simpa [quadrilateralHull] using hpq
    exact (not_hexBlockers_subset_convexHull_of_card_le_five
      hfour hh hhP hside hAB hAcard) hcontained

end Lax56Proofs.HKBColourClasses
