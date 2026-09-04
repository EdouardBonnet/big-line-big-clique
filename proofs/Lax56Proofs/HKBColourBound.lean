import Lax56Proofs.HKBPlanarFive
import Mathlib.Tactic

/-!
The five-or-more part of the HKB colour-class bound.
-/

namespace Lax56Proofs.HKBColourBound

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBHullCount
open Lax56Proofs.HKBPlanarFive
open Lax56Proofs.OrderGeometry

/-- Select five points of a finite subtype and put them in canonical
lexicographic order. -/
private theorem exists_ordered_five_in_finset
    {B : Finset Point} (C : Finset B) (hfive : 5 ≤ C.card) :
    ∃ x : Fin 5 → B, Function.Injective x ∧
      (∀ i, x i ∈ C) ∧
      StrictMono (fun i ↦ toLex (x i : Point)) := by
  classical
  obtain ⟨X, hXC, hXcard⟩ := Finset.exists_subset_card_eq hfive
  let A : Finset Point := X.image (fun q : B ↦ (q : Point))
  have hAcard : A.card = 5 := by
    change (X.image (fun q : B ↦ (q : Point))).card = 5
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hXcard]
  let idx : Fin 5 → Fin A.card := fun i ↦ Fin.cast hAcard.symm i
  let x : Fin 5 → B := fun i ↦ ⟨orderedPoint A (idx i), by
    have hpA := orderedPoint_mem A (idx i)
    obtain ⟨q, hqX, hq⟩ := Finset.mem_image.mp hpA
    rw [← hq]
    exact q.property⟩
  have hidx : Function.Injective idx := by
    intro i j hij
    apply Fin.ext
    simpa [idx] using congrArg Fin.val hij
  have hx : Function.Injective x := by
    intro i j hij
    apply hidx
    apply orderedPoint_injective A
    simpa [x] using congrArg Subtype.val hij
  have hxC (i : Fin 5) : x i ∈ C := by
    have hpA := orderedPoint_mem A (idx i)
    obtain ⟨q, hqX, hq⟩ := Finset.mem_image.mp hpA
    have hqx : q = x i := by
      apply Subtype.ext
      simpa [x] using hq
    rw [← hqx]
    exact hXC hqX
  have hlex : StrictMono (fun i ↦ toLex (x i : Point)) := by
    intro i j hij
    apply orderedPoint_strictMono A
    change (idx i).val < (idx j).val
    simpa [idx] using hij
  exact ⟨x, hx, hxC, hlex⟩

/-- Lemma 6.2: in the twelve-point hexagon blocker set, no colour class has
five points. -/
theorem colour_class_card_le_four
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
      fun p ↦ colour p = c).card ≤ 4 := by
  classical
  let B := hexBlockers P h
  let C : Finset B := Finset.univ.filter fun p ↦ colour p = c
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  change C.card ≤ 4
  by_contra hnot
  have hfive : 5 ≤ C.card := by omega
  obtain ⟨x, hxinj, hxC, hxlex⟩ := exists_ordered_five_in_finset C hfive
  have hxmono (i : Fin 5) : colour (x i) = c :=
    (Finset.mem_filter.mp (hxC i)).2
  obtain ⟨R, hRcard, hRcolour, hRhull⟩ :=
    exists_seven_distinct_blockers_of_five_mono
      hfourB colour hproper c x hxinj hxmono hxlex
  have hRC : Disjoint R C := by
    rw [Finset.disjoint_left]
    intro r hrR hrC
    exact hRcolour r hrR (Finset.mem_filter.mp hrC).2
  have hUnionCard : (R ∪ C).card = R.card + C.card :=
    Finset.card_union_of_disjoint hRC
  have hUnionLe : (R ∪ C).card ≤ B.card := by
    have hsub : R ∪ C ⊆ (Finset.univ : Finset B) := Finset.subset_univ _
    simpa using Finset.card_le_card hsub
  have hcount : 7 + C.card ≤ B.card := by
    simpa [hUnionCard, hRcard] using hUnionLe
  have hBcardLe : B.card ≤ 12 := by
    simpa [B] using hcard
  have hCcard : C.card = 5 := by
    omega
  have hBcard : B.card = 12 := by
    omega
  have hUnionEq : R ∪ C = (Finset.univ : Finset B) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [hUnionCard, hRcard, hCcard]
    simpa [hBcard]
  let A : Finset Point := Finset.univ.image fun i : Fin 5 ↦ (x i : Point)
  have hAcard : A.card = 5 := by
    change ((Finset.univ : Finset (Fin 5)).image
      (fun i : Fin 5 ↦ (x i : Point))).card = 5
    rw [Finset.card_image_of_injective _]
    · simp
    · exact fun i j hij ↦ hxinj (Subtype.val_injective hij)
  have hAB : A ⊆ B := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
    exact (x i).property
  have hxSurjC : ∀ z ∈ C, ∃ i : Fin 5, x i = z := by
    let xC : Fin 5 → C := fun i ↦ ⟨x i, hxC i⟩
    have hxCinj : Function.Injective xC := by
      intro i j hij
      apply hxinj
      exact congrArg Subtype.val hij
    have hxCcard : Fintype.card (Fin 5) = Fintype.card C := by
      simpa [hCcard]
    have hxCsurj : Function.Surjective xC :=
      ((Fintype.bijective_iff_injective_and_card xC).2 ⟨hxCinj, hxCcard⟩).2
    intro z hzC
    obtain ⟨i, hi⟩ := hxCsurj ⟨z, hzC⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hconv : ∀ p ∈ B, p ∈ convexHull ℝ (A : Set Point) := by
    intro p hpB
    have hpUnion : (⟨p, hpB⟩ : B) ∈ R ∪ C := by
      rw [hUnionEq]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hpUnion with hpR | hpC
    · have hp := hRhull ⟨p, hpB⟩ hpR
      simpa [A] using hp
    · obtain ⟨i, hi⟩ := hxSurjC ⟨p, hpB⟩ hpC
      have hpA : p ∈ A := by
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        exact congrArg Subtype.val hi
      exact subset_convexHull ℝ (A : Set Point) hpA
  exact (not_hexBlockers_subset_convexHull_of_card_le_five
    hfour hh hhP hside hAB (by omega)) hconv

end Lax56Proofs.HKBColourBound
