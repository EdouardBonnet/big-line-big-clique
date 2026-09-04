import Lax56Proofs.HKBHullCount
import Mathlib.Tactic

/-!
The concave four-point part of the HKB colour-class bound.
-/

namespace Lax56Proofs.HKBConcaveColour

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBHullCount
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

private theorem four_vector_injective
    {X : Type*} {a b c d : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → X) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem six_vector_injective
    {X : Type*} {a b c d e f : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective (![a, b, c, d, e, f] : Fin 6 → X) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Four equally coloured points, one strictly inside the triangle of the
other three, force ten points of the blocking set into that triangle: the
four points themselves and six distinct blockers. -/
theorem ten_le_triangle_filter_card_of_concave_mono_quad
    {k : ℕ} {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin k) (hproper : ProperBlocking B colour)
    {a b c d : B}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcab : colour a = colour b)
    (hcac : colour a = colour c)
    (hcad : colour a = colour d)
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point) (d : Point)) :
    10 ≤ triangleCount B (a : Point) (b : Point) (c : Point) := by
  classical
  obtain ⟨rAB, hrAB⟩ := hproper a b hab hcab
  obtain ⟨rAC, hrAC⟩ := hproper a c hac hcac
  obtain ⟨rAD, hrAD⟩ := hproper a d had hcad
  obtain ⟨rBC, hrBC⟩ := hproper b c hbc (hcab.symm.trans hcac)
  obtain ⟨rBD, hrBD⟩ := hproper b d hbd (hcab.symm.trans hcad)
  obtain ⟨rCD, hrCD⟩ := hproper c d hcd (hcac.symm.trans hcad)

  have hcAB : colour rAB ≠ colour a :=
    blocker_colour_ne hfour hproper hab hcab hrAB
  have hcAC : colour rAC ≠ colour a :=
    blocker_colour_ne hfour hproper hac hcac hrAC
  have hcAD : colour rAD ≠ colour a :=
    blocker_colour_ne hfour hproper had hcad hrAD
  have hcBC : colour rBC ≠ colour a := by
    intro e
    exact (blocker_colour_ne hfour hproper hbc
      (hcab.symm.trans hcac) hrBC) (e.trans hcab)
  have hcBD : colour rBD ≠ colour a := by
    intro e
    exact (blocker_colour_ne hfour hproper hbd
      (hcab.symm.trans hcad) hrBD) (e.trans hcab)
  have hcCD : colour rCD ≠ colour a := by
    intro e
    exact (blocker_colour_ne hfour hproper hcd
      (hcac.symm.trans hcad) hrCD) (e.trans hcac)

  have hshare : ∀ {x y z r s : B}, x ≠ y → x ≠ z → y ≠ z →
      (r : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      (s : Point) ∈ openSegment ℝ (x : Point) (z : Point) → r ≠ s := by
    intro x y z r s hxy hxz hyz hry hrs hrsEq
    apply hyz
    apply other_endpoint_eq_of_common_blocker hfour hxy hxz hry
    simpa only [hrsEq] using hrs

  have hABAC : rAB ≠ rAC := hshare hab hac hbc hrAB hrAC
  have hABAD : rAB ≠ rAD := hshare hab had hbd hrAB hrAD
  have hABBC : rAB ≠ rBC := by
    apply hshare hab.symm hbc hac
    · simpa only [openSegment_symm] using hrAB
    · exact hrBC
  have hABBD : rAB ≠ rBD := by
    apply hshare hab.symm hbd had
    · simpa only [openSegment_symm] using hrAB
    · exact hrBD
  have hACAD : rAC ≠ rAD := hshare hac had hcd hrAC hrAD
  have hACBC : rAC ≠ rBC := by
    apply hshare hac.symm hbc.symm hab
    · simpa only [openSegment_symm] using hrAC
    · simpa only [openSegment_symm] using hrBC
  have hACCD : rAC ≠ rCD := by
    apply hshare hac.symm hcd had
    · simpa only [openSegment_symm] using hrAC
    · exact hrCD
  have hADBD : rAD ≠ rBD := by
    apply hshare had.symm hbd.symm hab
    · simpa only [openSegment_symm] using hrAD
    · simpa only [openSegment_symm] using hrBD
  have hADCD : rAD ≠ rCD := by
    apply hshare had.symm hcd.symm hac
    · simpa only [openSegment_symm] using hrAD
    · simpa only [openSegment_symm] using hrCD
  have hBCBD : rBC ≠ rBD := hshare hbc hbd hcd hrBC hrBD
  have hBCCD : rBC ≠ rCD := by
    apply hshare hbc.symm hcd hbd
    · simpa only [openSegment_symm] using hrBC
    · exact hrCD
  have hBDCD : rBD ≠ rCD := by
    apply hshare hbd.symm hcd.symm hbc
    · simpa only [openSegment_symm] using hrBD
    · simpa only [openSegment_symm] using hrCD

  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle hd
  have hABCD : rAB ≠ rCD := by
    intro e
    have hCD' : (rAB : Point) ∈
        openSegment ℝ (c : Point) (d : Point) := by simpa [e] using hrCD
    have hpos := edgeTurn_pos_of_mem_openSegment hCD'
      habc.le hd.1.le (Or.inl habc)
    have hzero : turn (a : Point) (b : Point) (rAB : Point) = 0 :=
      turn_eq_zero_of_between hrAB
    linarith
  have hACBD : rAC ≠ rBD := by
    intro e
    have hBD' : (rAC : Point) ∈
        openSegment ℝ (b : Point) (d : Point) := by simpa [e] using hrBD
    have hcab : 0 < turn (c : Point) (a : Point) (b : Point) := by
      rw [turn_rotate, turn_rotate]
      exact habc
    have hpos := edgeTurn_pos_of_mem_openSegment hBD'
      hcab.le hd.2.2.le (Or.inl hcab)
    have hzeroAC : turn (a : Point) (c : Point) (rAC : Point) = 0 :=
      turn_eq_zero_of_between hrAC
    have hzeroCA : turn (c : Point) (a : Point) (rAC : Point) = 0 := by
      rw [turn_swap_first, hzeroAC, neg_zero]
    linarith
  have hADBC : rAD ≠ rBC := by
    intro e
    have hbca : 0 < turn (b : Point) (c : Point) (a : Point) := by
      rw [turn_rotate]
      exact habc
    have hpos := edgeTurn_pos_of_mem_openSegment hrAD
      hbca.le hd.2.1.le (Or.inl hbca)
    have hzero : turn (b : Point) (c : Point) (rAD : Point) = 0 := by
      have hz := turn_eq_zero_of_between hrBC
      simpa [e] using hz
    linarith

  let q : Fin 4 → B := ![a, b, c, d]
  have hq : Function.Injective q := by
    exact four_vector_injective hab hac had hbc hbd hcd
  let r : Fin 6 → B := ![rAB, rAC, rAD, rBC, rBD, rCD]
  have hr : Function.Injective r := by
    exact six_vector_injective hABAC hABAD hABBC hABBD hABCD
      hACAD hACBC hACBD hACCD hADBC hADBD hADCD hBCBD hBCCD hBDCD
  have hqcolour (i : Fin 4) : colour (q i) = colour a := by
    fin_cases i
    · rfl
    · exact hcab.symm
    · exact hcac.symm
    · exact hcad.symm
  have hrcolour (i : Fin 6) : colour (r i) ≠ colour a := by
    fin_cases i
    · exact hcAB
    · exact hcAC
    · exact hcAD
    · exact hcBC
    · exact hcBD
    · exact hcCD
  let f : Sum (Fin 4) (Fin 6) → B := Sum.elim q r
  have hf : Function.Injective f := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (hq hij)
    · exfalso
      apply hrcolour j
      exact (congrArg colour hij).symm.trans (hqcolour i)
    · exfalso
      apply hrcolour i
      exact (congrArg colour hij).trans (hqcolour j)
    · exact congrArg Sum.inr (hr hij)

  have haHull : (a : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    vertex_mem_triangleHull _ _ _
  have hbHull : (b : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    subset_convexHull ℝ _ (by simp [triangleHull])
  have hcHull : (c : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    subset_convexHull ℝ _ (by simp [triangleHull])
  have hdHull : (d : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    strictlyInsideTriangle_mem_triangleHull hd
  have hqhull (i : Fin 4) :
      (q i : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    fin_cases i
    · exact haHull
    · exact hbHull
    · exact hcHull
    · exact hdHull
  have hrhull (i : Fin 6) :
      (r i : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    fin_cases i
    · exact openSegment_mem_triangleHull_of_mem haHull hbHull hrAB
    · exact openSegment_mem_triangleHull_of_mem haHull hcHull hrAC
    · exact openSegment_mem_triangleHull_of_mem haHull hdHull hrAD
    · exact openSegment_mem_triangleHull_of_mem hbHull hcHull hrBC
    · exact openSegment_mem_triangleHull_of_mem hbHull hdHull hrBD
    · exact openSegment_mem_triangleHull_of_mem hcHull hdHull hrCD
  have hfhull (i : Sum (Fin 4) (Fin 6)) :
      (f i : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    rcases i with i | i
    · exact hqhull i
    · exact hrhull i
  let g : Sum (Fin 4) (Fin 6) → (B.filter fun p ↦
      p ∈ triangleHull (a : Point) (b : Point) (c : Point)) := fun i ↦
    ⟨f i, Finset.mem_filter.mpr ⟨(f i).property, hfhull i⟩⟩
  have hg : Function.Injective g := by
    intro i j hij
    apply hf
    apply Subtype.ext
    have hval := congrArg (fun x : (B.filter fun p ↦
      p ∈ triangleHull (a : Point) (b : Point) (c : Point)) ↦ (x : Point)) hij
    simpa [g] using hval
  have hcard := Fintype.card_le_of_injective g hg
  simpa [triangleCount] using hcard

/-- Lemma 6.3: under the hexagon hypotheses a monochromatic concave
four-point class is impossible.  Ten points would lie in its outer triangle,
so the whole blocker set would have a convex hull generated by at most the
three outer vertices and two exterior points. -/
theorem no_concave_mono_quad_in_hexBlockers
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : Lax56.HujterKisfaludiBak.StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card ≤ 12)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    {a b c d : hexBlockers P h}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (had : a ≠ d) (hbd : b ≠ d) (hcd : c ≠ d)
    (hcab : colour a = colour b)
    (hcac : colour a = colour c)
    (hcad : colour a = colour d)
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point) (d : Point)) :
    False := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hten : 10 ≤ triangleCount B (a : Point) (b : Point) (c : Point) :=
    ten_le_triangle_filter_card_of_concave_mono_quad hfourB colour hproper
      hab hac hbc had hbd hcd hcab hcac hcad hd
  let inside : Finset Point := B.filter fun p ↦
    p ∈ triangleHull (a : Point) (b : Point) (c : Point)
  let outside : Finset Point := B.filter fun p ↦
    p ∉ triangleHull (a : Point) (b : Point) (c : Point)
  have hins : 10 ≤ inside.card := by
    simpa [inside, triangleCount] using hten
  have hpartition : inside.card + outside.card = B.card := by
    simpa [inside, outside] using
      (Finset.card_filter_add_card_filter_not
        (s := B) (p := fun p ↦
          p ∈ triangleHull (a : Point) (b : Point) (c : Point)))
  have hout : outside.card ≤ 2 := by
    change B.card ≤ 12 at hcard
    omega
  let outer : Finset Point := {(a : Point), (b : Point), (c : Point)}
  let A : Finset Point := outer ∪ outside
  have habv : (a : Point) ≠ (b : Point) := Subtype.val_injective.ne hab
  have hacv : (a : Point) ≠ (c : Point) := Subtype.val_injective.ne hac
  have hbcv : (b : Point) ≠ (c : Point) := Subtype.val_injective.ne hbc
  have houtercard : outer.card = 3 := by
    simp [outer, habv, hacv, hbcv]
  have hAcard : A.card ≤ 5 := by
    have hu := Finset.card_union_le outer outside
    dsimp [A]
    omega
  have hAB : A ⊆ B := by
    intro p hp
    have hp' : p ∈ outer ∨ p ∈ outside := Finset.mem_union.mp hp
    rcases hp' with hpOuter | hpOutside
    · simp only [outer, Finset.mem_insert, Finset.mem_singleton] at hpOuter
      rcases hpOuter with rfl | rfl | rfl
      · exact a.property
      · exact b.property
      · exact c.property
    · exact (Finset.mem_filter.mp hpOutside).1
  have haA : (a : Point) ∈ convexHull ℝ (A : Set Point) :=
    subset_convexHull ℝ _ (by simp [A, outer])
  have hbA : (b : Point) ∈ convexHull ℝ (A : Set Point) :=
    subset_convexHull ℝ _ (by simp [A, outer])
  have hcA : (c : Point) ∈ convexHull ℝ (A : Set Point) :=
    subset_convexHull ℝ _ (by simp [A, outer])
  have hconv : ∀ p ∈ B, p ∈ convexHull ℝ (A : Set Point) := by
    intro p hpB
    by_cases hpHull : p ∈ triangleHull (a : Point) (b : Point) (c : Point)
    · exact (triangleHull_subset_of_mem (C := convexHull ℝ (A : Set Point))
        (convex_convexHull ℝ (A : Set Point)) haA hbA hcA) hpHull
    · apply subset_convexHull ℝ (A : Set Point)
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_filter.mpr ⟨hpB, hpHull⟩))
  exact not_hexBlockers_subset_convexHull_of_card_le_five
    hfour hh hhP hside hAB hAcard hconv

end Lax56Proofs.HKBConcaveColour
