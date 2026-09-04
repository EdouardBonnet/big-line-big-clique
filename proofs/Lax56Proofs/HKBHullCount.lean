import Lax56Proofs.HKBConcavity
import Mathlib.Tactic

/-!
Hull-cardinality consequences of the six exposed side blockers.
-/

namespace Lax56Proofs.HKBHullCount

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.HKBConvexity
open Lax56Proofs.HKBHexGeometry

/-- If a subset of the blocker set generates a convex hull containing every
blocker, then it contains all six exposed side blockers. -/
theorem six_le_card_of_hexBlockers_subset_convexHull
    {P A : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (hAB : A ⊆ hexBlockers P h)
    (hconv : ∀ p ∈ hexBlockers P h,
      p ∈ convexHull ℝ (A : Set Point)) :
    6 ≤ A.card := by
  classical
  let f : Fin 6 → A := fun i ↦
    ⟨sideBlocker hside i,
      sideBlocker_mem_of_mem_convexHull hfour hh hhP hside hAB i
        (hconv _ (sideBlocker_mem hside i))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply sideBlocker_injective hh hside
    exact congrArg Subtype.val hij
  have hcard : Fintype.card (Fin 6) ≤ Fintype.card A :=
    Fintype.card_le_of_injective f hf
  simpa using hcard

/-- In particular, at most five blocker points cannot generate a convex hull
containing the entire blocker set. -/
theorem not_hexBlockers_subset_convexHull_of_card_le_five
    {P A : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    (hAB : A ⊆ hexBlockers P h) (hAcard : A.card ≤ 5) :
    ¬(∀ p ∈ hexBlockers P h, p ∈ convexHull ℝ (A : Set Point)) := by
  intro hconv
  have := six_le_card_of_hexBlockers_subset_convexHull
    hfour hh hhP hside hAB hconv
  omega

end Lax56Proofs.HKBHullCount
