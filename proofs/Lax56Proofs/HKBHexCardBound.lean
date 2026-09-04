import Lax56Proofs.HKBHexGeometry
import Lax56Proofs.HKBDirectMc
import Mathlib.Tactic

/-!
The cardinality consequence of `mc₃(4) ≤ 12` for the blockers of an empty
monochromatic hexagon.  This is deliberately kept out of `HKBHexGeometry`, so
the geometric library used to prove the bound does not depend on the bound.
-/

namespace Lax56Proofs.HKBHexGeometry

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.Blockers
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBDirectMc

/-- The blockers inside an empty monochromatic hexagon form a four-coloured
blocking set, so `mc₃(4) ≤ 12` bounds their number by twelve. -/
theorem hexBlockers_card_le_twelve
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (C : (visibilityGraph P).Coloring (Fin 5)) (c : Fin 5)
    (hnotc : ∀ p (hp : p ∈ hexBlockers P h),
      C ⟨p, hexBlockers_subset P h hp⟩ ≠ c) :
    (hexBlockers P h).card ≤ 12 := by
  let B := hexBlockers P h
  let col : B → Fin 4 := blockerColour C c (fun p => hnotc p p.property)
  apply card_le_twelve_of_four_coloured_blocking B
    (fun h4 => hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)) col
  intro x y hxy hcol
  have hsame : C ⟨x, hexBlockers_subset P h x.property⟩ =
      C ⟨y, hexBlockers_subset P h y.property⟩ := by
    have hsub :
        (⟨C ⟨x, hexBlockers_subset P h x.property⟩,
          hnotc x x.property⟩ : {d : Fin 5 // d ≠ c}) =
        ⟨C ⟨y, hexBlockers_subset P h y.property⟩,
          hnotc y y.property⟩ := by
      apply (otherColourEquiv c).injective
      simpa [col, blockerColour] using hcol
    exact congrArg Subtype.val hsub
  have hnvis : ¬Visible P x y := by
    intro hv
    exact C.valid
      (show (visibilityGraph P).Adj
        ⟨x, hexBlockers_subset P h x.property⟩
        ⟨y, hexBlockers_subset P h y.property⟩ from hv) hsame
  obtain ⟨r, hrP, hr⟩ := exists_blocker (Subtype.val_injective.ne hxy) hnvis
  have hx := mem_hexBlockers.mp x.property
  have hy := mem_hexBlockers.mp y.property
  have hrHull : r ∈ convexHull ℝ (Set.range h) :=
    (convex_convexHull ℝ (Set.range h)).openSegment_subset hx.2.1 hy.2.1 hr
  have hrNot : r ∉ Set.range h := by
    rintro ⟨i, rfl⟩
    exact hexVertex_not_between_hull_points hfour hh hhP
      (hexBlockers_subset P h x.property) (hexBlockers_subset P h y.property)
      hx.2.1 hy.2.1 hx.2.2 hy.2.2 (Subtype.val_injective.ne hxy) i hr
  exact ⟨r, mem_hexBlockers.mpr ⟨hrP, hrHull, hrNot⟩, hr⟩

end Lax56Proofs.HKBHexGeometry
