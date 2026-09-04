import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Analysis.Convex.Hull
import Lax56.Geometry

/-!
---
title: The empty-hexagon input to the Hujter--Kisfaludi-Bak theorem
type: definition
---
This module isolates the geometric input that is external to the
Hujter--Kisfaludi-Bak blocking argument: the upper bound `h(6) ≤ 463` for the
empty convex hexagon number.  The visibility-colouring theorem itself is
proved in `Lax56Proofs.HujterKisfaludiBak`.
-/

namespace Lax56.HujterKisfaludiBak

open Lax56.Geometry

/-- Six labelled vertices in strict counterclockwise cyclic convex position.

The last conjunct records the complete cyclic order type, not merely its six
supporting-edge consequences.  This is useful in the direct geometric proof:
an increasing triple of cyclic labels is positively oriented. -/
def StrictConvexHexagon (h : Fin 6 → Point) : Prop :=
  Function.Injective h ∧
    (∀ i j : Fin 6, j ≠ i → j ≠ i + 1 →
      0 < turn (h i) (h (i + 1)) (h j)) ∧
    ∀ i j k : Fin 6, i < j → j < k →
      0 < turn (h i) (h j) (h k)

/-- A convex hexagon whose convex hull contains no further point of `P`. -/
def EmptyConvexHexagon (P : Finset Point) (h : Fin 6 → Point) : Prop :=
  StrictConvexHexagon h ∧
    (∀ i, h i ∈ P) ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (Set.range h) → p ∈ Set.range h

/-- The currently external geometric input, in an ordered form convenient for
the blocking proof.  This is precisely the bound `h(6) ≤ 463`. -/
axiom exists_emptyConvexHexagon
    (P : Finset Point) (hP : 463 ≤ P.card)
    (hgeneral : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, EmptyConvexHexagon P h

end Lax56.HujterKisfaludiBak
