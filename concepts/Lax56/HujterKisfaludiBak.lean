import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Analysis.Convex.Hull
import Lax56.Geometry

/-!
---
title: The unoptimized empty-hexagon bound
type: definition
---
This module states the upper bound `h(6) ≤ 2^428 + 1` and the ordered hexagon
definitions used by the blocking argument. The bound is proved in
`Lax56Proofs.EmptyHexagon` from Valtr's four-layer lemma. The visibility-colouring
theorem is proved in `Lax56Proofs.HujterKisfaludiBak`.
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

/-- The deliberately unoptimized Valtr bound `h(6) ≤ 2^428 + 1`, via 216
points in convex position. Its proof in `Lax56Proofs.EmptyHexagon` uses the
four-layer theorem interface, whose proof is also in this package. The
visibility-colouring argument uses this interface so Lax records the dependency;
the composed proof tree uses only standard logical axioms. -/
axiom exists_emptyConvexHexagon
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card)
    (hgeneral : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, EmptyConvexHexagon P h

end Lax56.HujterKisfaludiBak
