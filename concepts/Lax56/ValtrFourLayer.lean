import Lax56.ConvexLayers

/-!
---
title: Valtr's four-layer lemma (remaining geometric input)
type: theorem
---
This is the unexpanded geometric ingredient in the supplied informal proof.
All reductions from this lemma to the empty-hexagon bound `2^428 + 1` and the
headline bound `10^(2^450)` are proved in the proof package. This declaration
is still an axiom: the sector and chain-replacement argument has not yet been
formalized. It must not be mistaken for a completed Lean proof of that argument.

Reference: Pavel Valtr, "On Empty Hexagons", Section 3 (Section 2 in the
author's preprint at https://kam.mff.cuni.cz/~valtr/h.ps).
-/

namespace Lax56.ValtrFourLayer

open Lax56.Geometry Lax56.ConvexLayers

/-- The weakened four-layer lemma requested for the unoptimized proof.
`layer S 3` is the fourth layer because layer indices start at zero. -/
axiom exists_emptyHexagon_of_four_layers
    (S : Finset Point) (hgeneral : ¬HasThreeCollinear S)
    (hminimal : MinimalOuter S) (hlarge : 9 ≤ (extremeLayer S).card)
    (hfourth : (layer S 3).Nonempty) : HasEmptyHexagon S

end Lax56.ValtrFourLayer
