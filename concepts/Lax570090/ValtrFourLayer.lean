import Lax570090.ConvexLayers

/-!
---
title: Valtr's four-layer lemma
type: theorem
---
This theorem specification is proved in `Lax570090Proofs.ValtrFourLayer`.
The outer-layer threshold sixteen allows an unoptimized endgame; it is
sufficient for the 216-point convex-position application. Chain replacement,
all endpoint cases, and the four-layer reduction are proved in Lean. The
empty-hexagon proof uses this theorem interface so Lax records the dependency
on the proof supplied in this package.

Reference: Pavel Valtr, "On Empty Hexagons", Section 3 (Section 2 in the
author's preprint at https://kam.mff.cuni.cz/~valtr/h.ps).
-/

namespace Lax570090.ValtrFourLayer

open Lax570090.Geometry Lax570090.ConvexLayers

/-- The weakened four-layer lemma requested for the unoptimized proof.
`layer S 3` is the fourth layer because layer indices start at zero. -/
axiom exists_emptyHexagon_of_four_layers
    (S : Finset Point) (hgeneral : ¬HasThreeCollinear S)
    (hminimal : MinimalOuter S) (hlarge : 16 ≤ (extremeLayer S).card)
    (hfourth : (layer S 3).Nonempty) : HasEmptyHexagon S

end Lax570090.ValtrFourLayer
