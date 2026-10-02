import Lax570090.ValtrFourLayer
import Lax570090Proofs.ValtrCaps

namespace Lax570090Proofs.EmptyHexagon

open Lax570090.Geometry Lax570090.HujterKisfaludiBak

/--
---
conclusion: Lax570090.HujterKisfaludiBak.exists_emptyConvexHexagon
assumptions:
  - Lax570090.ValtrFourLayer.exists_emptyHexagon_of_four_layers
---
The unoptimized Valtr argument, using the four-layer theorem interface so
Lax records its dependency on the proof in `Lax570090Proofs.ValtrFourLayer`. The
minimum-polygon argument, consecutive-layer inequality, Erdős--Szekeres
bound, shear, and cyclic-order
bridge are all proved; no SAT solver or native decision axiom is used.
-/
theorem exists_emptyConvexHexagon
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card) (hgeneral : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, EmptyConvexHexagon P h :=
  Lax570090Proofs.ValtrCaps.exists_emptyConvexHexagon_of_fourLayer
    Lax570090.ValtrFourLayer.exists_emptyHexagon_of_four_layers P hP hgeneral

end Lax570090Proofs.EmptyHexagon
