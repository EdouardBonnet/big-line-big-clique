import Lax56.ValtrFourLayer
import Lax56Proofs.ValtrCaps

namespace Lax56Proofs.EmptyHexagon

open Lax56.Geometry Lax56.HujterKisfaludiBak

/--
---
conclusion: Lax56.HujterKisfaludiBak.exists_emptyConvexHexagon
assumptions:
  - Lax56.ValtrFourLayer.exists_emptyHexagon_of_four_layers
---
The unoptimized Valtr argument, using the four-layer theorem interface so
Lax records its dependency on the proof in `Lax56Proofs.ValtrFourLayer`. The
minimum-polygon argument, consecutive-layer inequality, Erdős--Szekeres
bound, shear, and cyclic-order
bridge are all proved; no SAT solver or native decision axiom is used.
-/
theorem exists_emptyConvexHexagon
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card) (hgeneral : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, EmptyConvexHexagon P h :=
  Lax56Proofs.ValtrCaps.exists_emptyConvexHexagon_of_fourLayer
    Lax56.ValtrFourLayer.exists_emptyHexagon_of_four_layers P hP hgeneral

end Lax56Proofs.EmptyHexagon
