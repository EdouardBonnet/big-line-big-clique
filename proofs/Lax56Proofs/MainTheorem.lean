import Lax56.MainTheorem
import Lax56Proofs.NumericalBounds

namespace Lax56Proofs.MainTheorem

open Lax56.Geometry
open Lax56Proofs.NumericalBounds

/--
---
conclusion: Lax56.MainTheorem.large_point_set_four_collinear_or_visible_six
assumptions:
  - Lax56.ValtrFourLayer.exists_emptyHexagon_of_four_layers
---
Every finite set of at least $10^{2^{450}}$ points in the real plane has
four distinct collinear points or six points which are pairwise visible with
respect to the entire set. The visibility-colouring and vertex-removal
stability inputs are proved in this package. The empty-convex-hexagon bound
$h(6) \le 2^{428}+1$ is derived from Valtr's four-layer lemma, which is the
remaining external geometric input.
-/
theorem large_point_set_four_collinear_or_visible_six
    (P : Finset Point) (hP : 10 ^ (2 ^ 450) ≤ P.card) :
    HasFourCollinear P ∨ HasVisibleClique P 6 := by
  by_cases hfour : HasFourCollinear P
  · exact Or.inl hfour
  by_cases hvisible : HasVisibleClique P 6
  · exact Or.inr hvisible
  exact (impossible_large_bad_set P hfour hvisible hP).elim

end Lax56Proofs.MainTheorem
