import Lax56.MainTheorem
import Lax56Proofs.NumericalBounds

namespace Lax56Proofs.MainTheorem

open Lax56.Geometry
open Lax56Proofs.NumericalBounds

/--
---
conclusion: Lax56.MainTheorem.large_point_set_four_collinear_or_visible_six
assumptions:
  - Lax56.HujterKisfaludiBak.visibilityGraph_not_fiveColorable
---
Every finite set of at least $10^{11055931}$ points in the real plane has
four distinct collinear points or six points which are pairwise visible with
respect to the entire set.  This formalizes the full argument of the paper;
the two named combinatorial inputs are isolated as the next proof stage.
-/
theorem large_point_set_four_collinear_or_visible_six
    (P : Finset Point) (hP : 10 ^ 11055931 ≤ P.card) :
    HasFourCollinear P ∨ HasVisibleClique P 6 := by
  by_cases hfour : HasFourCollinear P
  · exact Or.inl hfour
  by_cases hvisible : HasVisibleClique P 6
  · exact Or.inr hvisible
  exact (impossible_large_bad_set P hfour hvisible hP).elim

end Lax56Proofs.MainTheorem
