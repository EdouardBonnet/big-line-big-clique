import Lax56.MainTheorem
import Lax56Proofs.NumericalBounds

namespace Lax56Proofs.MainTheorem

open Lax56.Geometry
open Lax56Proofs.NumericalBounds

/--
---
conclusion: Lax56.MainTheorem.large_point_set_four_collinear_or_visible_six
assumptions:
  - Lax56.HujterKisfaludiBak.exists_emptyConvexHexagon
  - Lax56.VertexRemovalStability.exists_fiveColorable_delete
---
Every finite set of at least $10^{2^{450}}$ points in the real plane has
four distinct collinear points or six points which are pairwise visible with
respect to the entire set. The visibility-colouring and vertex-removal
stability inputs are proved in this package. The empty-convex-hexagon bound
$h(6) \le 2^{428}+1$ is derived from the fully proved four-layer lemma.
The empty-hexagon and stability inputs are used through their theorem
interfaces so Lax records the proof tree. Both have proofs in this package;
composing the tree leaves only Lean's standard logical axioms.
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
