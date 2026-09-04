import Lax56.Geometry

/-!
---
title: Large finite point sets have four collinear points or a visible six-clique
type: theorem
---
Every finite set of at least `10^11055931` points in the real plane contains
four distinct collinear points or six distinct points that pairwise see one
another with respect to the whole set.
-/

namespace Lax56.MainTheorem

open Lax56.Geometry

axiom large_point_set_four_collinear_or_visible_six
    (P : Finset Point) (hP : 10 ^ 11055931 ≤ P.card) :
    HasFourCollinear P ∨ HasVisibleClique P 6

end Lax56.MainTheorem
