import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic

/-!
---
title: Quantitative vertex-removal Erdős--Simonovits stability for K₆
type: theorem
---
For `0 < ε < 1/3750`, a `K₆`-free graph on at least 20 vertices with
more than `ex(m,K₆) - εm²` edges can be made 5-colourable by deleting
fewer than `3500εm` vertices.  This is the explicit vertex-removal form used
in the paper.
-/

namespace Lax56.VertexRemovalStability

open SimpleGraph

/-- The number of (unordered) edges of a finite simple graph. -/
noncomputable def edgeCount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

axiom exists_fiveColorable_delete
    {V : Type*} [Fintype V] (G : SimpleGraph V) (eps : ℝ)
    (hepsPos : 0 < eps) (hepsSmall : eps < 1 / 3750)
    (hcard : 20 ≤ Fintype.card V) (hK6 : G.CliqueFree 6)
    (hedges :
      (SimpleGraph.extremalNumber (Fintype.card V) (⊤ : SimpleGraph (Fin 6)) : ℝ) -
          eps * (Fintype.card V : ℝ) ^ 2 < edgeCount G) :
    ∃ Z : Set V,
      (Nat.card Z : ℝ) < 3500 * eps * Fintype.card V ∧
        (G.induce Zᶜ).Colorable 5

end Lax56.VertexRemovalStability
