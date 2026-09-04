import Mathlib.Analysis.Convex.Segment
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
---
title: Point visibility in the real plane
type: definition
---
A pair of distinct points of a finite planar point set is visible when the
open segment joining it contains no point of the ambient set.  This module
also defines the visibility graph and the two geometric alternatives used in
the headline theorem.
-/

namespace Lax56.Geometry

/-- The real affine plane, represented by Cartesian coordinates. -/
abbrev Point := ℝ × ℝ

/-- The signed twice-area of the oriented triangle `p q r`. -/
def turn (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- `p` and `q` see one another with respect to the ambient finite set `P`. -/
def Visible (P : Finset Point) (p q : Point) : Prop :=
  p ≠ q ∧ ∀ r ∈ P, r ∉ openSegment ℝ p q

/-- The point-visibility graph of `P`; its vertices retain their membership proofs. -/
def visibilityGraph (P : Finset Point) : SimpleGraph P where
  Adj p q := Visible P p q
  symm := by
    intro p q hpq
    refine ⟨hpq.1.symm, ?_⟩
    simpa only [openSegment_symm] using hpq.2
  loopless := ⟨fun p hp => hp.1 rfl⟩

/-- The finite point set contains four distinct collinear points. -/
def HasFourCollinear (P : Finset Point) : Prop :=
  ∃ f : Fin 4 → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧ Collinear ℝ (Set.range f)

/-- The finite point set contains three distinct collinear points. -/
def HasThreeCollinear (P : Finset Point) : Prop :=
  ∃ f : Fin 3 → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧ Collinear ℝ (Set.range f)

/-- The finite point set contains `k` points that pairwise see one another. -/
def HasVisibleClique (P : Finset Point) (k : ℕ) : Prop :=
  ∃ f : Fin k → Point,
    Function.Injective f ∧ (∀ i, f i ∈ P) ∧
      Set.Pairwise (Set.range f) (Visible P)

end Lax56.Geometry
