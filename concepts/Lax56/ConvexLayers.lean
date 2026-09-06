import Lax56.Geometry
import Mathlib.Analysis.Convex.Independent

/-!
---
title: Convex layers and minimal polygons
type: definition
---
The unordered, finite-set definitions used in the unoptimized convex-layer
route to Valtr's empty-hexagon theorem. No geometric theorem is assumed here.
-/

namespace Lax56.ConvexLayers

open Lax56.Geometry
open scoped Classical

/-- Every point is a vertex: no point lies in the convex hull of the others. -/
def ConvexPosition (P : Finset Point) : Prop :=
  ConvexIndependent ℝ (fun p : {p : Point // p ∈ P} ↦ p.val)

/-- Vertices of the convex hull, including all points of sets of size at most two. -/
noncomputable def extremeLayer (P : Finset Point) : Finset Point :=
  P.filter (fun p ↦ p ∈ (convexHull ℝ (P : Set Point)).extremePoints ℝ)

/-- The remainder after deleting the current outer layer. -/
noncomputable def inner (P : Finset Point) : Finset Point := P \ extremeLayer P

/-- The remainder after `n` layers have been removed. -/
noncomputable def remainder (P : Finset Point) : ℕ → Finset Point
  | 0 => P
  | n + 1 => inner (remainder P n)

/-- Layers are indexed from zero: `layer P 0` is the outer layer. -/
noncomputable def layer (P : Finset Point) (n : ℕ) : Finset Point :=
  extremeLayer (remainder P n)

/-- All ambient points in the convex hull of `A`, not just its interior points. -/
noncomputable def hullClosure (P A : Finset Point) : Finset Point :=
  P.filter (fun p ↦ p ∈ convexHull ℝ (A : Set Point))

/-- Passing from `P` to `S` loses no ambient point inside the new convex hull. -/
def HullClosedIn (P S : Finset Point) : Prop :=
  S ⊆ P ∧ ∀ p ∈ P, p ∈ convexHull ℝ (S : Set Point) → p ∈ S

/-- The exact minimality condition in the proposed four-layer lemma. -/
def MinimalOuter (S : Finset Point) : Prop :=
  ∀ X ⊆ S, ConvexPosition X → (extremeLayer S).card ≤ X.card → X = extremeLayer S

/-- An unordered empty convex polygon with exactly `k` vertices. -/
def EmptyPolygon (P H : Finset Point) (k : ℕ) : Prop :=
  H ⊆ P ∧ H.card = k ∧ ConvexPosition H ∧
    ∀ p ∈ P, p ∈ convexHull ℝ (H : Set Point) → p ∈ H

def HasEmptyHexagon (P : Finset Point) : Prop :=
  ∃ H, EmptyPolygon P H 6

end Lax56.ConvexLayers
