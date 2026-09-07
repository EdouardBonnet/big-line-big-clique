import Lax56Proofs.ConvexLayers
import Lax56.HujterKisfaludiBak

/-!
The reduction supplied by the user, with intermediate inputs exposed as
ordinary hypotheses. `ValtrCaps`, `ErdosSzekeres`, and `CyclicOrder` discharge
all of these inputs except the four-layer lemma. `EmptyHexagon` connects the
result to the main proof with that sole remaining external assumption.

Reference: Pavel Valtr, "On Empty Hexagons", Section 3 of the published paper
(Section 2 in the author's preprint, https://kam.mff.cuni.cz/~valtr/h.ps).
-/

namespace Lax56Proofs.ValtrReduction

open Lax56.Geometry Lax56.ConvexLayers Lax56Proofs.ConvexLayers

/-- The geometric four-layer ingredient. The threshold 16 is sufficient
for the three-five-sector-block proof of the endgame and for the intended
216-point application. Since layers are zero-indexed, `layer S 3` is the
fourth layer. -/
def FourLayerLemma : Prop :=
  ∀ S : Finset Point, ¬HasThreeCollinear S → MinimalOuter S →
    16 ≤ (extremeLayer S).card → (layer S 3).Nonempty → HasEmptyHexagon S

/-- The consecutive-six-vertex-block inequality, proved in
`ValtrCaps.consecutive_layer_bound` using cyclic polygon/chord separation. -/
def ConsecutiveLayerBound : Prop :=
  ∀ Q : Finset Point, ¬HasThreeCollinear Q → ¬HasEmptyHexagon Q →
    (extremeLayer Q).card ≤ 6 * (extremeLayer (inner Q)).card + 5

/-- Four-layer emptiness makes the third remainder a convex-position set. -/
theorem third_remainder_convexPosition {S : Finset Point} (hfour : layer S 3 = ∅) :
    ConvexPosition (remainder S 2) := by
  have hrem : remainder S 3 = ∅ := (extremeLayer_eq_empty_iff _).mp hfour
  have heq : extremeLayer (remainder S 2) = remainder S 2 := by
    apply Finset.Subset.antisymm (extremeLayer_subset _)
    exact Finset.sdiff_eq_empty_iff_subset.mp hrem
  rw [← heq]
  exact extremeLayer_convexPosition _

/-- With no hexagon and no fourth layer, the third layer has at most five vertices. -/
theorem third_layer_card_le_five {S : Finset Point}
    (hno : ¬HasEmptyHexagon S) (hfour : layer S 3 = ∅) : (layer S 2).card ≤ 5 := by
  have hconv := third_remainder_convexPosition hfour
  have hsmall : (remainder S 2).card ≤ 5 := by
    by_contra h
    exact hno (hasEmptyHexagon_transfer (remainder_hullClosedIn S 2)
      (hasEmptyHexagon_of_convexPosition hconv (by omega)))
  exact (Finset.card_le_card (extremeLayer_subset _)).trans hsmall

/-- The complete `216 → 215` contradiction, conditional only on the two stated
geometric ingredients. All minimality, hull-closure and residual-set arguments
are proved in `ConvexLayers`. -/
theorem hasEmptyHexagon_of_convex216
    (fourLayer : FourLayerLemma) (layerBound : ConsecutiveLayerBound)
    (P : Finset Point) (hgeneral : ¬HasThreeCollinear P)
    (hconvex : ∃ A ⊆ P, A.card = 216 ∧ ConvexPosition A) : HasEmptyHexagon P := by
  classical
  by_contra hno
  obtain ⟨A, hAP, hAcard, _hA, hext, hminimal⟩ := exists_minimal_polygon P 216 hconvex
  let S := hullClosure P A
  have hSgen : ¬HasThreeCollinear S :=
    fun h ↦ hgeneral (hasThreeCollinear_mono (hullClosure_subset P A) h)
  have hSno : ¬HasEmptyHexagon S :=
    fun h ↦ hno (hasEmptyHexagon_transfer (hullClosure_hullClosedIn P A) h)
  have houter : (extremeLayer S).card = 216 := by rw [hext, hAcard]
  have hD : layer S 3 = ∅ := by
    by_contra hD
    exact hSno (fourLayer S hSgen hminimal (by omega)
      (Finset.nonempty_iff_ne_empty.mpr hD))
  have hC := third_layer_card_le_five hSno hD
  have hinnergen : ¬HasThreeCollinear (inner S) :=
    fun h ↦ hSgen (hasThreeCollinear_mono (inner_subset S) h)
  have hinnerno : ¬HasEmptyHexagon (inner S) :=
    fun h ↦ hSno (hasEmptyHexagon_transfer (inner_hullClosedIn S) h)
  have hB := layerBound (inner S) hinnergen hinnerno
  have hA := layerBound S hSgen hSno
  change (extremeLayer (inner (inner S))).card ≤ 5 at hC
  omega

/-- The weak Erdős--Szekeres statement needed for the numerical corollary,
proved in `ErdosSzekeres.weak_erdos_szekeres`. -/
def WeakErdosSzekeres : Prop :=
  ∀ (P : Finset Point) (k : ℕ), 2 ≤ k → ¬HasThreeCollinear P →
    2 ^ (2 * k - 4) < P.card → ∃ A ⊆ P, A.card = k ∧ ConvexPosition A

theorem hasEmptyHexagon_of_card
    (fourLayer : FourLayerLemma) (layerBound : ConsecutiveLayerBound)
    (erdosSzekeres : WeakErdosSzekeres)
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card)
    (hgeneral : ¬HasThreeCollinear P) : HasEmptyHexagon P := by
  apply hasEmptyHexagon_of_convex216 fourLayer layerBound P hgeneral
  exact erdosSzekeres P 216 (by omega) hgeneral (by norm_num; omega)

/-- Bridge to the cyclically labelled representation used by the blocker
argument, proved in `CyclicOrder.ordered_hexagon_bridge`. -/
def OrderedHexagonBridge : Prop :=
  ∀ P : Finset Point, ¬HasThreeCollinear P → HasEmptyHexagon P →
    ∃ h : Fin 6 → Point, Lax56.HujterKisfaludiBak.EmptyConvexHexagon P h

/-- The modular reduction with all intermediate inputs visible as parameters.
There is no use of the old empty-hexagon axiom. -/
theorem exists_emptyConvexHexagon_of_ingredients
    (fourLayer : FourLayerLemma) (layerBound : ConsecutiveLayerBound)
    (erdosSzekeres : WeakErdosSzekeres) (ordered : OrderedHexagonBridge)
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card)
    (hgeneral : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, Lax56.HujterKisfaludiBak.EmptyConvexHexagon P h :=
  ordered P hgeneral (hasEmptyHexagon_of_card fourLayer layerBound erdosSzekeres P hP hgeneral)

end Lax56Proofs.ValtrReduction
