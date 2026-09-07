import Lax56.ValtrFourLayer
import Lax56Proofs.ValtrEndpointCompletion
import Lax56Proofs.ValtrExtremalRun

namespace Lax56Proofs.ValtrFourLayer

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrRunSupport Lax56Proofs.ValtrRunSetup
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrRunReduction
open Lax56Proofs.ValtrEndpointGeometry Lax56Proofs.ValtrEndpointCompletion
open Lax56Proofs.ValtrExtremalRun
open scoped Classical Fin.NatCast

theorem extremal_run_obstruction {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i)) :
    ExtremalRunObstruction S v c d := by
  intro start t ht htn hdefined hfirst hlast U hdisj hzero hlastCard hmiddle
  let b := runBase v start t
  let h := runChain v c start t
  have cfg : RunGeometry S t b h d :=
    runGeometry_of_apex_data hgen v hinj hrange htri hd c hdata start ht htn hdefined
  have hUeq (i) (hi : 1 ≤ i) (hit : i ≤ t) : runPoints S b h i = U (t - i) := by
    change (extremeLayer S).filter (fun x ↦ x ∈ sector
      ![runBase v start t i, runChain v c start t i, runBase v start t (i + 1)]) =
      sectorPoints S v c d (cyclicIndex start (t - i))
    rw [runBase_current v start hi hit, runBase_next, runChain_apex v c start hi hit]
    simp only [sectorPoints, if_pos (hdefined (t - i) (by omega))]
  apply extremal_run_impossible hgen hno cfg
    (first_quad_of_not_interior hgen v hinj hrange htri hd c hdata start ht htn hdefined hfirst)
    (last_quad_of_not_interior hgen v hinj hrange htri hd c hdata start ht htn hdefined hlast)
  · intro i j hi hit hj hjt hij
    rw [hUeq i hi hit, hUeq j hj hjt]
    exact hdisj (t - i) (t - j) (by omega) (by omega) (by omega)
  · rw [hUeq 1 (by decide) (by omega)]
    exact hlastCard
  · rw [hUeq t (by omega) le_rfl, Nat.sub_self]
    exact hzero
  · rw [hUeq 2 (by decide) ht]
    apply Finset.card_pos.mp
    by_cases ht2 : t = 2
    · subst t; simpa using (show 0 < (U 0).card by omega)
    · have hh := hmiddle (t - 2) (by omega) (by omega)
      omega

/--
---
conclusion: Lax56.ValtrFourLayer.exists_emptyHexagon_of_four_layers
---
Valtr's four-layer implication with the deliberately unoptimized
outer threshold sixteen. The convex endpoint case is proved by edge caps
and backward projective propagation, not assumed. -/
theorem exists_emptyHexagon_of_four_layers
    (S : Finset Point) (hgeneral : ¬HasThreeCollinear S)
    (hminimal : MinimalOuter S) (hlarge : 16 ≤ (extremeLayer S).card)
    (hfourth : (layer S 3).Nonempty) : HasEmptyHexagon S := by
  apply four_layer_of_extremal_run_obstruction hgeneral hminimal hlarge hfourth
  intro hno n inst hn v hinj hrange htri d hd c hdata
  exact extremal_run_obstruction hgeneral hno v hinj hrange htri
    (extremeLayer_subset _ hd) c hdata

end Lax56Proofs.ValtrFourLayer
