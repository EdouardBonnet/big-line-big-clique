import Lax56Proofs.ValtrFourLayerReduction
import Lax56Proofs.ValtrEndpointDrop

namespace Lax56Proofs.ValtrRunInduction

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrRunSetup
open Lax56Proofs.ValtrCyclicRuns Lax56Proofs.ValtrRunReduction
open Lax56Proofs.ValtrEndpointDrop
open scoped Classical Fin.NatCast

noncomputable def runUnion {n : ℕ} [NeZero n] (U : Fin n → Finset Point)
    (start : Fin n) (t : ℕ) : Finset Point :=
  (Finset.range t).biUnion (fun k ↦ U (cyclicIndex start k))

/-- The unresolved convex-endpoint counting input, in a form immediately
usable by the run induction. Clockwise first/last correspond to deleting
the last/first index, respectively, from the positively indexed run. -/
def EndpointDropBounds (S : Finset Point) {n : ℕ} [NeZero n]
    (v c : Fin n → Point) (d : Point) : Prop :=
  ∀ (start : Fin n) (t : ℕ), 2 ≤ t → t < n →
    (∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k)) →
    (¬StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
        (runBase v start t 2) (runChain v c start t 1) →
      (runUnion (sectorPoints S v c d) start t \
        runUnion (sectorPoints S v c d) start (t - 1)).card ≤ 1) ∧
    (¬StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
        (runBase v start t (t + 1)) (runChain v c start t t) →
      (runUnion (sectorPoints S v c d) start t \
        runUnion (sectorPoints S v c d) (start + 1) (t - 1)).card ≤ 1)

/-- The remaining both-convex endpoint case. The bounds on both shorter
runs are supplied by induction and are available to its geometric proof. -/
def DoublyConvexRunBound (S : Finset Point) {n : ℕ} [NeZero n]
    (v c : Fin n → Point) (d : Point) : Prop :=
  ∀ (start : Fin n) (t : ℕ), 2 ≤ t → t < n →
    (∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k)) →
    ¬StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1) →
    ¬StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t) →
    (runUnion (sectorPoints S v c d) start (t - 1)).card ≤ t →
    (runUnion (sectorPoints S v c d) (start + 1) (t - 1)).card ≤ t →
    (runUnion (sectorPoints S v c d) start t).card ≤ t + 1

/-- The entire sector-run induction. The nonconvex branch uses the
proved supporting-chain replacement; only the convex endpoint drop
estimate is an additional hypothesis. -/
theorem run_bound_of_endpoint_drop_bounds {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hmin : MinimalOuter S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (hendpoints : EndpointDropBounds S v c d) :
    CyclicRunBounds (sectorPoints S v c d) (MeetsThirdLayer S v d) := by
  let U := sectorPoints S v c d
  intro start t
  induction t using Nat.strong_induction_on generalizing start with
  | h t ih =>
    intro ht htn hdefined
    change (runUnion U start t).card ≤ t + 1
    have hsingle (k) (hk : k < t) : (U (cyclicIndex start k)).card ≤ 2 := by
      have hd' : MeetsThirdLayer S v d (cyclicIndex start k) := hdefined k hk
      simpa only [U, sectorPoints, if_pos hd'] using (hdata _ hd').outer_card
    by_cases ht1 : t = 1
    · subst t
      simpa [runUnion, cyclicIndex] using hsingle 0 (by decide)
    have ht2 : 2 ≤ t := by omega
    have hprefix : (runUnion U start (t - 1)).card ≤ t := by
      have hh := ih (t - 1) (by omega) start (by omega) (by omega)
        (fun k hk ↦ hdefined k (by omega))
      change (runUnion U start (t - 1)).card ≤ t - 1 + 1 at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hh
    have htail : (runUnion U (start + 1) (t - 1)).card ≤ t := by
      have hD : ∀ k < t - 1, MeetsThirdLayer S v d ((start + 1) + (↑k : Fin n)) := by
        intro k hk
        have hh := hdefined (k + 1) (by omega)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hh
      have hh := ih (t - 1) (by omega) (start + 1) (by omega) (by omega) hD
      change (runUnion U (start + 1) (t - 1)).card ≤ t - 1 + 1 at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hh
    have hupper : (runUnion U start t).card ≤ t + 2 := by
      have hsub : runUnion U start t ⊆
          runUnion U start (t - 1) ∪ U (cyclicIndex start (t - 1)) := by
        intro p hp
        obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
        have hkt := Finset.mem_range.mp hk
        by_cases hkp : k < t - 1
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkp, hp⟩)
        · have heq : k = t - 1 := by omega
          exact Finset.mem_union_right _ (heq ▸ hp)
      have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hs := hsingle (t - 1) (by omega)
      omega
    have hends := hendpoints start t ht2 htn hdefined
    by_cases hfirst : StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
        (runBase v start t 2) (runChain v c start t 1)
    · by_cases hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
          (runBase v start t (t + 1)) (runChain v c start t t)
      · exact (not_minimal_of_nonconvex_run_card_le hgen v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast hupper hmin).elim
      · have hdrop := hends.2 hlast
        have hh := Finset.card_le_card_sdiff_add_card (s := runUnion U start t)
          (t := runUnion U (start + 1) (t - 1))
        change (runUnion U start t \ runUnion U (start + 1) (t - 1)).card ≤ 1 at hdrop
        omega
    · have hdrop := hends.1 hfirst
      have hh := Finset.card_le_card_sdiff_add_card (s := runUnion U start t)
        (t := runUnion U start (t - 1))
      change (runUnion U start t \ runUnion U start (t - 1)).card ≤ 1 at hdrop
      omega

/-- All nonconvex and mixed endpoint cases are now proved. Only a
run with both endpoint quadrilaterals convex remains as a hypothesis. -/
theorem run_bound_of_doubly_convex_run_bound {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S) (hmin : MinimalOuter S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (hdoubly : DoublyConvexRunBound S v c d) :
    CyclicRunBounds (sectorPoints S v c d) (MeetsThirdLayer S v d) := by
  let U := sectorPoints S v c d
  intro start t
  induction t using Nat.strong_induction_on generalizing start with
  | h t ih =>
    intro ht htn hdefined
    change (runUnion U start t).card ≤ t + 1
    have hsingle (k) (hk : k < t) : (U (cyclicIndex start k)).card ≤ 2 := by
      have hd' : MeetsThirdLayer S v d (cyclicIndex start k) := hdefined k hk
      simpa only [U, sectorPoints, if_pos hd'] using (hdata _ hd').outer_card
    by_cases ht1 : t = 1
    · subst t
      simpa [runUnion, cyclicIndex] using hsingle 0 (by decide)
    have ht2 : 2 ≤ t := by omega
    have hprefix : (runUnion U start (t - 1)).card ≤ t := by
      have hh := ih (t - 1) (by omega) start (by omega) (by omega)
        (fun k hk ↦ hdefined k (by omega))
      change (runUnion U start (t - 1)).card ≤ t - 1 + 1 at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hh
    have htail : (runUnion U (start + 1) (t - 1)).card ≤ t := by
      have hD : ∀ k < t - 1, MeetsThirdLayer S v d ((start + 1) + (↑k : Fin n)) := by
        intro k hk
        have hh := hdefined (k + 1) (by omega)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hh
      have hh := ih (t - 1) (by omega) (start + 1) (by omega) (by omega) hD
      change (runUnion U (start + 1) (t - 1)).card ≤ t - 1 + 1 at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hh
    have hupper : (runUnion U start t).card ≤ t + 2 := by
      have hsub : runUnion U start t ⊆
          runUnion U start (t - 1) ∪ U (cyclicIndex start (t - 1)) := by
        intro p hp
        obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
        have hkt := Finset.mem_range.mp hk
        by_cases hkp : k < t - 1
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkp, hp⟩)
        · have heq : k = t - 1 := by omega
          exact Finset.mem_union_right _ (heq ▸ hp)
      have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hs := hsingle (t - 1) (by omega)
      omega
    by_cases hfirst : StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
        (runBase v start t 2) (runChain v c start t 1)
    · by_cases hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
          (runBase v start t (t + 1)) (runChain v c start t t)
      · exact (not_minimal_of_nonconvex_run_card_le hgen v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast hupper hmin).elim
      · have hdrop := last_drop_card_of_mixed_endpoints hgen hno v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast
        have hh := Finset.card_le_card_sdiff_add_card (s := runUnion U start t)
          (t := runUnion U (start + 1) (t - 1))
        change (runUnion U start t \ runUnion U (start + 1) (t - 1)).card ≤ 1 at hdrop
        omega
    · by_cases hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
          (runBase v start t (t + 1)) (runChain v c start t t)
      · have hdrop := first_drop_card_of_mixed_endpoints hgen hno v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast
        have hh := Finset.card_le_card_sdiff_add_card (s := runUnion U start t)
          (t := runUnion U start (t - 1))
        change (runUnion U start t \ runUnion U start (t - 1)).card ≤ 1 at hdrop
        omega
      · exact hdoubly start t ht2 htn hdefined hfirst hlast hprefix htail


/-- A direct reduction of the four-layer theorem to the two symmetric
convex-endpoint drop estimates. No other geometric step is left as an
assumption of this theorem. -/
theorem four_layer_of_endpoint_drop_bounds {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hmin : MinimalOuter S)
    (hlarge : 16 ≤ (extremeLayer S).card) (hfourth : (layer S 3).Nonempty)
    (hendpoints : ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ v : Fin n → Point,
      Function.Injective v → Set.range v = (extremeLayer (inner S) : Set Point) →
      (∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) →
      ∀ d ∈ layer S 3, ∀ c : Fin n → Point,
        (∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i)) → EndpointDropBounds S v c d) :
    HasEmptyHexagon S := by
  apply Lax56Proofs.ValtrFourLayerReduction.four_layer_of_run_bound hgen hmin hlarge hfourth
  intro n inst hn v hinj hrange htri d hd c hdata
  exact run_bound_of_endpoint_drop_bounds hgen hmin v hinj hrange htri
    (extremeLayer_subset _ hd) c hdata (hendpoints hn v hinj hrange htri d hd c hdata)

/-- The four-layer theorem is reduced to the both-convex run case.
The no-hexagon assumption and both shorter-run bounds are available to
that remaining proof; the mixed cases need no additional hypothesis. -/
theorem four_layer_of_doubly_convex_run_bound {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hmin : MinimalOuter S)
    (hlarge : 16 ≤ (extremeLayer S).card) (hfourth : (layer S 3).Nonempty)
    (hdoubly : ¬HasEmptyHexagon S → ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ v : Fin n → Point,
      Function.Injective v → Set.range v = (extremeLayer (inner S) : Set Point) →
      (∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) →
      ∀ d ∈ layer S 3, ∀ c : Fin n → Point,
        (∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i)) → DoublyConvexRunBound S v c d) :
    HasEmptyHexagon S := by
  by_contra hno
  apply hno
  apply Lax56Proofs.ValtrFourLayerReduction.four_layer_of_run_bound hgen hmin hlarge hfourth
  intro n inst hn v hinj hrange htri d hd c hdata
  exact run_bound_of_doubly_convex_run_bound hgen hno hmin v hinj hrange htri
    (extremeLayer_subset _ hd) c hdata (hdoubly hno hn v hinj hrange htri d hd c hdata)

end Lax56Proofs.ValtrRunInduction
