import Lax56Proofs.ValtrCoverSetup
import Lax56Proofs.ValtrCyclicRuns

namespace Lax56Proofs.ValtrRunReduction

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectorSetup
open Lax56Proofs.ValtrCoverSetup Lax56Proofs.ValtrRuns Lax56Proofs.ValtrCyclicRuns
open scoped Classical Fin.NatCast

/-- The finite outer-layer part of a defined sector; missing sectors
contribute the empty set. -/
noncomputable def sectorPoints (S : Finset Point) {n : ℕ} [NeZero n]
    (v c : Fin n → Point) (d : Point) (i : Fin n) : Finset Point :=
  if MeetsThirdLayer S v d i then
    (extremeLayer S).filter (fun q ↦ q ∈ sector ![v (i + 1), c i, v i])
  else ∅

theorem mem_sectorPoints_iff {S : Finset Point} {n : ℕ} [NeZero n]
    {v c : Fin n → Point} {d q : Point} {i : Fin n} :
    q ∈ sectorPoints S v c d i ↔
      MeetsThirdLayer S v d i ∧ q ∈ extremeLayer S ∧
        q ∈ sector ![v (i + 1), c i, v i] := by
  by_cases h : MeetsThirdLayer S v d i <;> simp [sectorPoints, h]

/-- The outer/inner strict cardinality inequality used by the cyclic
counting is a consequence of minimality, not an additional assumption. -/
theorem index_card_lt_outer {S : Finset Point} (hmin : MinimalOuter S)
    {n : ℕ} [NeZero n] {v : Fin n → Point}
    (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point)) :
    n < (extremeLayer S).card := by
  have hset : Finset.univ.image v = extremeLayer (inner S) := by
    apply Finset.coe_injective
    simpa using hrange
  have hcard : (extremeLayer (inner S)).card = n := by
    rw [← hset, Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin]
  have hv : v 0 ∈ extremeLayer (inner S) := by
    change v 0 ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self 0
  have hS : S.Nonempty := ⟨v 0, inner_subset S (extremeLayer_subset _ hv)⟩
  have hlt := layer_card_lt_outer hmin hS (show 0 < (1 : ℕ) by decide)
  change (extremeLayer (inner S)).card < (extremeLayer S).card at hlt
  rwa [hcard] at hlt

/-- The actual sector configuration satisfies Valtr's all-sectors
conclusion once the geometric run bound is supplied. Coverage, strict
layer-size comparison, and exhaustion of the third layer are all proved
from the displayed geometric hypotheses. -/
theorem all_sectors_consequences {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    (hmin : MinimalOuter S) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (hrun : CyclicRunBounds (sectorPoints S v c d) (MeetsThirdLayer S v d)) :
    (∀ i, MeetsThirdLayer S v d i) ∧
      (extremeLayer S).card = n + 1 ∧
      Finset.univ.image c = extremeLayer (inner (inner S)) ∧
      ∀ i, (privateRegion (extremeLayer S) (sectorPoints S v c d) i).Nonempty := by
  have hcover : ∀ q ∈ extremeLayer S, ∃ i, q ∈ sectorPoints S v c d i := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := outer_vertex_mem_defined_sector hgen hno hn v hinj
      hrange htri hd c hdata hq
    exact ⟨i, mem_sectorPoints_iff.mpr ⟨hi, hq, hqi⟩⟩
  have hempty (i) (hi : ¬MeetsThirdLayer S v d i) : sectorPoints S v c d i = ∅ := by
    simp only [sectorPoints, if_neg hi]
  obtain ⟨hall, hcard, hprivate⟩ := all_defined_card_and_private
    (sectorPoints S v c d) (MeetsThirdLayer S v d) hn hcover hempty
    (index_card_lt_outer hmin hinj hrange) hrun
  exact ⟨hall, hcard, third_layer_eq_all_apices hmin htri hdata hall hcard, hprivate⟩

end Lax56Proofs.ValtrRunReduction
