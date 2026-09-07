import Lax56Proofs.ValtrPrivateRuns

namespace Lax56Proofs.ValtrFourLayerReduction

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrCoverSetup
open Lax56Proofs.ValtrCyclicRuns Lax56Proofs.ValtrRunReduction Lax56Proofs.ValtrPrivateRuns

/-- The remaining input is precisely Valtr's sector-run bound, for
the actual selected-apex configurations. This is a proposition supplied
as an ordinary hypothesis below, not an axiom. -/
def SectorRunBound (S : Finset Point) : Prop :=
  ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ v : Fin n → Point,
    Function.Injective v → Set.range v = (extremeLayer (inner S) : Set Point) →
    (∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) →
    ∀ d ∈ layer S 3, ∀ c : Fin n → Point,
      (∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i)) →
      CyclicRunBounds (sectorPoints S v c d) (MeetsThirdLayer S v d)

/-- Every step after the sector-run lemma is formalized. The deliberately
weaker outer-layer threshold 16 permits three disjoint five-sector blocks
and avoids locating the extra outer point among the cyclic sector indices.
The intended 216-point application is unchanged. -/
theorem four_layer_of_run_bound {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hmin : MinimalOuter S)
    (hlarge : 16 ≤ (extremeLayer S).card) (hfourth : (layer S 3).Nonempty)
    (hrun : SectorRunBound S) : HasEmptyHexagon S := by
  classical
  by_contra hno
  obtain ⟨m, v, hinj, hrange, htri, d, hd, c, hdata⟩ :=
    exists_sector_setup_of_fourth_layer hgen hno hfourth
  have hddeep : d ∈ inner (inner (inner S)) := extremeLayer_subset _ hd
  obtain ⟨hall, hcard, hfull, hprivate⟩ := all_sectors_consequences hgen hno hmin
    (by omega : 3 ≤ m + 3) v hinj hrange htri hddeep c hdata
    (hrun (by omega) v hinj hrange htri d hd c hdata)
  have hallD : ∀ e ∈ layer S 3, ∀ i, MeetsThirdLayer S v e i := by
    intro e he
    have hedeep : e ∈ inner (inner (inner S)) := extremeLayer_subset _ he
    obtain ⟨f, hf⟩ := exists_radial_apices hgen hno (by omega : 2 ≤ m + 3)
      v hinj hrange htri hedeep
    exact (all_sectors_consequences hgen hno hmin (by omega : 3 ≤ m + 3)
      v hinj hrange htri hedeep f hf (hrun (by omega) v hinj hrange htri e he f hf)).1
  have hcover : ∀ q ∈ extremeLayer S, ∃ i, q ∈ sectorPoints S v c d i := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := outer_vertex_mem_defined_sector hgen hno (by omega : 3 ≤ m + 3)
      v hinj hrange htri hddeep c hdata hq
    exact ⟨i, mem_sectorPoints_iff.mpr ⟨hi, hq, hqi⟩⟩
  exact not_minimal_of_all_sectors hgen hno (by omega : 15 ≤ m + 3)
    v hinj hrange htri hddeep c (fun i ↦ hdata i (hall i)) hfull hallD hcover hcard hprivate hmin

end Lax56Proofs.ValtrFourLayerReduction
