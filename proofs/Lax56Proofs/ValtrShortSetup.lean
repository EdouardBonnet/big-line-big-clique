import Lax56Proofs.ValtrShortSplice

namespace Lax56Proofs.ValtrShortSetup

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrRadialOrder
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrCoverSetup
open Lax56Proofs.ValtrRunSetup Lax56Proofs.ValtrRunReduction Lax56Proofs.ValtrShortSplice
open scoped Classical Fin.NatCast

def fiveBase {n : ℕ} [NeZero n] (v : Fin n → Point) (start : Fin n) (k : ℕ) : Point :=
  v (cyclicIndex start (5 - k))

def fiveApices {n : ℕ} [NeZero n] (c : Fin n → Point) (start : Fin n) (k : ℕ) : Point :=
  c (cyclicIndex start (4 - k))

theorem fiveBase_current {n : ℕ} [NeZero n] (v : Fin n → Point) (start : Fin n)
    {k : ℕ} (hk : k ≤ 4) : fiveBase v start k = v (cyclicIndex start (4 - k) + 1) := by
  rw [← cyclicIndex_succ]
  unfold fiveBase
  congr 2
  omega

theorem fiveBase_next {n : ℕ} [NeZero n] (v : Fin n → Point) (start : Fin n)
    (k : ℕ) : fiveBase v start (k + 1) = v (cyclicIndex start (4 - k)) := by
  unfold fiveBase
  congr 2
  omega

/-- All data of the five-sector configuration follow from the actual
cyclic second layer, its selected apices, and the chosen center in the
five-apex cap. Reversal only changes the indexing direction. -/
theorem fiveSectorConfig_of_apex_data {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 5 < n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, ApexData S v d i (c i)) (start : Fin n)
    (hcap : d ∈ convexHull ℝ (Set.range (fun i : Fin 5 ↦ c (cyclicIndex start i)))) :
    FiveSectorConfig S (fiveBase v start) (fiveApices c start) d := by
  have hvB (i) : v i ∈ extremeLayer (inner S) := by
    change v i ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hcinj : Function.Injective c := by
    intro i j heq
    apply radial_triangle_index_eq htri (hdata i).strict_triangle
    rw [heq]
    exact (hdata j).strict_triangle
  have hcTri := apex_cyclic_triples hgen htri hd hdata
  have hctri (a b e : ℕ) (hab : a < b) (hbe : b < e) (he : e ≤ 4) :
      0 < turn (c (cyclicIndex start a)) (c (cyclicIndex start b)) (c (cyclicIndex start e)) := by
    simpa only [cyclicIndex, Fin.natCast_eq_mk (by omega : a < n),
      Fin.natCast_eq_mk (by omega : b < n), Fin.natCast_eq_mk (by omega : e < n), add_comm] using
      cyclic_shift_triples hcTri start (⟨a, by omega⟩ : Fin n) ⟨b, by omega⟩ ⟨e, by omega⟩ hab hbe
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hd, ?_, ?_⟩
  · intro i hi
    exact hvB _
  · intro i hi
    exact (hdata _).mem_third
  · intro i j hi hj heq
    have hh := cyclicIndex_injective_below start (by omega : 5 - i < n)
      (by omega : 5 - j < n) (hinj heq)
    omega
  · intro i j hi hj heq
    have hh := cyclicIndex_injective_below start (by omega : 4 - i < n)
      (by omega : 4 - j < n) (hcinj heq)
    omega
  · intro i hi p hp
    rw [fiveBase_current v start hi, fiveBase_next, turn_swap_first]
    apply neg_nonpos.mpr
    apply cyclic_edge_nonneg_of_mem_hull htri _ (cyclicIndex start (4 - i))
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hp
  · intro i j k hij hjk hk
    convert neg_neg_of_pos (hctri (4 - k) (4 - j) (4 - i) (by omega) (by omega) (by omega))
      using 1 <;> unfold fiveApices turn <;> ring
  · intro i hi
    rw [fiveBase_current v start hi, fiveBase_next]
    exact (hdata _).strict_triangle
  · have heq : Set.range (fun i : Fin 5 ↦ fiveApices c start i) =
        Set.range (fun i : Fin 5 ↦ c (cyclicIndex start i)) := by
      ext p
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨i.rev, ?_⟩
        simp only [fiveApices, Fin.val_rev]
        congr 2
        omega
      · rintro ⟨i, rfl⟩
        refine ⟨i.rev, ?_⟩
        simp only [fiveApices, Fin.val_rev]
        congr 2
        omega
    rwa [heq]
  · intro i hi p hp hptri
    rw [fiveBase_current v start hi, fiveBase_next] at hptri ⊢
    exact (hdata _).empty_triangle p hp hptri

/-- The final shortened splice applied to the actual finite sector
union. Its sole counting input is that the five sectors contain at most
five outer vertices. -/
theorem not_minimal_of_five_sector_cap {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 5 < n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, ApexData S v d i (c i)) (start : Fin n)
    (hcap : d ∈ convexHull ℝ (Set.range (fun i : Fin 5 ↦ c (cyclicIndex start i))))
    (hcard : ((Finset.range 5).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))).card ≤ 5) :
    ¬MinimalOuter S := by
  have cfg := fiveSectorConfig_of_apex_data hgen hn v hinj hrange htri hd c hdata start hcap
  have hdefined (i) : MeetsThirdLayer S v d i :=
    ⟨c i, (hdata i).mem_third, strictlyInsideTriangle_mem_triangleHull (hdata i).strict_triangle⟩
  let U := (Finset.range 5).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))
  let R := extremeLayer S \ U
  have hR : R ⊆ extremeLayer S := Finset.sdiff_subset
  have hout : ∀ x ∈ R, ∀ k, k ≤ 4 →
      x ∉ sector ![fiveBase v start k, fiveApices c start k, fiveBase v start (k + 1)] := by
    intro x hx k hk hs
    obtain ⟨hxA, hxU⟩ := Finset.mem_sdiff.mp hx
    apply hxU
    apply Finset.mem_biUnion.mpr
    refine ⟨4 - k, Finset.mem_range.mpr (by omega), mem_sectorPoints_iff.mpr ?_⟩
    refine ⟨hdefined _, hxA, ?_⟩
    simpa only [fiveBase_current v start hk, fiveBase_next, fiveApices] using hs
  have hremoved : (extremeLayer S \ R).card ≤ 5 := by
    have hsub : extremeLayer S \ R ⊆ U := by
      intro x hx
      by_contra hxU
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, hxU⟩)
    exact (Finset.card_le_card hsub).trans hcard
  exact cfg.not_minimal_of_removed_card_le hgen hR hout hremoved

theorem offsetIndex_eq_cyclicIndex {n : ℕ} [NeZero n] (a : ℕ) (ha : a + 5 ≤ n)
    (i : Fin 5) : Lax56Proofs.ValtrPolygon.offsetIndex a ha i =
      cyclicIndex (⟨a, by omega⟩ : Fin n) i := by
  apply Fin.ext
  simp only [Lax56Proofs.ValtrPolygon.offsetIndex, cyclicIndex, Fin.val_add, Fin.val_natCast]
  rw [Nat.mod_eq_of_lt (by omega : i.val < n), Nat.mod_eq_of_lt (by omega : a + i.val < n)]

/-- The complete center-changing and shortened-splice step. The
fourth-layer point in the five-apex cap preserves the chosen apices;
therefore it also preserves the five-sector count used by the splice. -/
theorem not_minimal_of_five_run_card_le {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (hn : 5 < n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, ApexData S v d i (c i))
    (hfull : Finset.univ.image c = extremeLayer (inner (inner S)))
    (hall : ∀ e ∈ layer S 3, ∀ i, MeetsThirdLayer S v e i)
    (a : ℕ) (ha : a + 5 ≤ n)
    (hcard : ((Finset.range 5).biUnion (fun k ↦
      sectorPoints S v c d (cyclicIndex (⟨a, by omega⟩ : Fin n) k))).card ≤ 5) :
    ¬MinimalOuter S := by
  obtain ⟨e, he, heCap, hnew⟩ := Lax56Proofs.ValtrMatching.exists_cap_point_preserving_apices
    hgen hno v hinj hrange htri hd c hdata hfull hall a ha
  have hdef (i) : MeetsThirdLayer S v d i :=
    ⟨c i, (hdata i).mem_third, strictlyInsideTriangle_mem_triangleHull (hdata i).strict_triangle⟩
  have hsets : sectorPoints S v c e = sectorPoints S v c d := by
    funext i
    simp only [sectorPoints, if_pos (hall e he i), if_pos (hdef i)]
  apply not_minimal_of_five_sector_cap hgen hn v hinj hrange htri
    (extremeLayer_subset _ he) c hnew (⟨a, by omega⟩ : Fin n)
  · simpa only [offsetIndex_eq_cyclicIndex] using heCap
  · rw [hsets]
    exact hcard

end Lax56Proofs.ValtrShortSetup
