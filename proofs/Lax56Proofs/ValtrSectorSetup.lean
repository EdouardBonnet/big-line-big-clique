import Lax56Proofs.ValtrSelection
import Lax56Proofs.ValtrSectorBounds

namespace Lax56Proofs.ValtrSectorSetup

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors Lax56Proofs.ValtrCyclic
open Lax56Proofs.ValtrSelection Lax56Proofs.ValtrSectorBounds
open scoped Classical

/-- A radial triangle of the second layer is defined when it meets the
third layer. Indices here follow the positively oriented cycle; reversing
the two base vertices gives Valtr's clockwise sector convention. -/
def MeetsThirdLayer (S : Finset Point) {n : ℕ} [NeZero n]
    (v : Fin n → Point) (d : Point) (i : Fin n) : Prop :=
  ∃ q ∈ extremeLayer (inner (inner S)), q ∈ triangleHull d (v i) (v (i + 1))

/-- The geometric data of a chosen apex. Every field is proved by
`exists_radial_apices`; neither the run bound nor four-layer conclusion
is a field of this structure. -/
structure ApexData (S : Finset Point) {n : ℕ} [NeZero n]
    (v : Fin n → Point) (d : Point) (i : Fin n) (c : Point) : Prop where
  mem_third : c ∈ extremeLayer (inner (inner S))
  strict_triangle : StrictlyInsideTriangle d (v i) (v (i + 1)) c
  oriented : 0 < turn (v (i + 1)) c (v i)
  empty_triangle : ∀ p ∈ inner S, p ∈ triangleHull (v (i + 1)) c (v i) →
    p = v (i + 1) ∨ p = c ∨ p = v i
  radial_subset : sector ![v (i + 1), d, v i] ⊆ sector ![v (i + 1), c, v i]
  outer_card : ((extremeLayer S).filter (fun p ↦
    p ∈ sector ![v (i + 1), c, v i])).card ≤ 2

/-- Simultaneous construction of Valtr's apices and single-sector bounds
directly from the finite layers. Undefined indices receive an unused
default value, and every geometric assertion is guarded by `MeetsThirdLayer`. -/
theorem exists_radial_apices {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (v : Fin n → Point)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) :
    ∃ c : Fin n → Point, ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i) := by
  have hgenQ : ¬HasThreeCollinear (inner S) :=
    fun h ↦ hgen (hasThreeCollinear_mono (inner_subset S) h)
  have hv (i) : v i ∈ extremeLayer (inner S) := by
    change v i ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hvQ (i) : v i ∈ inner S := extremeLayer_subset _ (hv i)
  have hbase (i) : ∀ p ∈ inner S, turn (v (i + 1)) (v i) p ≤ 0 := by
    intro p hp
    rw [turn_swap_first]
    apply neg_nonpos.mpr
    apply cyclic_edge_nonneg_of_mem_hull htri _ i
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hp
  have hchoose (i) : ∃ c, MeetsThirdLayer S v d i → ApexData S v d i c := by
    by_cases hmeet : MeetsThirdLayer S v d i
    · have hinext : i + 1 ≠ i := by
        intro h
        have hnxt := cyclic_next_cases i
        have hv := congrArg Fin.val h
        omega
      obtain ⟨c, hc, hcTri, hcorient, hcempty⟩ := exists_empty_layer_triangle hgenQ
        (hv (i + 1)) (hv i) (hinj.ne hinext) hd (hbase i) hmeet
      refine ⟨c, fun _ ↦ ?_⟩
      have hcQ : c ∈ inner S :=
        inner_subset (inner S) (extremeLayer_subset (inner (inner S)) hc)
      refine ⟨hc, hcTri, hcorient, hcempty, ?_, ?_⟩
      · apply sector_triangle_mono
        · rw [triangleHull_swap_last]
          exact strictlyInsideTriangle_mem_triangleHull hcTri
        · exact (strictlyInsideTriangle_ne_vertices hcTri).2.2
        · exact (strictlyInsideTriangle_ne_vertices hcTri).2.1
      · exact outer_sector_card_le_two hgen hno (hvQ (i + 1)) hcQ (hvQ i)
          hcorient (hbase i) hcempty
    · exact ⟨d, fun h ↦ (hmeet h).elim⟩
  choose c hc using hchoose
  exact ⟨c, hc⟩

/-- The complete initial sector configuration is constructed from a
nonempty fourth layer. There are at least three second-layer vertices;
all defined sectors carry their proved geometric and counting data. -/
theorem exists_sector_setup_of_fourth_layer {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    (hfourth : (layer S 3).Nonempty) :
    ∃ m : ℕ, ∃ v : Fin (m + 3) → Point,
      Function.Injective v ∧
      Set.range v = (extremeLayer (inner S) : Set Point) ∧
      (∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) ∧
      ∃ d ∈ layer S 3, ∃ c : Fin (m + 3) → Point,
        ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i) := by
  obtain ⟨d, hd⟩ := hfourth
  have hdrem : d ∈ inner (inner (inner S)) := extremeLayer_subset _ hd
  have hgenQ : ¬HasThreeCollinear (inner S) :=
    fun h ↦ hgen (hasThreeCollinear_mono (inner_subset S) h)
  have hcard : 3 ≤ (extremeLayer (inner S)).card :=
    three_le_outer_card_of_inner_nonempty hgenQ
      ⟨d, inner_subset (inner (inner S)) hdrem⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hcard
  have hsize : (extremeLayer (inner S)).card = m + 3 := by omega
  have hBgen : ¬HasThreeCollinear (extremeLayer (inner S)) :=
    fun h ↦ hgenQ (hasThreeCollinear_mono (extremeLayer_subset (inner S)) h)
  have horder := Lax56Proofs.CyclicOrder.exists_cyclic_order_card
    (extremeLayer (inner S)) (Finset.card_pos.mp (by omega))
    (extremeLayer_convexPosition (inner S)) hBgen
  rw [hsize] at horder
  obtain ⟨v, hinj, hrange, htri⟩ := horder
  obtain ⟨c, hc⟩ := exists_radial_apices hgen hno (by omega) v hinj hrange htri hdrem
  exact ⟨m, v, hinj, hrange, htri, d, hd, c, hc⟩

end Lax56Proofs.ValtrSectorSetup
