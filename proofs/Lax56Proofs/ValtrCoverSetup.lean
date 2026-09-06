import Lax56Proofs.ValtrCoverage

namespace Lax56Proofs.ValtrCoverSetup

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrSelection
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrMissing Lax56Proofs.ValtrCoverage
open scoped Classical

/-- The interiors of distinct fan triangles are disjoint; this version
needs only the oriented cycle and the two strict triangle memberships. -/
theorem radial_triangle_index_eq {n : ℕ} [NeZero n] {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d q : Point} {i j : Fin n}
    (hi : StrictlyInsideTriangle d (v i) (v (i + 1)) q)
    (hj : StrictlyInsideTriangle d (v j) (v (j + 1)) q) : i = j := by
  apply cyclic_line_crossing_unique htri (u := q) (w := d)
  · rw [← turn_rotate]; exact hi.1
  · have h : turn d (v (i + 1)) q < 0 := by rw [turn_swap_first]; exact neg_neg_of_pos hi.2.2
    rw [← turn_rotate]; exact h
  · rw [← turn_rotate]; exact hj.1
  · have h : turn d (v (j + 1)) q < 0 := by rw [turn_swap_first]; exact neg_neg_of_pos hj.2.2
    rw [← turn_rotate]; exact h

theorem defined_apex_index_eq {S : Finset Point} {n : ℕ} [NeZero n]
    {v c : Fin n → Point} {d : Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    {i j : Fin n} (hi : MeetsThirdLayer S v d i) (hj : MeetsThirdLayer S v d j)
    (heq : c i = c j) : i = j := by
  apply radial_triangle_index_eq htri (hdata i hi).strict_triangle
  rw [heq]
  exact (hdata j hj).strict_triangle

/-- In the `|A| = |B| + 1` case, if all apices exist, they are exactly the
third-layer vertices. This is Valtr's cardinality argument before moving
the fourth-layer point, independent of the remaining radial-order step. -/
theorem third_layer_eq_all_apices {S : Finset Point} (hmin : MinimalOuter S)
    {n : ℕ} [NeZero n] {v c : Fin n → Point} {d : Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (hall : ∀ i, MeetsThirdLayer S v d i)
    (hcard : (extremeLayer S).card = n + 1) :
    Finset.univ.image c = extremeLayer (inner (inner S)) := by
  have hcinj : Function.Injective c := fun i j hij ↦
    defined_apex_index_eq htri hdata (hall i) (hall j) hij
  have hmem (i) : c i ∈ extremeLayer (inner (inner S)) := (hdata i (hall i)).mem_third
  have hsub : Finset.univ.image c ⊆ extremeLayer (inner (inner S)) := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hmem i
  have hS : S.Nonempty := ⟨c 0, inner_subset S (inner_subset (inner S)
    (extremeLayer_subset _ (hmem 0)))⟩
  have hlt := layer_card_lt_outer hmin hS (show 0 < (2 : ℕ) by decide)
  change (extremeLayer (inner (inner S))).card < (extremeLayer S).card at hlt
  have himagecard : (Finset.univ.image c).card = n := by
    rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_fin]
  apply Finset.eq_of_subset_of_card_le hsub
  rw [himagecard]
  omega

/-- The defined sectors cover the whole outer layer. Missing radial
triangles are handled by the proved neighboring-sector coverage lemma,
not by adding an assumed covering property to the apex data. -/
theorem outer_vertex_mem_defined_sector {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (v : Fin n → Point)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    {q : Point} (hq : q ∈ extremeLayer S) :
    ∃ i, MeetsThirdLayer S v d i ∧ q ∈ sector ![v (i + 1), c i, v i] := by
  let Q := inner S
  have hgenQ : ¬HasThreeCollinear Q :=
    fun h ↦ hgen (hasThreeCollinear_mono (inner_subset S) h)
  have hgenI : ¬HasThreeCollinear (inner Q) :=
    fun h ↦ hgenQ (hasThreeCollinear_mono (inner_subset Q) h)
  let C := extremeLayer (inner Q)
  have hcard : 3 ≤ C.card := three_le_outer_card_of_inner_nonempty hgenI ⟨d, hd⟩
  letI : NeZero C.card := ⟨by omega⟩
  have hgenC : ¬HasThreeCollinear C :=
    fun h ↦ hgenI (hasThreeCollinear_mono (extremeLayer_subset (inner Q)) h)
  obtain ⟨u, huinj, hurange, hutri⟩ := Lax56Proofs.CyclicOrder.exists_cyclic_order_card C
    (Finset.card_pos.mp (by omega)) (extremeLayer_convexPosition (inner Q)) hgenC
  have huC (j) : u j ∈ C := by
    change u j ∈ (C : Set Point)
    rw [← hurange]
    exact Set.mem_range_self j
  have hvB (j) : v j ∈ extremeLayer Q := by
    change v j ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self j
  have hvQ (j) : v j ∈ Q := extremeLayer_subset Q (hvB j)
  have hvS (j) : v j ∈ S := inner_subset S (hvQ j)
  have hdI : d ∈ inner Q := inner_subset _ hd
  have hdQ : d ∈ Q := inner_subset _ hdI
  have hdHull : d ∈ convexHull ℝ (Set.range v) := by
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hdQ
  have hdnot : d ∉ Set.range v := by
    rw [hrange]
    exact (Finset.mem_sdiff.mp hdI).2
  have hqOut : q ∉ convexHull ℝ (Q : Set Point) := extreme_not_mem_convexHull_inner hq
  have hqOut' : q ∉ convexHull ℝ (Set.range v) := by
    rw [hrange, convexHull_extremeLayer]
    exact hqOut
  obtain ⟨i, hiRaw⟩ := exists_radial_sector_of_not_mem_hull hgen (by omega) v hinj htri
    hvS (inner_subset S hdQ) (extremeLayer_subset S hq) hdHull hdnot hqOut'
  by_cases hmeet : MeetsThirdLayer S v d i
  · exact ⟨i, hmeet, (hdata i hmeet).radial_subset hiRaw⟩
  have hprev : MeetsThirdLayer S v d (i - 1) := by
    apply (meetsThirdLayer_or_next hgen hno hn v hinj hrange htri hd (i - 1)).resolve_right
    simpa only [sub_add_cancel] using hmeet
  have hnext : MeetsThirdLayer S v d (i + 1) :=
    (meetsThirdLayer_or_next hgen hno hn v hinj hrange htri hd i).resolve_left hmeet
  have hprevData := hdata (i - 1) hprev
  have hnextData := hdata (i + 1) hnext
  have hsupp (j) : ∀ z ∈ inner Q, 0 < turn (v j) (v (j + 1)) z := by
    intro z hz
    apply cyclic_edge_strict_of_mem_hull hgenQ (by omega) v hinj htri hvQ
      (inner_subset Q hz) _ _ j
    · rw [hrange, convexHull_extremeLayer]
      exact subset_convexHull ℝ _ (inner_subset Q hz)
    · rw [hrange]
      exact (Finset.mem_sdiff.mp hz).2
  have hnoB {z : Point} (hz : z ∈ C) (j : Fin n) : z ≠ v j := by
    have hzI : z ∈ inner Q := extremeLayer_subset _ hz
    intro h
    exact (Finset.mem_sdiff.mp hzI).2 (h.symm ▸ hvB j)
  have hEmpty (j : Fin n) (hj : MeetsThirdLayer S v d j) :
      ∀ z ∈ C, z ∈ triangleHull (v j) (c j) (v (j + 1)) → z = c j := by
    intro z hz hzTri
    have hzQ : z ∈ Q := inner_subset Q (extremeLayer_subset _ hz)
    have hzTri' : z ∈ triangleHull (v (j + 1)) (c j) (v j) := by
      convert hzTri using 1
      unfold triangleHull
      congr 1
      ext x; simp [or_comm, or_left_comm, or_assoc]
    rcases (hdata j hj).empty_triangle z hzQ hzTri' with h | h | h
    · exact (hnoB hz (j + 1) h).elim
    · exact h
    · exact (hnoB hz j h).elim
  have hprevTri : StrictlyInsideTriangle d (v (i - 1)) (v i) (c (i - 1)) := by
    simpa only [sub_add_cancel] using hprevData.strict_triangle
  have hprevBase : ∀ z ∈ Lax56.ConvexLayers.inner Q, 0 ≤ turn (v (i - 1)) (v i) z := by
    intro z hz
    simpa only [sub_add_cancel] using (hsupp (i - 1) z hz).le
  have hprevEmpty : ∀ z ∈ C, z ∈ triangleHull (v (i - 1)) (c (i - 1)) (v i) → z = c (i - 1) := by
    simpa only [sub_add_cancel] using hEmpty (i - 1) hprev
  have hmissing (j) : u j ∉ triangleHull d (v i) (v (i + 1)) :=
    fun h ↦ hmeet ⟨u j, huC j, h⟩
  have hcover := missing_raw_sector_mem_neighbor hgen hno (inner_hullClosedIn S)
    (by omega) u huinj hurange hutri hd (hvB i) (hvB (i + 1))
    hprevData.mem_third hnextData.mem_third hprevTri hnextData.strict_triangle
    hprevBase (hsupp i) (fun z hz ↦ (hsupp (i + 1) z hz).le)
    hprevEmpty (hEmpty (i + 1) hnext) hmissing (extremeLayer_subset S hq) hqOut hiRaw
  rcases hcover with h | h
  · exact ⟨i - 1, hprev, by simpa only [sub_add_cancel] using h⟩
  · exact ⟨i + 1, hnext, h⟩

end Lax56Proofs.ValtrCoverSetup
