import Lax56Proofs.ValtrRunSetup

namespace Lax56Proofs.ValtrMatching

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrRadialOrder
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrCoverSetup Lax56Proofs.ValtrSelection
open scoped Classical

/-- Two positive cyclic enumerations of the same finite polygon that
agree at their first vertex agree everywhere. The induced permutation
is strictly increasing and hence is the identity on `Fin n`. -/
theorem cyclic_enumerations_eq_of_zero {n : ℕ} [NeZero n] {v w : Fin n → Point}
    (hvinj : Function.Injective v) (hwinj : Function.Injective w)
    (hvtri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hwtri : ∀ i j k, i < j → j < k → 0 < turn (w i) (w j) (w k))
    (hrange : Set.range v = Set.range w) (hzero : v 0 = w 0) : v = w := by
  have hex (i) : ∃ j, v j = w i := by
    have hi : w i ∈ Set.range v := by rw [hrange]; exact Set.mem_range_self i
    exact hi
  choose f hf using hex
  have hf0 : f 0 = 0 := hvinj ((hf 0).trans hzero.symm)
  have hfinj : Function.Injective f := by
    intro i j heq
    apply hwinj
    rw [← hf i, ← hf j, heq]
  have hfne (i) (hi : i ≠ 0) : f i ≠ 0 := by
    intro heq
    exact hi (hfinj (heq.trans hf0.symm))
  have hmono : StrictMono f := by
    intro i j hij
    by_cases hi0 : i = 0
    · subst i
      rw [hf0]
      have hne := hfne j (ne_of_gt hij)
      exact Fin.pos_iff_ne_zero.mpr hne
    have hj0 : j ≠ 0 := by
      intro hh
      have hh := congrArg Fin.val hh
      simp only [Fin.val_zero] at hh
      omega
    have hiPos : (0 : Fin n) < i := Fin.pos_iff_ne_zero.mpr hi0
    have hjPos : (0 : Fin n) < f j := Fin.pos_iff_ne_zero.mpr (hfne j hj0)
    have hpos := hwtri 0 i j hiPos hij
    rw [← hf 0, ← hf i, ← hf j, hf0] at hpos
    by_contra hh
    have hlt : f j < f i := lt_of_le_of_ne (le_of_not_gt hh) (hfinj.ne (ne_of_gt hij))
    have hneg := hvtri 0 (f j) (f i) hjPos hlt
    rw [turn_swap_last] at hneg
    linarith
  have hfid (i) : f i = i := le_antisymm (hmono.le_id i) (hmono.id_le i)
  funext i
  simpa only [hfid] using hf i

theorem range_cyclic_shift {n : ℕ} [NeZero n] (v : Fin n → Point) (a : Fin n) :
    Set.range (fun i ↦ v (i + a)) = Set.range v := by
  ext p
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i + a, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i - a, by simpa only [sub_add_cancel] using hi⟩

/-- A single common indexed vertex fixes the cyclic shift between two
positive enumerations of the same polygon. -/
theorem cyclic_enumerations_eq_of_fixed_index {n : ℕ} [NeZero n] {v w : Fin n → Point}
    (hvinj : Function.Injective v) (hwinj : Function.Injective w)
    (hvtri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hwtri : ∀ i j k, i < j → j < k → 0 < turn (w i) (w j) (w k))
    (hrange : Set.range v = Set.range w) {a : Fin n} (ha : v a = w a) : v = w := by
  have heq := cyclic_enumerations_eq_of_zero
    (v := fun i ↦ v (i + a)) (w := fun i ↦ w (i + a))
    (fun i j hij ↦ add_right_cancel (hvinj hij))
    (fun i j hij ↦ add_right_cancel (hwinj hij))
    (cyclic_shift_triples hvtri a) (cyclic_shift_triples hwtri a)
    (by rw [range_cyclic_shift, range_cyclic_shift, hrange])
    (by simpa only [zero_add] using ha)
  funext i
  have hh := congrFun heq (i - a)
  simpa only [sub_add_cancel] using hh

/-- When the selected apices exhaust the third layer, a closed radial
triangle contains only the apex with its own index. General position
converts the closed membership to a strict fan membership. -/
theorem apex_eq_of_mem_radial_triangle {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (v : Fin n → Point)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, ApexData S v d i (c i))
    (hfull : Finset.univ.image c = extremeLayer (inner (inner S)))
    {p : Point} (hp : p ∈ extremeLayer (inner (inner S))) (j : Fin n)
    (hpTri : p ∈ triangleHull d (v j) (v (j + 1))) : p = c j := by
  have hvB (i) : v i ∈ extremeLayer (inner S) := by
    change v i ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hvS (i) : v i ∈ S := inner_subset S (extremeLayer_subset _ (hvB i))
  have hdS : d ∈ S := inner_subset S (inner_subset _ (inner_subset _ hd))
  have hpI : p ∈ inner (inner S) := extremeLayer_subset _ hp
  have hpS : p ∈ S := inner_subset S (inner_subset _ hpI)
  have hpv (i) : p ≠ v i := by
    intro heq
    exact (Finset.mem_sdiff.mp hpI).2 (heq.symm ▸ hvB i)
  have hpd : p ≠ d := by
    intro heq
    exact (Finset.mem_sdiff.mp hd).2 (heq ▸ hp)
  have hpStrict := strictlyInsideTriangle_of_generalPosition hgen hdS (hvS j) (hvS (j + 1)) hpS
    (turn_pos_of_strictlyInsideTriangle (hdata j).strict_triangle) hpTri hpd (hpv j) (hpv (j + 1))
  rw [← hfull] at hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hij := radial_triangle_index_eq htri (hdata i).strict_triangle hpStrict
  rw [hij]

/-- Moving the center yields at least one unchanged apex index: take
the new fan triangle containing the old center. Its old fan triangle
is a subset, so it still contains the old selected apex. -/
theorem exists_fixed_apex_index {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d e : Point} (hd : d ∈ inner (inner (inner S))) (he : e ∈ inner (inner (inner S)))
    (c f : Fin n → Point) (hc : ∀ i, ApexData S v d i (c i))
    (hf : ∀ i, ApexData S v e i (f i))
    (hfull : Finset.univ.image f = extremeLayer (inner (inner S))) :
    ∃ i, c i = f i := by
  by_cases hde : d = e
  · subst e
    exact ⟨0, apex_eq_of_mem_radial_triangle hgen v hrange htri hd f hf hfull
      (hc 0).mem_third 0 (strictlyInsideTriangle_mem_triangleHull (hc 0).strict_triangle)⟩
  have hvB (i) : v i ∈ extremeLayer (inner S) := by
    change v i ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hvS (i) : v i ∈ S := inner_subset S (extremeLayer_subset _ (hvB i))
  have hdeep {p : Point} (hp : p ∈ inner (inner (inner S))) :
      p ∈ S ∧ p ∈ convexHull ℝ (Set.range v) ∧ p ∉ Set.range v := by
    have hpII : p ∈ inner (inner S) := inner_subset _ hp
    have hpI : p ∈ inner S := inner_subset _ hpII
    refine ⟨inner_subset S hpI, ?_, ?_⟩
    · rw [hrange, convexHull_extremeLayer]
      exact subset_convexHull ℝ _ hpI
    · rw [hrange]
      exact (Finset.mem_sdiff.mp hpII).2
  obtain ⟨hdS, hdHull, hdnot⟩ := hdeep hd
  obtain ⟨heS, heHull, henot⟩ := hdeep he
  obtain ⟨j, hj, _⟩ := exists_unique_radial_triangle hgen hn v hinj htri hvS heS hdS
    heHull henot hdHull hdnot (Ne.symm hde)
  have hcNew : c j ∈ triangleHull e (v j) (v (j + 1)) := by
    have hsub : triangleHull d (v j) (v (j + 1)) ⊆ triangleHull e (v j) (v (j + 1)) :=
      triangleHull_subset_of_mem (convex_convexHull ℝ _)
        (strictlyInsideTriangle_mem_triangleHull hj)
        (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
    exact hsub (strictlyInsideTriangle_mem_triangleHull (hc j).strict_triangle)
  exact ⟨j, apex_eq_of_mem_radial_triangle hgen v hrange htri he f hf hfull (hc j).mem_third j hcNew⟩

/-- If both deep viewpoints have one selected apex in every fan and
these exhaust the third layer, the indexed selections are identical.
This is the cyclic-matching step in the final `d` to `d′` argument. -/
theorem apex_selection_independent_of_deep_point {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d e : Point} (hd : d ∈ inner (inner (inner S))) (he : e ∈ inner (inner (inner S)))
    (c f : Fin n → Point) (hc : ∀ i, ApexData S v d i (c i))
    (hf : ∀ i, ApexData S v e i (f i))
    (hfullc : Finset.univ.image c = extremeLayer (inner (inner S)))
    (hfullf : Finset.univ.image f = extremeLayer (inner (inner S))) : c = f := by
  have hcinj : Function.Injective c := by
    intro i j heq
    apply radial_triangle_index_eq htri (hc i).strict_triangle
    rw [heq]
    exact (hc j).strict_triangle
  have hfinj : Function.Injective f := by
    intro i j heq
    apply radial_triangle_index_eq htri (hf i).strict_triangle
    rw [heq]
    exact (hf j).strict_triangle
  have hcR : Set.range c = (extremeLayer (inner (inner S)) : Set Point) := by
    simpa using congrArg (fun X : Finset Point ↦ (X : Set Point)) hfullc
  have hfR : Set.range f = (extremeLayer (inner (inner S)) : Set Point) := by
    simpa using congrArg (fun X : Finset Point ↦ (X : Set Point)) hfullf
  obtain ⟨j, hj⟩ := exists_fixed_apex_index hgen hn v hinj hrange htri hd he c f hc hf hfullf
  exact cyclic_enumerations_eq_of_fixed_index hcinj hfinj
    (apex_cyclic_triples hgen htri hd hc) (apex_cyclic_triples hgen htri he hf)
    (hcR.trans hfR.symm) hj

theorem apex_image_eq_of_card {S : Finset Point} {n : ℕ} [NeZero n]
    {v c : Fin n → Point} {d : Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hc : ∀ i, ApexData S v d i (c i))
    (hcard : (extremeLayer (inner (inner S))).card = n) :
    Finset.univ.image c = extremeLayer (inner (inner S)) := by
  have hcinj : Function.Injective c := by
    intro i j heq
    apply radial_triangle_index_eq htri (hc i).strict_triangle
    rw [heq]
    exact (hc j).strict_triangle
  apply Finset.eq_of_subset_of_card_le
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (hc i).mem_third
  · rw [hcard, Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_fin]

/-- Under Valtr's all-fans condition for fourth-layer viewpoints, every
consecutive five-apex cap contains a fourth-layer point that preserves
all the selected apices and hence all the sectors. This packages the
entire center-changing step before the final geometric splice. -/
theorem exists_cap_point_preserving_apices {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hc : ∀ i, ApexData S v d i (c i))
    (hfull : Finset.univ.image c = extremeLayer (inner (inner S)))
    (hall : ∀ e ∈ layer S 3, ∀ i, MeetsThirdLayer S v e i)
    (a : ℕ) (ha : a + 5 ≤ n) :
    ∃ e ∈ layer S 3,
      e ∈ convexHull ℝ (Set.range (fun i : Fin 5 ↦ c (Lax56Proofs.ValtrPolygon.offsetIndex a ha i))) ∧
      ∀ i, ApexData S v e i (c i) := by
  have hcinj : Function.Injective c := by
    intro i j heq
    apply radial_triangle_index_eq htri (hc i).strict_triangle
    rw [heq]
    exact (hc j).strict_triangle
  have hcrange : Set.range c = (extremeLayer (inner (inner S)) : Set Point) := by
    simpa using congrArg (fun X : Finset Point ↦ (X : Set Point)) hfull
  have hcCard : (extremeLayer (inner (inner S))).card = n := by
    rw [← hfull, Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_fin]
  have hgenQ : ¬HasThreeCollinear (inner (inner S)) := fun hh ↦ hgen
    (hasThreeCollinear_mono ((inner_subset (inner S)).trans (inner_subset S)) hh)
  have hclosed : HullClosedIn S (inner (inner S)) :=
    hullClosedIn_trans (inner_hullClosedIn S) (inner_hullClosedIn (inner S))
  have hnoQ : ¬HasEmptyHexagon (inner (inner S)) := fun hh ↦ hno (hasEmptyHexagon_transfer hclosed hh)
  obtain ⟨e, he, heCap⟩ := Lax56Proofs.ValtrPolygon.exists_next_layer_vertex_in_five_cap hgenQ hnoQ
    ⟨d, hd⟩ c hcinj hcrange (apex_cyclic_triples hgen htri hd hc) a ha
  have heD : e ∈ layer S 3 := he
  have hedeep : e ∈ inner (inner (inner S)) := extremeLayer_subset _ he
  obtain ⟨f, hf⟩ := exists_radial_apices hgen hno (by omega : 2 ≤ n) v hinj hrange htri hedeep
  have hf' (i) : ApexData S v e i (f i) := hf i (hall e heD i)
  have hfFull := apex_image_eq_of_card htri hf' hcCard
  have heq := apex_selection_independent_of_deep_point hgen (by omega : 2 ≤ n)
    v hinj hrange htri hd hedeep c f hc hf' hfull hfFull
  refine ⟨e, heD, heCap, ?_⟩
  rw [heq]
  exact hf'

end Lax56Proofs.ValtrMatching
