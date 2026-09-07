import Lax56Proofs.ValtrRunSetup

namespace Lax56Proofs.ValtrEndpointGeometry

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrSectorSetup
open Lax56Proofs.ValtrCoverSetup Lax56Proofs.ValtrRunSetup Lax56Proofs.ValtrLocalSupport
open scoped Classical Fin.NatCast

/-- With all three fixed quadrilateral turns positive, the remaining
turn distinguishes exactly the convex and interior-point cases. -/
theorem endpoint_quad_or_interior {a p q b : Point}
    (hapb : 0 < turn a p b) (haqb : 0 < turn a q b)
    (hpqb : 0 < turn p q b) (hne : turn a p q ≠ 0) :
    (0 < turn a p q ∧ 0 < turn a p b ∧ 0 < turn a q b ∧ 0 < turn p q b) ∨
      StrictlyInsideTriangle a q b p := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · apply Or.inr
    refine ⟨?_, ?_, ?_⟩
    · rw [turn_swap_last]; exact neg_pos.mpr hneg
    · rw [turn_rotate]; exact hpqb
    · convert hapb using 1 <;> unfold turn <;> ring
  · exact Or.inl ⟨hpos, hapb, haqb, hpqb⟩

theorem third_point_base_pos {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {p : Point} (hp : p ∈ inner (inner S)) (i : Fin n) : 0 < turn (v i) (v (i + 1)) p := by
  have hgenQ : ¬HasThreeCollinear (inner S) := fun hh ↦
    hgen (hasThreeCollinear_mono (inner_subset S) hh)
  have hv (j) : v j ∈ inner S := by
    apply extremeLayer_subset
    change v j ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self j
  apply cyclic_edge_strict_of_mem_hull hgenQ hn v hinj htri hv (inner_subset _ hp) _ _ i
  · rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ (inner_subset _ hp)
  · rw [hrange]
    exact (Finset.mem_sdiff.mp hp).2

/-- The first endpoint branch is genuinely the convex-quadrilateral
case: the three fixed turns follow from the layers and radial triangles. -/
theorem first_quad_of_not_interior {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (start : Fin n) {t : ℕ} (ht : 2 ≤ t) (htn : t < n)
    (hdefined : ∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k))
    (hnot : ¬StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1)) :
    let b := runBase v start t
    let h := runChain v c start t
    0 < turn (b 1) (h 1) (h 2) ∧ 0 < turn (b 1) (h 1) (b 2) ∧
      0 < turn (b 1) (h 2) (b 2) ∧ 0 < turn (h 1) (h 2) (b 2) := by
  let b := runBase v start t
  let h := runChain v c start t
  have hb (j) : b j ∈ extremeLayer (inner S) := by
    change v _ ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self _
  have hc (i) (hi : 1 ≤ i) (hit : i ≤ t) : h i ∈ inner (inner S) := by
    rw [show h i = c (cyclicIndex start (t - i)) from runChain_apex v c start hi hit]
    exact extremeLayer_subset _ (hdata _ (hdefined (t - i) (by omega))).mem_third
  have hcb (i j) (hi : 1 ≤ i) (hit : i ≤ t) : h i ≠ b j := fun heq ↦
    (Finset.mem_sdiff.mp (hc i hi hit)).2 (heq.symm ▸ hb j)
  have hfan (i) (hi : 1 ≤ i) (hit : i ≤ t) :
      StrictlyInsideTriangle d (b (i + 1)) (b i) (h i) := by
    change StrictlyInsideTriangle d (runBase v start t (i + 1)) (runBase v start t i)
      (runChain v c start t i)
    rw [runBase_current v start hi hit, runBase_next, runChain_apex v c start hi hit]
    exact (hdata _ (hdefined (t - i) (by omega))).strict_triangle
  have hab : 0 < turn (b 1) (h 1) (b 2) := by
    convert (hfan 1 (by decide) (by omega)).2.1 using 1 <;> unfold turn <;> ring
  have haqb : 0 < turn (b 1) (h 2) (b 2) := by
    change 0 < turn (runBase v start t 1) (h 2) (runBase v start t 2)
    rw [runBase_current v start (by decide) (by omega), runBase_next]
    convert third_point_base_pos hgen (by omega) v hinj hrange htri
      (hc 2 (by decide) ht) (cyclicIndex start (t - 1)) using 1 <;> unfold turn <;> ring
  have hmid : 0 < turn (h 1) (h 2) (b 2) := by
    apply intermediate_vertex_left_of_chord (hb 2) (inner_subset _ hd)
      (hc 1 (by decide) (by omega)) (hc 2 (by decide) ht)
    · rw [turn_swap_last]; exact neg_neg_of_pos (hfan 1 (by decide) (by omega)).1
    · rw [turn_swap_first]; exact neg_neg_of_pos (hfan 2 (by decide) ht).2.2
  have hhne : h 1 ≠ h 2 := by
    intro heq
    rw [heq] at hmid
    simp [turn] at hmid
  have hne := turn_ne_zero_of_generalPosition hgen
    (inner_subset _ (extremeLayer_subset _ (hb 1)))
    (inner_subset _ (inner_subset _ (hc 1 (by decide) (by omega))))
    (inner_subset _ (inner_subset _ (hc 2 (by decide) ht)))
    (hcb 1 1 (by decide) (by omega)).symm (hcb 2 1 (by decide) ht).symm hhne
  exact (endpoint_quad_or_interior hab haqb hmid hne).resolve_right hnot

theorem last_quad_of_not_interior {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (start : Fin n) {t : ℕ} (ht : 2 ≤ t) (htn : t < n)
    (hdefined : ∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k))
    (hnot : ¬StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t)) :
    let b := runBase v start t
    let h := runChain v c start t
    0 < turn (b t) (h (t - 1)) (h t) ∧ 0 < turn (b t) (h (t - 1)) (b (t + 1)) ∧
      0 < turn (b t) (h t) (b (t + 1)) ∧ 0 < turn (h (t - 1)) (h t) (b (t + 1)) := by
  let b := runBase v start t
  let h := runChain v c start t
  have hb (j) : b j ∈ extremeLayer (inner S) := by
    change v _ ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self _
  have hc (i) (hi : 1 ≤ i) (hit : i ≤ t) : h i ∈ inner (inner S) := by
    rw [show h i = c (cyclicIndex start (t - i)) from runChain_apex v c start hi hit]
    exact extremeLayer_subset _ (hdata _ (hdefined (t - i) (by omega))).mem_third
  have hcb (i j) (hi : 1 ≤ i) (hit : i ≤ t) : h i ≠ b j := fun heq ↦
    (Finset.mem_sdiff.mp (hc i hi hit)).2 (heq.symm ▸ hb j)
  have hfan (i) (hi : 1 ≤ i) (hit : i ≤ t) :
      StrictlyInsideTriangle d (b (i + 1)) (b i) (h i) := by
    change StrictlyInsideTriangle d (runBase v start t (i + 1)) (runBase v start t i)
      (runChain v c start t i)
    rw [runBase_current v start hi hit, runBase_next, runChain_apex v c start hi hit]
    exact (hdata _ (hdefined (t - i) (by omega))).strict_triangle
  have hab : 0 < turn (b t) (h t) (b (t + 1)) := by
    convert (hfan t (by omega) le_rfl).2.1 using 1 <;> unfold turn <;> ring
  have haqb : 0 < turn (b t) (h (t - 1)) (b (t + 1)) := by
    change 0 < turn (runBase v start t t) (h (t - 1)) (runBase v start t (t + 1))
    rw [runBase_current v start (by omega) le_rfl, runBase_next]
    convert third_point_base_pos hgen (by omega) v hinj hrange htri
      (hc (t - 1) (by omega) (by omega)) (cyclicIndex start (t - t)) using 1 <;> unfold turn <;> ring
  have hmid : 0 < turn (h (t - 1)) (h t) (b t) := by
    apply intermediate_vertex_left_of_chord (hb t) (inner_subset _ hd)
      (hc (t - 1) (by omega) (by omega)) (hc t (by omega) le_rfl)
    · have hf := (hfan (t - 1) (by omega) (by omega)).1
      rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at hf
      rw [turn_swap_last]; exact neg_neg_of_pos hf
    · rw [turn_swap_first]; exact neg_neg_of_pos (hfan t (by omega) le_rfl).2.2
  have hhne : h (t - 1) ≠ h t := by
    intro heq
    rw [heq] at hmid
    simp [turn] at hmid
  have hne := turn_ne_zero_of_generalPosition hgen
    (inner_subset _ (inner_subset _ (hc (t - 1) (by omega) (by omega))))
    (inner_subset _ (inner_subset _ (hc t (by omega) le_rfl)))
    (inner_subset _ (extremeLayer_subset _ (hb (t + 1)))) hhne
    (hcb (t - 1) (t + 1) (by omega) (by omega)) (hcb t (t + 1) (by omega) le_rfl)
  have hfirst : 0 < turn (b t) (h (t - 1)) (h t) := by rw [← turn_rotate]; exact hmid
  refine ⟨hfirst, haqb, hab, ?_⟩
  by_contra hh
  have hneg := lt_of_le_of_ne (le_of_not_gt hh) hne
  apply hnot
  refine ⟨hfirst, ?_, ?_⟩
  · rw [turn_swap_last]; exact neg_pos.mpr hneg
  · convert hab using 1 <;> unfold turn <;> ring

end Lax56Proofs.ValtrEndpointGeometry
