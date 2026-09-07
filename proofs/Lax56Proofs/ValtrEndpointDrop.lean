import Lax56Proofs.ValtrEndpointGeometry

namespace Lax56Proofs.ValtrEndpointDrop

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrProjective Lax56Proofs.ValtrMaximum
open Lax56Proofs.ValtrRunSupport Lax56Proofs.ValtrConvexRun
open Lax56Proofs.ValtrRunSetup Lax56Proofs.ValtrSectorSetup
open Lax56Proofs.ValtrRunReduction Lax56Proofs.ValtrEndpointGeometry
open scoped Classical Fin.NatCast

/-- Exclusion from the rest of a run forces the supporting-side test
needed for the first empty-pentagon extension, when the last endpoint
is nonconvex. No condition on the first endpoint is used here. -/
theorem first_sector_side_of_last_interior {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {m : ℕ} {b h : ℕ → Point} {d x : Point}
    (cfg : RunGeometry S m b h d)
    (hlast : StrictlyInsideTriangle (b m) (h (m - 1)) (b (m + 1)) (h m))
    (hx : x ∈ extremeLayer S) (hfirst : x ∈ sector ![b 1, h 1, b 2])
    (hout : ∀ k, 2 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)]) :
    0 < turn (h 2) (b 2) x := by
  have hm := cfg.length
  obtain ⟨l, hY⟩ := exists_positive_height_of_not_mem_hull
    (extreme_not_mem_convexHull_inner hx)
  have hYI (p) (hp : p ∈ inner S) : l x < l p := hY p (subset_convexHull ℝ _ hp)
  have hYh (k) (hk : k ≤ m + 1) := hYI (h k) (cfg.chain_inner k hk)
  have hYb (k) (hk : 1 ≤ k) (hkm : k ≤ m + 1) := hYI (b k) (cfg.base_inner k hk hkm)
  have hneX (p) (hp : p ∈ inner S) : p ≠ x := fun heq ↦
    (Finset.mem_sdiff.mp hp).2 (heq.symm ▸ hx)
  have hr : l x < l (h 1) := hYh 1 (by omega)
  let z := fun k ↦ projectiveValue l x (h 1) (h k)
  let a := fun k ↦ projectiveValue l x (h 1) (b k)
  have hlarge (k) (hk : 2 ≤ k) (hkm : k ≤ m) :
      z k < z (k - 1) ∨ z k < a k ∨ z k < a (k + 1) ∨ z k < z (k + 1) := by
    have hN (q) (hq : q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point)) :=
      cfg.neighbor_mem_ne k (by omega) hkm hq
    obtain ⟨q, hq, hlt⟩ := (projectiveValue_between_generators l hr (hYh k (by omega))
      (fun q hq ↦ hYI q (hN q hq).1) (cfg.tail_local_hulls hgen hlast k hk hkm)
      (cfg.neighbor_turn_ne hgen (extremeLayer_subset _ hx) k (by omega) hkm
        (hneX _ (cfg.chain_inner k (by omega))) (fun q hq ↦ hneX q (hN q hq).1))).2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Or.inl hlt
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (Or.inl hlt))
    · exact Or.inr (Or.inr (Or.inr hlt))
  have hbase_ne (k j) (hk : 1 ≤ k) (hkm : k ≤ m)
      (hj : 1 ≤ j) (hjm : j ≤ m + 1) : z k ≠ a j := by
    apply projectiveValue_ne l hr (hYh k (by omega)) (hYb j hj hjm)
    exact turn_ne_zero_of_generalPosition hgen
      (inner_subset _ (cfg.chain_inner k (by omega)))
      (inner_subset _ (cfg.base_inner j hj hjm)) (extremeLayer_subset _ hx)
      (cfg.apex_ne_base k j hk hkm hj hjm)
      (hneX _ (cfg.chain_inner k (by omega))) (hneX _ (cfg.base_inner j hj hjm))
  have hforbid (k) (hk : 2 ≤ k) (hkm : k ≤ m) : ¬(a k < z k ∧ z k < a (k + 1)) := by
    intro hi
    apply hout k hk hkm
    exact (sector_iff_projective_interval l hr (hYb k (by omega) (by omega))
      (hYh k (by omega)) (hYb (k + 1) (by omega) (by omega))).mpr hi
  have hstart : z 1 < a 2 := (sector_iff_projective_interval l hr
    (hYb 1 (by decide) (by omega)) (hYh 1 (by omega))
    (hYb 2 (by decide) (by omega))).mp hfirst |>.2
  apply (projectiveValue_lt_iff l hr (hYh 2 (by omega)) (hYb 2 (by decide) (by omega))).mp
  change z 2 < a 2
  by_contra hfail
  have hbad : a 2 < z 2 := lt_of_le_of_ne (le_of_not_gt hfail)
    (hbase_ne 2 2 (by decide) (by omega) (by decide) (by omega)).symm
  have hend : z (m + 1) = a (m + 1) := congrArg (projectiveValue l x (h 1)) cfg.last
  exact scalar_no_forward_ascent_state z a (Or.inl hend) hlarge
    (fun k hk hkm ↦ hbase_ne k (k + 1) (by omega) hkm (by omega) (by omega))
    hforbid 2 (by decide) (by omega) ⟨hstart.trans hbad, hbad⟩

/-- Symmetric propagation from a last-sector point when the first
endpoint is nonconvex. -/
theorem last_sector_side_of_first_interior {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {m : ℕ} {b h : ℕ → Point} {d x : Point}
    (cfg : RunGeometry S m b h d)
    (hfirst : StrictlyInsideTriangle (b 1) (h 2) (b 2) (h 1))
    (hx : x ∈ extremeLayer S) (hlast : x ∈ sector ![b m, h m, b (m + 1)])
    (hout : ∀ k, 1 ≤ k → k < m → x ∉ sector ![b k, h k, b (k + 1)]) :
    0 < turn (b m) (h (m - 1)) x := by
  have hm := cfg.length
  obtain ⟨l, hY⟩ := exists_positive_height_of_not_mem_hull
    (extreme_not_mem_convexHull_inner hx)
  have hYI (p) (hp : p ∈ inner S) : l x < l p := hY p (subset_convexHull ℝ _ hp)
  have hYh (k) (hk : k ≤ m + 1) := hYI (h k) (cfg.chain_inner k hk)
  have hYb (k) (hk : 1 ≤ k) (hkm : k ≤ m + 1) := hYI (b k) (cfg.base_inner k hk hkm)
  have hneX (p) (hp : p ∈ inner S) : p ≠ x := fun heq ↦
    (Finset.mem_sdiff.mp hp).2 (heq.symm ▸ hx)
  have hr : l x < l (h 1) := hYh 1 (by omega)
  let z := fun k ↦ projectiveValue l x (h 1) (h k)
  let a := fun k ↦ projectiveValue l x (h 1) (b k)
  have hsmall (k) (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
      z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k := by
    have hN (q) (hq : q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point)) :=
      cfg.neighbor_mem_ne k hk (by omega : k ≤ m) hq
    obtain ⟨q, hq, hlt⟩ := (projectiveValue_between_generators l hr (hYh k (by omega))
      (fun q hq ↦ hYI q (hN q hq).1) (cfg.head_local_hulls hgen hfirst k hk (by omega))
      (cfg.neighbor_turn_ne hgen (extremeLayer_subset _ hx) k hk (by omega)
        (hneX _ (cfg.chain_inner k (by omega))) (fun q hq ↦ hneX q (hN q hq).1))).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Or.inl hlt
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (Or.inl hlt))
    · exact Or.inr (Or.inr (Or.inr hlt))
  have hbase_ne (k j) (hk : 1 ≤ k) (hkm : k ≤ m)
      (hj : 1 ≤ j) (hjm : j ≤ m + 1) : z k ≠ a j := by
    apply projectiveValue_ne l hr (hYh k (by omega)) (hYb j hj hjm)
    exact turn_ne_zero_of_generalPosition hgen
      (inner_subset _ (cfg.chain_inner k (by omega)))
      (inner_subset _ (cfg.base_inner j hj hjm)) (extremeLayer_subset _ hx)
      (cfg.apex_ne_base k j hk hkm hj hjm)
      (hneX _ (cfg.chain_inner k (by omega))) (hneX _ (cfg.base_inner j hj hjm))
  have hforbid (k) (hk : 1 ≤ k) (hkm : k ≤ m - 1) : ¬(a k < z k ∧ z k < a (k + 1)) := by
    intro hi
    apply hout k hk (by omega)
    exact (sector_iff_projective_interval l hr (hYb k hk (by omega))
      (hYh k (by omega)) (hYb (k + 1) (by omega) (by omega))).mpr hi
  have hend : a m < z m := (sector_iff_projective_interval l hr
    (hYb m (by omega) (by omega)) (hYh m (by omega))
    (hYb (m + 1) (by omega) le_rfl)).mp hlast |>.1
  apply (projectiveValue_lt_iff l hr (hYb m (by omega) (by omega))
    (hYh (m - 1) (by omega))).mp
  change a m < z (m - 1)
  by_contra hfail
  have hbad : z (m - 1) < a m := lt_of_le_of_ne (le_of_not_gt hfail)
    (hbase_ne (m - 1) m (by omega) (by omega) (by omega) (by omega))
  have hstart : z 0 = a 1 := congrArg (projectiveValue l x (h 1)) cfg.first
  apply scalar_no_backward_ascent_state z a (Or.inl hstart) hsmall
    (fun k hk hkm ↦ hbase_ne k k hk (by omega) hk (by omega)) hforbid
    (m - 1) (by omega) le_rfl
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  exact ⟨hbad.trans hend, hbad⟩

theorem first_private_card_le_one {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {m : ℕ} {b h : ℕ → Point} {d : Point} (cfg : RunGeometry S m b h d)
    (hquad : 0 < turn (b 1) (h 1) (h 2) ∧ 0 < turn (b 1) (h 1) (b 2) ∧
      0 < turn (b 1) (h 2) (b 2) ∧ 0 < turn (h 1) (h 2) (b 2))
    (hlast : StrictlyInsideTriangle (b m) (h (m - 1)) (b (m + 1)) (h m)) :
    ((extremeLayer S).filter (fun x ↦ x ∈ sector ![b 1, h 1, b 2] ∧
      ∀ k, 2 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)])).card ≤ 1 := by
  have hm := cfg.length
  apply le_trans (Finset.card_le_card (show
      (extremeLayer S).filter (fun x ↦ x ∈ sector ![b 1, h 1, b 2] ∧
        ∀ k, 2 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)]) ⊆
      (extremeLayer S).filter (fun x ↦ x ∈ sector ![b 1, h 1, b 2] ∧
        0 < turn (h 2) (b 2) x) from ?_))
    (convex_quad_side_card_le_one hgen hno
      (cfg.base_inner 1 (by decide) (by omega)) (cfg.chain_inner 1 (by omega))
      (inner_subset _ (cfg.chain_inner 2 (by omega))) (cfg.base_inner 2 (by decide) (by omega))
      hquad.2.1 hquad.1 hquad.2.2.1 hquad.2.2.2
      (cfg.base_support 1 (by decide) (by omega)) (cfg.empty_triangle 1 (by decide) (by omega)))
  intro x hx
  obtain ⟨hx, hS, hout⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, hS,
    first_sector_side_of_last_interior hgen cfg hlast hx hS hout⟩

theorem last_private_card_le_one {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {m : ℕ} {b h : ℕ → Point} {d : Point} (cfg : RunGeometry S m b h d)
    (hquad : 0 < turn (b m) (h (m - 1)) (h m) ∧ 0 < turn (b m) (h (m - 1)) (b (m + 1)) ∧
      0 < turn (b m) (h m) (b (m + 1)) ∧ 0 < turn (h (m - 1)) (h m) (b (m + 1)))
    (hfirst : StrictlyInsideTriangle (b 1) (h 2) (b 2) (h 1)) :
    ((extremeLayer S).filter (fun x ↦ x ∈ sector ![b m, h m, b (m + 1)] ∧
      ∀ k, 1 ≤ k → k < m → x ∉ sector ![b k, h k, b (k + 1)])).card ≤ 1 := by
  have hm := cfg.length
  apply le_trans (Finset.card_le_card (show
      (extremeLayer S).filter (fun x ↦ x ∈ sector ![b m, h m, b (m + 1)] ∧
        ∀ k, 1 ≤ k → k < m → x ∉ sector ![b k, h k, b (k + 1)]) ⊆
      (extremeLayer S).filter (fun x ↦ x ∈ sector ![b m, h m, b (m + 1)] ∧
        0 < turn (b m) (h (m - 1)) x) from ?_))
    (last_convex_quad_side_card_le_one hgen hno
      (cfg.base_inner m (by omega) (by omega)) (cfg.chain_inner m (by omega))
      (inner_subset _ (cfg.chain_inner (m - 1) (by omega)))
      (cfg.base_inner (m + 1) (by omega) le_rfl)
      hquad.1 hquad.2.1 hquad.2.2.1 hquad.2.2.2
      (cfg.base_support m (by omega) le_rfl) (cfg.empty_triangle m (by omega) le_rfl))
  intro x hx
  obtain ⟨hx, hS, hout⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hx, hS,
    last_sector_side_of_first_interior hgen cfg hfirst hx hS hout⟩

/-- The clockwise first endpoint drop, on the actual positively
indexed finite run. This is the first convex/last nonconvex case. -/
theorem first_drop_card_of_mixed_endpoints {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (start : Fin n) {t : ℕ} (ht : 2 ≤ t) (htn : t < n)
    (hdefined : ∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k))
    (hfirst : ¬StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1))
    (hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t)) :
    (((Finset.range t).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))) \
      (Finset.range (t - 1)).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))).card ≤ 1 := by
  let b := runBase v start t
  let h := runChain v c start t
  have cfg := runGeometry_of_apex_data hgen v hinj hrange htri hd c hdata start ht htn hdefined
  have hquad := first_quad_of_not_interior hgen v hinj hrange htri hd c hdata start ht htn hdefined hfirst
  apply le_trans (Finset.card_le_card (t := (extremeLayer S).filter (fun x ↦
      x ∈ sector ![b 1, h 1, b 2] ∧ ∀ k, 2 ≤ k → k ≤ t →
        x ∉ sector ![b k, h k, b (k + 1)])) ?_)
    (first_private_card_le_one hgen hno cfg hquad hlast)
  intro x hx
  obtain ⟨hxU, hxNot⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxU
  have hit := Finset.mem_range.mp hi
  have hieq : i = t - 1 := by
    by_contra hh
    apply hxNot
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (by omega), hxi⟩
  subst i
  obtain ⟨_, hxA, hxS⟩ := mem_sectorPoints_iff.mp hxi
  apply Finset.mem_filter.mpr
  refine ⟨hxA, ?_, ?_⟩
  · change x ∈ sector ![runBase v start t 1, runChain v c start t 1, runBase v start t (1 + 1)]
    simpa only [runBase_current v start (t := t) (k := 1) (by decide) (by omega), runBase_next,
      runChain_apex v c start (t := t) (k := 1) (by decide) (by omega)] using hxS
  · intro k hk hkt hS
    apply hxNot
    apply Finset.mem_biUnion.mpr
    refine ⟨t - k, Finset.mem_range.mpr (by omega), mem_sectorPoints_iff.mpr ?_⟩
    refine ⟨hdefined (t - k) (by omega), hxA, ?_⟩
    simpa only [b, h, runBase_current v start (by omega : 1 ≤ k) hkt, runBase_next,
      runChain_apex v c start (by omega : 1 ≤ k) hkt] using hS

/-- The clockwise last endpoint drop: first nonconvex/last convex. -/
theorem last_drop_card_of_mixed_endpoints {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (start : Fin n) {t : ℕ} (ht : 2 ≤ t) (htn : t < n)
    (hdefined : ∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k))
    (hfirst : StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1))
    (hlast : ¬StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t)) :
    (((Finset.range t).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))) \
      (Finset.range (t - 1)).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex (start + 1) k))).card ≤ 1 := by
  let b := runBase v start t
  let h := runChain v c start t
  have cfg := runGeometry_of_apex_data hgen v hinj hrange htri hd c hdata start ht htn hdefined
  have hquad := last_quad_of_not_interior hgen v hinj hrange htri hd c hdata start ht htn hdefined hlast
  have hshift (k) : cyclicIndex (start + 1) k = cyclicIndex start (k + 1) := by
    simp only [cyclicIndex, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
  apply le_trans (Finset.card_le_card (t := (extremeLayer S).filter (fun x ↦
      x ∈ sector ![b t, h t, b (t + 1)] ∧ ∀ k, 1 ≤ k → k < t →
        x ∉ sector ![b k, h k, b (k + 1)])) ?_)
    (last_private_card_le_one hgen hno cfg hquad hfirst)
  intro x hx
  obtain ⟨hxU, hxNot⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hxU
  have hit := Finset.mem_range.mp hi
  have hieq : i = 0 := by
    by_contra hh
    apply hxNot
    apply Finset.mem_biUnion.mpr
    refine ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [hshift, Nat.sub_add_cancel (by omega : 1 ≤ i)]
    exact hxi
  subst i
  obtain ⟨_, hxA, hxS⟩ := mem_sectorPoints_iff.mp hxi
  apply Finset.mem_filter.mpr
  refine ⟨hxA, ?_, ?_⟩
  · change x ∈ sector ![runBase v start t t, runChain v c start t t, runBase v start t (t + 1)]
    simpa only [runBase_current v start (by omega : 1 ≤ t) le_rfl, runBase_next,
      runChain_apex v c start (by omega : 1 ≤ t) le_rfl, Nat.sub_self] using hxS
  · intro k hk hkt hS
    apply hxNot
    apply Finset.mem_biUnion.mpr
    refine ⟨t - k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    rw [hshift, Nat.sub_add_cancel (by omega : 1 ≤ t - k)]
    apply mem_sectorPoints_iff.mpr
    refine ⟨hdefined (t - k) (by omega), hxA, ?_⟩
    simpa only [b, h, runBase_current v start hk (by omega : k ≤ t), runBase_next,
      runChain_apex v c start hk (by omega : k ≤ t)] using hS

end Lax56Proofs.ValtrEndpointDrop
