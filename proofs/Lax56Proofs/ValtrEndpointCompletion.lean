import Lax56Proofs.ValtrEdgeCaps
import Lax56Proofs.ValtrEndpointDrop

namespace Lax56Proofs.ValtrEndpointCompletion

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrProjective Lax56Proofs.ValtrMaximum
open Lax56Proofs.ValtrRunSupport Lax56Proofs.ValtrConvexRun Lax56Proofs.ValtrEdgeCaps
open scoped Classical

/-- A backward ascent persists throughout the internal part of a run;
unlike the endpoint maximum principle, no condition at the first endpoint
is needed to conclude these internal inequalities. -/
theorem backward_states (z a : ℕ → ℝ) {m : ℕ} (hm : 2 ≤ m)
    (hsmall : ∀ k, 2 ≤ k → k < m →
      z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k)
    (hne : ∀ k, 2 ≤ k → k < m → z k ≠ a k)
    (hforbid : ∀ k, 2 ≤ k → k < m → ¬(a k < z k ∧ z k < a (k + 1)))
    (hstart : z (m - 1) < z m ∧ z (m - 1) < a m) :
    ∀ k, 1 ≤ k → k < m → z k < z (k + 1) ∧ z k < a (k + 1) := by
  intro k hk hkm
  refine Nat.decreasingInduction' (P := fun j ↦ z j < z (j + 1) ∧ z j < a (j + 1))
      (n := m - 1) (m := k) ?_ (by omega) ?_
  · intro j hj hkj hnext
    have hjpos : 2 ≤ j + 1 := by omega
    have hjlt : j + 1 < m := by omega
    have hown : z (j + 1) < a (j + 1) := by
      have hh : ¬a (j + 1) < z (j + 1) :=
        fun hh ↦ hforbid (j + 1) hjpos hjlt ⟨hh, hnext.2⟩
      exact lt_of_le_of_ne (le_of_not_gt hh) (hne (j + 1) hjpos hjlt)
    have hprev : z j < z (j + 1) := by
      have hh := hsmall (j + 1) hjpos hjlt
      simp only [Nat.add_sub_cancel] at hh
      rcases hh with hh | hh | hh | hh <;> linarith [hnext.1, hnext.2]
    exact ⟨hprev, hprev.trans hown⟩
  · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m)] using hstart

/-- If the last convex endpoint cannot extend its empty pentagon, a
private last-sector point lies beyond every base edge of the run. -/
theorem last_bad_point_beyond_bases {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {m : ℕ} {b h : ℕ → Point} {d x : Point}
    (cfg : RunGeometry S m b h d) (hx : x ∈ extremeLayer S)
    (hlast : x ∈ sector ![b m, h m, b (m + 1)])
    (hout : ∀ k, 1 ≤ k → k < m → x ∉ sector ![b k, h k, b (k + 1)])
    (hbad : turn (b m) (h (m - 1)) x < 0) :
    ∀ k, 1 ≤ k → k ≤ m → 0 < turn (b k) (b (k + 1)) x := by
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
  have hsmall (k) (hk : 2 ≤ k) (hkm : k < m) :
      z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k := by
    have hN (q) (hq : q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point)) :=
      cfg.neighbor_mem_ne k (by omega) (by omega) hq
    obtain ⟨q, hq, hlt⟩ := (projectiveValue_between_generators l hr (hYh k (by omega))
      (fun q hq ↦ hYI q (hN q hq).1) (cfg.internal_local_hull hgen k hk hkm)
      (cfg.neighbor_turn_ne hgen (extremeLayer_subset _ hx) k (by omega) (by omega)
        (hneX _ (cfg.chain_inner k (by omega))) (fun q hq ↦ hneX q (hN q hq).1))).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Or.inl hlt
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (Or.inl hlt))
    · exact Or.inr (Or.inr (Or.inr hlt))
  have hne (k) (hk : 2 ≤ k) (hkm : k < m) : z k ≠ a k := by
    apply projectiveValue_ne l hr (hYh k (by omega)) (hYb k (by omega) (by omega))
    exact turn_ne_zero_of_generalPosition hgen
      (inner_subset _ (cfg.chain_inner k (by omega)))
      (inner_subset _ (cfg.base_inner k (by omega) (by omega))) (extremeLayer_subset _ hx)
      (cfg.apex_ne_base k k (by omega) (by omega) (by omega) (by omega))
      (hneX _ (cfg.chain_inner k (by omega))) (hneX _ (cfg.base_inner k (by omega) (by omega)))
  have hforbid (k) (hk : 2 ≤ k) (hkm : k < m) : ¬(a k < z k ∧ z k < a (k + 1)) := by
    intro hh
    exact hout k (by omega) hkm ((sector_iff_projective_interval l hr
      (hYb k (by omega) (by omega)) (hYh k (by omega))
      (hYb (k + 1) (by omega) (by omega))).mpr hh)
  have hright : a m < z m := (sector_iff_projective_interval l hr
    (hYb m (by omega) (by omega)) (hYh m (by omega))
    (hYb (m + 1) (by omega) le_rfl)).mp hlast |>.1
  have hleft : z (m - 1) < a m := by
    apply (projectiveValue_lt_iff l hr (hYh (m - 1) (by omega))
      (hYb m (by omega) (by omega))).mpr
    rw [turn_swap_first]
    exact neg_pos.mpr hbad
  have hstates := backward_states z a hm hsmall hne hforbid ⟨hleft.trans hright, hleft⟩
  have hside (k) (hk : 1 ≤ k) (hkm : k < m) : 0 < turn (h k) (b (k + 1)) x :=
    (projectiveValue_lt_iff l hr (hYh k (by omega))
      (hYb (k + 1) (by omega) (by omega))).mp (hstates k hk hkm).2
  intro k hk hkm
  refine Nat.decreasingInduction' (P := fun j ↦ 0 < turn (b j) (b (j + 1)) x)
    (m := k) (n := m) ?_ hkm ?_
  · intro j hj hkj hnext
    apply previous_base_pos (e := h j) (f := b (j + 2))
    · exact cfg.base_strict hgen j (by omega) (by omega) (cfg.chain_inner j (by omega))
        (cfg.apex_ne_base j j (by omega) (by omega) (by omega) (by omega))
        (cfg.apex_ne_base j (j + 1) (by omega) (by omega) (by omega) (by omega))
    · apply cfg.base_strict hgen j (by omega) (by omega) (cfg.base_inner (j + 2) (by omega) (by omega))
      · intro heq; have := cfg.base_inj (j + 2) j (by omega) (by omega) (by omega) (by omega) heq; omega
      · intro heq; have := cfg.base_inj (j + 2) (j + 1) (by omega) (by omega) (by omega) (by omega) heq; omega
    · have hh := cfg.base_strict hgen (j + 1) (by omega) (by omega) (cfg.chain_inner j (by omega))
        (cfg.apex_ne_base j (j + 1) (by omega) (by omega) (by omega) (by omega))
        (cfg.apex_ne_base j (j + 1 + 1) (by omega) (by omega) (by omega) (by omega))
      rw [turn_swap_last]
      exact neg_pos.mpr hh
    · exact hnext
    · exact hside j (by omega) hj
  · exact hlast 0 2 (by decide)

noncomputable def runPoints (S : Finset Point) (b h : ℕ → Point) (i : ℕ) : Finset Point :=
  (extremeLayer S).filter (fun x ↦ x ∈ sector ![b i, h i, b (i + 1)])

/-- The extremal both-convex pattern is impossible. A bad point at the
first end puts the second sector in the first base cap. A bad point at
the last end propagates into that same cap, giving four outer vertices. -/
theorem extremal_run_impossible {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {m : ℕ} {b h : ℕ → Point} {d : Point} (cfg : RunGeometry S m b h d)
    (hfirstQuad : 0 < turn (b 1) (h 1) (h 2) ∧ 0 < turn (b 1) (h 1) (b 2) ∧
      0 < turn (b 1) (h 2) (b 2) ∧ 0 < turn (h 1) (h 2) (b 2))
    (hlastQuad : 0 < turn (b m) (h (m - 1)) (h m) ∧
      0 < turn (b m) (h (m - 1)) (b (m + 1)) ∧
      0 < turn (b m) (h m) (b (m + 1)) ∧
      0 < turn (h (m - 1)) (h m) (b (m + 1)))
    (hdisj : ∀ i j, 1 ≤ i → i ≤ m → 1 ≤ j → j ≤ m → i ≠ j →
      Disjoint (runPoints S b h i) (runPoints S b h j))
    (hfirstCard : (runPoints S b h 1).card = 2)
    (hlastCard : (runPoints S b h m).card = 2)
    (hsecond : (runPoints S b h 2).Nonempty) : False := by
  have hm := cfg.length
  let U := runPoints S b h
  let cap := (extremeLayer S).filter (fun x ↦ 0 < turn (b 1) (b 2) x)
  have hneX {p x : Point} (hp : p ∈ inner S) (hx : x ∈ extremeLayer S) : p ≠ x :=
    fun heq ↦ (Finset.mem_sdiff.mp hp).2 (heq.symm ▸ hx)
  have hbase_ne (i j) (hi : 1 ≤ i) (him : i ≤ m + 1)
      (hj : 1 ≤ j) (hjm : j ≤ m + 1) (hij : i ≠ j) : b i ≠ b j :=
    fun heq ↦ hij (cfg.base_inj i j hi him hj hjm heq)
  have hcapCard : cap.card ≤ 3 := outer_edge_card_le_three hgen hno
    (cfg.base_inner 1 (by decide) (by omega)) (cfg.base_inner 2 (by decide) (by omega))
    (hbase_ne 1 2 (by decide) (by omega) (by decide) (by omega) (by decide))
    (cfg.base_support 1 (by decide) (by omega))
  have hgoodFirst := convex_quad_side_card_le_one hgen hno
    (cfg.base_inner 1 (by decide) (by omega)) (cfg.chain_inner 1 (by omega))
    (inner_subset _ (cfg.chain_inner 2 (by omega))) (cfg.base_inner 2 (by decide) (by omega))
    hfirstQuad.2.1 hfirstQuad.1 hfirstQuad.2.2.1 hfirstQuad.2.2.2
    (cfg.base_support 1 (by decide) (by omega)) (cfg.empty_triangle 1 (by decide) (by omega))
  have hbadFirst : ∃ x ∈ U 1, turn (h 2) (b 2) x ≤ 0 := by
    by_contra! hh
    have hsub : U 1 ⊆ (extremeLayer S).filter
        (fun x ↦ x ∈ sector ![b 1, h 1, b 2] ∧ 0 < turn (h 2) (b 2) x) := by
      intro x hx
      obtain ⟨hxA, hxS⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxA, hxS, hh x hx⟩
    have hcard := (Finset.card_le_card hsub).trans hgoodFirst
    change (runPoints S b h 1).card ≤ 1 at hcard
    omega
  obtain ⟨x, hxU, hxBad⟩ := hbadFirst
  obtain ⟨hxA, hxS⟩ := Finset.mem_filter.mp hxU
  have hxne := turn_ne_zero_of_generalPosition hgen
    (inner_subset _ (cfg.chain_inner 2 (by omega)))
    (inner_subset _ (cfg.base_inner 2 (by decide) (by omega))) (extremeLayer_subset _ hxA)
    (cfg.apex_ne_base 2 2 (by decide) (by omega) (by decide) (by omega))
    (hneX (cfg.chain_inner 2 (by omega)) hxA) (hneX (cfg.base_inner 2 (by decide) (by omega)) hxA)
  have hxBE : 0 < turn (b 2) (h 2) x := by
    rw [turn_swap_first]
    exact neg_pos.mpr (lt_of_le_of_ne hxBad hxne)
  have hxout : x ∉ sector ![b 2, h 2, b 3] := by
    intro hh
    exact Finset.disjoint_left.mp (hdisj 1 2 (by decide) (by omega) (by decide) (by omega) (by decide))
      hxU (Finset.mem_filter.mpr ⟨hxA, hh⟩)
  have hU1cap : U 1 ⊆ cap := by
    intro p hp
    obtain ⟨hpA, hpS⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hpA, hpS 0 2 (by decide)⟩
  have hU2cap : U 2 ⊆ cap := by
    intro y hy
    obtain ⟨hyA, hyS⟩ := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨hyA, ?_⟩
    apply next_sector_in_previous_cap (e := h 2) (f := b 3) (x := x)
      (inner_subset _ (cfg.base_inner 2 (by decide) (by omega)))
      (inner_subset _ (cfg.base_inner 3 (by decide) (by omega))) (extremeLayer_subset _ hxA)
      ?_ ?_ ?_ (hxS 0 2 (by decide)) hxBE hxout hyA hyS
    · exact cfg.base_strict hgen 1 (by decide) (by omega) (cfg.chain_inner 2 (by omega))
        (cfg.apex_ne_base 2 1 (by decide) (by omega) (by decide) (by omega))
        (cfg.apex_ne_base 2 2 (by decide) (by omega) (by decide) (by omega))
    · exact cfg.base_strict hgen 1 (by decide) (by omega) (cfg.base_inner 3 (by decide) (by omega))
        (hbase_ne 3 1 (by decide) (by omega) (by decide) (by omega) (by decide))
        (hbase_ne 3 2 (by decide) (by omega) (by decide) (by omega) (by decide))
    · rw [turn_swap_last]
      exact neg_pos.mpr (cfg.base_strict hgen 2 (by decide) (by omega) (cfg.chain_inner 2 (by omega))
        (cfg.apex_ne_base 2 2 (by decide) (by omega) (by decide) (by omega))
        (cfg.apex_ne_base 2 3 (by decide) (by omega) (by decide) (by omega)))
  have hd12 : Disjoint (U 1) (U 2) :=
    hdisj 1 2 (by decide) (by omega) (by decide) (by omega) (by decide)
  have hUnionCap : U 1 ∪ U 2 ⊆ cap := Finset.union_subset hU1cap hU2cap
  by_cases hm2 : m = 2
  · have hcard := (Finset.card_le_card hUnionCap).trans hcapCard
    rw [Finset.card_union_of_disjoint hd12] at hcard
    change (runPoints S b h 1).card + (runPoints S b h 2).card ≤ 3 at hcard
    rw [hm2] at hlastCard
    omega
  have hgoodLast := last_convex_quad_side_card_le_one hgen hno
    (cfg.base_inner m (by omega) (by omega)) (cfg.chain_inner m (by omega))
    (inner_subset _ (cfg.chain_inner (m - 1) (by omega)))
    (cfg.base_inner (m + 1) (by omega) le_rfl)
    hlastQuad.1 hlastQuad.2.1 hlastQuad.2.2.1 hlastQuad.2.2.2
    (cfg.base_support m (by omega) le_rfl) (cfg.empty_triangle m (by omega) le_rfl)
  have hbadLast : ∃ y ∈ U m, turn (b m) (h (m - 1)) y ≤ 0 := by
    by_contra! hh
    have hsub : U m ⊆ (extremeLayer S).filter
        (fun y ↦ y ∈ sector ![b m, h m, b (m + 1)] ∧ 0 < turn (b m) (h (m - 1)) y) := by
      intro y hy
      obtain ⟨hyA, hyS⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyA, hyS, hh y hy⟩
    have hcard := (Finset.card_le_card hsub).trans hgoodLast
    change (runPoints S b h m).card ≤ 1 at hcard
    omega
  obtain ⟨y, hyU, hyBad⟩ := hbadLast
  obtain ⟨hyA, hyS⟩ := Finset.mem_filter.mp hyU
  have hyne := turn_ne_zero_of_generalPosition hgen
    (inner_subset _ (cfg.base_inner m (by omega) (by omega)))
    (inner_subset _ (cfg.chain_inner (m - 1) (by omega))) (extremeLayer_subset _ hyA)
    (cfg.apex_ne_base (m - 1) m (by omega) (by omega) (by omega) (by omega)).symm
    (hneX (cfg.base_inner m (by omega) (by omega)) hyA) (hneX (cfg.chain_inner (m - 1) (by omega)) hyA)
  have hyout (k) (hk : 1 ≤ k) (hkm : k < m) : y ∉ sector ![b k, h k, b (k + 1)] := by
    intro hh
    exact Finset.disjoint_left.mp (hdisj m k (by omega) le_rfl hk (by omega) (by omega))
      hyU (Finset.mem_filter.mpr ⟨hyA, hh⟩)
  have hyCap : y ∈ cap := Finset.mem_filter.mpr ⟨hyA,
    last_bad_point_beyond_bases hgen cfg hyA hyS hyout
      (lt_of_le_of_ne hyBad hyne) 1 (by decide) (by omega)⟩
  have hyNot : y ∉ U 1 ∪ U 2 := by
    intro hh
    rcases Finset.mem_union.mp hh with hh | hh
    · exact Finset.disjoint_left.mp (hdisj m 1 (by omega) le_rfl (by decide) (by omega) (by omega)) hyU hh
    · exact Finset.disjoint_left.mp (hdisj m 2 (by omega) le_rfl (by decide) (by omega) (by omega)) hyU hh
  have hc := (Finset.card_le_card (Finset.insert_subset hyCap hUnionCap)).trans hcapCard
  rw [Finset.card_insert_of_notMem hyNot, Finset.card_union_of_disjoint hd12] at hc
  change (runPoints S b h 1).card + (runPoints S b h 2).card + 1 ≤ 3 at hc
  have hpos := Finset.card_pos.mpr hsecond
  omega

end Lax56Proofs.ValtrEndpointCompletion
