import Lax56Proofs.ValtrSectorSetup
import Mathlib.Analysis.Convex.PathConnected

namespace Lax56Proofs.ValtrMissing

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrCaps Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors
open Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrSelection Lax56Proofs.ValtrSectorSetup
open Lax56Proofs.ValtrSectorBounds
open scoped Classical

theorem isOpen_sector {n : ℕ} (v : Fin n → Point) : IsOpen (sector v) := by
  have heq : sector v = ⋂ i, ⋂ j, ⋂ (_ : i < j),
      {q | 0 < turn (v i) (v j) q} := by ext q; simp [sector]
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _
  apply isOpen_lt continuous_const
  unfold turn
  fun_prop

/-- The open radial sectors of a strict convex polygon are pairwise
disjoint. The test point need not belong to the finite ambient set. -/
theorem radial_sector_unique {n : ℕ} [NeZero n] {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d q : Point} {i j : Fin n}
    (hi : q ∈ sector ![v (i + 1), d, v i])
    (hj : q ∈ sector ![v (j + 1), d, v j]) : i = j := by
  apply cyclic_line_crossing_unique htri (u := q) (w := d)
  · simpa only [turn_rotate] using hi 1 2 (by decide)
  · have h := hi 0 1 (by decide)
    change 0 < turn (v (i + 1)) d q at h
    rw [turn_swap_first] at h
    have hneg : turn d (v (i + 1)) q < 0 := by linarith
    convert hneg using 1 <;> unfold turn <;> ring
  · simpa only [turn_rotate] using hj 1 2 (by decide)
  · have h := hj 0 1 (by decide)
    change 0 < turn (v (j + 1)) d q at h
    rw [turn_swap_first] at h
    have hneg : turn d (v (j + 1)) q < 0 := by linarith
    convert hneg using 1 <;> unfold turn <;> ring

private theorem turn_zero_trans {d q a b : Point} (hdq : d ≠ q)
    (ha : turn d q a = 0) (hb : turn d q b = 0) : turn d a b = 0 := by
  have hx : turn d a b * (q.1 - d.1) =
      turn d q b * (a.1 - d.1) - turn d q a * (b.1 - d.1) := by
    unfold turn; ring
  have hy : turn d a b * (q.2 - d.2) =
      turn d q b * (a.2 - d.2) - turn d q a * (b.2 - d.2) := by
    unfold turn; ring
  rw [ha, hb, zero_mul, zero_mul, sub_self] at hx hy
  by_cases h : turn d a b = 0
  · exact h
  · have hx' := (mul_eq_zero.mp hx).resolve_left h
    have hy' := (mul_eq_zero.mp hy).resolve_left h
    exact (hdq (Prod.ext (sub_eq_zero.mp hx').symm (sub_eq_zero.mp hy').symm)).elim

/-- The radial fan covers any exterior point whose segment from the
interior point does not pass through a polygon vertex. This strengthened
version permits the exterior point to move continuously along another
polygon's edge, so general position cannot be assumed for that point. -/
theorem exists_radial_sector_of_no_vertex_on_ray {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hmem : ∀ i, v i ∈ P) {d q : Point} (hdP : d ∈ P)
    (hdHull : d ∈ convexHull ℝ (Set.range v)) (hdnot : d ∉ Set.range v)
    (hqout : q ∉ convexHull ℝ (Set.range v))
    (hray : ∀ i, v i ∉ segment ℝ d q) :
    ∃ i, q ∈ sector ![v (i + 1), d, v i] := by
  classical
  let C := Finset.univ.image v
  have hC : (C : Set Point) = Set.range v := by simp [C]
  have hdq : d ≠ q := by rintro rfl; exact hqout hdHull
  have hvd (i) : v i ≠ d := fun h ↦ hdnot ⟨i, h⟩
  let f : Point →ᵃ[ℝ] ℝ := -turnAffine d q
  have hf (p) : f p = turn d p q := by
    change -turn d q p = turn d p q
    rw [turn_swap_last d p q]
    exact neg_neg _
  have hzero : ∀ a ∈ C, ∀ b ∈ C, f a = 0 → f b = 0 → a = b := by
    intro a ha b hb hfa hfb
    obtain ⟨i, rfl⟩ := hC ▸ (show a ∈ (C : Set Point) from ha)
    obtain ⟨j, rfl⟩ := hC ▸ (show b ∈ (C : Set Point) from hb)
    by_contra hij
    have hz := turn_zero_trans hdq
      (a := v i) (b := v j) (by change -turn d q (v i) = 0 at hfa; linarith)
      (by change -turn d q (v j) = 0 at hfb; linarith)
    exact turn_ne_zero_of_generalPosition hgen hdP (hmem i) (hmem j)
      (hvd i).symm (hvd j).symm hij hz
  have hdC : d ∈ convexHull ℝ (C : Set Point) := hC ▸ hdHull
  have hdnotC : d ∉ C := by change d ∉ (C : Set Point); rwa [hC]
  have hfd : f d = 0 := by rw [hf]; simp [turn]
  obtain ⟨a, ha, hapos⟩ := exists_positive_of_nonvertex_zero hdC hdnotC f hfd hzero
  obtain ⟨b, hb, hbneg⟩ := exists_negative_of_nonvertex_zero hdC hdnotC f hfd hzero
  obtain ⟨ia, rfl⟩ := hC ▸ (show a ∈ (C : Set Point) from ha)
  obtain ⟨ib, rfl⟩ := hC ▸ (show b ∈ (C : Set Point) from hb)
  rw [hf] at hapos hbneg
  obtain ⟨i, hipos, hinot⟩ := exists_cyclic_transition
    (fun i ↦ 0 < turn d (v i) q) ⟨ia, hapos⟩ ⟨ib, not_lt.mpr hbneg.le⟩
  have hinside : 0 < turn d (v i) (v (i + 1)) := by
    rw [← turn_rotate d (v i) (v (i + 1))]
    exact cyclic_edge_strict_of_mem_hull hgen hn v hinj htri hmem hdP hdHull hdnot i
  have hinonzero : turn d (v (i + 1)) q ≠ 0 := by
    intro hz
    have hcol : Collinear ℝ ({d, v (i + 1), q} : Set Point) := by
      have h := collinear_insert_of_mem_affineSpan_pair
        (mem_line_of_turn_eq_zero (hvd (i + 1)).symm hz)
      convert h using 1
      ext p; simp [or_comm, or_left_comm]
    rcases hcol.wbtw_or_wbtw_or_wbtw with h | h | h
    · exact hray (i + 1) h.mem_segment
    · exact hqout ((convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (Set.mem_range_self (i + 1))) hdHull h.mem_segment)
    · have hseg : segment ℝ q (v (i + 1)) ⊆
          (turnAffine d (v i)) ⁻¹' Set.Ioi 0 :=
        ((convex_Ioi (0 : ℝ)).affine_preimage (turnAffine d (v i))).segment_subset
          hipos hinside
      have hh := hseg h.mem_segment
      change 0 < turn d (v i) d at hh
      simpa using hh
  have hineg := lt_of_le_of_ne (le_of_not_gt hinot) hinonzero
  have hedge : turn (v i) (v (i + 1)) q < 0 := by
    by_contra h
    have hqT : q ∈ triangleHull d (v i) (v (i + 1)) := by
      apply weaklyInsideTriangle_mem_triangleHull hinside
      refine ⟨hipos.le, le_of_not_gt h, ?_⟩
      rw [turn_swap_first]
      exact (neg_pos.mpr hineg).le
    exact hqout (triangleHull_subset_of_mem (convex_convexHull ℝ _) hdHull
      (subset_convexHull ℝ _ (Set.mem_range_self i))
      (subset_convexHull ℝ _ (Set.mem_range_self (i + 1))) hqT)
  refine ⟨i, ?_⟩
  have h01 : 0 < turn (v (i + 1)) d q := by
    rw [turn_swap_first]; exact neg_pos.mpr hineg
  have h02 : 0 < turn (v (i + 1)) (v i) q := by
    rw [turn_swap_first]; exact neg_pos.mpr hedge
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk <;> assumption

/-- A connected set covered by disjoint open radial sectors lies entirely
in one sector. This is the continuity step behind the unique-edge claim. -/
theorem preconnected_subset_radial_sector {n : ℕ} [NeZero n]
    {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} {T : Set Point} (hne : T.Nonempty) (hconn : IsPreconnected T)
    (hcover : ∀ q ∈ T, ∃ i, q ∈ sector ![v (i + 1), d, v i]) :
    ∃ i, T ⊆ sector ![v (i + 1), d, v i] := by
  classical
  obtain ⟨q₀, hq₀⟩ := hne
  obtain ⟨i, hi⟩ := hcover q₀ hq₀
  let W := ⋃ (j : Fin n) (_ : j ≠ i), sector ![v (j + 1), d, v j]
  have hWopen : IsOpen W := isOpen_iUnion (fun _ ↦ isOpen_iUnion (fun _ ↦ isOpen_sector _))
  have hdis : Disjoint (sector ![v (i + 1), d, v i]) W := by
    apply Set.disjoint_left.mpr
    intro q hqi hqW
    obtain ⟨j, hji, hqj⟩ := Set.mem_iUnion.mp hqW |>.imp fun j hj ↦ Set.mem_iUnion.mp hj
    exact hji (radial_sector_unique htri hqj hqi)
  have hcov : T ⊆ sector ![v (i + 1), d, v i] ∪ W := by
    intro q hq
    obtain ⟨j, hj⟩ := hcover q hq
    by_cases hji : j = i
    · exact Or.inl (hji ▸ hj)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hji, hj⟩⟩)
  exact ⟨i, hconn.subset_left_of_subset_union (isOpen_sector _) hWopen hdis hcov
    ⟨q₀, hq₀, hi⟩⟩

/-- If an outer edge's radial triangle misses every inner-polygon vertex,
then that entire edge is behind one inner-polygon edge as viewed from `d`.
In particular both outer endpoints belong to the same radial sector. -/
theorem segment_subset_radial_sector_of_empty_triangle {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hmem : ∀ i, v i ∈ P) {d a b : Point} (hdP : d ∈ P)
    (hdHull : d ∈ convexHull ℝ (Set.range v)) (hdnot : d ∉ Set.range v)
    (hsupport : ∀ i, 0 < turn a b (v i))
    (hempty : ∀ i, v i ∉ triangleHull d a b) :
    ∃ i, segment ℝ a b ⊆ sector ![v (i + 1), d, v i] := by
  apply preconnected_subset_radial_sector htri
    ⟨a, left_mem_segment ℝ a b⟩ (convex_segment a b).isPreconnected
  intro q hq
  apply exists_radial_sector_of_no_vertex_on_ray hgen hn v hinj htri hmem hdP hdHull hdnot
  · intro hqHull
    have hpos : 0 < turn a b q := by
      apply convexHull_min (t := (turnAffine a b) ⁻¹' Set.Ioi 0) _
        ((convex_Ioi (0 : ℝ)).affine_preimage (turnAffine a b)) hqHull
      rintro p ⟨i, rfl⟩
      exact hsupport i
    have hsegzero : segment ℝ a b ⊆ (turnAffine a b) ⁻¹' ({0} : Set ℝ) :=
      ((convex_singleton (0 : ℝ)).affine_preimage (turnAffine a b)).segment_subset
        (by change turn a b a = 0; simp) (by change turn a b b = 0; simp)
    have hz : turn a b q = 0 := hsegzero hq
    exact hpos.ne' hz
  · intro i hi
    apply hempty i
    have hT : Convex ℝ (triangleHull d a b) := convex_convexHull ℝ _
    have ha : a ∈ triangleHull d a b := subset_convexHull ℝ _ (by simp)
    have hb : b ∈ triangleHull d a b := subset_convexHull ℝ _ (by simp)
    exact hT.segment_subset (vertex_mem_triangleHull d a b)
      (hT.segment_subset ha hb hq) hi

/-- The two-outer-vertices bound also holds for a radial sector with an
arbitrary inner apex. Moving that apex to an empty triangle on the same
supporting base only enlarges the sector. -/
theorem outer_radial_sector_card_le_two {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) (hno : ¬HasEmptyHexagon Q) {a b d : Point}
    (ha : a ∈ inner Q) (hb : b ∈ inner Q) (hd : d ∈ inner Q)
    (htri : 0 < turn a b d) (hbase : ∀ p ∈ inner Q, 0 ≤ turn a b p) :
    ((extremeLayer Q).filter (fun p ↦ p ∈ sector ![b, d, a])).card ≤ 2 := by
  classical
  have hgenI : ¬HasThreeCollinear (inner Q) :=
    fun h ↦ hgen (hasThreeCollinear_mono (inner_subset Q) h)
  obtain ⟨r, hr, hrT, hrpos, hrempty⟩ :=
    exists_empty_triangle_on_base hgenI hd ha hb htri
  have hra : r ≠ a := by rintro rfl; simp at hrpos
  have hrb : r ≠ b := by rintro rfl; simp at hrpos
  have hsector : sector ![b, d, a] ⊆ sector ![b, r, a] :=
    sector_triangle_mono (by rwa [triangleHull_swap_last]) hrb hra
  have hrtri : 0 < turn b r a := by
    rw [turn_rotate a b r]
    exact hrpos
  have hbound := outer_sector_card_le_two hgen hno hb hr ha hrtri
    (fun p hp ↦ by rw [turn_swap_first]; exact neg_nonpos.mpr (hbase p hp))
    (fun p hp hpt ↦ by
      have hp' : p ∈ triangleHull r a b := by rwa [triangleHull_rotate]
      rcases hrempty p hp hp' with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h)
  apply (Finset.card_le_card ?_).trans hbound
  intro p hp
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
    hsector (Finset.mem_filter.mp hp).2⟩

/-- Two adjacent outer-edge triangles cannot both miss the next layer.
The unique-edge step is derived from connectedness, and the hexagon
contradiction uses the already verified empty-triangle sector bound. -/
theorem meets_inner_vertex_of_two_adjacent_triangles {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) (hno : ¬HasEmptyHexagon Q)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (v : Fin n → Point)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner Q) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d a b c : Point} (hd : d ∈ inner (inner Q))
    (ha : a ∈ extremeLayer Q) (hb : b ∈ extremeLayer Q) (hc : c ∈ extremeLayer Q)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hsupport₁ : ∀ p ∈ inner Q, 0 < turn a b p)
    (hsupport₂ : ∀ p ∈ inner Q, 0 < turn b c p) :
    ∃ r ∈ extremeLayer (inner Q),
      r ∈ triangleHull d a b ∨ r ∈ triangleHull d b c := by
  classical
  have hvC (i) : v i ∈ extremeLayer (inner Q) := by
    change v i ∈ (extremeLayer (inner Q) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hvI (i) : v i ∈ inner Q := extremeLayer_subset _ (hvC i)
  have hvQ (i) : v i ∈ Q := inner_subset _ (hvI i)
  have hdI : d ∈ inner Q := inner_subset _ hd
  have hdQ : d ∈ Q := inner_subset _ hdI
  have hdHull : d ∈ convexHull ℝ (Set.range v) := by
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hdI
  have hdnot : d ∉ Set.range v := by
    rw [hrange]
    exact (Finset.mem_sdiff.mp hd).2
  by_contra h
  have hmiss₁ (i) : v i ∉ triangleHull d a b :=
    fun ht ↦ h ⟨v i, hvC i, Or.inl ht⟩
  have hmiss₂ (i) : v i ∉ triangleHull d b c :=
    fun ht ↦ h ⟨v i, hvC i, Or.inr ht⟩
  obtain ⟨i, hi⟩ := segment_subset_radial_sector_of_empty_triangle hgen hn v hinj htri
    hvQ hdQ hdHull hdnot (fun i ↦ hsupport₁ _ (hvI i)) hmiss₁
  obtain ⟨j, hj⟩ := segment_subset_radial_sector_of_empty_triangle hgen hn v hinj htri
    hvQ hdQ hdHull hdnot (fun i ↦ hsupport₂ _ (hvI i)) hmiss₂
  have hij : j = i := radial_sector_unique htri
    (hj (left_mem_segment ℝ b c)) (hi (right_mem_segment ℝ a b))
  subst j
  have hdi : 0 < turn (v i) (v (i + 1)) d :=
    cyclic_edge_strict_of_mem_hull hgen hn v hinj htri hvQ hdQ hdHull hdnot i
  have hbase : ∀ p ∈ inner Q, 0 ≤ turn (v i) (v (i + 1)) p := by
    intro p hp
    apply cyclic_edge_nonneg_of_mem_hull htri _ i
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hp
  have hbound := outer_radial_sector_card_le_two hgen hno
    (hvI i) (hvI (i + 1)) hdI hdi hbase
  have hsub : ({a, b, c} : Finset Point) ⊆ (extremeLayer Q).filter
      (fun p ↦ p ∈ sector ![v (i + 1), d, v i]) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨ha, hi (left_mem_segment ℝ _ _)⟩
    · exact Finset.mem_filter.mpr ⟨hb, hi (right_mem_segment ℝ _ _)⟩
    · exact Finset.mem_filter.mpr ⟨hc, hj (right_mem_segment ℝ _ _)⟩
  have hthree : 3 ≤ ((extremeLayer Q).filter
      (fun p ↦ p ∈ sector ![v (i + 1), d, v i])).card := by
    simpa [hab, hac, hbc] using Finset.card_le_card hsub
  omega

/-- Valtr's Observation 3, stated directly for the second-layer cycle:
at least one of every two consecutive apices is defined. -/
theorem meetsThirdLayer_or_next {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (v : Fin n → Point)
    (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (i : Fin n) :
    MeetsThirdLayer S v d i ∨ MeetsThirdLayer S v d (i + 1) := by
  let Q := inner S
  have hgenQ : ¬HasThreeCollinear Q :=
    fun h ↦ hgen (hasThreeCollinear_mono (inner_subset S) h)
  have hnoQ : ¬HasEmptyHexagon Q :=
    fun h ↦ hno (hasEmptyHexagon_transfer (inner_hullClosedIn S) h)
  have hgenI : ¬HasThreeCollinear (inner Q) :=
    fun h ↦ hgenQ (hasThreeCollinear_mono (inner_subset Q) h)
  let C := extremeLayer (inner Q)
  have hcard : 3 ≤ C.card := three_le_outer_card_of_inner_nonempty hgenI ⟨d, hd⟩
  letI : NeZero C.card := ⟨by omega⟩
  have hgenC : ¬HasThreeCollinear C :=
    fun h ↦ hgenI (hasThreeCollinear_mono (extremeLayer_subset (inner Q)) h)
  obtain ⟨u, huinj, hurange, hutri⟩ := Lax56Proofs.CyclicOrder.exists_cyclic_order_card C
    (Finset.card_pos.mp (by omega)) (extremeLayer_convexPosition (inner Q)) hgenC
  have hvB (j) : v j ∈ extremeLayer Q := by
    change v j ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self j
  have hvQ (j) : v j ∈ Q := extremeLayer_subset Q (hvB j)
  have hsupp (j) : ∀ p ∈ inner Q, 0 < turn (v j) (v (j + 1)) p := by
    intro p hp
    apply cyclic_edge_strict_of_mem_hull hgenQ (by omega) v hinj htri hvQ
      (inner_subset Q hp) _ _ j
    · rw [hrange, convexHull_extremeLayer]
      exact subset_convexHull ℝ _ (inner_subset Q hp)
    · rw [hrange]
      exact (Finset.mem_sdiff.mp hp).2
  have hnext (j : Fin n) : j ≠ j + 1 := by
    intro h
    have hnxt := cyclic_next_cases j
    have hv := congrArg Fin.val h
    omega
  have htwo : i ≠ (i + 1) + 1 := by
    intro h
    have hnxt := cyclic_next_cases i
    have hnxt' := cyclic_next_cases (i + 1)
    have hv := congrArg Fin.val h
    omega
  obtain ⟨r, hr, ht | ht⟩ := meets_inner_vertex_of_two_adjacent_triangles hgenQ hnoQ
    (by omega) u huinj hurange hutri hd (hvB i) (hvB (i + 1)) (hvB ((i + 1) + 1))
    (hinj.ne (hnext i)) (hinj.ne htwo) (hinj.ne (hnext (i + 1))) (hsupp i) (hsupp (i + 1))
  · exact Or.inl ⟨r, hr, ht⟩
  · exact Or.inr ⟨r, hr, ht⟩

end Lax56Proofs.ValtrMissing
