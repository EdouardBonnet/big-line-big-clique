import Lax56Proofs.ValtrMissing

namespace Lax56Proofs.ValtrConvexRun

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors Lax56Proofs.ValtrCyclic
open scoped Classical

theorem extreme_not_mem_triangle {S : Finset Point} {p a b c : Point}
    (hp : p ∈ extremeLayer S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) : p ∉ triangleHull a b c := by
  have hsub : ({a, b, c} : Finset Point) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  simpa only [Finset.coe_insert, Finset.coe_singleton] using
    extreme_not_mem_convexHull hp hsub (by simp [hpa, hpb, hpc])

/-- Two outer vertices in the sector of an inner triangle have a definite
order around the resulting pentagon. The remaining chord inequalities
follow from outer extremality, not from an assumed cyclic order. -/
theorem pentagon_triples_of_outer_sector_points {S : Finset Point} {a c b q r : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (htri : 0 < turn a c b) (hq : q ∈ extremeLayer S) (hr : r ∈ extremeLayer S)
    (hqS : q ∈ sector ![a, c, b]) (hrS : r ∈ sector ![a, c, b])
    (horder : 0 < turn c q r) :
    ∀ i j k : Fin 5, i < j → j < k →
      0 < turn (![a, c, b, q, r] i) (![a, c, b, q, r] j) (![a, c, b, q, r] k) := by
  have houtne {x y : Point} (hx : x ∈ extremeLayer S) (hy : y ∈ inner S) : x ≠ y := by
    intro h
    exact (Finset.mem_sdiff.mp hy).2 (h ▸ hx)
  have hqr : q ≠ r := by rintro rfl; simp at horder
  have haq : 0 < turn a c q := hqS 0 1 (by decide)
  have har : 0 < turn a c r := hrS 0 1 (by decide)
  have habq : 0 < turn a b q := hqS 0 2 (by decide)
  have habr : 0 < turn a b r := hrS 0 2 (by decide)
  have hcbq : 0 < turn c b q := hqS 1 2 (by decide)
  have hcbr : 0 < turn c b r := hrS 1 2 (by decide)
  have haqr : 0 < turn a q r := by
    by_contra hh
    apply extreme_not_mem_triangle hr (inner_subset S ha) (inner_subset S hc)
      (extremeLayer_subset S hq) (houtne hr ha) (houtne hr hc) hqr.symm
    apply weaklyInsideTriangle_mem_triangleHull haq
    refine ⟨har.le, horder.le, ?_⟩
    rw [turn_swap_first]
    exact neg_nonneg.mpr (le_of_not_gt hh)
  have hbqr : 0 < turn b q r := by
    by_contra hh
    apply extreme_not_mem_triangle hq (inner_subset S hc) (inner_subset S hb)
      (extremeLayer_subset S hr) (houtne hq hc) (houtne hq hb) hqr
    apply weaklyInsideTriangle_mem_triangleHull hcbr
    refine ⟨hcbq.le, ?_, ?_⟩
    · rw [turn_swap_last]; exact neg_nonneg.mpr (le_of_not_gt hh)
    · rw [← turn_rotate r c q]; exact horder.le
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num at hij <;> norm_num at hjk <;> assumption

private theorem pentagon_injective_of_triples {v : Fin 5 → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) :
    Function.Injective v := by
  have hne (i j : Fin 5) (hij : i < j) : v i ≠ v j := by
    intro heq
    by_cases hj : j = 4
    · subst j
      by_cases hi : i = 0
      · subst i
        have h := htri 0 1 4 (by decide) (by decide)
        rw [heq] at h
        simp at h
      · have h := htri 0 i 4 (by omega) hij
        rw [heq] at h
        simp at h
    · have h := htri i j 4 hij (by omega)
      rw [heq] at h
      simp [turn] at h
  intro i j heq
  rcases lt_trichotomy i j with h | h | h
  · exact (hne i j h heq).elim
  · exact h
  · exact (hne j i h heq.symm).elim

/-- The supporting-line calculation for the convex-quadrilateral branch
of Valtr's run induction. It identifies exactly the four-sector condition
needed to extend the pentagon. -/
theorem extension_sector_of_convex_quad {a c e b q : Point}
    (hacb : 0 < turn a c b) (hace : 0 < turn a c e)
    (haeb : 0 < turn a e b) (hceb : 0 < turn c e b)
    (hq : q ∈ sector ![a, c, b]) (hebq : 0 < turn e b q) :
    e ∈ sector ![b, q, a, c] := by
  have hacq : 0 < turn a c q := hq 0 1 (by decide)
  have habq : 0 < turn a b q := hq 0 2 (by decide)
  have haeq : 0 < turn a e q := by
    apply (mul_pos_iff_of_pos_left hacb).mp
    have hid : turn a c b * turn a e q =
        turn a e b * turn a c q + turn a c e * turn a b q := by
      unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos haeb hacq) (mul_pos hace habq)
  have hceq : 0 < turn c e q := by
    apply (mul_pos_iff_of_pos_left haeb).mp
    have hid := turn_affine_circuit a e b q c e
    simp only [turn_self_right, mul_zero, zero_add] at hid
    rw [← hid]
    have hcea : 0 < turn c e a := by rw [turn_rotate]; exact hace
    exact add_pos (mul_pos hebq hcea) (mul_pos haeq hceb)
  have h01 : 0 < turn b q e := by rw [turn_rotate]; exact hebq
  have h02 : 0 < turn b a e := by rw [← turn_rotate]; exact haeb
  have h03 : 0 < turn b c e := by rw [← turn_rotate]; exact hceb
  have h12 : 0 < turn q a e := by rw [← turn_rotate]; exact haeq
  have h13 : 0 < turn q c e := by rw [← turn_rotate]; exact hceq
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- The full ordered empty-pentagon data from an empty inner triangle
and two outer vertices in its sector. -/
theorem empty_pentagon_data_of_two_outer_sector_points {S : Finset Point}
    {a c b q r : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (hacb : 0 < turn a c b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b)
    (hq : q ∈ extremeLayer S) (hr : r ∈ extremeLayer S)
    (hqS : q ∈ sector ![a, c, b]) (hrS : r ∈ sector ![a, c, b])
    (horder : 0 < turn c q r) :
    let v : Fin 5 → Point := ![b, q, r, a, c]
    Function.Injective v ∧
      (∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) ∧
      (∀ i, v i ∈ S) ∧
      (∀ p ∈ S, p ∈ convexHull ℝ (Set.range v) → p ∈ Set.range v) := by
  let v : Fin 5 → Point := ![b, q, r, a, c]
  have htrip := pentagon_triples_of_outer_sector_points ha hc hb hacb hq hr hqS hrS horder
  have hvshift (i : Fin 5) : v i = ![a, c, b, q, r] (i + 2) := by
    fin_cases i <;> rfl
  have hvtri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
    intro i j k hij hjk
    rw [hvshift, hvshift, hvshift]
    exact cyclic_shift_triples htrip (2 : Fin 5) i j k hij hjk
  have hvinj := pentagon_injective_of_triples hvtri
  have hvmem (i : Fin 5) : v i ∈ S := by
    fin_cases i
    · exact inner_subset S hb
    · exact extremeLayer_subset S hq
    · exact extremeLayer_subset S hr
    · exact inner_subset S ha
    · exact inner_subset S hc
  have hvempty : ∀ p ∈ S, p ∈ convexHull ℝ (Set.range v) → p ∈ Set.range v := by
    intro p hp hpHull
    by_cases hpouter : p ∈ extremeLayer S
    · by_contra hpnot
      have hsub : Finset.univ.image v ⊆ S := by
        intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        exact hvmem i
      have hpnot' : p ∉ Finset.univ.image v := by simpa using hpnot
      exact extreme_not_mem_convexHull hpouter hsub hpnot' (by simpa using hpHull)
    have hpinner : p ∈ inner S := Finset.mem_sdiff.mpr ⟨hp, hpouter⟩
    have hside₁ : 0 ≤ turn a c p := by
      apply turn_nonneg_of_mem_convexHull (A := Set.range v) _ hpHull
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact hacb.le
      · exact (hqS 0 1 (by decide)).le
      · exact (hrS 0 1 (by decide)).le
      · simp [v]
      · simp [v]
    have hside₂ : 0 ≤ turn c b p := by
      apply turn_nonneg_of_mem_convexHull (A := Set.range v) _ hpHull
      rintro x ⟨i, rfl⟩
      fin_cases i
      · simp [v]
      · exact (hqS 1 2 (by decide)).le
      · exact (hrS 1 2 (by decide)).le
      · change 0 ≤ turn c b a
        rw [turn_rotate]; exact hacb.le
      · simp [v]
    have hpTri : p ∈ triangleHull a c b := by
      apply weaklyInsideTriangle_mem_triangleHull hacb
      refine ⟨hside₁, hside₂, ?_⟩
      rw [turn_swap_first]
      exact neg_nonneg.mpr (hbase p hpinner)
    rcases hempty p hpinner hpTri with h | h | h
    · exact ⟨3, h.symm⟩
    · exact ⟨4, h.symm⟩
    · exact ⟨0, h.symm⟩
  exact ⟨hvinj, hvtri, hvmem, hvempty⟩

/-- The empty-pentagon obstruction in the convex endpoint branch, with
the separating-side condition stated explicitly. -/
theorem emptyHexagon_of_two_outer_points_of_convex_quad {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {a c e b q r : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (he : e ∈ S) (hb : b ∈ inner S)
    (hacb : 0 < turn a c b) (hace : 0 < turn a c e)
    (haeb : 0 < turn a e b) (hceb : 0 < turn c e b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b)
    (hq : q ∈ extremeLayer S) (hr : r ∈ extremeLayer S)
    (hqS : q ∈ sector ![a, c, b]) (hrS : r ∈ sector ![a, c, b])
    (horder : 0 < turn c q r) (hebq : 0 < turn e b q) : HasEmptyHexagon S := by
  obtain ⟨hinj, htri, hmem, hEmpty⟩ := empty_pentagon_data_of_two_outer_sector_points
    ha hc hb hacb hbase hempty hq hr hqS hrS horder
  exact empty_pentagon_extension hgen ![b, q, r, a, c] hinj htri hmem he hEmpty
    (extension_sector_of_convex_quad hacb hace haeb hceb hqS hebq)

/-- In the convex endpoint configuration, at most one outer vertex lies
in the first sector on the indicated side of the next apex's line.
Relating that side condition to exclusion from an entire sector run is a
separate geometric obligation. -/
theorem convex_quad_side_card_le_one {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S) {a c e b : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (he : e ∈ S) (hb : b ∈ inner S)
    (hacb : 0 < turn a c b) (hace : 0 < turn a c e)
    (haeb : 0 < turn a e b) (hceb : 0 < turn c e b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b) :
    ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b] ∧ 0 < turn e b p)).card ≤ 1 := by
  classical
  by_contra hh
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp (lt_of_not_ge hh)
  obtain ⟨hq, hqS, hqb⟩ := Finset.mem_filter.mp hq
  obtain ⟨hr, hrS, hrb⟩ := Finset.mem_filter.mp hr
  have hcq : c ≠ q := by
    intro h
    exact (Finset.mem_sdiff.mp hc).2 (h.symm ▸ hq)
  have hcr : c ≠ r := by
    intro h
    exact (Finset.mem_sdiff.mp hc).2 (h.symm ▸ hr)
  have hne := turn_ne_zero_of_generalPosition hgen (inner_subset S hc)
    (extremeLayer_subset S hq) (extremeLayer_subset S hr) hcq hcr hqr
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < turn c r q := by rw [turn_swap_last]; exact neg_pos.mpr hneg
    exact hno (emptyHexagon_of_two_outer_points_of_convex_quad hgen ha hc he hb
      hacb hace haeb hceb hbase hempty hr hq hrS hqS hpos' hrb)
  · exact hno (emptyHexagon_of_two_outer_points_of_convex_quad hgen ha hc he hb
      hacb hace haeb hceb hbase hempty hq hr hqS hrS hpos hqb)

/-- The mirrored four-sector calculation for a convex last endpoint.
The required side test is now `turn a e r > 0`. -/
theorem extension_sector_of_last_convex_quad {a c e b r : Point}
    (haec : 0 < turn a e c) (haeb : 0 < turn a e b)
    (hacb : 0 < turn a c b) (hecb : 0 < turn e c b)
    (hr : r ∈ sector ![a, c, b]) (haer : 0 < turn a e r) :
    e ∈ sector ![c, b, r, a] := by
  have hebr : 0 < turn e b r := by
    apply (mul_pos_iff_of_pos_left hacb).mp
    have hid : turn a c b * turn e b r =
        turn a e b * turn c b r + turn e c b * turn a b r := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos haeb (hr 1 2 (by decide))) (mul_pos hecb (hr 0 2 (by decide)))
  have hecr : 0 < turn e c r := by
    apply (mul_pos_iff_of_pos_left hacb).mp
    have hid : turn a c b * turn e c r =
        turn a e c * turn c b r + turn e c b * turn a c r := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos haec (hr 1 2 (by decide))) (mul_pos hecb (hr 0 1 (by decide)))
  have h01 : 0 < turn c b e := by rw [turn_rotate]; exact hecb
  have h02 : 0 < turn c r e := by rw [turn_rotate]; exact hecr
  have h03 : 0 < turn c a e := by rw [← turn_rotate]; exact haec
  have h12 : 0 < turn b r e := by rw [turn_rotate]; exact hebr
  have h13 : 0 < turn b a e := by rw [← turn_rotate]; exact haeb
  have h23 : 0 < turn r a e := by rw [← turn_rotate]; exact haer
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

theorem emptyHexagon_of_two_outer_points_of_last_convex_quad {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {a c e b q r : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (he : e ∈ S) (hb : b ∈ inner S)
    (haec : 0 < turn a e c) (haeb : 0 < turn a e b)
    (hacb : 0 < turn a c b) (hecb : 0 < turn e c b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b)
    (hq : q ∈ extremeLayer S) (hr : r ∈ extremeLayer S)
    (hqS : q ∈ sector ![a, c, b]) (hrS : r ∈ sector ![a, c, b])
    (horder : 0 < turn c q r) (haer : 0 < turn a e r) : HasEmptyHexagon S := by
  obtain ⟨hinj, htri, hmem, hEmpty⟩ := empty_pentagon_data_of_two_outer_sector_points
    ha hc hb hacb hbase hempty hq hr hqS hrS horder
  let v : Fin 5 → Point := ![c, b, q, r, a]
  have hshift (i : Fin 5) : v i = ![b, q, r, a, c] (i + 4) := by fin_cases i <;> rfl
  have hinj' : Function.Injective v := by
    intro i j hh
    rw [hshift, hshift] at hh
    exact add_right_cancel (hinj hh)
  have htri' : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
    intro i j k hij hjk
    rw [hshift, hshift, hshift]
    exact cyclic_shift_triples htri (4 : Fin 5) i j k hij hjk
  have hrange : Set.range v = Set.range ![b, q, r, a, c] := by
    ext p
    simp only [Set.mem_range]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i + 4, (hshift i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i - 4, ?_⟩
      rw [hshift, sub_add_cancel]
  apply empty_pentagon_extension hgen v hinj' htri'
    (fun i ↦ by rw [hshift]; exact hmem _) he
  · intro p hp hph
    rw [hrange] at hph ⊢
    exact hEmpty p hp hph
  · exact extension_sector_of_last_convex_quad haec haeb hacb hecb hrS haer

theorem last_convex_quad_side_card_le_one {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S) {a c e b : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (he : e ∈ S) (hb : b ∈ inner S)
    (haec : 0 < turn a e c) (haeb : 0 < turn a e b)
    (hacb : 0 < turn a c b) (hecb : 0 < turn e c b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b) :
    ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b] ∧ 0 < turn a e p)).card ≤ 1 := by
  by_contra hh
  obtain ⟨q, hq, r, hr, hqr⟩ := Finset.one_lt_card.mp (lt_of_not_ge hh)
  obtain ⟨hq, hqS, hqb⟩ := Finset.mem_filter.mp hq
  obtain ⟨hr, hrS, hrb⟩ := Finset.mem_filter.mp hr
  have hcq : c ≠ q := fun hh ↦ (Finset.mem_sdiff.mp hc).2 (hh.symm ▸ hq)
  have hcr : c ≠ r := fun hh ↦ (Finset.mem_sdiff.mp hc).2 (hh.symm ▸ hr)
  have hne := turn_ne_zero_of_generalPosition hgen (inner_subset _ hc)
    (extremeLayer_subset _ hq) (extremeLayer_subset _ hr) hcq hcr hqr
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < turn c r q := by rw [turn_swap_last]; exact neg_pos.mpr hneg
    exact hno (emptyHexagon_of_two_outer_points_of_last_convex_quad hgen ha hc he hb
      haec haeb hacb hecb hbase hempty hr hq hrS hqS hpos' hqb)
  · exact hno (emptyHexagon_of_two_outer_points_of_last_convex_quad hgen ha hc he hb
      haec haeb hacb hecb hbase hempty hq hr hqS hrS hpos hrb)

end Lax56Proofs.ValtrConvexRun
