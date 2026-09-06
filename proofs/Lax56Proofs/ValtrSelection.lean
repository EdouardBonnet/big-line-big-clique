import Lax56Proofs.ValtrPolygon
import Mathlib.Analysis.LocallyConvex.Separation

namespace Lax56Proofs.ValtrSelection

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors Lax56Proofs.ValtrPolygon
open scoped BigOperators

/-- A linear functional uniquely minimized at a finite generator is
strictly larger at every other point of the convex hull. -/
theorem linear_support_strict_on_hull {C : Finset Point} {r p : Point}
    (hr : r ∈ C) (l : Point →ₗ[ℝ] ℝ)
    (hs : ∀ q ∈ C, q ≠ r → l r < l q)
    (hp : p ∈ convexHull ℝ (C : Set Point)) (hpr : p ≠ r) : l r < l p := by
  classical
  obtain ⟨w, hw0, hw1, hwcenter⟩ := (Finset.mem_convexHull').mp hp
  have hnonneg (q) (hq : q ∈ C) : 0 ≤ l q - l r := by
    by_cases hqr : q = r
    · simp [hqr]
    · exact (sub_pos.mpr (hs q hq hqr)).le
  have hsum : ∑ q ∈ C, w q * (l q - l r) = l p - l r := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    congr 1
    rw [← hwcenter, map_sum]
    simp
  have hweight (q) (hq : q ∈ C) : 0 ≤ w q * (l q - l r) :=
    mul_nonneg (hw0 q hq) (hnonneg q hq)
  by_contra h
  have hz : ∑ q ∈ C, w q * (l q - l r) = 0 := by
    have := Finset.sum_nonneg hweight
    rw [hsum] at this ⊢
    linarith
  have hwother (q) (hq : q ∈ C) (hqr : q ≠ r) : w q = 0 := by
    have heq := (Finset.sum_eq_zero_iff_of_nonneg hweight).mp hz q hq
    exact (mul_eq_zero.mp heq).resolve_right (sub_pos.mpr (hs q hq hqr)).ne'
  have hwr : w r = 1 := by
    rw [← hw1]
    symm
    exact Finset.sum_eq_single r (fun q hq hqr ↦ hwother q hq hqr)
      (fun h ↦ (h hr).elim)
  apply hpr
  calc
    p = ∑ q ∈ C, w q • q := hwcenter.symm
    _ = w r • r := by
      apply Finset.sum_eq_single r
      · intro q hq hqr
        rw [hwother q hq hqr, zero_smul]
      · exact fun h ↦ (h hr).elim
    _ = r := by rw [hwr, one_smul]

/-- Every vertex of a finite convex-position set has a strict supporting
linear functional. The separation theorem is applied to the closed hull
of the other vertices, whose exclusion is the definition of a vertex. -/
theorem exists_strict_linear_support {C : Finset Point} (hC : ConvexPosition C)
    {r : Point} (hr : r ∈ C) :
    ∃ l : Point →ₗ[ℝ] ℝ, ∀ q ∈ C, q ≠ r → l r < l q := by
  classical
  have hnot : r ∉ convexHull ℝ (C.erase r : Set Point) := by
    simpa only [Finset.coe_erase] using (convexPosition_iff C).mp hC r hr
  obtain ⟨l, u, hru, hu⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (C.erase r : Set Point))
    ((C.erase r).finite_toSet.isClosed_convexHull ℝ) hnot
  refine ⟨l.toLinearMap, ?_⟩
  intro q hq hqr
  exact hru.trans (hu q (subset_convexHull ℝ _ (Finset.mem_erase.mpr ⟨hqr, hq⟩)))

/-- Barycentric evaluation about `r`, without any denominators. -/
theorem linear_triangle_identity (l : Point →ₗ[ℝ] ℝ) (a r b q : Point) :
    turn a r b * (l q - l r) =
      turn r b q * (l a - l r) + turn a r q * (l b - l r) := by
  have hv : turn a r b • (q - r) =
      turn r b q • (a - r) + turn a r q • (b - r) := by
    apply Prod.ext <;> simp [turn] <;> ring
  have h := congrArg l hv
  simpa only [map_smul, map_add, map_sub, RingHom.id_apply, smul_eq_mul] using h

theorem affine_support_strict_on_hull {C : Finset Point} {r p : Point}
    (hr : r ∈ C) (f : Point →ᵃ[ℝ] ℝ)
    (hs : ∀ q ∈ C, q ≠ r → f r < f q)
    (hp : p ∈ convexHull ℝ (C : Set Point)) (hpr : p ≠ r) : f r < f p := by
  have hid (q : Point) : f.linear q - f.linear r = f q - f r := by
    simpa only [vsub_eq_sub, map_sub] using f.linearMap_vsub q r
  have h := linear_support_strict_on_hull hr f.linear
    (fun q hq hqr ↦ by have := hid q; have := hs q hq hqr; linarith) hp hpr
  have := hid p
  linarith

/-- An affine line through a nonvertex hull point has a positive generator
if at most one generator lies on the line. Unlike general-position lemmas
about ambient points, this also applies to continuously moving test lines. -/
theorem exists_positive_of_nonvertex_zero {C : Finset Point} {d : Point}
    (hd : d ∈ convexHull ℝ (C : Set Point)) (hdnot : d ∉ C)
    (f : Point →ᵃ[ℝ] ℝ) (hfd : f d = 0)
    (hzero : ∀ a ∈ C, ∀ b ∈ C, f a = 0 → f b = 0 → a = b) :
    ∃ a ∈ C, 0 < f a := by
  classical
  by_contra h
  push Not at h
  by_cases hz : ∃ r ∈ C, f r = 0
  · obtain ⟨r, hr, hfr⟩ := hz
    have hstrict : ∀ q ∈ C, q ≠ r → (-f) r < (-f) q := by
      intro q hq hqr
      have hqf : f q < 0 := lt_of_le_of_ne (h q hq)
        (fun hh ↦ hqr (hzero q hq r hr hh hfr))
      change -f r < -f q
      rw [hfr]
      linarith
    have hp := affine_support_strict_on_hull hr (-f) hstrict hd
      (fun hh ↦ hdnot (hh.symm ▸ hr))
    change -f r < -f d at hp
    rw [hfr, hfd] at hp
    norm_num at hp
  · have hnegative : ∀ q ∈ C, f q < 0 := by
      intro q hq
      exact lt_of_le_of_ne (h q hq) (fun hh ↦ hz ⟨q, hq, hh⟩)
    have hp := convexHull_min hnegative ((convex_Iio (0 : ℝ)).affine_preimage f) hd
    change f d < 0 at hp
    rw [hfd] at hp
    exact (lt_irrefl _ hp)

theorem exists_negative_of_nonvertex_zero {C : Finset Point} {d : Point}
    (hd : d ∈ convexHull ℝ (C : Set Point)) (hdnot : d ∉ C)
    (f : Point →ᵃ[ℝ] ℝ) (hfd : f d = 0)
    (hzero : ∀ a ∈ C, ∀ b ∈ C, f a = 0 → f b = 0 → a = b) :
    ∃ a ∈ C, f a < 0 := by
  obtain ⟨a, ha, hfa⟩ := exists_positive_of_nonvertex_zero hd hdnot (-f)
    (by change -f d = 0; rw [hfd]; ring)
    (fun a ha b hb hfa hfb ↦ hzero a ha b hb (by simpa using hfa) (by simpa using hfb))
  exact ⟨a, ha, by change 0 < -f a at hfa; linarith⟩

private theorem quadrant_exclusion_of_negative_coefficient {C : Finset Point} {r p : Point}
    (hr : r ∈ C) (l : Point →ₗ[ℝ] ℝ)
    (hs : ∀ q ∈ C, q ≠ r → l r < l q)
    (g h : Point →ᵃ[ℝ] ℝ) (hgr : g r = 0)
    {A u w : ℝ} (hA : 0 < A) (hu : u < 0)
    (hid : ∀ q, A * (l q - l r) = u * g q + w * h q)
    (hempty : ∀ q ∈ C, q ≠ r → ¬(0 ≤ g q ∧ 0 ≤ h q))
    (hp : p ∈ convexHull ℝ (C : Set Point)) (hpr : p ≠ r)
    (hgp : 0 ≤ g p) (hhp : 0 ≤ h p) : False := by
  have hfp : 0 < l p - l r := sub_pos.mpr (linear_support_strict_on_hull hr l hs hp hpr)
  by_cases hw : 0 < w
  · have hnegative : ∀ q ∈ C, q ≠ r → g q < 0 := by
      intro q hq hqr
      by_contra hg
      have hg := le_of_not_gt hg
      have hh : h q < 0 := by
        by_contra hh
        exact hempty q hq hqr ⟨hg, le_of_not_gt hh⟩
      have hpos := mul_pos hA (sub_pos.mpr (hs q hq hqr))
      have hneg := add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg hu.le hg)
        (mul_neg_of_pos_of_neg hw hh)
      have h := hid q
      linarith
    have h := affine_support_strict_on_hull hr (-g)
      (fun q hq hqr ↦ by
        change -g r < -g q
        rw [hgr]
        linarith [hnegative q hq hqr]) hp hpr
    change -g r < -g p at h
    rw [hgr] at h
    linarith
  · have h := hid p
    have hpos := mul_pos hA hfp
    have hnonpos := add_nonpos (mul_nonpos_of_nonpos_of_nonneg hu.le hgp)
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hw) hhp)
    linarith

/-- The empty base triangle at a third-layer vertex contains no point of
that layer's whole hull other than the vertex itself. The hypothesis on
`d` says that its direction is strictly opposite the triangle's apex cone.
This rules out deeper-layer points, not merely other third-layer vertices. -/
theorem hull_inter_triangle_eq_vertex {C : Finset Point}
    (hC : ConvexPosition C) {a r b d : Point} (hr : r ∈ C)
    (htri : 0 < turn a r b)
    (hbase : ∀ q ∈ C, 0 ≤ turn b a q)
    (hempty : ∀ q ∈ C, q ∈ triangleHull a r b → q = r)
    (hd : d ∈ convexHull ℝ (C : Set Point)) (hdr : d ≠ r)
    (hd₁ : turn r b d < 0) (hd₂ : turn a r d < 0) :
    ∀ p ∈ convexHull ℝ (C : Set Point), p ∈ triangleHull a r b → p = r := by
  obtain ⟨l, hl⟩ := exists_strict_linear_support hC hr
  have hfd : 0 < l d - l r := sub_pos.mpr (linear_support_strict_on_hull hr l hl hd hdr)
  have hcoeff : l a - l r < 0 ∨ l b - l r < 0 := by
    by_contra hh
    push Not at hh
    have h := linear_triangle_identity l a r b d
    have hnonpos := add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hd₁.le hh.1)
      (mul_nonpos_of_nonpos_of_nonneg hd₂.le hh.2)
    have hpos := mul_pos htri hfd
    linarith
  have hnot (q) (hq : q ∈ C) (hqr : q ≠ r) :
      ¬(0 ≤ turn r b q ∧ 0 ≤ turn a r q) := by
    intro hh
    apply hqr
    exact hempty q hq (weaklyInsideTriangle_mem_triangleHull htri
      ⟨hh.2, hh.1, hbase q hq⟩)
  intro p hp hpTri
  by_contra hpr
  have hside := triangle_edge_nonneg htri.le hpTri
  rcases hcoeff with ha | hb
  · apply quadrant_exclusion_of_negative_coefficient hr l hl
      (Lax56Proofs.ValtrCaps.turnAffine r b) (Lax56Proofs.ValtrCaps.turnAffine a r)
      (by change turn r b r = 0; simp) (w := l b - l r)
      htri ha _ hnot hp hpr hside.2.1 hside.1
    intro q
    change turn a r b * (l q - l r) =
      (l a - l r) * turn r b q + (l b - l r) * turn a r q
    simpa only [mul_comm] using linear_triangle_identity l a r b q
  · apply quadrant_exclusion_of_negative_coefficient hr l hl
      (Lax56Proofs.ValtrCaps.turnAffine a r) (Lax56Proofs.ValtrCaps.turnAffine r b)
      (by change turn a r r = 0; simp) (w := l a - l r)
      htri hb _ _ hp hpr hside.1 hside.2.1
    · intro q
      change turn a r b * (l q - l r) =
        (l b - l r) * turn a r q + (l a - l r) * turn r b q
      simpa only [mul_comm, add_comm] using linear_triangle_identity l a r b q
    · intro q hq hqr hh
      exact hnot q hq hqr hh.symm

theorem strictlyInsideTriangle_of_generalPosition {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {a b c p : Point}
    (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hp : p ∈ P)
    (htri : 0 < turn a b c) (hpTri : p ∈ triangleHull a b c)
    (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c) :
    StrictlyInsideTriangle a b c p := by
  have hab : a ≠ b := by intro h; rw [h] at htri; simp [turn] at htri
  have hac : a ≠ c := by intro h; rw [h] at htri; simp at htri
  have hbc : b ≠ c := by intro h; rw [h] at htri; simp at htri
  have he := triangle_edge_nonneg htri.le hpTri
  exact ⟨lt_of_le_of_ne he.1
      (turn_ne_zero_of_generalPosition hgen ha hb hp hab hpa.symm hpb.symm).symm,
    lt_of_le_of_ne he.2.1
      (turn_ne_zero_of_generalPosition hgen hb hc hp hbc hpb.symm hpc.symm).symm,
    lt_of_le_of_ne he.2.2
      (turn_ne_zero_of_generalPosition hgen hc ha hp hac.symm hpc.symm hpa.symm).symm⟩

/-- A general-position point set with an interior point has at least
three outer vertices. This supplies the nondegeneracy of the inner
polygons in the four-layer construction. -/
theorem three_le_outer_card_of_inner_nonempty {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) (hinner : (inner Q).Nonempty) :
    3 ≤ (extremeLayer Q).card := by
  classical
  obtain ⟨q, hq⟩ := hinner
  have hqH : q ∈ convexHull ℝ (extremeLayer Q : Set Point) := by
    rw [convexHull_extremeLayer]
    exact subset_convexHull ℝ _ (inner_subset Q hq)
  have hnonempty : (extremeLayer Q).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    rw [h, Finset.coe_empty, convexHull_empty] at hqH
    exact hqH
  have hone : ¬(extremeLayer Q).card ≤ 1 := by
    intro h
    obtain ⟨a, ha⟩ := hnonempty
    have hsub : (extremeLayer Q : Set Point) ⊆ {a} := by
      intro p hp
      exact Finset.card_le_one.mp h p hp a ha
    have heq : q = a := by simpa using convexHull_mono hsub hqH
    exact (Finset.mem_sdiff.mp hq).2 (heq.symm ▸ ha)
  by_contra h
  have htwo : (extremeLayer Q).card = 2 := by omega
  obtain ⟨a, b, hab, hext⟩ := Finset.card_eq_two.mp htwo
  have ha : a ∈ extremeLayer Q := by rw [hext]; simp
  have hb : b ∈ extremeLayer Q := by rw [hext]; simp
  have hqa : a ≠ q := by intro h; subst a; exact (Finset.mem_sdiff.mp hq).2 ha
  have hqb : b ≠ q := by intro h; subst b; exact (Finset.mem_sdiff.mp hq).2 hb
  have hzero : ∀ p ∈ (extremeLayer Q : Set Point), turn a b p = 0 := by
    intro p hp
    rw [hext] at hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;> simp
  have hz : turn a b q = 0 := le_antisymm
    (turn_nonpos_of_mem_convexHull (fun p hp ↦ (hzero p hp).le) hqH)
    (turn_nonneg_of_mem_convexHull (fun p hp ↦ (hzero p hp).ge) hqH)
  exact turn_ne_zero_of_generalPosition hgen (extremeLayer_subset Q ha)
    (extremeLayer_subset Q hb) (inner_subset Q hq) hab hqa hqb hz

/-- Valtr's choice of `c_i`: if the radial triangle on a supporting outer
edge meets the next layer, one can choose an apex in that layer whose
base triangle is empty in the entire ambient set. In particular, points
in deeper layers have not been silently discarded. -/
theorem exists_empty_layer_triangle {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) {a b d : Point}
    (ha : a ∈ extremeLayer Q) (hb : b ∈ extremeLayer Q) (hab : a ≠ b)
    (hd : d ∈ inner (inner Q))
    (hbase : ∀ p ∈ Q, turn a b p ≤ 0)
    (hmeet : ∃ q ∈ extremeLayer (inner Q), q ∈ triangleHull d b a) :
    ∃ r ∈ extremeLayer (inner Q),
      StrictlyInsideTriangle d b a r ∧ 0 < turn a r b ∧
      ∀ p ∈ Q, p ∈ triangleHull a r b → p = a ∨ p = r ∨ p = b := by
  classical
  let C := extremeLayer (inner Q)
  have hCinner : C ⊆ inner Q := extremeLayer_subset (inner Q)
  have hCQ : C ⊆ Q := hCinner.trans (inner_subset Q)
  have hneOuter {p x : Point} (hp : p ∈ inner Q) (hx : x ∈ extremeLayer Q) : p ≠ x := by
    intro h
    subst p
    exact (Finset.mem_sdiff.mp hp).2 hx
  have hdinner : d ∈ inner Q := inner_subset (inner Q) hd
  have hdQ : d ∈ Q := inner_subset Q hdinner
  have hda : d ≠ a := hneOuter hdinner ha
  have hdb : d ≠ b := hneOuter hdinner hb
  have hdne : turn a b d ≠ 0 := turn_ne_zero_of_generalPosition hgen
    (extremeLayer_subset Q ha) (extremeLayer_subset Q hb) hdQ hab hda.symm hdb.symm
  have hTi : 0 < turn d b a := by
    rw [turn_reverse]
    exact neg_pos.mpr (lt_of_le_of_ne (hbase d hdQ) hdne)
  have hstrict {q : Point} (hq : q ∈ C) (hqT : q ∈ triangleHull d b a) :
      StrictlyInsideTriangle d b a q := by
    apply strictlyInsideTriangle_of_generalPosition hgen hdQ
      (extremeLayer_subset Q hb) (extremeLayer_subset Q ha) (hCQ hq) hTi hqT
    · intro h
      subst q
      exact (Finset.mem_sdiff.mp hd).2 hq
    · exact hneOuter (hCinner hq) hb
    · exact hneOuter (hCinner hq) ha
  obtain ⟨q, hqC, hqTi⟩ := hmeet
  have hqstrict := hstrict hqC hqTi
  let P := C ∪ {a, b}
  have hPQ : P ⊆ Q := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hCQ hp
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact extremeLayer_subset Q ha
      · exact extremeLayer_subset Q hb
  have hPgen : ¬HasThreeCollinear P := fun h ↦ hgen (hasThreeCollinear_mono hPQ h)
  obtain ⟨r, hrP, hrT, hrpos, hempty⟩ := exists_empty_triangle_on_base hPgen
    (Finset.mem_union_left _ hqC) (show b ∈ P by simp [P])
    (show a ∈ P by simp [P]) hqstrict.2.1
  have hrC : r ∈ C := by
    rcases Finset.mem_union.mp hrP with h | h
    · exact h
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with rfl | rfl <;> simp at hrpos
  have hrTi : r ∈ triangleHull d b a :=
    triangleHull_subset_of_mem (convex_convexHull ℝ _) hqTi
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hrT
  have hrstrict := hstrict hrC hrTi
  have htri : 0 < turn a r b := by rw [turn_rotate b a r]; exact hrpos
  have hCempty : ∀ p ∈ C, p ∈ triangleHull a r b → p = r := by
    intro p hp hpT
    have hh := hempty p (Finset.mem_union_left _ hp)
      (by simpa only [triangleHull_rotate] using hpT)
    rcases hh with h | h | h
    · exact h
    · exact (hneOuter (hCinner hp) hb h).elim
    · exact (hneOuter (hCinner hp) ha h).elim
  have hdC : d ∈ convexHull ℝ (C : Set Point) := by
    dsimp [C]
    rw [convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hdinner
  have hdr : d ≠ r := by intro h; subst d; exact (Finset.mem_sdiff.mp hd).2 hrC
  have hright : turn r b d < 0 := by
    rw [turn_reverse]
    exact neg_neg_of_pos hrstrict.1
  have hleft : turn a r d < 0 := by
    rw [turn_swap_last]
    exact neg_neg_of_pos hrstrict.2.2
  have hcap := hull_inter_triangle_eq_vertex (extremeLayer_convexPosition (inner Q))
    hrC htri (fun p hp ↦ by rw [turn_swap_first]; exact neg_nonneg.mpr (hbase p (hCQ hp)))
    hCempty hdC hdr hright hleft
  refine ⟨r, hrC, hrstrict, htri, ?_⟩
  intro p hp hpT
  by_cases hpB : p ∈ extremeLayer Q
  · by_contra h
    push Not at h
    have hsmall : ({a, r, b} : Finset Point) ⊆ Q := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact extremeLayer_subset Q ha
      · exact hCQ hrC
      · exact extremeLayer_subset Q hb
    apply extreme_not_mem_convexHull hpB hsmall (by simp [h.1, h.2.1, h.2.2])
    simpa only [Finset.coe_insert, Finset.coe_singleton] using hpT
  · right; left
    apply hcap p _ hpT
    rw [convexHull_extremeLayer]
    exact subset_convexHull ℝ _ (Finset.mem_sdiff.mpr ⟨hp, hpB⟩)

end Lax56Proofs.ValtrSelection
