import Lax56Proofs.ValtrMissingExtension
import Lax56Proofs.HKBAffineMirror

namespace Lax56Proofs.ValtrCoverage

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors Lax56Proofs.ValtrCyclic
open Lax56Proofs.ValtrConvexRun
open Lax56Proofs.ValtrMissingExtension
open Lax56Proofs.HKBAffineMirror
open scoped Classical

theorem extremeLayer_image_linear (e : Point ≃ₗ[ℝ] Point) (Q : Finset Point) :
    extremeLayer (Q.image e) = (extremeLayer Q).image e := by
  apply Finset.coe_injective
  simp only [Finset.coe_image, coe_extremeLayer]
  rw [image_extremePoints]
  congr 1
  exact (e.toLinearMap.toAffineMap.image_convexHull (Q : Set Point)).symm

theorem inner_image_linear (e : Point ≃ₗ[ℝ] Point) (Q : Finset Point) :
    inner (Q.image e) = (inner Q).image e := by
  unfold Lax56.ConvexLayers.inner
  rw [extremeLayer_image_linear]
  exact (Finset.image_sdiff _ _ e.injective).symm

theorem mirror_sector_reverse {n : ℕ} {v : Fin n → Point} {q : Point}
    (hq : q ∈ sector v) :
    mirrorAffine q ∈ sector (fun i ↦ mirrorAffine (v i.rev)) := by
  intro i j hij
  rw [turn_mirror, ← turn_swap_first]
  exact hq j.rev i.rev (Fin.rev_lt_rev.mpr hij)

/-- The first endpoint of an inner edge crossed by an outer radial
triangle lies between the preceding selected apex and the outer endpoint.
The two ingredients are inner extremality and emptiness of the preceding
base triangle; no unproved cyclic matching assertion is used. -/
theorem crossed_edge_endpoint_mem_triangle {Q : Finset Point} {d p a c u w : Point}
    (hc : c ∈ extremeLayer (inner Q)) (hu : u ∈ extremeLayer (inner Q))
    (hw : w ∈ extremeLayer (inner Q)) (hd : d ∈ inner (inner Q))
    (hcTri : StrictlyInsideTriangle d p a c)
    (haSector : a ∈ sector ![w, d, u])
    (hdedge : 0 < turn d u w)
    (hCbase : ∀ z ∈ inner Q, 0 ≤ turn u w z)
    (hBbase : ∀ z ∈ inner Q, 0 ≤ turn p a z)
    (hempty : ∀ z ∈ extremeLayer (inner Q), z ∈ triangleHull p c a → z = c) :
    u ∈ triangleHull d c a := by
  have hdcapos : 0 < turn d c a := by rw [turn_rotate a d c]; exact hcTri.2.2
  have hdua : 0 < turn d u a := haSector 1 2 (by decide)
  have hwdapos : 0 < turn w d a := haSector 0 1 (by decide)
  have hdaw : 0 < turn d a w := by rw [turn_rotate]; exact hwdapos
  have hangular : 0 ≤ turn d c u := by
    by_contra hh
    have hneg := lt_of_not_ge hh
    have hduc : 0 < turn d u c := by rw [turn_swap_last]; exact neg_pos.mpr hneg
    have hdcw : 0 < turn d c w := by
      apply (mul_pos_iff_of_pos_left hdua).mp
      have hid : turn d u a * turn d c w =
          turn d u c * turn d a w + turn d u w * turn d c a := by
        unfold turn; ring
      rw [hid]
      exact add_pos (mul_pos hduc hdaw) (mul_pos hdedge hdcapos)
    have hcduw : c ∈ triangleHull d u w := by
      apply weaklyInsideTriangle_mem_triangleHull hdedge
      refine ⟨hduc.le, hCbase c (extremeLayer_subset _ hc), ?_⟩
      rw [turn_swap_first]
      have hneg' : turn d w c < 0 := by rw [turn_swap_last]; exact neg_neg_of_pos hdcw
      exact (neg_pos.mpr hneg').le
    have hcd : c ≠ d := (strictlyInsideTriangle_ne_vertices hcTri).1
    have hcu : c ≠ u := by rintro rfl; simp at hneg
    have hcw : c ≠ w := by
      intro h
      rw [h] at hdcapos
      have hneg' : turn d w a < 0 := by rw [turn_swap_first]; exact neg_neg_of_pos hwdapos
      exact hdcapos.not_gt hneg'
    exact extreme_not_mem_triangle hc (inner_subset _ hd)
      (extremeLayer_subset _ hu) (extremeLayer_subset _ hw) hcd hcu hcw hcduw
  have hca : 0 ≤ turn c a u := by
    by_contra hh
    have hneg := lt_of_not_ge hh
    have hcdunonpos : turn c d u ≤ 0 := by rw [turn_swap_first]; exact neg_nonpos.mpr hangular
    have hcdp : 0 < turn c d p := by rw [← turn_rotate]; exact hcTri.1
    have hcpa : 0 < turn c p a := by rw [← turn_rotate]; exact hcTri.2.1
    have hcad : 0 < turn c a d := by rw [← turn_rotate]; exact hcTri.2.2
    have hcpu : 0 < turn c p u := by
      have hid := turn_origin_relation c d p a u
      have hneg₁ := mul_neg_of_pos_of_neg hcdp hneg
      have hneg₂ := mul_nonpos_of_nonneg_of_nonpos hcpa.le hcdunonpos
      have hpos : 0 < turn c a d * turn c p u := by linarith
      exact (mul_pos_iff_of_pos_left hcad).mp hpos
    have huTri : u ∈ triangleHull c p a := by
      apply weaklyInsideTriangle_mem_triangleHull hcpa
      refine ⟨hcpu.le, hBbase u (extremeLayer_subset _ hu), ?_⟩
      rw [turn_swap_first]
      exact (neg_pos.mpr hneg).le
    have huc : u = c := hempty u hu (by
      convert huTri using 1
      unfold triangleHull
      congr 1
      ext x; simp [or_comm, or_left_comm])
    rw [huc] at hneg
    simp at hneg
  apply weaklyInsideTriangle_mem_triangleHull hdcapos
  refine ⟨hangular, hca, ?_⟩
  rw [turn_swap_first]
  exact (neg_pos.mpr (by rw [turn_swap_last]; exact neg_neg_of_pos hdua)).le

/-- The second endpoint statement follows by reflection, using the same
proved extremality argument with the cyclic direction reversed. -/
theorem crossed_edge_endpoint_mem_triangle_right {Q : Finset Point} {d b f c u w : Point}
    (hc : c ∈ extremeLayer (inner Q)) (hu : u ∈ extremeLayer (inner Q))
    (hw : w ∈ extremeLayer (inner Q)) (hd : d ∈ inner (inner Q))
    (hcTri : StrictlyInsideTriangle d b f c)
    (hbSector : b ∈ sector ![w, d, u])
    (hdedge : 0 < turn d u w)
    (hCbase : ∀ z ∈ inner Q, 0 ≤ turn u w z)
    (hBbase : ∀ z ∈ inner Q, 0 ≤ turn b f z)
    (hempty : ∀ z ∈ extremeLayer (inner Q), z ∈ triangleHull b c f → z = c) :
    w ∈ triangleHull d b c := by
  have hIeq : inner (Q.image mirrorLinear) = (inner Q).image mirrorLinear :=
    inner_image_linear _ _
  have hCeq : extremeLayer (inner (Q.image mirrorLinear)) =
      (extremeLayer (inner Q)).image mirrorLinear := by
    rw [hIeq, extremeLayer_image_linear]
  have hIIeq : inner (inner (Q.image mirrorLinear)) =
      (inner (inner Q)).image mirrorLinear := by
    rw [hIeq, inner_image_linear]
  have hc' : mirrorAffine c ∈ extremeLayer (inner (Q.image mirrorLinear)) := by
    rw [hCeq]; exact Finset.mem_image.mpr ⟨c, hc, rfl⟩
  have hu' : mirrorAffine u ∈ extremeLayer (inner (Q.image mirrorLinear)) := by
    rw [hCeq]; exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hw' : mirrorAffine w ∈ extremeLayer (inner (Q.image mirrorLinear)) := by
    rw [hCeq]; exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hd' : mirrorAffine d ∈ inner (inner (Q.image mirrorLinear)) := by
    rw [hIIeq]; exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  have hbSector' : mirrorAffine b ∈ sector ![mirrorAffine u, mirrorAffine d, mirrorAffine w] := by
    have hm := mirror_sector_reverse hbSector
    have heq : (fun i : Fin 3 ↦ mirrorAffine (![w, d, u] i.rev)) =
        ![mirrorAffine u, mirrorAffine d, mirrorAffine w] := by
      funext i; fin_cases i <;> rfl
    rwa [heq] at hm
  have hdedge' : 0 < turn (mirrorAffine d) (mirrorAffine w) (mirrorAffine u) := by
    rw [turn_mirror, ← turn_swap_last]
    exact hdedge
  have hCbase' : ∀ z ∈ inner (Q.image mirrorLinear),
      0 ≤ turn (mirrorAffine w) (mirrorAffine u) z := by
    intro z hz
    rw [hIeq] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    change 0 ≤ turn (mirrorAffine w) (mirrorAffine u) (mirrorAffine z₀)
    rw [turn_mirror, ← turn_swap_first]
    exact hCbase z₀ hz₀
  have hBbase' : ∀ z ∈ Lax56.ConvexLayers.inner (Q.image mirrorLinear),
      0 ≤ turn (mirrorAffine f) (mirrorAffine b) z := by
    intro z hz
    rw [hIeq] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    change 0 ≤ turn (mirrorAffine f) (mirrorAffine b) (mirrorAffine z₀)
    rw [turn_mirror, ← turn_swap_first]
    exact hBbase z₀ hz₀
  have hempty' : ∀ z ∈ extremeLayer (inner (Q.image mirrorLinear)),
      z ∈ triangleHull (mirrorAffine f) (mirrorAffine c) (mirrorAffine b) → z = mirrorAffine c := by
    intro z hz hzTri
    rw [hCeq] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hz
    have hzOrigTri : z₀ ∈ triangleHull f c b := mirror_mem_triangleHull_iff.mp hzTri
    have hzTri' : z₀ ∈ triangleHull b c f := by
      convert hzOrigTri using 1
      unfold triangleHull
      congr 1
      ext x; simp [or_comm, or_left_comm]
    exact congrArg mirrorAffine (hempty z₀ hz₀ hzTri')
  have h := crossed_edge_endpoint_mem_triangle hc' hw' hu' hd'
    (mirror_strictlyInside_swap hcTri) hbSector' hdedge' hCbase' hBbase' hempty'
  exact mirror_mem_triangleHull_swap_iff.mp h

/-- A point on the outward side of the radial line, and on the indicated
side of the selected apex, belongs to the preceding sector. -/
theorem mem_preceding_sector_of_side {d p a c q : Point}
    (hc : StrictlyInsideTriangle d p a c)
    (hraw : 0 < turn d a q) (hacq : 0 < turn a c q) :
    q ∈ sector ![a, c, p] := by
  have hadc : 0 < turn a d c := hc.2.2
  have hcpa : 0 < turn c p a := by rw [← turn_rotate]; exact hc.2.1
  have hcpd : turn c p d < 0 := by
    rw [turn_rotate, turn_swap_last]
    exact neg_neg_of_pos hc.1
  have hdcq : 0 < turn d c q := by
    have hid : turn d c q = turn a d c + turn a c q + turn d a q := by
      unfold turn; ring
    rw [hid]
    positivity
  have hcpq : 0 < turn c p q := by
    have hid := turn_affine_circuit a d c q c p
    simp only [turn_self_left, mul_zero, add_zero] at hid
    have hleft := mul_pos hdcq hcpa
    have hneg := mul_neg_of_pos_of_neg hacq hcpd
    have hpos : 0 < turn a d c * turn c p q := by linarith
    exact (mul_pos_iff_of_pos_left hadc).mp hpos
  have hapq : 0 < turn a p q := by
    apply (mul_pos_iff_of_pos_left hadc).mp
    have hid : turn a d c * turn a p q =
        turn a d p * turn a c q + turn a p c * turn a d q := by
      unfold turn; ring
    rw [hid]
    have hadp : 0 < turn a d p := by rw [← turn_rotate]; exact turn_pos_of_strictlyInsideTriangle hc
    have hapc : turn a p c < 0 := by rw [turn_swap_first]; exact neg_neg_of_pos hc.2.1
    have hadq : turn a d q < 0 := by rw [turn_swap_first]; exact neg_neg_of_pos hraw
    exact add_pos (mul_pos hadp hacq) (mul_pos_of_neg_of_neg hapc hadq)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- Excluding the preceding sector gives the supporting inequality for
the actual crossed-edge endpoint, by the triangle containment above. -/
theorem crossed_endpoint_side_of_not_preceding_sector {d p a c u q : Point}
    (hc : StrictlyInsideTriangle d p a c) (hu : u ∈ triangleHull d c a) (hua : u ≠ a)
    (hraw : 0 < turn d a q) (hnot : q ∉ sector ![a, c, p])
    (hne : turn a c q ≠ 0) : 0 < turn u a q := by
  have hac : turn a c q < 0 := lt_of_le_of_ne
    (le_of_not_gt (fun h ↦ hnot (mem_preceding_sector_of_side hc hraw h))) hne
  have hcaq : 0 < turn c a q := by rw [turn_swap_first]; exact neg_pos.mpr hac
  rw [← turn_rotate u a q]
  apply turn_pos_on_triangle_except_vertex (a := a) (b := d) (c := c)
    (by simp) _ _ _ hua
  · rw [turn_rotate]; exact hraw
  · rw [turn_rotate]; exact hcaq
  · rwa [← triangleHull_rotate a d c]

theorem mirror_sector_reverse_iff {n : ℕ} {v : Fin n → Point} {q : Point} :
    mirrorAffine q ∈ sector (fun i ↦ mirrorAffine (v i.rev)) ↔ q ∈ sector v := by
  constructor
  · intro h
    have h' := mirror_sector_reverse h
    simpa only [mirrorAffine_involutive, Fin.rev_rev] using h'
  · exact mirror_sector_reverse

theorem crossed_endpoint_side_of_not_following_sector {d b f c w q : Point}
    (hc : StrictlyInsideTriangle d b f c) (hw : w ∈ triangleHull d b c) (hwb : w ≠ b)
    (hraw : 0 < turn b d q) (hnot : q ∉ sector ![f, c, b])
    (hne : turn b c q ≠ 0) : 0 < turn b w q := by
  have hnot' : mirrorAffine q ∉ sector ![mirrorAffine b, mirrorAffine c, mirrorAffine f] := by
    intro h
    apply hnot
    apply mirror_sector_reverse_iff.mp
    have heq : (fun i : Fin 3 ↦ mirrorAffine (![f, c, b] i.rev)) =
        ![mirrorAffine b, mirrorAffine c, mirrorAffine f] := by
      funext i; fin_cases i <;> rfl
    rwa [heq]
  have hraw' : 0 < turn (mirrorAffine d) (mirrorAffine b) (mirrorAffine q) := by
    rw [turn_mirror, ← turn_swap_first]
    exact hraw
  have hne' : turn (mirrorAffine b) (mirrorAffine c) (mirrorAffine q) ≠ 0 := by
    rw [turn_mirror]
    exact neg_ne_zero.mpr hne
  have h := crossed_endpoint_side_of_not_preceding_sector
    (mirror_strictlyInside_swap hc) (mirror_mem_triangleHull_swap_iff.mpr hw)
    (mirrorAffine.injective.ne hwb) hraw' hnot' hne'
  rwa [turn_mirror, ← turn_swap_first] at h

/-- For a convex quadrilateral, its two end sides and closing chord
already determine its exterior sector. The other three inequalities are
positive determinant combinations. -/
theorem quad_sector_of_three_sides {a b c d q : Point}
    (habc : 0 < turn a b c) (habd : 0 < turn a b d)
    (hacd : 0 < turn a c d) (hbcd : 0 < turn b c d)
    (habq : 0 < turn a b q) (hcdq : 0 < turn c d q) (hadq : 0 < turn a d q) :
    q ∈ sector ![a, b, c, d] := by
  have hacq : 0 < turn a c q := by
    apply (mul_pos_iff_of_pos_left habd).mp
    have hid : turn a b d * turn a c q =
        turn a c d * turn a b q + turn a b c * turn a d q := by
      unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos hacd habq) (mul_pos habc hadq)
  have hbcq : 0 < turn b c q := by
    apply (mul_pos_iff_of_pos_left hacd).mp
    have hid := turn_affine_circuit a c d q b c
    simp only [turn_self_right, mul_zero, zero_add] at hid
    rw [← hid]
    have hbca : 0 < turn b c a := by rw [turn_rotate]; exact habc
    exact add_pos (mul_pos hcdq hbca) (mul_pos hacq hbcd)
  have hbdq : 0 < turn b d q := by
    apply (mul_pos_iff_of_pos_left hacq).mp
    have hid : turn a c q * turn b d q =
        turn a b q * turn c d q + turn a d q * turn b c q := by
      unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos habq hcdq) (mul_pos hadq hbcq)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- The local missing-sector cover, with the actual crossed-edge
endpoints. All side implications come from the proved triangle geometry. -/
theorem raw_sector_mem_neighbor_or_four_sector {d p a b f c e u w q : Point}
    (hc : StrictlyInsideTriangle d p a c) (he : StrictlyInsideTriangle d b f e)
    (hu : u ∈ triangleHull d c a) (hua : u ≠ a)
    (hw : w ∈ triangleHull d b e) (hwb : w ≠ b)
    (hbwu : 0 < turn b w u) (hbwa : 0 < turn b w a)
    (hbua : 0 < turn b u a) (hwua : 0 < turn w u a)
    (hq : q ∈ sector ![b, d, a])
    (hne₁ : turn a c q ≠ 0) (hne₂ : turn b e q ≠ 0) :
    q ∈ sector ![a, c, p] ∨ q ∈ sector ![b, w, u, a] ∨ q ∈ sector ![f, e, b] := by
  by_cases hprev : q ∈ sector ![a, c, p]
  · exact Or.inl hprev
  by_cases hnext : q ∈ sector ![f, e, b]
  · exact Or.inr (Or.inr hnext)
  have huaq := crossed_endpoint_side_of_not_preceding_sector hc hu hua
    (hq 1 2 (by decide)) hprev hne₁
  have hbwq := crossed_endpoint_side_of_not_following_sector he hw hwb
    (hq 0 1 (by decide)) hnext hne₂
  exact Or.inr (Or.inl (quad_sector_of_three_sides hbwu hbwa hbua hwua
    hbwq huaq (hq 0 2 (by decide))))

/-- In a hexagon-free ambient set, a missing radial sector is covered by
the two neighboring defined sectors. The argument constructs the crossed
inner edge, establishes its endpoint containments, and excludes its
four-sector using the empty-pentagon extension theorem. -/
theorem missing_raw_sector_mem_neighbor {S Q : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    (hQ : HullClosedIn S Q) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner Q) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d p a b f c e q : Point} (hd : d ∈ inner (inner Q))
    (ha : a ∈ extremeLayer Q) (hb : b ∈ extremeLayer Q)
    (hc : c ∈ extremeLayer (inner Q)) (he : e ∈ extremeLayer (inner Q))
    (hcTri : StrictlyInsideTriangle d p a c) (heTri : StrictlyInsideTriangle d b f e)
    (hprevBase : ∀ z ∈ inner Q, 0 ≤ turn p a z)
    (hbase : ∀ z ∈ inner Q, 0 < turn a b z)
    (hnextBase : ∀ z ∈ inner Q, 0 ≤ turn b f z)
    (hprevEmpty : ∀ z ∈ extremeLayer (inner Q), z ∈ triangleHull p c a → z = c)
    (hnextEmpty : ∀ z ∈ extremeLayer (inner Q), z ∈ triangleHull b e f → z = e)
    (hmissing : ∀ i, v i ∉ triangleHull d a b)
    (hqS : q ∈ S) (hqOut : q ∉ convexHull ℝ (Q : Set Point))
    (hqRaw : q ∈ sector ![b, d, a]) :
    q ∈ sector ![a, c, p] ∨ q ∈ sector ![f, e, b] := by
  have hgenQ : ¬HasThreeCollinear Q :=
    fun h ↦ hgen (hasThreeCollinear_mono hQ.1 h)
  have hvC (i) : v i ∈ extremeLayer (inner Q) := by
    change v i ∈ (extremeLayer (inner Q) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hvI (i) : v i ∈ inner Q := extremeLayer_subset _ (hvC i)
  have hvQ (i) : v i ∈ Q := inner_subset _ (hvI i)
  have hdI : d ∈ inner Q := inner_subset _ hd
  have hdHull : d ∈ convexHull ℝ (Set.range v) := by
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hdI
  have hdnot : d ∉ Set.range v := by
    rw [hrange]
    exact (Finset.mem_sdiff.mp hd).2
  obtain ⟨i, hi, hforbid⟩ := exists_crossed_edge_four_sector_empty hgen hno hQ
    hn v hinj hrange htri hd ha hb hbase hmissing
  have haSector := hi (left_mem_segment ℝ a b)
  have hbSector := hi (right_mem_segment ℝ a b)
  have hdedge : 0 < turn d (v i) (v (i + 1)) := by
    rw [← turn_rotate]
    exact cyclic_edge_strict_of_mem_hull hgenQ hn v hinj htri hvQ
      (inner_subset _ hdI) hdHull hdnot i
  have hCbase : ∀ z ∈ inner Q, 0 ≤ turn (v i) (v (i + 1)) z := by
    intro z hz
    apply cyclic_edge_nonneg_of_mem_hull htri _ i
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hz
  have huTri := crossed_edge_endpoint_mem_triangle hc (hvC i) (hvC (i + 1)) hd
    hcTri haSector hdedge hCbase hprevBase hprevEmpty
  have hwTri := crossed_edge_endpoint_mem_triangle_right he (hvC i) (hvC (i + 1)) hd
    heTri hbSector hdedge hCbase hnextBase hnextEmpty
  have hneInnerOuter {x y : Point} (hx : x ∈ inner Q) (hy : y ∈ extremeLayer Q) : x ≠ y := by
    intro h
    exact (Finset.mem_sdiff.mp hx).2 (h.symm ▸ hy)
  have hbwu : 0 < turn b (v (i + 1)) (v i) := by
    rw [← turn_rotate]
    exact hbSector 0 2 (by decide)
  have hbwa : 0 < turn b (v (i + 1)) a := by rw [turn_rotate]; exact hbase _ (hvI (i + 1))
  have hbua : 0 < turn b (v i) a := by rw [turn_rotate]; exact hbase _ (hvI i)
  have hwua : 0 < turn (v (i + 1)) (v i) a := haSector 0 2 (by decide)
  have hqne {z : Point} (hz : z ∈ Q) : z ≠ q := by
    intro h
    exact hqOut (h ▸ subset_convexHull ℝ _ hz)
  have hcI : c ∈ inner Q := extremeLayer_subset _ hc
  have heI : e ∈ inner Q := extremeLayer_subset _ he
  have haQ := extremeLayer_subset Q ha
  have hbQ := extremeLayer_subset Q hb
  have hcQ := inner_subset Q hcI
  have heQ := inner_subset Q heI
  have hne₁ : turn a c q ≠ 0 := turn_ne_zero_of_generalPosition hgen
    (hQ.1 haQ) (hQ.1 hcQ) hqS (hneInnerOuter hcI ha).symm (hqne haQ) (hqne hcQ)
  have hne₂ : turn b e q ≠ 0 := turn_ne_zero_of_generalPosition hgen
    (hQ.1 hbQ) (hQ.1 heQ) hqS (hneInnerOuter heI hb).symm (hqne hbQ) (hqne heQ)
  rcases raw_sector_mem_neighbor_or_four_sector hcTri heTri huTri (hneInnerOuter (hvI i) ha)
    hwTri (hneInnerOuter (hvI (i + 1)) hb) hbwu hbwa hbua hwua hqRaw hne₁ hne₂ with h | h | h
  · exact Or.inl h
  · exact (hforbid q hqS h).elim
  · exact Or.inr h

end Lax56Proofs.ValtrCoverage
