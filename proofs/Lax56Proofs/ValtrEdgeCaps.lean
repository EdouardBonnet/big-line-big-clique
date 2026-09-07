import Lax56Proofs.ValtrConvexRun

namespace Lax56Proofs.ValtrEdgeCaps

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSplice Lax56Proofs.ValtrConvexRun
open scoped Classical

/-- Four outer vertices beyond a supporting edge of the inner remainder
form an empty hexagon together with the two endpoints of that edge. -/
theorem emptyHexagon_of_four_outer_edge_points {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {a b : Point}
    (ha : a ∈ inner S) (hb : b ∈ inner S) (hab : a ≠ b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hcard : 4 ≤ ((extremeLayer S).filter (fun p ↦ 0 < turn a b p)).card) :
    HasEmptyHexagon S := by
  obtain ⟨R, hRcap, hRcard⟩ := Finset.exists_subset_card_eq hcard
  have hR : R ⊆ extremeLayer S := hRcap.trans (Finset.filter_subset _ _)
  have hRside (p) (hp : p ∈ R) : 0 < turn a b p := (Finset.mem_filter.mp (hRcap hp)).2
  let v : Fin 2 → Point := ![a, b]
  have hinj : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have hvinner (i) : v i ∈ inner S := by fin_cases i <;> assumption
  let H := R ∪ Finset.univ.image v
  have hHS : H ⊆ S := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact extremeLayer_subset S (hR hp)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact inner_subset S (hvinner i)
  have hvH (i) : v i ∈ H :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hdisj : Disjoint R (Finset.univ.image v) := by
    apply Finset.disjoint_left.mpr
    intro p hpR hpv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hpv
    exact (Finset.mem_sdiff.mp (hvinner i)).2 (hR hpR)
  have hside (p) (hp : p ∈ H) : 0 ≤ turn a b p := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (hRside p hp).le
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      fin_cases i <;> simp [v]
  refine ⟨H, hHS, ?_, ?_, ?_⟩
  · dsimp [H]
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj, hRcard]
    decide
  · apply convexPosition_splice_of_edge_supports hgen hR v hinj
      (fun i ↦ inner_subset S (hvinner i))
    · intro i j
      fin_cases i; fin_cases j <;> simp [v]
    · intro i p hp
      fin_cases i
      exact (hRside p hp).le
  · intro p hp hpHull
    by_cases hpouter : p ∈ extremeLayer S
    · by_contra hpH
      exact extreme_not_mem_convexHull hpouter hHS hpH hpHull
    have hpinner : p ∈ inner S := Finset.mem_sdiff.mpr ⟨hp, hpouter⟩
    have hz : turn a b p = 0 := le_antisymm (hbase p hpinner)
      (turn_nonneg_of_mem_convexHull (A := (H : Set Point)) hside hpHull)
    by_cases hpa : p = a
    · subst p; exact hvH 0
    by_cases hpb : p = b
    · subst p; exact hvH 1
    exact (turn_ne_zero_of_generalPosition hgen (inner_subset S ha) (inner_subset S hb)
      hp hab (Ne.symm hpa) (Ne.symm hpb) hz).elim

theorem outer_edge_card_le_three {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S) {a b : Point}
    (ha : a ∈ inner S) (hb : b ∈ inner S) (hab : a ≠ b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0) :
    ((extremeLayer S).filter (fun p ↦ 0 < turn a b p)).card ≤ 3 := by
  by_contra hh
  exact hno (emptyHexagon_of_four_outer_edge_points hgen ha hb hab hbase (by omega))

/-- A side test at an inner point carries visibility across the next
edge of a clockwise convex polygon. -/
theorem next_base_pos {a b e f x : Point}
    (habe : turn a b e < 0) (habf : turn a b f < 0)
    (hbef : 0 < turn b e f) (habx : 0 < turn a b x)
    (hbex : 0 < turn b e x) : 0 < turn b f x := by
  have hid : (-turn a b f) * turn b e x =
      (-turn a b e) * turn b f x - turn b e f * turn a b x := by
    unfold turn; ring
  have hpos := mul_pos (neg_pos.mpr habf) hbex
  have hpos' := mul_pos hbef habx
  have hmul : 0 < (-turn a b e) * turn b f x := by nlinarith
  exact (mul_pos_iff_of_pos_left (neg_pos.mpr habe)).mp hmul

/-- The reversed edge-visibility implication. -/
theorem previous_base_pos {a b e f x : Point}
    (habe : turn a b e < 0) (habf : turn a b f < 0)
    (hbef : 0 < turn b e f) (hbfx : 0 < turn b f x)
    (hebx : 0 < turn e b x) : 0 < turn a b x := by
  have hid : (-turn a b f) * turn e b x =
      turn b e f * turn a b x + turn a b e * turn b f x := by
    unfold turn; ring
  have hpos := mul_pos (neg_pos.mpr habf) hebx
  have hneg := mul_neg_of_neg_of_pos habe hbfx
  have hmul : 0 < turn b e f * turn a b x := by nlinarith
  exact (mul_pos_iff_of_pos_left hbef).mp hmul

/-- A point beyond the next side, but outside the next sector, forces
every outer vertex of that sector into the preceding edge's outer cap.
The exclusion is proved by putting a contrary vertex in a triangle of
ambient points; no disjointness of planar sectors is asserted. -/
theorem next_sector_in_previous_cap {S : Finset Point} {a b e f x : Point}
    (hb : b ∈ S) (hf : f ∈ S) (hx : x ∈ S)
    (habe : turn a b e < 0) (habf : turn a b f < 0)
    (hbef : 0 < turn b e f) (habx : 0 < turn a b x)
    (hbex : 0 < turn b e x) (hout : x ∉ sector ![b, e, f])
    {y : Point} (hy : y ∈ extremeLayer S) (hyS : y ∈ sector ![b, e, f]) :
    0 < turn a b y := by
  have hbfx := next_base_pos habe habf hbef habx hbex
  have hefX : turn e f x ≤ 0 := by
    by_contra hh
    have hh' : 0 < turn e f x := lt_of_not_ge hh
    apply hout
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption
  have hbey : 0 < turn b e y := hyS 0 1 (by decide)
  have hefy : 0 < turn e f y := hyS 1 2 (by decide)
  have hbfy : 0 < turn b f y := hyS 0 2 (by decide)
  have hfxy : 0 < turn f x y := by
    have hid : turn b e f * turn f x y =
        (-turn e f x) * turn b f y + turn b f x * turn e f y := by
      unfold turn; ring
    have hnon := mul_nonneg (neg_nonneg.mpr hefX) hbfy.le
    have hpos := mul_pos hbfx hefy
    apply (mul_pos_iff_of_pos_left hbef).mp
    nlinarith
  by_contra hh
  have haby : turn a b y ≤ 0 := le_of_not_gt hh
  have hxby : 0 < turn x b y := by
    have hid : (-turn a b e) * turn x b y =
        turn a b x * turn b e y - turn a b y * turn b e x := by
      unfold turn; ring
    have hpos := mul_pos habx hbey
    have hnon := mul_nonpos_of_nonpos_of_nonneg haby hbex.le
    apply (mul_pos_iff_of_pos_left (neg_pos.mpr habe)).mp
    nlinarith
  have hyb : y ≠ b := by rintro rfl; simp [turn] at hbfy
  have hyf : y ≠ f := by rintro rfl; simp at hbfy
  have hyx : y ≠ x := by rintro rfl; exact hout hyS
  exact extreme_not_mem_triangle hy hb hf hx hyb hyf hyx
    (strictlyInsideTriangle_mem_triangleHull ⟨hbfy, hfxy, hxby⟩)

end Lax56Proofs.ValtrEdgeCaps
