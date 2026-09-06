import Lax56Proofs.ValtrSplice
import Lax56Proofs.ValtrCyclic

namespace Lax56Proofs.ValtrSectorBounds

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSplice Lax56Proofs.ValtrCyclic
open Lax56Proofs.ValtrSectors
open scoped Classical

/-- Three outer vertices in the sector of an empty inner triangle give
an empty hexagon. Its base must be an outward supporting edge of the
inner remainder. This is the base case of Valtr's sector-run bound. -/
theorem emptyHexagon_of_three_outer_sector_points {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) {a c b : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (htri : 0 < turn a c b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b)
    (hcard : 3 ≤ ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b])).card) :
    HasEmptyHexagon S := by
  classical
  let cap := (extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b])
  obtain ⟨R, hRcap, hRcard⟩ := Finset.exists_subset_card_eq hcard
  have hR : R ⊆ extremeLayer S := hRcap.trans (Finset.filter_subset _ _)
  have hRsector (p) (hp : p ∈ R) : p ∈ sector ![a, c, b] :=
    (Finset.mem_filter.mp (hRcap hp)).2
  let v : Fin 3 → Point := ![a, c, b]
  have hac : a ≠ c := by rintro rfl; simp [turn] at htri
  have hab : a ≠ b := by rintro rfl; simp at htri
  have hcb : c ≠ b := by rintro rfl; simp at htri
  have hinj : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have hvinner : ∀ i, v i ∈ inner S := by
    intro i
    fin_cases i <;> assumption
  have hchain : ∀ i : Fin 2, ∀ j : Fin 3,
      0 ≤ turn (v i.castSucc) (v i.succ) (v j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [v]
    · exact htri.le
    · rw [turn_rotate]
      exact htri.le
  have hcross : ∀ i : Fin 2, ∀ p ∈ R,
      0 ≤ turn (v i.castSucc) (v i.succ) p := by
    intro i p hp
    have h := hRsector p hp
    fin_cases i
    · exact (h 0 1 (by decide)).le
    · exact (h 1 2 (by decide)).le
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
  have hsupport (i : Fin 2) {p : Point} (hp : p ∈ convexHull ℝ (H : Set Point)) :
      0 ≤ turn (v i.castSucc) (v i.succ) p := by
    apply turn_nonneg_of_mem_convexHull (A := (H : Set Point)) _ hp
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hcross i q hq
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
      exact hchain i j
  refine ⟨H, hHS, ?_, ?_, ?_⟩
  · dsimp [H]
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hinj, hRcard]
    decide
  · exact convexPosition_splice_of_edge_supports hgen hR v hinj
      (fun i ↦ inner_subset S (hvinner i)) hchain hcross
  · intro p hp hpHull
    by_cases hpouter : p ∈ extremeLayer S
    · by_contra hpH
      exact extreme_not_mem_convexHull hpouter hHS hpH hpHull
    have hpinner : p ∈ inner S := Finset.mem_sdiff.mpr ⟨hp, hpouter⟩
    have hpTri : p ∈ triangleHull a c b := by
      apply weaklyInsideTriangle_mem_triangleHull htri
      refine ⟨hsupport 0 hpHull, hsupport 1 hpHull, ?_⟩
      rw [turn_swap_first]
      exact neg_nonneg.mpr (hbase p hpinner)
    rcases hempty p hpinner hpTri with rfl | rfl | rfl
    · exact hvH 0
    · exact hvH 1
    · exact hvH 2

theorem outer_sector_card_le_two {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S) {a c b : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (htri : 0 < turn a c b)
    (hbase : ∀ p ∈ inner S, turn a b p ≤ 0)
    (hempty : ∀ p ∈ inner S, p ∈ triangleHull a c b → p = a ∨ p = c ∨ p = b) :
    ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b])).card ≤ 2 := by
  by_contra h
  exact hno (emptyHexagon_of_three_outer_sector_points hgen ha hc hb htri hbase hempty
    (by omega))

/-- The nonconvex endpoint branch of the two-sector run bound. Here the
geometric supporting inequalities are conclusions, not additional
assumptions: the two strict triangle inclusions supply them. -/
theorem two_sectors_card_le_three_of_interior_endpoints {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hmin : MinimalOuter S) {a c b e f : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (he : e ∈ inner S) (hf : f ∈ inner S)
    (hcTri : StrictlyInsideTriangle a e b c)
    (heTri : StrictlyInsideTriangle b c f e)
    (hcard₁ : ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b])).card ≤ 2)
    (hcard₂ : ((extremeLayer S).filter (fun p ↦ p ∈ sector ![b, e, f])).card ≤ 2) :
    ((extremeLayer S).filter (fun p ↦
      p ∈ sector ![a, c, b] ∨ p ∈ sector ![b, e, f])).card ≤ 3 := by
  classical
  let U := (extremeLayer S).filter (fun p ↦
    p ∈ sector ![a, c, b] ∨ p ∈ sector ![b, e, f])
  let R := extremeLayer S \ U
  have hR : R ⊆ extremeLayer S := Finset.sdiff_subset
  have hU : U.card ≤ 4 := by
    have heq : U = (extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b]) ∪
        (extremeLayer S).filter (fun p ↦ p ∈ sector ![b, e, f]) := by
      ext p
      simp [U, and_or_left]
    rw [heq]
    exact (Finset.card_union_le _ _).trans (by omega)
  have hremoved : (extremeLayer S \ R).card ≤ 4 := by
    have hsub : extremeLayer S \ R ⊆ U := by
      intro p hp
      simp only [Finset.mem_sdiff, R] at hp
      tauto
    exact (Finset.card_le_card hsub).trans hU
  let v : Fin 4 → Point := ![a, c, e, f]
  have htri := two_sector_chain_clockwise hcTri heTri
  have h013 := htri 0 1 3 (by decide) (by decide)
  have h012 := htri 0 1 2 (by decide) (by decide)
  have h023 := htri 0 2 3 (by decide) (by decide)
  have h123 := htri 1 2 3 (by decide) (by decide)
  have hinj : Function.Injective v := by
    have h₁ : a ≠ c := by
      intro h
      have hh : turn a c e < 0 := h012
      simp [h, turn] at hh
    have h₂ : a ≠ e := by
      intro h
      have hh : turn a c e < 0 := h012
      simp [h] at hh
    have h₃ : a ≠ f := by
      intro h
      have hh : turn a c f < 0 := h013
      simp [h] at hh
    have h₄ : c ≠ e := by
      intro h
      have hh : turn a c e < 0 := h012
      simp [h, turn, mul_comm] at hh
    have h₅ : c ≠ f := by
      intro h
      have hh : turn a c f < 0 := h013
      simp [h, turn, mul_comm] at hh
    have h₆ : e ≠ f := by
      intro h
      have hh : turn c e f < 0 := h123
      simp [h, turn, mul_comm] at hh
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [v]
  have hmem : ∀ i, v i ∈ Lax56.ConvexLayers.inner S := by
    intro i
    fin_cases i <;> assumption
  have hchain : ∀ i : Fin 3, ∀ j : Fin 4,
      turn (v i.castSucc) (v i.succ) (v j) ≤ 0 := by
    intro i j
    by_cases hj₁ : j = i.castSucc
    · subst j; simp
    by_cases hj₂ : j = i.succ
    · subst j; simp
    have h := turn_consecutive_pos v (-1)
      (fun a b c hab hbc ↦ by simpa using htri a b c hab hbc)
      i.castSucc i.succ rfl j hj₁ hj₂
    simpa using h.le
  have hcross : ∀ i : Fin 3, ∀ p ∈ R,
      turn (v i.castSucc) (v i.succ) p ≤ 0 := by
    intro i p hp
    have hpout := extreme_not_mem_convexHull_inner (hR hp)
    have hnotTri {x y z : Point} (hx : x ∈ Lax56.ConvexLayers.inner S)
        (hy : y ∈ Lax56.ConvexLayers.inner S)
        (hz : z ∈ Lax56.ConvexLayers.inner S) : p ∉ triangleHull x y z := by
      intro h
      apply hpout
      apply convexHull_mono (t := (inner S : Set Point)) _ h
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> assumption
    have hs : p ∉ sector ![a, c, b] ∧ p ∉ sector ![b, e, f] := by
      have hh := (Finset.mem_sdiff.mp hp).2
      simpa only [U, Finset.mem_filter, hR hp, true_and, not_or] using hh
    have hsupport := two_sector_chain_support hcTri heTri
      (hnotTri ha hc hb) (hnotTri hb he hf) (hnotTri hc he hb) hs.1 hs.2
    fin_cases i
    · exact hsupport.1
    · exact hsupport.2.1
    · exact hsupport.2.2
  exact (not_minimal_of_supported_splice_clockwise hgen hR v hinj hmem
    hchain hcross hremoved hmin).elim

end Lax56Proofs.ValtrSectorBounds
