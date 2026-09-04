import Lax56Proofs.HKBColouring
import Mathlib.Tactic

/-!
Geometric preparation for the finite empty-hexagon certificate.
-/

namespace Lax56Proofs.HKBHexGeometry

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.Blockers
open Lax56Proofs.Orientation
open Lax56Proofs.HKBGeometry

/-- The six vertices of a labelled hexagon. -/
noncomputable def hexVertices (h : Fin 6 → Point) : Finset Point :=
  Finset.univ.image h

/-- Points of `P` in the closed hexagon, excluding its vertices. -/
noncomputable def hexBlockers (P : Finset Point) (h : Fin 6 → Point) : Finset Point := by
  classical
  exact P.filter fun p => p ∈ convexHull ℝ (Set.range h) ∧ p ∉ Set.range h

/-- Strict membership in all six supporting half-planes. -/
def StrictlyInsideHexagon (h : Fin 6 → Point) (p : Point) : Prop :=
  ∀ i : Fin 6, 0 < turn (h i) (h (i + 1)) p

@[simp] theorem mem_hexVertices {h : Fin 6 → Point} {p : Point} :
    p ∈ hexVertices h ↔ p ∈ Set.range h := by
  classical
  simp [hexVertices]

@[simp] theorem mem_hexBlockers {P : Finset Point} {h : Fin 6 → Point}
    {p : Point} :
    p ∈ hexBlockers P h ↔
      p ∈ P ∧ p ∈ convexHull ℝ (Set.range h) ∧ p ∉ Set.range h := by
  classical
  simp [hexBlockers, and_assoc]

theorem hexVertices_card {h : Fin 6 → Point} (hinj : Function.Injective h) :
    (hexVertices h).card = 6 := by
  classical
  rw [hexVertices, Finset.card_image_of_injective _ hinj]
  simp

theorem hexBlockers_subset (P : Finset Point) (h : Fin 6 → Point) :
    hexBlockers P h ⊆ P := by
  intro p hp
  exact (mem_hexBlockers.mp hp).1

theorem hasFourCollinear_mono {A B : Finset Point} (hAB : A ⊆ B) :
    HasFourCollinear A → HasFourCollinear B := by
  rintro ⟨f, hf, hmem, hcol⟩
  exact ⟨f, hf, fun i => hAB (hmem i), hcol⟩

/-- Every pair of same-coloured hexagon vertices has a blocker belonging to
`hexBlockers`. -/
theorem exists_hexBlocker
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (C : (visibilityGraph P).Coloring (Fin 5))
    (c : Fin 5) (hsame : ∀ i, C ⟨h i, hhP i⟩ = c)
    {i j : Fin 6} (hij : i ≠ j) :
    ∃ r ∈ hexBlockers P h, r ∈ openSegment ℝ (h i) (h j) := by
  have hneq : h i ≠ h j := hh.1.ne hij
  have hnvis : ¬Visible P (h i) (h j) := by
    intro hv
    exact C.valid
      (show (visibilityGraph P).Adj ⟨h i, hhP i⟩ ⟨h j, hhP j⟩ from hv)
      (by rw [hsame i, hsame j])
  obtain ⟨r, hrP, hr⟩ := exists_blocker hneq hnvis
  refine ⟨r, mem_hexBlockers.mpr ⟨hrP, ?_, ?_⟩, hr⟩
  · exact (segment_subset_convexHull (Set.mem_range_self i) (Set.mem_range_self j))
      (openSegment_subset_segment ℝ _ _ hr)
  · rintro ⟨k, rfl⟩
    exact hexVertex_not_between_hexVertices hh hij k hr

private theorem other_colours_card (c : Fin 5) :
    Fintype.card {d : Fin 5 // d ≠ c} = 4 := by
  classical
  change Fintype.card {d : Fin 5 // ¬d = c} = 4
  rw [Fintype.card_subtype_compl (fun d : Fin 5 => d = c),
    Fintype.card_subtype_eq]
  simp

/-- A fixed renaming of the four colours other than `c`. -/
noncomputable def otherColourEquiv (c : Fin 5) :
    {d : Fin 5 // d ≠ c} ≃ Fin 4 :=
  (Fintype.equivFin {d : Fin 5 // d ≠ c}).trans (finCongr (other_colours_card c))

/-- The induced four-colouring of the points inside the empty monochromatic
hexagon. -/
noncomputable def blockerColour
    {P : Finset Point} {h : Fin 6 → Point}
    (C : (visibilityGraph P).Coloring (Fin 5)) (c : Fin 5)
    (hnotc : ∀ p : hexBlockers P h,
      C ⟨p, hexBlockers_subset P h p.property⟩ ≠ c)
    (p : hexBlockers P h) : Fin 4 :=
  otherColourEquiv c
    ⟨C ⟨p, hexBlockers_subset P h p.property⟩, hnotc p⟩

/-- Choose one blocker in the relative interior of every side. -/
noncomputable def sideBlocker
    {B : Finset Point} {h : Fin 6 → Point}
    (hside : ∀ i : Fin 6,
      ∃ r ∈ B, r ∈ openSegment ℝ (h i) (h (i + 1)))
    (i : Fin 6) : Point :=
  Classical.choose (hside i)

theorem sideBlocker_mem
    {B : Finset Point} {h : Fin 6 → Point}
    (hside : ∀ i : Fin 6,
      ∃ r ∈ B, r ∈ openSegment ℝ (h i) (h (i + 1)))
    (i : Fin 6) : sideBlocker hside i ∈ B :=
  (Classical.choose_spec (hside i)).1

theorem sideBlocker_between
    {B : Finset Point} {h : Fin 6 → Point}
    (hside : ∀ i : Fin 6,
      ∃ r ∈ B, r ∈ openSegment ℝ (h i) (h (i + 1)))
    (i : Fin 6) :
    sideBlocker hside i ∈ openSegment ℝ (h i) (h (i + 1)) :=
  (Classical.choose_spec (hside i)).2

theorem sideBlocker_injective
    {B : Finset Point} {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ B, r ∈ openSegment ℝ (h i) (h (i + 1))) :
    Function.Injective (sideBlocker hside) := by
  intro i j hij
  by_contra hne
  exact (Set.disjoint_left.mp (side_openSegments_disjoint hh hne))
    (sideBlocker_between hside i)
    (by simpa [hij] using sideBlocker_between hside j)

open Classical in
/-- Under the no-four-collinear hypothesis, the only non-strict points of
`hexBlockers` are the six chosen side blockers. -/
theorem not_strictlyInside_iff_sideBlocker
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1)))
    {p : Point} (hp : p ∈ hexBlockers P h) :
    ¬StrictlyInsideHexagon h p ↔ ∃ i, p = sideBlocker hside i := by
  constructor
  · intro hn
    unfold StrictlyInsideHexagon at hn
    push Not at hn
    obtain ⟨i, hi⟩ := hn
    have hpdata := mem_hexBlockers.mp hp
    have hpnonneg := edgeTurn_nonneg_of_mem_convexHull hh hpdata.2.1 i
    have hpzero : turn (h i) (h (i + 1)) p = 0 := le_antisymm hi hpnonneg
    let s := sideBlocker hside i
    have hsP : s ∈ P := hexBlockers_subset P h (sideBlocker_mem hside i)
    have hsseg : s ∈ openSegment ℝ (h i) (h (i + 1)) :=
      sideBlocker_between hside i
    have hisucc : h i ≠ h (i + 1) := by
      apply hh.1.ne
      fin_cases i <;> decide
    have hpi : p ≠ h i := by
      intro e
      exact hpdata.2.2 ⟨i, e.symm⟩
    have hpis : p ≠ h (i + 1) := by
      intro e
      exact hpdata.2.2 ⟨i + 1, e.symm⟩
    have hsi : s ≠ h i := by
      intro e
      have hleft : h i ∈ openSegment ℝ (h i) (h (i + 1)) := by
        simpa [e] using hsseg
      exact hisucc ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hleft)
    have hsis : s ≠ h (i + 1) := by
      intro e
      have hright : h (i + 1) ∈ openSegment ℝ (h i) (h (i + 1)) := by
        simpa [e] using hsseg
      exact hisucc ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hright)
    refine ⟨i, third_point_unique hfour (hhP i) (hhP (i + 1))
      (hexBlockers_subset P h hp) hsP hisucc hpi hpis hsi hsis ?_ ?_⟩
    · exact mem_line_of_turn_eq_zero hisucc hpzero
    · exact mem_affineSpan_pair_of_mem_openSegment hsseg
  · rintro ⟨i, rfl⟩ hinner
    have hz : turn (h i) (h (i + 1)) (sideBlocker hside i) = 0 := by
      rw [turn_swap_last, turn_eq_zero_of_mem_openSegment
        (sideBlocker_between hside i), neg_zero]
    exact (ne_of_gt (hinner i)) hz

open Classical in
/-- Exactly `B.card - 6` blockers are strict interior points. -/
theorem strictInteriorBlockers_card
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6,
      ∃ r ∈ hexBlockers P h,
        r ∈ openSegment ℝ (h i) (h (i + 1))) :
    ((hexBlockers P h).filter (StrictlyInsideHexagon h)).card =
      (hexBlockers P h).card - 6 := by
  classical
  let B := hexBlockers P h
  let inside := StrictlyInsideHexagon h
  have hout :
      B.filter (fun p => ¬inside p) =
        Finset.univ.image (sideBlocker hside) := by
    ext p
    constructor
    · intro hp
      have hpB : p ∈ B := (Finset.mem_filter.mp hp).1
      have hn : ¬inside p := (Finset.mem_filter.mp hp).2
      obtain ⟨i, rfl⟩ :=
        (not_strictlyInside_iff_sideBlocker hfour hh hhP hside hpB).mp hn
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    · intro hp
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨sideBlocker_mem hside i,
        (not_strictlyInside_iff_sideBlocker hfour hh hhP hside
          (sideBlocker_mem hside i)).mpr ⟨i, rfl⟩⟩
  have houtcard : (B.filter fun p => ¬inside p).card = 6 := by
    rw [hout, Finset.card_image_of_injective _ (sideBlocker_injective hh hside)]
    simp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := B) (p := inside)
  change (B.filter inside).card = B.card - 6
  omega

end Lax56Proofs.HKBHexGeometry
