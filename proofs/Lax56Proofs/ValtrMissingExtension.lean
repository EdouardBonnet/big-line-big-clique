import Lax56Proofs.ValtrConvexRun

namespace Lax56Proofs.ValtrMissingExtension

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors Lax56Proofs.ValtrCyclic
open Lax56Proofs.ValtrMissing Lax56Proofs.ValtrConvexRun

/-- The pentagon obstruction behind Observation 4, using the actual
inner supporting edge crossed by a missing radial triangle. The chosen
empty triangle is inside the inner hull; hull closure transfers emptiness
back to the original ambient set before the outer point is adjoined. -/
theorem emptyHexagon_of_crossed_edge_four_sector {S Q : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hQ : HullClosedIn S Q)
    {u w d a b x : Point}
    (hu : u ∈ inner Q) (hw : w ∈ inner Q) (hd : d ∈ inner Q)
    (hdpos : 0 < turn u w d)
    (hCbase : ∀ p ∈ inner Q, 0 ≤ turn u w p)
    (ha : a ∈ extremeLayer Q) (hb : b ∈ extremeLayer Q)
    (haSector : a ∈ sector ![w, d, u]) (hbSector : b ∈ sector ![w, d, u])
    (hBbase : ∀ p ∈ inner Q, 0 < turn a b p)
    (hx : x ∈ S) (hxSector : x ∈ sector ![b, w, u, a]) : HasEmptyHexagon S := by
  have hgenQ : ¬HasThreeCollinear Q :=
    fun h ↦ hgen (hasThreeCollinear_mono hQ.1 h)
  have hgenI : ¬HasThreeCollinear (inner Q) :=
    fun h ↦ hgenQ (hasThreeCollinear_mono (inner_subset Q) h)
  obtain ⟨r, hr, hrTri, hrpos, hrEmpty⟩ := exists_empty_triangle_on_base hgenI hd hu hw hdpos
  have hru : r ≠ u := by rintro rfl; simp at hrpos
  have hrw : r ≠ w := by rintro rfl; simp at hrpos
  have hsector : sector ![w, d, u] ⊆ sector ![w, r, u] :=
    sector_triangle_mono (by rwa [triangleHull_swap_last]) hrw hru
  have hwrupos : 0 < turn w r u := by rw [turn_rotate]; exact hrpos
  have hempty : ∀ p ∈ inner Q, p ∈ triangleHull w r u → p = w ∨ p = r ∨ p = u := by
    intro p hp hpTri
    have hp' : p ∈ triangleHull r u w := by rwa [triangleHull_rotate]
    rcases hrEmpty p hp hp' with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  have horder : 0 < turn r a b := by rw [← turn_rotate]; exact hBbase r hr
  obtain ⟨hVin, hVtri, hVmem, hVempty⟩ := empty_pentagon_data_of_two_outer_sector_points
    hw hr hu hwrupos (fun p hp ↦ by rw [turn_swap_first]; exact neg_nonpos.mpr (hCbase p hp))
    hempty ha hb (hsector haSector) (hsector hbSector) horder
  let V : Fin 5 → Point := ![u, a, b, w, r]
  let v : Fin 5 → Point := ![b, w, r, u, a]
  have hshift (i : Fin 5) : v i = V (i + 2) := by fin_cases i <;> rfl
  have hvinj : Function.Injective v := by
    intro i j hij
    have h : V (i + 2) = V (j + 2) := by rwa [← hshift, ← hshift]
    exact add_right_cancel (hVin h)
  have hvtri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
    intro i j k hij hjk
    rw [hshift, hshift, hshift]
    exact cyclic_shift_triples hVtri (2 : Fin 5) i j k hij hjk
  have hvmem (i) : v i ∈ S := by rw [hshift]; exact hQ.1 (hVmem _)
  have hrange : Set.range v = Set.range V := by
    ext p
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i + 2, (hshift i).symm⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i - 2, ?_⟩
      rw [hshift, sub_add_cancel]
  have hvempty : ∀ p ∈ S, p ∈ convexHull ℝ (Set.range v) → p ∈ Set.range v := by
    intro p hp hpHull
    rw [hrange] at hpHull ⊢
    have hsub : Set.range V ⊆ (Q : Set Point) := by
      rintro p ⟨i, rfl⟩
      exact hVmem i
    exact hVempty p (hQ.2 p hp (convexHull_mono hsub hpHull)) hpHull
  exact empty_pentagon_extension hgen v hvinj hvtri hvmem hx hvempty hxSector

/-- A missing radial triangle determines an actual inner-polygon edge
whose four-sector contains no ambient point. This avoids assuming the
unique-edge assertion or the pentagon's emptiness from a diagram. -/
theorem exists_crossed_edge_four_sector_empty {S Q : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    (hQ : HullClosedIn S Q) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner Q) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d a b : Point} (hd : d ∈ inner (inner Q))
    (ha : a ∈ extremeLayer Q) (hb : b ∈ extremeLayer Q)
    (hBbase : ∀ p ∈ inner Q, 0 < turn a b p)
    (hempty : ∀ i, v i ∉ triangleHull d a b) :
    ∃ i, segment ℝ a b ⊆ sector ![v (i + 1), d, v i] ∧
      ∀ x ∈ S, x ∉ sector ![b, v (i + 1), v i, a] := by
  have hgenQ : ¬HasThreeCollinear Q :=
    fun h ↦ hgen (hasThreeCollinear_mono hQ.1 h)
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
  obtain ⟨i, hi⟩ := segment_subset_radial_sector_of_empty_triangle hgenQ hn v hinj htri
    hvQ hdQ hdHull hdnot (fun i ↦ hBbase _ (hvI i)) hempty
  refine ⟨i, hi, ?_⟩
  intro x hx hxSector
  apply hno
  apply emptyHexagon_of_crossed_edge_four_sector hgen hQ
    (hvI i) (hvI (i + 1)) hdI _ _ ha hb
    (hi (left_mem_segment ℝ a b)) (hi (right_mem_segment ℝ a b)) hBbase hx hxSector
  · exact cyclic_edge_strict_of_mem_hull hgenQ hn v hinj htri hvQ hdQ hdHull hdnot i
  · intro p hp
    apply cyclic_edge_nonneg_of_mem_hull htri _ i
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hp

end Lax56Proofs.ValtrMissingExtension
