import Lax56Proofs.ErdosSzekeres
import Lax56Proofs.HKBTriangle

namespace Lax56Proofs.CyclicOrder

set_option maxHeartbeats 1000000

open Lax56.Geometry Lax56.ConvexLayers Lax56.HujterKisfaludiBak
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry Lax56Proofs.ErdosSzekeres
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrReduction

noncomputable def slope (p q : Point) : ℝ := (q.2 - p.2) / (q.1 - p.1)

theorem turn_pos_of_slope_lt {p a b : Point} (ha : p.1 < a.1) (hb : p.1 < b.1)
    (hs : slope p a < slope p b) : 0 < turn p a b := by
  have h := (div_lt_div_iff₀ (sub_pos.mpr ha) (sub_pos.mpr hb)).mp hs
  unfold turn
  nlinarith

theorem slope_injective_right {P : Finset Point} (hgen : ¬HasThreeCollinear P)
    {p : Point} (hp : p ∈ P) (hmin : ∀ a ∈ P.erase p, p.1 < a.1) :
    Function.Injective (fun a : P.erase p ↦ slope p a.val) := by
  intro a b heq
  apply Subtype.ext
  by_contra hab
  have ha := Finset.mem_erase.mp a.property
  have hb := Finset.mem_erase.mp b.property
  have hz := (div_eq_div_iff (ne_of_gt (sub_pos.mpr (hmin a.val a.property)))
    (ne_of_gt (sub_pos.mpr (hmin b.val b.property)))).mp heq
  apply turn_ne_zero_of_generalPosition hgen hp ha.2 hb.2 ha.1.symm hb.1.symm hab
  unfold turn
  nlinarith

/-- Sorting by polar slope around a leftmost vertex gives the cyclic order
of a finite set in convex position. A reversed triple would put its middle
vertex in the triangle spanned by the pivot and the other two vertices. -/
theorem exists_cyclic_order_of_strict_x (P : Finset Point) (hP : P.Nonempty)
    (hconv : ConvexPosition P) (hgen : ¬HasThreeCollinear P)
    (hxinj : ∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q) :
    ∃ n : ℕ, n + 1 = P.card ∧ ∃ v : Fin (n + 1) → Point,
      Function.Injective v ∧ Set.range v = (P : Set Point) ∧
      ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
  classical
  obtain ⟨p, hp, hmin⟩ := P.exists_min_image Prod.fst hP
  let A := P.erase p
  have hxmin : ∀ a ∈ A, p.1 < a.1 := by
    intro a ha
    have hamem := Finset.mem_erase.mp ha
    have hle := hmin a hamem.2
    rcases hle.eq_or_lt with h | h
    · exact (hamem.1 (hxinj a hamem.2 p hp h.symm)).elim
    · exact h
  let ord : LinearOrder A := LinearOrder.lift' (fun a : A ↦ slope p a.val)
    (slope_injective_right hgen hp hxmin)
  letI : LinearOrder A := ord
  letI : PartialOrder A := ord.toPartialOrder
  letI : Preorder A := ord.toPreorder
  letI : LE A := ord.toLE
  letI : LT A := ord.toLT
  let e := Fintype.orderIsoFinOfCardEq A (Fintype.card_coe A)
  let w : Fin A.card → Point := fun i ↦ (e i).val
  let v : Fin (A.card + 1) → Point := Fin.cons p w
  have hwmem : ∀ i, w i ∈ A := fun i ↦ (e i).property
  have hwinj : Function.Injective w := Subtype.val_injective.comp e.injective
  have hpolar : ∀ i j, i < j → 0 < turn p (w i) (w j) := by
    intro i j hij
    exact turn_pos_of_slope_lt (hxmin _ (hwmem i)) (hxmin _ (hwmem j)) (e.strictMono hij)
  have htriples : ∀ i j k, i < j → j < k → 0 < turn (w i) (w j) (w k) := by
    intro i j k hij hjk
    by_contra hbad
    have hle : turn (w i) (w j) (w k) ≤ 0 := le_of_not_gt hbad
    have hinside : w j ∈ triangleHull p (w i) (w k) := by
      apply weaklyInsideTriangle_mem_triangleHull (hpolar i k (hij.trans hjk))
      refine ⟨(hpolar i j hij).le, ?_, ?_⟩
      · rw [turn_swap_last]
        linarith
      · rw [← turn_rotate (w k) p (w j)]
        exact (hpolar j k hjk).le
    apply (convexPosition_iff P).mp hconv (w j) (Finset.mem_of_mem_erase (hwmem j))
    apply convexHull_mono (s := ({p, w i, w k} : Set Point)) _ hinside
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hp, fun h ↦ (Finset.mem_erase.mp (hwmem j)).1 h.symm⟩
    · exact ⟨Finset.mem_of_mem_erase (hwmem i), hwinj.ne (ne_of_lt hij)⟩
    · exact ⟨Finset.mem_of_mem_erase (hwmem k), hwinj.ne (ne_of_gt hjk)⟩
  refine ⟨A.card, Finset.card_erase_add_one hp, v, ?_, ?_, ?_⟩
  · apply Fin.cons_injective_iff.mpr
    refine ⟨?_, hwinj⟩
    rintro ⟨i, hi⟩
    exact (Finset.mem_erase.mp (hwmem i)).1 hi
  · ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine Fin.cases hp (fun j ↦ Finset.mem_of_mem_erase (hwmem j)) i
    · intro hx
      by_cases hxp : x = p
      · exact ⟨0, by simp [v, hxp]⟩
      · let a : A := ⟨x, Finset.mem_erase.mpr ⟨hxp, hx⟩⟩
        exact ⟨(e.symm a).succ, by simp [v, w, a]⟩
  · intro i j k hij hjk
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        cases k using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hjk).elim
        | succ k => exact hpolar j k (Fin.succ_lt_succ_iff.mp hjk)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (Fin.not_lt_zero _ hij).elim
      | succ j =>
        cases k using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hjk).elim
        | succ k => exact htriples i j k (Fin.succ_lt_succ_iff.mp hij) (Fin.succ_lt_succ_iff.mp hjk)

@[simp] theorem turn_shearEquiv (t : ℝ) (a b c : Point) :
    turn (shearEquiv t a) (shearEquiv t b) (shearEquiv t c) = turn a b c := by
  change turn (a.1 + t * a.2, a.2) (b.1 + t * b.2, b.2) (c.1 + t * c.2, c.2) = _
  unfold turn
  ring

/-- Cyclic ordering in the original coordinates, after undoing the shear. -/
theorem exists_cyclic_order (P : Finset Point) (hP : P.Nonempty)
    (hconv : ConvexPosition P) (hgen : ¬HasThreeCollinear P) :
    ∃ n : ℕ, n + 1 = P.card ∧ ∃ v : Fin (n + 1) → Point,
      Function.Injective v ∧ Set.range v = (P : Set Point) ∧
      ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
  classical
  obtain ⟨t, ht⟩ := exists_separating_shear P
  let e := shearEquiv t
  let Q := P.image e
  have hQx : ∀ p ∈ Q, ∀ q ∈ Q, p.1 = q.1 → p = q := by
    intro p hp q hq hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg e (ht a ha b hb hx)
  obtain ⟨n, hn, v, hinj, hrange, htri⟩ := exists_cyclic_order_of_strict_x Q
    (hP.image e) (convexPosition_image e hconv) (generalPosition_image e hgen) hQx
  have hQcard : Q.card = P.card := Finset.card_image_of_injective _ e.injective
  refine ⟨n, hn.trans hQcard, e.symm ∘ v, e.symm.injective.comp hinj, ?_, ?_⟩
  · rw [Set.range_comp, hrange]
    simp [Q, Finset.coe_image, Set.image_image]
  · intro i j k hij hjk
    have h := htri i j k hij hjk
    have heq := turn_shearEquiv t (e.symm (v i)) (e.symm (v j)) (e.symm (v k))
    change turn (e (e.symm (v i))) (e (e.symm (v j))) (e (e.symm (v k))) = _ at heq
    simp only [LinearEquiv.apply_symm_apply] at heq
    simpa only [Function.comp_apply, ← heq] using h

/-- Cardinality-indexed version, convenient for splitting a polygon into blocks. -/
theorem exists_cyclic_order_card (P : Finset Point) (hP : P.Nonempty)
    (hconv : ConvexPosition P) (hgen : ¬HasThreeCollinear P) :
    ∃ v : Fin P.card → Point, Function.Injective v ∧ Set.range v = (P : Set Point) ∧
      ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
  obtain ⟨n, hn, v, hinj, hrange, htri⟩ := exists_cyclic_order P hP hconv hgen
  let w : Fin P.card → Point := fun i ↦ v (Fin.cast hn.symm i)
  refine ⟨w, hinj.comp (Fin.cast_injective _), ?_, ?_⟩
  · rw [← hrange]
    apply Set.Subset.antisymm
    · rintro x ⟨i, rfl⟩
      exact ⟨Fin.cast hn.symm i, rfl⟩
    · rintro x ⟨i, rfl⟩
      exact ⟨Fin.cast hn i, by simp [w]⟩
  · intro i j k hij hjk
    exact htri _ _ _ hij hjk

theorem strictConvexHexagon_of_triples (v : Fin 6 → Point) (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) :
    StrictConvexHexagon v := by
  refine ⟨hinj, ?_, htri⟩
  intro i j hji hjnext
  by_cases hi : i = 5
  · subst i
    have hj0 : (0 : Fin 6) < j := by omega
    have hj5 : j < (5 : Fin 6) := by omega
    have h := htri 0 j 5 hj0 hj5
    change 0 < turn (v 5) (v 0) (v j)
    rw [← turn_rotate (v 5) (v 0) (v j)]
    exact h
  · have hi5 : i.val < 5 := by omega
    have hadj : i.val + 1 = (i + 1).val := by omega
    simpa only [one_mul] using turn_consecutive_pos v 1
      (by simpa only [one_mul] using htri) i (i + 1) hadj j hji hjnext

/-- A six-vertex convex polygon is the intersection of its supporting
half-planes. The proof locates the point in one of the four triangles of
the fan rooted at vertex zero. -/
theorem mem_convexHull_hexagon_of_edge_nonneg {v : Fin 6 → Point}
    (hv : StrictConvexHexagon v) {p : Point}
    (hp : ∀ i, 0 ≤ turn (v i) (v (i + 1)) p) : p ∈ convexHull ℝ (Set.range v) := by
  have hfan (i j : Fin 6) (hi : 0 < i) (hij : i < j)
      (hleft : 0 ≤ turn (v 0) (v i) p)
      (hedge : 0 ≤ turn (v i) (v j) p)
      (hright : turn (v 0) (v j) p ≤ 0) : p ∈ convexHull ℝ (Set.range v) := by
    have hinside : p ∈ triangleHull (v 0) (v i) (v j) := by
      apply weaklyInsideTriangle_mem_triangleHull (hv.2.2 0 i j hi hij)
      refine ⟨hleft, hedge, ?_⟩
      rw [turn_swap_first]
      linarith
    apply convexHull_mono (s := ({v 0, v i, v j} : Set Point)) _ hinside
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> exact Set.mem_range_self _
  by_cases h₂ : turn (v 0) (v 2) p ≤ 0
  · exact hfan 1 2 (by decide) (by decide) (hp 0) (hp 1) h₂
  by_cases h₃ : turn (v 0) (v 3) p ≤ 0
  · exact hfan 2 3 (by decide) (by decide) (le_of_not_ge h₂) (hp 2) h₃
  by_cases h₄ : turn (v 0) (v 4) p ≤ 0
  · exact hfan 3 4 (by decide) (by decide) (le_of_not_ge h₃) (hp 3) h₄
  have h₅ : turn (v 0) (v 5) p ≤ 0 := by
    have h := hp 5
    change 0 ≤ turn (v 5) (v 0) p at h
    rw [turn_swap_first] at h
    linarith
  exact hfan 4 5 (by decide) (by decide) (le_of_not_ge h₄) (hp 4) h₅

/-- The unordered-to-labelled hexagon bridge is now a theorem, not an axiom. -/
theorem ordered_hexagon_bridge : OrderedHexagonBridge := by
  classical
  intro P hgen hhex
  obtain ⟨H, hHP, hcard, hconv, hempty⟩ := hhex
  have hHgen : ¬HasThreeCollinear H := fun h ↦ hgen (hasThreeCollinear_mono hHP h)
  obtain ⟨n, hn, v, hinj, hrange, htri⟩ := exists_cyclic_order H
    (Finset.card_pos.mp (by omega)) hconv hHgen
  have hn6 : n + 1 = 6 := hn.trans hcard
  let h : Fin 6 → Point := fun i ↦ v (Fin.cast hn6.symm i)
  have hhtri : ∀ i j k, i < j → j < k → 0 < turn (h i) (h j) (h k) := by
    intro i j k hij hjk
    exact htri _ _ _ hij hjk
  have hhinj : Function.Injective h := hinj.comp (Fin.cast_injective _)
  have hhrange : Set.range h = (H : Set Point) := by
    rw [← hrange]
    apply Set.Subset.antisymm
    · rintro x ⟨i, rfl⟩
      exact ⟨Fin.cast hn6.symm i, rfl⟩
    · rintro x ⟨i, rfl⟩
      exact ⟨Fin.cast hn6 i, by simp [h]⟩
  refine ⟨h, strictConvexHexagon_of_triples h hhinj hhtri, ?_, ?_⟩
  · intro i
    apply hHP
    change h i ∈ (H : Set Point)
    rw [← hhrange]
    exact Set.mem_range_self _
  · intro p hp hh
    rw [hhrange] at hh ⊢
    exact hempty p hp hh

end Lax56Proofs.CyclicOrder
