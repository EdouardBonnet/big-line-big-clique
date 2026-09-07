import Lax56Proofs.ValtrShortSetup

namespace Lax56Proofs.ValtrSectorArcs

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrConvexRun
open scoped Classical

theorem outer_ne_inner {S : Finset Point} {x p : Point}
    (hx : x ∈ extremeLayer S) (hp : p ∈ inner S) : x ≠ p := by
  intro hh
  exact (Finset.mem_sdiff.mp hp).2 (hh ▸ hx)

/-- An outer vertex between two other outer vertices in boundary order
also lies between their rays from an inner point, provided the shorter
radial arc is the boundary arc under consideration. -/
theorem radial_sides_of_outer_triple {S : Finset Point} {c q w r : Point}
    (hc : c ∈ inner S) (hq : q ∈ extremeLayer S) (hw : w ∈ extremeLayer S)
    (hr : r ∈ extremeLayer S) (hcycle : 0 < turn q w r) (hqr : 0 < turn c q r) :
    0 < turn c q w ∧ 0 < turn c w r := by
  have hqw : q ≠ w := by rintro rfl; simp [turn] at hcycle
  have hwr : w ≠ r := by rintro rfl; simp at hcycle
  have hqrne : q ≠ r := by rintro rfl; simp at hqr
  have hid : turn q w r = turn c q w + turn c w r - turn c q r := by unfold turn; ring
  have hfirst : 0 < turn c q w := by
    by_contra hh
    have hh := le_of_not_gt hh
    have htri : 0 < turn c w r := by linarith
    apply extreme_not_mem_triangle hq (inner_subset _ hc)
      (extremeLayer_subset _ hw) (extremeLayer_subset _ hr)
      (outer_ne_inner hq hc) hqw hqrne
    apply weaklyInsideTriangle_mem_triangleHull htri
    refine ⟨?_, ?_, ?_⟩
    · rw [turn_swap_last]; exact neg_nonneg.mpr hh
    · rw [turn_rotate]; exact hcycle.le
    · convert hqr.le using 1 <;> unfold turn <;> ring
  refine ⟨hfirst, ?_⟩
  by_contra hh
  have hh := le_of_not_gt hh
  apply extreme_not_mem_triangle hr (inner_subset _ hc)
    (extremeLayer_subset _ hq) (extremeLayer_subset _ hw)
    (outer_ne_inner hr hc) hqrne.symm hwr.symm
  apply weaklyInsideTriangle_mem_triangleHull hfirst
  refine ⟨hqr.le, hcycle.le, ?_⟩
  rw [turn_swap_first]
  exact neg_nonneg.mpr hh

/-- On the outer layer the two ray tests already imply the base-line
test: failure of the third test would put the outer vertex in the inner
base triangle. -/
theorem sector_of_outer_ray_tests {S : Finset Point} {a c b w : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (htri : 0 < turn a c b) (hw : w ∈ extremeLayer S)
    (hacw : 0 < turn a c w) (hcbw : 0 < turn c b w) : w ∈ sector ![a, c, b] := by
  have habw : 0 < turn a b w := by
    by_contra hh
    apply extreme_not_mem_triangle hw (inner_subset _ ha) (inner_subset _ hc)
      (inner_subset _ hb) (outer_ne_inner hw ha) (outer_ne_inner hw hc) (outer_ne_inner hw hb)
    apply weaklyInsideTriangle_mem_triangleHull htri
    refine ⟨hacw.le, hcbw.le, ?_⟩
    rw [turn_swap_first]
    exact neg_nonneg.mpr (le_of_not_gt hh)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- The outer-boundary arc between two points of a sector stays in the
sector. This finite oriented version avoids introducing topological arcs
or angular coordinates. -/
theorem sector_arc {S : Finset Point} {a c b q w r : Point}
    (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (htri : 0 < turn a c b) (hq : q ∈ extremeLayer S)
    (hw : w ∈ extremeLayer S) (hr : r ∈ extremeLayer S)
    (hqS : q ∈ sector ![a, c, b]) (hrS : r ∈ sector ![a, c, b])
    (hcycle : 0 < turn q w r) (hqr : 0 < turn c q r) : w ∈ sector ![a, c, b] := by
  obtain ⟨hqw, hwr⟩ := radial_sides_of_outer_triple hc hq hw hr hcycle hqr
  apply sector_of_outer_ray_tests ha hc hb htri hw
  · apply (mul_pos_iff_of_pos_left hqr).mp
    have hid : turn c q r * turn a c w =
        turn c w r * turn a c q + turn c q w * turn a c r := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos hwr (hqS 0 1 (by decide))) (mul_pos hqw (hrS 0 1 (by decide)))
  · apply (mul_pos_iff_of_pos_left hqr).mp
    have hid : turn c q r * turn c b w =
        turn c w r * turn c b q + turn c q w * turn c b r := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos hwr (hqS 1 2 (by decide))) (mul_pos hqw (hrS 1 2 (by decide)))

/-- A sector containing two outer vertices and no third outer vertex
can only join neighbors on the outer polygon. The distinguished endpoint
is indexed by zero. -/
theorem two_point_sector_neighbor {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hmem : ∀ i, v i ∈ extremeLayer S)
    (hcycle : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {a c b : Point} (ha : a ∈ inner S) (hc : c ∈ inner S) (hb : b ∈ inner S)
    (htri : 0 < turn a c b) {j : Fin n} (hj : j ≠ 0)
    (hzero : v 0 ∈ sector ![a, c, b]) (hjS : v j ∈ sector ![a, c, b])
    (hcard : ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a, c, b])).card ≤ 2) :
    j.val = 1 ∨ j.val + 1 = n := by
  by_contra hh
  have hh₁ : j.val ≠ 1 := fun h ↦ hh (Or.inl h)
  have hh₂ : j.val + 1 ≠ n := fun h ↦ hh (Or.inr h)
  have hjv : j.val ≠ 0 := fun h ↦ hj (Fin.ext h)
  have hthird (i : Fin n) (hi0 : i ≠ 0) (hij : i ≠ j)
      (hiS : v i ∈ sector ![a, c, b]) : False := by
    apply (not_lt_of_ge hcard)
    apply Finset.two_lt_card.mpr
    exact ⟨v 0, Finset.mem_filter.mpr ⟨hmem 0, hzero⟩,
      v j, Finset.mem_filter.mpr ⟨hmem j, hjS⟩,
      v i, Finset.mem_filter.mpr ⟨hmem i, hiS⟩,
      hinj.ne hj.symm, hinj.ne hi0.symm, hinj.ne hij.symm⟩
  have hne : turn c (v 0) (v j) ≠ 0 := turn_ne_zero_of_generalPosition hgen
    (inner_subset _ hc) (extremeLayer_subset _ (hmem 0)) (extremeLayer_subset _ (hmem j))
    (outer_ne_inner (hmem 0) hc).symm (outer_ne_inner (hmem j) hc).symm (hinj.ne hj.symm)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · let last : Fin n := ⟨n - 1, by omega⟩
    have hlast0 : last ≠ 0 := fun heq ↦ by
      have hv := congrArg Fin.val heq
      change n - 1 = 0 at hv
      omega
    have hlastj : last ≠ j := fun heq ↦ by
      have hv := congrArg Fin.val heq
      change n - 1 = j.val at hv
      omega
    apply hthird last hlast0 hlastj
    apply sector_arc ha hc hb htri (hmem j) (hmem last) (hmem 0) hjS hzero
    · rw [turn_rotate]
      exact hcycle 0 j last (by change 0 < j.val; omega) (by change j.val < n - 1; omega)
    · rw [turn_swap_last]; exact neg_pos.mpr hneg
  · let first : Fin n := ⟨1, by omega⟩
    have hfirst0 : first ≠ 0 := fun heq ↦ by
      have hv := congrArg Fin.val heq
      change 1 = 0 at hv
      omega
    have hfirstj : first ≠ j := fun heq ↦ by
      have hv := congrArg Fin.val heq
      change 1 = j.val at hv
      omega
    apply hthird first hfirst0 hfirstj
    exact sector_arc ha hc hb htri (hmem 0) (hmem first) (hmem j) hzero hjS
      (hcycle 0 first j (by change 0 < 1; decide) (by change 1 < j.val; omega)) hpos

/-- If each sector has a distinct designated outer point and at most
two outer points in total, any further outer point belongs to at most
two sectors. Both possible designated points are boundary neighbors of
that further point. -/
theorem sector_multiplicity_le_two {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    (hsize : 3 ≤ (extremeLayer S).card) {ι : Type*} [Fintype ι]
    (a c b u : ι → Point) {x : Point} (hx : x ∈ extremeLayer S)
    (ha : ∀ i, a i ∈ inner S) (hc : ∀ i, c i ∈ inner S) (hb : ∀ i, b i ∈ inner S)
    (htri : ∀ i, 0 < turn (a i) (c i) (b i))
    (hu : ∀ i, u i ∈ extremeLayer S) (huinj : Function.Injective u)
    (hux : ∀ i, u i ≠ x) (huS : ∀ i, u i ∈ sector ![a i, c i, b i])
    (hcard : ∀ i, ((extremeLayer S).filter (fun p ↦ p ∈ sector ![a i, c i, b i])).card ≤ 2) :
    (Finset.univ.filter (fun i ↦ x ∈ sector ![a i, c i, b i])).card ≤ 2 := by
  classical
  let N := (extremeLayer S).card
  letI : NeZero N := ⟨by dsimp [N]; omega⟩
  have hgenA : ¬HasThreeCollinear (extremeLayer S) := fun hh ↦
    hgen (hasThreeCollinear_mono (extremeLayer_subset S) hh)
  obtain ⟨v, hinj, hrange, hcycle⟩ := Lax56Proofs.CyclicOrder.exists_cyclic_order_card
    (extremeLayer S) ⟨x, hx⟩ (extremeLayer_convexPosition S) hgenA
  obtain ⟨j, hj⟩ : ∃ j, v j = x := Set.mem_range.mp (hrange.symm ▸ hx)
  let w : Fin N → Point := fun i ↦ v (i + j)
  have hwinj : Function.Injective w := fun i k hh ↦ add_right_cancel (hinj hh)
  have hwRange : Set.range w = (extremeLayer S : Set Point) :=
    (Lax56Proofs.ValtrMatching.range_cyclic_shift v j).trans hrange
  have hw0 : w 0 = x := by simpa [w] using hj
  have hwmem (i) : w i ∈ extremeLayer S := by
    change w i ∈ (extremeLayer S : Set Point)
    rw [← hwRange]
    exact Set.mem_range_self i
  have hwcycle : ∀ i k l, i < k → k < l → 0 < turn (w i) (w k) (w l) :=
    cyclic_shift_triples hcycle j
  let T := Finset.univ.filter (fun i ↦ x ∈ sector ![a i, c i, b i])
  let first : Fin N := ⟨1, by dsimp [N]; omega⟩
  let last : Fin N := ⟨N - 1, by dsimp [N]; omega⟩
  have hsub : T.image u ⊆ {w first, w last} := by
    intro p hp
    obtain ⟨i, hiT, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨k, hk⟩ : ∃ k, w k = u i := Set.mem_range.mp (hwRange.symm ▸ hu i)
    have hk0 : k ≠ 0 := by
      intro heq
      apply hux i
      rw [← hk, heq, hw0]
    have hz : w 0 ∈ sector ![a i, c i, b i] := by
      rw [hw0]
      exact (Finset.mem_filter.mp hiT).2
    have hkS : w k ∈ sector ![a i, c i, b i] := by rw [hk]; exact huS i
    have hnear := two_point_sector_neighbor hgen hsize w hwinj hwmem hwcycle
      (ha i) (hc i) (hb i) (htri i) hk0 hz hkS (hcard i)
    rw [Finset.mem_insert, Finset.mem_singleton, ← hk]
    rcases hnear with hnear | hnear
    · exact Or.inl (congrArg w (Fin.ext hnear))
    · apply Or.inr
      apply congrArg w
      apply Fin.ext
      change k.val = N - 1
      omega
  calc
    T.card = (T.image u).card := (Finset.card_image_of_injective _ huinj).symm
    _ ≤ ({w first, w last} : Finset Point).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

end Lax56Proofs.ValtrSectorArcs
