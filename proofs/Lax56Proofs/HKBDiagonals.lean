import Lax56Proofs.HKBColourCoverage
import Mathlib.Tactic

/-!
Incidence counting for the nine proper diagonals of a strict convex hexagon.
-/

namespace Lax56Proofs.HKBDiagonals

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.Orientation

/-- The nine unordered non-side pairs, listed with the smaller endpoint first. -/
def diagonalEnds : Fin 9 → Fin 6 × Fin 6 := ![
  (0, 2), (0, 3), (0, 4),
  (1, 3), (1, 4), (1, 5),
  (2, 4), (2, 5), (3, 5)]

theorem diagonalEnds_injective : Function.Injective diagonalEnds := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [diagonalEnds]

theorem diagonalEnds_lt (i : Fin 9) :
    (diagonalEnds i).1 < (diagonalEnds i).2 := by
  fin_cases i <;> decide

theorem diagonalEnds_ne (i : Fin 9) :
    (diagonalEnds i).1 ≠ (diagonalEnds i).2 :=
  (diagonalEnds_lt i).ne

theorem diagonalEnds_nonadjacent (i : Fin 9) :
    (diagonalEnds i).2 ≠ (diagonalEnds i).1 + 1 ∧
      (diagonalEnds i).1 ≠ (diagonalEnds i).2 + 1 := by
  fin_cases i <;> decide

/-- The endpoint pairs of two diagonals are disjoint. -/
def DisjointEnds (i j : Fin 9) : Prop :=
  (diagonalEnds i).1 ≠ (diagonalEnds j).1 ∧
  (diagonalEnds i).1 ≠ (diagonalEnds j).2 ∧
  (diagonalEnds i).2 ≠ (diagonalEnds j).1 ∧
  (diagonalEnds i).2 ≠ (diagonalEnds j).2

instance instDecidableDisjointEnds (i j : Fin 9) : Decidable (DisjointEnds i j) := by
  unfold DisjointEnds
  infer_instance

/-- Two chords through a common first hexagon vertex and a common interior
point have the same other endpoint.  The no-four-collinear hypothesis is
what rules out two different chord lines coinciding. -/
theorem same_right_of_common_left_chords
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    {a b c : Fin 6} {x : Point}
    (hab : a ≠ b) (hac : a ≠ c) (hxP : x ∈ P)
    (hxb : x ∈ openSegment ℝ (h a) (h b))
    (hxc : x ∈ openSegment ℝ (h a) (h c)) :
    b = c := by
  have habp : h a ≠ h b := hh.1.ne hab
  have hacp : h a ≠ h c := hh.1.ne hac
  have hax : h a ≠ x := by
    intro e
    have haopen : h a ∈ openSegment ℝ (h a) (h b) := by
      simpa [e] using hxb
    exact habp ((left_mem_openSegment_iff (𝕜 := ℝ)).mp haopen)
  have hbx : h b ≠ x := by
    intro e
    have hbopen : h b ∈ openSegment ℝ (h a) (h b) := by
      simpa [e] using hxb
    exact habp ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hbopen)
  have hcx : h c ≠ x := by
    intro e
    have hcopen : h c ∈ openSegment ℝ (h a) (h c) := by
      simpa [e] using hxc
    exact hacp ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hcopen)
  have hbeq : h b = h c :=
    third_point_unique hfour (hhP a) hxP (hhP b) (hhP c)
      hax habp.symm hbx hacp.symm hcx
      (right_mem_affineSpan_pair_of_between habp hxb)
      (right_mem_affineSpan_pair_of_between hacp hxc)
  exact hh.1 hbeq

/-- Distinct hexagon diagonals passing through the same point cannot share a
hexagon endpoint. -/
theorem disjointEnds_of_common_point
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    {i j : Fin 9} (hij : i ≠ j) {x : Point} (hxP : x ∈ P)
    (hi : x ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (hj : x ∈ openSegment ℝ (h (diagonalEnds j).1) (h (diagonalEnds j).2)) :
    DisjointEnds i j := by
  have hine := diagonalEnds_ne i
  have hjne := diagonalEnds_ne j
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro heq
    have hright : (diagonalEnds i).2 = (diagonalEnds j).2 :=
      same_right_of_common_left_chords hfour hh hhP hine
        (by simpa [heq] using hjne) hxP hi (by simpa [heq] using hj)
    apply hij
    apply diagonalEnds_injective
    exact Prod.ext heq hright
  · intro heq
    have hright : (diagonalEnds i).2 = (diagonalEnds j).1 :=
      same_right_of_common_left_chords hfour hh hhP hine
        (by simpa [heq] using hjne.symm) hxP hi
        (by simpa [openSegment_symm, heq] using hj)
    have hiord := diagonalEnds_lt i
    have hjord := diagonalEnds_lt j
    omega
  · intro heq
    have hright : (diagonalEnds i).1 = (diagonalEnds j).2 :=
      same_right_of_common_left_chords hfour hh hhP hine.symm
        (by simpa [heq] using hjne) hxP
        (by simpa only [openSegment_symm] using hi)
        (by simpa [heq] using hj)
    have hiord := diagonalEnds_lt i
    have hjord := diagonalEnds_lt j
    omega
  · intro heq
    have hleft : (diagonalEnds i).1 = (diagonalEnds j).1 :=
      same_right_of_common_left_chords hfour hh hhP hine.symm
        (by simpa [heq] using hjne.symm) hxP
        (by simpa only [openSegment_symm] using hi)
        (by simpa [openSegment_symm, heq] using hj)
    apply hij
    apply diagonalEnds_injective
    exact Prod.ext hleft heq

/-- The finite set of proper diagonals passing through a point. -/
noncomputable def diagonalsThrough (h : Fin 6 → Point) (x : Point) : Finset (Fin 9) := by
  classical
  exact (Finset.univ : Finset (Fin 9)).filter fun i ↦
    x ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2)

@[simp] theorem mem_diagonalsThrough {h : Fin 6 → Point} {x : Point} {i : Fin 9} :
    i ∈ diagonalsThrough h x ↔
      x ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2) := by
  classical
  simp [diagonalsThrough]

/-- At most three proper hexagon diagonals can pass through one point. -/
theorem diagonalsThrough_card_le_three
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P) {x : Point} (hxP : x ∈ P) :
    (diagonalsThrough h x).card ≤ 3 := by
  classical
  let D := diagonalsThrough h x
  by_contra hle
  have hlt : 3 < D.card := Nat.lt_of_not_ge hle
  obtain ⟨i, hiD, j, hjD, k, hkD, l, hlD,
      hij, hik, hil, hjk, hjl, hkl⟩ := Finset.three_lt_card.mp hlt
  have hi := mem_diagonalsThrough.mp hiD
  have hj := mem_diagonalsThrough.mp hjD
  have hk := mem_diagonalsThrough.mp hkD
  have hl := mem_diagonalsThrough.mp hlD
  have hdij := disjointEnds_of_common_point hfour hh hhP hij hxP hi hj
  have hdik := disjointEnds_of_common_point hfour hh hhP hik hxP hi hk
  have hdil := disjointEnds_of_common_point hfour hh hhP hil hxP hi hl
  have hdjk := disjointEnds_of_common_point hfour hh hhP hjk hxP hj hk
  have hdjl := disjointEnds_of_common_point hfour hh hhP hjl hxP hj hl
  have hdkl := disjointEnds_of_common_point hfour hh hhP hkl hxP hk hl
  have hine' : (diagonalEnds i).2 ≠ (diagonalEnds i).1 := (diagonalEnds_ne i).symm
  have hjne' : (diagonalEnds j).2 ≠ (diagonalEnds j).1 := (diagonalEnds_ne j).symm
  have hkne' : (diagonalEnds k).2 ≠ (diagonalEnds k).1 := (diagonalEnds_ne k).symm
  have hlne' : (diagonalEnds l).2 ≠ (diagonalEnds l).1 := (diagonalEnds_ne l).symm
  let f : Fin 8 → Fin 6 := ![
    (diagonalEnds i).1, (diagonalEnds i).2,
    (diagonalEnds j).1, (diagonalEnds j).2,
    (diagonalEnds k).1, (diagonalEnds k).2,
    (diagonalEnds l).1, (diagonalEnds l).2]
  have hf : Function.Injective f := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp_all [f, DisjointEnds]
  have hcard := Fintype.card_le_of_injective f hf
  norm_num at hcard

/-- The four perfect matchings of the nine-diagonal incidence graph. -/
theorem disjoint_triple_classification :
    ∀ i j k : Fin 9, i ≠ j → i ≠ k → j ≠ k →
      DisjointEnds i j → DisjointEnds i k → DisjointEnds j k →
      ({i, j, k} : Finset (Fin 9)) = {1, 4, 7} ∨
      ({i, j, k} : Finset (Fin 9)) = {0, 4, 8} ∨
      ({i, j, k} : Finset (Fin 9)) = {1, 5, 6} ∨
      ({i, j, k} : Finset (Fin 9)) = {2, 3, 7} := by
  decide

private def mainDiagonalSet : Finset (Fin 9) := {1, 4, 7}

/-- If every monochromatic triple is the main-diagonal triple, no fibre can
contain four labels.  This is the counting fact behind both finite incidence
classifications below. -/
private theorem fibre_card_le_three
    {n : ℕ} (f : Fin 9 → Fin n)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = mainDiagonalSet)
    (c : Fin n) :
    ((Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c).card ≤ 3 := by
  classical
  let S := (Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c
  change S.card ≤ 3
  by_contra hle
  have hfour : 3 < S.card := by omega
  obtain ⟨a, ha, b, hb, d, hd, e, he,
      hab, had, hae, hbd, hbe, hde⟩ := Finset.three_lt_card.mp hfour
  have hfa : f a = c := (Finset.mem_filter.mp ha).2
  have hfb : f b = c := (Finset.mem_filter.mp hb).2
  have hfd : f d = c := (Finset.mem_filter.mp hd).2
  have hfe : f e = c := (Finset.mem_filter.mp he).2
  have h₁ := htriple a b d hab had hbd
    (hfa.trans hfb.symm) (hfb.trans hfd.symm)
  have h₂ := htriple a b e hab hae hbe
    (hfa.trans hfb.symm) (hfb.trans hfe.symm)
  have heMem : e ∈ ({a, b, d} : Finset (Fin 9)) := by
    rw [h₁, ← h₂]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at heMem
  rcases heMem with rfl | rfl | hed
  · exact hae rfl
  · exact hbe rfl
  · exact hde hed.symm

private theorem large_fibre_eq_main
    {n : ℕ} (f : Fin 9 → Fin n)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = mainDiagonalSet)
    (c : Fin n)
    (hlarge : 2 < ((Finset.univ : Finset (Fin 9)).filter
      fun i ↦ f i = c).card) :
    ((Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c) =
      mainDiagonalSet := by
  classical
  let S := (Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c
  have hle : S.card ≤ 3 := by
    simpa [S] using fibre_card_le_three f htriple c
  have hlargeS : 2 < S.card := by simpa [S] using hlarge
  have hcard : S.card = 3 := by omega
  obtain ⟨i, j, k, hij, hik, hjk, hS⟩ := Finset.card_eq_three.mp hcard
  change S = mainDiagonalSet
  rw [hS]
  apply htriple i j k hij hik hjk
  · have hi : i ∈ S := by rw [hS]; simp
    have hj : j ∈ S := by rw [hS]; simp
    exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  · have hj : j ∈ S := by rw [hS]; simp
    have hk : k ∈ S := by rw [hS]; simp
    exact (Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hk).2.symm

/-- Two chords cannot meet in their relative interiors when both endpoints
of the second chord lie strictly on the same side of the first chord. -/
theorem no_common_point_of_turn_pos
    {a b c d x : Point}
    (hc : 0 < turn a b c) (hd : 0 < turn a b d)
    (hab : x ∈ openSegment ℝ a b)
    (hcd : x ∈ openSegment ℝ c d) : False := by
  have hxpos : 0 < turn a b x :=
    edgeTurn_pos_of_mem_openSegment hcd hc.le hd.le (Or.inl hc)
  exact hxpos.ne' (Lax56Proofs.HKBTriangle.turn_eq_zero_of_between hab)

theorem no_common_diagonals_0_8
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h) {x : Point}
    (h0 : x ∈ openSegment ℝ (h (diagonalEnds 0).1) (h (diagonalEnds 0).2))
    (h8 : x ∈ openSegment ℝ (h (diagonalEnds 8).1) (h (diagonalEnds 8).2)) :
    False := by
  have h023 : 0 < turn (h 0) (h 2) (h 3) := by
    rw [← turn_rotate (h 0) (h 2) (h 3)]
    exact hh.2.1 2 0 (by decide) (by decide)
  have h025 : 0 < turn (h 0) (h 2) (h 5) := by
    rw [turn_rotate (h 5) (h 0) (h 2)]
    exact hh.2.1 5 2 (by decide) (by decide)
  apply no_common_point_of_turn_pos h023 h025
  · simpa [diagonalEnds] using h0
  · simpa [diagonalEnds] using h8

theorem no_common_diagonals_5_6
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h) {x : Point}
    (h5 : x ∈ openSegment ℝ (h (diagonalEnds 5).1) (h (diagonalEnds 5).2))
    (h6 : x ∈ openSegment ℝ (h (diagonalEnds 6).1) (h (diagonalEnds 6).2)) :
    False := by
  have h512 : 0 < turn (h 5) (h 1) (h 2) := by
    rw [← turn_rotate (h 5) (h 1) (h 2)]
    exact hh.2.1 1 5 (by decide) (by decide)
  have h514 : 0 < turn (h 5) (h 1) (h 4) := by
    rw [turn_rotate (h 4) (h 5) (h 1)]
    exact hh.2.1 4 1 (by decide) (by decide)
  apply no_common_point_of_turn_pos h512 h514
  · simpa [diagonalEnds, openSegment_symm] using h5
  · simpa [diagonalEnds] using h6

theorem no_common_diagonals_2_3
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h) {x : Point}
    (h2 : x ∈ openSegment ℝ (h (diagonalEnds 2).1) (h (diagonalEnds 2).2))
    (h3 : x ∈ openSegment ℝ (h (diagonalEnds 3).1) (h (diagonalEnds 3).2)) :
    False := by
  have h401 : 0 < turn (h 4) (h 0) (h 1) := by
    rw [← turn_rotate (h 4) (h 0) (h 1)]
    exact hh.2.1 0 4 (by decide) (by decide)
  have h403 : 0 < turn (h 4) (h 0) (h 3) := by
    rw [turn_rotate (h 3) (h 4) (h 0)]
    exact hh.2.1 3 0 (by decide) (by decide)
  apply no_common_point_of_turn_pos h401 h403
  · simpa [diagonalEnds, openSegment_symm] using h2
  · simpa [diagonalEnds] using h3

/-- Three distinct diagonals through one point are exactly the three main
diagonals. -/
theorem common_point_triple_is_main
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P) {x : Point} (hxP : x ∈ P)
    {i j k : Fin 9} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : x ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (hj : x ∈ openSegment ℝ (h (diagonalEnds j).1) (h (diagonalEnds j).2))
    (hk : x ∈ openSegment ℝ (h (diagonalEnds k).1) (h (diagonalEnds k).2)) :
    ({i, j, k} : Finset (Fin 9)) = {1, 4, 7} := by
  classical
  have hdij := disjointEnds_of_common_point hfour hh hhP hij hxP hi hj
  have hdik := disjointEnds_of_common_point hfour hh hhP hik hxP hi hk
  have hdjk := disjointEnds_of_common_point hfour hh hhP hjk hxP hj hk
  rcases disjoint_triple_classification i j k hij hik hjk hdij hdik hdjk with
      hmain | hbad0 | hbad1 | hbad2
  · exact hmain
  · have hthrough : ∀ t : Fin 9, t ∈ ({i, j, k} : Finset (Fin 9)) →
        x ∈ openSegment ℝ (h (diagonalEnds t).1) (h (diagonalEnds t).2) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    exact (no_common_diagonals_0_8 hh
      (hthrough 0 (by rw [hbad0]; simp))
      (hthrough 8 (by rw [hbad0]; simp))).elim
  · have hthrough : ∀ t : Fin 9, t ∈ ({i, j, k} : Finset (Fin 9)) →
        x ∈ openSegment ℝ (h (diagonalEnds t).1) (h (diagonalEnds t).2) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    exact (no_common_diagonals_5_6 hh
      (hthrough 5 (by rw [hbad1]; simp))
      (hthrough 6 (by rw [hbad1]; simp))).elim
  · have hthrough : ∀ t : Fin 9, t ∈ ({i, j, k} : Finset (Fin 9)) →
        x ∈ openSegment ℝ (h (diagonalEnds t).1) (h (diagonalEnds t).2) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact hi
      · exact hj
      · exact hk
    exact (no_common_diagonals_2_3 hh
      (hthrough 2 (by rw [hbad2]; simp))
      (hthrough 3 (by rw [hbad2]; simp))).elim

/-- Three labels cannot cover all nine diagonals if every label class is a
matching and every three-edge class is the main-diagonal matching. -/
theorem no_three_geometric_matching_cover :
    ¬∃ f : Fin 9 → Fin 3,
      (∀ i j, i ≠ j → f i = f j → DisjointEnds i j) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        f i = f j → f j = f k →
        ({i, j, k} : Finset (Fin 9)) = {1, 4, 7}) := by
  classical
  rintro ⟨f, hmatching, htriple⟩
  have hpigeon : Fintype.card (Fin 3) * 2 < Fintype.card (Fin 9) := by decide
  obtain ⟨c, hc⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := f) hpigeon
  have hmain : ((Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c) =
      mainDiagonalSet := by
    apply large_fibre_eq_main f
    · simpa [mainDiagonalSet] using htriple
    · simpa using hc
  let T : Finset (Fin 9) :=
    (Finset.univ : Finset (Fin 9)) \ mainDiagonalSet
  have hTcard : T.card = 6 := by decide
  let Other := {d : Fin 3 // d ≠ c}
  have hOther : Fintype.card Other = 2 := by
    fin_cases c <;> decide
  have hfne (x : T) : f x ≠ c := by
    intro heq
    have hxMain : (x : Fin 9) ∈ mainDiagonalSet := by
      rw [← hmain]
      simp [heq]
    exact (Finset.mem_sdiff.mp x.property).2 hxMain
  let g : T → Other := fun x ↦ ⟨f x, hfne x⟩
  have hpigeon2 : Fintype.card Other * 2 < Fintype.card T := by
    simpa [hOther, hTcard]
  obtain ⟨d, hd⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := g) hpigeon2
  have hthree : 2 < ((Finset.univ : Finset T).filter fun x ↦ g x = d).card := by
    simpa using hd
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have hfxy : f x = f y := by
    exact congrArg Subtype.val ((Finset.mem_filter.mp hx).2.trans
      (Finset.mem_filter.mp hy).2.symm)
  have hfyz : f y = f z := by
    exact congrArg Subtype.val ((Finset.mem_filter.mp hy).2.trans
      (Finset.mem_filter.mp hz).2.symm)
  have hxyz := htriple (x : Fin 9) (y : Fin 9) (z : Fin 9)
    (Subtype.val_injective.ne hxy) (Subtype.val_injective.ne hxz)
    (Subtype.val_injective.ne hyz) hfxy hfyz
  have hxMain : (x : Fin 9) ∈ mainDiagonalSet := by
    rw [← (show ({(x : Fin 9), (y : Fin 9), (z : Fin 9)} : Finset (Fin 9)) =
      mainDiagonalSet by simpa [mainDiagonalSet] using hxyz)]
    simp
  exact (Finset.mem_sdiff.mp x.property).2 hxMain

/-- The only endpoint-disjoint diagonal pairs that still cannot meet are the
three nested short-diagonal pairs. -/
def ShareCompatible (i j : Fin 9) : Prop :=
  DisjointEnds i j ∧
    ({i, j} : Finset (Fin 9)) ≠ {0, 8} ∧
    ({i, j} : Finset (Fin 9)) ≠ {5, 6} ∧
    ({i, j} : Finset (Fin 9)) ≠ {2, 3}

instance instDecidableShareCompatible (i j : Fin 9) :
    Decidable (ShareCompatible i j) := by
  unfold ShareCompatible
  infer_instance

theorem shareCompatible_of_common_point
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    {i j : Fin 9} (hij : i ≠ j) {x : Point} (hxP : x ∈ P)
    (hi : x ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (hj : x ∈ openSegment ℝ (h (diagonalEnds j).1) (h (diagonalEnds j).2)) :
    ShareCompatible i j := by
  classical
  refine ⟨disjointEnds_of_common_point hfour hh hhP hij hxP hi hj, ?_, ?_, ?_⟩
  · intro hp
    have hii : i = 0 ∨ i = 8 := by
      have : i ∈ ({0, 8} : Finset (Fin 9)) := by rw [← hp]; simp
      simpa using this
    have hjj : j = 0 ∨ j = 8 := by
      have : j ∈ ({0, 8} : Finset (Fin 9)) := by rw [← hp]; simp
      simpa using this
    rcases hii with rfl | rfl <;> rcases hjj with rfl | rfl
    · exact hij rfl
    · exact no_common_diagonals_0_8 hh hi hj
    · exact no_common_diagonals_0_8 hh hj hi
    · exact hij rfl
  · intro hp
    have hii : i = 5 ∨ i = 6 := by
      have : i ∈ ({5, 6} : Finset (Fin 9)) := by rw [← hp]; simp
      simpa using this
    have hjj : j = 5 ∨ j = 6 := by
      have : j ∈ ({5, 6} : Finset (Fin 9)) := by rw [← hp]; simp
      simpa using this
    rcases hii with rfl | rfl <;> rcases hjj with rfl | rfl
    · exact hij rfl
    · exact no_common_diagonals_5_6 hh hi hj
    · exact no_common_diagonals_5_6 hh hj hi
    · exact hij rfl
  · intro hp
    have hii : i = 2 ∨ i = 3 := by
      have : i ∈ ({2, 3} : Finset (Fin 9)) := by rw [← hp]; simp
      simpa using this
    have hjj : j = 2 ∨ j = 3 := by
      have : j ∈ ({2, 3} : Finset (Fin 9)) := by rw [← hp]; simp
      simpa using this
    rcases hii with rfl | rfl <;> rcases hjj with rfl | rfl
    · exact hij rfl
    · exact no_common_diagonals_2_3 hh hi hj
    · exact no_common_diagonals_2_3 hh hj hi
    · exact hij rfl

/-- The two alternating incidence patterns left after the main-diagonal
triple has been removed. -/
def FourAssignmentPattern (f : Fin 9 → Fin 4) : Prop :=
  ∃ p q₀ q₁ q₂ : Fin 4,
    f 1 = p ∧ f 4 = p ∧ f 7 = p ∧
    ((f 0 = q₀ ∧ f 3 = q₀ ∧ f 6 = q₁ ∧ f 8 = q₁ ∧
        f 2 = q₂ ∧ f 5 = q₂) ∨
      (f 3 = q₀ ∧ f 6 = q₀ ∧ f 8 = q₁ ∧ f 2 = q₁ ∧
        f 5 = q₂ ∧ f 0 = q₂))

instance instDecidableFourAssignmentPattern (f : Fin 9 → Fin 4) :
    Decidable (FourAssignmentPattern f) := by
  unfold FourAssignmentPattern
  infer_instance

private def shortDiagonalSet : Finset (Fin 9) :=
  (Finset.univ : Finset (Fin 9)) \ mainDiagonalSet

private theorem shortDiagonalSet_card : shortDiagonalSet.card = 6 := by
  decide

private theorem card_fin4_away_from_two
    (a b : Fin 4) (hab : a ≠ b) :
    Fintype.card {d : Fin 4 // d ≠ a ∧ d ≠ b} = 2 := by
  fin_cases a <;> fin_cases b <;> simp_all
  all_goals decide

private theorem exists_large_fibre_four
    (f : Fin 9 → Fin 4)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = mainDiagonalSet) :
    ∃ c : Fin 4,
      ((Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c) =
        mainDiagonalSet := by
  have hpigeon : Fintype.card (Fin 4) * 2 < Fintype.card (Fin 9) := by decide
  obtain ⟨c, hc⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := f) hpigeon
  exact ⟨c, large_fibre_eq_main f htriple c (by simpa using hc)⟩

private theorem short_colour_ne_main
    (f : Fin 9 → Fin 4) (c : Fin 4)
    (hmain : ((Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c) =
      mainDiagonalSet)
    (x : shortDiagonalSet) : f x ≠ c := by
  intro heq
  have hxMain : (x : Fin 9) ∈ mainDiagonalSet := by
    rw [← hmain]
    simp [heq]
  exact (Finset.mem_sdiff.mp x.property).2 hxMain

/-- Every short diagonal has a second short diagonal assigned to the same
point.  Otherwise the other five short diagonals would use only two colours,
and three of them would coincide, contrary to the main-triple condition. -/
private theorem exists_short_mate
    (f : Fin 9 → Fin 4)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = mainDiagonalSet)
    (c : Fin 4)
    (hmain : ((Finset.univ : Finset (Fin 9)).filter fun i ↦ f i = c) =
      mainDiagonalSet)
    (x : shortDiagonalSet) :
    ∃ y : shortDiagonalSet, y ≠ x ∧ f y = f x := by
  classical
  by_contra hmate
  push Not at hmate
  let U : Finset shortDiagonalSet :=
    (Finset.univ : Finset shortDiagonalSet).erase x
  have hUcard : U.card = 5 := by
    simp [U, shortDiagonalSet_card]
  have hcfx : c ≠ f x := (short_colour_ne_main f c hmain x).symm
  let Other := {d : Fin 4 // d ≠ c ∧ d ≠ f x}
  have hOther : Fintype.card Other = 2 :=
    card_fin4_away_from_two c (f x) hcfx
  have hune (u : U) : (u.1 : shortDiagonalSet) ≠ x :=
    (Finset.mem_erase.mp u.property).1
  let g : U → Other := fun u ↦
    ⟨f (u.1 : shortDiagonalSet), short_colour_ne_main f c hmain u.1,
      hmate u.1 (hune u)⟩
  have hpigeon : Fintype.card Other * 2 < Fintype.card U := by
    simpa [hOther, hUcard]
  obtain ⟨d, hd⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := g) hpigeon
  have hthree : 2 < ((Finset.univ : Finset U).filter fun u ↦ g u = d).card := by
    simpa using hd
  obtain ⟨u, v, w, hu, hv, hw, huv, huw, hvw⟩ :=
    Finset.two_lt_card_iff.mp hthree
  have hfuv : f (u.1 : shortDiagonalSet) = f (v.1 : shortDiagonalSet) := by
    exact congrArg Subtype.val ((Finset.mem_filter.mp hu).2.trans
      (Finset.mem_filter.mp hv).2.symm)
  have hfvw : f (v.1 : shortDiagonalSet) = f (w.1 : shortDiagonalSet) := by
    exact congrArg Subtype.val ((Finset.mem_filter.mp hv).2.trans
      (Finset.mem_filter.mp hw).2.symm)
  have hmainTriple := htriple
    (u.1.1 : Fin 9) (v.1.1 : Fin 9) (w.1.1 : Fin 9)
    (by exact Subtype.val_injective.ne (Subtype.val_injective.ne huv))
    (by exact Subtype.val_injective.ne (Subtype.val_injective.ne huw))
    (by exact Subtype.val_injective.ne (Subtype.val_injective.ne hvw))
    hfuv hfvw
  have huMain : (u.1.1 : Fin 9) ∈ mainDiagonalSet := by
    rw [← hmainTriple]
    simp
  exact (Finset.mem_sdiff.mp u.1.property).2 huMain

private theorem share_zero_cases (j : shortDiagonalSet)
    (hj : (j : Fin 9) ≠ 0) (h : ShareCompatible 0 j) :
    (j : Fin 9) = 3 ∨ (j : Fin 9) = 5 := by
  revert j
  decide

private theorem share_six_cases (j : shortDiagonalSet)
    (hj : (j : Fin 9) ≠ 6) (h : ShareCompatible 6 j) :
    (j : Fin 9) = 3 ∨ (j : Fin 9) = 8 := by
  revert j
  decide

private theorem share_two_cases (j : shortDiagonalSet)
    (hj : (j : Fin 9) ≠ 2) (h : ShareCompatible 2 j) :
    (j : Fin 9) = 5 ∨ (j : Fin 9) = 8 := by
  revert j
  decide

private theorem share_three_cases (j : shortDiagonalSet)
    (hj : (j : Fin 9) ≠ 3) (h : ShareCompatible 3 j) :
    (j : Fin 9) = 0 ∨ (j : Fin 9) = 6 := by
  revert j
  decide

private theorem share_eight_cases (j : shortDiagonalSet)
    (hj : (j : Fin 9) ≠ 8) (h : ShareCompatible 8 j) :
    (j : Fin 9) = 2 ∨ (j : Fin 9) = 6 := by
  revert j
  decide

private theorem bad_triple_ne_main (a b c : Fin 9)
    (hbad : ({a, b, c} : Finset (Fin 9)) ≠ mainDiagonalSet)
    (f : Fin 9 → Fin 4)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = mainDiagonalSet)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hfab : f a = f b) (hfbc : f b = f c) : False :=
  hbad (htriple a b c hab hac hbc hfab hfbc)

/-- Incidence classification for four points covering all nine diagonals. -/
theorem four_assignment_classification
    (f : Fin 9 → Fin 4)
    (hshare : ∀ i j, i ≠ j → f i = f j → ShareCompatible i j)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = {1, 4, 7}) :
    FourAssignmentPattern f := by
  classical
  have htriple' : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = mainDiagonalSet := by
    simpa [mainDiagonalSet] using htriple
  obtain ⟨p, hp⟩ := exists_large_fibre_four f htriple'
  have hpval (i : Fin 9) (hi : i ∈ mainDiagonalSet) : f i = p := by
    have : i ∈ ((Finset.univ : Finset (Fin 9)).filter fun j ↦ f j = p) := by
      rw [hp]
      exact hi
    exact (Finset.mem_filter.mp this).2
  have hp1 : f 1 = p := hpval 1 (by decide)
  have hp4 : f 4 = p := hpval 4 (by decide)
  have hp7 : f 7 = p := hpval 7 (by decide)
  let x0 : shortDiagonalSet := ⟨0, by decide⟩
  let x2 : shortDiagonalSet := ⟨2, by decide⟩
  let x3 : shortDiagonalSet := ⟨3, by decide⟩
  let x6 : shortDiagonalSet := ⟨6, by decide⟩
  let x8 : shortDiagonalSet := ⟨8, by decide⟩
  obtain ⟨m0, hm0ne, hm0⟩ := exists_short_mate f htriple' p hp x0
  have hm0share : ShareCompatible 0 m0 := by
    apply hshare 0 m0
    · exact Subtype.val_injective.ne hm0ne.symm
    · simpa [x0] using hm0.symm
  rcases share_zero_cases m0 (Subtype.val_injective.ne hm0ne) hm0share with
      hm03 | hm05
  · have h03 : f 0 = f 3 := by simpa [x0, hm03] using hm0.symm
    obtain ⟨m6, hm6ne, hm6⟩ := exists_short_mate f htriple' p hp x6
    have hm6share : ShareCompatible 6 m6 := by
      apply hshare 6 m6
      · exact Subtype.val_injective.ne hm6ne.symm
      · simpa [x6] using hm6.symm
    rcases share_six_cases m6 (Subtype.val_injective.ne hm6ne) hm6share with
        hm63 | hm68
    · have h36 : f 3 = f 6 := by
        have : f 6 = f 3 := by simpa [x6, hm63] using hm6.symm
        exact this.symm
      exact (bad_triple_ne_main 0 3 6 (by decide) f htriple'
        (by decide) (by decide) (by decide) h03 h36).elim
    · have h68 : f 6 = f 8 := by simpa [x6, hm68] using hm6.symm
      obtain ⟨m2, hm2ne, hm2⟩ := exists_short_mate f htriple' p hp x2
      have hm2share : ShareCompatible 2 m2 := by
        apply hshare 2 m2
        · exact Subtype.val_injective.ne hm2ne.symm
        · simpa [x2] using hm2.symm
      rcases share_two_cases m2 (Subtype.val_injective.ne hm2ne) hm2share with
          hm25 | hm28
      · have h25 : f 2 = f 5 := by simpa [x2, hm25] using hm2.symm
        exact ⟨p, f 0, f 6, f 2, hp1, hp4, hp7, Or.inl
          ⟨rfl, h03.symm, rfl, h68.symm, rfl, h25.symm⟩⟩
      · have h28 : f 2 = f 8 := by simpa [x2, hm28] using hm2.symm
        exact (bad_triple_ne_main 2 8 6 (by decide) f htriple'
          (by decide) (by decide) (by decide) h28 h68.symm).elim
  · have h05 : f 0 = f 5 := by simpa [x0, hm05] using hm0.symm
    obtain ⟨m3, hm3ne, hm3⟩ := exists_short_mate f htriple' p hp x3
    have hm3share : ShareCompatible 3 m3 := by
      apply hshare 3 m3
      · exact Subtype.val_injective.ne hm3ne.symm
      · simpa [x3] using hm3.symm
    rcases share_three_cases m3 (Subtype.val_injective.ne hm3ne) hm3share with
        hm30 | hm36
    · have h30 : f 3 = f 0 := by simpa [x3, hm30] using hm3.symm
      exact (bad_triple_ne_main 3 0 5 (by decide) f htriple'
        (by decide) (by decide) (by decide) h30 h05).elim
    · have h36 : f 3 = f 6 := by simpa [x3, hm36] using hm3.symm
      obtain ⟨m8, hm8ne, hm8⟩ := exists_short_mate f htriple' p hp x8
      have hm8share : ShareCompatible 8 m8 := by
        apply hshare 8 m8
        · exact Subtype.val_injective.ne hm8ne.symm
        · simpa [x8] using hm8.symm
      rcases share_eight_cases m8 (Subtype.val_injective.ne hm8ne) hm8share with
          hm82 | hm86
      · have h82 : f 8 = f 2 := by simpa [x8, hm82] using hm8.symm
        exact ⟨p, f 3, f 8, f 5, hp1, hp4, hp7, Or.inr
          ⟨rfl, h36.symm, rfl, h82.symm, rfl, h05⟩⟩
      · have h86 : f 8 = f 6 := by simpa [x8, hm86] using hm8.symm
        exact (bad_triple_ne_main 8 6 3 (by decide) f htriple'
          (by decide) (by decide) (by decide) h86 h36.symm).elim

/-- Choose one blocker on each proper diagonal. -/
noncomputable def diagonalBlocker
    {B : Finset Point} {h : Fin 6 → Point}
    (hdiag : ∀ i : Fin 9, ∃ r ∈ B,
      r ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (i : Fin 9) : Point :=
  Classical.choose (hdiag i)

theorem diagonalBlocker_mem
    {B : Finset Point} {h : Fin 6 → Point}
    (hdiag : ∀ i : Fin 9, ∃ r ∈ B,
      r ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (i : Fin 9) : diagonalBlocker hdiag i ∈ B :=
  (Classical.choose_spec (hdiag i)).1

theorem diagonalBlocker_between
    {B : Finset Point} {h : Fin 6 → Point}
    (hdiag : ∀ i : Fin 9, ∃ r ∈ B,
      r ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2))
    (i : Fin 9) :
    diagonalBlocker hdiag i ∈
      openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2) :=
  (Classical.choose_spec (hdiag i)).2

open Classical in
/-- Corollary 4.2: blocking all nine proper diagonals requires at least four
strict-interior points. -/
theorem four_le_card_strictInside_of_diagonals_blocked
    {P B : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P) (hBP : B ⊆ P)
    (hdiag : ∀ i : Fin 9, ∃ r ∈ B,
      r ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2)) :
    4 ≤ (B.filter (StrictlyInsideHexagon h)).card := by
  classical
  let I := B.filter (StrictlyInsideHexagon h)
  have hbstrict (i : Fin 9) :
      StrictlyInsideHexagon h (diagonalBlocker hdiag i) := by
    intro side
    exact diagonalPoint_edgeTurn_pos hh (diagonalEnds_ne i)
      (diagonalEnds_nonadjacent i).1 (diagonalEnds_nonadjacent i).2
      (diagonalBlocker_between hdiag i) side
  have hbI (i : Fin 9) : diagonalBlocker hdiag i ∈ I := by
    exact Finset.mem_filter.mpr ⟨diagonalBlocker_mem hdiag i, hbstrict i⟩
  let block : Fin 9 → I := fun i ↦ ⟨diagonalBlocker hdiag i, hbI i⟩
  by_contra hcard
  have hbasecard : (B.filter (StrictlyInsideHexagon h)).card ≤ 3 := by omega
  have hIcard : I.card ≤ 3 := by
    simpa [I] using hbasecard
  have htypecard : Fintype.card I ≤ 3 := by
    simpa using hIcard
  let e : I ↪ Fin 3 :=
    (Fintype.equivFin I).toEmbedding.trans (Fin.castLEEmb htypecard)
  let f : Fin 9 → Fin 3 := fun i ↦ e (block i)
  have hmatching : ∀ i j, i ≠ j → f i = f j → DisjointEnds i j := by
    intro i j hij hfij
    have hbij : block i = block j := e.injective hfij
    have hpij : diagonalBlocker hdiag i = diagonalBlocker hdiag j :=
      congrArg Subtype.val hbij
    have hiP : diagonalBlocker hdiag i ∈ P :=
      hBP (diagonalBlocker_mem hdiag i)
    apply disjointEnds_of_common_point hfour hh hhP hij hiP
      (diagonalBlocker_between hdiag i)
    simpa [hpij] using diagonalBlocker_between hdiag j
  have htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      f i = f j → f j = f k →
      ({i, j, k} : Finset (Fin 9)) = {1, 4, 7} := by
    intro i j k hij hik hjk hfij hfjk
    have hbij : block i = block j := e.injective hfij
    have hbjk : block j = block k := e.injective hfjk
    have hpij : diagonalBlocker hdiag i = diagonalBlocker hdiag j :=
      congrArg Subtype.val hbij
    have hpjk : diagonalBlocker hdiag j = diagonalBlocker hdiag k :=
      congrArg Subtype.val hbjk
    have hiP : diagonalBlocker hdiag i ∈ P :=
      hBP (diagonalBlocker_mem hdiag i)
    apply common_point_triple_is_main hfour hh hhP hiP hij hik hjk
      (diagonalBlocker_between hdiag i)
    · simpa [hpij] using diagonalBlocker_between hdiag j
    · have hpik : diagonalBlocker hdiag i = diagonalBlocker hdiag k :=
        hpij.trans hpjk
      simpa [hpik] using diagonalBlocker_between hdiag k
  exact no_three_geometric_matching_cover ⟨f, hmatching, htriple⟩

end Lax56Proofs.HKBDiagonals
