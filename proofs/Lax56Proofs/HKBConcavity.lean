import Lax56Proofs.HKBDiagonals
import Mathlib.Tactic

/-!
The geometric core of the four-diagonal-blocker concavity argument.
-/

namespace Lax56Proofs.HKBConcavity

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBDiagonals
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- Lemma 5.2 in a determinant-only form. -/
theorem quadrilateral_crossing_inside
    {A B C D p q : Point}
    (hABD : 0 < turn A B D)
    (hBCA : 0 < turn B C A)
    (hACD : 0 < turn A C D)
    (hp : p ∈ openSegment ℝ D A)
    (hqAC : q ∈ openSegment ℝ A C)
    (hqBD : q ∈ openSegment ℝ B D) :
    StrictlyInsideTriangle p B C q := by
  have hBDA : 0 < turn B D A := by
    simpa only [turn_rotate] using hABD
  have hBDp : 0 < turn B D p :=
    edgeTurn_pos_of_mem_openSegment hp (by simp) hBDA.le (Or.inr hBDA)
  have hpBD : 0 < turn p B D := by
    simpa only [turn_rotate] using hBDp
  have hpBq : 0 < turn p B q :=
    edgeTurn_pos_of_mem_openSegment hqBD (by simp) hpBD.le (Or.inr hpBD)
  have hBCq : 0 < turn B C q :=
    edgeTurn_pos_of_mem_openSegment hqAC hBCA.le (by simp) (Or.inl hBCA)
  have hACp : 0 < turn A C p :=
    edgeTurn_pos_of_mem_openSegment hp hACD.le (by simp) (Or.inl hACD)
  have hCpA : 0 < turn C p A := by
    rw [← turn_rotate C p A, ← turn_rotate p A C]
    exact hACp
  have hCpq : 0 < turn C p q :=
    edgeTurn_pos_of_mem_openSegment hqAC hCpA.le (by simp) (Or.inl hCpA)
  exact ⟨hpBq, hBCq, hCpq⟩

/-- If `p` lies strictly between opposite points `a,a'`, then crossing the
ray `pa` counterclockwise is equivalent to crossing the opposite ray in the
reverse order. -/
theorem turn_pos_to_opposite_ray
    {p a a' q : Point}
    (hp : p ∈ openSegment ℝ a a')
    (hpaq : 0 < turn p a q) :
    0 < turn p q a' := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := q) (b := a) hp
  have hqap : turn q a p = -turn p a q := by
    simp [turn]
    ring
  have hqaa' : turn q a a' < 0 := by
    simp only [turn_self_right] at heq
    rw [hqap] at heq
    nlinarith
  obtain ⟨s, hs0, hs1, heq'⟩ :=
    turn_of_mem_openSegment (a := q) (b := a') hp
  have hqa'a : 0 < turn q a' a := by
    rw [turn_swap_last]
    linarith
  have hqa'p : 0 < turn q a' p := by
    simp only [turn_self_right] at heq'
    rw [heq']
    exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr hs1) hqa'a) (mul_nonneg hs0.le (by simp))
  simpa only [turn_rotate] using hqa'p

/-- The alternating three short-diagonal intersections surround the common
point of the three main diagonals.  This combines Lemmas 5.2 and 5.3 in the
exact incidence form needed later. -/
theorem main_and_short_blockers_surround
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {p q₀ q₁ q₂ : Point}
    (hp03 : p ∈ openSegment ℝ (h 0) (h 3))
    (hp14 : p ∈ openSegment ℝ (h 1) (h 4))
    (hp25 : p ∈ openSegment ℝ (h 2) (h 5))
    (hq₀02 : q₀ ∈ openSegment ℝ (h 0) (h 2))
    (hq₀13 : q₀ ∈ openSegment ℝ (h 1) (h 3))
    (hq₁24 : q₁ ∈ openSegment ℝ (h 2) (h 4))
    (hq₁35 : q₁ ∈ openSegment ℝ (h 3) (h 5))
    (hq₂40 : q₂ ∈ openSegment ℝ (h 4) (h 0))
    (hq₂51 : q₂ ∈ openSegment ℝ (h 5) (h 1)) :
    StrictlyInsideTriangle q₀ q₁ q₂ p := by
  have h₀ : StrictlyInsideTriangle p (h 1) (h 2) q₀ := by
    apply quadrilateral_crossing_inside
    · exact hh.2.1 0 3 (by decide) (by decide)
    · exact hh.2.1 1 0 (by decide) (by decide)
    · rw [← turn_rotate (h 0) (h 2) (h 3)]
      exact hh.2.1 2 0 (by decide) (by decide)
    · simpa only [openSegment_symm] using hp03
    · exact hq₀02
    · exact hq₀13
  have h₁ : StrictlyInsideTriangle p (h 3) (h 4) q₁ := by
    apply quadrilateral_crossing_inside
    · exact hh.2.1 2 5 (by decide) (by decide)
    · exact hh.2.1 3 2 (by decide) (by decide)
    · rw [← turn_rotate (h 2) (h 4) (h 5)]
      exact hh.2.1 4 2 (by decide) (by decide)
    · simpa only [openSegment_symm] using hp25
    · exact hq₁24
    · exact hq₁35
  have h₂ : StrictlyInsideTriangle p (h 5) (h 0) q₂ := by
    apply quadrilateral_crossing_inside
    · exact hh.2.1 4 1 (by decide) (by decide)
    · exact hh.2.1 5 4 (by decide) (by decide)
    · rw [← turn_rotate (h 4) (h 0) (h 1)]
      exact hh.2.1 0 4 (by decide) (by decide)
    · exact hp14
    · exact hq₂40
    · exact hq₂51
  have hpq₀q₁ : 0 < turn p q₀ q₁ := by
    have hpq₀h2 : 0 < turn p q₀ (h 2) := by
      simpa only [turn_rotate] using h₀.2.2
    have hpq₀h4 : 0 < turn p q₀ (h 4) :=
      turn_pos_to_opposite_ray hp14 h₀.1
    exact edgeTurn_pos_of_mem_openSegment hq₁24
      hpq₀h2.le hpq₀h4.le (Or.inl hpq₀h2)
  have hpq₁q₂ : 0 < turn p q₁ q₂ := by
    have hpq₁h4 : 0 < turn p q₁ (h 4) := by
      simpa only [turn_rotate] using h₁.2.2
    have hpq₁h0 : 0 < turn p q₁ (h 0) :=
      turn_pos_to_opposite_ray
        (by simpa only [openSegment_symm] using hp03) h₁.1
    exact edgeTurn_pos_of_mem_openSegment hq₂40
      hpq₁h4.le hpq₁h0.le (Or.inl hpq₁h4)
  have hpq₂q₀ : 0 < turn p q₂ q₀ := by
    have hpq₂h0 : 0 < turn p q₂ (h 0) := by
      simpa only [turn_rotate] using h₂.2.2
    have hpq₂h2 : 0 < turn p q₂ (h 2) :=
      turn_pos_to_opposite_ray
        (by simpa only [openSegment_symm] using hp25) h₂.1
    exact edgeTurn_pos_of_mem_openSegment hq₀02
      hpq₂h0.le hpq₂h2.le (Or.inl hpq₂h0)
  exact ⟨by simpa only [turn_rotate] using hpq₀q₁,
    by simpa only [turn_rotate] using hpq₁q₂,
    by simpa only [turn_rotate] using hpq₂q₀⟩

/-- Cyclically rotating the labels of a strict convex hexagon preserves the
defining orientation conditions. -/
def rotateHexOne (h : Fin 6 → Point) (i : Fin 6) : Point := h (i + 1)

theorem strictConvexHexagon_rotateHexOne
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h) :
    StrictConvexHexagon (rotateHexOne h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact add_right_cancel (hh.1 hij)
  · intro i j hji hjs
    apply hh.2.1 (i + 1) (j + 1)
    · intro heq
      apply hji
      exact add_right_cancel heq
    · intro heq
      apply hjs
      apply add_right_cancel (b := (1 : Fin 6))
      simpa [add_assoc] using heq
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [rotateHexOne]
    all_goals first
      | exact hh.2.2 _ _ _ (by decide) (by decide)
      | rw [turn_rotate]
        exact hh.2.2 _ _ _ (by decide) (by decide)

/-- Lemma 5.4: four points blocking all nine proper diagonals contain one
point strictly inside the triangle formed by three of the others. -/
theorem four_diagonal_blockers_are_concave
    {P J : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P) (hJP : J ⊆ P) (hJcard : J.card = 4)
    (hdiag : ∀ i : Fin 9, ∃ r ∈ J,
      r ∈ openSegment ℝ (h (diagonalEnds i).1) (h (diagonalEnds i).2)) :
    ∃ p q₀ q₁ q₂ : J,
      StrictlyInsideTriangle (q₀ : Point) (q₁ : Point) (q₂ : Point) (p : Point) := by
  classical
  have htypecard : Fintype.card J = 4 := by
    simpa using hJcard
  let e : J ≃ Fin 4 := (Fintype.equivFin J).trans (finCongr htypecard)
  let block : Fin 9 → J := fun i ↦
    ⟨diagonalBlocker hdiag i, diagonalBlocker_mem hdiag i⟩
  let f : Fin 9 → Fin 4 := fun i ↦ e (block i)
  have hshare : ∀ i j, i ≠ j → f i = f j → ShareCompatible i j := by
    intro i j hij hfij
    have hbij : block i = block j := e.injective hfij
    have hpij : diagonalBlocker hdiag i = diagonalBlocker hdiag j :=
      congrArg Subtype.val hbij
    have hiP : diagonalBlocker hdiag i ∈ P :=
      hJP (diagonalBlocker_mem hdiag i)
    apply shareCompatible_of_common_point hfour hh hhP hij hiP
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
      hJP (diagonalBlocker_mem hdiag i)
    apply common_point_triple_is_main hfour hh hhP hiP hij hik hjk
      (diagonalBlocker_between hdiag i)
    · simpa [hpij] using diagonalBlocker_between hdiag j
    · have hpik : diagonalBlocker hdiag i = diagonalBlocker hdiag k :=
        hpij.trans hpjk
      simpa [hpik] using diagonalBlocker_between hdiag k
  rcases four_assignment_classification f hshare htriple with
    ⟨pcode, q₀code, q₁code, q₂code, hp1, hp4, hp7, hpattern⟩
  have hb14 : block 1 = block 4 := e.injective (hp1.trans hp4.symm)
  have hb17 : block 1 = block 7 := e.injective (hp1.trans hp7.symm)
  have hp14eq : diagonalBlocker hdiag 1 = diagonalBlocker hdiag 4 :=
    congrArg Subtype.val hb14
  have hp17eq : diagonalBlocker hdiag 1 = diagonalBlocker hdiag 7 :=
    congrArg Subtype.val hb17
  rcases hpattern with hfirst | hsecond
  · rcases hfirst with ⟨h0, h3, h6, h8, h2, h5⟩
    have hb03 : block 0 = block 3 := e.injective (h0.trans h3.symm)
    have hb68 : block 6 = block 8 := e.injective (h6.trans h8.symm)
    have hb25 : block 2 = block 5 := e.injective (h2.trans h5.symm)
    have hq₀03eq : diagonalBlocker hdiag 0 = diagonalBlocker hdiag 3 :=
      congrArg Subtype.val hb03
    have hq₁68eq : diagonalBlocker hdiag 6 = diagonalBlocker hdiag 8 :=
      congrArg Subtype.val hb68
    have hq₂25eq : diagonalBlocker hdiag 2 = diagonalBlocker hdiag 5 :=
      congrArg Subtype.val hb25
    refine ⟨block 1, block 0, block 6, block 2, ?_⟩
    apply main_and_short_blockers_surround hh
    · simpa [block, diagonalEnds] using diagonalBlocker_between hdiag 1
    · simpa [block, diagonalEnds, hp14eq] using diagonalBlocker_between hdiag 4
    · simpa [block, diagonalEnds, hp17eq] using diagonalBlocker_between hdiag 7
    · simpa [block, diagonalEnds] using diagonalBlocker_between hdiag 0
    · simpa [block, diagonalEnds, hq₀03eq] using diagonalBlocker_between hdiag 3
    · simpa [block, diagonalEnds] using diagonalBlocker_between hdiag 6
    · simpa [block, diagonalEnds, hq₁68eq] using diagonalBlocker_between hdiag 8
    · simpa [block, diagonalEnds, openSegment_symm] using
        diagonalBlocker_between hdiag 2
    · simpa [block, diagonalEnds, hq₂25eq, openSegment_symm] using
        diagonalBlocker_between hdiag 5
  · rcases hsecond with ⟨h3, h6, h8, h2, h5, h0⟩
    have hb36 : block 3 = block 6 := e.injective (h3.trans h6.symm)
    have hb82 : block 8 = block 2 := e.injective (h8.trans h2.symm)
    have hb50 : block 5 = block 0 := e.injective (h5.trans h0.symm)
    have hq₀36eq : diagonalBlocker hdiag 3 = diagonalBlocker hdiag 6 :=
      congrArg Subtype.val hb36
    have hq₁82eq : diagonalBlocker hdiag 8 = diagonalBlocker hdiag 2 :=
      congrArg Subtype.val hb82
    have hq₂50eq : diagonalBlocker hdiag 5 = diagonalBlocker hdiag 0 :=
      congrArg Subtype.val hb50
    let h' := rotateHexOne h
    have hh' : StrictConvexHexagon h' := strictConvexHexagon_rotateHexOne hh
    refine ⟨block 1, block 3, block 8, block 5, ?_⟩
    apply main_and_short_blockers_surround hh'
    · simpa [h', rotateHexOne, block, diagonalEnds, hp14eq, openSegment_symm] using
        diagonalBlocker_between hdiag 4
    · simpa [h', rotateHexOne, block, diagonalEnds, hp17eq] using
        diagonalBlocker_between hdiag 7
    · simpa [h', rotateHexOne, block, diagonalEnds, openSegment_symm] using
        diagonalBlocker_between hdiag 1
    · simpa [h', rotateHexOne, block, diagonalEnds] using
        diagonalBlocker_between hdiag 3
    · simpa [h', rotateHexOne, block, diagonalEnds, hq₀36eq] using
        diagonalBlocker_between hdiag 6
    · simpa [h', rotateHexOne, block, diagonalEnds] using
        diagonalBlocker_between hdiag 8
    · simpa [h', rotateHexOne, block, diagonalEnds, hq₁82eq,
        openSegment_symm] using
        diagonalBlocker_between hdiag 2
    · simpa [h', rotateHexOne, block, diagonalEnds, openSegment_symm] using
        diagonalBlocker_between hdiag 5
    · simpa [h', rotateHexOne, block, diagonalEnds, hq₂50eq] using
        diagonalBlocker_between hdiag 0

end Lax56Proofs.HKBConcavity
