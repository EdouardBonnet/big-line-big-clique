import Lax56Proofs.Blockers
import Mathlib.Tactic

/-!
The finite certificates used in the Hujter--Kisfaludi-Bak argument speak only
about signs of oriented triangle areas.  This file proves that the signs of
real planar points, sorted lexicographically, satisfy the generalized
rank-three signotope rule even when one triple in a quadruple is collinear.
-/

namespace Lax56Proofs.Orientation

open Lax56.Geometry

/-- The three possible signs of an oriented triangle. -/
inductive Sign where
  | neg | zero | pos
  deriving DecidableEq, BEq

open Sign

/-- The sign of the oriented twice-area. -/
noncomputable def turnSign (a b c : Point) : Sign :=
  if turn a b c < 0 then neg else if turn a b c = 0 then zero else pos

def weakNeg (s : Sign) : Prop := s = neg ∨ s = zero
def weakPos (s : Sign) : Prop := s = pos ∨ s = zero

/-- A positive linear combination of two weakly equal signs has that sign. -/
def coneRule (x y out : Sign) : Prop :=
  ((weakNeg x ∧ weakNeg y ∧ (x = neg ∨ y = neg)) → out = neg) ∧
  ((weakPos x ∧ weakPos y ∧ (x = pos ∨ y = pos)) → out = pos)

/-- The generalized signotope constraint on the four triples of an ordered
quadruple, together with the no-four-collinear condition. -/
def AllowedQuad (a b c d : Sign) : Prop :=
  ¬(a = zero ∧ b = zero) ∧ ¬(a = zero ∧ c = zero) ∧
  ¬(a = zero ∧ d = zero) ∧ ¬(b = zero ∧ c = zero) ∧
  ¬(b = zero ∧ d = zero) ∧ ¬(c = zero ∧ d = zero) ∧
  coneRule a c b ∧ coneRule b d c ∧
  ¬(weakNeg a ∧ weakNeg d ∧ weakPos b ∧ weakPos c) ∧
  ¬(weakPos a ∧ weakPos d ∧ weakNeg b ∧ weakNeg c)

/-- At most one of four real numbers vanishes. -/
def NoTwoZero (a b c d : ℝ) : Prop :=
  ¬(a = 0 ∧ b = 0) ∧ ¬(a = 0 ∧ c = 0) ∧ ¬(a = 0 ∧ d = 0) ∧
  ¬(b = 0 ∧ c = 0) ∧ ¬(b = 0 ∧ d = 0) ∧ ¬(c = 0 ∧ d = 0)

@[simp] theorem turnSign_eq_neg_iff (a b c : Point) :
    turnSign a b c = neg ↔ turn a b c < 0 := by
  unfold turnSign
  split_ifs <;> simp_all

@[simp] theorem turnSign_eq_zero_iff (a b c : Point) :
    turnSign a b c = zero ↔ turn a b c = 0 := by
  unfold turnSign
  by_cases hn : turn a b c < 0
  · simp [hn, hn.ne]
  · by_cases hz : turn a b c = 0
    · simp [hn, hz]
    · simp [hn, hz]

@[simp] theorem turnSign_eq_pos_iff (a b c : Point) :
    turnSign a b c = pos ↔ 0 < turn a b c := by
  unfold turnSign
  by_cases hn : turn a b c < 0
  · simp [hn, hn.not_gt]
  · by_cases hz : turn a b c = 0
    · simp [hz]
    · have hp : 0 < turn a b c := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      simp [hn, hz, hp]

@[simp] theorem weakNeg_turnSign_iff (a b c : Point) :
    weakNeg (turnSign a b c) ↔ turn a b c ≤ 0 := by
  rw [weakNeg, turnSign_eq_neg_iff, turnSign_eq_zero_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    rcases h.lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr h

@[simp] theorem weakPos_turnSign_iff (a b c : Point) :
    weakPos (turnSign a b c) ↔ 0 ≤ turn a b c := by
  rw [weakPos, turnSign_eq_pos_iff, turnSign_eq_zero_iff]
  constructor
  · rintro (h | h) <;> linarith
  · intro h
    rcases h.eq_or_lt with h | h
    · exact Or.inr h.symm
    · exact Or.inl h

private lemma positive_combo_neg {α β γ x y z : ℝ}
    (heq : α * x = β * y + γ * z)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hy : y ≤ 0) (hz : z ≤ 0) (hs : y < 0 ∨ z < 0) : x < 0 := by
  have hax : α * x < 0 := by
    rw [heq]
    rcases hs with hy' | hz'
    · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hβ hy')
        (mul_nonpos_of_nonneg_of_nonpos hγ.le hz)
    · exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos hβ.le hy)
        (mul_neg_of_pos_of_neg hγ hz')
  by_contra hx
  exact (not_lt_of_ge (mul_nonneg hα.le (le_of_not_gt hx))) hax

private lemma positive_combo_pos {α β γ x y z : ℝ}
    (heq : α * x = β * y + γ * z)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hs : 0 < y ∨ 0 < z) : 0 < x := by
  have hax : 0 < α * x := by
    rw [heq]
    rcases hs with hy' | hz'
    · exact add_pos_of_pos_of_nonneg (mul_pos hβ hy') (mul_nonneg hγ.le hz)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hβ.le hy) (mul_pos hγ hz')
  by_contra hx
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hα.le (le_of_not_gt hx))) hax

/-- The signotope rule when the four first coordinates are strictly ordered. -/
theorem allowedQuad_of_strict_x
    (a b c d : Point)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (hz : NoTwoZero (turn a b c) (turn a b d) (turn a c d) (turn b c d)) :
    AllowedQuad (turnSign a b c) (turnSign a b d)
      (turnSign a c d) (turnSign b c d) := by
  have hac : a.1 < c.1 := hab.trans hbc
  have had : a.1 < d.1 := hac.trans hcd
  have hbd : b.1 < d.1 := hbc.trans hcd
  have hB :
      (c.1 - a.1) * turn a b d =
        (d.1 - a.1) * turn a b c + (b.1 - a.1) * turn a c d := by
    simp [turn]
    ring
  have hC :
      (d.1 - b.1) * turn a c d =
        (d.1 - c.1) * turn a b d + (d.1 - a.1) * turn b c d := by
    simp [turn]
    ring
  have hMidB :
      (c.1 - b.1) * turn a b d =
        (d.1 - b.1) * turn a b c + (b.1 - a.1) * turn b c d := by
    simp [turn]
    ring
  rcases hz with ⟨hzAB, hzAC, hzAD, hzBC, hzBD, hzCD⟩
  simp only [AllowedQuad, turnSign_eq_zero_iff]
  refine ⟨hzAB, hzAC, hzAD, hzBC, hzBD, hzCD, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hA, hC', hstrict⟩
      rw [turnSign_eq_neg_iff]
      apply positive_combo_neg hB (by linarith) (by linarith) (by linarith)
        ((weakNeg_turnSign_iff _ _ _).mp hA) ((weakNeg_turnSign_iff _ _ _).mp hC')
      simpa using hstrict
    · rintro ⟨hA, hC', hstrict⟩
      rw [turnSign_eq_pos_iff]
      apply positive_combo_pos hB (by linarith) (by linarith) (by linarith)
        ((weakPos_turnSign_iff _ _ _).mp hA) ((weakPos_turnSign_iff _ _ _).mp hC')
      simpa using hstrict
  · constructor
    · rintro ⟨hB', hD, hstrict⟩
      rw [turnSign_eq_neg_iff]
      apply positive_combo_neg hC (by linarith) (by linarith) (by linarith)
        ((weakNeg_turnSign_iff _ _ _).mp hB') ((weakNeg_turnSign_iff _ _ _).mp hD)
      simpa using hstrict
    · rintro ⟨hB', hD, hstrict⟩
      rw [turnSign_eq_pos_iff]
      apply positive_combo_pos hC (by linarith) (by linarith) (by linarith)
        ((weakPos_turnSign_iff _ _ _).mp hB') ((weakPos_turnSign_iff _ _ _).mp hD)
      simpa using hstrict
  · rintro ⟨hA, hD, hB', -⟩
    have hA' := (weakNeg_turnSign_iff _ _ _).mp hA
    have hD' := (weakNeg_turnSign_iff _ _ _).mp hD
    have hs : turn a b c < 0 ∨ turn b c d < 0 := by
      by_contra hn
      push Not at hn
      apply hzAD
      constructor <;> linarith
    have hneg : turn a b d < 0 := positive_combo_neg hMidB
      (by linarith) (by linarith) (by linarith) hA' hD' hs
    exact (not_lt_of_ge ((weakPos_turnSign_iff _ _ _).mp hB')) hneg
  · rintro ⟨hA, hD, hB', -⟩
    have hA' := (weakPos_turnSign_iff _ _ _).mp hA
    have hD' := (weakPos_turnSign_iff _ _ _).mp hD
    have hs : 0 < turn a b c ∨ 0 < turn b c d := by
      by_contra hn
      push Not at hn
      apply hzAD
      constructor <;> linarith
    have hpos : 0 < turn a b d := positive_combo_pos hMidB
      (by linarith) (by linarith) (by linarith) hA' hD' hs
    exact (not_lt_of_ge ((weakNeg_turnSign_iff _ _ _).mp hB')) hpos

/-- A horizontal shear, used only to break ties in lexicographic order. -/
def shear (t : ℝ) (p : Point) : Point := (p.1 + t * p.2, p.2)

@[simp] theorem turn_shear (t : ℝ) (a b c : Point) :
    turn (shear t a) (shear t b) (shear t c) = turn a b c := by
  simp [shear, turn]
  ring

private theorem exists_shearOrder {p q : Point} (hpq : toLex p < toLex q) :
    ∃ e : ℝ, 0 < e ∧ ∀ t : ℝ, 0 < t → t ≤ e →
      (shear t p).1 < (shear t q).1 := by
  rcases Prod.Lex.toLex_lt_toLex.mp hpq with hx | ⟨hx, hy⟩
  · by_cases hyv : p.2 ≤ q.2
    · refine ⟨1, zero_lt_one, ?_⟩
      intro t ht _htle
      have hm : 0 ≤ t * (q.2 - p.2) := mul_nonneg ht.le (sub_nonneg.mpr hyv)
      simp only [shear]
      nlinarith
    · have hyv' : q.2 < p.2 := lt_of_not_ge hyv
      let e : ℝ := (q.1 - p.1) / (2 * (p.2 - q.2))
      have hden : 0 < 2 * (p.2 - q.2) := mul_pos (by norm_num) (sub_pos.mpr hyv')
      have he : 0 < e := div_pos (sub_pos.mpr hx) hden
      refine ⟨e, he, ?_⟩
      intro t ht hte
      have hmul := mul_le_mul_of_nonneg_right hte (sub_nonneg.mpr hyv'.le)
      have heq : e * (p.2 - q.2) = (q.1 - p.1) / 2 := by
        dsimp [e]
        field_simp [ne_of_gt (sub_pos.mpr hyv')]
      simp only [shear]
      nlinarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht _htle
    have hm : t * p.2 < t * q.2 := mul_lt_mul_of_pos_left hy ht
    simp only [shear]
    nlinarith

private theorem exists_shear_strict_x
    {a b c d : Point} (hab : toLex a < toLex b)
    (hbc : toLex b < toLex c) (hcd : toLex c < toLex d) :
    ∃ t : ℝ,
      (shear t a).1 < (shear t b).1 ∧
      (shear t b).1 < (shear t c).1 ∧
      (shear t c).1 < (shear t d).1 := by
  obtain ⟨e₁, he₁, hab'⟩ := exists_shearOrder hab
  obtain ⟨e₂, he₂, hbc'⟩ := exists_shearOrder hbc
  obtain ⟨e₃, he₃, hcd'⟩ := exists_shearOrder hcd
  let t := min e₁ (min e₂ e₃)
  have ht : 0 < t := lt_min he₁ (lt_min he₂ he₃)
  refine ⟨t, hab' t ht (min_le_left _ _),
    hbc' t ht ((min_le_right _ _).trans (min_le_left _ _)),
    hcd' t ht ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The generalized signotope rule for lexicographically ordered points. -/
theorem allowedQuad_of_lex
    (a b c d : Point)
    (hab : toLex a < toLex b) (hbc : toLex b < toLex c)
    (hcd : toLex c < toLex d)
    (hz : NoTwoZero (turn a b c) (turn a b d) (turn a c d) (turn b c d)) :
    AllowedQuad (turnSign a b c) (turnSign a b d)
      (turnSign a c d) (turnSign b c d) := by
  obtain ⟨t, hab', hbc', hcd'⟩ := exists_shear_strict_x hab hbc hcd
  have hs := allowedQuad_of_strict_x
    (shear t a) (shear t b) (shear t c) (shear t d) hab' hbc' hcd' (by
      simpa [NoTwoZero] using hz)
  simpa [turnSign] using hs

/-- A zero determinant puts the third point on the affine line through the
first two. -/
theorem mem_line_of_turn_eq_zero {a b c : Point} (hab : a ≠ b)
    (hz : turn a b c = 0) : c ∈ affineSpan ℝ {a, b} := by
  by_cases hx : a.1 = b.1
  · have hy : a.2 ≠ b.2 := by
      intro h
      apply hab
      exact Prod.ext hx h
    have hcx : c.1 = a.1 := by
      simp only [turn, hx, sub_self, zero_mul, zero_sub] at hz
      have hmul : (b.2 - a.2) * (c.1 - b.1) = 0 := by linarith
      rcases mul_eq_zero.mp hmul with h | h
      · exact (hy (sub_eq_zero.mp h).symm).elim
      · exact (sub_eq_zero.mp h).trans hx.symm
    let t : ℝ := (c.2 - a.2) / (b.2 - a.2)
    have hline : AffineMap.lineMap a b t = c := by
      apply Prod.ext
      · simp [AffineMap.lineMap_apply, t, hx, hcx]
      · simp [AffineMap.lineMap_apply, t]
        field_simp [sub_ne_zero.mpr hy]
        ring
    rw [← hline]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  · let t : ℝ := (c.1 - a.1) / (b.1 - a.1)
    have hline : AffineMap.lineMap a b t = c := by
      apply Prod.ext
      · simp [AffineMap.lineMap_apply, t]
        field_simp [sub_ne_zero.mpr hx]
        ring
      · simp only [AffineMap.lineMap_apply, Prod.snd_sub, Prod.smul_snd, Prod.snd_add]
        dsimp [t]
        field_simp [sub_ne_zero.mpr hx]
        simp only [turn] at hz
        nlinarith
    rw [← hline]
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

theorem turn_swap_last (a b c : Point) : turn a c b = -turn a b c := by
  simp [turn]
  ring

theorem turn_swap_first (a b c : Point) : turn b a c = -turn a b c := by
  simp [turn]
  ring

theorem turn_reverse (a b c : Point) : turn c b a = -turn a b c := by
  simp [turn]
  ring

theorem turn_rotate (a b c : Point) : turn b c a = turn a b c := by
  simp [turn]
  ring

private theorem not_both_turn_zero
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {x y u v : Point} (hxP : x ∈ P) (hyP : y ∈ P)
    (huP : u ∈ P) (hvP : v ∈ P)
    (hxy : x ≠ y) (hux : u ≠ x) (huy : u ≠ y)
    (hvx : v ≠ x) (hvy : v ≠ y) (huv : u ≠ v) :
    ¬(turn x y u = 0 ∧ turn x y v = 0) := by
  rintro ⟨hu, hv⟩
  apply huv
  exact Lax56Proofs.Blockers.third_point_unique hfour hxP hyP huP hvP
    hxy hux huy hvx hvy
    (mem_line_of_turn_eq_zero hxy hu) (mem_line_of_turn_eq_zero hxy hv)

/-- No four collinear points imply that at most one triple of any four
distinct points has zero determinant. -/
theorem noTwoZero_of_noFour
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {a b c d : Point} (haP : a ∈ P) (hbP : b ∈ P)
    (hcP : c ∈ P) (hdP : d ∈ P)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    NoTwoZero (turn a b c) (turn a b d) (turn a c d) (turn b c d) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact not_both_turn_zero hfour haP hbP hcP hdP hab
      hac.symm hbc.symm had.symm hbd.symm hcd
  · rintro ⟨hA, hC⟩
    apply not_both_turn_zero hfour haP hcP hbP hdP hac
      hab.symm hbc had.symm hcd.symm hbd
    exact ⟨by rw [turn_swap_last, hA, neg_zero], hC⟩
  · rintro ⟨hA, hD⟩
    apply not_both_turn_zero hfour hbP hcP haP hdP hbc
      hab hac hbd.symm hcd.symm had
    exact ⟨by rw [turn_rotate, hA], hD⟩
  · rintro ⟨hB, hC⟩
    apply not_both_turn_zero hfour haP hdP hbP hcP had
      hab.symm hbd hac.symm hcd hbc
    exact ⟨by rw [turn_swap_last, hB, neg_zero],
      by rw [turn_swap_last, hC, neg_zero]⟩
  · rintro ⟨hB, hD⟩
    apply not_both_turn_zero hfour hbP hdP haP hcP hbd
      hab had hbc.symm hcd hac
    exact ⟨by rw [turn_rotate, hB], by rw [turn_swap_last, hD, neg_zero]⟩
  · rintro ⟨hC, hD⟩
    apply not_both_turn_zero hfour hcP hdP haP hbP hcd
      hac had hbc hbd hab
    exact ⟨by rw [turn_rotate, hC], by rw [turn_rotate, hD]⟩

/-- A point on an open segment makes a zero oriented area. -/
theorem turn_eq_zero_of_mem_openSegment {a b c : Point}
    (hc : c ∈ openSegment ℝ a b) : turn a c b = 0 := by
  rw [openSegment_eq_image] at hc
  obtain ⟨t, -, rfl⟩ := hc
  simp [turn]
  ring

end Lax56Proofs.Orientation
