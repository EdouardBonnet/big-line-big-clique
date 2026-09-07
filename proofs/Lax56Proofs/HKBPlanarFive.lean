import Lax56Proofs.HKBConcaveColour
import Mathlib.Tactic

/-!
A finite order-type formulation of the elementary fact that five points in
general position have seven pairwise noncrossing connecting segments.

Only the ten orientation signs of increasing triples are enumerated.  The
enumeration is checked by Lean's kernel (`decide`), and its geometric
interpretation is proved below from the real determinant identities.
-/

namespace Lax56Proofs.HKBPlanarFive

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- The ten edges of the complete graph on five ordered vertices. -/
def fiveEdgeEnds : Fin 10 → Fin 5 × Fin 5 := ![
  (0, 1), (0, 2), (0, 3), (0, 4), (1, 2),
  (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- The ten increasing triples of five ordered vertices. -/
def fiveTripleEnds : Fin 10 → Fin 5 × Fin 5 × Fin 5 := ![
  (0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 3), (0, 2, 4),
  (0, 3, 4), (1, 2, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4)]

theorem fiveEdgeEnds_injective : Function.Injective fiveEdgeEnds := by
  decide

theorem fiveEdgeEnds_ne (e : Fin 10) :
    (fiveEdgeEnds e).1 ≠ (fiveEdgeEnds e).2 := by
  fin_cases e <;> decide

/-- Index of the unordered triple.  The final default branch is used only
when the three inputs are not distinct. -/
def fiveTripleIndex (i j k : Fin 5) : Fin 10 :=
  if ({i, j, k} : Finset (Fin 5)) = {0, 1, 2} then 0
  else if ({i, j, k} : Finset (Fin 5)) = {0, 1, 3} then 1
  else if ({i, j, k} : Finset (Fin 5)) = {0, 1, 4} then 2
  else if ({i, j, k} : Finset (Fin 5)) = {0, 2, 3} then 3
  else if ({i, j, k} : Finset (Fin 5)) = {0, 2, 4} then 4
  else if ({i, j, k} : Finset (Fin 5)) = {0, 3, 4} then 5
  else if ({i, j, k} : Finset (Fin 5)) = {1, 2, 3} then 6
  else if ({i, j, k} : Finset (Fin 5)) = {1, 2, 4} then 7
  else if ({i, j, k} : Finset (Fin 5)) = {1, 3, 4} then 8
  else 9

def cyclicOrder (i j k a b c : Fin 5) : Bool :=
  (i == a && j == b && k == c) ||
  (i == b && j == c && k == a) ||
  (i == c && j == a && k == b)

/-- Recover the orientation of an arbitrary ordered triple from the sign of
its increasing reordering. -/
def orientedPositive (sign : Fin 10 → Bool) (i j k : Fin 5) : Bool :=
  let t := fiveTripleIndex i j k
  let abc := fiveTripleEnds t
  if cyclicOrder i j k abc.1 abc.2.1 abc.2.2 then sign t else !sign t

/-- Two straight edges cross when both pairs of endpoints occur on opposite
sides of the other supporting line. -/
def edgeCrosses (sign : Fin 10 → Bool) (e f : Fin 10) : Prop :=
  let ab := fiveEdgeEnds e
  let cd := fiveEdgeEnds f
  ab.1 ≠ cd.1 ∧ ab.1 ≠ cd.2 ∧ ab.2 ≠ cd.1 ∧ ab.2 ≠ cd.2 ∧
    orientedPositive sign ab.1 ab.2 cd.1 ≠
      orientedPositive sign ab.1 ab.2 cd.2 ∧
    orientedPositive sign cd.1 cd.2 ab.1 ≠
      orientedPositive sign cd.1 cd.2 ab.2

instance edgeCrossesDecidable (sign : Fin 10 → Bool) (e f : Fin 10) :
    Decidable (edgeCrosses sign e f) := by
  unfold edgeCrosses
  infer_instance

def bitChange (a b : Bool) : ℕ := if a = b then 0 else 1

/-- The nonzero rank-three signotope condition: along the four triples of
an increasing quadruple the sign changes at most once. -/
def quadOKBits (a b c d : Bool) : Prop :=
  bitChange a b + bitChange b c + bitChange c d ≤ 1

instance quadOKBitsDecidable (a b c d : Bool) : Decidable (quadOKBits a b c d) := by
  unfold quadOKBits
  infer_instance

/-- The four triples of the increasing quadruple obtained by omitting `q`. -/
def fiveQuadTriples : Fin 5 → Fin 10 × Fin 10 × Fin 10 × Fin 10 := ![
  (6, 7, 8, 9), (3, 4, 5, 9), (1, 2, 5, 8),
  (0, 2, 4, 7), (0, 1, 3, 6)]

def allQuadsOK (sign : Fin 10 → Bool) : Prop :=
  ∀ q : Fin 5,
    let t := fiveQuadTriples q
    quadOKBits (sign t.1) (sign t.2.1) (sign t.2.2.1) (sign t.2.2.2)

instance allQuadsOKDecidable (sign : Fin 10 → Bool) : Decidable (allQuadsOK sign) := by
  unfold allQuadsOK
  infer_instance

def HasSevenNoncrossingEdges (sign : Fin 10 → Bool) : Prop :=
  ∃ E : Finset (Fin 10), E.card = 7 ∧
    ∀ e ∈ E, ∀ f ∈ E, e ≠ f → ¬edgeCrosses sign e f

instance hasSevenNoncrossingEdgesDecidable (sign : Fin 10 → Bool) :
    Decidable (HasSevenNoncrossingEdges sign) := by
  unfold HasSevenNoncrossingEdges
  infer_instance

def signOfBool : Bool → Sign
  | false => .neg
  | true => .pos

/-- On nonzero signs, the generalized signotope rule is exactly the
at-most-one-change rule used by the finite five-point check. -/
theorem quadOKBits_of_allowedQuad (a b c d : Bool)
    (h : AllowedQuad (signOfBool a) (signOfBool b)
      (signOfBool c) (signOfBool d)) :
    quadOKBits a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [quadOKBits, bitChange, AllowedQuad, coneRule,
      weakNeg, weakPos, signOfBool]

theorem turnSign_eq_signOfBool_of_ne_zero
    (a b c : Point) (hne : turn a b c ≠ 0) :
    turnSign a b c = signOfBool (decide (0 < turn a b c)) := by
  by_cases hp : 0 < turn a b c
  · simp [signOfBool, hp]
  · have hn : turn a b c < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hp) hne
    simp [signOfBool, hp, hn]

/-- Real ordered quadruples satisfying `AllowedQuad` satisfy the Boolean
condition consumed by the finite order-type lemma. -/
theorem quadOKBits_of_real_allowedQuad
    (a b c d : Point)
    (hallowed : AllowedQuad (turnSign a b c) (turnSign a b d)
      (turnSign a c d) (turnSign b c d))
    (hA : turn a b c ≠ 0) (hB : turn a b d ≠ 0)
    (hC : turn a c d ≠ 0) (hD : turn b c d ≠ 0) :
    quadOKBits (decide (0 < turn a b c)) (decide (0 < turn a b d))
      (decide (0 < turn a c d)) (decide (0 < turn b c d)) := by
  apply quadOKBits_of_allowedQuad
  simpa [turnSign_eq_signOfBool_of_ne_zero a b c hA,
    turnSign_eq_signOfBool_of_ne_zero a b d hB,
    turnSign_eq_signOfBool_of_ne_zero a c d hC,
    turnSign_eq_signOfBool_of_ne_zero b c d hD] using hallowed

private theorem decide_pos_neg_of_ne_zero (r : ℝ) (hr : r ≠ 0) :
    decide (0 < -r) = !(decide (0 < r)) := by
  rcases lt_or_gt_of_ne hr with hrneg | hrpos
  · have hnpos : ¬0 < r := by linarith
    have hnegpos : 0 < -r := by linarith
    simp [hnpos, hnegpos]
  · have hnnegpos : ¬0 < -r := by linarith
    simp [hrpos, hnnegpos]

def EvenTriplePermutation (i j k a b c : Fin 5) : Prop :=
  (i = a ∧ j = b ∧ k = c) ∨
  (i = b ∧ j = c ∧ k = a) ∨
  (i = c ∧ j = a ∧ k = b)

def OddTriplePermutation (i j k a b c : Fin 5) : Prop :=
  (i = a ∧ j = c ∧ k = b) ∨
  (i = c ∧ j = b ∧ k = a) ∨
  (i = b ∧ j = a ∧ k = c)

instance evenTriplePermutationDecidable (i j k a b c : Fin 5) :
    Decidable (EvenTriplePermutation i j k a b c) := by
  unfold EvenTriplePermutation
  infer_instance

instance oddTriplePermutationDecidable (i j k a b c : Fin 5) :
    Decidable (OddTriplePermutation i j k a b c) := by
  unfold OddTriplePermutation
  infer_instance

/-- The lookup table returns the increasing triple and records precisely the
parity of the requested ordering. -/
theorem fiveTripleIndex_permutation : ∀ i j k : Fin 5,
    i ≠ j → i ≠ k → j ≠ k →
    let abc := fiveTripleEnds (fiveTripleIndex i j k)
    (cyclicOrder i j k abc.1 abc.2.1 abc.2.2 = true ∧
      EvenTriplePermutation i j k abc.1 abc.2.1 abc.2.2) ∨
    (cyclicOrder i j k abc.1 abc.2.1 abc.2.2 = false ∧
      OddTriplePermutation i j k abc.1 abc.2.1 abc.2.2) := by
  decide

/-- Correctness of the lookup table recovering arbitrary orientations from
the ten increasing-triple signs. -/
theorem orientedPositive_real
    (x : Fin 5 → Point) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hne : turn (x i) (x j) (x k) ≠ 0) :
    orientedPositive (fun t ↦
      let abc := fiveTripleEnds t
      decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2))) i j k =
        decide (0 < turn (x i) (x j) (x k)) := by
  let t := fiveTripleIndex i j k
  let abc := fiveTripleEnds t
  have hspec := fiveTripleIndex_permutation i j k hij hik hjk
  change (if cyclicOrder i j k abc.1 abc.2.1 abc.2.2 then
      decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2))
    else !(decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2)))) =
      decide (0 < turn (x i) (x j) (x k))
  change ((cyclicOrder i j k abc.1 abc.2.1 abc.2.2 = true ∧
      EvenTriplePermutation i j k abc.1 abc.2.1 abc.2.2) ∨
    (cyclicOrder i j k abc.1 abc.2.1 abc.2.2 = false ∧
      OddTriplePermutation i j k abc.1 abc.2.1 abc.2.2)) at hspec
  rcases hspec with ⟨hcyc, heven⟩ | ⟨hcyc, hodd⟩
  · simp only [hcyc, if_true]
    rcases heven with h | h | h
    · rcases h with ⟨hi, hj, hk⟩
      rw [hi, hj, hk]
    · rcases h with ⟨hi, hj, hk⟩
      rw [hi, hj, hk,
        turn_rotate (x abc.1) (x abc.2.1) (x abc.2.2)]
    · rcases h with ⟨hi, hj, hk⟩
      rw [hi, hj, hk,
        turn_rotate (x abc.2.1) (x abc.2.2) (x abc.1),
        turn_rotate (x abc.1) (x abc.2.1) (x abc.2.2)]
  · simp only [hcyc, Bool.false_eq]
    rcases hodd with h | h | h
    · rcases h with ⟨hi, hj, hk⟩
      have hne' : turn (x abc.1) (x abc.2.2) (x abc.2.1) ≠ 0 := by
        rw [← hi, ← hj, ← hk]
        exact hne
      have hbase : turn (x abc.1) (x abc.2.1) (x abc.2.2) ≠ 0 := by
        intro hz
        apply hne'
        rw [turn_swap_last, hz, neg_zero]
      rw [hi, hj, hk,
        turn_swap_last (x abc.1) (x abc.2.1) (x abc.2.2)]
      exact (decide_pos_neg_of_ne_zero _ hbase).symm
    · rcases h with ⟨hi, hj, hk⟩
      have hne' : turn (x abc.2.2) (x abc.2.1) (x abc.1) ≠ 0 := by
        rw [← hi, ← hj, ← hk]
        exact hne
      have hbase : turn (x abc.1) (x abc.2.1) (x abc.2.2) ≠ 0 := by
        intro hz
        apply hne'
        rw [turn_reverse, hz, neg_zero]
      rw [hi, hj, hk,
        turn_reverse (x abc.1) (x abc.2.1) (x abc.2.2)]
      exact (decide_pos_neg_of_ne_zero _ hbase).symm
    · rcases h with ⟨hi, hj, hk⟩
      have hne' : turn (x abc.2.1) (x abc.1) (x abc.2.2) ≠ 0 := by
        rw [← hi, ← hj, ← hk]
        exact hne
      have hbase : turn (x abc.1) (x abc.2.1) (x abc.2.2) ≠ 0 := by
        intro hz
        apply hne'
        rw [turn_swap_first, hz, neg_zero]
      rw [hi, hj, hk,
        turn_swap_first (x abc.1) (x abc.2.1) (x abc.2.2)]
      exact (decide_pos_neg_of_ne_zero _ hbase).symm

/-- The ten orientation bits of five lexicographically ordered points satisfy
the finite signotope constraints. -/
theorem allQuadsOK_of_real
    (x : Fin 5 → Point)
    (hlex : StrictMono (fun i ↦ toLex (x i)))
    (hgeneral : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      turn (x i) (x j) (x k) ≠ 0) :
    allQuadsOK (fun t ↦
      let abc := fiveTripleEnds t
      decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2))) := by
  let sign : Fin 10 → Bool := fun t ↦
    let abc := fiveTripleEnds t
    decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2))
  have hquad (a b c d : Fin 5) (hab : a < b) (hbc : b < c) (hcd : c < d) :
      quadOKBits
        (decide (0 < turn (x a) (x b) (x c)))
        (decide (0 < turn (x a) (x b) (x d)))
        (decide (0 < turn (x a) (x c) (x d)))
        (decide (0 < turn (x b) (x c) (x d))) := by
    have hab' : a ≠ b := ne_of_lt hab
    have hac' : a ≠ c := ne_of_lt (hab.trans hbc)
    have had' : a ≠ d := ne_of_lt (hab.trans (hbc.trans hcd))
    have hbc' : b ≠ c := ne_of_lt hbc
    have hbd' : b ≠ d := ne_of_lt (hbc.trans hcd)
    have hcd' : c ≠ d := ne_of_lt hcd
    have hA := hgeneral a b c hab' hac' hbc'
    have hB := hgeneral a b d hab' had' hbd'
    have hC := hgeneral a c d hac' had' hcd'
    have hD := hgeneral b c d hbc' hbd' hcd'
    apply quadOKBits_of_real_allowedQuad (hA := hA) (hB := hB)
      (hC := hC) (hD := hD)
    apply allowedQuad_of_lex (x a) (x b) (x c) (x d)
      (hlex hab) (hlex hbc) (hlex hcd)
    simp only [NoTwoZero, hA, hB, hC, hD, false_and, not_false_eq_true,
      true_and]
  intro q
  fin_cases q
  · simpa [fiveQuadTriples, sign] using hquad 1 2 3 4 (by decide) (by decide) (by decide)
  · simpa [fiveQuadTriples, sign] using hquad 0 2 3 4 (by decide) (by decide) (by decide)
  · simpa [fiveQuadTriples, sign] using hquad 0 1 3 4 (by decide) (by decide) (by decide)
  · simpa [fiveQuadTriples, sign] using hquad 0 1 2 4 (by decide) (by decide) (by decide)
  · simpa [fiveQuadTriples, sign] using hquad 0 1 2 3 (by decide) (by decide) (by decide)

-- Exhaustive check of the `2^10` nonzero order types.  This is the finite
-- core of Lemma 6.1.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem seven_noncrossing_edges_of_allQuadsOK :
    ∀ sign : Fin 10 → Bool,
      allQuadsOK sign → HasSevenNoncrossingEdges sign := by
  decide

private theorem positive_bits_differ_of_strict_combo_zero
    (a b t : ℝ) (ht : 0 < t) (ht1 : t < 1) (ha : a ≠ 0)
    (heq : (1 - t) * a + t * b = 0) :
    decide (0 < a) ≠ decide (0 < b) := by
  have hcoef : 0 < 1 - t := sub_pos.mpr ht1
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hbPos : 0 < b := by
      by_contra h
      have hbNonpos : b ≤ 0 := le_of_not_gt h
      have hleft : (1 - t) * a < 0 := mul_neg_of_pos_of_neg hcoef haNeg
      have hright : t * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hbNonpos
      linarith
    simp [haNeg.not_gt, hbPos]
  · have hbNeg : b < 0 := by
      by_contra h
      have hbNonneg : 0 ≤ b := le_of_not_gt h
      have hleft : 0 < (1 - t) * a := mul_pos hcoef haPos
      have hright : 0 ≤ t * b := mul_nonneg ht.le hbNonneg
      linarith
    simp [haPos, hbNeg.not_gt]

/-- If two open segments meet, the endpoints of either segment lie on
opposite sides of the other supporting line (provided the turns are
nonzero). -/
theorem positive_bits_differ_of_common_openSegment
    {a b c d p : Point}
    (hpab : p ∈ openSegment ℝ a b) (hpcd : p ∈ openSegment ℝ c d)
    (hne : turn a b c ≠ 0) :
    decide (0 < turn a b c) ≠ decide (0 < turn a b d) := by
  have hpzero : turn a b p = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hpab, neg_zero]
  obtain ⟨t, ht, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := a) (b := b) hpcd
  exact positive_bits_differ_of_strict_combo_zero
    (turn a b c) (turn a b d) t ht ht1 hne (heq.symm.trans hpzero)

/-- Geometric correctness of the Boolean crossing predicate. -/
theorem edgeCrosses_of_common_openSegment
    (x : Fin 5 → Point)
    (hgeneral : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      turn (x i) (x j) (x k) ≠ 0)
    (e f : Fin 10)
    (hac : (fiveEdgeEnds e).1 ≠ (fiveEdgeEnds f).1)
    (had : (fiveEdgeEnds e).1 ≠ (fiveEdgeEnds f).2)
    (hbc : (fiveEdgeEnds e).2 ≠ (fiveEdgeEnds f).1)
    (hbd : (fiveEdgeEnds e).2 ≠ (fiveEdgeEnds f).2)
    {p : Point}
    (hpe : p ∈ openSegment ℝ
      (x (fiveEdgeEnds e).1) (x (fiveEdgeEnds e).2))
    (hpf : p ∈ openSegment ℝ
      (x (fiveEdgeEnds f).1) (x (fiveEdgeEnds f).2)) :
    edgeCrosses (fun t ↦
      let abc := fiveTripleEnds t
      decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2))) e f := by
  let a := (fiveEdgeEnds e).1
  let b := (fiveEdgeEnds e).2
  let c := (fiveEdgeEnds f).1
  let d := (fiveEdgeEnds f).2
  have hab : a ≠ b := fiveEdgeEnds_ne e
  have hcd : c ≠ d := fiveEdgeEnds_ne f
  have hABC := hgeneral a b c hab hac hbc
  have hABD := hgeneral a b d hab had hbd
  have hCDA := hgeneral c d a hcd hac.symm had.symm
  have hCDB := hgeneral c d b hcd hbc.symm hbd.symm
  have hop1 := positive_bits_differ_of_common_openSegment hpe hpf hABC
  have hop2 := positive_bits_differ_of_common_openSegment hpf hpe hCDA
  unfold edgeCrosses
  dsimp only [a, b, c, d] at hab hcd hABC hABD hCDA hCDB hop1 hop2 ⊢
  refine ⟨hac, had, hbc, hbd, ?_, ?_⟩
  · simpa only [orientedPositive_real x _ _ _ hab hac hbc hABC,
      orientedPositive_real x _ _ _ hab had hbd hABD] using hop1
  · simpa only [orientedPositive_real x _ _ _ hcd hac.symm had.symm hCDA,
      orientedPositive_real x _ _ _ hcd hbc.symm hbd.symm hCDB] using hop2

theorem fiveEdgeEnds_lt (e : Fin 10) :
    (fiveEdgeEnds e).1 < (fiveEdgeEnds e).2 := by
  fin_cases e <;> decide

private theorem second_ne_of_distinct_edges_first_eq : ∀ e f : Fin 10,
    e ≠ f → (fiveEdgeEnds e).1 = (fiveEdgeEnds f).1 →
      (fiveEdgeEnds e).2 ≠ (fiveEdgeEnds f).2 := by
  decide

private theorem second_ne_first_of_distinct_edges_first_eq_second : ∀ e f : Fin 10,
    e ≠ f → (fiveEdgeEnds e).1 = (fiveEdgeEnds f).2 →
      (fiveEdgeEnds e).2 ≠ (fiveEdgeEnds f).1 := by
  decide

private theorem first_ne_second_of_distinct_edges_second_eq_first : ∀ e f : Fin 10,
    e ≠ f → (fiveEdgeEnds e).2 = (fiveEdgeEnds f).1 →
      (fiveEdgeEnds e).1 ≠ (fiveEdgeEnds f).2 := by
  decide

private theorem first_ne_of_distinct_edges_second_eq : ∀ e f : Fin 10,
    e ≠ f → (fiveEdgeEnds e).2 = (fiveEdgeEnds f).2 →
      (fiveEdgeEnds e).1 ≠ (fiveEdgeEnds f).1 := by
  decide

private theorem turn_eq_zero_of_common_left_openSegments
    {a b c p : Point}
    (hpab : p ∈ openSegment ℝ a b)
    (hpac : p ∈ openSegment ℝ a c) :
    turn a b c = 0 := by
  have hpzero : turn a b p = 0 := by
    rw [turn_swap_last, turn_eq_zero_of_mem_openSegment hpab, neg_zero]
  obtain ⟨t, ht, -, heq⟩ :=
    turn_of_mem_openSegment (a := a) (b := b) hpac
  have haa : turn a b a = 0 := by simp [turn]
  rw [haa, mul_zero, zero_add] at heq
  nlinarith

/-- Five lexicographically ordered points in general position have seven
edges whose relative interiors are pairwise disjoint. -/
theorem exists_seven_geometrically_noncrossing_edges
    (x : Fin 5 → Point)
    (hlex : StrictMono (fun i ↦ toLex (x i)))
    (hgeneral : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      turn (x i) (x j) (x k) ≠ 0) :
    ∃ E : Finset (Fin 10), E.card = 7 ∧
      ∀ e ∈ E, ∀ f ∈ E, e ≠ f →
        Disjoint
          (openSegment ℝ (x (fiveEdgeEnds e).1) (x (fiveEdgeEnds e).2))
          (openSegment ℝ (x (fiveEdgeEnds f).1) (x (fiveEdgeEnds f).2)) := by
  let sign : Fin 10 → Bool := fun t ↦
    let abc := fiveTripleEnds t
    decide (0 < turn (x abc.1) (x abc.2.1) (x abc.2.2))
  obtain ⟨E, hEcard, hEnon⟩ :=
    seven_noncrossing_edges_of_allQuadsOK sign (allQuadsOK_of_real x hlex hgeneral)
  refine ⟨E, hEcard, ?_⟩
  intro e heE f hfE hef
  rw [Set.disjoint_left]
  intro p hpe hpf
  let a := (fiveEdgeEnds e).1
  let b := (fiveEdgeEnds e).2
  let c := (fiveEdgeEnds f).1
  let d := (fiveEdgeEnds f).2
  have hab : a ≠ b := fiveEdgeEnds_ne e
  have hcd : c ≠ d := fiveEdgeEnds_ne f
  have hac : a ≠ c := by
    intro hacEq
    have hbd := second_ne_of_distinct_edges_first_eq e f hef hacEq
    have had' : a ≠ d := by
      intro hadEq
      exact hcd (hacEq.symm.trans hadEq)
    have hz : turn (x a) (x b) (x d) = 0 := by
      apply turn_eq_zero_of_common_left_openSegments hpe
      simpa only [a, c, hacEq] using hpf
    exact hgeneral a b d hab had' hbd hz
  have had : a ≠ d := by
    intro hadEq
    have hbc := second_ne_first_of_distinct_edges_first_eq_second e f hef hadEq
    have hac' : a ≠ c := by
      intro hacEq
      exact hcd (hacEq.symm.trans hadEq)
    have hz : turn (x a) (x b) (x c) = 0 := by
      apply turn_eq_zero_of_common_left_openSegments hpe
      rw [openSegment_symm]
      simpa only [a, d, hadEq] using hpf
    exact hgeneral a b c hab hac' hbc hz
  have hbc : b ≠ c := by
    intro hbcEq
    have had := first_ne_second_of_distinct_edges_second_eq_first e f hef hbcEq
    have hbd' : b ≠ d := by
      intro hbdEq
      exact hcd (hbcEq.symm.trans hbdEq)
    have hz : turn (x b) (x a) (x d) = 0 := by
      apply turn_eq_zero_of_common_left_openSegments
      · simpa only [openSegment_symm] using hpe
      · simpa only [b, c, hbcEq] using hpf
    exact hgeneral b a d hab.symm hbd' had hz
  have hbd : b ≠ d := by
    intro hbdEq
    have hac := first_ne_of_distinct_edges_second_eq e f hef hbdEq
    have hbc' : b ≠ c := by
      intro hbcEq
      exact hcd (hbcEq.symm.trans hbdEq)
    have hz : turn (x b) (x a) (x c) = 0 := by
      apply turn_eq_zero_of_common_left_openSegments
      · simpa only [openSegment_symm] using hpe
      · rw [openSegment_symm]
        simpa only [b, d, hbdEq] using hpf
    exact hgeneral b a c hab.symm hbc' hac hz
  exact (hEnon e heE f hfE hef)
    (edgeCrosses_of_common_openSegment x hgeneral e f hac had hbc hbd hpe hpf)

/-- Seven noncrossing pairs among five same-coloured points have seven
distinct blockers, all of a different colour and all in the convex hull of
the five points. -/
theorem exists_seven_distinct_blockers_of_five_mono
    {k : ℕ} {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin k) (hproper : ProperBlocking B colour)
    (c : Fin k) (x : Fin 5 → B)
    (hinj : Function.Injective x)
    (hmono : ∀ i, colour (x i) = c)
    (hlex : StrictMono (fun i ↦ toLex (x i : Point))) :
    ∃ R : Finset B, R.card = 7 ∧
      (∀ r ∈ R, colour r ≠ c) ∧
      ∀ r ∈ R, (r : Point) ∈
        convexHull ℝ (Set.range fun i ↦ (x i : Point)) := by
  classical
  have hgeneral : ∀ i j k : Fin 5, i ≠ j → i ≠ k → j ≠ k →
      turn (x i : Point) (x j : Point) (x k : Point) ≠ 0 := by
    intro i j k hij hik hjk
    apply turn_ne_zero_of_same_colour hfour hproper
      (hinj.ne hij) (hinj.ne hjk) (hinj.ne hik).symm
      (hmono i |>.trans (hmono j).symm)
      (hmono j |>.trans (hmono k).symm)
  obtain ⟨E, hEcard, hEnon⟩ :=
    exists_seven_geometrically_noncrossing_edges
      (fun i ↦ (x i : Point)) hlex hgeneral
  have hpair (e : Fin 10) :
      x (fiveEdgeEnds e).1 ≠ x (fiveEdgeEnds e).2 :=
    hinj.ne (fiveEdgeEnds_ne e)
  have hpairColour (e : Fin 10) :
      colour (x (fiveEdgeEnds e).1) = colour (x (fiveEdgeEnds e).2) :=
    (hmono _).trans (hmono _).symm
  choose r hr using fun e ↦ hproper
    (x (fiveEdgeEnds e).1) (x (fiveEdgeEnds e).2)
    (hpair e) (hpairColour e)
  have hrInj : Set.InjOn r E := by
    intro e heE f hfE herf
    by_contra hef
    have hdisjoint := hEnon e heE f hfE hef
    rw [Set.disjoint_left] at hdisjoint
    exact hdisjoint (hr e) (by simpa only [herf] using hr f)
  let R : Finset B := E.image r
  refine ⟨R, ?_, ?_, ?_⟩
  · change (E.image r).card = 7
    rw [E.card_image_of_injOn hrInj, hEcard]
  · intro z hzR
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hzR
    intro hrc
    have hne := blocker_colour_ne hfour hproper
      (hpair e) (hpairColour e) (hr e)
    exact hne (hrc.trans (hmono _).symm)
  · intro z hzR
    obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hzR
    exact (segment_subset_convexHull
      (Set.mem_range_self (fiveEdgeEnds e).1)
      (Set.mem_range_self (fiveEdgeEnds e).2))
      (openSegment_subset_segment ℝ _ _ (hr e))

end Lax56Proofs.HKBPlanarFive
