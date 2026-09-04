import Lax56Proofs.Blockers
import Mathlib.Tactic

namespace Lax56Proofs.WeightedPairs

open scoped BigOperators
open Lax56.Geometry
open Lax56Proofs.OrderGeometry
open Lax56Proofs.Blockers

/-- An unordered pair represented by its increasing ordering. -/
abbrev OrderedPair (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}

namespace OrderedPair

def left {n : ℕ} (e : OrderedPair n) : Fin n := e.1.1
def right {n : ℕ} (e : OrderedPair n) : Fin n := e.1.2

theorem left_lt_right {n : ℕ} (e : OrderedPair n) : e.left < e.right := e.2

@[ext] theorem ext {n : ℕ} {e f : OrderedPair n}
    (hl : e.left = f.left) (hr : e.right = f.right) : e = f := by
  apply Subtype.ext
  exact Prod.ext hl hr

/-- The positive difference between the two indices. -/
def stretch {n : ℕ} (e : OrderedPair n) : ℕ := e.right - e.left

theorem stretch_pos {n : ℕ} (e : OrderedPair n) : 0 < e.stretch := by
  simp only [stretch, left, right]
  omega

/-- Reciprocal-stretch weight. -/
noncomputable def weight {n : ℕ} (e : OrderedPair n) : ℝ :=
  1 / (e.stretch : ℝ)

theorem weight_nonneg {n : ℕ} (e : OrderedPair n) : 0 ≤ e.weight := by
  unfold weight
  positivity

end OrderedPair

/-- Increasing pairs which are not visible in the ambient point set. -/
abbrev BadPair (P : Finset Point) :=
  {e : OrderedPair P.card //
    ¬Visible P (orderedPoint P e.left) (orderedPoint P e.right)}

noncomputable instance badPairFintype (P : Finset Point) : Fintype (BadPair P) :=
  Fintype.ofFinite _

theorem exists_blockerIndex (P : Finset Point) (e : BadPair P) :
    ∃ k : Fin P.card,
      e.1.left < k ∧ k < e.1.right ∧
        orderedPoint P k ∈
          openSegment ℝ (orderedPoint P e.1.left) (orderedPoint P e.1.right) := by
  have hneq : orderedPoint P e.1.left ≠ orderedPoint P e.1.right :=
    (orderedPoint_injective P).ne e.1.left_lt_right.ne
  obtain ⟨r, hrP, hrseg⟩ := exists_blocker hneq e.2
  obtain ⟨k, rfl⟩ := orderedPoint_surjective P r hrP
  have hbetween := lex_between_of_mem_openSegment
    ((orderedPoint_strictMono P) e.1.left_lt_right) hrseg
  exact ⟨k,
    (orderedPoint_strictMono P).lt_iff_lt.mp hbetween.1,
    (orderedPoint_strictMono P).lt_iff_lt.mp hbetween.2,
    hrseg⟩

/-- The unique blocker index chosen for a nonvisible pair. -/
noncomputable def blockerIndex (P : Finset Point) (e : BadPair P) : Fin P.card :=
  Classical.choose (exists_blockerIndex P e)

theorem left_lt_blockerIndex (P : Finset Point) (e : BadPair P) :
    e.1.left < blockerIndex P e :=
  (Classical.choose_spec (exists_blockerIndex P e)).1

theorem blockerIndex_lt_right (P : Finset Point) (e : BadPair P) :
    blockerIndex P e < e.1.right :=
  (Classical.choose_spec (exists_blockerIndex P e)).2.1

theorem blockerIndex_mem_openSegment (P : Finset Point) (e : BadPair P) :
    orderedPoint P (blockerIndex P e) ∈
      openSegment ℝ (orderedPoint P e.1.left) (orderedPoint P e.1.right) :=
  (Classical.choose_spec (exists_blockerIndex P e)).2.2

def mkPair {n : ℕ} (i j : Fin n) (h : i < j) : OrderedPair n :=
  ⟨(i, j), h⟩

/-- The three positions in the charging triple. -/
inductive ChargeKind
  | left
  | right
  | outer
  deriving DecidableEq, Fintype

/-- The three pairs charged by a blocked pair: left-blocker,
blocker-right, and left-right. -/
noncomputable def chargePair (P : Finset Point) (x : BadPair P × ChargeKind) :
    OrderedPair P.card :=
  let e := x.1
  let k := blockerIndex P e
  match x.2 with
  | .left => mkPair e.1.left k (left_lt_blockerIndex P e)
  | .right => mkPair k e.1.right (blockerIndex_lt_right P e)
  | .outer => e.1

/-- The point of the blocked triple omitted by `chargePair`. -/
noncomputable def thirdIndex (P : Finset Point) (x : BadPair P × ChargeKind) : Fin P.card :=
  let e := x.1
  match x.2 with
  | .left => e.1.right
  | .right => e.1.left
  | .outer => blockerIndex P e

theorem chargeData_injective (P : Finset Point) :
    Function.Injective
      (fun x : BadPair P × ChargeKind ↦ (chargePair P x, thirdIndex P x)) := by
  rintro ⟨e, t⟩ ⟨f, u⟩ h
  have heij : e.1.1.1.val < e.1.1.2.val := e.1.2
  have hfij : f.1.1.1.val < f.1.1.2.val := f.1.2
  have hek₁ : e.1.1.1.val < (blockerIndex P e).val := by
    simpa [OrderedPair.left] using left_lt_blockerIndex P e
  have hek₂ : (blockerIndex P e).val < e.1.1.2.val := by
    simpa [OrderedPair.right] using blockerIndex_lt_right P e
  have hfk₁ : f.1.1.1.val < (blockerIndex P f).val := by
    simpa [OrderedPair.left] using left_lt_blockerIndex P f
  have hfk₂ : (blockerIndex P f).val < f.1.1.2.val := by
    simpa [OrderedPair.right] using blockerIndex_lt_right P f
  have hl := congrArg
    (fun z : OrderedPair P.card × Fin P.card ↦ z.1.left.val) h
  have hr := congrArg
    (fun z : OrderedPair P.card × Fin P.card ↦ z.1.right.val) h
  have hthird := congrArg
    (fun z : OrderedPair P.card × Fin P.card ↦ z.2.val) h
  cases t <;> cases u <;>
    simp [chargePair, thirdIndex, mkPair, OrderedPair.left, OrderedPair.right]
      at hl hr hthird ⊢
  · apply Subtype.ext
    exact OrderedPair.ext (Fin.ext hl) (Fin.ext hthird)
  · omega
  · omega
  · omega
  · apply Subtype.ext
    exact OrderedPair.ext (Fin.ext hthird) (Fin.ext hr)
  · omega
  · omega
  · omega
  · apply Subtype.ext
    exact OrderedPair.ext (Fin.ext hl) (Fin.ext hr)

theorem third_mem_affineSpan_charge (P : Finset Point) (x : BadPair P × ChargeKind) :
    orderedPoint P (thirdIndex P x) ∈
      affineSpan ℝ
        {orderedPoint P (chargePair P x).left,
          orderedPoint P (chargePair P x).right} := by
  rcases x with ⟨e, t⟩
  have hkline := mem_affineSpan_pair_of_mem_openSegment
    (blockerIndex_mem_openSegment P e)
  have hcol : Collinear ℝ
      ({orderedPoint P (blockerIndex P e), orderedPoint P e.1.left,
        orderedPoint P e.1.right} : Set Point) :=
    collinear_insert_of_mem_affineSpan_pair hkline
  cases t
  all_goals
    simp only [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right]
  · exact hcol.mem_affineSpan_of_mem_of_ne
      (p₁ := orderedPoint P e.1.left)
      (p₂ := orderedPoint P (blockerIndex P e))
      (p₃ := orderedPoint P e.1.right)
      (by simp) (by simp) (by simp)
      ((orderedPoint_injective P).ne (left_lt_blockerIndex P e).ne)
  · exact hcol.mem_affineSpan_of_mem_of_ne
      (p₁ := orderedPoint P (blockerIndex P e))
      (p₂ := orderedPoint P e.1.right)
      (p₃ := orderedPoint P e.1.left)
      (by simp) (by simp) (by simp)
      ((orderedPoint_injective P).ne (blockerIndex_lt_right P e).ne)
  · exact hkline

theorem third_ne_charge_left (P : Finset Point) (x : BadPair P × ChargeKind) :
    orderedPoint P (thirdIndex P x) ≠ orderedPoint P (chargePair P x).left := by
  apply (orderedPoint_injective P).ne
  rcases x with ⟨e, t⟩
  have h₁ := e.1.left_lt_right
  have h₂ := left_lt_blockerIndex P e
  have h₃ := blockerIndex_lt_right P e
  cases t
  · simpa [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right] using h₁.ne'
  · simpa [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right] using h₂.ne
  · simpa [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right] using h₂.ne'

theorem third_ne_charge_right (P : Finset Point) (x : BadPair P × ChargeKind) :
    orderedPoint P (thirdIndex P x) ≠ orderedPoint P (chargePair P x).right := by
  apply (orderedPoint_injective P).ne
  rcases x with ⟨e, t⟩
  have h₁ := e.1.left_lt_right
  have h₂ := left_lt_blockerIndex P e
  have h₃ := blockerIndex_lt_right P e
  cases t
  · simpa [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right] using h₃.ne'
  · simpa [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right] using h₁.ne
  · simpa [thirdIndex, chargePair, mkPair, OrderedPair.left, OrderedPair.right] using h₃.ne

/-- No charged pair is reused by another blocked pair. -/
theorem chargePair_injective (P : Finset Point) (hfour : ¬HasFourCollinear P) :
    Function.Injective (chargePair P) := by
  intro x y hxy
  have hthirdPoint :
      orderedPoint P (thirdIndex P x) = orderedPoint P (thirdIndex P y) := by
    apply third_point_unique hfour
      (orderedPoint_mem P (chargePair P x).left)
      (orderedPoint_mem P (chargePair P x).right)
      (orderedPoint_mem P (thirdIndex P x))
      (orderedPoint_mem P (thirdIndex P y))
      ((orderedPoint_injective P).ne (chargePair P x).left_lt_right.ne)
      (third_ne_charge_left P x) (third_ne_charge_right P x)
    · simpa [hxy] using third_ne_charge_left P y
    · simpa [hxy] using third_ne_charge_right P y
    · exact third_mem_affineSpan_charge P x
    · simpa [hxy] using third_mem_affineSpan_charge P y
  apply chargeData_injective P
  exact Prod.ext hxy ((orderedPoint_injective P) hthirdPoint)

end Lax56Proofs.WeightedPairs
