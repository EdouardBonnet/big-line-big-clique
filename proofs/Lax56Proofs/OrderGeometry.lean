import Lax56
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

namespace Lax56Proofs.OrderGeometry

open Lax56.Geometry

/-- A point strictly inside a planar segment lies strictly between its endpoints
in lexicographic order. -/
theorem lex_between_of_mem_openSegment
    {p q r : Point} (hpq : toLex p < toLex q)
    (hr : r ∈ openSegment ℝ p q) :
    toLex p < toLex r ∧ toLex r < toLex q := by
  rw [openSegment_eq_image] at hr
  obtain ⟨t, ht, rfl⟩ := hr
  rcases (Prod.Lex.toLex_lt_toLex.mp hpq) with hpq₁ | hpq₂
  · constructor <;> rw [Prod.Lex.toLex_lt_toLex]
    · left
      dsimp
      nlinarith [ht.1, ht.2]
    · left
      dsimp
      nlinarith [ht.1, ht.2]
  · rcases hpq₂ with ⟨hpq₁, hpq₂⟩
    constructor <;> rw [Prod.Lex.toLex_lt_toLex]
    · right
      constructor
      · dsimp
        rw [hpq₁]
        ring
      · dsimp
        nlinarith [ht.1, ht.2]
    · right
      constructor
      · dsimp
        rw [hpq₁]
        ring
      · dsimp
        nlinarith [ht.1, ht.2]

/-- The finite point set transported to the lexicographically ordered copy of
the plane. -/
noncomputable def lexPoints (P : Finset Point) : Finset (Lex Point) :=
  P.map toLex.toEmbedding

@[simp] theorem card_lexPoints (P : Finset Point) :
    (lexPoints P).card = P.card := by
  simp [lexPoints]

/-- The points of `P` in lexicographic order. -/
noncomputable def orderedPoint (P : Finset Point) (i : Fin P.card) : Point :=
  ofLex (((lexPoints P).orderIsoOfFin (card_lexPoints P)) i : Lex Point)

theorem orderedPoint_mem (P : Finset Point) (i : Fin P.card) :
    orderedPoint P i ∈ P := by
  classical
  have hmem :
      (((lexPoints P).orderIsoOfFin (card_lexPoints P)) i : Lex Point) ∈
        lexPoints P :=
    (((lexPoints P).orderIsoOfFin (card_lexPoints P)) i).property
  simpa [lexPoints, orderedPoint] using hmem

theorem orderedPoint_injective (P : Finset Point) :
    Function.Injective (orderedPoint P) := by
  intro i j hij
  apply ((lexPoints P).orderIsoOfFin (card_lexPoints P)).injective
  apply Subtype.ext
  simpa [orderedPoint] using congrArg toLex hij

theorem orderedPoint_surjective (P : Finset Point) :
    ∀ p ∈ P, ∃ i : Fin P.card, orderedPoint P i = p := by
  classical
  intro p hp
  have hlex : toLex p ∈ lexPoints P := by
    simp [lexPoints, hp]
  let q : lexPoints P := ⟨toLex p, hlex⟩
  refine ⟨((lexPoints P).orderIsoOfFin (card_lexPoints P)).symm q, ?_⟩
  simp [orderedPoint, q]

theorem orderedPoint_strictMono (P : Finset Point) :
    StrictMono (fun i : Fin P.card ↦ toLex (orderedPoint P i)) := by
  intro i j hij
  change
    (((lexPoints P).orderIsoOfFin (card_lexPoints P)) i : Lex Point) <
      (((lexPoints P).orderIsoOfFin (card_lexPoints P)) j : Lex Point)
  exact ((lexPoints P).orderIsoOfFin (card_lexPoints P)).strictMono hij

/-- A closed interval in the canonical ordering of `P`, viewed as a point set. -/
noncomputable def pointInterval (P : Finset Point) (a b : Fin P.card) : Finset Point :=
  (Finset.Icc a b).image (orderedPoint P)

@[simp] theorem orderedPoint_mem_pointInterval_iff
    (P : Finset Point) (a b i : Fin P.card) :
    orderedPoint P i ∈ pointInterval P a b ↔ a ≤ i ∧ i ≤ b := by
  classical
  constructor
  · intro h
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp h
    have : k = i := orderedPoint_injective P hki
    simpa [this] using (Finset.mem_Icc.mp hk)
  · intro h
    exact Finset.mem_image.mpr ⟨i, Finset.mem_Icc.mpr h, rfl⟩

theorem pointInterval_subset (P : Finset Point) (a b : Fin P.card) :
    pointInterval P a b ⊆ P := by
  intro p hp
  classical
  simp only [pointInterval, Finset.mem_image] at hp
  obtain ⟨i, -, rfl⟩ := hp
  exact orderedPoint_mem P i

/-- Restricting to a consecutive interval does not alter visibility between
its points. This is Observation 2.1 of the paper. -/
theorem visible_pointInterval_iff
    (P : Finset Point) (a b i j : Fin P.card)
    (hi : a ≤ i) (hij : i < j) (hj : j ≤ b) :
    Visible (pointInterval P a b) (orderedPoint P i) (orderedPoint P j) ↔
      Visible P (orderedPoint P i) (orderedPoint P j) := by
  constructor
  · intro hsmall
    refine ⟨(orderedPoint_injective P).ne hij.ne, ?_⟩
    intro r hrP hrseg
    obtain ⟨k, rfl⟩ := orderedPoint_surjective P r hrP
    have hbetween := lex_between_of_mem_openSegment
      ((orderedPoint_strictMono P) hij) hrseg
    have hik : i < k := (orderedPoint_strictMono P).lt_iff_lt.mp hbetween.1
    have hkj : k < j := (orderedPoint_strictMono P).lt_iff_lt.mp hbetween.2
    exact hsmall.2 (orderedPoint P k)
      (orderedPoint_mem_pointInterval_iff P a b k |>.2
        ⟨hi.trans hik.le, hkj.le.trans hj⟩) hrseg
  · intro hlarge
    refine ⟨hlarge.1, ?_⟩
    intro r hrI
    exact hlarge.2 r (pointInterval_subset P a b hrI)

end Lax56Proofs.OrderGeometry
