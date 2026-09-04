import Lax56Proofs.OrderGeometry
import Mathlib.Tactic

namespace Lax56Proofs.Blockers

open Lax56.Geometry
open Lax56Proofs.OrderGeometry

theorem exists_blocker
    {P : Finset Point} {p q : Point} (hpq : p ≠ q)
    (hnot : ¬Visible P p q) :
    ∃ r ∈ P, r ∈ openSegment ℝ p q := by
  by_contra h
  apply hnot
  refine ⟨hpq, ?_⟩
  intro r hrP hrseg
  exact h ⟨r, hrP, hrseg⟩

theorem mem_affineSpan_pair_of_mem_openSegment
    {p q r : Point} (hr : r ∈ openSegment ℝ p q) :
    r ∈ affineSpan ℝ {p, q} := by
  rw [openSegment_eq_image_lineMap] at hr
  obtain ⟨t, -, rfl⟩ := hr
  exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- With no four collinear points, a line through two points of `P` contains
at most one further point of `P`. -/
theorem third_point_unique
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {p q r s : Point} (hpP : p ∈ P) (hqP : q ∈ P)
    (hrP : r ∈ P) (hsP : s ∈ P)
    (hpq : p ≠ q) (hrp : r ≠ p) (hrq : r ≠ q)
    (hsp : s ≠ p) (hsq : s ≠ q)
    (hrline : r ∈ affineSpan ℝ {p, q})
    (hsline : s ∈ affineSpan ℝ {p, q}) : r = s := by
  by_contra hrs
  apply hfour
  let f : Fin 4 → Point := ![p, q, r, s]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  · intro i
    fin_cases i
    · simpa [f] using hpP
    · simpa [f] using hqP
    · simpa [f] using hrP
    · simpa [f] using hsP
  · have hcol : Collinear ℝ ({r, s, p, q} : Set Point) :=
      collinear_insert_insert_of_mem_affineSpan_pair hrline hsline
    have hrange : Set.range f = ({p, q, r, s} : Set Point) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [f]
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨0, by simp [f]⟩
        · exact ⟨1, by simp [f]⟩
        · exact ⟨2, by simp [f]⟩
        · exact ⟨3, by simp [f]⟩
    rw [hrange]
    convert hcol using 1 <;> ext x <;> simp [or_comm, or_left_comm]

/-- If there are no four collinear points, a blocked ordered pair has only one
blocker. -/
theorem blocker_unique
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {p q r s : Point} (hpq : toLex p < toLex q)
    (hpP : p ∈ P) (hqP : q ∈ P)
    (hrP : r ∈ P) (hr : r ∈ openSegment ℝ p q)
    (hsP : s ∈ P) (hs : s ∈ openSegment ℝ p q) :
    r = s := by
  by_contra hrs
  have hrbetween := lex_between_of_mem_openSegment hpq hr
  have hsbetween := lex_between_of_mem_openSegment hpq hs
  apply hfour
  let f : Fin 4 → Point := ![p, q, r, s]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, ne_eq]
  · intro i
    fin_cases i
    · simpa [f] using hpP
    · simpa [f] using hqP
    · simpa [f] using hrP
    · simpa [f] using hsP
  · have hcol : Collinear ℝ ({r, s, p, q} : Set Point) :=
      collinear_insert_insert_of_mem_affineSpan_pair
        (mem_affineSpan_pair_of_mem_openSegment hr)
        (mem_affineSpan_pair_of_mem_openSegment hs)
    have hrange : Set.range f = ({p, q, r, s} : Set Point) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [f]
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl
        · exact ⟨0, by simp [f]⟩
        · exact ⟨1, by simp [f]⟩
        · exact ⟨2, by simp [f]⟩
        · exact ⟨3, by simp [f]⟩
    rw [hrange]
    convert hcol using 1 <;> ext x <;> simp [or_comm, or_left_comm, or_assoc]

end Lax56Proofs.Blockers
