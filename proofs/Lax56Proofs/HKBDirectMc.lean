import Lax56Proofs.HKBDirectConcaveClosure
import Mathlib.Tactic

/-!
A direct, kernel-checked proof of the geometric bound `mc₃(4) ≤ 12`.
This module contains no finite SAT certificate.
-/

namespace Lax56Proofs.HKBDirectMc

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBColourClasses
open Lax56Proofs.HKBDirectConcave
open Lax56Proofs.HKBDirectConcaveCases
open Lax56Proofs.HKBDirectConcaveCases.ConcaveConfiguration
open Lax56Proofs.HKBDirectCore
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBTriangle
open Lax56Proofs.OrderGeometry

/-- A thirteen-point properly four-coloured blocking configuration cannot
exist.  The minimum monochromatic four-set is either the already-classified
convex nine-point pattern or the direct concave ten-point pattern. -/
theorem no_thirteen_of_four_coloured_blocking
    (P : Finset Point) (hcard : P.card = 13)
    (hfour : ¬HasFourCollinear P)
    (colour : P → Fin 4) (hproper : ProperBlocking P colour) : False := by
  obtain ⟨X, hmin⟩ := exists_minimal_monoFour P colour
    (exists_monoFour_of_card_eq_thirteen P colour hcard)
  have hgp : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      turn (X.point i : Point) (X.point j : Point) (X.point k : Point) ≠ 0 := by
    intro i j k hij hik hjk
    apply turn_ne_zero_of_same_colour hfour hproper
    · exact X.injective.ne hij
    · exact X.injective.ne hjk
    · exact X.injective.ne hik.symm
    · exact (X.mono i).trans (X.mono j).symm
    · exact (X.mono j).trans (X.mono k).symm
  rcases four_point_dichotomy (fun p : P ↦ (p : Point))
      Subtype.val_injective X.point X.injective hgp with
      ⟨R, hinside⟩ | ⟨R, hquad⟩
  · have hRmono (i : Fin 4) :
        colour (R.q i) = colour (R.q 0) := by
      have hi : R.q i ∈ Set.range X.point := by
        rw [← R.range_eq]
        exact Set.mem_range_self i
      have hzero : R.q 0 ∈ Set.range X.point := by
        rw [← R.range_eq]
        exact Set.mem_range_self 0
      obtain ⟨j, hj⟩ := hi
      obtain ⟨k, hk⟩ := hzero
      rw [← hj, ← hk, X.mono j, X.mono k]
    have hab : R.q 0 ≠ R.q 1 := R.injective.ne (by decide)
    have hac : R.q 0 ≠ R.q 2 := R.injective.ne (by decide)
    have had : R.q 0 ≠ R.q 3 := R.injective.ne (by decide)
    have hbc : R.q 1 ≠ R.q 2 := R.injective.ne (by decide)
    have hbd : R.q 1 ≠ R.q 3 := R.injective.ne (by decide)
    have hcd : R.q 2 ≠ R.q 3 := R.injective.ne (by decide)
    have hmonoB : colour (R.q 0) = colour (R.q 1) := (hRmono 1).symm
    have hmonoC : colour (R.q 0) = colour (R.q 2) := (hRmono 2).symm
    have hmonoD : colour (R.q 0) = colour (R.q 3) := (hRmono 3).symm
    obtain ⟨skeleton⟩ := exists_concaveSkeleton hfour colour hproper
      hab hac had hbc hbd hcd hmonoB hmonoC hmonoD hinside
    let K : ConcaveConfiguration P colour (R.q 0) (R.q 1) (R.q 2) (R.q 3) :=
      { hab := hab
        hac := hac
        had := had
        hbc := hbc
        hbd := hbd
        hcd := hcd
        hfour := hfour
        proper := hproper
        monoB := hmonoB
        monoC := hmonoC
        monoD := hmonoD
        inside := hinside
        skeleton := skeleton
        redHull := by
          intro z hz hc
          obtain ⟨i, hi⟩ := same_colour_eq_concaveVertex_of_minimal
            hfour hmin R hinside z hz hc
          fin_cases i
          · exact Or.inl hi
          · exact Or.inr (Or.inl hi)
          · exact Or.inr (Or.inr (Or.inl hi))
          · exact Or.inr (Or.inr (Or.inr hi))
        otherColourBound := by
          intro e he
          exact other_colour_card_le_three_in_concave_hull
            hfour hmin R hinside e he }
    have hle := card_le_ten K
    omega
  · exact no_thirteen_of_minimal_convex hcard hfour colour hproper
      X hmin R hquad

/-- A four-coloured point set with no four collinear points, in which every
equal-coloured pair has a blocker in the set, has at most twelve points.
The first thirteen points in lexicographic order form a blocker-closed
interval, so the exact thirteen-point theorem applies. -/
theorem card_le_twelve_of_four_coloured_blocking
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (colouring : P → Fin 4)
    (hblocked : ∀ (p q : P), p ≠ q → colouring p = colouring q →
      ∃ r ∈ P, r ∈ openSegment ℝ (p : Point) (q : Point)) :
    P.card ≤ 12 := by
  by_contra hcard
  have h13 : 13 ≤ P.card := by omega
  let lo : Fin P.card := ⟨0, by omega⟩
  let hi : Fin P.card := ⟨12, by omega⟩
  let Q : Finset Point := pointInterval P lo hi
  have hQcard : Q.card = 13 := by
    dsimp [Q]
    rw [pointInterval, Finset.card_image_of_injective]
    · simp [lo, hi]
    · exact orderedPoint_injective P
  have hQP : Q ⊆ P := by
    simpa [Q] using pointInterval_subset P lo hi
  have hfourQ : ¬HasFourCollinear Q := by
    intro h
    exact hfour (hasFourCollinear_mono hQP h)
  let inclusion : Q → P := fun x ↦ ⟨(x : Point), hQP x.property⟩
  let colourQ : Q → Fin 4 := fun x ↦ colouring (inclusion x)
  have hproperQ : ProperBlocking Q colourQ := by
    intro x y hxy hcolour
    have hxyP : inclusion x ≠ inclusion y := by
      intro h
      apply hxy
      apply Subtype.ext
      exact congrArg (fun z : P ↦ (z : Point)) h
    have hcolourP : colouring (inclusion x) = colouring (inclusion y) := by
      simpa [colourQ] using hcolour
    obtain ⟨r, hrP, hr⟩ := hblocked (inclusion x) (inclusion y) hxyP hcolourP
    have hr' : r ∈ openSegment ℝ (x : Point) (y : Point) := by
      simpa [inclusion] using hr
    have hxmem : (x : Point) ∈ pointInterval P lo hi := by
      simpa [Q] using x.property
    have hymem : (y : Point) ∈ pointInterval P lo hi := by
      simpa [Q] using y.property
    rw [pointInterval] at hxmem hymem
    obtain ⟨i, hiIcc, hix⟩ := Finset.mem_image.mp hxmem
    obtain ⟨j, hjIcc, hjy⟩ := Finset.mem_image.mp hymem
    have hiBounds := Finset.mem_Icc.mp hiIcc
    have hjBounds := Finset.mem_Icc.mp hjIcc
    have hij : i ≠ j := by
      intro hij
      apply hxy
      apply Subtype.ext
      rw [← hix, ← hjy, hij]
    obtain ⟨k, hkr⟩ := orderedPoint_surjective P r hrP
    have hrQ : r ∈ Q := by
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hrOrdered : r ∈ openSegment ℝ
            (orderedPoint P i) (orderedPoint P j) := by
          simpa [hix, hjy] using hr'
        have hbetween := lex_between_of_mem_openSegment
          ((orderedPoint_strictMono P) hij) hrOrdered
        have hik : i < k := by
          apply (orderedPoint_strictMono P).lt_iff_lt.mp
          simpa [hkr] using hbetween.1
        have hkj : k < j := by
          apply (orderedPoint_strictMono P).lt_iff_lt.mp
          simpa [hkr] using hbetween.2
        have hkQ : orderedPoint P k ∈ pointInterval P lo hi :=
          (orderedPoint_mem_pointInterval_iff P lo hi k).2
            ⟨hiBounds.1.trans hik.le, hkj.le.trans hjBounds.2⟩
        simpa [Q, hkr] using hkQ
      · have hrOrdered : r ∈ openSegment ℝ
            (orderedPoint P j) (orderedPoint P i) := by
          rw [openSegment_symm]
          simpa [hix, hjy] using hr'
        have hbetween := lex_between_of_mem_openSegment
          ((orderedPoint_strictMono P) hji) hrOrdered
        have hjk : j < k := by
          apply (orderedPoint_strictMono P).lt_iff_lt.mp
          simpa [hkr] using hbetween.1
        have hki : k < i := by
          apply (orderedPoint_strictMono P).lt_iff_lt.mp
          simpa [hkr] using hbetween.2
        have hkQ : orderedPoint P k ∈ pointInterval P lo hi :=
          (orderedPoint_mem_pointInterval_iff P lo hi k).2
            ⟨hjBounds.1.trans hjk.le, hki.le.trans hiBounds.2⟩
        simpa [Q, hkr] using hkQ
    exact ⟨⟨r, hrQ⟩, by simpa using hr'⟩
  exact no_thirteen_of_four_coloured_blocking Q hQcard hfourQ colourQ hproperQ

end Lax56Proofs.HKBDirectMc
