import Lax56Proofs.HKBFinalCases
import Lax56Proofs.HKBHexCardBound
import Lax56.HujterKisfaludiBak
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-!
The direct Hujter--Kisfaludi--Bak visibility-colouring theorem.

The empty-hexagon input is used through its concept-layer theorem interface,
so Lax records the dependency on `Lax56Proofs.EmptyHexagon`. That proof uses
Valtr's four-layer lemma, proved in `Lax56Proofs.ValtrFourLayer`. The blocker cases
of cardinalities 10, 11 and 12 are proved in the `Lax56Proofs.HKB*` modules.
-/

namespace Lax56Proofs.HujterKisfaludiBak

set_option exponentiation.threshold 512

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBColouring
open Lax56Proofs.HKBDiagonals
open Lax56Proofs.HKBFinalCases
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexFinalGeometry
open Lax56Proofs.HKBHexGeometry

/-- Every set of at least `5 * 2^428 + 1` points either has four collinear points or
its visibility graph is not five-colourable. -/
theorem visibilityGraph_not_fiveColorable
    (P : Finset Point) (hP : 5 * 2 ^ 428 + 1 ≤ P.card) :
    HasFourCollinear P ∨ ¬(visibilityGraph P).Colorable 5 := by
  classical
  by_cases hfour' : HasFourCollinear P
  · exact Or.inl hfour'
  right
  intro hcolourable
  obtain ⟨C⟩ := hcolourable
  have hPtype : Fintype.card P = P.card := Fintype.card_coe P
  have hpigeon : Fintype.card (Fin 5) * 2 ^ 428 < Fintype.card P := by
    simp only [Fintype.card_fin, hPtype]
    omega
  obtain ⟨c, hc⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card (f := C) hpigeon
  let fibre : Finset P := Finset.univ.filter (fun x ↦ C x = c)
  have hcfibre : 2 ^ 428 < fibre.card := by
    simpa [fibre] using hc
  let qEmbed : P ↪ Point :=
    ⟨fun x ↦ (x : Point), by
      intro x y hxy
      apply Subtype.ext
      exact hxy⟩
  let Q : Finset Point := fibre.map qEmbed
  have hQcard : 2 ^ 428 + 1 ≤ Q.card := by
    have hcardMap : Q.card = fibre.card := by
      simp [Q]
    omega
  have hQP : Q ⊆ P := by
    intro p hp
    change p ∈ fibre.map qEmbed at hp
    rw [Finset.mem_map] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact x.property
  have hQcolour : ∀ p (hp : p ∈ Q), C ⟨p, hQP hp⟩ = c := by
    intro p hp
    change p ∈ fibre.map qEmbed at hp
    rw [Finset.mem_map] at hp
    obtain ⟨x, hxc, hx⟩ := hp
    have heq : (⟨p, hQP hp⟩ : P) = x := by
      apply Subtype.ext
      exact hx.symm
    rw [heq]
    simpa [fibre] using hxc
  have hQgeneral : ¬HasThreeCollinear Q :=
    noThreeCollinear_of_constantColour hQP hfour' C c hQcolour
  obtain ⟨hex, hempty⟩ := Lax56.HujterKisfaludiBak.exists_emptyConvexHexagon Q hQcard hQgeneral
  have hh : StrictConvexHexagon hex := hempty.1
  have hhQ : ∀ i, hex i ∈ Q := hempty.2.1
  have hhP : ∀ i, hex i ∈ P := fun i ↦ hQP (hhQ i)
  have hsame : ∀ i, C ⟨hex i, hhP i⟩ = c := by
    intro i
    simpa using hQcolour (hex i) (hhQ i)
  have hside : ∀ i : Fin 6, ∃ r ∈ hexBlockers P hex,
      r ∈ openSegment ℝ (hex i) (hex (i + 1)) := by
    intro i
    apply exists_hexBlocker hfour' hh hhP C c hsame
    fin_cases i <;> decide
  have hdiag : ∀ d : Fin 9, ∃ r ∈ hexBlockers P hex,
      r ∈ openSegment ℝ
        (hex (diagonalEnds d).1) (hex (diagonalEnds d).2) := by
    intro d
    exact exists_hexBlocker hfour' hh hhP C c hsame (diagonalEnds_ne d)
  have hnotc : ∀ p (hp : p ∈ hexBlockers P hex),
      C ⟨p, hexBlockers_subset P hex hp⟩ ≠ c := by
    intro p hp hcp
    have hpdata := mem_hexBlockers.mp hp
    let pP : P := ⟨p, hpdata.1⟩
    have hpPc : C pP = c := by
      simpa [pP] using hcp
    have hpQ : p ∈ Q := by
      change p ∈ fibre.map qEmbed
      rw [Finset.mem_map]
      exact ⟨pP, by simpa [fibre, pP] using hpPc, rfl⟩
    exact hpdata.2.2 (hempty.2.2 p hpQ hpdata.2.1)
  let B := hexBlockers P hex
  let col : B → Fin 4 :=
    blockerColour C c (fun p ↦ hnotc p p.property)
  have hproper : ProperBlocking B col := by
    intro x y hxy hcol
    have hsameXY :
        C ⟨x, hexBlockers_subset P hex x.property⟩ =
          C ⟨y, hexBlockers_subset P hex y.property⟩ := by
      have hsub :
          (⟨C ⟨x, hexBlockers_subset P hex x.property⟩,
            hnotc x x.property⟩ : {d : Fin 5 // d ≠ c}) =
          ⟨C ⟨y, hexBlockers_subset P hex y.property⟩,
            hnotc y y.property⟩ := by
        apply (otherColourEquiv c).injective
        simpa [col, blockerColour] using hcol
      exact congrArg Subtype.val hsub
    have hnvis : ¬Visible P x y := by
      intro hv
      exact C.valid
        (show (visibilityGraph P).Adj
          ⟨x, hexBlockers_subset P hex x.property⟩
          ⟨y, hexBlockers_subset P hex y.property⟩ from hv) hsameXY
    obtain ⟨r, hrP, hr⟩ :=
      exists_blocker (Subtype.val_injective.ne hxy) hnvis
    have hx := mem_hexBlockers.mp x.property
    have hy := mem_hexBlockers.mp y.property
    have hrHull : r ∈ convexHull ℝ (Set.range hex) :=
      (convex_convexHull ℝ (Set.range hex)).openSegment_subset
        hx.2.1 hy.2.1 hr
    have hrNot : r ∉ Set.range hex := by
      rintro ⟨i, rfl⟩
      exact hexVertex_not_between_hull_points hfour' hh hhP
        (hexBlockers_subset P hex x.property)
        (hexBlockers_subset P hex y.property)
        hx.2.1 hy.2.1 hx.2.2 hy.2.2
        (Subtype.val_injective.ne hxy) i hr
    exact ⟨⟨r, mem_hexBlockers.mpr ⟨hrP, hrHull, hrNot⟩⟩, hr⟩
  have hupper : B.card ≤ 12 := by
    exact hexBlockers_card_le_twelve hfour' hh hhP C c hnotc
  have hlowerInside : 4 ≤ (B.filter (StrictlyInsideHexagon hex)).card :=
    four_le_card_strictInside_of_diagonals_blocked hfour' hh hhP
      (hexBlockers_subset P hex) hdiag
  have hinsideCard : (B.filter (StrictlyInsideHexagon hex)).card = B.card - 6 := by
    simpa [B] using strictInteriorBlockers_card hfour' hh hhP hside
  have hlower : 10 ≤ B.card := by omega
  have hcases : B.card = 10 ∨ B.card = 11 ∨ B.card = 12 := by omega
  rcases hcases with hten | heleven | htwelve
  · exact no_ten_hexBlockers hfour' hh hhP hside hdiag
      (by simpa [B] using hten) col hproper
  · exact no_eleven_hexBlockers hfour' hh hhP hside hdiag
      (by simpa [B] using heleven) col hproper
  · exact no_twelve_hexBlockers hfour' hh hhP hside
      (by simpa [B] using htwelve) col hproper

end Lax56Proofs.HujterKisfaludiBak
