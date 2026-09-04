import Lax56Proofs.HKBDirectConcaveCases
import Mathlib.Tactic

/-!
The final closure of the direct concave Hujter--Kisfaludi--Bak argument.
Keeping these short transports in a separate module makes the large case
theorems opaque before they are reflected or cyclically relabeled.
-/

namespace Lax56Proofs.HKBDirectConcaveCases

open Lax56.Geometry
open Lax56Proofs.HKBDirectConcave

namespace ConcaveConfiguration

variable {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (K : ConcaveConfiguration P colour a b c d)

/-- The reflected form of the corrected `(0,1,2)` elimination. -/
theorem impossible_I₁_zero_I₂_two_I₃_one
    (h₁ : K.I₁.card = 0) (h₂ : K.I₂.card = 2)
    (h₃ : K.I₃.card = 1) : False := by
  apply K.mirror.impossible_I₁_zero_I₂_one_I₃_two
  · simpa using h₁
  · simpa using h₃
  · simpa using h₂

/-- Every nonempty distribution of cell-interior points is eliminated by
the direct case analysis, up to cyclic relabeling and reflection. -/
theorem all_cells_empty : K.I₁ = ∅ ∧ K.I₂ = ∅ ∧ K.I₃ = ∅ := by
  have hsum := K.I_sum_le_three
  by_cases h₁ : K.I₁.card = 0
  · by_cases h₂ : K.I₂.card = 0
    · by_cases h₃ : K.I₃.card = 0
      · exact ⟨Finset.card_eq_zero.mp h₁, Finset.card_eq_zero.mp h₂,
          Finset.card_eq_zero.mp h₃⟩
      · have hc : K.I₃.card = 1 ∨ K.I₃.card = 2 ∨
            K.I₃.card = 3 := by omega
        rcases hc with hc | hc | hc
        · exact (K.impossible_only_I₃_one h₁ h₂ hc).elim
        · exact (K.impossible_only_I₃_two h₁ h₂ hc).elim
        · exact (K.impossible_only_I₃_three h₁ h₂ hc).elim
    · by_cases h₃ : K.I₃.card = 0
      · have hc : K.I₂.card = 1 ∨ K.I₂.card = 2 ∨
            K.I₂.card = 3 := by omega
        rcases hc with hc | hc | hc
        · apply (K.rotate.rotate.impossible_only_I₃_one
              (by simpa using h₃) (by simpa using h₁) (by simpa using hc)).elim
        · apply (K.rotate.rotate.impossible_only_I₃_two
              (by simpa using h₃) (by simpa using h₁) (by simpa using hc)).elim
        · apply (K.rotate.rotate.impossible_only_I₃_three
              (by simpa using h₃) (by simpa using h₁) (by simpa using hc)).elim
      · have hc :
            (K.I₂.card = 1 ∧ K.I₃.card = 1) ∨
            (K.I₂.card = 1 ∧ K.I₃.card = 2) ∨
            (K.I₂.card = 2 ∧ K.I₃.card = 1) := by omega
        rcases hc with hc | hc | hc
        · exact (K.impossible_I₁_zero_I₂_one_I₃_one h₁ hc.1 hc.2).elim
        · exact (K.impossible_I₁_zero_I₂_one_I₃_two h₁ hc.1 hc.2).elim
        · exact (K.impossible_I₁_zero_I₂_two_I₃_one h₁ hc.1 hc.2).elim
  · by_cases h₂ : K.I₂.card = 0
    · by_cases h₃ : K.I₃.card = 0
      · have hc : K.I₁.card = 1 ∨ K.I₁.card = 2 ∨
            K.I₁.card = 3 := by omega
        rcases hc with hc | hc | hc
        · apply (K.rotate.impossible_only_I₃_one
              (by simpa using h₂) (by simpa using h₃) (by simpa using hc)).elim
        · apply (K.rotate.impossible_only_I₃_two
              (by simpa using h₂) (by simpa using h₃) (by simpa using hc)).elim
        · apply (K.rotate.impossible_only_I₃_three
              (by simpa using h₂) (by simpa using h₃) (by simpa using hc)).elim
      · have hc :
            (K.I₁.card = 1 ∧ K.I₃.card = 1) ∨
            (K.I₁.card = 1 ∧ K.I₃.card = 2) ∨
            (K.I₁.card = 2 ∧ K.I₃.card = 1) := by omega
        rcases hc with hc | hc | hc
        · apply (K.rotate.impossible_I₁_zero_I₂_one_I₃_one
              (by simpa using h₂) (by simpa using hc.2) (by simpa using hc.1)).elim
        · apply (K.rotate.impossible_I₁_zero_I₂_two_I₃_one
              (by simpa using h₂) (by simpa using hc.2) (by simpa using hc.1)).elim
        · apply (K.rotate.impossible_I₁_zero_I₂_one_I₃_two
              (by simpa using h₂) (by simpa using hc.2) (by simpa using hc.1)).elim
    · by_cases h₃ : K.I₃.card = 0
      · have hc :
            (K.I₁.card = 1 ∧ K.I₂.card = 1) ∨
            (K.I₁.card = 1 ∧ K.I₂.card = 2) ∨
            (K.I₁.card = 2 ∧ K.I₂.card = 1) := by omega
        rcases hc with hc | hc | hc
        · apply (K.rotate.rotate.impossible_I₁_zero_I₂_one_I₃_one
              (by simpa using h₃) (by simpa using hc.1) (by simpa using hc.2)).elim
        · apply (K.rotate.rotate.impossible_I₁_zero_I₂_one_I₃_two
              (by simpa using h₃) (by simpa using hc.1) (by simpa using hc.2)).elim
        · apply (K.rotate.rotate.impossible_I₁_zero_I₂_two_I₃_one
              (by simpa using h₃) (by simpa using hc.1) (by simpa using hc.2)).elim
      · have hc : K.I₁.card = 1 ∧ K.I₂.card = 1 ∧
            K.I₃.card = 1 := by omega
        exact (K.impossible_I₁_one_I₂_one_I₃_one hc.1 hc.2.1 hc.2.2).elim

/-- A minimum concave monochromatic four-set forces the entire ambient
configuration to be the ten named points of the standard concave pattern. -/
theorem card_le_ten (K : ConcaveConfiguration P colour a b c d) : P.card ≤ 10 := by
  rcases all_cells_empty K with ⟨h₁, h₂, h₃⟩
  let named : Fin 10 → Point :=
    ![(a : Point), (b : Point), (c : Point), (d : Point),
      (K.skeleton.u₁ : Point), (K.skeleton.u₂ : Point),
      (K.skeleton.u₃ : Point), (K.skeleton.v₁ : Point),
      (K.skeleton.v₂ : Point), (K.skeleton.v₃ : Point)]
  let Q : Finset Point := Finset.univ.image named
  have hmem (i : Fin 10) : named i ∈ Q := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hsub : P ⊆ Q := by
    intro x hx
    let x' : P := ⟨x, hx⟩
    have hxHull := K.empty_cells_all_points_mem_hull h₁ h₂ h₃ x'
    rcases K.empty_hull_point_cases h₁ h₂ h₃ hxHull with
        h | h | h | h | h | h | h | h | h | h
    · have hx' : x = (a : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (0 : Fin 10)
    · have hx' : x = (b : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (1 : Fin 10)
    · have hx' : x = (c : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (2 : Fin 10)
    · have hx' : x = (d : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (3 : Fin 10)
    · have hx' : x = (K.skeleton.u₁ : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (4 : Fin 10)
    · have hx' : x = (K.skeleton.u₂ : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (5 : Fin 10)
    · have hx' : x = (K.skeleton.u₃ : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (6 : Fin 10)
    · have hx' : x = (K.skeleton.v₁ : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (7 : Fin 10)
    · have hx' : x = (K.skeleton.v₂ : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (8 : Fin 10)
    · have hx' : x = (K.skeleton.v₃ : Point) := by
        simpa [x'] using congrArg Subtype.val h
      rw [hx']
      simpa [named] using hmem (9 : Fin 10)
  calc
    P.card ≤ Q.card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 10)).card := by
      exact Finset.card_image_le
    _ = 10 := by simp

end ConcaveConfiguration

end Lax56Proofs.HKBDirectConcaveCases
