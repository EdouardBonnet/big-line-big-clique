import Lax56Proofs.HKBGeometry
import Mathlib.Combinatorics.Pigeonhole

namespace Lax56Proofs.HKBColouring

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBGeometry

/-- A same-coloured subset of a properly coloured visibility graph is in
general position when the ambient set has no four collinear points. -/
theorem noThreeCollinear_of_constantColour
    {P S : Finset Point} (hSP : S ⊆ P) (hfour : ¬HasFourCollinear P)
    (C : (visibilityGraph P).Coloring (Fin 5)) (c : Fin 5)
    (hcolour : ∀ p (hp : p ∈ S), C ⟨p, hSP hp⟩ = c) :
    ¬HasThreeCollinear S := by
  rintro ⟨f, hfinj, hfS, hcol⟩
  let p₀ := f 0
  let p₁ := f 1
  let p₂ := f 2
  have hp₀S : p₀ ∈ S := hfS 0
  have hp₁S : p₁ ∈ S := hfS 1
  have hp₂S : p₂ ∈ S := hfS 2
  have hp₀P : p₀ ∈ P := hSP hp₀S
  have hp₁P : p₁ ∈ P := hSP hp₁S
  have hp₂P : p₂ ∈ P := hSP hp₂S
  have h₀₁ : p₀ ≠ p₁ := hfinj.ne (by decide)
  have h₀₂ : p₀ ≠ p₂ := hfinj.ne (by decide)
  have h₁₂ : p₁ ≠ p₂ := hfinj.ne (by decide)
  have hc₀₁ : C ⟨p₀, hp₀P⟩ = C ⟨p₁, hp₁P⟩ := by
    rw [hcolour p₀ hp₀S, hcolour p₁ hp₁S]
  have hc₀₂ : C ⟨p₀, hp₀P⟩ = C ⟨p₂, hp₂P⟩ := by
    rw [hcolour p₀ hp₀S, hcolour p₂ hp₂S]
  have hnvis₀₁ : ¬Visible P p₀ p₁ := by
    intro hv
    exact C.valid
      (show (visibilityGraph P).Adj ⟨p₀, hp₀P⟩ ⟨p₁, hp₁P⟩ from hv) hc₀₁
  have hnvis₀₂ : ¬Visible P p₀ p₂ := by
    intro hv
    exact C.valid
      (show (visibilityGraph P).Adj ⟨p₀, hp₀P⟩ ⟨p₂, hp₂P⟩ from hv) hc₀₂
  obtain ⟨r₀₁, hr₀₁P, hr₀₁⟩ := exists_blocker h₀₁ hnvis₀₁
  obtain ⟨r₀₂, hr₀₂P, hr₀₂⟩ := exists_blocker h₀₂ hnvis₀₂
  have hr₀₁₀ : r₀₁ ≠ p₀ := by
    intro h
    subst r₀₁
    exact h₀₁ ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hr₀₁)
  have hr₀₁₁ : r₀₁ ≠ p₁ := by
    intro h
    subst r₀₁
    exact h₀₁ ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hr₀₁)
  have hr₀₂₀ : r₀₂ ≠ p₀ := by
    intro h
    subst r₀₂
    exact h₀₂ ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hr₀₂)
  have hr₀₂₂ : r₀₂ ≠ p₂ := by
    intro h
    subst r₀₂
    exact h₀₂ ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hr₀₂)
  have hp₂line : p₂ ∈ affineSpan ℝ {p₀, p₁} :=
    hcol.mem_affineSpan_of_mem_of_ne ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ h₀₁
  have hp₁line : p₁ ∈ affineSpan ℝ {p₀, p₂} :=
    hcol.mem_affineSpan_of_mem_of_ne ⟨0, rfl⟩ ⟨2, rfl⟩ ⟨1, rfl⟩ h₀₂
  have hr₀₁eq : r₀₁ = p₂ :=
    third_point_unique hfour hp₀P hp₁P hr₀₁P hp₂P h₀₁
      hr₀₁₀ hr₀₁₁ h₀₂.symm h₁₂.symm
      (mem_affineSpan_pair_of_mem_openSegment hr₀₁) hp₂line
  have hr₀₂eq : r₀₂ = p₁ :=
    third_point_unique hfour hp₀P hp₂P hr₀₂P hp₁P h₀₂
      hr₀₂₀ hr₀₂₂ h₀₁.symm h₁₂
      (mem_affineSpan_pair_of_mem_openSegment hr₀₂) hp₁line
  exact not_two_mutual_openSegments h₀₁
    ⟨hr₀₁eq ▸ hr₀₁, hr₀₂eq ▸ hr₀₂⟩

end Lax56Proofs.HKBColouring
