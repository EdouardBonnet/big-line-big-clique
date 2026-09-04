import Lax56Proofs.HKBSixStructure
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
Colour coverage inside a monochromatic triangle in a properly four-coloured
blocking set.
-/

namespace Lax56Proofs.HKBColourCoverage

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBTriangle

/-- Lemma 2.4: the closed hull of a monochromatic triangle contains a point
of every other colour. -/
theorem exists_colour_in_triangleHull
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 4} (hproper : ProperBlocking B colour)
    {a b c : B} (hmono : MonoTriple colour a b c)
    (d : Fin 4) (hd : d ≠ colour a) :
    ∃ p : B,
      (p : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) ∧
        colour p = d := by
  classical
  by_contra hexists
  have hmissing : ∀ p : B,
      (p : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) →
        colour p ≠ d := by
    intro p hp hpd
    exact hexists ⟨p, hp, hpd⟩
  let T : Finset Point :=
    B.filter fun p ↦ p ∈ triangleHull (a : Point) (b : Point) (c : Point)
  have hTB : T ⊆ B := by
    exact Finset.filter_subset _ _
  have hfourT : ¬HasFourCollinear T := by
    intro h4
    exact hfour (hasFourCollinear_mono hTB h4)
  let incl : T → B := fun p ↦ ⟨p, hTB p.property⟩
  have hinHull (p : T) :
      (incl p : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    exact (Finset.mem_filter.mp p.property).2
  have havoid (p : T) : colour (incl p) ≠ d :=
    hmissing (incl p) (hinHull p)
  let colourT : T → Fin 3 := fun p ↦
    (finSuccAboveEquiv d).symm ⟨colour (incl p), havoid p⟩
  have hproperT : ProperBlocking T colourT := by
    intro x y hxy hcolxy
    have hixy : incl x ≠ incl y := by
      intro h
      apply hxy
      apply Subtype.ext
      exact congrArg (fun p : B ↦ (p : Point)) h
    have horigcol : colour (incl x) = colour (incl y) := by
      have hsub :
          (⟨colour (incl x), havoid x⟩ : {e : Fin 4 // e ≠ d}) =
            ⟨colour (incl y), havoid y⟩ := by
        apply (finSuccAboveEquiv d).symm.injective
        simpa [colourT] using hcolxy
      exact congrArg Subtype.val hsub
    obtain ⟨z, hz⟩ := hproper (incl x) (incl y) hixy horigcol
    have hzHull :
        (z : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
      openSegment_mem_triangleHull_of_mem (hinHull x) (hinHull y) hz
    have hzT : (z : Point) ∈ T := by
      exact Finset.mem_filter.mpr ⟨z.property, hzHull⟩
    let zT : T := ⟨z, hzT⟩
    exact ⟨zT, hz⟩
  have haHull :
      (a : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    vertex_mem_triangleHull _ _ _
  have hbHull :
      (b : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hcHull :
      (c : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have haTmem : (a : Point) ∈ T := Finset.mem_filter.mpr ⟨a.property, haHull⟩
  have hbTmem : (b : Point) ∈ T := Finset.mem_filter.mpr ⟨b.property, hbHull⟩
  have hcTmem : (c : Point) ∈ T := Finset.mem_filter.mpr ⟨c.property, hcHull⟩
  let aT : T := ⟨a, haTmem⟩
  let bT : T := ⟨b, hbTmem⟩
  let cT : T := ⟨c, hcTmem⟩
  have habT : aT ≠ bT := by
    intro h
    apply hmono.1
    apply Subtype.ext
    exact congrArg (fun p : T ↦ (p : Point)) h
  have hbcT : bT ≠ cT := by
    intro h
    apply hmono.2.1
    apply Subtype.ext
    exact congrArg (fun p : T ↦ (p : Point)) h
  have hcaT : cT ≠ aT := by
    intro h
    apply hmono.2.2.1
    apply Subtype.ext
    exact congrArg (fun p : T ↦ (p : Point)) h
  have hcolabT : colourT aT = colourT bT := by
    unfold colourT
    apply congrArg (finSuccAboveEquiv d).symm
    apply Subtype.ext
    change colour a = colour b
    exact hmono.2.2.2.1
  have hcolbcT : colourT bT = colourT cT := by
    unfold colourT
    apply congrArg (finSuccAboveEquiv d).symm
    apply Subtype.ext
    change colour b = colour c
    exact hmono.2.2.2.2
  exact no_monoTriple_three_colours hfourT hproperT
    ⟨habT, hbcT, hcaT, hcolabT, hcolbcT⟩

end Lax56Proofs.HKBColourCoverage
