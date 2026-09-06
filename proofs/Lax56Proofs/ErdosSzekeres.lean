import Lax56Proofs.CupsCapsGeometry
import Lax56Proofs.ValtrReduction

namespace Lax56Proofs.ErdosSzekeres

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry Lax56Proofs.ValtrReduction

/-- The invertible shear used to separate first coordinates. -/
def shearEquiv (t : ℝ) : Point ≃ₗ[ℝ] Point where
  toFun p := (p.1 + t * p.2, p.2)
  invFun p := (p.1 - t * p.2, p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp <;> ring
  map_smul' u p := by ext <;> simp <;> ring

/-- Excluding one real parameter for each ordered pair of points suffices. -/
theorem exists_separating_shear (P : Finset Point) :
    ∃ t : ℝ, ∀ p ∈ P, ∀ q ∈ P,
      (shearEquiv t p).1 = (shearEquiv t q).1 → p = q := by
  classical
  let bad := (P.product P).image (fun pq ↦ (pq.2.1 - pq.1.1) / (pq.1.2 - pq.2.2))
  obtain ⟨t, ht⟩ := bad.exists_notMem
  refine ⟨t, ?_⟩
  intro p hp q hq heq
  change p.1 + t * p.2 = q.1 + t * q.2 at heq
  by_cases hy : p.2 = q.2
  · exact Prod.ext (by rw [hy] at heq; linarith) hy
  · have htval : (q.1 - p.1) / (p.2 - q.2) = t := by
      apply (div_eq_iff (sub_ne_zero.mpr hy)).mpr
      nlinarith
    exact (ht (Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, htval⟩)).elim

/-- Collinearity is preserved by a linear map, by mapping its point-and-direction
parameterization. -/
theorem collinear_linear_image (f : Point →ₗ[ℝ] Point) {S : Set Point}
    (hS : Collinear ℝ S) : Collinear ℝ (f '' S) := by
  obtain ⟨p₀, v, hparam⟩ := (collinear_iff_exists_forall_eq_smul_vadd S).mp hS
  apply (collinear_iff_exists_forall_eq_smul_vadd _).mpr
  refine ⟨f p₀, f v, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨r, rfl⟩ := hparam p hp
  exact ⟨r, by simp⟩

theorem generalPosition_image (e : Point ≃ₗ[ℝ] Point) {P : Finset Point}
    (hP : ¬HasThreeCollinear P) : ¬HasThreeCollinear (P.image e) := by
  classical
  rintro ⟨f, hf, hmem, hcol⟩
  apply hP
  refine ⟨e.symm ∘ f, e.symm.injective.comp hf, ?_, ?_⟩
  · intro i
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp (hmem i)
    simpa only [Function.comp_apply, ← hpi, LinearEquiv.symm_apply_apply] using hp
  · have h := collinear_linear_image e.symm.toLinearMap hcol
    simpa only [LinearEquiv.coe_coe, Set.range_comp] using h

theorem convexIndependent_linear_image {ι : Type*} {v : ι → Point}
    (hv : ConvexIndependent ℝ v) (e : Point ≃ₗ[ℝ] Point) :
    ConvexIndependent ℝ (e ∘ v) := by
  intro S i hi
  apply hv S i
  apply e.injective.mem_set_image.mp
  change e (v i) ∈ (e.toLinearMap.toAffineMap : Point → Point) '' convexHull ℝ (v '' S)
  have himage := e.toLinearMap.toAffineMap.image_convexHull (v '' S)
  rw [himage]
  simpa only [Set.image_image, Function.comp_def] using hi

theorem convexPosition_image (e : Point ≃ₗ[ℝ] Point) {P : Finset Point}
    (hP : ConvexPosition P) : ConvexPosition (P.image e) := by
  classical
  have h := (convexIndependent_linear_image hP e).range
  have heq : Set.range (e ∘ (fun p : P ↦ p.val)) = (P.image e : Set Point) := by
    ext x
    simp only [Set.mem_range, Function.comp_apply, Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [heq] at h
  exact h

/-- The complete weak Erdős--Szekeres bound in the real plane. The proof uses
the finite forbidden-parameter shear, the cups/caps recurrence, and strict
supporting functions; it does not use a geometric existence axiom. -/
theorem weak_erdos_szekeres : WeakErdosSzekeres := by
  classical
  intro P k hk hgen hcard
  obtain ⟨t, ht⟩ := exists_separating_shear P
  let e := shearEquiv t
  let Q := P.image e
  have hQcard : Q.card = P.card := Finset.card_image_of_injective _ e.injective
  have hQx : ∀ p ∈ Q, ∀ q ∈ Q, p.1 = q.1 → p = q := by
    intro p hp q hq hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact congrArg e (ht a ha b hb hx)
  obtain ⟨A, hAQ, hAk, hA⟩ := exists_convex_of_strict_x Q k hk
    (generalPosition_image e hgen) hQx (by rwa [hQcard])
  refine ⟨A.image e.symm, ?_, ?_, convexPosition_image e.symm hA⟩
  · intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hAQ ha)
    simpa using hb
  · rw [Finset.card_image_of_injective _ e.symm.injective, hAk]

end Lax56Proofs.ErdosSzekeres
