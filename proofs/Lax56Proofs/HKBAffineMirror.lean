import Lax56Proofs.HKBBlocking
import Lax56Proofs.HKBTriangle
import Lax56Proofs.Orientation
import Mathlib.Tactic

/-!
An orientation-reversing affine involution of the plane, together with the
transport facts needed to reuse an oriented geometric argument after a
reflection.  This is entirely structural: no finite search is involved.
-/

namespace Lax56Proofs.HKBAffineMirror

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- Reflection in the first coordinate axis. -/
def mirrorLinear : Point ≃ₗ[ℝ] Point where
  toFun p := (p.1, -p.2)
  invFun p := (p.1, -p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' p q := by ext <;> simp <;> ring
  map_smul' r p := by ext <;> simp

def mirrorAffine : Point ≃ᵃ[ℝ] Point := mirrorLinear.toAffineEquiv

@[simp] theorem mirrorAffine_apply (p : Point) :
    mirrorAffine p = (p.1, -p.2) := rfl

@[simp] theorem mirrorAffine_involutive (p : Point) :
    mirrorAffine (mirrorAffine p) = p := by ext <;> simp

def mirrorEmbedding : Point ↪ Point := mirrorAffine.toEquiv.toEmbedding

noncomputable def mirrorFinset (P : Finset Point) : Finset Point :=
  P.map mirrorEmbedding

/-- Reflection gives a canonical equivalence between a finite point set and
its reflected copy. -/
noncomputable def mirrorSubtypeEquiv (P : Finset Point) :
    P ≃ mirrorFinset P where
  toFun p := ⟨mirrorAffine p, by
    rw [mirrorFinset, Finset.mem_map]
    exact ⟨p, p.property, rfl⟩⟩
  invFun q := ⟨mirrorAffine q, by
    have hmem : (q : Point) ∈ P.map mirrorEmbedding := by
      simpa only [mirrorFinset] using q.property
    rw [Finset.mem_map] at hmem
    obtain ⟨p, hp, he⟩ := hmem
    have hval : (q : Point) = mirrorAffine p := he.symm
    rw [hval, mirrorAffine_involutive]
    exact hp⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv q := by apply Subtype.ext; simp

@[simp] theorem mirrorSubtypeEquiv_val (P : Finset Point) (p : P) :
    ((mirrorSubtypeEquiv P p : mirrorFinset P) : Point) = mirrorAffine p := rfl

@[simp] theorem mirrorSubtypeEquiv_symm_val (P : Finset Point)
    (p : mirrorFinset P) :
    (((mirrorSubtypeEquiv P).symm p : P) : Point) = mirrorAffine p := rfl

/-- Transport a colouring to the reflected copy. -/
noncomputable def mirrorColour {P : Finset Point} (colour : P → Fin 4) :
    mirrorFinset P → Fin 4 := fun p ↦ colour ((mirrorSubtypeEquiv P).symm p)

@[simp] theorem mirrorColour_apply {P : Finset Point} (colour : P → Fin 4)
    (p : P) : mirrorColour colour (mirrorSubtypeEquiv P p) = colour p := by
  simp [mirrorColour]

theorem mirror_openSegment {p q r : Point}
    (h : r ∈ openSegment ℝ p q) :
    mirrorAffine r ∈ openSegment ℝ (mirrorAffine p) (mirrorAffine q) := by
  change mirrorAffine.toAffineMap r ∈
    openSegment ℝ (mirrorAffine.toAffineMap p) (mirrorAffine.toAffineMap q)
  rw [← image_openSegment ℝ mirrorAffine.toAffineMap]
  exact ⟨r, h, rfl⟩

theorem mirror_openSegment_iff {p q r : Point} :
    mirrorAffine r ∈ openSegment ℝ (mirrorAffine p) (mirrorAffine q) ↔
      r ∈ openSegment ℝ p q := by
  constructor
  · intro h
    simpa only [mirrorAffine_involutive] using mirror_openSegment h
  · exact mirror_openSegment

theorem collinear_mirror (s : Set Point) (h : Collinear ℝ s) :
    Collinear ℝ (mirrorAffine '' s) := by
  rw [show Collinear ℝ (mirrorAffine '' s) ↔ Collinear ℝ s by
    unfold Collinear
    change Module.rank ℝ (vectorSpan ℝ (mirrorAffine.toAffineMap '' s)) ≤ 1 ↔ _
    rw [← mirrorAffine.toAffineMap.map_vectorSpan]
    change Module.rank ℝ
      (Submodule.map mirrorLinear.toLinearMap (vectorSpan ℝ s)) ≤ 1 ↔ _
    rw [mirrorLinear.rank_map_eq]]
  exact h

theorem mirror_noFour {P : Finset Point} (hfour : ¬HasFourCollinear P) :
    ¬HasFourCollinear (mirrorFinset P) := by
  intro h
  apply hfour
  obtain ⟨f, hinj, hmem, hcol⟩ := h
  let g : Fin 4 → Point := fun i ↦ mirrorAffine (f i)
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i j hij
    exact hinj (mirrorAffine.injective hij)
  · intro i
    have hm := hmem i
    change f i ∈ mirrorFinset P at hm
    have hm' : f i ∈ P.map mirrorEmbedding := by
      simpa only [mirrorFinset] using hm
    rw [Finset.mem_map] at hm'
    obtain ⟨p, hp, he⟩ := hm'
    change mirrorAffine (f i) ∈ P
    have hval : f i = mirrorAffine p := he.symm
    rw [hval, mirrorAffine_involutive]
    exact hp
  · have hi := collinear_mirror (Set.range f) hcol
    have hrange : mirrorAffine '' Set.range f = Set.range g := by
      ext z
      simp [g]
    rwa [hrange] at hi

theorem mirror_proper {P : Finset Point} {colour : P → Fin 4}
    (h : ProperBlocking P colour) :
    ProperBlocking (mirrorFinset P) (mirrorColour colour) := by
  intro x y hxy hc
  let x' : P := (mirrorSubtypeEquiv P).symm x
  let y' : P := (mirrorSubtypeEquiv P).symm y
  have hxy' : x' ≠ y' := by
    intro e
    apply hxy
    exact (mirrorSubtypeEquiv P).symm.injective e
  have hc' : colour x' = colour y' := hc
  obtain ⟨z, hz⟩ := h x' y' hxy' hc'
  refine ⟨mirrorSubtypeEquiv P z, ?_⟩
  have hm := mirror_openSegment hz
  simpa [x', y'] using hm

@[simp] theorem turn_mirror (p q r : Point) :
    turn (mirrorAffine p) (mirrorAffine q) (mirrorAffine r) = -turn p q r := by
  simp [turn]
  ring

theorem mirror_triangleHull (a b c : Point) :
    mirrorAffine '' triangleHull a b c =
      triangleHull (mirrorAffine a) (mirrorAffine b) (mirrorAffine c) := by
  unfold triangleHull
  change mirrorAffine.toAffineMap '' convexHull ℝ ({a, b, c} : Set Point) = _
  rw [mirrorAffine.toAffineMap.image_convexHull]
  congr 1
  ext x
  simp [eq_comm]

theorem mirror_mem_triangleHull_iff {a b c x : Point} :
    mirrorAffine x ∈
        triangleHull (mirrorAffine a) (mirrorAffine b) (mirrorAffine c) ↔
      x ∈ triangleHull a b c := by
  rw [← mirror_triangleHull]
  constructor
  · rintro ⟨y, hy, he⟩
    exact mirrorAffine.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mirror_mem_triangleHull_swap_iff {a b c x : Point} :
    mirrorAffine x ∈
        triangleHull (mirrorAffine a) (mirrorAffine c) (mirrorAffine b) ↔
      x ∈ triangleHull a b c := by
  rw [triangleHull_swap_last]
  exact mirror_mem_triangleHull_iff

theorem mirror_strictlyInside_swap {a b c x : Point}
    (h : StrictlyInsideTriangle a b c x) :
    StrictlyInsideTriangle (mirrorAffine a) (mirrorAffine c)
      (mirrorAffine b) (mirrorAffine x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [turn_mirror, ← turn_swap_first a c x]
    exact h.2.2
  · rw [turn_mirror, ← turn_swap_first c b x]
    exact h.2.1
  · rw [turn_mirror, ← turn_swap_first b a x]
    exact h.1

theorem mirror_strictlyInside_swap_iff {a b c x : Point} :
    StrictlyInsideTriangle (mirrorAffine a) (mirrorAffine c)
        (mirrorAffine b) (mirrorAffine x) ↔
      StrictlyInsideTriangle a b c x := by
  constructor
  · intro h
    simpa only [mirrorAffine_involutive] using mirror_strictlyInside_swap h
  · exact mirror_strictlyInside_swap

/-- The cyclic form used by the three cells after the reflected outer
vertices are ordered as `a,c,b`. -/
theorem mirror_strictlyInside_cell_iff {a b c x : Point} :
    StrictlyInsideTriangle (mirrorAffine b) (mirrorAffine a)
        (mirrorAffine c) (mirrorAffine x) ↔
      StrictlyInsideTriangle a b c x := by
  constructor
  · intro h
    apply mirror_strictlyInside_swap_iff.mp
    exact ⟨h.2.1, h.2.2, h.1⟩
  · intro h
    have hm := mirror_strictlyInside_swap h
    exact ⟨hm.2.2, hm.1, hm.2.1⟩

end Lax56Proofs.HKBAffineMirror
