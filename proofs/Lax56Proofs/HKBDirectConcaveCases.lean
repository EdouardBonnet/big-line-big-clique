import Lax56Proofs.HKBDirectTrianglePatterns
import Lax56Proofs.HKBAffineMirror
import Mathlib.Tactic

/-!
The cell case analysis for the concave monochromatic four-point
configuration.  This file follows the corrected, blocker-localized version
of the Hujter--Kisfaludi--Bak argument.
-/

namespace Lax56Proofs.HKBDirectConcaveCases

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBDirectCells
open Lax56Proofs.HKBDirectConcave
open Lax56Proofs.HKBDirectCore
open Lax56Proofs.HKBDirectTrianglePatterns
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBAffineMirror
open Lax56Proofs.HKBQuadrilateralMaximal
open Lax56Proofs.HKBSixStructure
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- The hypotheses available inside the hull of a minimum concave
monochromatic four-set. -/
structure ConcaveConfiguration
    (P : Finset Point) (colour : P → Fin 4) (a b c d : P) where
  hab : a ≠ b
  hac : a ≠ c
  had : a ≠ d
  hbc : b ≠ c
  hbd : b ≠ d
  hcd : c ≠ d
  hfour : ¬HasFourCollinear P
  proper : ProperBlocking P colour
  monoB : colour a = colour b
  monoC : colour a = colour c
  monoD : colour a = colour d
  inside : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
    (d : Point)
  skeleton : ConcaveSkeleton P colour a b c d
  redHull : ∀ z : P,
    (z : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) →
    colour z = colour a → z = a ∨ z = b ∨ z = c ∨ z = d
  otherColourBound : ∀ e : Fin 4, e ≠ colour a →
    (pointsOfColourInTriangle P colour (a : Point) (b : Point)
      (c : Point) e).card ≤ 3

namespace ConcaveConfiguration

variable {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (K : ConcaveConfiguration P colour a b c d)

abbrev T₁ : CellSkeleton P colour (colour a) b c d :=
  Lax56Proofs.HKBDirectTrianglePatterns.ConcaveSkeleton.cellOne
    K.skeleton K.hbc K.hcd K.hbd K.monoB K.monoC K.monoD K.inside

abbrev T₂ : CellSkeleton P colour (colour a) c a d :=
  Lax56Proofs.HKBDirectTrianglePatterns.ConcaveSkeleton.cellTwo
    K.skeleton K.hac K.had K.hcd K.monoC K.monoD K.inside

abbrev T₃ : CellSkeleton P colour (colour a) a b d :=
  Lax56Proofs.HKBDirectTrianglePatterns.ConcaveSkeleton.cellThree
    K.skeleton K.hab K.hbd K.had K.monoB K.monoD K.inside

noncomputable def I₁ (K : ConcaveConfiguration P colour a b c d) : Finset P :=
  cellPoints P (b : Point) (c : Point) (d : Point)
noncomputable def I₂ (K : ConcaveConfiguration P colour a b c d) : Finset P :=
  cellPoints P (c : Point) (a : Point) (d : Point)
noncomputable def I₃ (K : ConcaveConfiguration P colour a b c d) : Finset P :=
  cellPoints P (a : Point) (b : Point) (d : Point)

private abbrev rotateBlockerIndex : Fin 6 → Fin 6 := ![1, 2, 0, 4, 5, 3]

private theorem rotateBlockerIndex_injective :
    Function.Injective rotateBlockerIndex := by decide

private abbrev mirrorBlockerIndex : Fin 6 → Fin 6 := ![0, 2, 1, 3, 5, 4]

private theorem mirrorBlockerIndex_injective :
    Function.Injective mirrorBlockerIndex := by decide

/-- Reflect the configuration and reverse the last two outer vertices, so
the reflected outer triangle retains positive orientation. -/
noncomputable def mirrorSkeleton (K : ConcaveConfiguration P colour a b c d) :
    ConcaveSkeleton (mirrorFinset P) (mirrorColour colour)
      (mirrorSubtypeEquiv P a) (mirrorSubtypeEquiv P c)
      (mirrorSubtypeEquiv P b) (mirrorSubtypeEquiv P d) where
  u₁ := mirrorSubtypeEquiv P K.skeleton.u₁
  u₂ := mirrorSubtypeEquiv P K.skeleton.u₃
  u₃ := mirrorSubtypeEquiv P K.skeleton.u₂
  v₁ := mirrorSubtypeEquiv P K.skeleton.v₁
  v₂ := mirrorSubtypeEquiv P K.skeleton.v₃
  v₃ := mirrorSubtypeEquiv P K.skeleton.v₂
  hu₁ := by simpa using mirror_openSegment K.skeleton.hu₁
  hu₂ := by simpa using mirror_openSegment K.skeleton.hu₃
  hu₃ := by simpa using mirror_openSegment K.skeleton.hu₂
  hv₁ := by simpa only [mirrorSubtypeEquiv_val, openSegment_symm] using
    mirror_openSegment K.skeleton.hv₁
  hv₂ := by simpa using mirror_openSegment K.skeleton.hv₃
  hv₃ := by simpa using mirror_openSegment K.skeleton.hv₂
  blockers_injective := by
    intro i j hij
    have hlookup (k : Fin 6) :
        (![
          mirrorSubtypeEquiv P K.skeleton.u₁,
          mirrorSubtypeEquiv P K.skeleton.u₃,
          mirrorSubtypeEquiv P K.skeleton.u₂,
          mirrorSubtypeEquiv P K.skeleton.v₁,
          mirrorSubtypeEquiv P K.skeleton.v₃,
          mirrorSubtypeEquiv P K.skeleton.v₂] : Fin 6 → mirrorFinset P) k =
          mirrorSubtypeEquiv P
            ((![K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
              K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P)
              (mirrorBlockerIndex k)) := by
      fin_cases k <;> rfl
    apply mirrorBlockerIndex_injective
    apply K.skeleton.blockers_injective
    apply (mirrorSubtypeEquiv P).injective
    rw [← hlookup i, ← hlookup j]
    exact hij
  blocker_colour_ne := by
    intro i
    fin_cases i
    · simpa using K.skeleton.blocker_colour_ne 0
    · simpa using K.skeleton.blocker_colour_ne 2
    · simpa using K.skeleton.blocker_colour_ne 1
    · simpa using K.skeleton.blocker_colour_ne 3
    · simpa using K.skeleton.blocker_colour_ne 5
    · simpa using K.skeleton.blocker_colour_ne 4

/-- Cyclically rotate the three outer vertices and all six skeleton points. -/
def rotateSkeleton (K : ConcaveConfiguration P colour a b c d) :
    ConcaveSkeleton P colour b c a d where
  u₁ := K.skeleton.u₂
  u₂ := K.skeleton.u₃
  u₃ := K.skeleton.u₁
  v₁ := K.skeleton.v₂
  v₂ := K.skeleton.v₃
  v₃ := K.skeleton.v₁
  hu₁ := K.skeleton.hu₂
  hu₂ := K.skeleton.hu₃
  hu₃ := K.skeleton.hu₁
  hv₁ := by simpa only [openSegment_symm] using K.skeleton.hv₂
  hv₂ := by simpa only [openSegment_symm] using K.skeleton.hv₃
  hv₃ := K.skeleton.hv₁
  blockers_injective := by
    intro i j hij
    have hlookup (k : Fin 6) :
        (![
          K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
          K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P)
            (rotateBlockerIndex k) =
          (![
            K.skeleton.u₂, K.skeleton.u₃, K.skeleton.u₁,
            K.skeleton.v₂, K.skeleton.v₃, K.skeleton.v₁] : Fin 6 → P) k := by
      fin_cases k <;> rfl
    apply rotateBlockerIndex_injective
    apply K.skeleton.blockers_injective
    rw [hlookup i, hlookup j]
    exact hij
  blocker_colour_ne := by
    intro i
    fin_cases i
    · intro h; exact K.skeleton.blocker_colour_ne 1 (h.trans K.monoB.symm)
    · intro h; exact K.skeleton.blocker_colour_ne 2 (h.trans K.monoB.symm)
    · intro h; exact K.skeleton.blocker_colour_ne 0 (h.trans K.monoB.symm)
    · intro h; exact K.skeleton.blocker_colour_ne 4 (h.trans K.monoB.symm)
    · intro h; exact K.skeleton.blocker_colour_ne 5 (h.trans K.monoB.symm)
    · intro h; exact K.skeleton.blocker_colour_ne 3 (h.trans K.monoB.symm)

/-- Cyclic relabeling preserves every hypothesis of a concave configuration. -/
def rotate (K : ConcaveConfiguration P colour a b c d) :
    ConcaveConfiguration P colour b c a d where
  hab := K.hbc
  hac := K.hab.symm
  had := K.hbd
  hbc := K.hac.symm
  hbd := K.hcd
  hcd := K.had
  hfour := K.hfour
  proper := K.proper
  monoB := K.monoB.symm.trans K.monoC
  monoC := K.monoB.symm
  monoD := K.monoB.symm.trans K.monoD
  inside := ⟨K.inside.2.1, K.inside.2.2, K.inside.1⟩
  skeleton := K.rotateSkeleton
  redHull := by
    intro z hz hc
    have hz' : (z : Point) ∈
        triangleHull (a : Point) (b : Point) (c : Point) := by
      simpa only [triangleHull_rotate] using hz
    have hc' : colour z = colour a := hc.trans K.monoB.symm
    rcases K.redHull z hz' hc' with hza | hzb | hzc | hzd
    · exact Or.inr (Or.inr (Or.inl hza))
    · exact Or.inl hzb
    · exact Or.inr (Or.inl hzc)
    · exact Or.inr (Or.inr (Or.inr hzd))
  otherColourBound := by
    intro e he
    have hea : e ≠ colour a := by
      intro h
      exact he (h.trans K.monoB)
    have hbound := K.otherColourBound e hea
    have hEq :
        pointsOfColourInTriangle P colour (b : Point) (c : Point)
            (a : Point) e =
          pointsOfColourInTriangle P colour (a : Point) (b : Point)
            (c : Point) e := by
      ext z
      simp only [mem_pointsOfColourInTriangle]
      rw [triangleHull_rotate (a : Point) (b : Point) (c : Point)]
    rw [hEq]
    exact hbound

/-- Reflection followed by swapping the last two outer vertices preserves a
concave configuration and exchanges cells two and three. -/
noncomputable def mirror (K : ConcaveConfiguration P colour a b c d) :
    ConcaveConfiguration (mirrorFinset P) (mirrorColour colour)
      (mirrorSubtypeEquiv P a) (mirrorSubtypeEquiv P c)
      (mirrorSubtypeEquiv P b) (mirrorSubtypeEquiv P d) where
  hab := (mirrorSubtypeEquiv P).injective.ne K.hac
  hac := (mirrorSubtypeEquiv P).injective.ne K.hab
  had := (mirrorSubtypeEquiv P).injective.ne K.had
  hbc := (mirrorSubtypeEquiv P).injective.ne K.hbc.symm
  hbd := (mirrorSubtypeEquiv P).injective.ne K.hcd
  hcd := (mirrorSubtypeEquiv P).injective.ne K.hbd
  hfour := mirror_noFour K.hfour
  proper := mirror_proper K.proper
  monoB := by simpa using K.monoC
  monoC := by simpa using K.monoB
  monoD := by simpa using K.monoD
  inside := by simpa using mirror_strictlyInside_swap K.inside
  skeleton := K.mirrorSkeleton
  redHull := by
    intro z hz hc
    let z₀ : P := (mirrorSubtypeEquiv P).symm z
    have hz₀ : (z₀ : Point) ∈
        triangleHull (a : Point) (b : Point) (c : Point) := by
      apply mirror_mem_triangleHull_swap_iff.mp
      simpa [z₀] using hz
    have hc₀ : colour z₀ = colour a := by
      simpa [z₀] using hc
    rcases K.redHull z₀ hz₀ hc₀ with hza | hzb | hzc | hzd
    · exact Or.inl (by
        simpa [z₀] using congrArg (mirrorSubtypeEquiv P) hza)
    · exact Or.inr (Or.inr (Or.inl (by
        simpa [z₀] using congrArg (mirrorSubtypeEquiv P) hzb)))
    · exact Or.inr (Or.inl (by
        simpa [z₀] using congrArg (mirrorSubtypeEquiv P) hzc))
    · exact Or.inr (Or.inr (Or.inr (by
        simpa [z₀] using congrArg (mirrorSubtypeEquiv P) hzd)))
  otherColourBound := by
    intro e he
    have he₀ : e ≠ colour a := by simpa using he
    refine le_trans (Finset.card_le_card_of_injOn
      (fun z : mirrorFinset P ↦ (mirrorSubtypeEquiv P).symm z) ?_ ?_)
      (K.otherColourBound e he₀)
    · intro z hz
      change z ∈ pointsOfColourInTriangle (mirrorFinset P) (mirrorColour colour)
        (mirrorSubtypeEquiv P a : Point) (mirrorSubtypeEquiv P c : Point)
        (mirrorSubtypeEquiv P b : Point) e at hz
      change (mirrorSubtypeEquiv P).symm z ∈
        pointsOfColourInTriangle P colour (a : Point) (b : Point) (c : Point) e
      rw [mem_pointsOfColourInTriangle] at hz ⊢
      constructor
      · apply mirror_mem_triangleHull_swap_iff.mp
        simpa using hz.1
      · simpa [mirrorColour] using hz.2
    · intro x hx y hy hxy
      exact (mirrorSubtypeEquiv P).symm.injective hxy

private theorem cellPoints_mirror_card (x y z : Point) :
    (cellPoints (mirrorFinset P) (mirrorAffine y) (mirrorAffine x)
      (mirrorAffine z)).card = (cellPoints P x y z).card := by
  apply Nat.le_antisymm
  · apply Finset.card_le_card_of_injOn
      (fun p : mirrorFinset P ↦ (mirrorSubtypeEquiv P).symm p)
    · intro p hp
      change p ∈ cellPoints (mirrorFinset P) (mirrorAffine y)
        (mirrorAffine x) (mirrorAffine z) at hp
      change (mirrorSubtypeEquiv P).symm p ∈ cellPoints P x y z
      rw [mem_cellPoints] at hp ⊢
      apply mirror_strictlyInside_cell_iff.mp
      simpa using hp
    · intro p hp q hq hpq
      exact (mirrorSubtypeEquiv P).symm.injective hpq
  · apply Finset.card_le_card_of_injOn (mirrorSubtypeEquiv P)
    · intro p hp
      change p ∈ cellPoints P x y z at hp
      change mirrorSubtypeEquiv P p ∈
        cellPoints (mirrorFinset P) (mirrorAffine y) (mirrorAffine x)
          (mirrorAffine z)
      rw [mem_cellPoints] at hp ⊢
      simpa using mirror_strictlyInside_cell_iff.mpr hp
    · intro p hp q hq hpq
      exact (mirrorSubtypeEquiv P).injective hpq

@[simp] theorem mirror_I₁_card : K.mirror.I₁.card = K.I₁.card := by
  exact cellPoints_mirror_card (P := P) (b : Point) (c : Point) (d : Point)

@[simp] theorem mirror_I₂_card : K.mirror.I₂.card = K.I₃.card := by
  exact cellPoints_mirror_card (P := P) (a : Point) (b : Point) (d : Point)

@[simp] theorem mirror_I₃_card : K.mirror.I₃.card = K.I₂.card := by
  exact cellPoints_mirror_card (P := P) (c : Point) (a : Point) (d : Point)

@[simp] theorem rotate_I₁ : K.rotate.I₁ = K.I₂ := rfl
@[simp] theorem rotate_I₂ : K.rotate.I₂ = K.I₃ := rfl
@[simp] theorem rotate_I₃ : K.rotate.I₃ = K.I₁ := rfl

@[simp] theorem rotate_T₁_side (i : Fin 3) :
    K.rotate.T₁.side i = K.T₂.side i := by
  fin_cases i <;> rfl

@[simp] theorem rotate_T₂_side (i : Fin 3) :
    K.rotate.T₂.side i = K.T₃.side i := by
  fin_cases i <;> rfl

@[simp] theorem rotate_T₃_side (i : Fin 3) :
    K.rotate.T₃.side i = K.T₁.side i := by
  fin_cases i <;> rfl

/-- Transport a one-interior pattern in the old second cell to the first
cell after cyclic relabeling. -/
def rotateOne₂₁ {p : P} {i j k : Fin 3}
    (H : OneInteriorPatternAt colour (colour a) K.T₂ p i j k) :
    OneInteriorPatternAt colour (colour b) K.rotate.T₁ p i j k where
  hp := H.hp
  hij := H.hij
  hjk := H.hjk
  hki := H.hki
  beam_colour := by simpa using H.beam_colour
  beam_between := by simpa using H.beam_between
  p_colour_ne := by intro l; simpa using H.p_colour_ne l
  remaining_colour_ne := by simpa using H.remaining_colour_ne

/-- Transport a one-interior pattern in the old third cell to the second
cell after cyclic relabeling. -/
def rotateOne₃₂ {p : P} {i j k : Fin 3}
    (H : OneInteriorPatternAt colour (colour a) K.T₃ p i j k) :
    OneInteriorPatternAt colour (colour b) K.rotate.T₂ p i j k where
  hp := H.hp
  hij := H.hij
  hjk := H.hjk
  hki := H.hki
  beam_colour := by simpa using H.beam_colour
  beam_between := by simpa using H.beam_between
  p_colour_ne := by intro l; simpa using H.p_colour_ne l
  remaining_colour_ne := by simpa using H.remaining_colour_ne

/-- Transport a one-interior pattern in the old first cell to the third
cell after cyclic relabeling. -/
def rotateOne₁₃ {p : P} {i j k : Fin 3}
    (H : OneInteriorPatternAt colour (colour a) K.T₁ p i j k) :
    OneInteriorPatternAt colour (colour b) K.rotate.T₃ p i j k where
  hp := H.hp
  hij := H.hij
  hjk := H.hjk
  hki := H.hki
  beam_colour := by simpa using H.beam_colour
  beam_between := by simpa using H.beam_between
  p_colour_ne := by intro l; simpa using H.p_colour_ne l
  remaining_colour_ne := by simpa using H.remaining_colour_ne

@[simp] theorem mem_I₁ {p : P} : p ∈ K.I₁ ↔
    StrictlyInsideTriangle (b : Point) (c : Point) (d : Point) (p : Point) := by
  simp [I₁]

@[simp] theorem mem_I₂ {p : P} : p ∈ K.I₂ ↔
    StrictlyInsideTriangle (c : Point) (a : Point) (d : Point) (p : Point) := by
  simp [I₂]

@[simp] theorem mem_I₃ {p : P} : p ∈ K.I₃ ↔
    StrictlyInsideTriangle (a : Point) (b : Point) (d : Point) (p : Point) := by
  simp [I₃]

theorem interior_colour_ne_red₁
    (K : ConcaveConfiguration P colour a b c d) (p : P)
    (hp : StrictlyInsideTriangle (b : Point) (c : Point) (d : Point)
      (p : Point)) : colour p ≠ colour a := by
  apply allCellPoint_colour_ne_red K.inside K.redHull
  exact mem_allCellPoints.mpr (Or.inl hp)

theorem interior_colour_ne_red₂
    (K : ConcaveConfiguration P colour a b c d) (p : P)
    (hp : StrictlyInsideTriangle (c : Point) (a : Point) (d : Point)
      (p : Point)) : colour p ≠ colour a := by
  apply allCellPoint_colour_ne_red K.inside K.redHull
  exact mem_allCellPoints.mpr (Or.inr (Or.inl hp))

theorem interior_colour_ne_red₃
    (K : ConcaveConfiguration P colour a b c d) (p : P)
    (hp : StrictlyInsideTriangle (a : Point) (b : Point) (d : Point)
      (p : Point)) : colour p ≠ colour a := by
  apply allCellPoint_colour_ne_red K.inside K.redHull
  exact mem_allCellPoints.mpr (Or.inr (Or.inr hp))

noncomputable def M₁ : CellModel colour (colour a) K.T₁ :=
  Classical.choice (K.T₁.exists_model K.hfour K.proper K.interior_colour_ne_red₁)

noncomputable def M₂ : CellModel colour (colour a) K.T₂ :=
  Classical.choice (K.T₂.exists_model K.hfour K.proper K.interior_colour_ne_red₂)

noncomputable def M₃ : CellModel colour (colour a) K.T₃ :=
  Classical.choice (K.T₃.exists_model K.hfour K.proper K.interior_colour_ne_red₃)

@[simp] theorem T₁_side_zero : K.T₁.side 0 = K.skeleton.v₁ := rfl
@[simp] theorem T₁_side_one : K.T₁.side 1 = K.skeleton.u₃ := rfl
@[simp] theorem T₁_side_two : K.T₁.side 2 = K.skeleton.u₂ := rfl
@[simp] theorem T₂_side_zero : K.T₂.side 0 = K.skeleton.v₂ := rfl
@[simp] theorem T₂_side_one : K.T₂.side 1 = K.skeleton.u₁ := rfl
@[simp] theorem T₂_side_two : K.T₂.side 2 = K.skeleton.u₃ := rfl
@[simp] theorem T₃_side_zero : K.T₃.side 0 = K.skeleton.v₃ := rfl
@[simp] theorem T₃_side_one : K.T₃.side 1 = K.skeleton.u₂ := rfl
@[simp] theorem T₃_side_two : K.T₃.side 2 = K.skeleton.u₁ := rfl

theorem cellPoint_ne_skeleton
    {p : P}
    (hp : p ∈ K.I₁ ∨ p ∈ K.I₂ ∨ p ∈ K.I₃) (i : Fin 6) :
    p ≠ (![K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
      K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P) i := by
  intro e
  have hpAll : p ∈ allCellPoints P (a : Point) (b : Point) (c : Point) (d : Point) := by
    rw [mem_allCellPoints]
    rcases hp with h | h | h
    · exact Or.inl (K.mem_I₁.mp h)
    · exact Or.inr (Or.inl (K.mem_I₂.mp h))
    · exact Or.inr (Or.inr (K.mem_I₃.mp h))
  have hs :
      (![K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
        K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P) i ∈
        skeletonPoints K.skeleton := by
    exact mem_skeletonPoints.mpr ⟨i, rfl⟩
  subst p
  exact (Finset.disjoint_left.mp
    (skeletonPoints_disjoint_allCellPoints K.inside K.skeleton)) hs hpAll

theorem skeleton_ne (i j : Fin 6) (hij : i ≠ j) :
    (![K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
      K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P) i ≠
    (![K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
      K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P) j :=
  K.skeleton.blockers_injective.ne hij

theorem cellPoint_ne_T₁_side {p : P}
    (hp : p ∈ K.I₁ ∨ p ∈ K.I₂ ∨ p ∈ K.I₃) (i : Fin 3) :
    p ≠ K.T₁.side i := by
  fin_cases i
  · simpa using K.cellPoint_ne_skeleton hp 3
  · simpa using K.cellPoint_ne_skeleton hp 2
  · simpa using K.cellPoint_ne_skeleton hp 1

theorem cellPoint_ne_T₂_side {p : P}
    (hp : p ∈ K.I₁ ∨ p ∈ K.I₂ ∨ p ∈ K.I₃) (i : Fin 3) :
    p ≠ K.T₂.side i := by
  fin_cases i
  · simpa using K.cellPoint_ne_skeleton hp 4
  · simpa using K.cellPoint_ne_skeleton hp 0
  · simpa using K.cellPoint_ne_skeleton hp 2

theorem cellPoint_ne_T₃_side {p : P}
    (hp : p ∈ K.I₁ ∨ p ∈ K.I₂ ∨ p ∈ K.I₃) (i : Fin 3) :
    p ≠ K.T₃.side i := by
  fin_cases i
  · simpa using K.cellPoint_ne_skeleton hp 5
  · simpa using K.cellPoint_ne_skeleton hp 1
  · simpa using K.cellPoint_ne_skeleton hp 0

theorem interiorPoints_empty₁ (h : K.I₁.card = 0) :
    cellInteriorPoints P (b : Point) (c : Point) (d : Point) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [← cellPoints_card_eq_cellInteriorPoints_card]
  exact h

theorem interiorPoints_empty₂ (h : K.I₂.card = 0) :
    cellInteriorPoints P (c : Point) (a : Point) (d : Point) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [← cellPoints_card_eq_cellInteriorPoints_card]
  exact h

theorem interiorPoints_empty₃ (h : K.I₃.card = 0) :
    cellInteriorPoints P (a : Point) (b : Point) (d : Point) = ∅ := by
  apply Finset.card_eq_zero.mp
  rw [← cellPoints_card_eq_cellInteriorPoints_card]
  exact h

private theorem fin4_eq_one_of_three_of_avoid
    {red x x₀ x₁ x₂ : Fin 4}
    (hx : x ≠ red) (h₀ : x₀ ≠ red) (h₁ : x₁ ≠ red) (h₂ : x₂ ≠ red)
    (h₀₁ : x₀ ≠ x₁) (h₁₂ : x₁ ≠ x₂) (h₂₀ : x₂ ≠ x₀) :
    x = x₀ ∨ x = x₁ ∨ x = x₂ := by
  omega

private theorem fin3_eq_one_of_three_local
    (x i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    x = i ∨ x = j ∨ x = k := by
  by_contra h
  push_neg at h
  have hxiv : x.val ≠ i.val := fun e ↦ h.1 (Fin.ext e)
  have hxjv : x.val ≠ j.val := fun e ↦ h.2.1 (Fin.ext e)
  have hxkv : x.val ≠ k.val := fun e ↦ h.2.2 (Fin.ext e)
  have hijv : i.val ≠ j.val := fun e ↦ hij (Fin.ext e)
  have hjkv : j.val ≠ k.val := fun e ↦ hjk (Fin.ext e)
  have hkiv : k.val ≠ i.val := fun e ↦ hki (Fin.ext e)
  omega

/-- A rainbow side triple exhausts the three nonred colours. -/
theorem colour_eq_some_side
    {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C)
    (hpair : Pairwise fun i j : Fin 3 ↦ colour (T.side i) ≠ colour (T.side j))
    (p : P) (hp : colour p ≠ red) :
    ∃ i : Fin 3, colour p = colour (T.side i) := by
  have h := fin4_eq_one_of_three_of_avoid hp T.colour_s₀ T.colour_s₁ T.colour_s₂
    (hpair (i := 0) (j := 1) (by decide))
    (hpair (i := 1) (j := 2) (by decide))
    (hpair (i := 2) (j := 0) (by decide))
  rcases h with h | h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩
  · exact ⟨2, by simpa using h⟩

theorem I_sum_le_three : K.I₁.card + K.I₂.card + K.I₃.card ≤ 3 := by
  have h := allCellPoints_card_le_three K.inside K.skeleton K.redHull
    K.otherColourBound
  rw [allCellPoints_card_eq_sum] at h
  simpa [I₁, I₂, I₃, add_assoc] using h

theorem nonred_card₁ : K.T₁.nonredPoints.card = 3 + K.I₁.card := by
  rw [K.T₁.nonredPoints_card, ← cellPoints_card_eq_cellInteriorPoints_card]
  rfl

theorem nonred_card₂ : K.T₂.nonredPoints.card = 3 + K.I₂.card := by
  rw [K.T₂.nonredPoints_card, ← cellPoints_card_eq_cellInteriorPoints_card]
  rfl

theorem nonred_card₃ : K.T₃.nonredPoints.card = 3 + K.I₃.card := by
  rw [K.T₃.nonredPoints_card, ← cellPoints_card_eq_cellInteriorPoints_card]
  rfl

theorem skeleton_mem_outer (i : Fin 6) :
    ((![K.skeleton.u₁, K.skeleton.u₂, K.skeleton.u₃,
      K.skeleton.v₁, K.skeleton.v₂, K.skeleton.v₃] : Fin 6 → P) i : Point) ∈
      triangleHull (a : Point) (b : Point) (c : Point) := by
  have ha : (a : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    vertex_mem_triangleHull _ _ _
  have hb : (b : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    subset_convexHull ℝ _ (by simp [triangleHull])
  have hc : (c : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    subset_convexHull ℝ _ (by simp [triangleHull])
  have hd := strictlyInsideTriangle_mem_triangleHull K.inside
  fin_cases i
  · exact openSegment_mem_triangleHull_of_mem ha hd K.skeleton.hu₁
  · exact openSegment_mem_triangleHull_of_mem hb hd K.skeleton.hu₂
  · exact openSegment_mem_triangleHull_of_mem hc hd K.skeleton.hu₃
  · exact openSegment_mem_triangleHull_of_mem hb hc K.skeleton.hv₁
  · exact openSegment_mem_triangleHull_of_mem ha hc K.skeleton.hv₂
  · exact openSegment_mem_triangleHull_of_mem ha hb K.skeleton.hv₃

private theorem four_same_colour_card_contradiction
    {P : Finset Point} {colour : P → Fin 4} {a b c : Point}
    {red : Fin 4} {x₀ x₁ x₂ x₃ : P}
    (h₀₁ : x₀ ≠ x₁) (h₀₂ : x₀ ≠ x₂) (h₀₃ : x₀ ≠ x₃)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃)
    (hx₀ : (x₀ : Point) ∈ triangleHull a b c)
    (hx₁ : (x₁ : Point) ∈ triangleHull a b c)
    (hx₂ : (x₂ : Point) ∈ triangleHull a b c)
    (hx₃ : (x₃ : Point) ∈ triangleHull a b c)
    (hc₁ : colour x₁ = colour x₀) (hc₂ : colour x₂ = colour x₀)
    (hc₃ : colour x₃ = colour x₀) (hred : colour x₀ ≠ red)
    (hbound : (pointsOfColourInTriangle P colour a b c (colour x₀)).card ≤ 3) : False := by
  let Q : Finset P := {x₀, x₁, x₂, x₃}
  let F := pointsOfColourInTriangle P colour a b c (colour x₀)
  have hsub : Q ⊆ F := by
    intro x hx
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mem_pointsOfColourInTriangle.mpr ⟨hx₀, rfl⟩
    · exact mem_pointsOfColourInTriangle.mpr ⟨hx₁, hc₁⟩
    · exact mem_pointsOfColourInTriangle.mpr ⟨hx₂, hc₂⟩
    · exact mem_pointsOfColourInTriangle.mpr ⟨hx₃, hc₃⟩
  have hcard := Finset.card_le_card hsub
  have hQ : Q.card = 4 := by
    simp [Q, h₀₁, h₀₂, h₀₃, h₁₂, h₁₃, h₂₃]
  dsimp [F] at hcard
  omega

/-- Points strictly in cell one and cell two lie on opposite sides of the
separator line `cd`; cell three may meet either side. -/
theorem turn_cd_pos_of_mem_I₁ {p : P} (hp : p ∈ K.I₁) :
    0 < turn (c : Point) (d : Point) (p : Point) :=
  (K.mem_I₁.mp hp).2.1

theorem turn_cd_neg_of_mem_I₂ {p : P} (hp : p ∈ K.I₂) :
    turn (c : Point) (d : Point) (p : Point) < 0 := by
  have h := (K.mem_I₂.mp hp).2.2
  rw [turn_swap_first] at h
  linarith

theorem turn_cd_ne_zero_of_mem_I₃ {p : P} (hp : p ∈ K.I₃) :
    turn (c : Point) (d : Point) (p : Point) ≠ 0 := by
  intro hz
  rcases point_eq_of_on_full_line K.hfour K.hcd K.skeleton.hu₃ hz with h | h | h
  · have hi := (K.mem_I₃.mp hp).2.1
    have hout := K.inside.2.1
    rw [h, turn_swap_last] at hi
    linarith
  · exact (strictlyInsideTriangle_ne_vertices (K.mem_I₃.mp hp)).2.2
      (congrArg Subtype.val h)
  · have hi := (K.mem_I₃.mp hp).2.1
    rw [h] at hi
    obtain ⟨t, ht, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (b : Point)) (b := (d : Point))
        K.skeleton.hu₃
    have hout := K.inside.2.1
    rw [turn_swap_last] at hout
    simp only [turn_self_right] at heq
    nlinarith

/-- A strict point of cell two is not on its opposite red spoke `bd`. -/
theorem turn_bd_ne_zero_of_mem_I₂ {p : P} (hp : p ∈ K.I₂) :
    turn (b : Point) (d : Point) (p : Point) ≠ 0 := by
  intro hz
  rcases point_eq_of_on_full_line K.hfour K.hbd K.skeleton.hu₂ hz with h | h | h
  · have hi := (K.mem_I₂.mp hp).2.1
    have hout := K.inside.1
    rw [h, turn_swap_last] at hi
    linarith
  · exact (strictlyInsideTriangle_ne_vertices (K.mem_I₂.mp hp)).2.2
      (congrArg Subtype.val h)
  · exact (K.cellPoint_ne_skeleton (Or.inr (Or.inl hp)) 1 h).elim

private theorem turn_neg_of_between_nonpos
    {e f x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : turn e f x < 0) (hy : turn e f y ≤ 0) :
    turn e f z < 0 := by
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment (a := e) (b := f) hz
  rw [heq]
  nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hx,
    mul_nonpos_of_nonneg_of_nonpos ht.le hy]

private theorem turn_pos_of_between_nonneg
    {e f x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : 0 < turn e f x) (hy : 0 ≤ turn e f y) :
    0 < turn e f z :=
  edgeTurn_pos_of_mem_openSegment hz hx.le hy (Or.inl hx)

private theorem turn_pos_of_right_of_positive_between_nonpos
    {e f x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : turn e f x ≤ 0) (hzpos : 0 < turn e f z) :
    0 < turn e f y := by
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment (a := e) (b := f) hz
  rw [heq] at hzpos
  by_contra h
  have hy : turn e f y ≤ 0 := le_of_not_gt h
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht1.le) hx,
    mul_nonpos_of_nonneg_of_nonpos ht.le hy]

private theorem turn_neg_of_right_of_negative_between_nonneg
    {e f x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : 0 ≤ turn e f x) (hzneg : turn e f z < 0) :
    turn e f y < 0 := by
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment (a := e) (b := f) hz
  rw [heq] at hzneg
  by_contra h
  have hy : 0 ≤ turn e f y := le_of_not_gt h
  nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) hx, mul_nonneg ht.le hy]

private theorem strict_outer_of_between_strict_hull
    {x y z : Point}
    (hpos : 0 < turn (a : Point) (b : Point) (c : Point))
    (hx : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point) x)
    (hy : y ∈ triangleHull (a : Point) (b : Point) (c : Point))
    (hz : z ∈ openSegment ℝ x y) :
    StrictlyInsideTriangle (a : Point) (b : Point) (c : Point) z := by
  have hey := triangle_edge_nonneg hpos.le hy
  exact ⟨edgeTurn_pos_of_mem_openSegment hz hx.1.le hey.1 (Or.inl hx.1),
    edgeTurn_pos_of_mem_openSegment hz hx.2.1.le hey.2.1 (Or.inl hx.2.1),
    edgeTurn_pos_of_mem_openSegment hz hx.2.2.le hey.2.2 (Or.inl hx.2.2)⟩

/-- A crosscut through the two sides incident with `r` separates `r` from
the opposite side. -/
private theorem triangle_crosscut_signs
    {p q r g b₀ : Point} (hpqr : 0 < turn p q r)
    (hg : g ∈ openSegment ℝ p r) (hb : b₀ ∈ openSegment ℝ q r) :
    0 < turn b₀ g p ∧ 0 < turn b₀ g q ∧ turn b₀ g r < 0 := by
  have hrpq : 0 < turn r p q := by
    rw [turn_rotate, turn_rotate]
    exact hpqr
  have hrpb : 0 < turn r p b₀ :=
    edgeTurn_pos_of_mem_openSegment hb hrpq.le (by simp) (Or.inl hrpq)
  have hpbr : 0 < turn p b₀ r := by
    rw [turn_rotate r p b₀]
    exact hrpb
  have hpbg : 0 < turn p b₀ g :=
    edgeTurn_pos_of_mem_openSegment hg (by simp) hpbr.le (Or.inr hpbr)
  have hbgp : 0 < turn b₀ g p := by
    rw [turn_rotate p b₀ g]
    exact hpbg
  have hbgr : turn b₀ g r < 0 := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := b₀) (b := g) hg
    simp only [turn_self_right] at heq
    nlinarith [mul_pos (sub_pos.mpr ht1) hbgp]
  have hbgq : 0 < turn b₀ g q := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := b₀) (b := g) hb
    simp only [turn_self_left] at heq
    nlinarith [mul_neg_of_pos_of_neg ht0 hbgr]
  exact ⟨hbgp, hbgq, hbgr⟩

/-- The three spoke blockers surround the inner red point. -/
private theorem red_center_strictly_inside_spoke_triangle :
    StrictlyInsideTriangle
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (d : Point) := by
  have hadb : turn (a : Point) (d : Point) (b : Point) < 0 := by
    rw [turn_swap_last]
    linarith [K.inside.1]
  have hadu₂ : turn (a : Point) (d : Point) (K.skeleton.u₂ : Point) < 0 :=
    turn_neg_of_between_nonpos K.skeleton.hu₂ hadb (by simp)
  have had₂ : 0 < turn (a : Point) (K.skeleton.u₂ : Point) (d : Point) := by
    rw [turn_swap_last]
    linarith
  have h₁ : 0 < turn (K.skeleton.u₁ : Point)
      (K.skeleton.u₂ : Point) (d : Point) := by
    have hrot : 0 < turn (K.skeleton.u₂ : Point) (d : Point) (a : Point) := by
      simpa only [turn_rotate] using had₂
    have h := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₁ hrot.le (by simp)
      (Or.inl hrot)
    simpa only [turn_rotate] using h
  have hbdc : turn (b : Point) (d : Point) (c : Point) < 0 := by
    rw [turn_swap_last]
    linarith [K.inside.2.1]
  have hbdu₃ : turn (b : Point) (d : Point) (K.skeleton.u₃ : Point) < 0 :=
    turn_neg_of_between_nonpos K.skeleton.hu₃ hbdc (by simp)
  have hbd₃ : 0 < turn (b : Point) (K.skeleton.u₃ : Point) (d : Point) := by
    rw [turn_swap_last]
    linarith
  have h₂ : 0 < turn (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (d : Point) := by
    have hrot : 0 < turn (K.skeleton.u₃ : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using hbd₃
    have h := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hrot.le (by simp)
      (Or.inl hrot)
    simpa only [turn_rotate] using h
  have hcda : turn (c : Point) (d : Point) (a : Point) < 0 := by
    rw [turn_swap_last]
    linarith [K.inside.2.2]
  have hcdu₁ : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 :=
    turn_neg_of_between_nonpos K.skeleton.hu₁ hcda (by simp)
  have hcd₁ : 0 < turn (c : Point) (K.skeleton.u₁ : Point) (d : Point) := by
    rw [turn_swap_last]
    linarith
  have h₃ : 0 < turn (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) (d : Point) := by
    have hrot : 0 < turn (K.skeleton.u₁ : Point) (d : Point) (c : Point) := by
      simpa only [turn_rotate] using hcd₁
    have h := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₃ hrot.le (by simp)
      (Or.inl hrot)
    rw [turn_rotate] at h
    exact h
  exact ⟨h₁, h₂, h₃⟩

/-- A point between a vertex and the relative interior of the opposite
side is strictly inside the triangle. -/
private theorem strictlyInside_between_vertex_and_opposite_side
    {x y z s r : Point} (hxyz : 0 < turn x y z)
    (hs : s ∈ openSegment ℝ z x) (hr : r ∈ openSegment ℝ s y) :
    StrictlyInsideTriangle x y z r := by
  have hxyS : 0 < turn x y s :=
    edgeTurn_pos_of_mem_openSegment hs hxyz.le (by simp) (Or.inl hxyz)
  have hyzS : 0 < turn y z s := by
    have hrot : 0 < turn y z x := by
      simpa only [turn_rotate] using hxyz
    exact edgeTurn_pos_of_mem_openSegment hs (by simp) hrot.le (Or.inr hrot)
  have hzxS : turn z x s = 0 := turn_eq_zero_of_between hs
  have hzxY : 0 < turn z x y := by
    simpa only [turn_rotate] using hxyz
  exact ⟨
    edgeTurn_pos_of_mem_openSegment hr hxyS.le (by simp) (Or.inl hxyS),
    edgeTurn_pos_of_mem_openSegment hr hyzS.le (by simp) (Or.inl hyzS),
    edgeTurn_pos_of_mem_openSegment hr (le_of_eq hzxS.symm) hzxY.le
      (Or.inr hzxY)⟩

/-- Each outer-side blocker is strictly beyond the corresponding side of
the spoke triangle. -/
private theorem v₁_spoke_side_neg :
    turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.v₁ : Point) < 0 := by
  have hcross := triangle_crosscut_signs K.inside.2.1
    K.skeleton.hu₂ K.skeleton.hu₃
  have hpos : 0 < turn (K.skeleton.u₃ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.v₁ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hv₁ hcross.1.le
      hcross.2.1.le (Or.inl hcross.1)
  rw [turn_swap_first] at hpos
  linarith

private theorem v₂_spoke_side_neg :
    turn (K.skeleton.u₃ : Point) (K.skeleton.u₁ : Point)
      (K.skeleton.v₂ : Point) < 0 := by
  have hcross := triangle_crosscut_signs K.inside.2.2
    K.skeleton.hu₃ K.skeleton.hu₁
  have hpos : 0 < turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.v₂ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hv₂ hcross.2.1.le
      hcross.1.le (Or.inl hcross.2.1)
  rw [turn_swap_first] at hpos
  linarith

private theorem v₃_spoke_side_neg :
    turn (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.v₃ : Point) < 0 := by
  have hcross := triangle_crosscut_signs K.inside.1
    K.skeleton.hu₁ K.skeleton.hu₂
  have hpos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₁ : Point)
      (K.skeleton.v₃ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hv₃ hcross.1.le
      hcross.2.1.le (Or.inl hcross.1)
  rw [turn_swap_first] at hpos
  linarith

/-- In the `C,D` beam arrangement, the only possible point on the chord
from the `C`-beam point to the opposite spoke blocker is the red centre. -/
private theorem blocker_from_C_beam_to_u₂_eq_center
    {w p r : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (hwBeam : (w : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point))
    (hpNeg : turn (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (p : Point) < 0)
    (hr : (r : Point) ∈ openSegment ℝ
      (w : Point) (K.skeleton.u₂ : Point)) : r = d := by
  have hcenter := K.red_center_strictly_inside_spoke_triangle
  have hcenterPos := turn_pos_of_strictlyInsideTriangle hcenter
  have hrCentral : StrictlyInsideTriangle
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (r : Point) :=
    strictlyInside_between_vertex_and_opposite_side hcenterPos
      (by simpa only [openSegment_symm] using hwBeam) hr
  have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (w : Point) := strict_cell_strict_outer K.inside
        (Or.inr (Or.inl (K.mem_I₂.mp hw)))
  have hrOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (r : Point) := strict_outer_of_between_strict_hull
        (turn_pos_of_strictlyInsideTriangle K.inside) hwOuter
        (K.skeleton_mem_outer 1) hr
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuter
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.2
      (congrArg Subtype.val hrc)).elim
  · exact hrd
  · exact ((strictlyInsideTriangle_ne_vertices hrCentral).1
      (congrArg Subtype.val hru₁)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrCentral).2.1
      (congrArg Subtype.val hru₂)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrCentral).2.2
      (congrArg Subtype.val hru₃)).elim
  · rw [hrv₁] at hrCentral
    linarith [hrCentral.2.1, K.v₁_spoke_side_neg]
  · rw [hrv₂] at hrCentral
    linarith [hrCentral.2.2, K.v₂_spoke_side_neg]
  · rw [hrv₃] at hrCentral
    linarith [hrCentral.1, K.v₃_spoke_side_neg]
  · have hrI : r ∈ K.I₁ := K.mem_I₁.mpr hr₁
    rw [hempty₁] at hrI
    simp at hrI
  · have hrw := hunique₂ r (K.mem_I₂.mpr hr₂)
    subst r
    have hEq := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hr
    exact (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
      (Subtype.ext hEq)).elim
  · have hrp := hunique₃ r (K.mem_I₃.mpr hr₃)
    rw [hrp] at hrCentral
    linarith [hrCentral.1, hpNeg]

/-- Reflected central-triangle localization: a blocker from a point on the
`F` beam `u₁u₂` to the opposite spoke `u₃` can only be the red centre. -/
private theorem blocker_from_F_beam_to_u₃_eq_center
    {w p r : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (hwBeam : (w : Point) ∈ openSegment ℝ
      (K.skeleton.v₂ : Point) (K.skeleton.u₁ : Point))
    (hpBeam : (p : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point))
    (hr : (r : Point) ∈ openSegment ℝ
      (p : Point) (K.skeleton.u₃ : Point)) : r = d := by
  have hcenter := K.red_center_strictly_inside_spoke_triangle
  have hcenterPos := turn_pos_of_strictlyInsideTriangle hcenter
  have hrotPos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) := by
    simpa only [turn_rotate] using hcenterPos
  have hrRot := strictlyInside_between_vertex_and_opposite_side hrotPos hpBeam hr
  have hrCentral : StrictlyInsideTriangle
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (r : Point) :=
    ⟨hrRot.2.2, hrRot.1, hrRot.2.1⟩
  have hpOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (p : Point) := strict_cell_strict_outer K.inside
        (Or.inr (Or.inr (K.mem_I₃.mp hp)))
  have hrOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (r : Point) := strict_outer_of_between_strict_hull
        (turn_pos_of_strictlyInsideTriangle K.inside) hpOuter
        (K.skeleton_mem_outer 2) hr
  have hwNeg : turn (K.skeleton.u₃ : Point) (K.skeleton.u₁ : Point)
      (w : Point) < 0 :=
    turn_neg_of_between_nonpos hwBeam K.v₂_spoke_side_neg (by simp)
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuter
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.2
      (congrArg Subtype.val hrc)).elim
  · exact hrd
  · exact ((strictlyInsideTriangle_ne_vertices hrCentral).1
      (congrArg Subtype.val hru₁)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrCentral).2.1
      (congrArg Subtype.val hru₂)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrCentral).2.2
      (congrArg Subtype.val hru₃)).elim
  · rw [hrv₁] at hrCentral
    linarith [hrCentral.2.1, K.v₁_spoke_side_neg]
  · rw [hrv₂] at hrCentral
    linarith [hrCentral.2.2, K.v₂_spoke_side_neg]
  · rw [hrv₃] at hrCentral
    linarith [hrCentral.1, K.v₃_spoke_side_neg]
  · have hrI : r ∈ K.I₁ := K.mem_I₁.mpr hr₁
    rw [hempty₁] at hrI
    simp at hrI
  · have hrw := hunique₂ r (K.mem_I₂.mpr hr₂)
    rw [hrw] at hrCentral
    linarith [hrCentral.2.2, hwNeg]
  · have hrp := hunique₃ r (K.mem_I₃.mpr hr₃)
    subst r
    have hEq := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hr
    exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
      (Subtype.ext hEq)).elim

/-- A blocker on a chord starting at a strict point of the outer triangle
is either the inner red point, a spoke blocker, or a strict cell point.
The three outer vertices and three outer-side blockers are excluded by
strictness. -/
private theorem strict_outer_chord_cases
    {x y r : P}
    (hx : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (x : Point))
    (hy : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
    (hr : (r : Point) ∈ openSegment ℝ (x : Point) (y : Point)) :
    r = d ∨ r = K.skeleton.u₁ ∨ r = K.skeleton.u₂ ∨
      r = K.skeleton.u₃ ∨ r ∈ K.I₁ ∨ r ∈ K.I₂ ∨ r ∈ K.I₃ := by
  have hrOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (r : Point) := strict_outer_of_between_strict_hull
        (turn_pos_of_strictlyInsideTriangle K.inside) hx hy hr
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuter
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.2
      (congrArg Subtype.val hrc)).elim
  · exact Or.inl hrd
  · exact Or.inr (Or.inl hru₁)
  · exact Or.inr (Or.inr (Or.inl hru₂))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hru₃)))
  · rw [hrv₁] at hrOuter
    linarith [hrOuter.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
  · rw [hrv₂] at hrOuter
    have hz := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz
    linarith [hrOuter.2.2, hz]
  · rw [hrv₃] at hrOuter
    linarith [hrOuter.1, turn_eq_zero_of_between K.skeleton.hv₃]
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (K.mem_I₁.mpr hr₁)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (K.mem_I₂.mpr hr₂))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (K.mem_I₃.mpr hr₃))))))

private theorem turn_pos_beyond_zero_from_neg
    {l₀ l₁ x z y : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : turn l₀ l₁ x < 0) (hz0 : turn l₀ l₁ z = 0) :
    0 < turn l₀ l₁ y := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := l₀) (b := l₁) hz
  rw [hz0] at heq
  nlinarith

private theorem turn_neg_beyond_zero_from_pos
    {l₀ l₁ x z y : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : 0 < turn l₀ l₁ x) (hz0 : turn l₀ l₁ z = 0) :
    turn l₀ l₁ y < 0 := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := l₀) (b := l₁) hz
  rw [hz0] at heq
  nlinarith

/-- Betweenness is nested along a ray: if `q` is between `p,s` and `s` is
between `p,y`, then `q` is between `p,y`. -/
private theorem openSegment_left_nested
    {p q s y : Point} (hq : q ∈ openSegment ℝ p s)
    (hs : s ∈ openSegment ℝ p y) : q ∈ openSegment ℝ p y := by
  rw [openSegment_eq_image] at hq hs ⊢
  obtain ⟨t, ht, rfl⟩ := hq
  obtain ⟨u, hu, rfl⟩ := hs
  refine ⟨t * u, ⟨mul_pos ht.1 hu.1, ?_⟩, ?_⟩
  · have htu : t * u < u := by
      nlinarith [mul_pos (sub_pos.mpr ht.2) hu.1]
    exact htu.trans hu.2
  · simp
    module

/-- Two saturated three-point lines through `z` exclude all four of their
named points as blockers from `z` to a fourth target.  The target is allowed
to be the portal endpoint itself. -/
private theorem three_line_candidates_exclude
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {z x w e portal y : P}
    (hze : z ≠ e) (hzy : z ≠ y) (hey : e ≠ y)
    (hportalw : portal ≠ w) (hportalz : portal ≠ z)
    (hwz : w ≠ z) (hwy : w ≠ y)
    (hxLine : (x : Point) ∈ openSegment ℝ (z : Point) (e : Point))
    (hzLine : (z : Point) ∈ openSegment ℝ (portal : Point) (w : Point)) :
    (z : Point) ∉ openSegment ℝ (z : Point) (y : Point) ∧
      (x : Point) ∉ openSegment ℝ (z : Point) (y : Point) ∧
      (w : Point) ∉ openSegment ℝ (z : Point) (y : Point) ∧
      (portal : Point) ∉ openSegment ℝ (z : Point) (y : Point) := by
  have hzNot : (z : Point) ∉ openSegment ℝ (z : Point) (y : Point) := by
    intro h
    exact hzy (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp h))
  have hxNot : (x : Point) ∉ openSegment ℝ (z : Point) (y : Point) := by
    intro h
    have heq := other_endpoint_eq_of_common_blocker hfour hze hzy hxLine h
    exact hey heq
  by_cases hy : y = portal
  · subst y
    have hwNot : (w : Point) ∉
        openSegment ℝ (z : Point) (portal : Point) := by
      intro h
      exact not_two_mutual_openSegments (Subtype.val_injective.ne hportalw)
        ⟨hzLine, by simpa only [openSegment_symm] using h⟩
    have hpNot : (portal : Point) ∉
        openSegment ℝ (z : Point) (portal : Point) := by
      intro h
      exact hportalz (Subtype.ext
        ((right_mem_openSegment_iff (𝕜 := ℝ)).mp h).symm)
    exact ⟨hzNot, hxNot, hwNot, hpNot⟩
  · have hcross := first_pair_points_do_not_block_second hfour
      hportalw hzy hportalz (fun h ↦ hy h.symm) hwz hwy hzLine
    exact ⟨hzNot, hxNot, hcross.2, hcross.1⟩

/-- The crosscut `v₃v₁` and the spoke `bd` cannot have their intersection
also on the chord from a point of the beam `u₁v₃` to `u₃`. -/
theorem u₂_cannot_block_both_exceptional_pairs
    {p : P}
    (hpBeam : (p : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.v₃ : Point))
    (hu₂Boundary : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
      (K.skeleton.v₁ : Point) (K.skeleton.v₃ : Point))
    (hu₂Interior : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
      (p : Point) (K.skeleton.u₃ : Point)) : False := by
  have hCAB : 0 < turn (c : Point) (a : Point) (b : Point) := by
    rw [turn_rotate, turn_rotate]
    exact turn_pos_of_strictlyInsideTriangle K.inside
  have hcross := triangle_crosscut_signs hCAB
    (by simpa only [openSegment_symm] using K.skeleton.hv₁)
    K.skeleton.hv₃
  have hu₂zero : turn (K.skeleton.v₃ : Point) (K.skeleton.v₁ : Point)
      (K.skeleton.u₂ : Point) = 0 := by
    have h := turn_eq_zero_of_between hu₂Boundary
    rw [turn_swap_first] at h
    linarith
  have hdpos : 0 < turn (K.skeleton.v₃ : Point) (K.skeleton.v₁ : Point)
      (d : Point) :=
    turn_pos_beyond_zero_from_neg K.skeleton.hu₂ hcross.2.2 hu₂zero
  have hu₁pos : 0 < turn (K.skeleton.v₃ : Point) (K.skeleton.v₁ : Point)
      (K.skeleton.u₁ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₁ hcross.2.1.le hdpos.le
      (Or.inl hcross.2.1)
  have hu₃pos : 0 < turn (K.skeleton.v₃ : Point) (K.skeleton.v₁ : Point)
      (K.skeleton.u₃ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₃ hcross.1.le hdpos.le
      (Or.inl hcross.1)
  have hpPos : 0 < turn (K.skeleton.v₃ : Point) (K.skeleton.v₁ : Point)
      (p : Point) :=
    edgeTurn_pos_of_mem_openSegment hpBeam hu₁pos.le (by simp)
      (Or.inl hu₁pos)
  have hu₂pos := edgeTurn_pos_of_mem_openSegment hu₂Interior hpPos.le hu₃pos.le
    (Or.inl hpPos)
  linarith

/-- Reflected crosscut obstruction for the beam `v₃u₂`. -/
theorem u₁_cannot_block_both_exceptional_pairs
    {p : P}
    (hpBeam : (p : Point) ∈ openSegment ℝ
      (K.skeleton.v₃ : Point) (K.skeleton.u₂ : Point))
    (hu₁Boundary : (K.skeleton.u₁ : Point) ∈ openSegment ℝ
      (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point))
    (hu₁Interior : (K.skeleton.u₁ : Point) ∈ openSegment ℝ
      (p : Point) (K.skeleton.u₃ : Point)) : False := by
  have hBCA : 0 < turn (b : Point) (c : Point) (a : Point) := by
    rw [turn_rotate]
    exact turn_pos_of_strictlyInsideTriangle K.inside
  have hcross := triangle_crosscut_signs hBCA
    (by simpa only [openSegment_symm] using K.skeleton.hv₃)
    (by simpa only [openSegment_symm] using K.skeleton.hv₂)
  have hu₁zero : turn (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point)
      (K.skeleton.u₁ : Point) = 0 :=
    turn_eq_zero_of_between hu₁Boundary
  have hdpos : 0 < turn (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point)
      (d : Point) :=
    turn_pos_beyond_zero_from_neg K.skeleton.hu₁ hcross.2.2 hu₁zero
  have hu₂pos : 0 < turn (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point)
      (K.skeleton.u₂ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hcross.1.le hdpos.le
      (Or.inl hcross.1)
  have hu₃pos : 0 < turn (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point)
      (K.skeleton.u₃ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₃ hcross.2.1.le hdpos.le
      (Or.inl hcross.2.1)
  have hpPos : 0 < turn (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point)
      (p : Point) :=
    edgeTurn_pos_of_mem_openSegment hpBeam (by simp) hu₂pos.le
      (Or.inr hu₂pos)
  have hu₁pos := edgeTurn_pos_of_mem_openSegment hu₁Interior hpPos.le hu₃pos.le
    (Or.inl hpPos)
  linarith

/-- Third cyclic crosscut obstruction, used by the reflected `A,E` beam
pair. -/
theorem u₃_cannot_block_both_exceptional_pairs
    {w : P}
    (hwBeam : (w : Point) ∈ openSegment ℝ
      (K.skeleton.v₂ : Point) (K.skeleton.u₁ : Point))
    (hu₃Boundary : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
      (K.skeleton.v₁ : Point) (K.skeleton.v₂ : Point))
    (hu₃Interior : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
      (w : Point) (K.skeleton.u₂ : Point)) : False := by
  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  have hcross := triangle_crosscut_signs habc K.skeleton.hv₂ K.skeleton.hv₁
  have hu₃zero : turn (K.skeleton.v₁ : Point) (K.skeleton.v₂ : Point)
      (K.skeleton.u₃ : Point) = 0 := turn_eq_zero_of_between hu₃Boundary
  have hdpos : 0 < turn (K.skeleton.v₁ : Point) (K.skeleton.v₂ : Point)
      (d : Point) :=
    turn_pos_beyond_zero_from_neg K.skeleton.hu₃ hcross.2.2 hu₃zero
  have hu₁pos : 0 < turn (K.skeleton.v₁ : Point) (K.skeleton.v₂ : Point)
      (K.skeleton.u₁ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₁ hcross.1.le hdpos.le
      (Or.inl hcross.1)
  have hu₂pos : 0 < turn (K.skeleton.v₁ : Point) (K.skeleton.v₂ : Point)
      (K.skeleton.u₂ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hcross.2.1.le hdpos.le
      (Or.inl hcross.2.1)
  have hwpos : 0 < turn (K.skeleton.v₁ : Point) (K.skeleton.v₂ : Point)
      (w : Point) :=
    edgeTurn_pos_of_mem_openSegment hwBeam (by simp) hu₁pos.le
      (Or.inr hu₁pos)
  have hu₃pos := edgeTurn_pos_of_mem_openSegment hu₃Interior hwpos.le hu₂pos.le
    (Or.inl hwpos)
  linarith

/-- Portal localization from the negative half of cell three into cell two.
The only skeleton point which can occur on such a segment is their common
side blocker `u₁`. -/
theorem portal_three_to_two
    {z y r : P} (hz : z ∈ K.I₃)
    (hzneg : turn (c : Point) (d : Point) (z : Point) < 0)
    (hy : (y : Point) ∈ triangleHull (c : Point) (a : Point) (d : Point))
    (hr : (r : Point) ∈ openSegment ℝ (z : Point) (y : Point)) :
    r ∈ K.I₃ ∨ r = K.skeleton.u₁ ∨ r ∈ K.I₂ := by
  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle K.inside
  have hzOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (z : Point) := strict_cell_strict_outer K.inside (Or.inr (Or.inr (K.mem_I₃.mp hz)))
  have hyOuter : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    cell_two_hull_subset_outer K.inside hy
  have hrOuterStrict := strict_outer_of_between_strict_hull habc hzOuter hyOuter hr
  have hycd : turn (c : Point) (d : Point) (y : Point) ≤ 0 := by
    have he := triangle_edge_nonneg K.inside.2.2.le hy
    -- `da` is not the required side; the third cell edge is `dc`.
    have hdc := he.2.2
    rw [turn_swap_first] at hdc
    linarith
  have hrcd : turn (c : Point) (d : Point) (r : Point) < 0 :=
    turn_neg_of_between_nonpos hr hzneg hycd
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuterStrict
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.2
      (congrArg Subtype.val hrc)).elim
  · rw [hrd] at hrcd
    simp at hrcd
  · exact Or.inr (Or.inl hru₁)
  · have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using K.inside.2.1
    have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
      hbcd.le (by simp) (Or.inl hbcd)
    rw [hru₂] at hrcd
    linarith
  · rw [hru₃, turn_eq_zero_of_between K.skeleton.hu₃] at hrcd
    linarith
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₁
    rw [hrv₁] at hrOuterStrict
    linarith [hrOuterStrict.2.1, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₂
    rw [hrv₂] at hrOuterStrict
    rw [turn_swap_first] at hz0
    linarith [hrOuterStrict.2.2, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₃
    rw [hrv₃] at hrOuterStrict
    linarith [hrOuterStrict.1, hz0]
  · linarith [hr₁.2.1]
  · exact Or.inr (Or.inr (K.mem_I₂.mpr hr₂))
  · exact Or.inl (K.mem_I₃.mpr hr₃)

/-- The positive-half analogue: the portal into cell one is `u₂`. -/
theorem portal_three_to_one
    {z y r : P} (hz : z ∈ K.I₃)
    (hzpos : 0 < turn (c : Point) (d : Point) (z : Point))
    (hy : (y : Point) ∈ triangleHull (b : Point) (c : Point) (d : Point))
    (hr : (r : Point) ∈ openSegment ℝ (z : Point) (y : Point)) :
    r ∈ K.I₃ ∨ r = K.skeleton.u₂ ∨ r ∈ K.I₁ := by
  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle K.inside
  have hzOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (z : Point) := strict_cell_strict_outer K.inside (Or.inr (Or.inr (K.mem_I₃.mp hz)))
  have hyOuter : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    cell_one_hull_subset_outer K.inside hy
  have hrOuterStrict := strict_outer_of_between_strict_hull habc hzOuter hyOuter hr
  have hycd : 0 ≤ turn (c : Point) (d : Point) (y : Point) :=
    (triangle_edge_nonneg K.inside.2.1.le hy).2.1
  have hrcd : 0 < turn (c : Point) (d : Point) (r : Point) :=
    turn_pos_of_between_nonneg hr hzpos hycd
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuterStrict
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.2
      (congrArg Subtype.val hrc)).elim
  · rw [hrd] at hrcd
    simp at hrcd
  · have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
      have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
        rw [(turn_rotate (d : Point) (c : Point) (a : Point)).symm]
        exact K.inside.2.2
      rw [turn_swap_first] at h
      linarith
    have hu₁neg := turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    rw [hru₁] at hrcd
    linarith
  · exact Or.inr (Or.inl hru₂)
  · rw [hru₃, turn_eq_zero_of_between K.skeleton.hu₃] at hrcd
    linarith
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₁
    rw [hrv₁] at hrOuterStrict
    linarith [hrOuterStrict.2.1, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₂
    rw [hrv₂] at hrOuterStrict
    rw [turn_swap_first] at hz0
    linarith [hrOuterStrict.2.2, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₃
    rw [hrv₃] at hrOuterStrict
    linarith [hrOuterStrict.1, hz0]
  · exact Or.inr (Or.inr (K.mem_I₁.mpr hr₁))
  · have hdc := hr₂.2.2
    rw [turn_swap_first] at hdc
    linarith
  · exact Or.inl (K.mem_I₃.mpr hr₃)

/-- A strict point of cell one is not on the opposite red spoke `ad`. -/
theorem turn_ad_ne_zero_of_mem_I₁ {p : P} (hp : p ∈ K.I₁) :
    turn (a : Point) (d : Point) (p : Point) ≠ 0 := by
  intro hz
  rcases point_eq_of_on_full_line K.hfour K.had K.skeleton.hu₁ hz with h | h | h
  · have hout := strict_cell_strict_outer K.inside (Or.inl (K.mem_I₁.mp hp))
    exact (strictlyInsideTriangle_ne_vertices hout).1 (congrArg Subtype.val h)
  · exact (strictlyInsideTriangle_ne_vertices (K.mem_I₁.mp hp)).2.2
      (congrArg Subtype.val h)
  · exact (K.cellPoint_ne_skeleton (Or.inl hp) 0 h).elim

/-- Portal localization from the `b`-half of cell one into cell three. -/
theorem portal_one_to_three
    {z y r : P} (hz : z ∈ K.I₁)
    (hzneg : turn (a : Point) (d : Point) (z : Point) < 0)
    (hy : (y : Point) ∈ triangleHull (a : Point) (b : Point) (d : Point))
    (hr : (r : Point) ∈ openSegment ℝ (z : Point) (y : Point)) :
    r ∈ K.I₁ ∨ r = K.skeleton.u₂ ∨ r ∈ K.I₃ := by
  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle K.inside
  have hzOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (z : Point) := strict_cell_strict_outer K.inside (Or.inl (K.mem_I₁.mp hz))
  have hyOuter : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    cell_three_hull_subset_outer K.inside hy
  have hrOuterStrict := strict_outer_of_between_strict_hull habc hzOuter hyOuter hr
  have hyad : turn (a : Point) (d : Point) (y : Point) ≤ 0 := by
    have hda := (triangle_edge_nonneg K.inside.1.le hy).2.2
    rw [turn_swap_first] at hda
    linarith
  have hrad : turn (a : Point) (d : Point) (r : Point) < 0 :=
    turn_neg_of_between_nonpos hr hzneg hyad
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuterStrict
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.2
      (congrArg Subtype.val hrc)).elim
  · rw [hrd] at hrad; simp at hrad
  · rw [hru₁, turn_eq_zero_of_between K.skeleton.hu₁] at hrad
    linarith
  · exact Or.inr (Or.inl hru₂)
  · have hadc : 0 < turn (a : Point) (d : Point) (c : Point) := by
      simpa only [← turn_rotate] using K.inside.2.2
    have hu₃pos := turn_pos_of_between_nonneg K.skeleton.hu₃ hadc (by simp)
    rw [hru₃] at hrad
    linarith
  · rw [hrv₁] at hrOuterStrict
    linarith [hrOuterStrict.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
  · rw [hrv₂] at hrOuterStrict
    have hz0 := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz0
    linarith [hrOuterStrict.2.2, hz0]
  · rw [hrv₃] at hrOuterStrict
    linarith [hrOuterStrict.1, turn_eq_zero_of_between K.skeleton.hv₃]
  · exact Or.inl (K.mem_I₁.mpr hr₁)
  · linarith [hr₂.2.1]
  · exact Or.inr (Or.inr (K.mem_I₃.mpr hr₃))

/-- Portal localization from the `c`-half of cell one into cell two. -/
theorem portal_one_to_two
    {z y r : P} (hz : z ∈ K.I₁)
    (hzpos : 0 < turn (a : Point) (d : Point) (z : Point))
    (hy : (y : Point) ∈ triangleHull (c : Point) (a : Point) (d : Point))
    (hr : (r : Point) ∈ openSegment ℝ (z : Point) (y : Point)) :
    r ∈ K.I₁ ∨ r = K.skeleton.u₃ ∨ r ∈ K.I₂ := by
  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle K.inside
  have hzOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (z : Point) := strict_cell_strict_outer K.inside (Or.inl (K.mem_I₁.mp hz))
  have hyOuter : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    cell_two_hull_subset_outer K.inside hy
  have hrOuterStrict := strict_outer_of_between_strict_hull habc hzOuter hyOuter hr
  have hyad : 0 ≤ turn (a : Point) (d : Point) (y : Point) :=
    (triangle_edge_nonneg K.inside.2.2.le hy).2.1
  have hrad : 0 < turn (a : Point) (d : Point) (r : Point) :=
    turn_pos_of_between_nonneg hr hzpos hyad
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuterStrict
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.2
      (congrArg Subtype.val hrc)).elim
  · rw [hrd] at hrad; simp at hrad
  · rw [hru₁, turn_eq_zero_of_between K.skeleton.hu₁] at hrad
    linarith
  · have hadb : turn (a : Point) (d : Point) (b : Point) < 0 := by
      rw [turn_swap_last]
      linarith [K.inside.1]
    have hu₂neg := turn_neg_of_between_nonpos K.skeleton.hu₂ hadb (by simp)
    rw [hru₂] at hrad
    linarith
  · exact Or.inr (Or.inl hru₃)
  · rw [hrv₁] at hrOuterStrict
    linarith [hrOuterStrict.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
  · rw [hrv₂] at hrOuterStrict
    have hz0 := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz0
    linarith [hrOuterStrict.2.2, hz0]
  · rw [hrv₃] at hrOuterStrict
    linarith [hrOuterStrict.1, turn_eq_zero_of_between K.skeleton.hv₃]
  · exact Or.inl (K.mem_I₁.mpr hr₁)
  · exact Or.inr (Or.inr (K.mem_I₂.mpr hr₂))
  · have hda := hr₃.2.2
    rw [turn_swap_first] at hda
    linarith

/-- A chord from the outer blocker `v₃` to `v₁` crosses from cell three
to cell one only through the spoke blocker `u₂`. -/
theorem portal_v₃_v₁
    (hv₃pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₃ : Point))
    {r : P}
    (hr : (r : Point) ∈ openSegment ℝ
      (K.skeleton.v₁ : Point) (K.skeleton.v₃ : Point)) :
    r ∈ K.I₃ ∨ r = K.skeleton.u₂ ∨ r ∈ K.I₁ := by
  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  have hrOuterStrict := strictlyInside_between_adjacent_sides habc
    K.skeleton.hv₃ K.skeleton.hv₁
    (by simpa only [openSegment_symm] using hr)
  have hbpos : 0 < turn (c : Point) (d : Point) (b : Point) := by
    simpa only [turn_rotate] using K.inside.2.1
  have hv₁pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₁ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hv₁ hbpos.le (by simp)
      (Or.inl hbpos)
  have hrpos := edgeTurn_pos_of_mem_openSegment hr hv₁pos.le hv₃pos.le
    (Or.inl hv₁pos)
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuterStrict
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.2
      (congrArg Subtype.val hrc)).elim
  · rw [hrd] at hrpos
    simp at hrpos
  · have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
      have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
        rw [(turn_rotate (d : Point) (c : Point) (a : Point)).symm]
        exact K.inside.2.2
      rw [turn_swap_first] at h
      linarith
    have hu₁neg := turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    rw [hru₁] at hrpos
    linarith
  · exact Or.inr (Or.inl hru₂)
  · rw [hru₃, turn_eq_zero_of_between K.skeleton.hu₃] at hrpos
    linarith
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₁
    rw [hrv₁] at hrOuterStrict
    linarith [hrOuterStrict.2.1, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz0
    rw [hrv₂] at hrOuterStrict
    linarith [hrOuterStrict.2.2, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₃
    rw [hrv₃] at hrOuterStrict
    linarith [hrOuterStrict.1, hz0]
  · exact Or.inr (Or.inr (K.mem_I₁.mpr hr₁))
  · have hdc := hr₂.2.2
    rw [turn_swap_first] at hdc
    linarith
  · exact Or.inl (K.mem_I₃.mpr hr₃)

/-- Reflected boundary chord localization through the portal `u₁`. -/
theorem portal_v₂_v₃
    (hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0)
    {r : P}
    (hr : (r : Point) ∈ openSegment ℝ
      (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point)) :
    r ∈ K.I₃ ∨ r = K.skeleton.u₁ ∨ r ∈ K.I₂ := by
  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  have hcab : 0 < turn (c : Point) (a : Point) (b : Point) := by
    rw [turn_rotate, turn_rotate]
    exact habc
  have hrRot := strictlyInside_between_adjacent_sides hcab
    (by simpa only [openSegment_symm] using K.skeleton.hv₂)
    K.skeleton.hv₃ hr
  have hrOuterStrict : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (r : Point) := ⟨hrRot.2.1, hrRot.2.2, hrRot.1⟩
  have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
    have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
      rw [(turn_rotate (d : Point) (c : Point) (a : Point)).symm]
      exact K.inside.2.2
    rw [turn_swap_first] at h
    linarith
  have hv₂neg := turn_neg_of_between_nonpos K.skeleton.hv₂ hacd (by simp)
  have hrneg : turn (c : Point) (d : Point) (r : Point) < 0 :=
    turn_neg_of_between_nonpos hr hv₂neg hv₃neg.le
  have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuterStrict
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton r hrHull with
      hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
      hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).1
      (congrArg Subtype.val hra)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.1
      (congrArg Subtype.val hrb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hrOuterStrict).2.2
      (congrArg Subtype.val hrc)).elim
  · rw [hrd] at hrneg
    simp at hrneg
  · exact Or.inr (Or.inl hru₁)
  · have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using K.inside.2.1
    have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
      hbcd.le (by simp) (Or.inl hbcd)
    rw [hru₂] at hrneg
    linarith
  · rw [hru₃, turn_eq_zero_of_between K.skeleton.hu₃] at hrneg
    linarith
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₁
    rw [hrv₁] at hrOuterStrict
    linarith [hrOuterStrict.2.1, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz0
    rw [hrv₂] at hrOuterStrict
    linarith [hrOuterStrict.2.2, hz0]
  · have hz0 := turn_eq_zero_of_between K.skeleton.hv₃
    rw [hrv₃] at hrOuterStrict
    linarith [hrOuterStrict.1, hz0]
  · linarith [hr₁.2.1]
  · exact Or.inr (Or.inr (K.mem_I₂.mpr hr₂))
  · exact Or.inl (K.mem_I₃.mpr hr₃)

/-- The secondary three-point line in a two-interior cell cannot supply a
blocker from its beam point to a fourth skeleton point. -/
theorem two_secondary_line_excludes
    {p q y : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hpy : p ≠ y) (hqy : q ≠ y)
    (hySide : ∀ l : Fin 3, y ≠ K.T₃.side l) :
    (q : Point) ∉ openSegment ℝ (p : Point) (y : Point) ∧
      (K.T₃.side k : Point) ∉ openSegment ℝ (p : Point) (y : Point) := by
  have hpSide : p ≠ K.T₃.side k :=
    K.cellPoint_ne_T₃_side (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) k
  have hqSide : q ≠ K.T₃.side k :=
    K.cellPoint_ne_T₃_side (Or.inr (Or.inr (K.mem_I₃.mpr H.hq))) k
  have hSideY : K.T₃.side k ≠ y := (hySide k).symm
  rcases H.secondary with hsec | hsec
  · constructor
    · intro hqyBetween
      have heq := other_endpoint_eq_of_common_blocker K.hfour hpSide hpy
        hsec.2 hqyBetween
      exact hSideY heq
    · intro hsBetween
      have hqyBetween := openSegment_left_nested hsec.2 hsBetween
      have heq := other_endpoint_eq_of_common_blocker K.hfour hpSide hpy
        hsec.2 hqyBetween
      exact hSideY heq
  · have hcross := first_pair_points_do_not_block_second K.hfour
      hqSide hpy H.hpq.symm hqy hpSide.symm hSideY hsec.2
    exact hcross

/-- In the positive half of cell three, neither of the two nonportal side
points of cell one can be blocked from the beam blocker of a two-interior
pattern. -/
theorem no_blocker_two_positive_nonportal
    {p q r y : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (hppos : 0 < turn (c : Point) (d : Point) (p : Point))
    (hyHull : (y : Point) ∈ triangleHull (b : Point) (c : Point) (d : Point))
    (hpy : p ≠ y) (hqy : q ≠ y)
    (hySide : ∀ l : Fin 3, y ≠ K.T₃.side l)
    (hr : (r : Point) ∈ openSegment ℝ (p : Point) (y : Point)) : False := by
  have hsec := K.two_secondary_line_excludes H hpy hqy hySide
  have hcases := K.portal_three_to_one (K.mem_I₃.mpr H.hp) hppos hyHull hr
  rcases hcases with hrI₃ | hru₂ | hrI₁
  · rcases hunique r hrI₃ with rfl | rfl
    · have heq := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hr
      exact hpy (Subtype.ext heq)
    · exact hsec.1 hr
  · have huBetween : (K.skeleton.u₂ : Point) ∈
        openSegment ℝ (p : Point) (y : Point) := by
      simpa [hru₂] using hr
    have hcross := first_pair_points_do_not_block_second K.hfour
      (K.T₃.side_injective'.ne H.hij) hpy
      (K.cellPoint_ne_T₃_side (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) i).symm
      (hySide i).symm
      (K.cellPoint_ne_T₃_side (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) j).symm
      (hySide j).symm H.beam_between
    have hportal := fin3_eq_one_of_three_local (1 : Fin 3) i j k
      H.hij H.hjk H.hki
    rcases hportal with hi | hj | hk
    · apply hcross.1
      simpa [← hi] using huBetween
    · apply hcross.2
      simpa [← hj] using huBetween
    · apply hsec.2
      simpa [← hk] using huBetween
  · rw [hempty₁] at hrI₁
    simp at hrI₁

/-- Negative-half counterpart of
`no_blocker_two_positive_nonportal`. -/
theorem no_blocker_two_negative_nonportal
    {p q r y : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₂ : K.I₂ = ∅)
    (hpneg : turn (c : Point) (d : Point) (p : Point) < 0)
    (hyHull : (y : Point) ∈ triangleHull (c : Point) (a : Point) (d : Point))
    (hpy : p ≠ y) (hqy : q ≠ y)
    (hySide : ∀ l : Fin 3, y ≠ K.T₃.side l)
    (hr : (r : Point) ∈ openSegment ℝ (p : Point) (y : Point)) : False := by
  have hsec := K.two_secondary_line_excludes H hpy hqy hySide
  have hcases := K.portal_three_to_two (K.mem_I₃.mpr H.hp) hpneg hyHull hr
  rcases hcases with hrI₃ | hru₁ | hrI₂
  · rcases hunique r hrI₃ with rfl | rfl
    · have heq := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hr
      exact hpy (Subtype.ext heq)
    · exact hsec.1 hr
  · have huBetween : (K.skeleton.u₁ : Point) ∈
        openSegment ℝ (p : Point) (y : Point) := by
      simpa [hru₁] using hr
    have hcross := first_pair_points_do_not_block_second K.hfour
      (K.T₃.side_injective'.ne H.hij) hpy
      (K.cellPoint_ne_T₃_side (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) i).symm
      (hySide i).symm
      (K.cellPoint_ne_T₃_side (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) j).symm
      (hySide j).symm H.beam_between
    have hportal := fin3_eq_one_of_three_local (2 : Fin 3) i j k
      H.hij H.hjk H.hki
    rcases hportal with hi | hj | hk
    · apply hcross.1
      simpa [← hi] using huBetween
    · apply hcross.2
      simpa [← hj] using huBetween
    · apply hsec.2
      simpa [← hk] using huBetween
  · rw [hempty₂] at hrI₂
    simp at hrI₂

/-- In the exceptional positive order `p-q-u₂`, neither `p` nor `u₂`
can block `q` from a nonportal point of the empty first cell. -/
theorem no_blocker_two_positive_exception_q
    {p q r y : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (hppos : 0 < turn (c : Point) (d : Point) (p : Point))
    (hqBetween : (q : Point) ∈ openSegment ℝ
      (p : Point) (K.skeleton.u₂ : Point))
    (hyHull : (y : Point) ∈ triangleHull (b : Point) (c : Point) (d : Point))
    (hpy : p ≠ y) (hqy : q ≠ y) (hu₂y : K.skeleton.u₂ ≠ y)
    (hr : (r : Point) ∈ openSegment ℝ (q : Point) (y : Point)) : False := by
  have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
    simpa only [turn_rotate] using K.inside.2.1
  have hu₂pos : 0 < turn (c : Point) (d : Point) (K.skeleton.u₂ : Point) :=
    edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hbcd.le (by simp)
      (Or.inl hbcd)
  have hqpos := turn_pos_of_between_nonneg hqBetween hppos hu₂pos.le
  have hp_u₂ : p ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) 1
  have hq_u₂ : q ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr (K.mem_I₃.mpr H.hq))) 1
  have hcross := first_pair_points_do_not_block_second K.hfour
    hp_u₂ hqy H.hpq hpy hq_u₂.symm hu₂y hqBetween
  have hcases := K.portal_three_to_one (K.mem_I₃.mpr H.hq) hqpos hyHull hr
  rcases hcases with hrI₃ | hru₂ | hrI₁
  · rcases hunique r hrI₃ with rfl | rfl
    · exact hcross.1 hr
    · have heq := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hr
      exact hqy (Subtype.ext heq)
  · apply hcross.2
    simpa [hru₂] using hr
  · rw [hempty₁] at hrI₁
    simp at hrI₁

/-- Reflected exceptional order `p-q-u₁` in the negative half. -/
theorem no_blocker_two_negative_exception_q
    {p q r y : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₂ : K.I₂ = ∅)
    (hpneg : turn (c : Point) (d : Point) (p : Point) < 0)
    (hqBetween : (q : Point) ∈ openSegment ℝ
      (p : Point) (K.skeleton.u₁ : Point))
    (hyHull : (y : Point) ∈ triangleHull (c : Point) (a : Point) (d : Point))
    (hpy : p ≠ y) (hqy : q ≠ y) (hu₁y : K.skeleton.u₁ ≠ y)
    (hr : (r : Point) ∈ openSegment ℝ (q : Point) (y : Point)) : False := by
  have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
    have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
      rw [← turn_rotate]
      exact K.inside.2.2
    rw [turn_swap_first] at h
    linarith
  have hu₁neg := turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
  have hqneg := turn_neg_of_between_nonpos hqBetween hpneg hu₁neg.le
  have hp_u₁ : p ≠ K.skeleton.u₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr (K.mem_I₃.mpr H.hp))) 0
  have hq_u₁ : q ≠ K.skeleton.u₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr (K.mem_I₃.mpr H.hq))) 0
  have hcross := first_pair_points_do_not_block_second K.hfour
    hp_u₁ hqy H.hpq hpy hq_u₁.symm hu₁y hqBetween
  have hcases := K.portal_three_to_two (K.mem_I₃.mpr H.hq) hqneg hyHull hr
  rcases hcases with hrI₃ | hru₁ | hrI₂
  · rcases hunique r hrI₃ with rfl | rfl
    · exact hcross.1 hr
    · have heq := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hr
      exact hqy (Subtype.ext heq)
  · apply hcross.2
    simpa [hru₁] using hr
  · rw [hempty₂] at hrI₂
    simp at hrI₂

/-- A point of cell three lying on two saturated lines, one through the
positive portal `u₂`, cannot carry any of the three nonred colours when
cell one is empty. -/
theorem impossible_three_positive_full_lines
    {z x w e : P}
    (hz : z ∈ K.I₃) (hx : x ∈ K.I₃) (hw : w ∈ K.I₃)
    (hcover : ∀ r : P, r ∈ K.I₃ → r = z ∨ r = x ∨ r = w)
    (hempty₁ : K.I₁ = ∅)
    (hzpos : 0 < turn (c : Point) (d : Point) (z : Point))
    (hze : z ≠ e) (hwz : w ≠ z)
    (hxLine : (x : Point) ∈ openSegment ℝ (z : Point) (e : Point))
    (hzLine : (z : Point) ∈ openSegment ℝ
      (K.skeleton.u₂ : Point) (w : Point))
    (heSide : ∀ l : Fin 3, e ≠ K.T₁.side l) : False := by
  have hpair := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  obtain ⟨l, hcolour⟩ := colour_eq_some_side K.T₁ hpair z
    (K.interior_colour_ne_red₃ z (K.mem_I₃.mp hz))
  have hzy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hz)) l
  have hwy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hw)) l
  have hu₂w := K.cellPoint_ne_skeleton (Or.inr (Or.inr hw)) 1 |>.symm
  have hu₂z := K.cellPoint_ne_skeleton (Or.inr (Or.inr hz)) 1 |>.symm
  obtain ⟨r, hr⟩ := K.proper z (K.T₁.side l) hzy hcolour
  have hexclude := three_line_candidates_exclude K.hfour hze hzy
    (heSide l) hu₂w hu₂z hwz hwy hxLine hzLine
  have hcases := K.portal_three_to_one hz hzpos
    (K.T₁.nonredPoint_mem_hull (by
      simpa only [K.T₁.coe_sideLocal] using (K.T₁.sideLocal l).property)) hr
  rcases hcases with hrI₃ | hru₂ | hrI₁
  · rcases hcover r hrI₃ with rfl | rfl | rfl
    · exact hexclude.1 hr
    · exact hexclude.2.1 hr
    · exact hexclude.2.2.1 hr
  · apply hexclude.2.2.2
    simpa [hru₂] using hr
  · rw [hempty₁] at hrI₁
    simp at hrI₁

/-- Negative-portal counterpart of
`impossible_three_positive_full_lines`. -/
theorem impossible_three_negative_full_lines
    {z x w e : P}
    (hz : z ∈ K.I₃) (hx : x ∈ K.I₃) (hw : w ∈ K.I₃)
    (hcover : ∀ r : P, r ∈ K.I₃ → r = z ∨ r = x ∨ r = w)
    (hempty₂ : K.I₂ = ∅)
    (hzneg : turn (c : Point) (d : Point) (z : Point) < 0)
    (hze : z ≠ e) (hwz : w ≠ z)
    (hxLine : (x : Point) ∈ openSegment ℝ (z : Point) (e : Point))
    (hzLine : (z : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (w : Point))
    (heSide : ∀ l : Fin 3, e ≠ K.T₂.side l) : False := by
  have hpair := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [hempty₂]))
  obtain ⟨l, hcolour⟩ := colour_eq_some_side K.T₂ hpair z
    (K.interior_colour_ne_red₃ z (K.mem_I₃.mp hz))
  have hzy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hz)) l
  have hwy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hw)) l
  have hu₁w := K.cellPoint_ne_skeleton (Or.inr (Or.inr hw)) 0 |>.symm
  have hu₁z := K.cellPoint_ne_skeleton (Or.inr (Or.inr hz)) 0 |>.symm
  obtain ⟨r, hr⟩ := K.proper z (K.T₂.side l) hzy hcolour
  have hexclude := three_line_candidates_exclude K.hfour hze hzy
    (heSide l) hu₁w hu₁z hwz hwy hxLine hzLine
  have hcases := K.portal_three_to_two hz hzneg
    (K.T₂.nonredPoint_mem_hull (by
      simpa only [K.T₂.coe_sideLocal] using (K.T₂.sideLocal l).property)) hr
  rcases hcases with hrI₃ | hru₁ | hrI₂
  · rcases hcover r hrI₃ with rfl | rfl | rfl
    · exact hexclude.1 hr
    · exact hexclude.2.1 hr
    · exact hexclude.2.2.1 hr
  · apply hexclude.2.2.2
    simpa [hru₁] using hr
  · rw [hempty₂] at hrI₂
    simp at hrI₂

theorem impossible_two_pattern_positive
    {p q : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (hppos : 0 < turn (c : Point) (d : Point) (p : Point)) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H.hq
  obtain ⟨l, hcolour⟩ := colour_eq_some_side K.T₁ hpair₁ p
    (K.interior_colour_ne_red₃ p H.hp)
  fin_cases l
  · have hpy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hpI)) 0
    have hqy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hqI)) 0
    obtain ⟨r, hr⟩ := K.proper p (K.T₁.side 0) hpy hcolour
    apply K.no_blocker_two_positive_nonportal H hunique hempty₁ hppos
      (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 0).property)
      hpy hqy
    · intro m
      fin_cases m
      · simpa using K.skeleton_ne 3 5 (by decide)
      · simpa using K.skeleton_ne 3 1 (by decide)
      · simpa using K.skeleton_ne 3 0 (by decide)
    · exact hr
  · have hpy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hpI)) 1
    have hqy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hqI)) 1
    obtain ⟨r, hr⟩ := K.proper p (K.T₁.side 1) hpy hcolour
    apply K.no_blocker_two_positive_nonportal H hunique hempty₁ hppos
      (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property)
      hpy hqy
    · intro m
      fin_cases m
      · simpa using K.skeleton_ne 2 5 (by decide)
      · simpa using K.skeleton_ne 2 1 (by decide)
      · simpa using K.skeleton_ne 2 0 (by decide)
    · exact hr
  · have hpneJ : colour p ≠ colour (K.T₃.side j) := by
      intro h
      exact H.p_colour_ne_beam (h.trans H.beam_colour.symm)
    have hportal := fin3_eq_one_of_three_local (1 : Fin 3) i j k
      H.hij H.hjk H.hki
    rcases hportal with hi | hj | hk
    · apply H.p_colour_ne_beam
      simpa [← hi] using hcolour
    · apply hpneJ
      simpa [← hj] using hcolour
    · rcases H.secondary with hsec | hsec
      · have hqBetween : (q : Point) ∈ openSegment ℝ
            (p : Point) (K.skeleton.u₂ : Point) := by
          simpa [← hk] using hsec.2
        obtain ⟨m, hqColour⟩ := colour_eq_some_side K.T₁ hpair₁ q
          (K.interior_colour_ne_red₃ q H.hq)
        fin_cases m
        · have hpy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hpI)) 0
          have hqy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hqI)) 0
          obtain ⟨r, hr⟩ := K.proper q (K.T₁.side 0) hqy hqColour
          apply K.no_blocker_two_positive_exception_q H hunique hempty₁
            hppos hqBetween
            (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 0).property)
            hpy hqy
          · simpa using K.skeleton_ne 1 3 (by decide)
          · exact hr
        · have hpy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hpI)) 1
          have hqy := K.cellPoint_ne_T₁_side (Or.inr (Or.inr hqI)) 1
          obtain ⟨r, hr⟩ := K.proper q (K.T₁.side 1) hqy hqColour
          apply K.no_blocker_two_positive_exception_q H hunique hempty₁
            hppos hqBetween
            (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property)
            hpy hqy
          · simpa using K.skeleton_ne 1 2 (by decide)
          · exact hr
        · apply H.interior_colour_ne
          calc
            colour p = colour (K.T₃.side k) := hsec.1
            _ = colour K.skeleton.u₂ := by
              rw [← hk]
              simp only [K.T₃_side_one]
            _ = colour (K.T₁.side 2) := by
              simp only [K.T₁_side_two]
            _ = colour q := hqColour.symm
      · apply H.interior_colour_ne
        calc
          colour p = colour (K.T₁.side 2) := hcolour
          _ = colour K.skeleton.u₂ := by
            simp only [K.T₁_side_two]
          _ = colour (K.T₃.side k) := by
            rw [← hk]
            simp only [K.T₃_side_one]
          _ = colour q := hsec.1.symm

theorem impossible_two_pattern_negative
    {p q : P} {i j k : Fin 3}
    (H : TwoInteriorPatternAt colour (colour a) K.T₃ p q i j k)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₂ : K.I₂ = ∅)
    (hpneg : turn (c : Point) (d : Point) (p : Point) < 0) : False := by
  have hpair₂ := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [hempty₂]))
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H.hq
  obtain ⟨l, hcolour⟩ := colour_eq_some_side K.T₂ hpair₂ p
    (K.interior_colour_ne_red₃ p H.hp)
  fin_cases l
  · have hpy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hpI)) 0
    have hqy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hqI)) 0
    obtain ⟨r, hr⟩ := K.proper p (K.T₂.side 0) hpy hcolour
    apply K.no_blocker_two_negative_nonportal H hunique hempty₂ hpneg
      (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property)
      hpy hqy
    · intro m
      fin_cases m
      · simpa using K.skeleton_ne 4 5 (by decide)
      · simpa using K.skeleton_ne 4 1 (by decide)
      · simpa using K.skeleton_ne 4 0 (by decide)
    · exact hr
  · have hpneJ : colour p ≠ colour (K.T₃.side j) := by
      intro h
      exact H.p_colour_ne_beam (h.trans H.beam_colour.symm)
    have hportal := fin3_eq_one_of_three_local (2 : Fin 3) i j k
      H.hij H.hjk H.hki
    rcases hportal with hi | hj | hk
    · apply H.p_colour_ne_beam
      simpa [← hi] using hcolour
    · apply hpneJ
      simpa [← hj] using hcolour
    · rcases H.secondary with hsec | hsec
      · have hqBetween : (q : Point) ∈ openSegment ℝ
            (p : Point) (K.skeleton.u₁ : Point) := by
          simpa [← hk] using hsec.2
        obtain ⟨m, hqColour⟩ := colour_eq_some_side K.T₂ hpair₂ q
          (K.interior_colour_ne_red₃ q H.hq)
        fin_cases m
        · have hpy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hpI)) 0
          have hqy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hqI)) 0
          obtain ⟨r, hr⟩ := K.proper q (K.T₂.side 0) hqy hqColour
          apply K.no_blocker_two_negative_exception_q H hunique hempty₂
            hpneg hqBetween
            (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property)
            hpy hqy
          · simpa using K.skeleton_ne 0 4 (by decide)
          · exact hr
        · apply H.interior_colour_ne
          calc
            colour p = colour (K.T₃.side k) := hsec.1
            _ = colour K.skeleton.u₁ := by
              rw [← hk]
              simp only [K.T₃_side_two]
            _ = colour (K.T₂.side 1) := by
              simp only [K.T₂_side_one]
            _ = colour q := hqColour.symm
        · have hpy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hpI)) 2
          have hqy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hqI)) 2
          obtain ⟨r, hr⟩ := K.proper q (K.T₂.side 2) hqy hqColour
          apply K.no_blocker_two_negative_exception_q H hunique hempty₂
            hpneg hqBetween
            (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property)
            hpy hqy
          · simpa using K.skeleton_ne 0 2 (by decide)
          · exact hr
      · apply H.interior_colour_ne
        calc
          colour p = colour (K.T₂.side 1) := hcolour
          _ = colour K.skeleton.u₁ := by
            simp only [K.T₂_side_one]
          _ = colour (K.T₃.side k) := by
            rw [← hk]
            simp only [K.T₃_side_two]
          _ = colour q := hsec.1.symm
  · have hpy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hpI)) 2
    have hqy := K.cellPoint_ne_T₂_side (Or.inr (Or.inr hqI)) 2
    obtain ⟨r, hr⟩ := K.proper p (K.T₂.side 2) hpy hcolour
    apply K.no_blocker_two_negative_nonportal H hunique hempty₂ hpneg
      (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property)
      hpy hqy
    · intro m
      fin_cases m
      · simpa using K.skeleton_ne 2 5 (by decide)
      · simpa using K.skeleton_ne 2 1 (by decide)
      · simpa using K.skeleton_ne 2 0 (by decide)
    · exact hr

/-- If the negative half of cell three has a unique point on a full beam
through the portal `u₁`, that point cannot be coloured at all: it sees the
rainbow side triple of the empty second cell. -/
theorem impossible_negative_portal_beam
    {p e : P} (hp : p ∈ K.I₃)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty : K.I₂ = ∅)
    (hpneg : turn (c : Point) (d : Point) (p : Point) < 0)
    (hbeam : (p : Point) ∈
      openSegment ℝ (e : Point) (K.skeleton.u₁ : Point))
    (hpe : p ≠ e) (heu₁ : e ≠ K.skeleton.u₁)
    (heSide : ∀ i : Fin 3, e ≠ K.T₂.side i) : False := by
  have hsidePair := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [hempty]))
  obtain ⟨i, hpiColour⟩ := colour_eq_some_side K.T₂ hsidePair p
    (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
  have hpSide : p ≠ K.T₂.side i :=
    K.cellPoint_ne_T₂_side (Or.inr (Or.inr hp)) i
  obtain ⟨r, hr⟩ := K.proper p (K.T₂.side i) hpSide hpiColour
  have hyHull := K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal i).property
  have hcases := K.portal_three_to_two hp hpneg
    (by simpa only [K.T₂.coe_sideLocal] using hyHull) hr
  rcases hcases with hrI₃ | hru₁ | hrI₂
  · have hrp := hunique r hrI₃
    have heq : (p : Point) = (K.T₂.side i : Point) := by
      apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
      simpa [hrp] using hr
    exact hpSide (Subtype.ext heq)
  · have huBetween : (K.skeleton.u₁ : Point) ∈
        openSegment ℝ (p : Point) (K.T₂.side i : Point) := by
      simpa [hru₁] using hr
    fin_cases i
    · have hcross := first_pair_points_do_not_block_second K.hfour
        heu₁ (by simpa using hpSide)
        hpe.symm (heSide 0)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
        (by simpa using K.skeleton_ne 0 4 (by decide)) hbeam
      exact (hcross.2 (by simpa using huBetween)).elim
    · have heq := (right_mem_openSegment_iff (𝕜 := ℝ)).mp huBetween
      exact hpSide (Subtype.ext (by simpa using heq))
    · have hcross := first_pair_points_do_not_block_second K.hfour
        heu₁ (by simpa using hpSide)
        hpe.symm (heSide 2)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
        (by simpa using K.skeleton_ne 0 2 (by decide)) hbeam
      exact (hcross.2 (by simpa using huBetween)).elim
  · rw [hempty] at hrI₂
    simp at hrI₂

/-- Positive-half counterpart of `impossible_negative_portal_beam`. -/
theorem impossible_positive_portal_beam
    {p e : P} (hp : p ∈ K.I₃)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty : K.I₁ = ∅)
    (hppos : 0 < turn (c : Point) (d : Point) (p : Point))
    (hbeam : (p : Point) ∈
      openSegment ℝ (e : Point) (K.skeleton.u₂ : Point))
    (hpe : p ≠ e) (heu₂ : e ≠ K.skeleton.u₂)
    (heSide : ∀ i : Fin 3, e ≠ K.T₁.side i) : False := by
  have hsidePair := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty]))
  obtain ⟨i, hpiColour⟩ := colour_eq_some_side K.T₁ hsidePair p
    (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
  have hpSide : p ≠ K.T₁.side i :=
    K.cellPoint_ne_T₁_side (Or.inr (Or.inr hp)) i
  obtain ⟨r, hr⟩ := K.proper p (K.T₁.side i) hpSide hpiColour
  have hyHull := K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal i).property
  have hcases := K.portal_three_to_one hp hppos
    (by simpa only [K.T₁.coe_sideLocal] using hyHull) hr
  rcases hcases with hrI₃ | hru₂ | hrI₁
  · have hrp := hunique r hrI₃
    have heq : (p : Point) = (K.T₁.side i : Point) := by
      apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
      simpa [hrp] using hr
    exact hpSide (Subtype.ext heq)
  · have huBetween : (K.skeleton.u₂ : Point) ∈
        openSegment ℝ (p : Point) (K.T₁.side i : Point) := by
      simpa [hru₂] using hr
    fin_cases i
    · have hcross := first_pair_points_do_not_block_second K.hfour
        heu₂ (by simpa using hpSide)
        hpe.symm (heSide 0)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
        (by simpa using K.skeleton_ne 1 3 (by decide)) hbeam
      exact (hcross.2 (by simpa using huBetween)).elim
    · have hcross := first_pair_points_do_not_block_second K.hfour
        heu₂ (by simpa using hpSide)
        hpe.symm (heSide 1)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
        (by simpa using K.skeleton_ne 1 2 (by decide)) hbeam
      exact (hcross.2 (by simpa using huBetween)).elim
    · have heq := (right_mem_openSegment_iff (𝕜 := ℝ)).mp huBetween
      exact hpSide (Subtype.ext (by simpa using heq))
  · rw [hempty] at hrI₁
    simp at hrI₁

theorem impossible_one_in_three_central_beam
    {p : P} (hp : p ∈ K.I₃)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅) (hempty₂ : K.I₂ = ∅)
    (H : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  have hne := K.turn_cd_ne_zero_of_mem_I₃ hp
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · apply K.impossible_negative_portal_beam hp hunique hempty₂ hneg
      (by simpa using H.beam_between)
    · simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1
    · simpa using K.skeleton_ne 1 0 (by decide)
    · intro i
      fin_cases i
      · simpa using K.skeleton_ne 1 4 (by decide)
      · simpa using K.skeleton_ne 1 0 (by decide)
      · simpa using K.skeleton_ne 1 2 (by decide)
  · apply K.impossible_positive_portal_beam hp hunique hempty₁ hpos
      (by simpa only [K.T₃_side_one, K.T₃_side_two, openSegment_symm]
        using H.beam_between)
    · simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0
    · simpa using K.skeleton_ne 0 1 (by decide)
    · intro i
      fin_cases i
      · simpa using K.skeleton_ne 0 3 (by decide)
      · simpa using K.skeleton_ne 0 2 (by decide)
      · simpa using K.skeleton_ne 0 1 (by decide)

theorem impossible_one_in_three_u₁_v₃_exception
    {p : P} (hp : p ∈ K.I₃)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅) (hempty₂ : K.I₂ = ∅)
    (hppos : 0 < turn (c : Point) (d : Point) (p : Point))
    (H : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hpair₂ := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [hempty₂]))
  have hv₃u₂ : colour K.skeleton.v₃ ≠ colour K.skeleton.u₂ := by
    intro h
    exact H.remaining_colour_ne (h.symm.trans H.beam_colour.symm)
  have hu₂p : colour K.skeleton.u₂ ≠ colour p :=
    (H.p_colour_ne 1).symm
  have hpv₃ : colour p ≠ colour K.skeleton.v₃ := H.p_colour_ne 0
  have hu₃p : colour K.skeleton.u₃ = colour p := by
    have hexhaust := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 5)
      (K.skeleton.blocker_colour_ne 1)
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      hv₃u₂ hu₂p hpv₃
    rcases hexhaust with h | h | h
    · exact (hpair₂ (i := 1) (j := 2) (by decide)
        (by simpa using H.beam_colour.trans h.symm)).elim
    · exact (hpair₁ (i := 1) (j := 2) (by decide)
        (by simpa using h)).elim
    · exact h
  have hv₁v₃ : colour K.skeleton.v₁ = colour K.skeleton.v₃ := by
    have hexhaust := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 3)
      (K.skeleton.blocker_colour_ne 5)
      (K.skeleton.blocker_colour_ne 1)
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      hv₃u₂ hu₂p hpv₃
    rcases hexhaust with h | h | h
    · exact h
    · exact (hpair₁ (i := 0) (j := 2) (by decide)
        (by simpa using h)).elim
    · exact (hpair₁ (i := 0) (j := 1) (by decide)
        (by simpa using h.trans hu₃p.symm)).elim
  have hp_u₃_ne : p ≠ K.skeleton.u₃ := by
    simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
  obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃_ne hu₃p.symm
  have hrCases := K.portal_three_to_one hp hppos
    (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property) hr
  have hru₂ : r = K.skeleton.u₂ := by
    rcases hrCases with hrI₃ | h | hrI₁
    · have hrp := hunique r hrI₃
      have heq : (p : Point) = (K.skeleton.u₃ : Point) := by
        apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
        simpa [hrp] using hr
      exact (hp_u₃_ne (Subtype.ext heq)).elim
    · exact h
    · rw [hempty₁] at hrI₁
      simp at hrI₁
  have hu₂Interior : (K.skeleton.u₂ : Point) ∈
      openSegment ℝ (p : Point) (K.skeleton.u₃ : Point) := by
    simpa [hru₂] using hr
  have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
    have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
      have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
        rw [(turn_rotate (d : Point) (c : Point) (a : Point)).symm]
        exact K.inside.2.2
      rw [turn_swap_first] at h
      linarith
    exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
  have hv₃pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) := by
    by_contra hn
    have hle : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) ≤ 0 :=
      le_of_not_gt hn
    have hpneg := turn_neg_of_between_nonpos
      (by simpa using H.beam_between) hu₁neg hle
    linarith
  have hv₁_v₃_ne : K.skeleton.v₁ ≠ K.skeleton.v₃ := by
    simpa using K.skeleton_ne 3 5 (by decide)
  obtain ⟨s, hs⟩ := K.proper K.skeleton.v₁ K.skeleton.v₃ hv₁_v₃_ne hv₁v₃
  have hsCases := K.portal_v₃_v₁ hv₃pos hs
  have hsu₂ : s = K.skeleton.u₂ := by
    rcases hsCases with hsI₃ | h | hsI₁
    · have hsp := hunique s hsI₃
      have hpOn : (p : Point) ∈ openSegment ℝ
          (K.skeleton.v₁ : Point) (K.skeleton.v₃ : Point) := by
        simpa [hsp] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (by simpa using K.skeleton_ne 5 0 (by decide))
        (by simpa using K.skeleton_ne 5 3 (by decide))
        (by simpa only [K.T₃_side_two, K.T₃_side_zero, openSegment_symm]
          using H.beam_between)
        (by simpa only [openSegment_symm] using hpOn)
      exact (K.skeleton_ne 0 3 (by decide) heq).elim
    · exact h
    · rw [hempty₁] at hsI₁
      simp at hsI₁
  exact K.u₂_cannot_block_both_exceptional_pairs
    (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H.beam_between)
    (by simpa [hsu₂] using hs) hu₂Interior

theorem impossible_one_in_three_v₃_u₂_exception
    {p : P} (hp : p ∈ K.I₃)
    (hunique : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅) (hempty₂ : K.I₂ = ∅)
    (hpneg : turn (c : Point) (d : Point) (p : Point) < 0)
    (H : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hpair₂ := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [hempty₂]))
  have hv₃u₁ : colour K.skeleton.v₃ ≠ colour K.skeleton.u₁ :=
    H.remaining_colour_ne.symm
  have hu₁p : colour K.skeleton.u₁ ≠ colour p :=
    (H.p_colour_ne 2).symm
  have hpv₃ : colour p ≠ colour K.skeleton.v₃ := H.p_colour_ne 0
  have hu₃p : colour K.skeleton.u₃ = colour p := by
    have hexhaust := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 5)
      (K.skeleton.blocker_colour_ne 0)
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      hv₃u₁ hu₁p hpv₃
    rcases hexhaust with h | h | h
    · exact (hpair₁ (i := 1) (j := 2) (by decide)
        (by simpa using h.trans H.beam_colour)).elim
    · exact (hpair₂ (i := 1) (j := 2) (by decide)
        (by simpa using h.symm)).elim
    · exact h
  have hv₂v₃ : colour K.skeleton.v₂ = colour K.skeleton.v₃ := by
    have hexhaust := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 4)
      (K.skeleton.blocker_colour_ne 5)
      (K.skeleton.blocker_colour_ne 0)
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      hv₃u₁ hu₁p hpv₃
    rcases hexhaust with h | h | h
    · exact h
    · exact (hpair₂ (i := 0) (j := 1) (by decide)
        (by simpa using h)).elim
    · exact (hpair₂ (i := 0) (j := 2) (by decide)
        (by simpa using h.trans hu₃p.symm)).elim
  have hp_u₃_ne : p ≠ K.skeleton.u₃ := by
    simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
  obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃_ne hu₃p.symm
  have hrCases := K.portal_three_to_two hp hpneg
    (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr
  have hru₁ : r = K.skeleton.u₁ := by
    rcases hrCases with hrI₃ | h | hrI₂
    · have hrp := hunique r hrI₃
      have heq : (p : Point) = (K.skeleton.u₃ : Point) := by
        apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
        simpa [hrp] using hr
      exact (hp_u₃_ne (Subtype.ext heq)).elim
    · exact h
    · rw [hempty₂] at hrI₂
      simp at hrI₂
  have hu₁Interior : (K.skeleton.u₁ : Point) ∈
      openSegment ℝ (p : Point) (K.skeleton.u₃ : Point) := by
    simpa [hru₁] using hr
  have hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0 := by
    have hbpos : 0 < turn (c : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using K.inside.2.1
    have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
      hbpos.le (by simp) (Or.inl hbpos)
    by_contra hn
    have hge : 0 ≤ turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) :=
      le_of_not_gt hn
    have hppos := edgeTurn_pos_of_mem_openSegment
      (by simpa using H.beam_between) hge hu₂pos.le (Or.inr hu₂pos)
    linarith
  have hv₂_v₃_ne : K.skeleton.v₂ ≠ K.skeleton.v₃ := by
    simpa using K.skeleton_ne 4 5 (by decide)
  obtain ⟨s, hs⟩ := K.proper K.skeleton.v₂ K.skeleton.v₃ hv₂_v₃_ne hv₂v₃
  have hsCases := K.portal_v₂_v₃ hv₃neg hs
  have hsu₁ : s = K.skeleton.u₁ := by
    rcases hsCases with hsI₃ | h | hsI₂
    · have hsp := hunique s hsI₃
      have hpOn : (p : Point) ∈ openSegment ℝ
          (K.skeleton.v₂ : Point) (K.skeleton.v₃ : Point) := by
        simpa [hsp] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (by simpa using K.skeleton_ne 5 1 (by decide))
        (by simpa using K.skeleton_ne 5 4 (by decide))
        (by simpa only [K.T₃_side_zero, K.T₃_side_one]
          using H.beam_between)
        (by simpa only [openSegment_symm] using hpOn)
      exact (K.skeleton_ne 1 4 (by decide) heq).elim
    · exact h
    · rw [hempty₂] at hsI₂
      simp at hsI₂
  exact K.u₁_cannot_block_both_exceptional_pairs
    (by simpa only [K.T₃_side_zero, K.T₃_side_one]
      using H.beam_between)
    (by simpa [hsu₁] using hs) hu₁Interior

/-- The corrected complete elimination of the `(0,0,1)` cell distribution.
The two noncentral beams use the exceptional crosscut arguments above on
the side where the older radial claim was too strong. -/
theorem impossible_only_I₃_one
    (h₁ : K.I₁.card = 0) (h₂ : K.I₂.card = 0)
    (h₃ : K.I₃.card = 1) : False := by
  have hempty₁ : K.I₁ = ∅ := Finset.card_eq_zero.mp h₁
  have hempty₂ : K.I₂ = ∅ := Finset.card_eq_zero.mp h₂
  obtain ⟨p, hpSet⟩ := Finset.card_eq_one.mp h₃
  have hp : p ∈ K.I₃ := by
    rw [hpSet]
    simp
  have hunique : ∀ z : P, z ∈ K.I₃ → z = p := by
    intro z hz
    rw [hpSet] at hz
    simpa using hz
  have hpattern := K.M₃.one_interior_pattern K.hfour
    (K.mem_I₃.mp hp) (fun z hz ↦ hunique z (K.mem_I₃.mpr hz))
  have hne := K.turn_cd_ne_zero_of_mem_I₃ hp
  rcases hpattern with H | H | H
  · rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact K.impossible_one_in_three_v₃_u₂_exception hp hunique
        hempty₁ hempty₂ hneg H
    · apply K.impossible_positive_portal_beam hp hunique hempty₁ hpos
        (by simpa only [K.T₃_side_zero, K.T₃_side_one]
          using H.beam_between)
      · simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 5
      · simpa using K.skeleton_ne 5 1 (by decide)
      · intro i
        fin_cases i
        · simpa using K.skeleton_ne 5 3 (by decide)
        · simpa using K.skeleton_ne 5 2 (by decide)
        · simpa using K.skeleton_ne 5 1 (by decide)
  · exact K.impossible_one_in_three_central_beam hp hunique
      hempty₁ hempty₂ H
  · rcases lt_or_gt_of_ne hne with hneg | hpos
    · apply K.impossible_negative_portal_beam (e := K.skeleton.v₃)
        hp hunique hempty₂ hneg
        (by
          rw [openSegment_symm]
          simpa only [K.T₃_side_two, K.T₃_side_zero] using H.beam_between)
      · simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 5
      · simpa using K.skeleton_ne 5 0 (by decide)
      · intro i
        fin_cases i
        · simpa using K.skeleton_ne 5 4 (by decide)
        · simpa using K.skeleton_ne 5 0 (by decide)
        · simpa using K.skeleton_ne 5 2 (by decide)
    · exact K.impossible_one_in_three_u₁_v₃_exception hp hunique
        hempty₁ hempty₂ hpos H

/-- Complete corrected elimination of the `(0,0,2)` distribution. -/
theorem impossible_only_I₃_two
    (h₁ : K.I₁.card = 0) (h₂ : K.I₂.card = 0)
    (h₃ : K.I₃.card = 2) : False := by
  have hempty₁ : K.I₁ = ∅ := Finset.card_eq_zero.mp h₁
  have hempty₂ : K.I₂ = ∅ := Finset.card_eq_zero.mp h₂
  obtain ⟨p, q, hpq, hpqSet⟩ := Finset.card_eq_two.mp h₃
  have hp : p ∈ K.I₃ := by
    rw [hpqSet]
    simp
  have hq : q ∈ K.I₃ := by
    rw [hpqSet]
    simp
  have hunique : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q := by
    intro z hz
    rw [hpqSet] at hz
    simpa using hz
  have hunique' : ∀ z : P, z ∈ K.I₃ → z = q ∨ z = p := by
    intro z hz
    exact (hunique z hz).symm
  have hpattern := K.M₃.two_interior_pattern K.hfour
    (K.mem_I₃.mp hp) (K.mem_I₃.mp hq) hpq
    (fun z hz ↦ hunique z (K.mem_I₃.mpr hz))
  have solve {x y : P} {i j k : Fin 3}
      (H : TwoInteriorPatternAt colour (colour a) K.T₃ x y i j k)
      (hu : ∀ z : P, z ∈ K.I₃ → z = x ∨ z = y) : False := by
    have hne := K.turn_cd_ne_zero_of_mem_I₃ (K.mem_I₃.mpr H.hp)
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact K.impossible_two_pattern_negative H hu hempty₂ hneg
    · exact K.impossible_two_pattern_positive H hu hempty₁ hpos
  rcases hpattern with (H | H) | (H | H) | (H | H)
  · exact solve H hunique
  · exact solve H hunique'
  · exact solve H hunique
  · exact solve H hunique'
  · exact solve H hunique
  · exact solve H hunique'

/-- Complete elimination of the `(0,0,3)` distribution. -/
theorem impossible_only_I₃_three
    (h₁ : K.I₁.card = 0) (h₂ : K.I₂.card = 0)
    (h₃ : K.I₃.card = 3) : False := by
  have hempty₁ : K.I₁ = ∅ := Finset.card_eq_zero.mp h₁
  have hempty₂ : K.I₂ = ∅ := Finset.card_eq_zero.mp h₂
  have hcard : K.T₃.nonredPoints.card = 6 := by
    rw [K.nonred_card₃, h₃]
  obtain ⟨H⟩ := K.M₃.three_interior_pattern K.hfour
    (fun p hp ↦ K.interior_colour_ne_red₃ p hp) hcard
  have hm₀ : H.mate 0 ∈ K.I₃ := K.mem_I₃.mpr (H.strict 0)
  have hm₁ : H.mate 1 ∈ K.I₃ := K.mem_I₃.mpr (H.strict 1)
  have hm₂ : H.mate 2 ∈ K.I₃ := K.mem_I₃.mpr (H.strict 2)
  have hcover₀₁₂ : ∀ r : P, r ∈ K.I₃ →
      r = H.mate 0 ∨ r = H.mate 1 ∨ r = H.mate 2 := by
    intro r hr
    obtain ⟨i, hi⟩ := H.cover r (K.mem_I₃.mp hr)
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
    have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
      have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
        rw [← turn_rotate]
        exact K.inside.2.2
      rw [turn_swap_first] at h
      linarith
    exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
  have hu₂pos : 0 < turn (c : Point) (d : Point) (K.skeleton.u₂ : Point) := by
    have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using K.inside.2.1
    exact edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hbcd.le (by simp)
      (Or.inl hbcd)
  have hm₀ne := K.turn_cd_ne_zero_of_mem_I₃ hm₀
  rcases H.cycle with hcycle | hcycle
  · rcases lt_or_gt_of_ne hm₀ne with hm₀neg | hm₀pos
    · apply K.impossible_three_negative_full_lines
        hm₀ hm₁ hm₂ hcover₀₁₂ hempty₂ hm₀neg
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hm₀)) 5)
        (H.injective.ne (by decide))
        (by simpa only [K.T₃_side_zero, openSegment_symm] using hcycle.1)
        (by simpa only [K.T₃_side_two] using hcycle.2.2)
      intro l
      fin_cases l
      · simpa using K.skeleton_ne 5 4 (by decide)
      · simpa using K.skeleton_ne 5 0 (by decide)
      · simpa using K.skeleton_ne 5 2 (by decide)
    · have hm₂pos : 0 < turn (c : Point) (d : Point) (H.mate 2 : Point) :=
        turn_pos_of_right_of_positive_between_nonpos
          (by simpa only [K.T₃_side_two] using hcycle.2.2)
          hu₁neg.le hm₀pos
      have hcover₂₀₁ : ∀ r : P, r ∈ K.I₃ →
          r = H.mate 2 ∨ r = H.mate 0 ∨ r = H.mate 1 := by
        intro r hr
        rcases hcover₀₁₂ r hr with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      apply K.impossible_three_positive_full_lines
        hm₂ hm₀ hm₁ hcover₂₀₁ hempty₁ hm₂pos
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hm₂)) 0)
        (H.injective.ne (by decide))
        (by simpa only [K.T₃_side_two, openSegment_symm] using hcycle.2.2)
        (by simpa only [K.T₃_side_one] using hcycle.2.1)
      intro l
      fin_cases l
      · simpa using K.skeleton_ne 0 3 (by decide)
      · simpa using K.skeleton_ne 0 2 (by decide)
      · simpa using K.skeleton_ne 0 1 (by decide)
  · rcases lt_or_gt_of_ne hm₀ne with hm₀neg | hm₀pos
    · have hm₁neg : turn (c : Point) (d : Point) (H.mate 1 : Point) < 0 :=
        turn_neg_of_right_of_negative_between_nonneg
          (by simpa only [K.T₃_side_one] using hcycle.2.1)
          hu₂pos.le hm₀neg
      have hcover₁₀₂ : ∀ r : P, r ∈ K.I₃ →
          r = H.mate 1 ∨ r = H.mate 0 ∨ r = H.mate 2 := by
        intro r hr
        rcases hcover₀₁₂ r hr with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      apply K.impossible_three_negative_full_lines
        hm₁ hm₀ hm₂ hcover₁₀₂ hempty₂ hm₁neg
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hm₁)) 1)
        (H.injective.ne (by decide))
        (by simpa only [K.T₃_side_one, openSegment_symm] using hcycle.2.1)
        (by simpa only [K.T₃_side_two] using hcycle.2.2)
      intro l
      fin_cases l
      · simpa using K.skeleton_ne 1 4 (by decide)
      · simpa using K.skeleton_ne 1 0 (by decide)
      · simpa using K.skeleton_ne 1 2 (by decide)
    · have hcover₀₂₁ : ∀ r : P, r ∈ K.I₃ →
          r = H.mate 0 ∨ r = H.mate 2 ∨ r = H.mate 1 := by
        intro r hr
        rcases hcover₀₁₂ r hr with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl h)
      apply K.impossible_three_positive_full_lines
        hm₀ hm₂ hm₁ hcover₀₂₁ hempty₁ hm₀pos
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hm₀)) 5)
        (H.injective.ne (by decide))
        (by simpa only [K.T₃_side_zero, openSegment_symm] using hcycle.1)
        (by simpa only [K.T₃_side_one] using hcycle.2.1)
      intro l
      fin_cases l
      · simpa using K.skeleton_ne 5 3 (by decide)
      · simpa using K.skeleton_ne 5 2 (by decide)
      · simpa using K.skeleton_ne 5 1 (by decide)

/-- Beam pair `(v₂u₁, v₃u₁)`: three skeleton points already have
one colour, and the empty first cell supplies a fourth. -/
theorem impossible_one_one_beams_A_D
    {w p : P}
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hpair := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  obtain ⟨l, hcolour⟩ := colour_eq_some_side K.T₁ hpair K.skeleton.v₂
    (K.skeleton.blocker_colour_ne 4)
  let y := K.T₁.side l
  have hv₂y : K.skeleton.v₂ ≠ y := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_ne 4 3 (by decide)
    · simpa using K.skeleton_ne 4 2 (by decide)
    · simpa using K.skeleton_ne 4 1 (by decide)
  have hu₁y : K.skeleton.u₁ ≠ y := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_ne 0 3 (by decide)
    · simpa using K.skeleton_ne 0 2 (by decide)
    · simpa using K.skeleton_ne 0 1 (by decide)
  have hv₃y : K.skeleton.v₃ ≠ y := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_ne 5 3 (by decide)
    · simpa using K.skeleton_ne 5 2 (by decide)
    · simpa using K.skeleton_ne 5 1 (by decide)
  have hyHull : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_mem_outer 3
    · simpa using K.skeleton_mem_outer 2
    · simpa using K.skeleton_mem_outer 1
  apply four_same_colour_card_contradiction
      (x₀ := K.skeleton.v₂) (x₁ := K.skeleton.u₁)
      (x₂ := K.skeleton.v₃) (x₃ := y)
      (red := colour a)
    (K.skeleton_ne 4 0 (by decide))
    (K.skeleton_ne 4 5 (by decide)) hv₂y
    (K.skeleton_ne 0 5 (by decide)) hu₁y hv₃y
    (K.skeleton_mem_outer 4) (K.skeleton_mem_outer 0)
    (K.skeleton_mem_outer 5) hyHull
    (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm)
    (by
      calc
        colour K.skeleton.v₃ = colour K.skeleton.u₁ := by
          simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour.symm
        _ = colour K.skeleton.v₂ := by
          simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm)
    (by simpa [y] using hcolour.symm)
    (K.skeleton.blocker_colour_ne 4)
    (K.otherColourBound _ (K.skeleton.blocker_colour_ne 4))

/-- Beam pair `(u₁u₃, u₁u₂)`: the empty first cell would have to
contain the blocker of the equal-coloured pair `u₂u₃`. -/
theorem impossible_one_one_beams_C_F
    {w p : P}
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  have hcolour : colour K.skeleton.u₂ = colour K.skeleton.u₃ := by
    calc
      colour K.skeleton.u₂ = colour K.skeleton.u₁ := by
        simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_colour
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
  have hne : K.skeleton.u₂ ≠ K.skeleton.u₃ := K.skeleton_ne 1 2 (by decide)
  obtain ⟨r, hr⟩ := K.proper K.skeleton.u₂ K.skeleton.u₃ hne hcolour
  have hrStrict : StrictlyInsideTriangle (b : Point) (c : Point) (d : Point)
      (r : Point) := K.T₁.strict_of_between_distinct_sides (i := 2) (j := 1)
        (by decide) (by
          simpa only [K.T₁_side_two, K.T₁_side_one] using hr)
  have hrI : r ∈ K.I₁ := K.mem_I₁.mpr hrStrict
  rw [hempty₁] at hrI
  simp at hrI

/-- Beam pair `(v₂u₃, v₃u₂)`. -/
theorem impossible_one_one_beams_B_E
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₃u₂ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₂ := by
    exact hpair₁ (i := 1) (j := 2) (by decide)
  have hu₂u₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₁ := by
    intro h
    apply H₃.remaining_colour_ne
    calc
      colour (K.T₃.side 2) = colour K.skeleton.u₁ := by
        simp only [K.T₃_side_two]
      _ = colour K.skeleton.u₂ := h.symm
      _ = colour K.skeleton.v₃ := by
        simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
      _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero]
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne
  have hpu₃ : colour p = colour K.skeleton.u₃ := by
    have hexhaust := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 0)
      hu₃u₂ hu₂u₁ hu₁u₃
    rcases hexhaust with h | h | h
    · exact h
    · exact (H₃.p_colour_ne 1 (by simpa using h)).elim
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
  have hp_u₃ : p ≠ K.skeleton.u₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
  have hp_v₂ : p ≠ K.skeleton.v₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 4
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hp
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hv₂u₃ : colour K.skeleton.v₂ = colour K.skeleton.u₃ := by
      simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_colour.symm
    obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    obtain ⟨s, hs⟩ := K.proper p K.skeleton.v₂ hp_v₂
      (hpu₃.trans hv₂u₃.symm)
    have hrCases := K.portal_three_to_two hp hpneg
      (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr
    have hsCases := K.portal_three_to_two hp hpneg
      (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property) hs
    have hru₁ : r = K.skeleton.u₁ := by
      rcases hrCases with hrI₃ | h | hrI₂
      · have hrp := hunique₃ r hrI₃
        have heq : p = K.skeleton.u₃ := by simpa [hrp] using hr
        exact (hp_u₃ heq).elim
      · exact h
      · have hrw := hunique₂ r hrI₂
        have hcommon := other_endpoint_eq_of_common_blocker K.hfour
          (by simpa using K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
          (by simpa only [K.T₂_side_two, K.T₂_side_zero, hrw]
            using H₂.beam_between)
          (by simpa only [openSegment_symm, hrw] using hr)
        exact (hp_v₂ hcommon.symm).elim
    have hsu₁ : s = K.skeleton.u₁ := by
      rcases hsCases with hsI₃ | h | hsI₂
      · have hsp := hunique₃ s hsI₃
        have heq : p = K.skeleton.v₂ := by simpa [hsp] using hs
        exact (hp_v₂ heq).elim
      · exact h
      · have hsw := hunique₂ s hsI₂
        have hcommon := other_endpoint_eq_of_common_blocker K.hfour
          (by simpa using K.skeleton_ne 4 2 (by decide)) hp_v₂.symm
          (by
            rw [openSegment_symm]
            simpa only [K.T₂_side_two, K.T₂_side_zero, hsw]
              using H₂.beam_between)
          (by simpa only [openSegment_symm, hsw] using hs)
        exact (hp_u₃ hcommon.symm).elim
    have heq := other_endpoint_eq_of_common_blocker K.hfour hp_u₃ hp_v₂
      (by simpa [hru₁] using hr) (by simpa [hsu₁] using hs)
    exact (K.skeleton_ne 2 4 (by decide) heq).elim
  · obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    have hrCases := K.portal_three_to_one hp hppos
      (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property) hr
    rcases hrCases with hrI₃ | hru₂ | hrI₁
    · have hrp := hunique₃ r hrI₃
      have heq : p = K.skeleton.u₃ := by simpa [hrp] using hr
      exact hp_u₃ heq
    · have huBetween : (K.skeleton.u₂ : Point) ∈
          openSegment ℝ (p : Point) (K.skeleton.u₃ : Point) := by
        simpa [hru₂] using hr
      have hcross := first_pair_points_do_not_block_second K.hfour
        (by simpa using K.skeleton_ne 5 1 (by decide)) hp_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 5).symm
        (by simpa using K.skeleton_ne 5 2 (by decide))
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
        (by simpa using K.skeleton_ne 1 2 (by decide))
        (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
      exact hcross.2 huBetween
    · rw [hempty₁] at hrI₁
      simp at hrI₁

/-- Beam pair `(v₂u₃, u₁u₂)`. -/
theorem impossible_one_one_beams_B_F
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne
  have hu₃w : colour K.skeleton.u₃ ≠ colour w :=
    (H₂.p_colour_ne 2).symm
  have hwu₁ : colour w ≠ colour K.skeleton.u₁ := H₂.p_colour_ne 1
  have hpCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 2)
    (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
    hu₁u₃ hu₃w hwu₁
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hp
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · rcases hpCases with hpu₁ | hpu₃ | hpwColour
    · exact (H₃.p_colour_ne 2 (by simpa using hpu₁)).elim
    · have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
      obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      have hrCases := K.portal_three_to_two hp hpneg
        (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr
      rcases hrCases with hrI₃ | hru₁ | hrI₂
      · have hrp := hunique₃ r hrI₃
        exact hp_u₃ (by simpa [hrp] using hr)
      · have hcross := first_pair_points_do_not_block_second K.hfour
          (by simpa using K.skeleton_ne 1 0 (by decide)) hp_u₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
          (by simpa using K.skeleton_ne 1 2 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
          (by simpa using K.skeleton_ne 0 2 (by decide))
          (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
        exact hcross.2 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        have hcommon := other_endpoint_eq_of_common_blocker K.hfour
          (by simpa using K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
          (by simpa only [K.T₂_side_two, K.T₂_side_zero, hrw]
            using H₂.beam_between)
          (by simpa only [openSegment_symm, hrw] using hr)
        exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 4 hcommon.symm).elim
    · have hpw : p ≠ w := by
        intro h
        exact (Finset.disjoint_left.mp (cellPoints_pairwise_disjoint).2.2)
          hw (h ▸ hp)
      obtain ⟨r, hr⟩ := K.proper p w hpw hpwColour
      have hwHull := strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)
      have hrCases := K.portal_three_to_two hp hpneg hwHull hr
      rcases hrCases with hrI₃ | hru₁ | hrI₂
      · have hrp := hunique₃ r hrI₃
        exact hpw (by simpa [hrp] using hr)
      · have hcross := first_pair_points_do_not_block_second K.hfour
          (by simpa using K.skeleton_ne 1 0 (by decide)) hpw
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
        exact hcross.2 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        exact hpw (by simpa [hrw] using hr)
  · apply K.impossible_positive_portal_beam (e := K.skeleton.u₁)
        hp hunique₃ hempty₁ hppos
    · rw [openSegment_symm]
      simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between
    · simpa using K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0
    · simpa using K.skeleton_ne 0 1 (by decide)
    · intro l
      fin_cases l
      · simpa using K.skeleton_ne 0 3 (by decide)
      · simpa using K.skeleton_ne 0 2 (by decide)
      · simpa using K.skeleton_ne 0 1 (by decide)

/-- Beam pair `(v₂u₃, v₃u₁)`. -/
theorem impossible_one_one_beams_B_D
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne.symm
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    intro h
    apply H₃.remaining_colour_ne
    calc
      colour (K.T₃.side 1) = colour K.skeleton.u₂ := by simp only [K.T₃_side_one]
      _ = colour K.skeleton.u₁ := h.symm
      _ = colour (K.T₃.side 2) := by simp only [K.T₃_side_two]
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ := by
    exact hpair₁ (i := 2) (j := 1) (by decide)
  have hpu₃ : colour p = colour K.skeleton.u₃ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      hu₃u₁ hu₁u₂ hu₂u₃
    rcases hcases with h | h | h
    · exact h
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
    · exact (H₃.p_colour_ne 1 (by simpa using h)).elim
  have hv₁v₃ : colour K.skeleton.v₁ = colour K.skeleton.v₃ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 3)
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      hu₃u₁ hu₁u₂ hu₂u₃
    rcases hcases with h | h | h
    · exact (hpair₁ (i := 0) (j := 1) (by decide) (by simpa using h)).elim
    · calc
        colour K.skeleton.v₁ = colour K.skeleton.u₁ := h
        _ = colour K.skeleton.v₃ := by
          simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour
    · exact (hpair₁ (i := 0) (j := 2) (by decide) (by simpa using h)).elim
  have hp_u₃ : p ≠ K.skeleton.u₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
  have hp_v₂ : p ≠ K.skeleton.v₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 4
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hp
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hv₂u₃ : colour K.skeleton.v₂ = colour K.skeleton.u₃ := by
      simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_colour.symm
    obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    obtain ⟨s, hs⟩ := K.proper p K.skeleton.v₂ hp_v₂
      (hpu₃.trans hv₂u₃.symm)
    have forcePortal {t y : P} (ht : (t : Point) ∈ openSegment ℝ (p : Point) (y : Point))
        (hy : y = K.skeleton.u₃ ∨ y = K.skeleton.v₂) : t = K.skeleton.u₁ := by
      have hyHull : (y : Point) ∈ triangleHull (c : Point) (a : Point) (d : Point) := by
        rcases hy with rfl | rfl
        · exact K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property
        · exact K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property
      rcases K.portal_three_to_two hp hpneg hyHull ht with htI₃ | h | htI₂
      · have htp := hunique₃ t htI₃
        rcases hy with rfl | rfl
        · exact (hp_u₃ (by simpa [htp] using ht)).elim
        · exact (hp_v₂ (by simpa [htp] using ht)).elim
      · exact h
      · have htw := hunique₂ t htI₂
        rcases hy with rfl | rfl
        · have heq := other_endpoint_eq_of_common_blocker K.hfour
              (by simpa using K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
              (by simpa only [K.T₂_side_two, K.T₂_side_zero, htw]
                using H₂.beam_between)
              (by simpa only [openSegment_symm, htw] using ht)
          exact (hp_v₂ heq.symm).elim
        · have heq := other_endpoint_eq_of_common_blocker K.hfour
              (by simpa using K.skeleton_ne 4 2 (by decide)) hp_v₂.symm
              (by
                rw [openSegment_symm]
                simpa only [K.T₂_side_two, K.T₂_side_zero, htw]
                  using H₂.beam_between)
              (by simpa only [openSegment_symm, htw] using ht)
          exact (hp_u₃ heq.symm).elim
    have hru₁ := forcePortal hr (Or.inl rfl)
    have hsu₁ := forcePortal hs (Or.inr rfl)
    have heq := other_endpoint_eq_of_common_blocker K.hfour hp_u₃ hp_v₂
      (by simpa [hru₁] using hr) (by simpa [hsu₁] using hs)
    exact (K.skeleton_ne 2 4 (by decide) heq).elim
  · obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    have hrCases := K.portal_three_to_one hp hppos
      (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property) hr
    have hru₂ : r = K.skeleton.u₂ := by
      rcases hrCases with hrI₃ | h | hrI₁
      · have hrp := hunique₃ r hrI₃
        exact (hp_u₃ (by simpa [hrp] using hr)).elim
      · exact h
      · rw [hempty₁] at hrI₁
        simp at hrI₁
    have hu₂Interior : (K.skeleton.u₂ : Point) ∈
        openSegment ℝ (p : Point) (K.skeleton.u₃ : Point) := by
      simpa [hru₂] using hr
    have hv₃pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) := by
      have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
        have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
          have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
            rw [← turn_rotate]
            exact K.inside.2.2
          rw [turn_swap_first] at h
          linarith
        exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
      exact turn_pos_of_right_of_positive_between_nonpos
        (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
        hu₁neg.le hppos
    obtain ⟨s, hs⟩ := K.proper K.skeleton.v₁ K.skeleton.v₃
      (K.skeleton_ne 3 5 (by decide)) hv₁v₃
    have hsCases := K.portal_v₃_v₁ hv₃pos hs
    have hsu₂ : s = K.skeleton.u₂ := by
      rcases hsCases with hsI₃ | h | hsI₁
      · have hsp := hunique₃ s hsI₃
        have hpOn : (p : Point) ∈ openSegment ℝ
            (K.skeleton.v₁ : Point) (K.skeleton.v₃ : Point) := by
          simpa [hsp] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (by simpa using K.skeleton_ne 5 0 (by decide))
          (by simpa using K.skeleton_ne 5 3 (by decide))
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
          (by simpa only [openSegment_symm] using hpOn)
        exact (K.skeleton_ne 0 3 (by decide) heq).elim
      · exact h
      · rw [hempty₁] at hsI₁
        simp at hsI₁
    exact K.u₂_cannot_block_both_exceptional_pairs
      (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
      (by simpa [hsu₂] using hs) hu₂Interior

/-- Beam pair `(u₁u₃, v₃u₁)`.  The only difficult subcase reduces to
opposite signs across the full spoke line `bd`; this is the synthetic form
of the barycentric computation in the paper repair. -/
theorem impossible_one_one_beams_C_D
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    simpa only [K.T₃_side_two, K.T₃_side_one] using H₃.remaining_colour_ne.symm
  have hu₂v₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.v₁ := by
    exact hpair₁ (i := 2) (j := 0) (by decide)
  have hv₁u₁ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₁ := by
    intro h
    apply hpair₁ (i := 0) (j := 1) (by decide)
    calc
      colour (K.T₁.side 0) = colour K.skeleton.v₁ := by simp only [K.T₁_side_zero]
      _ = colour K.skeleton.u₁ := h
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour (K.T₁.side 1) := by simp only [K.T₁_side_one]
  have hwCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 1)
    (K.skeleton.blocker_colour_ne 3)
    hu₁u₂ hu₂v₁ hv₁u₁
  have hw_u₂ : w ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
  have hw_v₁ : w ≠ K.skeleton.v₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3
  have hp_v₁ : p ≠ K.skeleton.v₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 3
  have hwp : w ≠ p := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
      hw (e ▸ hp)
  rcases hwCases with hwu₁ | hwu₂ | hwv₁
  · exact (H₂.p_colour_ne 1 (by simpa using hwu₁)).elim
  · obtain ⟨r, hr⟩ := K.proper w K.skeleton.u₂ hw_u₂ hwu₂
    have hrd := K.blocker_from_C_beam_to_u₂_eq_center hw hp hunique₂ hunique₃
      hempty₁
      (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
      (by
        apply turn_neg_of_between_nonpos
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
          K.v₃_spoke_side_neg
        simp)
      hr
    have hb_u₂ : b ≠ K.skeleton.u₂ := by
      intro e
      have hm : (b : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₂
      exact K.hbd (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
    have hd_u₂ : d ≠ K.skeleton.u₂ := by
      intro e
      have hm : (d : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₂
      exact K.hbd (Subtype.ext
        ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
    have hb_w : b ≠ w := by
      have hwOuter := strict_cell_strict_outer K.inside
        (Or.inr (Or.inl (K.mem_I₂.mp hw)))
      intro e
      exact (strictlyInsideTriangle_ne_vertices hwOuter).2.1
        (congrArg Subtype.val e.symm)
    have hd_w : d ≠ w := by
      intro e
      exact (strictlyInsideTriangle_ne_vertices (K.mem_I₂.mp hw)).2.2
        (congrArg Subtype.val e.symm)
    have hbd := first_pair_points_do_not_block_second K.hfour K.hbd hw_u₂.symm
      hb_u₂ hb_w hd_u₂ hd_w K.skeleton.hu₂
    exact hbd.2 (by simpa only [openSegment_symm, hrd] using hr)
  · have hpu₁ : colour p ≠ colour K.skeleton.u₁ := by
      simpa only [K.T₃_side_two] using H₃.p_colour_ne 2
    have hpu₂ : colour p ≠ colour K.skeleton.u₂ := by
      simpa only [K.T₃_side_one] using H₃.p_colour_ne 1
    have hpv₁ : colour p = colour K.skeleton.v₁ := by
      have hpCases := fin4_eq_one_of_three_of_avoid
        (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
        (K.skeleton.blocker_colour_ne 0)
        (K.skeleton.blocker_colour_ne 1)
        (K.skeleton.blocker_colour_ne 3)
        hu₁u₂ hu₂v₁ hv₁u₁
      rcases hpCases with h | h | h
      · exact (hpu₁ h).elim
      · exact (hpu₂ h).elim
      · exact h
    obtain ⟨r, hr⟩ := K.proper w K.skeleton.v₁ hw_v₁ hwv₁
    obtain ⟨s, hs⟩ := K.proper w p hwp (hwv₁.trans hpv₁.symm)
    have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (w : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inl (K.mem_I₂.mp hw)))
    have hpOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (p : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inr (K.mem_I₃.mp hp)))
    have hCwv := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 2 (by decide)) hw_v₁
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
      (K.skeleton_ne 0 3 (by decide))
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
      (K.skeleton_ne 2 3 (by decide))
      (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
    have hrCases : r = d ∨ r = K.skeleton.u₂ ∨ r = p := by
      have hrOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
          (r : Point) := strict_outer_of_between_strict_hull
            (turn_pos_of_strictlyInsideTriangle K.inside) hwOuter
            (K.skeleton_mem_outer 3) hr
      have hrHull := strictlyInsideTriangle_mem_triangleHull hrOuter
      rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
          K.inside K.skeleton r hrHull with
          hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
          hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
      · exact ((strictlyInsideTriangle_ne_vertices hrOuter).1
          (congrArg Subtype.val hra)).elim
      · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.1
          (congrArg Subtype.val hrb)).elim
      · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.2
          (congrArg Subtype.val hrc)).elim
      · exact Or.inl hrd
      · subst r; exact (hCwv.1 hr).elim
      · exact Or.inr (Or.inl hru₂)
      · subst r; exact (hCwv.2 hr).elim
      · rw [hrv₁] at hrOuter
        linarith [hrOuter.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
      · rw [hrv₂] at hrOuter
        have hz := turn_eq_zero_of_between K.skeleton.hv₂
        rw [turn_swap_first] at hz
        linarith [hrOuter.2.2, hz]
      · rw [hrv₃] at hrOuter
        linarith [hrOuter.1, turn_eq_zero_of_between K.skeleton.hv₃]
      · have hrI : r ∈ K.I₁ := K.mem_I₁.mpr hr₁
        rw [hempty₁] at hrI
        simp at hrI
      · have hrw := hunique₂ r (K.mem_I₂.mpr hr₂)
        subst r
        exact (hw_v₁ (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hr))).elim
      · exact Or.inr (Or.inr (hunique₃ r (K.mem_I₃.mpr hr₃)))
    have hCwp := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 2 (by decide)) hwp
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2).symm
      (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
    have hDpw := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 5 0 (by decide)) hwp.symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 5).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
      (by
        rw [openSegment_symm]
        simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
    have hsCases : s = d ∨ s = K.skeleton.u₂ := by
      have hsOuter := strictlyInside_between_inside_points hwOuter hpOuter hs
      have hsHull := strictlyInsideTriangle_mem_triangleHull hsOuter
      rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
          K.inside K.skeleton s hsHull with
          hsa | hsb | hsc | hsd | hsu₁ | hsu₂ | hsu₃ |
          hsv₁ | hsv₂ | hsv₃ | hs₁ | hs₂ | hs₃
      · exact ((strictlyInsideTriangle_ne_vertices hsOuter).1
          (congrArg Subtype.val hsa)).elim
      · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.1
          (congrArg Subtype.val hsb)).elim
      · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.2
          (congrArg Subtype.val hsc)).elim
      · exact Or.inl hsd
      · subst s; exact (hCwp.1 hs).elim
      · exact Or.inr hsu₂
      · subst s; exact (hCwp.2 hs).elim
      · rw [hsv₁] at hsOuter
        linarith [hsOuter.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
      · rw [hsv₂] at hsOuter
        have hz := turn_eq_zero_of_between K.skeleton.hv₂
        rw [turn_swap_first] at hz
        linarith [hsOuter.2.2, hz]
      · subst s
        exact (hDpw.1 (by simpa only [openSegment_symm] using hs)).elim
      · have hsI : s ∈ K.I₁ := K.mem_I₁.mpr hs₁
        rw [hempty₁] at hsI
        simp at hsI
      · have hsw := hunique₂ s (K.mem_I₂.mpr hs₂)
        subst s
        exact (hwp (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hs))).elim
      · have hsp := hunique₃ s (K.mem_I₃.mpr hs₃)
        subst s
        exact (hwp (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hs))).elim
    have hv₁neg : turn (b : Point) (d : Point) (K.skeleton.v₁ : Point) < 0 := by
      have hbdc : turn (b : Point) (d : Point) (c : Point) < 0 := by
        rw [turn_swap_last]
        linarith [K.inside.2.1]
      exact turn_neg_of_between_nonpos
        (by simpa only [openSegment_symm] using K.skeleton.hv₁)
        hbdc (by simp)
    have hbdA : 0 < turn (b : Point) (d : Point) (a : Point) := by
      simpa only [turn_rotate] using K.inside.1
    have hv₃pos : 0 < turn (b : Point) (d : Point)
        (K.skeleton.v₃ : Point) :=
      edgeTurn_pos_of_mem_openSegment K.skeleton.hv₃ hbdA.le (by simp)
        (Or.inl hbdA)
    have hu₁pos : 0 < turn (b : Point) (d : Point)
        (K.skeleton.u₁ : Point) :=
      edgeTurn_pos_of_mem_openSegment K.skeleton.hu₁ hbdA.le (by simp)
        (Or.inl hbdA)
    have hppos : 0 < turn (b : Point) (d : Point) (p : Point) :=
      edgeTurn_pos_of_mem_openSegment
        (by
          rw [openSegment_symm]
          simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
        hv₃pos.le hu₁pos.le (Or.inl hv₃pos)
    have hu₂zero : turn (b : Point) (d : Point) (K.skeleton.u₂ : Point) = 0 :=
      turn_eq_zero_of_between K.skeleton.hu₂
    have hdzero : turn (b : Point) (d : Point) (d : Point) = 0 := by simp
    rcases hrCases with hrd | hru₂ | hrp
    · have hrd' : (d : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hrd] using hr
      rcases hsCases with hsd | hsu₂
      · have hsd' : (d : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hsd] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour hw_v₁ hwp hrd' hsd'
        exact (hp_v₁ heq.symm).elim
      · have hsu₂' : (K.skeleton.u₂ : Point) ∈
            openSegment ℝ (w : Point) (p : Point) := by simpa only [hsu₂] using hs
        have hwpos := turn_pos_beyond_zero_from_neg
          (by simpa only [openSegment_symm] using hrd') hv₁neg hdzero
        have hwneg := turn_neg_beyond_zero_from_pos
          (by simpa only [openSegment_symm] using hsu₂') hppos hu₂zero
        linarith
    · have hru₂' : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hru₂] using hr
      rcases hsCases with hsd | hsu₂
      · have hsd' : (d : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hsd] using hs
        have hwpos := turn_pos_beyond_zero_from_neg
          (by simpa only [openSegment_symm] using hru₂') hv₁neg hu₂zero
        have hwneg := turn_neg_beyond_zero_from_pos
          (by simpa only [openSegment_symm] using hsd') hppos hdzero
        linarith
      · have hsu₂' : (K.skeleton.u₂ : Point) ∈
            openSegment ℝ (w : Point) (p : Point) := by simpa only [hsu₂] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour hw_v₁ hwp
          hru₂' hsu₂'
        exact (hp_v₁ heq.symm).elim
    · have hpBetween : (p : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hrp] using hr
      have hsNested := openSegment_left_nested hs hpBetween
      have hsZero := turn_eq_zero_of_between hsNested
      rcases point_eq_of_on_full_line K.hfour hw_v₁ hpBetween hsZero with
          hsw | hsv₁ | hsp
      · have hm : (w : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hsw] using hs
        exact (hwp (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
      · have hm : (K.skeleton.v₁ : Point) ∈
            openSegment ℝ (w : Point) (p : Point) := by simpa only [hsv₁] using hs
        exact not_two_mutual_openSegments (Subtype.val_injective.ne hw_v₁)
          ⟨hpBetween, hm⟩
      · have hm : (p : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hsp] using hs
        exact (hwp (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim

/-- Reflected difficult beam pair `(v₂u₁, u₁u₂)`. -/
theorem impossible_one_one_beams_A_F
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    intro h
    apply H₂.remaining_colour_ne
    calc
      colour (K.T₂.side 2) = colour K.skeleton.u₃ := by simp only [K.T₂_side_two]
      _ = colour K.skeleton.u₁ := h.symm
      _ = colour K.skeleton.v₂ := by
        simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm
      _ = colour (K.T₂.side 0) := by simp only [K.T₂_side_zero]
  have hu₃v₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.v₁ := by
    exact hpair₁ (i := 1) (j := 0) (by decide)
  have hv₁u₁ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₁ := by
    intro h
    apply hpair₁ (i := 0) (j := 2) (by decide)
    calc
      colour (K.T₁.side 0) = colour K.skeleton.v₁ := by simp only [K.T₁_side_zero]
      _ = colour K.skeleton.u₁ := h
      _ = colour K.skeleton.u₂ := by
        simpa only [K.T₃_side_two, K.T₃_side_one] using H₃.beam_colour.symm
      _ = colour (K.T₁.side 2) := by simp only [K.T₁_side_two]
  have hpCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 2)
    (K.skeleton.blocker_colour_ne 3)
    hu₁u₃ hu₃v₁ hv₁u₁
  have hp_u₃ : p ≠ K.skeleton.u₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2
  have hp_v₁ : p ≠ K.skeleton.v₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 3
  have hw_v₁ : w ≠ K.skeleton.v₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3
  have hpw : p ≠ w := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
      hw (e.symm ▸ hp)
  rcases hpCases with hpu₁ | hpu₃ | hpv₁
  · exact (H₃.p_colour_ne 2 (by simpa using hpu₁)).elim
  · obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    have hrd := K.blocker_from_F_beam_to_u₃_eq_center hw hp hunique₂ hunique₃
      hempty₁
      (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
      (by
        rw [openSegment_symm]
        simpa only [K.T₃_side_two, K.T₃_side_one] using H₃.beam_between)
      hr
    have hc_u₃ : c ≠ K.skeleton.u₃ := by
      intro e
      have hm : (c : Point) ∈ openSegment ℝ (c : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₃
      exact K.hcd (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
    have hd_u₃ : d ≠ K.skeleton.u₃ := by
      intro e
      have hm : (d : Point) ∈ openSegment ℝ (c : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₃
      exact K.hcd (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
    have hc_p : c ≠ p := by
      have hpOuter := strict_cell_strict_outer K.inside
        (Or.inr (Or.inr (K.mem_I₃.mp hp)))
      intro e
      exact (strictlyInsideTriangle_ne_vertices hpOuter).2.2
        (congrArg Subtype.val e.symm)
    have hd_p : d ≠ p := by
      intro e
      exact (strictlyInsideTriangle_ne_vertices (K.mem_I₃.mp hp)).2.2
        (congrArg Subtype.val e.symm)
    have hcd := first_pair_points_do_not_block_second K.hfour K.hcd hp_u₃.symm
      hc_u₃ hc_p hd_u₃ hd_p K.skeleton.hu₃
    exact hcd.2 (by simpa only [openSegment_symm, hrd] using hr)
  · have hwu₁ : colour w ≠ colour K.skeleton.u₁ := by
      simpa only [K.T₂_side_one] using H₂.p_colour_ne 1
    have hwu₃ : colour w ≠ colour K.skeleton.u₃ := by
      simpa only [K.T₂_side_two] using H₂.p_colour_ne 2
    have hwv₁ : colour w = colour K.skeleton.v₁ := by
      have hwCases := fin4_eq_one_of_three_of_avoid
        (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
        (K.skeleton.blocker_colour_ne 0)
        (K.skeleton.blocker_colour_ne 2)
        (K.skeleton.blocker_colour_ne 3)
        hu₁u₃ hu₃v₁ hv₁u₁
      rcases hwCases with h | h | h
      · exact (hwu₁ h).elim
      · exact (hwu₃ h).elim
      · exact h
    obtain ⟨r, hr⟩ := K.proper p K.skeleton.v₁ hp_v₁ hpv₁
    obtain ⟨s, hs⟩ := K.proper p w hpw (hpv₁.trans hwv₁.symm)
    have hpOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (p : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inr (K.mem_I₃.mp hp)))
    have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (w : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inl (K.mem_I₂.mp hw)))
    have hFpv := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 1 (by decide)) hp_v₁
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
      (K.skeleton_ne 0 3 (by decide))
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
      (K.skeleton_ne 1 3 (by decide))
      (by
        rw [openSegment_symm]
        simpa only [K.T₃_side_two, K.T₃_side_one] using H₃.beam_between)
    have hrCases : r = d ∨ r = K.skeleton.u₃ ∨ r = w := by
      rcases K.strict_outer_chord_cases hpOuter (K.skeleton_mem_outer 3) hr with
        hrd | hru₁ | hru₂ | hru₃ | hr₁ | hr₂ | hr₃
      · exact Or.inl hrd
      · subst r; exact (hFpv.1 hr).elim
      · subst r; exact (hFpv.2 hr).elim
      · exact Or.inr (Or.inl hru₃)
      · rw [hempty₁] at hr₁; simp at hr₁
      · exact Or.inr (Or.inr (hunique₂ r hr₂))
      · have hrp := hunique₃ r hr₃
        have hm : (p : Point) ∈ openSegment ℝ
            (p : Point) (K.skeleton.v₁ : Point) := by simpa only [hrp] using hr
        exact (hp_v₁ (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
    have hFpw := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 1 (by decide)) hpw
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1).symm
      (by
        rw [openSegment_symm]
        simpa only [K.T₃_side_two, K.T₃_side_one] using H₃.beam_between)
    have hsCases : s = d ∨ s = K.skeleton.u₃ := by
      rcases K.strict_outer_chord_cases hpOuter
          (strictlyInsideTriangle_mem_triangleHull hwOuter) hs with
        hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
      · exact Or.inl hsd
      · subst s; exact (hFpw.1 hs).elim
      · subst s; exact (hFpw.2 hs).elim
      · exact Or.inr hsu₃
      · rw [hempty₁] at hs₁; simp at hs₁
      · have hsw := hunique₂ s hs₂
        have hm : (w : Point) ∈ openSegment ℝ (p : Point) (w : Point) := by
          simpa only [hsw] using hs
        exact (hpw (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
      · have hsp := hunique₃ s hs₃
        have hm : (p : Point) ∈ openSegment ℝ (p : Point) (w : Point) := by
          simpa only [hsp] using hs
        exact (hpw (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
    have hv₁pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₁ : Point) := by
      have hcdb : 0 < turn (c : Point) (d : Point) (b : Point) := by
        simpa only [turn_rotate] using K.inside.2.1
      exact edgeTurn_pos_of_mem_openSegment K.skeleton.hv₁
        hcdb.le (by simp) (Or.inl hcdb)
    have hcda : turn (c : Point) (d : Point) (a : Point) < 0 := by
      rw [turn_swap_last]
      linarith [K.inside.2.2]
    have hv₂neg : turn (c : Point) (d : Point) (K.skeleton.v₂ : Point) < 0 :=
      turn_neg_of_between_nonpos K.skeleton.hv₂ hcda (by simp)
    have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 :=
      turn_neg_of_between_nonpos K.skeleton.hu₁ hcda (by simp)
    have hwneg : turn (c : Point) (d : Point) (w : Point) < 0 :=
      turn_neg_of_between_nonpos
        (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
        hv₂neg hu₁neg.le
    have hu₃zero : turn (c : Point) (d : Point) (K.skeleton.u₃ : Point) = 0 :=
      turn_eq_zero_of_between K.skeleton.hu₃
    have hdzero : turn (c : Point) (d : Point) (d : Point) = 0 := by simp
    rcases hrCases with hrd | hru₃ | hrw
    · have hrd' : (d : Point) ∈ openSegment ℝ
          (p : Point) (K.skeleton.v₁ : Point) := by simpa only [hrd] using hr
      rcases hsCases with hsd | hsu₃
      · have hsd' : (d : Point) ∈ openSegment ℝ (p : Point) (w : Point) := by
          simpa only [hsd] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour hp_v₁ hpw hrd' hsd'
        exact (hw_v₁ heq.symm).elim
      · have hsu₃' : (K.skeleton.u₃ : Point) ∈
            openSegment ℝ (p : Point) (w : Point) := by simpa only [hsu₃] using hs
        have hpneg := turn_neg_beyond_zero_from_pos
          (x := (K.skeleton.v₁ : Point)) (z := (d : Point)) (y := (p : Point))
          (by rw [openSegment_symm]; exact hrd') hv₁pos hdzero
        have hppos := turn_pos_beyond_zero_from_neg
          (x := (w : Point)) (z := (K.skeleton.u₃ : Point)) (y := (p : Point))
          (by rw [openSegment_symm]; exact hsu₃') hwneg hu₃zero
        linarith
    · have hru₃' : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
          (p : Point) (K.skeleton.v₁ : Point) := by simpa only [hru₃] using hr
      rcases hsCases with hsd | hsu₃
      · have hsd' : (d : Point) ∈ openSegment ℝ (p : Point) (w : Point) := by
          simpa only [hsd] using hs
        have hpneg := turn_neg_beyond_zero_from_pos
          (x := (K.skeleton.v₁ : Point)) (z := (K.skeleton.u₃ : Point))
          (y := (p : Point)) (by rw [openSegment_symm]; exact hru₃')
          hv₁pos hu₃zero
        have hppos := turn_pos_beyond_zero_from_neg
          (x := (w : Point)) (z := (d : Point)) (y := (p : Point))
          (by rw [openSegment_symm]; exact hsd') hwneg hdzero
        linarith
      · have hsu₃' : (K.skeleton.u₃ : Point) ∈
            openSegment ℝ (p : Point) (w : Point) := by simpa only [hsu₃] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour hp_v₁ hpw
          hru₃' hsu₃'
        exact (hw_v₁ heq.symm).elim
    · have hwBetween : (w : Point) ∈ openSegment ℝ
          (p : Point) (K.skeleton.v₁ : Point) := by simpa only [hrw] using hr
      have hsNested := openSegment_left_nested hs hwBetween
      have hsZero := turn_eq_zero_of_between hsNested
      rcases point_eq_of_on_full_line K.hfour hp_v₁ hwBetween hsZero with
          hsp | hsv₁ | hsw
      · have hm : (p : Point) ∈ openSegment ℝ (p : Point) (w : Point) := by
          simpa only [hsp] using hs
        exact (hpw (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
      · have hm : (K.skeleton.v₁ : Point) ∈
            openSegment ℝ (p : Point) (w : Point) := by simpa only [hsv₁] using hs
        exact not_two_mutual_openSegments (Subtype.val_injective.ne hp_v₁)
          ⟨hwBetween, hm⟩
      · have hm : (w : Point) ∈ openSegment ℝ (p : Point) (w : Point) := by
          simpa only [hsw] using hs
        exact (hpw (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim

/-- Reflected pair `(u₁u₃, v₃u₂)`. -/
theorem impossible_one_one_beams_C_E
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    intro h
    apply hpair₁ (i := 1) (j := 2) (by decide)
    calc
      colour (K.T₁.side 1) = colour K.skeleton.u₃ := by simp only [K.T₁_side_one]
      _ = colour K.skeleton.u₁ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour.symm
      _ = colour K.skeleton.u₂ := h
      _ = colour (K.T₁.side 2) := by simp only [K.T₁_side_two]
  have hu₂v₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.v₁ :=
    hpair₁ (i := 2) (j := 0) (by decide)
  have hv₁u₁ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₁ := by
    intro h
    apply hpair₁ (i := 0) (j := 1) (by decide)
    calc
      colour (K.T₁.side 0) = colour K.skeleton.v₁ := by simp only [K.T₁_side_zero]
      _ = colour K.skeleton.u₁ := h
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour (K.T₁.side 1) := by simp only [K.T₁_side_one]
  have hwCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 1)
    (K.skeleton.blocker_colour_ne 3)
    hu₁u₂ hu₂v₁ hv₁u₁
  have hw_u₂ : w ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
  have hw_v₁ : w ≠ K.skeleton.v₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3
  have hp_v₁ : p ≠ K.skeleton.v₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 3
  have hwp : w ≠ p := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
      hw (e ▸ hp)
  rcases hwCases with hwu₁ | hwu₂ | hwv₁
  · exact (H₂.p_colour_ne 1 (by simpa using hwu₁)).elim
  · obtain ⟨r, hr⟩ := K.proper w K.skeleton.u₂ hw_u₂ hwu₂
    have hpNeg : turn (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
        (p : Point) < 0 :=
      turn_neg_of_between_nonpos
        (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
        K.v₃_spoke_side_neg (by simp)
    have hrd := K.blocker_from_C_beam_to_u₂_eq_center hw hp hunique₂ hunique₃
      hempty₁
      (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
      hpNeg hr
    have hb_u₂ : b ≠ K.skeleton.u₂ := by
      intro e
      have hm : (b : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₂
      exact K.hbd (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
    have hd_u₂ : d ≠ K.skeleton.u₂ := by
      intro e
      have hm : (d : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₂
      exact K.hbd (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
    have hb_w : b ≠ w := by
      have hwOuter := strict_cell_strict_outer K.inside
        (Or.inr (Or.inl (K.mem_I₂.mp hw)))
      intro e
      exact (strictlyInsideTriangle_ne_vertices hwOuter).2.1
        (congrArg Subtype.val e.symm)
    have hd_w : d ≠ w := by
      intro e
      exact (strictlyInsideTriangle_ne_vertices (K.mem_I₂.mp hw)).2.2
        (congrArg Subtype.val e.symm)
    have hbd := first_pair_points_do_not_block_second K.hfour K.hbd hw_u₂.symm
      hb_u₂ hb_w hd_u₂ hd_w K.skeleton.hu₂
    exact hbd.2 (by simpa only [openSegment_symm, hrd] using hr)
  · have hpu₁ : colour p ≠ colour K.skeleton.u₁ := by
      simpa only [K.T₃_side_two] using H₃.p_colour_ne 2
    have hpu₂ : colour p ≠ colour K.skeleton.u₂ := by
      simpa only [K.T₃_side_one] using H₃.p_colour_ne 1
    have hpv₁ : colour p = colour K.skeleton.v₁ := by
      have hpCases := fin4_eq_one_of_three_of_avoid
        (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
        (K.skeleton.blocker_colour_ne 0)
        (K.skeleton.blocker_colour_ne 1)
        (K.skeleton.blocker_colour_ne 3)
        hu₁u₂ hu₂v₁ hv₁u₁
      rcases hpCases with h | h | h
      · exact (hpu₁ h).elim
      · exact (hpu₂ h).elim
      · exact h
    obtain ⟨r, hr⟩ := K.proper w K.skeleton.v₁ hw_v₁ hwv₁
    obtain ⟨s, hs⟩ := K.proper w p hwp (hwv₁.trans hpv₁.symm)
    have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (w : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inl (K.mem_I₂.mp hw)))
    have hpOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (p : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inr (K.mem_I₃.mp hp)))
    have hCwv := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 2 (by decide)) hw_v₁
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
      (K.skeleton_ne 0 3 (by decide))
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
      (K.skeleton_ne 2 3 (by decide))
      (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
    have hrCases : r = d ∨ r = K.skeleton.u₂ ∨ r = p := by
      rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 3) hr with
        hrd | hru₁ | hru₂ | hru₃ | hr₁ | hr₂ | hr₃
      · exact Or.inl hrd
      · subst r; exact (hCwv.1 hr).elim
      · exact Or.inr (Or.inl hru₂)
      · subst r; exact (hCwv.2 hr).elim
      · rw [hempty₁] at hr₁; simp at hr₁
      · have hrw := hunique₂ r hr₂
        have hm : (w : Point) ∈ openSegment ℝ
            (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hrw] using hr
        exact (hw_v₁ (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
      · exact Or.inr (Or.inr (hunique₃ r hr₃))
    have hCwp := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 2 (by decide)) hwp
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 0).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 2).symm
      (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
    have hEpw := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 5 1 (by decide)) hwp.symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 5).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 1).symm
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1).symm
      (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
    have hsd : s = d := by
      rcases K.strict_outer_chord_cases hwOuter
          (strictlyInsideTriangle_mem_triangleHull hpOuter) hs with
        hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
      · exact hsd
      · subst s; exact (hCwp.1 hs).elim
      · subst s
        exact (hEpw.2 (by simpa only [openSegment_symm] using hs)).elim
      · subst s; exact (hCwp.2 hs).elim
      · rw [hempty₁] at hs₁; simp at hs₁
      · have hsw := hunique₂ s hs₂
        have hm : (w : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hsw] using hs
        exact (hwp (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
      · have hsp := hunique₃ s hs₃
        have hm : (p : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hsp] using hs
        exact (hwp (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
    have hsd' : (d : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
      simpa only [hsd] using hs
    rcases hrCases with hrd | hru₂ | hrp
    · have hrd' : (d : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hrd] using hr
      have heq := other_endpoint_eq_of_common_blocker K.hfour hw_v₁ hwp hrd' hsd'
      exact (hp_v₁ heq.symm).elim
    · have hru₂' : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hru₂] using hr
      have hv₁neg : turn (b : Point) (d : Point) (K.skeleton.v₁ : Point) < 0 := by
        have hbdc : turn (b : Point) (d : Point) (c : Point) < 0 := by
          rw [turn_swap_last]
          linarith [K.inside.2.1]
        exact turn_neg_of_between_nonpos
          (by simpa only [openSegment_symm] using K.skeleton.hv₁)
          hbdc (by simp)
      have hbdA : 0 < turn (b : Point) (d : Point) (a : Point) := by
        simpa only [turn_rotate] using K.inside.1
      have hv₃pos : 0 < turn (b : Point) (d : Point) (K.skeleton.v₃ : Point) :=
        edgeTurn_pos_of_mem_openSegment K.skeleton.hv₃ hbdA.le (by simp)
          (Or.inl hbdA)
      have hppos : 0 < turn (b : Point) (d : Point) (p : Point) :=
        edgeTurn_pos_of_mem_openSegment
          (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
          hv₃pos.le (le_of_eq (turn_eq_zero_of_between K.skeleton.hu₂).symm)
          (Or.inl hv₃pos)
      have hwpos := turn_pos_beyond_zero_from_neg
        (x := (K.skeleton.v₁ : Point)) (z := (K.skeleton.u₂ : Point))
        (y := (w : Point)) (by rw [openSegment_symm]; exact hru₂')
        hv₁neg (turn_eq_zero_of_between K.skeleton.hu₂)
      have hwneg := turn_neg_beyond_zero_from_pos
        (x := (p : Point)) (z := (d : Point)) (y := (w : Point))
        (by rw [openSegment_symm]; exact hsd') hppos (by simp)
      linarith
    · have hpBetween : (p : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₁ : Point) := by simpa only [hrp] using hr
      have hdNested := openSegment_left_nested hsd' hpBetween
      have hdZero := turn_eq_zero_of_between hdNested
      rcases point_eq_of_on_full_line K.hfour hw_v₁ hpBetween hdZero with
        hdw | hdv₁ | hdp
      · have hm : (w : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hdw] using hsd'
        exact (hwp (Subtype.ext
          ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim
      · have hm : (K.skeleton.v₁ : Point) ∈ openSegment ℝ
            (w : Point) (p : Point) := by simpa only [hdv₁] using hsd'
        exact not_two_mutual_openSegments (Subtype.val_injective.ne hw_v₁)
          ⟨hpBetween, hm⟩
      · have hm : (p : Point) ∈ openSegment ℝ (w : Point) (p : Point) := by
          simpa only [hdp] using hsd'
        exact (hwp (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))).elim

/-- Beam pair `(v₂u₁, v₃u₂)`.  Splitting the first beam blocker
across the spoke `bd`, the negative side forces `u₃` to block both the
beam-to-spoke pair and the boundary chord `v₁v₂`; the positive side is
excluded by signs. -/
theorem impossible_one_one_beams_A_E
    {w p : P} (hw : w ∈ K.I₂) (hp : p ∈ K.I₃)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₂u₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₁ := by
    intro h
    apply H₃.remaining_colour_ne
    calc
      colour (K.T₃.side 2) = colour K.skeleton.u₁ := by
        simp only [K.T₃_side_two]
      _ = colour K.skeleton.u₂ := h.symm
      _ = colour K.skeleton.v₃ := by
        simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
      _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero]
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    intro h
    apply H₂.remaining_colour_ne
    calc
      colour (K.T₂.side 2) = colour K.skeleton.u₃ := by
        simp only [K.T₂_side_two]
      _ = colour K.skeleton.u₁ := h.symm
      _ = colour K.skeleton.v₂ := by
        simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm
      _ = colour (K.T₂.side 0) := by simp only [K.T₂_side_zero]
  have hu₃u₂ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₂ :=
    hpair₁ (i := 1) (j := 2) (by decide)
  have hwu₂ : colour w = colour K.skeleton.u₂ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      hu₂u₁ hu₁u₃ hu₃u₂
    rcases hcases with h | h | h
    · exact h
    · exact (H₂.p_colour_ne 1 (by simpa using h)).elim
    · exact (H₂.p_colour_ne 2 (by simpa using h)).elim
  have hpu₃ : colour p = colour K.skeleton.u₃ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hp))
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      hu₂u₁ hu₁u₃ hu₃u₂
    rcases hcases with h | h | h
    · exact (H₃.p_colour_ne 1 (by simpa using h)).elim
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
    · exact h
  have hv₁v₂ : colour K.skeleton.v₁ = colour K.skeleton.v₂ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 3)
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      hu₂u₁ hu₁u₃ hu₃u₂
    rcases hcases with h | h | h
    · exact (hpair₁ (i := 0) (j := 2) (by decide) (by simpa using h)).elim
    · calc
        colour K.skeleton.v₁ = colour K.skeleton.u₁ := h
        _ = colour K.skeleton.v₂ := by
          simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm
    · exact (hpair₁ (i := 0) (j := 1) (by decide) (by simpa using h)).elim
  have hw_u₂ : w ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
  have hw_v₂ : w ≠ K.skeleton.v₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4
  have hw_v₃ : w ≠ K.skeleton.v₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5
  have hp_v₃ : p ≠ K.skeleton.v₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hp)) 5
  have hA := first_pair_points_do_not_block_second K.hfour
    (K.skeleton_ne 4 0 (by decide)) hw_u₂
    hw_v₂.symm (K.skeleton_ne 4 1 (by decide))
    (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
    (K.skeleton_ne 0 1 (by decide))
    (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
  obtain ⟨r, hr⟩ := K.proper w K.skeleton.u₂ hw_u₂ hwu₂
  have hrCases : r = d ∨ r = K.skeleton.u₃ := by
    have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (w : Point) := strict_cell_strict_outer K.inside
          (Or.inr (Or.inl (K.mem_I₂.mp hw)))
    rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 1) hr with
      hrd | hru₁ | hru₂ | hru₃ | hr₁ | hr₂ | hr₃
    · exact Or.inl hrd
    · subst r; exact (hA.2 hr).elim
    · subst r
      exact (hw_u₂ (Subtype.ext
        ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hr))).elim
    · exact Or.inr hru₃
    · rw [hempty₁] at hr₁; simp at hr₁
    · have hrw := hunique₂ r hr₂
      subst r
      exact (hw_u₂ (Subtype.ext
        ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hr))).elim
    · have hrp := hunique₃ r hr₃
      have hpOn : (p : Point) ∈ openSegment ℝ
          (K.skeleton.u₂ : Point) (w : Point) := by
        simpa only [hrp, openSegment_symm] using hr
      have hpBeam : (p : Point) ∈ openSegment ℝ
          (K.skeleton.u₂ : Point) (K.skeleton.v₃ : Point) := by
        simpa only [K.T₃_side_zero, K.T₃_side_one, openSegment_symm]
          using H₃.beam_between
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 1 5 (by decide)) hw_u₂.symm hpBeam hpOn
      exact (hw_v₃ heq.symm).elim
  have hwne := K.turn_bd_ne_zero_of_mem_I₂ hw
  rcases lt_or_gt_of_ne hwne with hwneg | hwpos
  · have hrneg : turn (b : Point) (d : Point) (r : Point) < 0 :=
      turn_neg_of_between_nonpos hr hwneg
        (le_of_eq (turn_eq_zero_of_between K.skeleton.hu₂))
    have hru₃ : r = K.skeleton.u₃ := by
      rcases hrCases with hrd | hru₃
      · rw [hrd] at hrneg; simp at hrneg
      · exact hru₃
    have hu₃Interior : (K.skeleton.u₃ : Point) ∈
        openSegment ℝ (w : Point) (K.skeleton.u₂ : Point) := by
      simpa only [hru₃] using hr
    have hbda : 0 < turn (b : Point) (d : Point) (a : Point) := by
      simpa only [turn_rotate] using K.inside.1
    have hu₁pos : 0 < turn (b : Point) (d : Point) (K.skeleton.u₁ : Point) :=
      edgeTurn_pos_of_mem_openSegment K.skeleton.hu₁ hbda.le (by simp)
        (Or.inl hbda)
    have hv₂neg : turn (b : Point) (d : Point) (K.skeleton.v₂ : Point) < 0 :=
      turn_neg_of_right_of_negative_between_nonneg
        (by simpa only [K.T₂_side_zero, K.T₂_side_one, openSegment_symm]
          using H₂.beam_between)
        hu₁pos.le hwneg
    have hbdc : turn (b : Point) (d : Point) (c : Point) < 0 := by
      rw [turn_swap_last]
      linarith [K.inside.2.1]
    have hv₁neg : turn (b : Point) (d : Point) (K.skeleton.v₁ : Point) < 0 :=
      turn_neg_of_between_nonpos
        (by simpa only [openSegment_symm] using K.skeleton.hv₁)
        hbdc (by simp)
    have hv₃pos : 0 < turn (b : Point) (d : Point) (K.skeleton.v₃ : Point) :=
      edgeTurn_pos_of_mem_openSegment K.skeleton.hv₃ hbda.le (by simp)
        (Or.inl hbda)
    have hppos : 0 < turn (b : Point) (d : Point) (p : Point) :=
      edgeTurn_pos_of_mem_openSegment
        (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
        hv₃pos.le (le_of_eq (turn_eq_zero_of_between K.skeleton.hu₂).symm)
        (Or.inl hv₃pos)
    obtain ⟨s, hs⟩ := K.proper K.skeleton.v₁ K.skeleton.v₂
      (K.skeleton_ne 3 4 (by decide)) hv₁v₂
    have hsneg : turn (b : Point) (d : Point) (s : Point) < 0 :=
      turn_neg_of_between_nonpos hs hv₁neg hv₂neg.le
    have hBCA : 0 < turn (b : Point) (c : Point) (a : Point) := by
      rw [turn_rotate]
      exact turn_pos_of_strictlyInsideTriangle K.inside
    have hsRot := strictlyInside_between_adjacent_sides hBCA K.skeleton.hv₁
      (by simpa only [openSegment_symm] using K.skeleton.hv₂) hs
    have hsOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
        (s : Point) := ⟨hsRot.2.2, hsRot.1, hsRot.2.1⟩
    have hsu₃ : s = K.skeleton.u₃ := by
      rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
          K.inside K.skeleton s (strictlyInsideTriangle_mem_triangleHull hsOuter) with
        hsa | hsb | hsc | hsd | hsu₁ | hsu₂ | hsu₃ |
        hsv₁ | hsv₂ | hsv₃ | hs₁ | hs₂ | hs₃
      · exact ((strictlyInsideTriangle_ne_vertices hsOuter).1
          (congrArg Subtype.val hsa)).elim
      · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.1
          (congrArg Subtype.val hsb)).elim
      · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.2
          (congrArg Subtype.val hsc)).elim
      · rw [hsd] at hsneg; simp at hsneg
      · rw [hsu₁] at hsneg; linarith
      · rw [hsu₂, turn_eq_zero_of_between K.skeleton.hu₂] at hsneg
        linarith
      · exact hsu₃
      · rw [hsv₁] at hsOuter
        linarith [hsOuter.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
      · rw [hsv₂] at hsOuter
        have hz := turn_eq_zero_of_between K.skeleton.hv₂
        rw [turn_swap_first] at hz
        linarith [hsOuter.2.2, hz]
      · rw [hsv₃] at hsOuter
        linarith [hsOuter.1, turn_eq_zero_of_between K.skeleton.hv₃]
      · have hsI₁ := K.mem_I₁.mpr hs₁
        rw [hempty₁] at hsI₁; simp at hsI₁
      · have hsw := hunique₂ s (K.mem_I₂.mpr hs₂)
        have hwOn : (w : Point) ∈ openSegment ℝ
            (K.skeleton.v₂ : Point) (K.skeleton.v₁ : Point) := by
          simpa only [hsw, openSegment_symm] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.skeleton_ne 4 3 (by decide)) (K.skeleton_ne 4 0 (by decide))
          hwOn
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
        exact (K.skeleton_ne 3 0 (by decide) heq).elim
      · have hsp := hunique₃ s (K.mem_I₃.mpr hs₃)
        rw [hsp] at hsneg
        linarith
    exact K.u₃_cannot_block_both_exceptional_pairs
      (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
      (by simpa only [hsu₃] using hs) hu₃Interior
  · have hrpos : 0 < turn (b : Point) (d : Point) (r : Point) :=
      edgeTurn_pos_of_mem_openSegment hr hwpos.le
        (le_of_eq (turn_eq_zero_of_between K.skeleton.hu₂).symm)
        (Or.inl hwpos)
    have hbdc : turn (b : Point) (d : Point) (c : Point) < 0 := by
      rw [turn_swap_last]
      linarith [K.inside.2.1]
    have hu₃neg : turn (b : Point) (d : Point) (K.skeleton.u₃ : Point) < 0 :=
      turn_neg_of_between_nonpos K.skeleton.hu₃ hbdc (by simp)
    rcases hrCases with hrd | hru₃
    · rw [hrd] at hrpos; simp at hrpos
    · rw [hru₃] at hrpos
      linarith

/-- Complete elimination of the `(0,1,1)` cell distribution. -/
theorem impossible_I₁_zero_I₂_one_I₃_one
    (h₁ : K.I₁.card = 0) (h₂ : K.I₂.card = 1)
    (h₃ : K.I₃.card = 1) : False := by
  have hempty₁ : K.I₁ = ∅ := Finset.card_eq_zero.mp h₁
  obtain ⟨w, hwSet⟩ := Finset.card_eq_one.mp h₂
  obtain ⟨p, hpSet⟩ := Finset.card_eq_one.mp h₃
  have hw : w ∈ K.I₂ := by rw [hwSet]; simp
  have hp : p ∈ K.I₃ := by rw [hpSet]; simp
  have hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w := by
    intro z hz
    rw [hwSet] at hz
    simpa using hz
  have hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p := by
    intro z hz
    rw [hpSet] at hz
    simpa using hz
  have H₂ := K.M₂.one_interior_pattern K.hfour (K.mem_I₂.mp hw)
    (fun z hz ↦ hunique₂ z (K.mem_I₂.mpr hz))
  have H₃ := K.M₃.one_interior_pattern K.hfour (K.mem_I₃.mp hp)
    (fun z hz ↦ hunique₃ z (K.mem_I₃.mpr hz))
  rcases H₂ with H₂ | H₂ | H₂ <;> rcases H₃ with H₃ | H₃ | H₃
  · exact K.impossible_one_one_beams_A_E hw hp hunique₂ hunique₃ hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_A_F hw hp hunique₂ hunique₃ hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_A_D hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_C_E hw hp hunique₂ hunique₃ hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_C_F hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_C_D hw hp hunique₂ hunique₃ hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_B_E hw hp hunique₂ hunique₃ hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_B_F hw hp hunique₂ hunique₃ hempty₁ H₂ H₃
  · exact K.impossible_one_one_beams_B_D hw hp hunique₂ hunique₃ hempty₁ H₂ H₃

/-- In the `(0,1,2)` distribution, beam pair `(v₂u₁,v₃u₁)`
already gives four points of one nonred colour in the outer triangle. -/
theorem impossible_one_two_beams_A_D
    {w p q : P} (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 2 0 1) : False := by
  have hpair := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  obtain ⟨l, hcolour⟩ := colour_eq_some_side K.T₁ hpair K.skeleton.v₂
    (K.skeleton.blocker_colour_ne 4)
  let y := K.T₁.side l
  have hv₂y : K.skeleton.v₂ ≠ y := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_ne 4 3 (by decide)
    · simpa using K.skeleton_ne 4 2 (by decide)
    · simpa using K.skeleton_ne 4 1 (by decide)
  have hu₁y : K.skeleton.u₁ ≠ y := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_ne 0 3 (by decide)
    · simpa using K.skeleton_ne 0 2 (by decide)
    · simpa using K.skeleton_ne 0 1 (by decide)
  have hv₃y : K.skeleton.v₃ ≠ y := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_ne 5 3 (by decide)
    · simpa using K.skeleton_ne 5 2 (by decide)
    · simpa using K.skeleton_ne 5 1 (by decide)
  have hyHull : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    dsimp [y]
    fin_cases l
    · simpa using K.skeleton_mem_outer 3
    · simpa using K.skeleton_mem_outer 2
    · simpa using K.skeleton_mem_outer 1
  apply four_same_colour_card_contradiction
      (x₀ := K.skeleton.v₂) (x₁ := K.skeleton.u₁)
      (x₂ := K.skeleton.v₃) (x₃ := y)
      (red := colour a)
    (K.skeleton_ne 4 0 (by decide))
    (K.skeleton_ne 4 5 (by decide)) hv₂y
    (K.skeleton_ne 0 5 (by decide)) hu₁y hv₃y
    (K.skeleton_mem_outer 4) (K.skeleton_mem_outer 0)
    (K.skeleton_mem_outer 5) hyHull
    (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm)
    (by
      calc
        colour K.skeleton.v₃ = colour K.skeleton.u₁ := by
          simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour.symm
        _ = colour K.skeleton.v₂ := by
          simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm)
    (by simpa [y] using hcolour.symm)
    (K.skeleton.blocker_colour_ne 4)
    (K.otherColourBound _ (K.skeleton.blocker_colour_ne 4))

/-- In the `(0,1,2)` distribution, beam pair `(u₁u₃,u₁u₂)`
leaves the equal-coloured chord `u₂u₃` in the empty first cell. -/
theorem impossible_one_two_beams_C_F
    {w p q : P} (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 1 2 0) : False := by
  have hcolour : colour K.skeleton.u₂ = colour K.skeleton.u₃ := by
    calc
      colour K.skeleton.u₂ = colour K.skeleton.u₁ := by
        simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_colour
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
  obtain ⟨r, hr⟩ := K.proper K.skeleton.u₂ K.skeleton.u₃
    (K.skeleton_ne 1 2 (by decide)) hcolour
  have hrI : r ∈ K.I₁ := K.mem_I₁.mpr
    (K.T₁.strict_of_between_distinct_sides (i := 2) (j := 1)
      (by decide) (by simpa only [K.T₁_side_two, K.T₁_side_one] using hr))
  rw [hempty₁] at hrI
  simp at hrI

/-- Beam pair `(v₂u₃,u₁u₂)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_B_F
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 1 2 0) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne
  have hu₃w : colour K.skeleton.u₃ ≠ colour w :=
    (H₂.p_colour_ne 2).symm
  have hwu₁ : colour w ≠ colour K.skeleton.u₁ := H₂.p_colour_ne 1
  have hpCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₃ p H₃.hp)
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 2)
    (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
    hu₁u₃ hu₃w hwu₁
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · rcases hpCases with hpu₁ | hpu₃ | hpwColour
    · exact (H₃.p_colour_ne_beam (by
        calc
          colour p = colour K.skeleton.u₁ := hpu₁
          _ = colour K.skeleton.u₂ := by
            simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_colour.symm
          _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one])).elim
    · have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      have hq_u₃ : q ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
      have hsec := K.two_secondary_line_excludes H₃ hp_u₃ hq_u₃ (by
        intro l
        fin_cases l
        · simpa using K.skeleton_ne 2 5 (by decide)
        · simpa using K.skeleton_ne 2 1 (by decide)
        · simpa using K.skeleton_ne 2 0 (by decide))
      have hbeam := first_pair_points_do_not_block_second K.hfour
        (K.skeleton_ne 1 0 (by decide)) hp_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
        (K.skeleton_ne 1 2 (by decide))
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
        (K.skeleton_ne 0 2 (by decide))
        (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
      obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      rcases K.portal_three_to_two hpI hpneg
          (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
        hrI₃ | hru₁ | hrI₂
      · rcases hunique₃ r hrI₃ with hrp | hrq
        · exact hp_u₃ (by simpa [hrp] using hr)
        · exact hsec.1 (by simpa [hrq] using hr)
      · exact hbeam.2 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        have hwOn : (w : Point) ∈ openSegment ℝ
            (K.skeleton.u₃ : Point) (p : Point) := by
          simpa only [hrw, openSegment_symm] using hr
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
          (by simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
          hwOn
        exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4 heq.symm).elim
    · have hpw : p ≠ w := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
          hw (e ▸ hpI)
      have hqw : q ≠ w := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
          hw (e ▸ hqI)
      have hsec := K.two_secondary_line_excludes H₃ hpw hqw (by
        intro l
        exact K.cellPoint_ne_T₃_side (Or.inr (Or.inl hw)) l)
      have hbeam := first_pair_points_do_not_block_second K.hfour
        (K.skeleton_ne 1 0 (by decide)) hpw
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
        (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1).symm
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
        (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
        (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
      obtain ⟨r, hr⟩ := K.proper p w hpw hpwColour
      rcases K.portal_three_to_two hpI hpneg
          (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
        hrI₃ | hru₁ | hrI₂
      · rcases hunique₃ r hrI₃ with hrp | hrq
        · exact hpw (by simpa [hrp] using hr)
        · exact hsec.1 (by simpa [hrq] using hr)
      · exact hbeam.2 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        exact hpw (by simpa [hrw] using hr)
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Beam pair `(v₂u₃,v₃u₂)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_B_E
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 0 1 2) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne
  have hu₃w : colour K.skeleton.u₃ ≠ colour w :=
    (H₂.p_colour_ne 2).symm
  have hwu₁ : colour w ≠ colour K.skeleton.u₁ := H₂.p_colour_ne 1
  have hu₂u₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₁ := by
    intro h
    have hkBeam : colour (K.T₃.side 2) = colour (K.T₃.side 0) := by
      calc
        colour (K.T₃.side 2) = colour K.skeleton.u₁ := by simp only [K.T₃_side_two]
        _ = colour K.skeleton.u₂ := h.symm
        _ = colour K.skeleton.v₃ := by
          simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
        _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero]
    rcases H₃.secondary with hsec | hsec
    · exact H₃.p_colour_ne_beam (hsec.1.trans hkBeam)
    · exact H₃.q_colour_ne_beam (hsec.1.trans hkBeam)
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ :=
    hpair₁ (i := 2) (j := 1) (by decide)
  have hu₂w : colour K.skeleton.u₂ = colour w := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
      hu₁u₃ hu₃w hwu₁
    rcases hcases with h | h | h
    · exact (hu₂u₁ h).elim
    · exact (hu₂u₃ h).elim
    · exact h
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
      have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
        have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
          rw [← turn_rotate]
          exact K.inside.2.2
        rw [turn_swap_first] at h
        linarith
      exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    rcases H₃.secondary with hsec | hsec
    · have hqu₃ : colour q = colour K.skeleton.u₃ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ q H₃.hq)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 2)
          (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
          hu₁u₃ hu₃w hwu₁
        rcases hcases with h | h | h
        · exact (H₃.interior_colour_ne (calc
            colour p = colour (K.T₃.side 2) := hsec.1
            _ = colour K.skeleton.u₁ := by simp only [K.T₃_side_two]
            _ = colour q := h.symm)).elim
        · exact h
        · exact (H₃.q_colour_ne_beam (calc
            colour q = colour w := h
            _ = colour K.skeleton.u₂ := hu₂w.symm
            _ = colour K.skeleton.v₃ := by
              simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
            _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero])).elim
      have hqneg := turn_neg_of_between_nonpos
        (by simpa only [K.T₃_side_two] using hsec.2) hpneg hu₁neg.le
      have hq_u₃ : q ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
      have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      have hline := first_pair_points_do_not_block_second K.hfour
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0) hq_u₃
        H₃.hpq hp_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
        (K.skeleton_ne 0 2 (by decide))
        (by simpa only [K.T₃_side_two] using hsec.2)
      obtain ⟨r, hr⟩ := K.proper q K.skeleton.u₃ hq_u₃ hqu₃
      rcases K.portal_three_to_two hqI hqneg
          (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
        hrI₃ | hru₁ | hrI₂
      · rcases hunique₃ r hrI₃ with hrp | hrq
        · exact hline.1 (by simpa [hrp] using hr)
        · exact hq_u₃ (by simpa [hrq] using hr)
      · exact hline.2 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        have hwOn : (w : Point) ∈ openSegment ℝ
            (K.skeleton.u₃ : Point) (q : Point) := by
          simpa only [hrw, openSegment_symm] using hr
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.skeleton_ne 2 4 (by decide)) hq_u₃.symm
          (by simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
          hwOn
        exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4 heq.symm).elim
    · have hpu₃ : colour p = colour K.skeleton.u₃ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ p H₃.hp)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 2)
          (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
          hu₁u₃ hu₃w hwu₁
        rcases hcases with h | h | h
        · exact (H₃.interior_colour_ne (calc
            colour p = colour K.skeleton.u₁ := h
            _ = colour (K.T₃.side 2) := by simp only [K.T₃_side_two]
            _ = colour q := hsec.1.symm)).elim
        · exact h
        · exact (H₃.p_colour_ne_beam (calc
            colour p = colour w := h
            _ = colour K.skeleton.u₂ := hu₂w.symm
            _ = colour K.skeleton.v₃ := by
              simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
            _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero])).elim
      have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      have hq_u₃ : q ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
      have hline := first_pair_points_do_not_block_second K.hfour
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0) hp_u₃
        H₃.hpq.symm hq_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
        (K.skeleton_ne 0 2 (by decide))
        (by simpa only [K.T₃_side_two] using hsec.2)
      obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      rcases K.portal_three_to_two hpI hpneg
          (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
        hrI₃ | hru₁ | hrI₂
      · rcases hunique₃ r hrI₃ with hrp | hrq
        · exact hp_u₃ (by simpa [hrp] using hr)
        · exact hline.1 (by simpa [hrq] using hr)
      · exact hline.2 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        have hwOn : (w : Point) ∈ openSegment ℝ
            (K.skeleton.u₃ : Point) (p : Point) := by
          simpa only [hrw, openSegment_symm] using hr
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
          (by simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
          hwOn
        exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4 heq.symm).elim
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Beam pair `(u₁u₃,v₃u₁)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_C_D
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 2 0 1) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    intro h
    apply hpair₁ (i := 1) (j := 2) (by decide)
    calc
      colour (K.T₁.side 1) = colour K.skeleton.u₃ := by simp only [K.T₁_side_one]
      _ = colour K.skeleton.u₁ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour.symm
      _ = colour K.skeleton.u₂ := h
      _ = colour (K.T₁.side 2) := by simp only [K.T₁_side_two]
  have hu₂v₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.v₁ :=
    hpair₁ (i := 2) (j := 0) (by decide)
  have hv₁u₁ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₁ := by
    intro h
    apply hpair₁ (i := 0) (j := 1) (by decide)
    calc
      colour (K.T₁.side 0) = colour K.skeleton.v₁ := by simp only [K.T₁_side_zero]
      _ = colour K.skeleton.u₁ := h
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour (K.T₁.side 1) := by simp only [K.T₁_side_one]
  have hwCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 1)
    (K.skeleton.blocker_colour_ne 3)
    hu₁u₂ hu₂v₁ hv₁u₁
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · rcases hwCases with hwu₁ | hwu₂ | hwv₁
    · exact (H₂.p_colour_ne 1 (by simpa using hwu₁)).elim
    · have hw_u₂ : w ≠ K.skeleton.u₂ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
      obtain ⟨r, hr⟩ := K.proper w K.skeleton.u₂ hw_u₂ hwu₂
      have hcenter := K.red_center_strictly_inside_spoke_triangle
      have hrCentral : StrictlyInsideTriangle
          (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
          (K.skeleton.u₃ : Point) (r : Point) :=
        strictlyInside_between_vertex_and_opposite_side
          (turn_pos_of_strictlyInsideTriangle hcenter)
          (by
            rw [openSegment_symm]
            simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
          hr
      have hpCentralNeg : turn (K.skeleton.u₁ : Point)
          (K.skeleton.u₂ : Point) (p : Point) < 0 :=
        turn_neg_of_between_nonpos
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
          K.v₃_spoke_side_neg (by simp)
      have hqCentralNeg : turn (K.skeleton.u₁ : Point)
          (K.skeleton.u₂ : Point) (q : Point) < 0 := by
        rcases H₃.secondary with hsec | hsec
        · exact turn_neg_of_between_nonpos
            (by simpa only [K.T₃_side_one] using hsec.2)
            hpCentralNeg (by simp)
        · exact turn_neg_of_right_of_negative_between_nonneg
            (by
              rw [openSegment_symm]
              simpa only [K.T₃_side_one] using hsec.2)
            (by simp) hpCentralNeg
      have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
          (w : Point) := strict_cell_strict_outer K.inside
            (Or.inr (Or.inl (K.mem_I₂.mp hw)))
      have hrOuter := strict_outer_of_between_strict_hull
        (turn_pos_of_strictlyInsideTriangle K.inside) hwOuter
        (K.skeleton_mem_outer 1) hr
      have hrd : r = d := by
        rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
            K.inside K.skeleton r
            (strictlyInsideTriangle_mem_triangleHull hrOuter) with
          hra | hrb | hrc | hrd | hru₁ | hru₂ | hru₃ |
          hrv₁ | hrv₂ | hrv₃ | hr₁ | hr₂ | hr₃
        · exact ((strictlyInsideTriangle_ne_vertices hrOuter).1
            (congrArg Subtype.val hra)).elim
        · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.1
            (congrArg Subtype.val hrb)).elim
        · exact ((strictlyInsideTriangle_ne_vertices hrOuter).2.2
            (congrArg Subtype.val hrc)).elim
        · exact hrd
        · exact ((strictlyInsideTriangle_ne_vertices hrCentral).1
            (congrArg Subtype.val hru₁)).elim
        · exact ((strictlyInsideTriangle_ne_vertices hrCentral).2.1
            (congrArg Subtype.val hru₂)).elim
        · exact ((strictlyInsideTriangle_ne_vertices hrCentral).2.2
            (congrArg Subtype.val hru₃)).elim
        · rw [hrv₁] at hrCentral
          linarith [hrCentral.2.1, K.v₁_spoke_side_neg]
        · rw [hrv₂] at hrCentral
          linarith [hrCentral.2.2, K.v₂_spoke_side_neg]
        · rw [hrv₃] at hrCentral
          linarith [hrCentral.1, K.v₃_spoke_side_neg]
        · have hrI := K.mem_I₁.mpr hr₁
          rw [hempty₁] at hrI; simp at hrI
        · have hrw := hunique₂ r (K.mem_I₂.mpr hr₂)
          subst r
          exact (hw_u₂ (Subtype.ext
            ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hr))).elim
        · rcases hunique₃ r (K.mem_I₃.mpr hr₃) with hrp | hrq
          · rw [hrp] at hrCentral
            linarith [hrCentral.1, hpCentralNeg]
          · rw [hrq] at hrCentral
            linarith [hrCentral.1, hqCentralNeg]
      have hb_u₂ : b ≠ K.skeleton.u₂ := by
        intro e
        have hm : (b : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
          simpa only [e] using K.skeleton.hu₂
        exact K.hbd (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
      have hd_u₂ : d ≠ K.skeleton.u₂ := by
        intro e
        have hm : (d : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
          simpa only [e] using K.skeleton.hu₂
        exact K.hbd (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
      have hb_w : b ≠ w := by
        intro e
        exact (strictlyInsideTriangle_ne_vertices hwOuter).2.1
          (congrArg Subtype.val e.symm)
      have hd_w : d ≠ w := by
        intro e
        exact (strictlyInsideTriangle_ne_vertices (K.mem_I₂.mp hw)).2.2
          (congrArg Subtype.val e.symm)
      have hbd := first_pair_points_do_not_block_second K.hfour K.hbd hw_u₂.symm
        hb_u₂ hb_w hd_u₂ hd_w K.skeleton.hu₂
      exact hbd.2 (by simpa only [openSegment_symm, hrd] using hr)
    · have hwp : w ≠ p := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
      have hwq : w ≠ q := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hqI)
      rcases H₃.secondary with hsec | hsec
      · have hqv₁ : colour q = colour K.skeleton.v₁ := by
          have hcases := fin4_eq_one_of_three_of_avoid
            (K.interior_colour_ne_red₃ q H₃.hq)
            (K.skeleton.blocker_colour_ne 0)
            (K.skeleton.blocker_colour_ne 1)
            (K.skeleton.blocker_colour_ne 3)
            hu₁u₂ hu₂v₁ hv₁u₁
          rcases hcases with h | h | h
          · exact (H₃.q_colour_ne_beam (by
              simpa only [K.T₃_side_two] using h)).elim
          · exact (H₃.interior_colour_ne (by
              calc
                colour p = colour (K.T₃.side 1) := hsec.1
                _ = colour K.skeleton.u₂ := by simp only [K.T₃_side_one]
                _ = colour q := h.symm)).elim
          · exact h
        have hqne := K.turn_cd_ne_zero_of_mem_I₃ hqI
        rcases lt_or_gt_of_ne hqne with hqneg | hqpos
        · have hline := first_pair_points_do_not_block_second K.hfour
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1) hwq.symm
            H₃.hpq hwp.symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 1).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1).symm
            (by simpa only [K.T₃_side_one] using hsec.2)
          have hwline := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 0 2 (by decide)) hwq
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2).symm
            (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
          obtain ⟨r, hr⟩ := K.proper q w hwq.symm (hqv₁.trans hwv₁.symm)
          rcases K.portal_three_to_two hqI hqneg
              (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
            hrI₃ | hru₁ | hrI₂
          · rcases hunique₃ r hrI₃ with hrp | hrq
            · exact hline.1 (by simpa [hrp] using hr)
            · exact hwq.symm (by simpa [hrq] using hr)
          · exact hwline.1 (by simpa only [hru₁, openSegment_symm] using hr)
          · have hrw := hunique₂ r hrI₂
            exact hwq.symm (by simpa [hrw] using hr)
        · have hline := first_pair_points_do_not_block_second K.hfour
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1)
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3)
            H₃.hpq (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 3)
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 1).symm
            (K.skeleton_ne 1 3 (by decide))
            (by simpa only [K.T₃_side_one] using hsec.2)
          obtain ⟨r, hr⟩ := K.proper q K.skeleton.v₁
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3) hqv₁
          rcases K.portal_three_to_one hqI hqpos
              (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 0).property) hr with
            hrI₃ | hru₂ | hrI₁
          · rcases hunique₃ r hrI₃ with hrp | hrq
            · exact hline.1 (by simpa [hrp] using hr)
            · exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3
                (by simpa [hrq] using hr)).elim
          · exact hline.2 (by simpa [hru₂] using hr)
          · rw [hempty₁] at hrI₁; simp at hrI₁
      · have hpv₁ : colour p = colour K.skeleton.v₁ := by
          have hcases := fin4_eq_one_of_three_of_avoid
            (K.interior_colour_ne_red₃ p H₃.hp)
            (K.skeleton.blocker_colour_ne 0)
            (K.skeleton.blocker_colour_ne 1)
            (K.skeleton.blocker_colour_ne 3)
            hu₁u₂ hu₂v₁ hv₁u₁
          rcases hcases with h | h | h
          · exact (H₃.p_colour_ne_beam (by
              simpa only [K.T₃_side_two] using h)).elim
          · exact (H₃.interior_colour_ne (by
              calc
                colour p = colour K.skeleton.u₂ := h
                _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one]
                _ = colour q := hsec.1.symm)).elim
          · exact h
        have hsecLine := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 1) hwp.symm
          H₃.hpq.symm hwq.symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1).symm
          (by simpa only [K.T₃_side_one] using hsec.2)
        have hbeamLine := first_pair_points_do_not_block_second K.hfour
          (K.skeleton_ne 0 5 (by decide)) hwp.symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5).symm
          (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
        obtain ⟨r, hr⟩ := K.proper p w hwp.symm (hpv₁.trans hwv₁.symm)
        rcases K.portal_three_to_two hpI hpneg
            (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
          hrI₃ | hru₁ | hrI₂
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact hwp.symm (by simpa [hrp] using hr)
          · exact hsecLine.1 (by simpa [hrq] using hr)
        · exact hbeamLine.1 (by simpa [hru₁] using hr)
        · have hrw := hunique₂ r hrI₂
          exact hwp.symm (by simpa [hrw] using hr)
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Beam pair `(v₂u₃,v₃u₁)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_B_D
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 2 0 1) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne
  have hu₃w : colour K.skeleton.u₃ ≠ colour w :=
    (H₂.p_colour_ne 2).symm
  have hwu₁ : colour w ≠ colour K.skeleton.u₁ := H₂.p_colour_ne 1
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ :=
    hpair₁ (i := 2) (j := 1) (by decide)
  have hu₂u₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₁ := by
    intro h
    have hkBeam : colour (K.T₃.side 1) = colour (K.T₃.side 2) := by
      calc
        colour (K.T₃.side 1) = colour K.skeleton.u₂ := by simp only [K.T₃_side_one]
        _ = colour K.skeleton.u₁ := h
        _ = colour (K.T₃.side 2) := by simp only [K.T₃_side_two]
    rcases H₃.secondary with hsec | hsec
    · exact H₃.p_colour_ne_beam
        (hsec.1.trans hkBeam)
    · exact H₃.q_colour_ne_beam
        (hsec.1.trans hkBeam)
  have hu₂w : colour K.skeleton.u₂ = colour w := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
      hu₁u₃ hu₃w hwu₁
    rcases hcases with h | h | h
    · exact (hu₂u₁ h).elim
    · exact (hu₂u₃ h).elim
    · exact h
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · rcases H₃.secondary with hsec | hsec
    · have hqu₃ : colour q = colour K.skeleton.u₃ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ q H₃.hq)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 1)
          (K.skeleton.blocker_colour_ne 2)
          hu₂u₁.symm hu₂u₃ hu₁u₃.symm
        rcases hcases with h | h | h
        · exact (H₃.q_colour_ne_beam (by
              simpa only [K.T₃_side_two] using h)).elim
        · exact (H₃.interior_colour_ne (by
              calc
                colour p = colour (K.T₃.side 1) := hsec.1
                _ = colour K.skeleton.u₂ := by simp only [K.T₃_side_one]
                _ = colour q := h.symm)).elim
        · exact h
      have hqne := K.turn_cd_ne_zero_of_mem_I₃ hqI
      rcases lt_or_gt_of_ne hqne with hqneg | hqpos
      · have forceU₁ {y r : P}
            (hy : y = K.skeleton.u₃ ∨ y = K.skeleton.v₂)
            (hr : (r : Point) ∈ openSegment ℝ (q : Point) (y : Point)) :
            r = K.skeleton.u₁ := by
          have hq_y : q ≠ y := by
            rcases hy with rfl | rfl
            · exact K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
            · exact K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4
          have hp_y : p ≠ y := by
            rcases hy with rfl | rfl
            · exact K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
            · exact K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4
          have hu₂_y : K.skeleton.u₂ ≠ y := by
            rcases hy with rfl | rfl
            · exact K.skeleton_ne 1 2 (by decide)
            · exact K.skeleton_ne 1 4 (by decide)
          have hline := first_pair_points_do_not_block_second K.hfour
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1) hq_y
            H₃.hpq hp_y
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 1).symm hu₂_y
            (by simpa only [K.T₃_side_one] using hsec.2)
          have hyHull : (y : Point) ∈ triangleHull (c : Point) (a : Point) (d : Point) := by
            rcases hy with rfl | rfl
            · exact K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property
            · exact K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property
          rcases K.portal_three_to_two hqI hqneg hyHull hr with hrI₃ | hru₁ | hrI₂
          · rcases hunique₃ r hrI₃ with hrp | hrq
            · exact (hline.1 (by simpa [hrp] using hr)).elim
            · exact (hq_y (by simpa [hrq] using hr)).elim
          · exact hru₁
          · have hrw := hunique₂ r hrI₂
            rcases hy with rfl | rfl
            · have hwOn : (w : Point) ∈ openSegment ℝ
                  (K.skeleton.u₃ : Point) (q : Point) := by
                simpa only [hrw, openSegment_symm] using hr
              have heq := other_endpoint_eq_of_common_blocker K.hfour
                (K.skeleton_ne 2 4 (by decide))
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2).symm
                (by simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
                hwOn
              exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4 heq.symm).elim
            · have hwOn : (w : Point) ∈ openSegment ℝ
                  (K.skeleton.v₂ : Point) (q : Point) := by
                simpa only [hrw, openSegment_symm] using hr
              have heq := other_endpoint_eq_of_common_blocker K.hfour
                (K.skeleton_ne 4 2 (by decide))
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4).symm
                (by
                  rw [openSegment_symm]
                  simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
                hwOn
              exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2 heq.symm).elim
        obtain ⟨r, hr⟩ := K.proper q K.skeleton.u₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2) hqu₃
        have hru₁ := forceU₁ (Or.inl rfl) hr
        have hv₂u₃ : colour K.skeleton.v₂ = colour K.skeleton.u₃ := by
          simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_colour.symm
        obtain ⟨s, hs⟩ := K.proper q K.skeleton.v₂
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4)
          (hqu₃.trans hv₂u₃.symm)
        have hsu₁ := forceU₁ (Or.inr rfl) hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2)
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4)
          (by simpa [hru₁] using hr) (by simpa [hsu₁] using hs)
        exact (K.skeleton_ne 2 4 (by decide) heq).elim
      · have hline := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1)
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2)
          H₃.hpq (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2)
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 1).symm
          (K.skeleton_ne 1 2 (by decide))
          (by simpa only [K.T₃_side_one] using hsec.2)
        obtain ⟨r, hr⟩ := K.proper q K.skeleton.u₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2) hqu₃
        rcases K.portal_three_to_one hqI hqpos
            (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property) hr with
          hrI₃ | hru₂ | hrI₁
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact hline.1 (by simpa [hrp] using hr)
          · exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
              (by simpa [hrq] using hr)).elim
        · exact hline.2 (by simpa [hru₂] using hr)
        · rw [hempty₁] at hrI₁; simp at hrI₁
    · have hpu₃ : colour p = colour K.skeleton.u₃ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ p H₃.hp)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 1)
          (K.skeleton.blocker_colour_ne 2)
          hu₂u₁.symm hu₂u₃ hu₁u₃.symm
        rcases hcases with h | h | h
        · exact (H₃.p_colour_ne_beam (by
              simpa only [K.T₃_side_two] using h)).elim
        · exact (H₃.interior_colour_ne (by
              calc
                colour p = colour K.skeleton.u₂ := h
                _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one]
                _ = colour q := hsec.1.symm)).elim
        · exact h
      have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      have hsecLine := first_pair_points_do_not_block_second K.hfour
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 1) hp_u₃
        H₃.hpq.symm (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
        (K.skeleton_ne 1 2 (by decide))
        (by simpa only [K.T₃_side_one] using hsec.2)
      have hbeamLine := first_pair_points_do_not_block_second K.hfour
        (K.skeleton_ne 0 5 (by decide)) hp_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
        (K.skeleton_ne 0 2 (by decide))
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5).symm
        (K.skeleton_ne 5 2 (by decide))
        (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
      obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      rcases K.portal_three_to_two hpI hpneg
          (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
        hrI₃ | hru₁ | hrI₂
      · rcases hunique₃ r hrI₃ with hrp | hrq
        · exact hp_u₃ (by simpa [hrp] using hr)
        · exact hsecLine.1 (by simpa [hrq] using hr)
      · exact hbeamLine.1 (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        have hwOn : (w : Point) ∈ openSegment ℝ
            (K.skeleton.u₃ : Point) (p : Point) := by
          simpa only [hrw, openSegment_symm] using hr
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
          (by simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
          hwOn
        exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4 heq.symm).elim
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Beam pair `(u₁u₃,v₃u₂)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_C_E
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 0 1 2) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    intro h
    apply hpair₁ (i := 1) (j := 2) (by decide)
    calc
      colour (K.T₁.side 1) = colour K.skeleton.u₃ := by simp only [K.T₁_side_one]
      _ = colour K.skeleton.u₁ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour.symm
      _ = colour K.skeleton.u₂ := h
      _ = colour (K.T₁.side 2) := by simp only [K.T₁_side_two]
  have hu₂v₁ : colour K.skeleton.u₂ ≠ colour K.skeleton.v₁ :=
    hpair₁ (i := 2) (j := 0) (by decide)
  have hv₁u₁ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₁ := by
    intro h
    apply hpair₁ (i := 0) (j := 1) (by decide)
    calc
      colour (K.T₁.side 0) = colour K.skeleton.v₁ := by simp only [K.T₁_side_zero]
      _ = colour K.skeleton.u₁ := h
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour (K.T₁.side 1) := by simp only [K.T₁_side_one]
  have hwCases := fin4_eq_one_of_three_of_avoid
    (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
    (K.skeleton.blocker_colour_ne 0)
    (K.skeleton.blocker_colour_ne 1)
    (K.skeleton.blocker_colour_ne 3)
    hu₁u₂ hu₂v₁ hv₁u₁
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
      have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
        have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
          rw [← turn_rotate]
          exact K.inside.2.2
        rw [turn_swap_first] at h
        linarith
      exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    rcases H₃.secondary with hsec | hsec
    · have hqneg := turn_neg_of_between_nonpos
        (by simpa only [K.T₃_side_two] using hsec.2) hpneg hu₁neg.le
      have hqv₁ : colour q = colour K.skeleton.v₁ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ q H₃.hq)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 1)
          (K.skeleton.blocker_colour_ne 3)
          hu₁u₂ hu₂v₁ hv₁u₁
        rcases hcases with h | h | h
        · exact (H₃.interior_colour_ne (by
            calc
              colour p = colour (K.T₃.side 2) := hsec.1
              _ = colour K.skeleton.u₁ := by simp only [K.T₃_side_two]
              _ = colour q := h.symm)).elim
        · exact (H₃.q_colour_ne_beam (by
            calc
              colour q = colour K.skeleton.u₂ := h
              _ = colour K.skeleton.v₃ := by
                simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
              _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero])).elim
        · exact h
      rcases hwCases with hwu₁ | hwu₂ | hwv₁
      · exact (H₂.p_colour_ne 1 (by simpa using hwu₁)).elim
      · have hv₂v₁ : colour K.skeleton.v₂ = colour K.skeleton.v₁ := by
          have hcases := fin4_eq_one_of_three_of_avoid
            (K.skeleton.blocker_colour_ne 4)
            (K.skeleton.blocker_colour_ne 0)
            (K.skeleton.blocker_colour_ne 1)
            (K.skeleton.blocker_colour_ne 3)
            hu₁u₂ hu₂v₁ hv₁u₁
          rcases hcases with h | h | h
          · exact (H₂.remaining_colour_ne (by
              simpa only [K.T₂_side_zero, K.T₂_side_one] using h)).elim
          · exact (H₂.p_colour_ne 0 (by
              calc
                colour w = colour K.skeleton.u₂ := hwu₂
                _ = colour K.skeleton.v₂ := h.symm
                _ = colour (K.T₂.side 0) := by simp only [K.T₂_side_zero])).elim
          · exact h
        have hq_v₂ : q ≠ K.skeleton.v₂ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4
        have hp_v₂ : p ≠ K.skeleton.v₂ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4
        have hline := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0) hq_v₂
          H₃.hpq hp_v₂
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
          (K.skeleton_ne 0 4 (by decide))
          (by simpa only [K.T₃_side_two] using hsec.2)
        obtain ⟨r, hr⟩ := K.proper q K.skeleton.v₂ hq_v₂
          (hqv₁.trans hv₂v₁.symm)
        have hrw : r = w := by
          rcases K.portal_three_to_two hqI hqneg
              (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property) hr with
            hrI₃ | hru₁ | hrI₂
          · rcases hunique₃ r hrI₃ with hrp | hrq
            · exact (hline.1 (by simpa [hrp] using hr)).elim
            · exact (hq_v₂ (by simpa [hrq] using hr)).elim
          · exact (hline.2 (by simpa [hru₁] using hr)).elim
          · exact hunique₂ r hrI₂
        have hwv₂ : (w : Point) ∈ openSegment ℝ
            (q : Point) (K.skeleton.v₂ : Point) := by simpa [hrw] using hr
        have hw_v₃ : w ≠ K.skeleton.v₃ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5
        have hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0 :=
          turn_neg_of_right_of_negative_between_nonneg
            (by
              rw [openSegment_symm]
              simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
            (by
              have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
                simpa only [turn_rotate] using K.inside.2.1
              exact (edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hbcd.le (by simp)
                (Or.inl hbcd)).le)
            hpneg
        obtain ⟨s, hs⟩ := K.proper w K.skeleton.v₃ hw_v₃ (by
          calc
            colour w = colour K.skeleton.u₂ := hwu₂
            _ = colour K.skeleton.v₃ := by
              simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm)
        have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
            (w : Point) := strict_cell_strict_outer K.inside
              (Or.inr (Or.inl (K.mem_I₂.mp hw)))
        have hsneg := turn_neg_of_between_nonpos hs
          (K.turn_cd_neg_of_mem_I₂ hw) hv₃neg.le
        have hsCases : s = K.skeleton.u₁ ∨ s = p ∨ s = q := by
          rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 5) hs with
            hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
          · rw [hsd] at hsneg; simp at hsneg
          · exact Or.inl hsu₁
          · rw [hsu₂] at hsneg
            have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
              simpa only [turn_rotate] using K.inside.2.1
            have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
              hbcd.le (by simp) (Or.inl hbcd)
            linarith
          · rw [hsu₃, turn_eq_zero_of_between K.skeleton.hu₃] at hsneg
            linarith
          · rw [hempty₁] at hs₁; simp at hs₁
          · have hsw := hunique₂ s hs₂
            exact (hw_v₃ (by simpa [hsw] using hs)).elim
          · rcases hunique₃ s hs₃ with hsp | hsq
            · exact Or.inr (Or.inl hsp)
            · exact Or.inr (Or.inr hsq)
        have hu₁Not : (K.skeleton.u₁ : Point) ∉
            openSegment ℝ (w : Point) (K.skeleton.v₃ : Point) := by
          have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 0 2 (by decide)) hw_v₃
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
            (K.skeleton_ne 0 5 (by decide))
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
            (K.skeleton_ne 2 5 (by decide))
            (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
          exact hfull.1
        rcases hsCases with hsu₁ | hsp | hsq
        · exact hu₁Not (by simpa [hsu₁] using hs)
        · have hpOn : (p : Point) ∈ openSegment ℝ
              (K.skeleton.v₃ : Point) (w : Point) := by
            simpa only [hsp, openSegment_symm] using hs
          have heq := other_endpoint_eq_of_common_blocker K.hfour
            (K.skeleton_ne 5 1 (by decide)) hw_v₃.symm
            (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
            hpOn
          exact (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1 heq.symm).elim
        · have hwq : w ≠ q := by
            intro e
            exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
              hw (e.symm ▸ hqI)
          have hfull := first_pair_points_do_not_block_second K.hfour
            hq_v₂ hw_v₃ hwq.symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5)
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
            (K.skeleton_ne 4 5 (by decide)) hwv₂
          exact hfull.1 (by simpa only [hsq] using hs)
      · have hqw : q ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hqI)
        have hwp : p ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
        have hline := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0) hqw
          H₃.hpq hwp
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (by simpa only [K.T₃_side_two] using hsec.2)
        obtain ⟨r, hr⟩ := K.proper q w hqw (hqv₁.trans hwv₁.symm)
        rcases K.portal_three_to_two hqI hqneg
            (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
          hrI₃ | hru₁ | hrI₂
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact hline.1 (by simpa [hrp] using hr)
          · exact hqw (by simpa [hrq] using hr)
        · exact hline.2 (by simpa [hru₁] using hr)
        · have hrw := hunique₂ r hrI₂
          exact hqw (by simpa [hrw] using hr)
    · have hpv₁ : colour p = colour K.skeleton.v₁ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ p H₃.hp)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 1)
          (K.skeleton.blocker_colour_ne 3)
          hu₁u₂ hu₂v₁ hv₁u₁
        rcases hcases with h | h | h
        · exact (H₃.interior_colour_ne (by
            calc
              colour p = colour K.skeleton.u₁ := h
              _ = colour (K.T₃.side 2) := by simp only [K.T₃_side_two]
              _ = colour q := hsec.1.symm)).elim
        · exact (H₃.p_colour_ne_beam (by
            calc
              colour p = colour K.skeleton.u₂ := h
              _ = colour K.skeleton.v₃ := by
                simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
              _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero])).elim
        · exact h
      rcases hwCases with hwu₁ | hwu₂ | hwv₁
      · exact (H₂.p_colour_ne 1 (by simpa using hwu₁)).elim
      · have hv₂v₁ : colour K.skeleton.v₂ = colour K.skeleton.v₁ := by
          have hcases := fin4_eq_one_of_three_of_avoid
            (K.skeleton.blocker_colour_ne 4)
            (K.skeleton.blocker_colour_ne 0)
            (K.skeleton.blocker_colour_ne 1)
            (K.skeleton.blocker_colour_ne 3)
            hu₁u₂ hu₂v₁ hv₁u₁
          rcases hcases with h | h | h
          · exact (H₂.remaining_colour_ne (by
              simpa only [K.T₂_side_zero, K.T₂_side_one] using h)).elim
          · exact (H₂.p_colour_ne 0 (by
              calc
                colour w = colour K.skeleton.u₂ := hwu₂
                _ = colour K.skeleton.v₂ := h.symm
                _ = colour (K.T₂.side 0) := by simp only [K.T₂_side_zero])).elim
          · exact h
        have hp_v₂ : p ≠ K.skeleton.v₂ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4
        have hq_v₂ : q ≠ K.skeleton.v₂ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4
        have hline := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0) hp_v₂
          H₃.hpq.symm hq_v₂
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
          (K.skeleton_ne 0 4 (by decide))
          (by simpa only [K.T₃_side_two] using hsec.2)
        obtain ⟨r, hr⟩ := K.proper p K.skeleton.v₂ hp_v₂
          (hpv₁.trans hv₂v₁.symm)
        have hrw : r = w := by
          rcases K.portal_three_to_two hpI hpneg
              (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 0).property) hr with
            hrI₃ | hru₁ | hrI₂
          · rcases hunique₃ r hrI₃ with hrp | hrq
            · exact (hp_v₂ (by simpa [hrp] using hr)).elim
            · exact (hline.1 (by simpa [hrq] using hr)).elim
          · exact (hline.2 (by simpa [hru₁] using hr)).elim
          · exact hunique₂ r hrI₂
        have hwv₂ : (w : Point) ∈ openSegment ℝ
            (p : Point) (K.skeleton.v₂ : Point) := by simpa [hrw] using hr
        have hw_v₃ : w ≠ K.skeleton.v₃ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5
        obtain ⟨s, hs⟩ := K.proper w K.skeleton.v₃ hw_v₃ (by
          calc
            colour w = colour K.skeleton.u₂ := hwu₂
            _ = colour K.skeleton.v₃ := by
              simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm)
        have hsCases : s = q := by
          have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
              (w : Point) := strict_cell_strict_outer K.inside
                (Or.inr (Or.inl (K.mem_I₂.mp hw)))
          have hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0 :=
            turn_neg_of_right_of_negative_between_nonneg
              (by
                rw [openSegment_symm]
                simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
              (by
                have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
                  simpa only [turn_rotate] using K.inside.2.1
                exact (edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hbcd.le (by simp)
                  (Or.inl hbcd)).le)
              hpneg
          have hsneg := turn_neg_of_between_nonpos hs
            (K.turn_cd_neg_of_mem_I₂ hw) hv₃neg.le
          have hu₁Not : (K.skeleton.u₁ : Point) ∉
              openSegment ℝ (w : Point) (K.skeleton.v₃ : Point) := by
            have hfull := first_pair_points_do_not_block_second K.hfour
              (K.skeleton_ne 0 2 (by decide)) hw_v₃
              (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
              (K.skeleton_ne 0 5 (by decide))
              (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
              (K.skeleton_ne 2 5 (by decide))
              (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
            exact hfull.1
          rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 5) hs with
            hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
          · rw [hsd] at hsneg; simp at hsneg
          · exact (hu₁Not (by simpa [hsu₁] using hs)).elim
          · rw [hsu₂] at hsneg
            have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
              simpa only [turn_rotate] using K.inside.2.1
            have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
              hbcd.le (by simp) (Or.inl hbcd)
            linarith
          · rw [hsu₃, turn_eq_zero_of_between K.skeleton.hu₃] at hsneg
            linarith
          · rw [hempty₁] at hs₁; simp at hs₁
          · have hsw := hunique₂ s hs₂
            exact (hw_v₃ (by simpa [hsw] using hs)).elim
          · rcases hunique₃ s hs₃ with hsp | hsq
            · have hpw : p ≠ w := by
                intro e
                exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
                  hw (e ▸ hpI)
              have hfull := first_pair_points_do_not_block_second K.hfour
                hp_v₂ hw_v₃ hpw
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5)
                (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
                (K.skeleton_ne 4 5 (by decide)) hwv₂
              exact (hfull.1 (by simpa only [hsp] using hs)).elim
            · exact hsq
        have hqw_v₃ : (q : Point) ∈ openSegment ℝ
            (w : Point) (K.skeleton.v₃ : Point) := by simpa [hsCases] using hs
        have hw_u₂ : w ≠ K.skeleton.u₂ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
        obtain ⟨t, ht⟩ := K.proper w K.skeleton.u₂ hw_u₂ hwu₂
        have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
            (w : Point) := strict_cell_strict_outer K.inside
              (Or.inr (Or.inl (K.mem_I₂.mp hw)))
        rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 1) ht with
          htd | htu₁ | htu₂ | htu₃ | ht₁ | ht₂ | ht₃
        · have hb_u₂ : b ≠ K.skeleton.u₂ := by
            intro e
            have hm : (b : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
              simpa only [e] using K.skeleton.hu₂
            exact K.hbd (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
          have hb_w : b ≠ w := by
            intro e
            exact (strictlyInsideTriangle_ne_vertices hwOuter).2.1
              (congrArg Subtype.val e.symm)
          have hd_u₂ : d ≠ K.skeleton.u₂ := by
            intro e
            have hm : (d : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
              simpa only [e] using K.skeleton.hu₂
            exact K.hbd (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
          have hd_w : d ≠ w := by
            intro e
            exact (strictlyInsideTriangle_ne_vertices (K.mem_I₂.mp hw)).2.2
              (congrArg Subtype.val e.symm)
          have hfull := first_pair_points_do_not_block_second K.hfour K.hbd hw_u₂.symm
            hb_u₂ hb_w hd_u₂ hd_w K.skeleton.hu₂
          exact hfull.2 (by simpa only [htd, openSegment_symm] using ht)
        · have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 0 2 (by decide)) hw_u₂
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
            (K.skeleton_ne 0 1 (by decide))
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
            (K.skeleton_ne 2 1 (by decide))
            (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
          exact hfull.1 (by simpa [htu₁] using ht)
        · exact (hw_u₂ (Subtype.ext
            ((right_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [htu₂] using ht)))).elim
        · have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 0 2 (by decide)) hw_u₂
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
            (K.skeleton_ne 0 1 (by decide))
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
            (K.skeleton_ne 2 1 (by decide))
            (by simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_between)
          exact hfull.2 (by simpa [htu₃] using ht)
        · rw [hempty₁] at ht₁; simp at ht₁
        · have htw := hunique₂ t ht₂
          exact (hw_u₂ (by simpa [htw] using ht)).elim
        · rcases hunique₃ t ht₃ with htp | htq
          · have hpOn : (p : Point) ∈ openSegment ℝ
                (K.skeleton.u₂ : Point) (w : Point) := by
              simpa only [htp, openSegment_symm] using ht
            have heq := other_endpoint_eq_of_common_blocker K.hfour
              (K.skeleton_ne 1 5 (by decide)) hw_u₂.symm
              (by
                rw [openSegment_symm]
                simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
              hpOn
            exact (hw_v₃ heq.symm).elim
          · have heq := other_endpoint_eq_of_common_blocker K.hfour
              hw_v₃ hw_u₂ hqw_v₃
              (by simpa only [htq] using ht)
            exact (K.skeleton_ne 5 1 (by decide) heq).elim
      · have hpw : p ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
        have hqw : q ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
            hw (e ▸ hqI)
        have hline := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0) hpw
          H₃.hpq.symm hqw
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (by simpa only [K.T₃_side_two] using hsec.2)
        obtain ⟨r, hr⟩ := K.proper p w hpw (hpv₁.trans hwv₁.symm)
        rcases K.portal_three_to_two hpI hpneg
            (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
          hrI₃ | hru₁ | hrI₂
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact hpw (by simpa [hrp] using hr)
          · exact hline.1 (by simpa [hrq] using hr)
        · exact hline.2 (by simpa [hru₁] using hr)
        · have hrw := hunique₂ r hrI₂
          exact hpw (by simpa [hrw] using hr)
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Beam pair `(v₂u₁,v₃u₂)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_A_E
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 0 1 2) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ :=
    hpair₁ (i := 2) (j := 1) (by decide)
  have hu₃v₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.v₁ :=
    hpair₁ (i := 1) (j := 0) (by decide)
  have hv₁u₂ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₂ :=
    hpair₁ (i := 0) (j := 2) (by decide)
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    intro h
    have hkBeam : colour (K.T₃.side 2) = colour (K.T₃.side 0) := by
      calc
        colour (K.T₃.side 2) = colour K.skeleton.u₁ := by simp only [K.T₃_side_two]
        _ = colour K.skeleton.u₂ := h
        _ = colour K.skeleton.v₃ := by
          simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
        _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero]
    rcases H₃.secondary with hsec | hsec
    · exact H₃.p_colour_ne_beam (hsec.1.trans hkBeam)
    · exact H₃.q_colour_ne_beam (hsec.1.trans hkBeam)
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    intro h
    apply H₂.remaining_colour_ne
    calc
      colour (K.T₂.side 2) = colour K.skeleton.u₃ := by simp only [K.T₂_side_two]
      _ = colour K.skeleton.u₁ := h.symm
      _ = colour K.skeleton.v₂ := by
        simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour.symm
      _ = colour (K.T₂.side 0) := by simp only [K.T₂_side_zero]
  have hu₁v₁ : colour K.skeleton.u₁ = colour K.skeleton.v₁ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 3)
      hu₂u₃ hu₃v₁ hv₁u₂
    rcases hcases with h | h | h
    · exact (hu₁u₂ h).elim
    · exact (hu₁u₃ h).elim
    · exact h
  have hwu₂ : colour w = colour K.skeleton.u₂ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      (K.skeleton.blocker_colour_ne 2)
      hu₁u₂ hu₂u₃ hu₁u₃.symm
    rcases hcases with h | h | h
    · exact (H₂.p_colour_ne 1 (by simpa using h)).elim
    · exact h
    · exact (H₂.p_colour_ne 2 (by simpa using h)).elim
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
      have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
        have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
          rw [← turn_rotate]
          exact K.inside.2.2
        rw [turn_swap_first] at h
        linarith
      exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    rcases H₃.secondary with hsec | hsec
    · have hqu₃ : colour q = colour K.skeleton.u₃ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ q H₃.hq)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 1)
          (K.skeleton.blocker_colour_ne 2)
          hu₁u₂ hu₂u₃ hu₁u₃.symm
        rcases hcases with h | h | h
        · exact (H₃.interior_colour_ne (by
            calc
              colour p = colour (K.T₃.side 2) := hsec.1
              _ = colour K.skeleton.u₁ := by simp only [K.T₃_side_two]
              _ = colour q := h.symm)).elim
        · exact (H₃.q_colour_ne_beam (by
            calc
              colour q = colour K.skeleton.u₂ := h
              _ = colour K.skeleton.v₃ := by
                simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
              _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero])).elim
        · exact h
      have hqneg := turn_neg_of_between_nonpos
        (by simpa only [K.T₃_side_two] using hsec.2) hpneg hu₁neg.le
      have hq_u₃ : q ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
      have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      have hline := first_pair_points_do_not_block_second K.hfour
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0) hq_u₃
        H₃.hpq hp_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
        (K.skeleton_ne 0 2 (by decide))
        (by simpa only [K.T₃_side_two] using hsec.2)
      obtain ⟨r, hr⟩ := K.proper q K.skeleton.u₃ hq_u₃ hqu₃
      have hrw : r = w := by
        rcases K.portal_three_to_two hqI hqneg
            (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
          hrI₃ | hru₁ | hrI₂
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact (hline.1 (by simpa [hrp] using hr)).elim
          · exact (hq_u₃ (by simpa [hrq] using hr)).elim
        · exact (hline.2 (by simpa [hru₁] using hr)).elim
        · exact hunique₂ r hrI₂
      have hw_u₃ : (w : Point) ∈ openSegment ℝ
          (q : Point) (K.skeleton.u₃ : Point) := by simpa [hrw] using hr
      have hw_v₃ : w ≠ K.skeleton.v₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5
      obtain ⟨s, hs⟩ := K.proper w K.skeleton.v₃ hw_v₃ (by
        calc
          colour w = colour K.skeleton.u₂ := hwu₂
          _ = colour K.skeleton.v₃ := by
            simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm)
      have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
          (w : Point) := strict_cell_strict_outer K.inside
            (Or.inr (Or.inl (K.mem_I₂.mp hw)))
      have hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0 :=
        turn_neg_of_right_of_negative_between_nonneg
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
          (by
            have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
              simpa only [turn_rotate] using K.inside.2.1
            exact (edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hbcd.le (by simp)
              (Or.inl hbcd)).le)
          hpneg
      have hsneg := turn_neg_of_between_nonpos hs
        (K.turn_cd_neg_of_mem_I₂ hw) hv₃neg.le
      have hu₁Not : (K.skeleton.u₁ : Point) ∉
          openSegment ℝ (w : Point) (K.skeleton.v₃ : Point) := by
        have hfull := first_pair_points_do_not_block_second K.hfour
          (K.skeleton_ne 4 0 (by decide)) hw_v₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
          (K.skeleton_ne 4 5 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (K.skeleton_ne 0 5 (by decide))
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
        exact hfull.2
      rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 5) hs with
        hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
      · rw [hsd] at hsneg; simp at hsneg
      · exact hu₁Not (by simpa [hsu₁] using hs)
      · rw [hsu₂] at hsneg
        have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
          simpa only [turn_rotate] using K.inside.2.1
        have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
          hbcd.le (by simp) (Or.inl hbcd)
        linarith
      · rw [hsu₃, turn_eq_zero_of_between K.skeleton.hu₃] at hsneg
        linarith
      · rw [hempty₁] at hs₁; simp at hs₁
      · have hsw := hunique₂ s hs₂
        exact hw_v₃ (by simpa [hsw] using hs)
      · rcases hunique₃ s hs₃ with hsp | hsq
        · have hpOn : (p : Point) ∈ openSegment ℝ
              (K.skeleton.v₃ : Point) (w : Point) := by
            simpa only [hsp, openSegment_symm] using hs
          have heq := other_endpoint_eq_of_common_blocker K.hfour
            (K.skeleton_ne 5 1 (by decide)) hw_v₃.symm
            (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
            hpOn
          exact (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1 heq.symm).elim
        · have hqw : q ≠ w := by
            intro e
            exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
              hw (e ▸ hqI)
          have hfull := first_pair_points_do_not_block_second K.hfour
            hq_u₃ hw_v₃ hqw
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5)
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
            (K.skeleton_ne 2 5 (by decide)) hw_u₃
          exact hfull.1 (by simpa only [hsq] using hs)
    · have hpu₃ : colour p = colour K.skeleton.u₃ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ p H₃.hp)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 1)
          (K.skeleton.blocker_colour_ne 2)
          hu₁u₂ hu₂u₃ hu₁u₃.symm
        rcases hcases with h | h | h
        · exact (H₃.interior_colour_ne (by
            calc
              colour p = colour K.skeleton.u₁ := h
              _ = colour (K.T₃.side 2) := by simp only [K.T₃_side_two]
              _ = colour q := hsec.1.symm)).elim
        · exact (H₃.p_colour_ne_beam (by
            calc
              colour p = colour K.skeleton.u₂ := h
              _ = colour K.skeleton.v₃ := by
                simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm
              _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero])).elim
        · exact h
      have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      have hq_u₃ : q ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2
      have hline := first_pair_points_do_not_block_second K.hfour
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0) hp_u₃
        H₃.hpq.symm hq_u₃
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
        (K.skeleton_ne 0 2 (by decide))
        (by simpa only [K.T₃_side_two] using hsec.2)
      obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      have hrw : r = w := by
        rcases K.portal_three_to_two hpI hpneg
            (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
          hrI₃ | hru₁ | hrI₂
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact (hp_u₃ (by simpa [hrp] using hr)).elim
          · exact (hline.1 (by simpa [hrq] using hr)).elim
        · exact (hline.2 (by simpa [hru₁] using hr)).elim
        · exact hunique₂ r hrI₂
      have hw_u₃ : (w : Point) ∈ openSegment ℝ
          (p : Point) (K.skeleton.u₃ : Point) := by simpa [hrw] using hr
      have hw_v₃ : w ≠ K.skeleton.v₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5
      obtain ⟨s, hs⟩ := K.proper w K.skeleton.v₃ hw_v₃ (by
        calc
          colour w = colour K.skeleton.u₂ := hwu₂
          _ = colour K.skeleton.v₃ := by
            simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour.symm)
      have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
          (w : Point) := strict_cell_strict_outer K.inside
            (Or.inr (Or.inl (K.mem_I₂.mp hw)))
      have hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0 :=
        turn_neg_of_right_of_negative_between_nonneg
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
          (by
            have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
              simpa only [turn_rotate] using K.inside.2.1
            exact (edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂ hbcd.le (by simp)
              (Or.inl hbcd)).le)
          hpneg
      have hsneg := turn_neg_of_between_nonpos hs
        (K.turn_cd_neg_of_mem_I₂ hw) hv₃neg.le
      have hu₁Not : (K.skeleton.u₁ : Point) ∉
          openSegment ℝ (w : Point) (K.skeleton.v₃ : Point) := by
        have hfull := first_pair_points_do_not_block_second K.hfour
          (K.skeleton_ne 4 0 (by decide)) hw_v₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
          (K.skeleton_ne 4 5 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (K.skeleton_ne 0 5 (by decide))
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
        exact hfull.2
      have hsCases : s = q := by
        rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 5) hs with
          hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
        · rw [hsd] at hsneg; simp at hsneg
        · exact (hu₁Not (by simpa [hsu₁] using hs)).elim
        · rw [hsu₂] at hsneg
          have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
            simpa only [turn_rotate] using K.inside.2.1
          have hu₂pos := edgeTurn_pos_of_mem_openSegment K.skeleton.hu₂
            hbcd.le (by simp) (Or.inl hbcd)
          linarith
        · rw [hsu₃, turn_eq_zero_of_between K.skeleton.hu₃] at hsneg
          linarith
        · rw [hempty₁] at hs₁; simp at hs₁
        · have hsw := hunique₂ s hs₂
          exact (hw_v₃ (by simpa [hsw] using hs)).elim
        · rcases hunique₃ s hs₃ with hsp | hsq
          · have hpOn : (p : Point) ∈ openSegment ℝ
                (K.skeleton.v₃ : Point) (w : Point) := by
              simpa only [hsp, openSegment_symm] using hs
            have heq := other_endpoint_eq_of_common_blocker K.hfour
              (K.skeleton_ne 5 1 (by decide)) hw_v₃.symm
              (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
              hpOn
            exact (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1 heq.symm).elim
          · exact hsq
      have hqw_v₃ : (q : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₃ : Point) := by simpa [hsCases] using hs
      have hw_u₂ : w ≠ K.skeleton.u₂ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 1
      obtain ⟨t, ht⟩ := K.proper w K.skeleton.u₂ hw_u₂ hwu₂
      have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
          (w : Point) := strict_cell_strict_outer K.inside
            (Or.inr (Or.inl (K.mem_I₂.mp hw)))
      rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 1) ht with
        htd | htu₁ | htu₂ | htu₃ | ht₁ | ht₂ | ht₃
      · have hb_u₂ : b ≠ K.skeleton.u₂ := by
          intro e
          have hm : (b : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
            simpa only [e] using K.skeleton.hu₂
          exact K.hbd (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
        have hb_w : b ≠ w := by
          intro e
          exact (strictlyInsideTriangle_ne_vertices hwOuter).2.1
            (congrArg Subtype.val e.symm)
        have hd_u₂ : d ≠ K.skeleton.u₂ := by
          intro e
          have hm : (d : Point) ∈ openSegment ℝ (b : Point) (d : Point) := by
            simpa only [e] using K.skeleton.hu₂
          exact K.hbd (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm))
        have hd_w : d ≠ w := by
          intro e
          exact (strictlyInsideTriangle_ne_vertices (K.mem_I₂.mp hw)).2.2
            (congrArg Subtype.val e.symm)
        have hfull := first_pair_points_do_not_block_second K.hfour K.hbd hw_u₂.symm
          hb_u₂ hb_w hd_u₂ hd_w K.skeleton.hu₂
        exact hfull.2 (by simpa only [htd, openSegment_symm] using ht)
      · have hfull := first_pair_points_do_not_block_second K.hfour
          (K.skeleton_ne 4 0 (by decide)) hw_u₂
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
          (K.skeleton_ne 4 1 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (K.skeleton_ne 0 1 (by decide))
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
        exact hfull.2 (by simpa [htu₁] using ht)
      · exact (hw_u₂ (Subtype.ext
          ((right_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [htu₂] using ht)))).elim
      · have hfull := first_pair_points_do_not_block_second K.hfour
          hp_u₃ hw_u₂
          (by
            intro e
            exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
              hw (e ▸ hpI))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1)
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
          (K.skeleton_ne 2 1 (by decide)) hw_u₃
        exact hfull.2 (by simpa [htu₃] using ht)
      · rw [hempty₁] at ht₁; simp at ht₁
      · have htw := hunique₂ t ht₂
        exact (hw_u₂ (by simpa [htw] using ht)).elim
      · rcases hunique₃ t ht₃ with htp | htq
        · have hfull := first_pair_points_do_not_block_second K.hfour
            hp_u₃ hw_u₂
            (by
              intro e
              exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
                hw (e ▸ hpI))
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1)
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
            (K.skeleton_ne 2 1 (by decide)) hw_u₃
          exact hfull.1 (by simpa [htp] using ht)
        · have heq := other_endpoint_eq_of_common_blocker K.hfour
            hw_v₃ hw_u₂ hqw_v₃ (by simpa [htq] using ht)
          exact (K.skeleton_ne 5 1 (by decide) heq).elim
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Beam pair `(v₂u₁,u₂u₁)` in the `(0,1,2)` distribution. -/
theorem impossible_one_two_beams_A_F
    {w p q : P} (hw : w ∈ K.I₂)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q)
    (hempty₁ : K.I₁ = ∅)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : TwoInteriorPatternAt colour (colour a) K.T₃ p q 1 2 0) : False := by
  have hpI : p ∈ K.I₃ := K.mem_I₃.mpr H₃.hp
  have hqI : q ∈ K.I₃ := K.mem_I₃.mpr H₃.hq
  have hpair₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [hempty₁]))
  have hu₁u₂ : colour K.skeleton.u₁ = colour K.skeleton.u₂ := by
    simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_colour.symm
  have hv₂u₁ : colour K.skeleton.v₂ = colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour
  have hu₁u₃ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₃ := by
    intro h
    apply hpair₁ (i := 2) (j := 1) (by decide)
    calc
      colour (K.T₁.side 2) = colour K.skeleton.u₂ := by simp only [K.T₁_side_two]
      _ = colour K.skeleton.u₁ := hu₁u₂.symm
      _ = colour K.skeleton.u₃ := h
      _ = colour (K.T₁.side 1) := by simp only [K.T₁_side_one]
  have hu₃v₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.v₁ :=
    hpair₁ (i := 1) (j := 0) (by decide)
  have hv₁u₁ : colour K.skeleton.v₁ ≠ colour K.skeleton.u₁ := by
    intro h
    apply hpair₁ (i := 0) (j := 2) (by decide)
    calc
      colour (K.T₁.side 0) = colour K.skeleton.v₁ := by simp only [K.T₁_side_zero]
      _ = colour K.skeleton.u₁ := h
      _ = colour K.skeleton.u₂ := hu₁u₂
      _ = colour (K.T₁.side 2) := by simp only [K.T₁_side_two]
  have hwv₁ : colour w = colour K.skeleton.v₁ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hw))
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 3)
      hu₁u₃ hu₃v₁ hv₁u₁
    rcases hcases with h | h | h
    · exact (H₂.p_colour_ne 1 (by simpa using h)).elim
    · exact (H₂.p_colour_ne 2 (by simpa using h)).elim
    · exact h
  have hv₃u₁ : colour K.skeleton.v₃ ≠ colour K.skeleton.u₁ := by
    intro h
    rcases H₃.secondary with hsec | hsec
    · apply H₃.p_colour_ne_beam
      calc
        colour p = colour (K.T₃.side 0) := hsec.1
        _ = colour K.skeleton.v₃ := by simp only [K.T₃_side_zero]
        _ = colour K.skeleton.u₁ := h
        _ = colour K.skeleton.u₂ := hu₁u₂
        _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one]
    · apply H₃.q_colour_ne_beam
      calc
        colour q = colour (K.T₃.side 0) := hsec.1
        _ = colour K.skeleton.v₃ := by simp only [K.T₃_side_zero]
        _ = colour K.skeleton.u₁ := h
        _ = colour K.skeleton.u₂ := hu₁u₂
        _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one]
  have hv₃v₁ : colour K.skeleton.v₃ ≠ colour K.skeleton.v₁ := by
    intro h
    have hwHull : (w : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
      strictlyInsideTriangle_mem_triangleHull
        (strict_cell_strict_outer K.inside (Or.inr (Or.inl (K.mem_I₂.mp hw))))
    have hwp : w ≠ p := by
      intro e
      exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
    have hwq : w ≠ q := by
      intro e
      exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hqI)
    rcases H₃.secondary with hsec | hsec
    · apply four_same_colour_card_contradiction
          (x₀ := K.skeleton.v₁) (x₁ := w)
          (x₂ := K.skeleton.v₃) (x₃ := p)
          (red := colour a)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3).symm
        (K.skeleton_ne 3 5 (by decide))
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 3).symm
        (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5)
        hwp
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5).symm
        (K.skeleton_mem_outer 3) hwHull (K.skeleton_mem_outer 5)
        (strictlyInsideTriangle_mem_triangleHull
          (strict_cell_strict_outer K.inside (Or.inr (Or.inr H₃.hp))))
        hwv₁ h
        (by
          calc
            colour p = colour (K.T₃.side 0) := hsec.1
            _ = colour K.skeleton.v₃ := by simp only [K.T₃_side_zero]
            _ = colour K.skeleton.v₁ := h)
        (K.skeleton.blocker_colour_ne 3)
        (K.otherColourBound _ (K.skeleton.blocker_colour_ne 3))
    · apply four_same_colour_card_contradiction
          (x₀ := K.skeleton.v₁) (x₁ := w)
          (x₂ := K.skeleton.v₃) (x₃ := q)
          (red := colour a)
        (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3).symm
        (K.skeleton_ne 3 5 (by decide))
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3).symm
        (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5)
        hwq
        (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5).symm
        (K.skeleton_mem_outer 3) hwHull (K.skeleton_mem_outer 5)
        (strictlyInsideTriangle_mem_triangleHull
          (strict_cell_strict_outer K.inside (Or.inr (Or.inr H₃.hq))))
        hwv₁ h
        (by
          calc
            colour q = colour (K.T₃.side 0) := hsec.1
            _ = colour K.skeleton.v₃ := by simp only [K.T₃_side_zero]
            _ = colour K.skeleton.v₁ := h)
        (K.skeleton.blocker_colour_ne 3)
        (K.otherColourBound _ (K.skeleton.blocker_colour_ne 3))
  have hv₃u₃ : colour K.skeleton.v₃ = colour K.skeleton.u₃ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.skeleton.blocker_colour_ne 5)
      (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 3)
      hu₁u₃ hu₃v₁ hv₁u₁
    rcases hcases with h | h | h
    · exact (hv₃u₁ h).elim
    · exact h
    · exact (hv₃v₁ h).elim
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · rcases H₃.secondary with hsec | hsec
    · have hqv₁ : colour q = colour K.skeleton.v₁ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ q H₃.hq)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 2)
          (K.skeleton.blocker_colour_ne 3)
          hu₁u₃ hu₃v₁ hv₁u₁
        rcases hcases with h | h | h
        · exact (H₃.q_colour_ne_beam (by
            calc
              colour q = colour K.skeleton.u₁ := h
              _ = colour K.skeleton.u₂ := hu₁u₂
              _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one])).elim
        · exact (H₃.interior_colour_ne (by
            calc
              colour p = colour (K.T₃.side 0) := hsec.1
              _ = colour K.skeleton.v₃ := by simp only [K.T₃_side_zero]
              _ = colour K.skeleton.u₃ := hv₃u₃
              _ = colour q := h.symm)).elim
        · exact h
      have hqne := K.turn_cd_ne_zero_of_mem_I₃ hqI
      rcases lt_or_gt_of_ne hqne with hqneg | hqpos
      · have hqw : q ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hqI)
        have hpw : p ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
        have hpNot : (p : Point) ∉ openSegment ℝ (q : Point) (w : Point) := by
          have hfull := first_pair_points_do_not_block_second K.hfour
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5)
            hqw H₃.hpq hpw
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5).symm
            (by simpa only [K.T₃_side_zero] using hsec.2)
          exact hfull.1
        have hu₁Not : (K.skeleton.u₁ : Point) ∉
            openSegment ℝ (q : Point) (w : Point) := by
          have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 4 0 (by decide)) hqw.symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
            (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
          simpa only [openSegment_symm] using hfull.2
        obtain ⟨r, hr⟩ := K.proper q w hqw (hqv₁.trans hwv₁.symm)
        rcases K.portal_three_to_two hqI hqneg
            (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
          hrI₃ | hru₁ | hrI₂
        · rcases hunique₃ r hrI₃ with hrp | hrq
          · exact hpNot (by simpa [hrp] using hr)
          · exact hqw (by simpa [hrq] using hr)
        · exact hu₁Not (by simpa [hru₁] using hr)
        · have hrw := hunique₂ r hrI₂
          exact hqw (by simpa [hrw] using hr)
      · have hpw : p ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
        have hpu₃ : colour p = colour K.skeleton.u₃ := by
          calc
            colour p = colour (K.T₃.side 0) := hsec.1
            _ = colour K.skeleton.v₃ := by simp only [K.T₃_side_zero]
            _ = colour K.skeleton.u₃ := hv₃u₃
        have hp_u₃ : p ≠ K.skeleton.u₃ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
        obtain ⟨r, hr⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
        have hrw : r = w := by
          rcases K.portal_three_to_two hpI hpneg
              (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hr with
            hrI₃ | hru₁ | hrI₂
          · rcases hunique₃ r hrI₃ with hrp | hrq
            · exact (hp_u₃ (by simpa [hrp] using hr)).elim
            · have hqOn : (q : Point) ∈ openSegment ℝ
                  (p : Point) (K.skeleton.u₃ : Point) := by simpa [hrq] using hr
              have heq := other_endpoint_eq_of_common_blocker K.hfour
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5)
                hp_u₃ hsec.2 hqOn
              exact (K.skeleton_ne 5 2 (by decide) heq).elim
          · have hfull := first_pair_points_do_not_block_second K.hfour
                (K.skeleton_ne 1 0 (by decide)) hp_u₃
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
                (K.skeleton_ne 1 2 (by decide))
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
                (K.skeleton_ne 0 2 (by decide))
                (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
            exact (hfull.2 (by simpa [hru₁] using hr)).elim
          · exact hunique₂ r hrI₂
        have hw_u₃ : (w : Point) ∈ openSegment ℝ
            (p : Point) (K.skeleton.u₃ : Point) := by simpa [hrw] using hr
        have hq_v₁ : q ≠ K.skeleton.v₁ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3
        have hpNot : (p : Point) ∉
            openSegment ℝ (q : Point) (K.skeleton.v₁ : Point) := by
          have hfull := first_pair_points_do_not_block_second K.hfour
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5)
            hq_v₁ H₃.hpq
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 3)
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5).symm
            (K.skeleton_ne 5 3 (by decide))
            (by simpa only [K.T₃_side_zero] using hsec.2)
          exact hfull.1
        obtain ⟨s, hs⟩ := K.proper q K.skeleton.v₁ hq_v₁ hqv₁
        have hsu₂ : s = K.skeleton.u₂ := by
          rcases K.portal_three_to_one hqI hqpos
              (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 0).property) hs with
            hsI₃ | hsu₂ | hsI₁
          · rcases hunique₃ s hsI₃ with hsp | hsq
            · exact (hpNot (by simpa [hsp] using hs)).elim
            · exact (hq_v₁ (by simpa [hsq] using hs)).elim
          · exact hsu₂
          · rw [hempty₁] at hsI₁; simp at hsI₁
        have hu₂_qv₁ : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
            (q : Point) (K.skeleton.v₁ : Point) := by simpa [hsu₂] using hs
        have hqw : q ≠ w := by
          intro e
          exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hqI)
        obtain ⟨t, ht⟩ := K.proper q w hqw (hqv₁.trans hwv₁.symm)
        have hqOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
            (q : Point) := strict_cell_strict_outer K.inside
              (Or.inr (Or.inr (K.mem_I₃.mp hqI)))
        have htd : t = d := by
          rcases K.strict_outer_chord_cases hqOuter
              (strictlyInsideTriangle_mem_triangleHull
                (strict_cell_strict_outer K.inside (Or.inr (Or.inl (K.mem_I₂.mp hw))))) ht with
            htd | htu₁ | htu₂ | htu₃ | ht₁ | ht₂ | ht₃
          · exact htd
          · have hfull := first_pair_points_do_not_block_second K.hfour
                (K.skeleton_ne 4 0 (by decide)) hqw.symm
                (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 4).symm
                (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 0).symm
                (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
            exact (hfull.2 (by simpa [htu₁, openSegment_symm] using ht)).elim
          · have heq := other_endpoint_eq_of_common_blocker K.hfour
                hq_v₁ hqw hu₂_qv₁ (by simpa [htu₂] using ht)
            exact ((K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3).symm heq).elim
          · have hfull := first_pair_points_do_not_block_second K.hfour
                hp_u₃ hqw.symm hpw H₃.hpq
                (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 2).symm
                hw_u₃
            exact (hfull.2 (by simpa [htu₃, openSegment_symm] using ht)).elim
          · rw [hempty₁] at ht₁; simp at ht₁
          · have htw := hunique₂ t ht₂
            exact (hqw (by simpa [htw] using ht)).elim
          · rcases hunique₃ t ht₃ with htp | htq
            · have hfull := first_pair_points_do_not_block_second K.hfour
                  (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5)
                  hqw H₃.hpq hpw
                  (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5).symm
                  (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5).symm
                  (by simpa only [K.T₃_side_zero] using hsec.2)
              exact (hfull.1 (by simpa [htp] using ht)).elim
            · exact (hqw (by simpa [htq] using ht)).elim
        have hd_qw : (d : Point) ∈ openSegment ℝ (q : Point) (w : Point) := by
          simpa [htd] using ht
        have hw_v₁ : w ≠ K.skeleton.v₁ :=
          K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 3
        obtain ⟨s, hs⟩ := K.proper w K.skeleton.v₁ hw_v₁ hwv₁
        have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
            (w : Point) := strict_cell_strict_outer K.inside
              (Or.inr (Or.inl (K.mem_I₂.mp hw)))
        rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 3) hs with
          hsd | hsu₁ | hsu₂ | hsu₃ | hs₁ | hs₂ | hs₃
        · have hd_wq : (d : Point) ∈ openSegment ℝ (w : Point) (q : Point) := by
            simpa only [openSegment_symm] using hd_qw
          have heq := other_endpoint_eq_of_common_blocker K.hfour hqw.symm hw_v₁
            hd_wq (by simpa [hsd] using hs)
          exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3 heq).elim
        · have hfull := first_pair_points_do_not_block_second K.hfour
              (K.skeleton_ne 4 0 (by decide)) hw_v₁
              (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
              (K.skeleton_ne 4 3 (by decide))
              (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
              (K.skeleton_ne 0 3 (by decide))
              (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
          exact hfull.2 (by simpa [hsu₁] using hs)
        · have heq := other_endpoint_eq_of_common_blocker K.hfour
              hq_v₁.symm hw_v₁.symm
              (by simpa only [openSegment_symm] using hu₂_qv₁)
              (by simpa [hsu₂, openSegment_symm] using hs)
          exact (hqw heq).elim
        · have hfull := first_pair_points_do_not_block_second K.hfour
              hp_u₃ hw_v₁
              (by
                intro e
                exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
                  hw (e ▸ hpI))
              (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 3)
              (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
              (K.skeleton_ne 2 3 (by decide)) hw_u₃
          exact hfull.2 (by simpa [hsu₃] using hs)
        · rw [hempty₁] at hs₁; simp at hs₁
        · have hsw := hunique₂ s hs₂
          exact (hw_v₁ (by simpa [hsw] using hs)).elim
        · rcases hunique₃ s hs₃ with hsp | hsq
          · have hfull := first_pair_points_do_not_block_second K.hfour
                hp_u₃ hw_v₁
                (by
                  intro e
                  exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2)
                    hw (e ▸ hpI))
                (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 3)
                (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 2).symm
                (K.skeleton_ne 2 3 (by decide)) hw_u₃
            exact (hfull.1 (by simpa [hsp] using hs)).elim
          · have hd_wq : (d : Point) ∈ openSegment ℝ (w : Point) (q : Point) := by
              simpa only [openSegment_symm] using hd_qw
            have hq_wv₁ : (q : Point) ∈ openSegment ℝ
                (w : Point) (K.skeleton.v₁ : Point) := by simpa [hsq] using hs
            have hd_wv₁ := openSegment_left_nested hd_wq hq_wv₁
            have heq := other_endpoint_eq_of_common_blocker K.hfour hqw.symm hw_v₁
              hd_wq hd_wv₁
            exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 3 heq).elim
    · have hpv₁ : colour p = colour K.skeleton.v₁ := by
        have hcases := fin4_eq_one_of_three_of_avoid
          (K.interior_colour_ne_red₃ p H₃.hp)
          (K.skeleton.blocker_colour_ne 0)
          (K.skeleton.blocker_colour_ne 2)
          (K.skeleton.blocker_colour_ne 3)
          hu₁u₃ hu₃v₁ hv₁u₁
        rcases hcases with h | h | h
        · exact (H₃.p_colour_ne_beam (by
            calc
              colour p = colour K.skeleton.u₁ := h
              _ = colour K.skeleton.u₂ := hu₁u₂
              _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one])).elim
        · exact (H₃.interior_colour_ne (by
            calc
              colour p = colour K.skeleton.u₃ := h
              _ = colour K.skeleton.v₃ := hv₃u₃.symm
              _ = colour (K.T₃.side 0) := by simp only [K.T₃_side_zero]
              _ = colour q := hsec.1.symm)).elim
        · exact h
      have hpw : p ≠ w := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hpI)
      have hqw : q ≠ w := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hw (e ▸ hqI)
      have hqNot : (q : Point) ∉ openSegment ℝ (p : Point) (w : Point) := by
        have hfull := first_pair_points_do_not_block_second K.hfour
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hqI)) 5)
          hpw H₃.hpq.symm hqw
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 5).symm
          (by simpa only [K.T₃_side_zero] using hsec.2)
        exact hfull.1
      have hu₁Not : (K.skeleton.u₁ : Point) ∉
          openSegment ℝ (p : Point) (w : Point) := by
        have hfull := first_pair_points_do_not_block_second K.hfour
          (K.skeleton_ne 4 0 (by decide)) hpw.symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 4).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hw)) 0).symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
        simpa only [openSegment_symm] using hfull.2
      obtain ⟨r, hr⟩ := K.proper p w hpw (hpv₁.trans hwv₁.symm)
      rcases K.portal_three_to_two hpI hpneg
          (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hw)) hr with
        hrI₃ | hru₁ | hrI₂
      · rcases hunique₃ r hrI₃ with hrp | hrq
        · exact hpw (by simpa [hrp] using hr)
        · exact hqNot (by simpa [hrq] using hr)
      · exact hu₁Not (by simpa [hru₁] using hr)
      · have hrw := hunique₂ r hrI₂
        exact hpw (by simpa [hrw] using hr)
  · exact K.impossible_two_pattern_positive H₃ hunique₃ hempty₁ hppos

/-- Complete corrected elimination of the `(0,1,2)` cell distribution. -/
theorem impossible_I₁_zero_I₂_one_I₃_two
    (h₁ : K.I₁.card = 0) (h₂ : K.I₂.card = 1)
    (h₃ : K.I₃.card = 2) : False := by
  have hempty₁ : K.I₁ = ∅ := Finset.card_eq_zero.mp h₁
  obtain ⟨w, hwSet⟩ := Finset.card_eq_one.mp h₂
  obtain ⟨p, q, hpq, hpqSet⟩ := Finset.card_eq_two.mp h₃
  have hw : w ∈ K.I₂ := by rw [hwSet]; simp
  have hp : p ∈ K.I₃ := by rw [hpqSet]; simp
  have hq : q ∈ K.I₃ := by rw [hpqSet]; simp
  have hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w := by
    intro z hz
    rw [hwSet] at hz
    simpa using hz
  have hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p ∨ z = q := by
    intro z hz
    rw [hpqSet] at hz
    simpa using hz
  have hunique₃' : ∀ z : P, z ∈ K.I₃ → z = q ∨ z = p := by
    intro z hz
    exact (hunique₃ z hz).symm
  have H₂ := K.M₂.one_interior_pattern K.hfour (K.mem_I₂.mp hw)
    (fun z hz ↦ hunique₂ z (K.mem_I₂.mpr hz))
  have H₃ := K.M₃.two_interior_pattern K.hfour
    (K.mem_I₃.mp hp) (K.mem_I₃.mp hq) hpq
    (fun z hz ↦ hunique₃ z (K.mem_I₃.mpr hz))
  rcases H₂ with HA | HC | HB
  · rcases H₃ with (HE | HE) | (HF | HF) | (HD | HD)
    · exact K.impossible_one_two_beams_A_E hw hunique₂ hunique₃ hempty₁ HA HE
    · exact K.impossible_one_two_beams_A_E hw hunique₂ hunique₃' hempty₁ HA HE
    · exact K.impossible_one_two_beams_A_F hw hunique₂ hunique₃ hempty₁ HA HF
    · exact K.impossible_one_two_beams_A_F hw hunique₂ hunique₃' hempty₁ HA HF
    · exact K.impossible_one_two_beams_A_D hempty₁ HA HD
    · exact K.impossible_one_two_beams_A_D hempty₁ HA HD
  · rcases H₃ with (HE | HE) | (HF | HF) | (HD | HD)
    · exact K.impossible_one_two_beams_C_E hw hunique₂ hunique₃ hempty₁ HC HE
    · exact K.impossible_one_two_beams_C_E hw hunique₂ hunique₃' hempty₁ HC HE
    · exact K.impossible_one_two_beams_C_F hempty₁ HC HF
    · exact K.impossible_one_two_beams_C_F hempty₁ HC HF
    · exact K.impossible_one_two_beams_C_D hw hunique₂ hunique₃ hempty₁ HC HD
    · exact K.impossible_one_two_beams_C_D hw hunique₂ hunique₃' hempty₁ HC HD
  · rcases H₃ with (HE | HE) | (HF | HF) | (HD | HD)
    · exact K.impossible_one_two_beams_B_E hw hunique₂ hunique₃ hempty₁ HB HE
    · exact K.impossible_one_two_beams_B_E hw hunique₂ hunique₃' hempty₁ HB HE
    · exact K.impossible_one_two_beams_B_F hw hunique₂ hunique₃ hempty₁ HB HF
    · exact K.impossible_one_two_beams_B_F hw hunique₂ hunique₃' hempty₁ HB HF
    · exact K.impossible_one_two_beams_B_D hw hunique₂ hunique₃ hempty₁ HB HD
    · exact K.impossible_one_two_beams_B_D hw hunique₂ hunique₃' hempty₁ HB HD

set_option maxHeartbeats 1000000 in
/-- The canonical mixed path-plus-edge arrangement in the `(1,1,1)` case. -/
theorem impossible_three_single_mixed_Y_B_D
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hu₃u₂ : colour K.skeleton.u₃ = colour K.skeleton.u₂ := by
    simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_colour
  have hu₃v₂ : colour K.skeleton.u₃ = colour K.skeleton.v₂ := by
    simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_colour
  have hu₁v₃ : colour K.skeleton.u₁ = colour K.skeleton.v₃ := by
    simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.remaining_colour_ne.symm
  have hu₁w : colour K.skeleton.u₁ ≠ colour w :=
    (H₂.p_colour_ne 1).symm
  have hwu₃ : colour w ≠ colour K.skeleton.u₃ := H₂.p_colour_ne 2
  have hpw : colour p = colour w := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hpI))
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI))
      hu₃u₁ hu₁w hwu₃
    rcases hcases with h | h | h
    · exact (H₃.p_colour_ne 1 (by
          calc
            colour p = colour K.skeleton.u₃ := h
            _ = colour K.skeleton.u₂ := hu₃u₂
            _ = colour (K.T₃.side 1) := by simp only [K.T₃_side_one])).elim
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
    · exact h
  have hrCases : colour r = colour K.skeleton.u₁ ∨ colour r = colour w := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₁ r (K.mem_I₁.mp hrI))
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI))
      hu₃u₁ hu₁w hwu₃
    rcases hcases with h | h | h
    · exact (H₁.p_colour_ne 1 (by simpa using h)).elim
    · exact Or.inl h
    · exact Or.inr h
  have hrne := K.turn_ad_ne_zero_of_mem_I₁ hrI
  rcases lt_or_gt_of_ne hrne with hrneg | hrpos
  · rcases hrCases with hru₁ | hrw
    · have hr_v₃ : r ≠ K.skeleton.v₃ :=
        K.cellPoint_ne_skeleton (Or.inl hrI) 5
      obtain ⟨s, hs⟩ := K.proper r K.skeleton.v₃ hr_v₃
        (hru₁.trans hu₁v₃)
      rcases K.portal_one_to_three hrI hrneg
          (K.T₃.nonredPoint_mem_hull (K.T₃.sideLocal 0).property) hs with
        hsI₁ | hsu₂ | hsI₃
      · have hsr := hunique₁ s hsI₁
        exact hr_v₃ (by simpa [hsr] using hs)
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 2 1 (by decide)) hr_v₃
            (K.cellPoint_ne_skeleton (Or.inl hrI) 2).symm
            (K.skeleton_ne 2 5 (by decide))
            (K.cellPoint_ne_skeleton (Or.inl hrI) 1).symm
            (K.skeleton_ne 1 5 (by decide))
            (by simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_between)
        exact hfull.2 (by simpa [hsu₂] using hs)
      · have hsp := hunique₃ s hsI₃
        have hpOn : (p : Point) ∈ openSegment ℝ
            (K.skeleton.v₃ : Point) (r : Point) := by
          simpa only [hsp, openSegment_symm] using hs
        have heq := other_endpoint_eq_of_common_blocker K.hfour
          (K.skeleton_ne 5 0 (by decide)) hr_v₃.symm
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
          hpOn
        exact (K.cellPoint_ne_skeleton (Or.inl hrI) 0 heq.symm).elim
    · have hrp : r ≠ p := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.1) hrI (e ▸ hpI)
      obtain ⟨s, hs⟩ := K.proper r p hrp (hrw.trans hpw.symm)
      rcases K.portal_one_to_three hrI hrneg
          (strictlyInsideTriangle_mem_triangleHull (K.mem_I₃.mp hpI)) hs with
        hsI₁ | hsu₂ | hsI₃
      · have hsr := hunique₁ s hsI₁
        exact hrp (by simpa [hsr] using hs)
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 2 1 (by decide)) hrp
            (K.cellPoint_ne_skeleton (Or.inl hrI) 2).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2).symm
            (K.cellPoint_ne_skeleton (Or.inl hrI) 1).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
            (by simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_between)
        exact hfull.2 (by simpa [hsu₂] using hs)
      · have hsp := hunique₃ s hsI₃
        exact hrp (by simpa [hsp] using hs)
  · rcases hrCases with hru₁ | hrw
    · have hr_u₁ : r ≠ K.skeleton.u₁ :=
        K.cellPoint_ne_skeleton (Or.inl hrI) 0
      obtain ⟨s, hs⟩ := K.proper r K.skeleton.u₁ hr_u₁ hru₁
      rcases K.portal_one_to_two hrI hrpos
          (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 1).property) hs with
        hsI₁ | hsu₃ | hsI₂
      · have hsr := hunique₁ s hsI₁
        exact hr_u₁ (by simpa [hsr] using hs)
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 2 1 (by decide)) hr_u₁
            (K.cellPoint_ne_skeleton (Or.inl hrI) 2).symm
            (K.skeleton_ne 2 0 (by decide))
            (K.cellPoint_ne_skeleton (Or.inl hrI) 1).symm
            (K.skeleton_ne 1 0 (by decide))
            (by simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_between)
        exact hfull.1 (by simpa [hsu₃] using hs)
      · have hsw := hunique₂ s hsI₂
        have hcenter := K.red_center_strictly_inside_spoke_triangle
        have hu₂neg : turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (K.skeleton.u₂ : Point) < 0 := by
          have h := turn_pos_of_strictlyInsideTriangle hcenter
          rw [turn_swap_last] at h
          linarith
        have hrline : turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (r : Point) < 0 := turn_neg_of_between_nonpos
            (by
              rw [openSegment_symm]
              simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_between)
          hu₂neg (by simp)
        have hv₂pos : 0 < turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (K.skeleton.v₂ : Point) := by
          rw [turn_swap_first]
          linarith [K.v₂_spoke_side_neg]
        have hwline : 0 < turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (w : Point) := turn_pos_of_between_nonneg
          (by
            rw [openSegment_symm]
            simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_between)
          hv₂pos (by simp)
        have hsline := turn_neg_of_between_nonpos hs hrline (by simp)
        rw [hsw] at hsline
        linarith
    · have hrwNe : r ≠ w := by
        intro e
        exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.1) hrI (e ▸ hwI)
      obtain ⟨s, hs⟩ := K.proper r w hrwNe hrw
      rcases K.portal_one_to_two hrI hrpos
          (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hwI)) hs with
        hsI₁ | hsu₃ | hsI₂
      · have hsr := hunique₁ s hsI₁
        exact hrwNe (by simpa [hsr] using hs)
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (K.skeleton_ne 2 1 (by decide)) hrwNe
            (K.cellPoint_ne_skeleton (Or.inl hrI) 2).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 2).symm
            (K.cellPoint_ne_skeleton (Or.inl hrI) 1).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 1).symm
            (by simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_between)
        exact hfull.1 (by simpa [hsu₃] using hs)
      · have hsw := hunique₂ s hsI₂
        exact hrwNe (by simpa [hsw] using hs)

/-- The cyclic image `Z-C-D` of the canonical mixed arrangement. -/
theorem impossible_three_single_mixed_Z_C_D
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 2 0 1)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  apply K.rotate.impossible_three_single_mixed_Y_B_D
      hwI hpI hrI
  · intro z hz
    exact hunique₂ z (by simpa using hz)
  · intro z hz
    exact hunique₃ z (by simpa using hz)
  · intro z hz
    exact hunique₁ z (by simpa using hz)
  · exact K.rotateOne₂₁ H₂
  · exact K.rotateOne₃₂ H₃
  · exact K.rotateOne₁₃ H₁

/-- The second cyclic image `Z-B-F` of the canonical mixed arrangement. -/
theorem impossible_three_single_mixed_Z_B_F
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 2 0 1)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  apply K.rotate.impossible_three_single_mixed_Z_C_D
      hwI hpI hrI
  · intro z hz
    exact hunique₂ z (by simpa using hz)
  · intro z hz
    exact hunique₃ z (by simpa using hz)
  · intro z hz
    exact hunique₁ z (by simpa using hz)
  · exact K.rotateOne₂₁ H₂
  · exact K.rotateOne₃₂ H₃
  · exact K.rotateOne₁₃ H₁

set_option maxHeartbeats 1000000 in
/-- The opposite-orientation representative `X-A-F` of the mixed
path-plus-edge arrangements. -/
theorem impossible_three_single_mixed_X_A_F
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 0 1 2)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  have hv₁u₃ : colour K.skeleton.v₁ = colour K.skeleton.u₃ := by
    simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour
  have hv₂u₁ : colour K.skeleton.v₂ = colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour
  have hu₂u₁ : colour K.skeleton.u₂ = colour K.skeleton.u₁ := by
    simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_colour
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    intro h
    exact H₂.remaining_colour_ne (by
      simpa only [K.T₂_side_two, K.T₂_side_zero] using
        h.trans hv₂u₁.symm)
  have hu₁w : colour K.skeleton.u₁ ≠ colour w := (H₂.p_colour_ne 1).symm
  have hwu₃ : colour w ≠ colour K.skeleton.u₃ := H₂.p_colour_ne 2
  have hrw : colour r = colour w := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₁ r (K.mem_I₁.mp hrI))
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI))
      hu₃u₁ hu₁w hwu₃
    rcases hcases with h | h | h
    · exact (H₁.p_colour_ne 1 (by simpa using h)).elim
    · exact (H₁.p_colour_ne 2 (by
          simpa only [K.T₁_side_two] using h.trans hu₂u₁.symm)).elim
    · exact h
  have hpCases : colour p = colour K.skeleton.u₃ ∨ colour p = colour w := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hpI))
      (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI))
      hu₃u₁ hu₁w hwu₃
    rcases hcases with h | h | h
    · exact Or.inl h
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
    · exact Or.inr h
  have hpw : p ≠ w := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hwI (e ▸ hpI)
  have hpr : p ≠ r := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.1) hrI (e.symm ▸ hpI)
  have hne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hne with hpneg | hppos
  · rcases hpCases with hpu₃ | hpwColour
    · have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      obtain ⟨s, hs⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      rcases K.portal_three_to_two hpI hpneg
          (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hs with
        hsI₃ | hsu₁ | hsI₂
      · have hsp := hunique₃ s hsI₃
        exact hp_u₃ (by
          apply Subtype.ext
          exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [hsp] using hs))
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (a := K.skeleton.u₂) (a' := K.skeleton.u₁)
            (b := p) (b' := K.skeleton.u₃)
            (K.skeleton_ne 1 0 (by decide)) hp_u₃
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
            (K.skeleton_ne 1 2 (by decide))
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
            (K.skeleton_ne 0 2 (by decide))
            (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
        exact hfull.2 (by simpa [hsu₁] using hs)
      · have hsw := hunique₂ s hsI₂
        have hcenter := K.red_center_strictly_inside_spoke_triangle
        have hu₂neg : turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (K.skeleton.u₂ : Point) < 0 := by
          have h := turn_pos_of_strictlyInsideTriangle hcenter
          rw [turn_swap_last] at h
          linarith
        have hpLine : turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (p : Point) < 0 := turn_neg_of_between_nonpos
          (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
          hu₂neg (by simp)
        have hv₂pos : 0 < turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (K.skeleton.v₂ : Point) := by
          rw [turn_swap_first]
          linarith [K.v₂_spoke_side_neg]
        have hwLine : 0 < turn (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point)
            (w : Point) := turn_pos_of_between_nonneg
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
          hv₂pos (by simp)
        have hsLine := turn_neg_of_between_nonpos hs hpLine (by simp)
        rw [hsw] at hsLine
        linarith
    · obtain ⟨s, hs⟩ := K.proper p w hpw hpwColour
      rcases K.portal_three_to_two hpI hpneg
          (strictlyInsideTriangle_mem_triangleHull (K.mem_I₂.mp hwI)) hs with
        hsI₃ | hsu₁ | hsI₂
      · have hsp := hunique₃ s hsI₃
        exact hpw (by
          apply Subtype.ext
          exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [hsp] using hs))
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (a := K.skeleton.u₂) (a' := K.skeleton.u₁)
            (b := p) (b' := w)
            (K.skeleton_ne 1 0 (by decide)) hpw
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 1).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 0).symm
            (by simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
        exact hfull.2 (by simpa [hsu₁] using hs)
      · have hsw := hunique₂ s hsI₂
        exact hpw (by
          apply Subtype.ext
          exact (right_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [hsw] using hs))
  · rcases hpCases with hpu₃ | hpwColour
    · have hp_u₃ : p ≠ K.skeleton.u₃ :=
        K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
      obtain ⟨s, hs⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
      rcases K.portal_three_to_one hpI hppos
          (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property) hs with
        hsI₃ | hsu₂ | hsI₁
      · have hsp := hunique₃ s hsI₃
        exact hp_u₃ (by
          apply Subtype.ext
          exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [hsp] using hs))
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (a := K.skeleton.u₁) (a' := K.skeleton.u₂)
            (b := p) (b' := K.skeleton.u₃)
            (K.skeleton_ne 0 1 (by decide)) hp_u₃
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
            (K.skeleton_ne 0 2 (by decide))
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
            (K.skeleton_ne 1 2 (by decide))
            (by
              rw [openSegment_symm]
              simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
        exact hfull.2 (by simpa [hsu₂] using hs)
      · have hsr := hunique₁ s hsI₁
        have hcenter := K.red_center_strictly_inside_spoke_triangle
        have hu₁pos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
            (K.skeleton.u₁ : Point) := by
          simpa only [turn_rotate] using turn_pos_of_strictlyInsideTriangle hcenter
        have hpLine : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
            (p : Point) := turn_pos_of_between_nonneg
          (by
            rw [openSegment_symm]
            simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
          hu₁pos (by simp)
        have hrLine : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
            (r : Point) < 0 := turn_neg_of_between_nonpos
          (by simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_between)
          K.v₁_spoke_side_neg (by simp)
        have hsLine := turn_pos_of_between_nonneg hs hpLine (by simp)
        rw [hsr] at hsLine
        linarith
    · obtain ⟨s, hs⟩ := K.proper p r hpr (hpwColour.trans hrw.symm)
      rcases K.portal_three_to_one hpI hppos
          (strictlyInsideTriangle_mem_triangleHull (K.mem_I₁.mp hrI)) hs with
        hsI₃ | hsu₂ | hsI₁
      · have hsp := hunique₃ s hsI₃
        exact hpr (by
          apply Subtype.ext
          exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [hsp] using hs))
      · have hfull := first_pair_points_do_not_block_second K.hfour
            (a := K.skeleton.u₁) (a' := K.skeleton.u₂)
            (b := p) (b' := r)
            (K.skeleton_ne 0 1 (by decide)) hpr
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
            (K.cellPoint_ne_skeleton (Or.inl hrI) 0).symm
            (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
            (K.cellPoint_ne_skeleton (Or.inl hrI) 1).symm
            (by
              rw [openSegment_symm]
              simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_between)
        exact hfull.2 (by simpa [hsu₂] using hs)
      · have hsr := hunique₁ s hsI₁
        exact hpr (by
          apply Subtype.ext
          exact (right_mem_openSegment_iff (𝕜 := ℝ)).mp (by simpa [hsr] using hs))

/-- The cyclic image `Y-A-E` of `X-A-F`. -/
theorem impossible_three_single_mixed_Y_A_E
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  apply K.rotate.impossible_three_single_mixed_X_A_F
      hwI hpI hrI
  · intro z hz
    exact hunique₂ z (by simpa using hz)
  · intro z hz
    exact hunique₃ z (by simpa using hz)
  · intro z hz
    exact hunique₁ z (by simpa using hz)
  · exact K.rotateOne₂₁ H₂
  · exact K.rotateOne₃₂ H₃
  · exact K.rotateOne₁₃ H₁

/-- The second cyclic image `X-C-E` of `X-A-F`. -/
theorem impossible_three_single_mixed_X_C_E
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 0 1 2)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  apply K.rotate.impossible_three_single_mixed_Y_A_E
      hwI hpI hrI
  · intro z hz
    exact hunique₂ z (by simpa using hz)
  · intro z hz
    exact hunique₃ z (by simpa using hz)
  · intro z hz
    exact hunique₁ z (by simpa using hz)
  · exact K.rotateOne₂₁ H₂
  · exact K.rotateOne₃₂ H₃
  · exact K.rotateOne₁₃ H₁

/-- First representative of a length-three beam path. -/
theorem impossible_three_single_path_X_C_F
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 0 1 2)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  apply four_same_colour_card_contradiction
      (x₀ := K.skeleton.v₁) (x₁ := K.skeleton.u₃)
      (x₂ := K.skeleton.u₁) (x₃ := K.skeleton.u₂)
      (red := colour a)
    (K.skeleton_ne 3 2 (by decide))
    (K.skeleton_ne 3 0 (by decide))
    (K.skeleton_ne 3 1 (by decide))
    (K.skeleton_ne 2 0 (by decide))
    (K.skeleton_ne 2 1 (by decide))
    (K.skeleton_ne 0 1 (by decide))
    (K.skeleton_mem_outer 3) (K.skeleton_mem_outer 2)
    (K.skeleton_mem_outer 0) (K.skeleton_mem_outer 1)
  · simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour.symm
  · calc
      colour K.skeleton.u₁ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour K.skeleton.v₁ := by
        simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour.symm
  · calc
      colour K.skeleton.u₂ = colour K.skeleton.u₁ := by
        simpa only [K.T₃_side_one, K.T₃_side_two] using H₃.beam_colour
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour K.skeleton.v₁ := by
        simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour.symm
  · exact K.skeleton.blocker_colour_ne 3
  · exact K.otherColourBound _ (K.skeleton.blocker_colour_ne 3)

/-- Second representative of a length-three beam path. -/
theorem impossible_three_single_path_X_C_D
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 0 1 2)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  apply four_same_colour_card_contradiction
      (x₀ := K.skeleton.v₁) (x₁ := K.skeleton.u₃)
      (x₂ := K.skeleton.u₁) (x₃ := K.skeleton.v₃)
      (red := colour a)
    (K.skeleton_ne 3 2 (by decide))
    (K.skeleton_ne 3 0 (by decide))
    (K.skeleton_ne 3 5 (by decide))
    (K.skeleton_ne 2 0 (by decide))
    (K.skeleton_ne 2 5 (by decide))
    (K.skeleton_ne 0 5 (by decide))
    (K.skeleton_mem_outer 3) (K.skeleton_mem_outer 2)
    (K.skeleton_mem_outer 0) (K.skeleton_mem_outer 5)
  · simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour.symm
  · calc
      colour K.skeleton.u₁ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour K.skeleton.v₁ := by
        simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour.symm
  · calc
      colour K.skeleton.v₃ = colour K.skeleton.u₁ := by
        simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour.symm
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour K.skeleton.v₁ := by
        simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour.symm
  · exact K.skeleton.blocker_colour_ne 3
  · exact K.otherColourBound _ (K.skeleton.blocker_colour_ne 3)

/-- Third representative of a length-three beam path. -/
theorem impossible_three_single_path_Y_C_D
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  apply four_same_colour_card_contradiction
      (x₀ := K.skeleton.u₂) (x₁ := K.skeleton.u₃)
      (x₂ := K.skeleton.u₁) (x₃ := K.skeleton.v₃)
      (red := colour a)
    (K.skeleton_ne 1 2 (by decide))
    (K.skeleton_ne 1 0 (by decide))
    (K.skeleton_ne 1 5 (by decide))
    (K.skeleton_ne 2 0 (by decide))
    (K.skeleton_ne 2 5 (by decide))
    (K.skeleton_ne 0 5 (by decide))
    (K.skeleton_mem_outer 1) (K.skeleton_mem_outer 2)
    (K.skeleton_mem_outer 0) (K.skeleton_mem_outer 5)
  · simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_colour
  · calc
      colour K.skeleton.u₁ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour K.skeleton.u₂ := by
        simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_colour
  · calc
      colour K.skeleton.v₃ = colour K.skeleton.u₁ := by
        simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour.symm
      _ = colour K.skeleton.u₃ := by
        simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
      _ = colour K.skeleton.u₂ := by
        simpa only [K.T₁_side_one, K.T₁_side_two] using H₁.beam_colour
  · exact K.skeleton.blocker_colour_ne 1
  · exact K.otherColourBound _ (K.skeleton.blocker_colour_ne 1)

theorem impossible_three_single_path_Y_A_F
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  exact K.rotate.impossible_three_single_path_X_C_F
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

theorem impossible_three_single_path_Y_C_E
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  exact K.rotate.impossible_three_single_path_Y_A_F
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

theorem impossible_three_single_path_Z_A_F
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 2 0 1)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  exact K.rotate.impossible_three_single_path_X_C_D
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

theorem impossible_three_single_path_Y_B_E
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  exact K.rotate.impossible_three_single_path_Z_A_F
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

theorem impossible_three_single_path_Z_C_F
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 2 0 1)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  exact K.rotate.impossible_three_single_path_Y_C_D
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

theorem impossible_three_single_path_Y_B_F
    {r w p : P}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  exact K.rotate.impossible_three_single_path_Z_C_F
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

/-- The beam colour, the remaining-side colour, and the unique interior
colour exhaust the three nonred colours of a one-point cell. -/
private theorem one_pattern_colour_cover
    {red : Fin 4} {A B C p x : P}
    {T : CellSkeleton P colour red A B C} {i j k : Fin 3}
    (H : OneInteriorPatternAt colour red T p i j k)
    (hxred : colour x ≠ red) (hpred : colour p ≠ red) :
    colour x = colour (T.side i) ∨
      colour x = colour (T.side k) ∨ colour x = colour p := by
  have hired : colour (T.side i) ≠ red := by
    fin_cases i
    · exact T.colour_s₀
    · exact T.colour_s₁
    · exact T.colour_s₂
  have hkred : colour (T.side k) ≠ red := by
    fin_cases k
    · exact T.colour_s₀
    · exact T.colour_s₁
    · exact T.colour_s₂
  exact fin4_eq_one_of_three_of_avoid hxred hired hkred hpred
    H.remaining_colour_ne.symm (H.p_colour_ne k).symm (H.p_colour_ne i)

/-- A path `v₂-u₁-v₃` forces a fourth point of its colour in cell one. -/
theorem impossible_three_single_outer_path_A_D
    {r w p : P} {i j k : Fin 3}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r i j k)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hv₂u₁ : colour K.skeleton.v₂ = colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour
  have hu₁v₃ : colour K.skeleton.u₁ = colour K.skeleton.v₃ := by
    simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour
  have hrI : r ∈ K.I₁ := K.mem_I₁.mpr H₁.hp
  have hcover := one_pattern_colour_cover H₁
    (K.skeleton.blocker_colour_ne 4)
    (K.interior_colour_ne_red₁ r H₁.hp)
  have solve (y : P)
      (hyv₂ : y ≠ K.skeleton.v₂) (hyu₁ : y ≠ K.skeleton.u₁)
      (hyv₃ : y ≠ K.skeleton.v₃)
      (hyHull : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
      (hyColour : colour y = colour K.skeleton.v₂) : False := by
    apply four_same_colour_card_contradiction
        (x₀ := K.skeleton.v₂) (x₁ := K.skeleton.u₁)
        (x₂ := K.skeleton.v₃) (x₃ := y) (red := colour a)
      (K.skeleton_ne 4 0 (by decide))
      (K.skeleton_ne 4 5 (by decide)) hyv₂.symm
      (K.skeleton_ne 0 5 (by decide)) hyu₁.symm hyv₃.symm
      (K.skeleton_mem_outer 4) (K.skeleton_mem_outer 0)
      (K.skeleton_mem_outer 5) hyHull
      hv₂u₁.symm (hu₁v₃.symm.trans hv₂u₁.symm) hyColour
      (K.skeleton.blocker_colour_ne 4)
      (K.otherColourBound _ (K.skeleton.blocker_colour_ne 4))
  rcases hcover with h | h | h
  · apply solve (K.T₁.side i)
    · fin_cases i
      · simpa using K.skeleton_ne 3 4 (by decide)
      · simpa using K.skeleton_ne 2 4 (by decide)
      · simpa using K.skeleton_ne 1 4 (by decide)
    · fin_cases i
      · simpa using K.skeleton_ne 3 0 (by decide)
      · simpa using K.skeleton_ne 2 0 (by decide)
      · simpa using K.skeleton_ne 1 0 (by decide)
    · fin_cases i
      · simpa using K.skeleton_ne 3 5 (by decide)
      · simpa using K.skeleton_ne 2 5 (by decide)
      · simpa using K.skeleton_ne 1 5 (by decide)
    · fin_cases i
      · simpa using K.skeleton_mem_outer 3
      · simpa using K.skeleton_mem_outer 2
      · simpa using K.skeleton_mem_outer 1
    · exact h.symm

  · apply solve (K.T₁.side k)
    · fin_cases k
      · simpa using K.skeleton_ne 3 4 (by decide)
      · simpa using K.skeleton_ne 2 4 (by decide)
      · simpa using K.skeleton_ne 1 4 (by decide)
    · fin_cases k
      · simpa using K.skeleton_ne 3 0 (by decide)
      · simpa using K.skeleton_ne 2 0 (by decide)
      · simpa using K.skeleton_ne 1 0 (by decide)
    · fin_cases k
      · simpa using K.skeleton_ne 3 5 (by decide)
      · simpa using K.skeleton_ne 2 5 (by decide)
      · simpa using K.skeleton_ne 1 5 (by decide)
    · fin_cases k
      · simpa using K.skeleton_mem_outer 3
      · simpa using K.skeleton_mem_outer 2
      · simpa using K.skeleton_mem_outer 1
    · exact h.symm
  · apply solve r
    · exact K.cellPoint_ne_skeleton (Or.inl hrI) 4
    · exact K.cellPoint_ne_skeleton (Or.inl hrI) 0
    · exact K.cellPoint_ne_skeleton (Or.inl hrI) 5
    · exact strictlyInsideTriangle_mem_triangleHull
        (strict_cell_strict_outer K.inside (Or.inl H₁.hp))
    · exact h.symm

/-- Cyclic form: a path `v₁-u₂-v₃` forces its fourth point in cell two. -/
theorem impossible_three_single_outer_path_Z_E
    {r w p : P} {i j k : Fin 3}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 2 0 1)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w i j k)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  exact K.rotate.impossible_three_single_outer_path_A_D
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

/-- Cyclic form: a path `v₁-u₃-v₂` forces its fourth point in cell three. -/
theorem impossible_three_single_outer_path_X_B
    {r w p : P} {i j k : Fin 3}
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 0 1 2)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p i j k) : False := by
  exact K.rotate.impossible_three_single_outer_path_Z_E
    (K.rotateOne₂₁ H₂) (K.rotateOne₃₂ H₃) (K.rotateOne₁₃ H₁)

/-- A positive-side chord from a point of cell one to `v₃` can pass
only through cell one, the portal `u₂`, or cell three. -/
theorem portal_one_to_v₃
    {y s : P} (hy : y ∈ K.I₁)
    (hv₃pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₃ : Point))
    (hs : (s : Point) ∈ openSegment ℝ (y : Point) (K.skeleton.v₃ : Point)) :
    s ∈ K.I₁ ∨ s = K.skeleton.u₂ ∨ s ∈ K.I₃ := by
  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  have hyOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (y : Point) := strict_cell_strict_outer K.inside (Or.inl (K.mem_I₁.mp hy))
  have hsOuter := strict_outer_of_between_strict_hull habc hyOuter
    (K.skeleton_mem_outer 5) hs
  have hspos : 0 < turn (c : Point) (d : Point) (s : Point) :=
    turn_pos_of_between_nonneg hs (K.turn_cd_pos_of_mem_I₁ hy) hv₃pos.le
  have hsHull := strictlyInsideTriangle_mem_triangleHull hsOuter
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton s hsHull with
      hsa | hsb | hsc | hsd | hsu₁ | hsu₂ | hsu₃ |
      hsv₁ | hsv₂ | hsv₃ | hs₁ | hs₂ | hs₃
  · exact ((strictlyInsideTriangle_ne_vertices hsOuter).1
      (congrArg Subtype.val hsa)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.1
      (congrArg Subtype.val hsb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.2
      (congrArg Subtype.val hsc)).elim
  · rw [hsd] at hspos; simp at hspos
  · have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
      have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
        rw [← turn_rotate]
        exact K.inside.2.2
      rw [turn_swap_first] at h
      linarith
    have hu₁neg := turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    rw [hsu₁] at hspos
    linarith
  · exact Or.inr (Or.inl hsu₂)
  · rw [hsu₃, turn_eq_zero_of_between K.skeleton.hu₃] at hspos
    linarith
  · rw [hsv₁] at hsOuter
    linarith [hsOuter.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
  · rw [hsv₂] at hsOuter
    have hz := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz
    linarith [hsOuter.2.2, hz]
  · rw [hsv₃] at hsOuter
    linarith [hsOuter.1, turn_eq_zero_of_between K.skeleton.hv₃]
  · exact Or.inl (K.mem_I₁.mpr hs₁)
  · have hdc := hs₂.2.2
    rw [turn_swap_first] at hdc
    linarith
  · exact Or.inr (Or.inr (K.mem_I₃.mpr hs₃))

set_option maxHeartbeats 1000000 in
/-- The positive cyclic perfect matching `Z-B-D`. -/
theorem impossible_three_single_matching_Z_B_D
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 2 0 1)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 2 0 1)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 2 0 1) : False := by
  have hu₂v₁ : colour K.skeleton.u₂ = colour K.skeleton.v₁ := by
    simpa only [K.T₁_side_two, K.T₁_side_zero] using H₁.beam_colour
  have hu₃v₂ : colour K.skeleton.u₃ = colour K.skeleton.v₂ := by
    simpa only [K.T₂_side_two, K.T₂_side_zero] using H₂.beam_colour
  have hu₁v₃ : colour K.skeleton.u₁ = colour K.skeleton.v₃ := by
    simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_colour
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₁_side_two, K.T₁_side_one] using H₁.remaining_colour_ne.symm
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_two, K.T₂_side_one] using H₂.remaining_colour_ne.symm
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    simpa only [K.T₃_side_two, K.T₃_side_one] using H₃.remaining_colour_ne.symm
  have hru₁ : colour r = colour K.skeleton.u₁ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₁ r (K.mem_I₁.mp hrI))
      (K.skeleton.blocker_colour_ne 1) (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      hu₂u₃ hu₃u₁ hu₁u₂
    rcases hcases with h | h | h
    · exact (H₁.p_colour_ne 2 (by simpa using h)).elim
    · exact (H₁.p_colour_ne 1 (by simpa using h)).elim
    · exact h
  have hwu₂ : colour w = colour K.skeleton.u₂ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI))
      (K.skeleton.blocker_colour_ne 1) (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      hu₂u₃ hu₃u₁ hu₁u₂
    rcases hcases with h | h | h
    · exact h
    · exact (H₂.p_colour_ne 2 (by simpa using h)).elim
    · exact (H₂.p_colour_ne 1 (by simpa using h)).elim
  have hpu₃ : colour p = colour K.skeleton.u₃ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hpI))
      (K.skeleton.blocker_colour_ne 1) (K.skeleton.blocker_colour_ne 2)
      (K.skeleton.blocker_colour_ne 0)
      hu₂u₃ hu₃u₁ hu₁u₂
    rcases hcases with h | h | h
    · exact (H₃.p_colour_ne 1 (by simpa using h)).elim
    · exact h
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hp_u₃ : p ≠ K.skeleton.u₃ :=
      K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
    obtain ⟨s, hs⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    rcases K.portal_three_to_two hpI hpneg
        (K.T₂.nonredPoint_mem_hull (K.T₂.sideLocal 2).property) hs with
      hsI₃ | hsu₁ | hsI₂
    · have hsp := hunique₃ s hsI₃
      exact hp_u₃ (by simpa [hsp] using hs)
    · have hfull := first_pair_points_do_not_block_second K.hfour
          (a := K.skeleton.u₁) (a' := K.skeleton.v₃)
          (b := p) (b' := K.skeleton.u₃)
          (K.skeleton_ne 0 5 (by decide)) hp_u₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0).symm
          (K.skeleton_ne 0 2 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5).symm
          (K.skeleton_ne 5 2 (by decide))
          (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
      exact hfull.1 (by simpa [hsu₁] using hs)
    · have hsw := hunique₂ s hsI₂
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 2 4 (by decide)) hp_u₃.symm
        (by simpa only [K.T₂_side_two, K.T₂_side_zero, openSegment_symm]
          using H₂.beam_between)
        (by simpa [hsw, openSegment_symm] using hs)
      exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 4 heq.symm).elim
  · have hu₁neg : turn (c : Point) (d : Point) (K.skeleton.u₁ : Point) < 0 := by
      have hacd : turn (c : Point) (d : Point) (a : Point) < 0 := by
        have h : 0 < turn (d : Point) (c : Point) (a : Point) := by
          rw [← turn_rotate]
          exact K.inside.2.2
        rw [turn_swap_first] at h
        linarith
      exact turn_neg_of_between_nonpos K.skeleton.hu₁ hacd (by simp)
    have hv₃pos : 0 < turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) :=
      turn_pos_of_right_of_positive_between_nonpos
        (by simpa only [K.T₃_side_two, K.T₃_side_zero] using H₃.beam_between)
        hu₁neg.le hppos
    have hv₃r : colour K.skeleton.v₃ = colour r := hu₁v₃.symm.trans hru₁.symm
    have hv₃_r : K.skeleton.v₃ ≠ r :=
      (K.cellPoint_ne_skeleton (Or.inl hrI) 5).symm
    obtain ⟨s, hs⟩ := K.proper K.skeleton.v₃ r hv₃_r hv₃r
    rcases K.portal_one_to_v₃ hrI hv₃pos (by simpa only [openSegment_symm] using hs) with
      hsI₁ | hsu₂ | hsI₃
    · have hsr := hunique₁ s hsI₁
      exact hv₃_r (by simpa [hsr] using hs)
    · have hfull := first_pair_points_do_not_block_second K.hfour
          (a := K.skeleton.v₁) (a' := K.skeleton.u₂)
          (b := r) (b' := K.skeleton.v₃)
          (K.skeleton_ne 3 1 (by decide)) hv₃_r.symm
          (K.cellPoint_ne_skeleton (Or.inl hrI) 3).symm
          (K.skeleton_ne 3 5 (by decide))
          (K.cellPoint_ne_skeleton (Or.inl hrI) 1).symm
          (K.skeleton_ne 1 5 (by decide))
          (by simpa only [K.T₁_side_two, K.T₁_side_zero, openSegment_symm]
            using H₁.beam_between)
      exact hfull.2 (by simpa [hsu₂, openSegment_symm] using hs)
    · have hsp := hunique₃ s hsI₃
      have hpOn : (p : Point) ∈ openSegment ℝ
          (K.skeleton.v₃ : Point) (r : Point) := by simpa [hsp] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 5 0 (by decide)) hv₃_r
        (by simpa only [K.T₃_side_two, K.T₃_side_zero, openSegment_symm]
          using H₃.beam_between)
        hpOn
      exact (K.cellPoint_ne_skeleton (Or.inl hrI) 0).symm heq

/-- The negative-side counterpart of `portal_one_to_v₃`. -/
theorem portal_two_to_v₃
    {y s : P} (hy : y ∈ K.I₂)
    (hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0)
    (hs : (s : Point) ∈ openSegment ℝ (y : Point) (K.skeleton.v₃ : Point)) :
    s ∈ K.I₂ ∨ s = K.skeleton.u₁ ∨ s ∈ K.I₃ := by
  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  have hyOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (y : Point) := strict_cell_strict_outer K.inside (Or.inr (Or.inl (K.mem_I₂.mp hy)))
  have hsOuter := strict_outer_of_between_strict_hull habc hyOuter
    (K.skeleton_mem_outer 5) hs
  have hsneg : turn (c : Point) (d : Point) (s : Point) < 0 :=
    turn_neg_of_between_nonpos hs (K.turn_cd_neg_of_mem_I₂ hy) hv₃neg.le
  have hsHull := strictlyInsideTriangle_mem_triangleHull hsOuter
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton s hsHull with
      hsa | hsb | hsc | hsd | hsu₁ | hsu₂ | hsu₃ |
      hsv₁ | hsv₂ | hsv₃ | hs₁ | hs₂ | hs₃
  · exact ((strictlyInsideTriangle_ne_vertices hsOuter).1
      (congrArg Subtype.val hsa)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.1
      (congrArg Subtype.val hsb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hsOuter).2.2
      (congrArg Subtype.val hsc)).elim
  · rw [hsd] at hsneg; simp at hsneg
  · exact Or.inr (Or.inl hsu₁)
  · have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using K.inside.2.1
    have hu₂pos := turn_pos_of_between_nonneg K.skeleton.hu₂ hbcd (by simp)
    rw [hsu₂] at hsneg
    linarith
  · rw [hsu₃, turn_eq_zero_of_between K.skeleton.hu₃] at hsneg
    linarith
  · rw [hsv₁] at hsOuter
    linarith [hsOuter.2.1, turn_eq_zero_of_between K.skeleton.hv₁]
  · rw [hsv₂] at hsOuter
    have hz := turn_eq_zero_of_between K.skeleton.hv₂
    rw [turn_swap_first] at hz
    linarith [hsOuter.2.2, hz]
  · rw [hsv₃] at hsOuter
    linarith [hsOuter.1, turn_eq_zero_of_between K.skeleton.hv₃]
  · linarith [K.turn_cd_pos_of_mem_I₁ (K.mem_I₁.mpr hs₁)]
  · exact Or.inl (K.mem_I₂.mpr hs₂)
  · exact Or.inr (Or.inr (K.mem_I₃.mpr hs₃))

set_option maxHeartbeats 1000000 in
/-- The negative cyclic perfect matching `X-A-E`. -/
theorem impossible_three_single_matching_X_A_E
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 0 1 2)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 0 1 2)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 0 1 2) : False := by
  have hv₁u₃ : colour K.skeleton.v₁ = colour K.skeleton.u₃ := by
    simpa only [K.T₁_side_zero, K.T₁_side_one] using H₁.beam_colour
  have hv₂u₁ : colour K.skeleton.v₂ = colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_colour
  have hv₃u₂ : colour K.skeleton.v₃ = colour K.skeleton.u₂ := by
    simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_colour
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    intro h
    exact H₂.remaining_colour_ne (by
      simpa only [K.T₂_side_two, K.T₂_side_zero] using h.trans hv₂u₁.symm)
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    intro h
    exact H₃.remaining_colour_ne (by
      simpa only [K.T₃_side_two, K.T₃_side_zero] using h.trans hv₃u₂.symm)
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ := by
    intro h
    exact H₁.remaining_colour_ne (by
      simpa only [K.T₁_side_two, K.T₁_side_zero] using h.trans hv₁u₃.symm)
  have hru₁ : colour r = colour K.skeleton.u₁ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₁ r (K.mem_I₁.mp hrI))
      (K.skeleton.blocker_colour_ne 2) (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      hu₃u₁ hu₁u₂ hu₂u₃
    rcases hcases with h | h | h
    · exact (H₁.p_colour_ne 1 (by simpa using h)).elim
    · exact h
    · exact (H₁.p_colour_ne 2 (by simpa using h)).elim
  have hwu₂ : colour w = colour K.skeleton.u₂ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI))
      (K.skeleton.blocker_colour_ne 2) (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      hu₃u₁ hu₁u₂ hu₂u₃
    rcases hcases with h | h | h
    · exact (H₂.p_colour_ne 2 (by simpa using h)).elim
    · exact (H₂.p_colour_ne 1 (by simpa using h)).elim
    · exact h
  have hpu₃ : colour p = colour K.skeleton.u₃ := by
    have hcases := fin4_eq_one_of_three_of_avoid
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hpI))
      (K.skeleton.blocker_colour_ne 2) (K.skeleton.blocker_colour_ne 0)
      (K.skeleton.blocker_colour_ne 1)
      hu₃u₁ hu₁u₂ hu₂u₃
    rcases hcases with h | h | h
    · exact h
    · exact (H₃.p_colour_ne 2 (by simpa using h)).elim
    · exact (H₃.p_colour_ne 1 (by simpa using h)).elim
  have hpne := K.turn_cd_ne_zero_of_mem_I₃ hpI
  rcases lt_or_gt_of_ne hpne with hpneg | hppos
  · have hbcd : 0 < turn (c : Point) (d : Point) (b : Point) := by
      simpa only [turn_rotate] using K.inside.2.1
    have hu₂pos : 0 < turn (c : Point) (d : Point) (K.skeleton.u₂ : Point) :=
      turn_pos_of_between_nonneg K.skeleton.hu₂ hbcd (by simp)
    have hv₃neg : turn (c : Point) (d : Point) (K.skeleton.v₃ : Point) < 0 :=
      turn_neg_of_right_of_negative_between_nonneg
        (by
          rw [openSegment_symm]
          simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
        hu₂pos.le hpneg
    have hv₃w : colour K.skeleton.v₃ = colour w := hv₃u₂.trans hwu₂.symm
    have hv₃_w : K.skeleton.v₃ ≠ w :=
      (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 5).symm
    obtain ⟨s, hs⟩ := K.proper K.skeleton.v₃ w hv₃_w hv₃w
    rcases K.portal_two_to_v₃ hwI hv₃neg (by simpa only [openSegment_symm] using hs) with
      hsI₂ | hsu₁ | hsI₃
    · have hsw := hunique₂ s hsI₂
      exact hv₃_w (by simpa [hsw] using hs)
    · have hfull := first_pair_points_do_not_block_second K.hfour
          (a := K.skeleton.v₂) (a' := K.skeleton.u₁)
          (b := w) (b' := K.skeleton.v₃)
          (K.skeleton_ne 4 0 (by decide)) hv₃_w.symm
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 4).symm
          (K.skeleton_ne 4 5 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 0).symm
          (K.skeleton_ne 0 5 (by decide))
          (by simpa only [K.T₂_side_zero, K.T₂_side_one] using H₂.beam_between)
      exact hfull.2 (by simpa [hsu₁, openSegment_symm] using hs)
    · have hsp := hunique₃ s hsI₃
      have hpOn : (p : Point) ∈ openSegment ℝ
          (K.skeleton.v₃ : Point) (w : Point) := by simpa [hsp] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 5 1 (by decide)) hv₃_w
        (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
        hpOn
      exact (K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 1).symm heq
  · have hp_u₃ : p ≠ K.skeleton.u₃ :=
      K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
    obtain ⟨s, hs⟩ := K.proper p K.skeleton.u₃ hp_u₃ hpu₃
    rcases K.portal_three_to_one hpI hppos
        (K.T₁.nonredPoint_mem_hull (K.T₁.sideLocal 1).property) hs with
      hsI₃ | hsu₂ | hsI₁
    · have hsp := hunique₃ s hsI₃
      exact hp_u₃ (by simpa [hsp] using hs)
    · have hfull := first_pair_points_do_not_block_second K.hfour
          (a := K.skeleton.v₃) (a' := K.skeleton.u₂)
          (b := p) (b' := K.skeleton.u₃)
          (K.skeleton_ne 5 1 (by decide)) hp_u₃
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 5).symm
          (K.skeleton_ne 5 2 (by decide))
          (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1).symm
          (K.skeleton_ne 1 2 (by decide))
          (by simpa only [K.T₃_side_zero, K.T₃_side_one] using H₃.beam_between)
      exact hfull.2 (by simpa [hsu₂] using hs)
    · have hsr := hunique₁ s hsI₁
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 2 3 (by decide)) hp_u₃.symm
        (by simpa only [K.T₁_side_zero, K.T₁_side_one, openSegment_symm]
          using H₁.beam_between)
        (by simpa [hsr, openSegment_symm] using hs)
      exact (K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 3 heq.symm).elim

/-- In the central `Y-C-F` arrangement, the red centre is the unique point
of `P` lying strictly inside both the outer triangle and the triangle of
the three spoke blockers. -/
private theorem central_strict_outer_eq_center
    {r w p z : P}
    (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ x : P, x ∈ K.I₁ → x = r)
    (hunique₂ : ∀ x : P, x ∈ K.I₂ → x = w)
    (hunique₃ : ∀ x : P, x ∈ K.I₃ → x = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0)
    (hzCentral : StrictlyInsideTriangle
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (z : Point))
    (hzOuter : StrictlyInsideTriangle
      (a : Point) (b : Point) (c : Point) (z : Point)) : z = d := by
  have hzHull := strictlyInsideTriangle_mem_triangleHull hzOuter
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton z hzHull with
      hza | hzb | hzc | hzd | hzu₁ | hzu₂ | hzu₃ |
      hzv₁ | hzv₂ | hzv₃ | hz₁ | hz₂ | hz₃
  · exact ((strictlyInsideTriangle_ne_vertices hzOuter).1
      (congrArg Subtype.val hza)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hzOuter).2.1
      (congrArg Subtype.val hzb)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hzOuter).2.2
      (congrArg Subtype.val hzc)).elim
  · exact hzd
  · exact ((strictlyInsideTriangle_ne_vertices hzCentral).1
      (congrArg Subtype.val hzu₁)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hzCentral).2.1
      (congrArg Subtype.val hzu₂)).elim
  · exact ((strictlyInsideTriangle_ne_vertices hzCentral).2.2
      (congrArg Subtype.val hzu₃)).elim
  · rw [hzv₁] at hzCentral
    linarith [hzCentral.2.1, K.v₁_spoke_side_neg]
  · rw [hzv₂] at hzCentral
    linarith [hzCentral.2.2, K.v₂_spoke_side_neg]
  · rw [hzv₃] at hzCentral
    linarith [hzCentral.1, K.v₃_spoke_side_neg]
  · have hzr := hunique₁ z (K.mem_I₁.mpr hz₁)
    rw [hzr] at hzCentral
    have hz0 : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
        (r : Point) = 0 := turn_eq_zero_of_between (by
      simpa only [K.T₁_side_one, K.T₁_side_two, openSegment_symm]
        using H₁.beam_between)
    linarith [hzCentral.2.1, hz0]
  · have hzw := hunique₂ z (K.mem_I₂.mpr hz₂)
    rw [hzw] at hzCentral
    have hz0 : turn (K.skeleton.u₃ : Point) (K.skeleton.u₁ : Point)
        (w : Point) = 0 := turn_eq_zero_of_between (by
      simpa only [K.T₂_side_one, K.T₂_side_two, openSegment_symm]
        using H₂.beam_between)
    linarith [hzCentral.2.2, hz0]
  · have hzp := hunique₃ z (K.mem_I₃.mpr hz₃)
    rw [hzp] at hzCentral
    have hz0 : turn (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
        (p : Point) = 0 := turn_eq_zero_of_between (by
      simpa only [K.T₃_side_one, K.T₃_side_two, openSegment_symm]
        using H₃.beam_between)
    linarith [hzCentral.1, hz0]

set_option maxHeartbeats 1000000 in
/-- The central `Y-C-F` arrangement is impossible when the first two beam
blockers have the same colour.  Cyclic relabeling will handle either of the
other two equal-colour pairs. -/
private theorem impossible_three_single_central_of_first_second
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0)
    (hrwColour : colour r = colour w) : False := by
  have hrBeam : (r : Point) ∈ openSegment ℝ
      (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point) := by
    simpa only [K.T₁_side_one, K.T₁_side_two, openSegment_symm]
      using H₁.beam_between
  have hwBeam : (w : Point) ∈ openSegment ℝ
      (K.skeleton.u₃ : Point) (K.skeleton.u₁ : Point) := by
    simpa only [K.T₂_side_one, K.T₂_side_two, openSegment_symm]
      using H₂.beam_between
  have hpBeam : (p : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point) := by
    simpa only [K.T₃_side_one, K.T₃_side_two, openSegment_symm]
      using H₃.beam_between
  have hrOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (r : Point) := strict_cell_strict_outer K.inside
        (Or.inl (K.mem_I₁.mp hrI))
  have hwOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (w : Point) := strict_cell_strict_outer K.inside
        (Or.inr (Or.inl (K.mem_I₂.mp hwI)))
  have hpOuter : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (p : Point) := strict_cell_strict_outer K.inside
        (Or.inr (Or.inr (K.mem_I₃.mp hpI)))
  have hrw : r ≠ w := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.1) hrI (e ▸ hwI)
  have hrp : r ≠ p := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.1) hrI (e ▸ hpI)
  have hwp : w ≠ p := by
    intro e
    exact (Finset.disjoint_left.mp cellPoints_pairwise_disjoint.2.2) hwI (e ▸ hpI)
  have hcenter := K.red_center_strictly_inside_spoke_triangle
  have hcenterPos := turn_pos_of_strictlyInsideTriangle hcenter
  have hcenterRot : 0 < turn (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (K.skeleton.u₁ : Point) := by
    simpa only [turn_rotate] using hcenterPos

  obtain ⟨s₀, hs₀⟩ := K.proper r w hrw hrwColour
  have hs₀Rot : StrictlyInsideTriangle
      (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) (s₀ : Point) :=
    strictlyInside_between_adjacent_sides hcenterRot hrBeam hwBeam hs₀
  have hs₀Central : StrictlyInsideTriangle
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (s₀ : Point) :=
    ⟨hs₀Rot.2.2, hs₀Rot.1, hs₀Rot.2.1⟩
  have hs₀Outer := strictlyInside_between_inside_points hrOuter hwOuter hs₀
  have hs₀d := K.central_strict_outer_eq_center hrI hwI hpI
    hunique₁ hunique₂ hunique₃ H₁ H₂ H₃ hs₀Central hs₀Outer
  have hdRW : (d : Point) ∈ openSegment ℝ (r : Point) (w : Point) := by
    simpa only [hs₀d] using hs₀

  have hprColour : colour p ≠ colour r := by
    intro hprc
    obtain ⟨t₀, ht₀⟩ := K.proper r p hrp hprc.symm
    have ht₀Central := strictlyInside_between_adjacent_sides hcenterPos hpBeam hrBeam
      (by simpa only [openSegment_symm] using ht₀)
    have ht₀Outer := strictlyInside_between_inside_points hrOuter hpOuter ht₀
    have ht₀d := K.central_strict_outer_eq_center hrI hwI hpI
      hunique₁ hunique₂ hunique₃ H₁ H₂ H₃ ht₀Central ht₀Outer
    have hdRP : (d : Point) ∈ openSegment ℝ (r : Point) (p : Point) := by
      simpa only [ht₀d] using ht₀
    have heq := other_endpoint_eq_of_common_blocker K.hfour hrw hrp hdRW hdRP
    exact hwp heq

  have hv₃rColour : colour K.skeleton.v₃ = colour r := by
    have hcover := one_pattern_colour_cover H₃
      (K.interior_colour_ne_red₁ r (K.mem_I₁.mp hrI))
      (K.interior_colour_ne_red₃ p (K.mem_I₃.mp hpI))
    rcases hcover with hru₂ | hrv₃ | hrpColour
    · exact (H₁.p_colour_ne 2 (by
        simpa only [K.T₁_side_two, K.T₃_side_one] using hru₂)).elim
    · simpa only [K.T₃_side_zero] using hrv₃.symm
    · exact (hprColour hrpColour.symm).elim

  have hr_v₃ : r ≠ K.skeleton.v₃ :=
    K.cellPoint_ne_skeleton (Or.inl hrI) 5
  have hw_v₃ : w ≠ K.skeleton.v₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 5
  have hr_u₁ : r ≠ K.skeleton.u₁ :=
    K.cellPoint_ne_skeleton (Or.inl hrI) 0
  have hr_u₂ : r ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inl hrI) 1
  have hr_u₃ : r ≠ K.skeleton.u₃ :=
    K.cellPoint_ne_skeleton (Or.inl hrI) 2
  have hw_u₁ : w ≠ K.skeleton.u₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 0
  have hw_u₂ : w ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 1
  have hw_u₃ : w ≠ K.skeleton.u₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inl hwI)) 2
  have hp_u₁ : p ≠ K.skeleton.u₁ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 0
  have hp_u₂ : p ≠ K.skeleton.u₂ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 1
  have hp_u₃ : p ≠ K.skeleton.u₃ :=
    K.cellPoint_ne_skeleton (Or.inr (Or.inr hpI)) 2
  have hv₃d : K.skeleton.v₃ ≠ d := by
    intro e
    apply K.skeleton.blocker_colour_ne 5
    rw [e]
    exact K.monoD.symm

  have hRLine := first_pair_points_do_not_block_second K.hfour
    (K.skeleton_ne 1 2 (by decide)) hr_v₃
    hr_u₂.symm (K.skeleton_ne 1 5 (by decide))
    hr_u₃.symm (K.skeleton_ne 2 5 (by decide)) hrBeam
  have hWLine := first_pair_points_do_not_block_second K.hfour
    (K.skeleton_ne 2 0 (by decide)) hw_v₃
    hw_u₃.symm (K.skeleton_ne 2 5 (by decide))
    hw_u₁.symm (K.skeleton_ne 0 5 (by decide)) hwBeam

  obtain ⟨s, hs⟩ := K.proper r K.skeleton.v₃ hr_v₃ hv₃rColour.symm
  have hsCases : s = K.skeleton.u₁ ∨ s = p := by
    rcases K.strict_outer_chord_cases hrOuter (K.skeleton_mem_outer 5) hs with
      hsd | hsu₁ | hsu₂ | hsu₃ | hsI₁ | hsI₂ | hsI₃
    · have hdRV : (d : Point) ∈ openSegment ℝ
          (r : Point) (K.skeleton.v₃ : Point) := by simpa only [hsd] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour hrw hr_v₃ hdRW hdRV
      exact (hw_v₃ heq).elim
    · exact Or.inl hsu₁
    · exact (hRLine.1 (by simpa only [hsu₂] using hs)).elim
    · exact (hRLine.2 (by simpa only [hsu₃] using hs)).elim
    · have hsr := hunique₁ s hsI₁
      subst s
      have hm := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hs
      exact (Subtype.val_injective.ne hr_v₃ hm).elim
    · have hsw := hunique₂ s hsI₂
      have hwOn : (w : Point) ∈ openSegment ℝ
          (r : Point) (K.skeleton.v₃ : Point) := by simpa only [hsw] using hs
      have hvZero : turn (r : Point) (w : Point)
          (K.skeleton.v₃ : Point) = 0 := by
        have hz := turn_eq_zero_of_between hwOn
        rw [turn_swap_last] at hz
        linarith
      rcases point_eq_of_on_full_line K.hfour hrw hdRW hvZero with
        hvr | hvw | hvd
      · exact (hr_v₃ hvr.symm).elim
      · exact (hw_v₃ hvw.symm).elim
      · exact (hv₃d hvd).elim
    · exact Or.inr (hunique₃ s hsI₃)

  obtain ⟨t, ht⟩ := K.proper w K.skeleton.v₃ hw_v₃
    (hrwColour.symm.trans hv₃rColour.symm)
  have htCases : t = K.skeleton.u₂ ∨ t = p := by
    rcases K.strict_outer_chord_cases hwOuter (K.skeleton_mem_outer 5) ht with
      htd | htu₁ | htu₂ | htu₃ | htI₁ | htI₂ | htI₃
    · have hdWV : (d : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₃ : Point) := by simpa only [htd] using ht
      have heq := other_endpoint_eq_of_common_blocker K.hfour hrw.symm hw_v₃
        (by simpa only [openSegment_symm] using hdRW) hdWV
      exact (hr_v₃ heq).elim
    · exact (hWLine.2 (by simpa only [htu₁] using ht)).elim
    · exact Or.inl htu₂
    · exact (hWLine.1 (by simpa only [htu₃] using ht)).elim
    · have htr := hunique₁ t htI₁
      have hrOn : (r : Point) ∈ openSegment ℝ
          (w : Point) (K.skeleton.v₃ : Point) := by simpa only [htr] using ht
      have hvZero : turn (r : Point) (w : Point)
          (K.skeleton.v₃ : Point) = 0 := by
        have hz := turn_eq_zero_of_between hrOn
        rw [← turn_rotate, ← turn_rotate] at hz
        exact hz
      rcases point_eq_of_on_full_line K.hfour hrw hdRW hvZero with
        hvr | hvw | hvd
      · exact (hr_v₃ hvr.symm).elim
      · exact (hw_v₃ hvw.symm).elim
      · exact (hv₃d hvd).elim
    · have htw := hunique₂ t htI₂
      subst t
      have hm := (left_mem_openSegment_iff (𝕜 := ℝ)).mp ht
      exact (Subtype.val_injective.ne hw_v₃ hm).elim
    · exact Or.inr (hunique₃ t htI₃)

  have hL₃₁u₂ : 0 < turn (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) (K.skeleton.u₂ : Point) := by
    simpa only [turn_rotate, turn_rotate] using hcenterPos
  have hL₃₁r : 0 < turn (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) (r : Point) :=
    turn_pos_of_between_nonneg hrBeam hL₃₁u₂ (by simp)
  have hL₃₁p : 0 < turn (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) (p : Point) :=
    turn_pos_of_between_nonneg (by simpa only [openSegment_symm] using hpBeam)
      hL₃₁u₂ (by simp)
  have hL₂₃u₁ : 0 < turn (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (K.skeleton.u₁ : Point) := hcenterRot
  have hwBeam' : (w : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.u₃ : Point) := by
    rw [openSegment_symm]
    exact hwBeam
  have hL₂₃w : 0 < turn (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (w : Point) :=
    turn_pos_of_between_nonneg hwBeam' hL₂₃u₁ (by simp)
  have hL₂₃p : 0 < turn (K.skeleton.u₂ : Point)
      (K.skeleton.u₃ : Point) (p : Point) :=
    turn_pos_of_between_nonneg hpBeam hL₂₃u₁ (by simp)

  rcases hsCases with hsu₁ | hsp <;> rcases htCases with htu₂ | htp
  · have hsu₁' : (K.skeleton.u₁ : Point) ∈ openSegment ℝ
        (r : Point) (K.skeleton.v₃ : Point) := by simpa only [hsu₁] using hs
    have htu₂' : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
        (w : Point) (K.skeleton.v₃ : Point) := by simpa only [htu₂] using ht
    have hvNeg := turn_neg_beyond_zero_from_pos hsu₁' hL₃₁r (by simp)
    have hvPos := turn_pos_of_right_of_positive_between_nonpos htu₂'
      (turn_eq_zero_of_between hwBeam).le hL₃₁u₂
    linarith
  · have hsu₁' : (K.skeleton.u₁ : Point) ∈ openSegment ℝ
        (r : Point) (K.skeleton.v₃ : Point) := by simpa only [hsu₁] using hs
    have htp' : (p : Point) ∈ openSegment ℝ
        (w : Point) (K.skeleton.v₃ : Point) := by simpa only [htp] using ht
    have hvNeg := turn_neg_beyond_zero_from_pos hsu₁' hL₃₁r (by simp)
    have hvPos := turn_pos_of_right_of_positive_between_nonpos htp'
      (turn_eq_zero_of_between hwBeam).le hL₃₁p
    linarith
  · have hsp' : (p : Point) ∈ openSegment ℝ
        (r : Point) (K.skeleton.v₃ : Point) := by simpa only [hsp] using hs
    have htu₂' : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
        (w : Point) (K.skeleton.v₃ : Point) := by simpa only [htu₂] using ht
    have hvPos := turn_pos_of_right_of_positive_between_nonpos hsp'
      (turn_eq_zero_of_between hrBeam).le hL₂₃p
    have hvNeg := turn_neg_beyond_zero_from_pos htu₂' hL₂₃w (by simp)
    linarith
  · have hsp' : (p : Point) ∈ openSegment ℝ
        (r : Point) (K.skeleton.v₃ : Point) := by simpa only [hsp] using hs
    have htp' : (p : Point) ∈ openSegment ℝ
        (w : Point) (K.skeleton.v₃ : Point) := by simpa only [htp] using ht
    have heq := other_endpoint_eq_of_common_blocker K.hfour hr_v₃.symm hw_v₃.symm
      (by simpa only [openSegment_symm] using hsp')
      (by simpa only [openSegment_symm] using htp')
    exact hrw heq

/-- The last of the twenty-seven one-point-per-cell beam arrangements:
the three beams are the sides of the central spoke triangle. -/
theorem impossible_three_single_central_Y_C_F
    {r w p : P} (hrI : r ∈ K.I₁) (hwI : w ∈ K.I₂) (hpI : p ∈ K.I₃)
    (hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r)
    (hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w)
    (hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p)
    (H₁ : OneInteriorPatternAt colour (colour a) K.T₁ r 1 2 0)
    (H₂ : OneInteriorPatternAt colour (colour a) K.T₂ w 1 2 0)
    (H₃ : OneInteriorPatternAt colour (colour a) K.T₃ p 1 2 0) : False := by
  have hu₁u₃ : colour K.skeleton.u₁ = colour K.skeleton.u₃ := by
    simpa only [K.T₂_side_one, K.T₂_side_two] using H₂.beam_colour
  have hrα : colour r ≠ colour K.skeleton.u₁ := by
    intro h
    exact H₁.p_colour_ne 1 (by
      simpa only [K.T₁_side_one] using h.trans hu₁u₃)
  have hwα : colour w ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_one] using H₂.p_colour_ne 1
  have hpα : colour p ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₃_side_two] using H₃.p_colour_ne 2
  have hrred := K.interior_colour_ne_red₁ r (K.mem_I₁.mp hrI)
  have hwred := K.interior_colour_ne_red₂ w (K.mem_I₂.mp hwI)
  have hpred := K.interior_colour_ne_red₃ p (K.mem_I₃.mp hpI)
  have hαred : colour K.skeleton.u₁ ≠ colour a :=
    K.skeleton.blocker_colour_ne 0
  have hpigeon : colour r = colour w ∨ colour w = colour p ∨
      colour p = colour r := by
    omega
  rcases hpigeon with hrw | hwp | hpr
  · exact K.impossible_three_single_central_of_first_second hrI hwI hpI
      hunique₁ hunique₂ hunique₃ H₁ H₂ H₃ hrw
  · apply K.rotate.impossible_three_single_central_of_first_second
      (r := w) (w := p) (p := r)
    · simpa only [K.rotate_I₁] using hwI
    · simpa only [K.rotate_I₂] using hpI
    · simpa only [K.rotate_I₃] using hrI
    · intro z hz
      exact hunique₂ z (by simpa only [K.rotate_I₁] using hz)
    · intro z hz
      exact hunique₃ z (by simpa only [K.rotate_I₂] using hz)
    · intro z hz
      exact hunique₁ z (by simpa only [K.rotate_I₃] using hz)
    · exact K.rotateOne₂₁ H₂
    · exact K.rotateOne₃₂ H₃
    · exact K.rotateOne₁₃ H₁
    · exact hwp
  · apply K.rotate.rotate.impossible_three_single_central_of_first_second
      (r := p) (w := r) (p := w)
    · simpa only [ConcaveConfiguration.rotate_I₁,
        ConcaveConfiguration.rotate_I₂] using hpI
    · simpa only [ConcaveConfiguration.rotate_I₁,
        ConcaveConfiguration.rotate_I₃] using hrI
    · simpa only [ConcaveConfiguration.rotate_I₂,
        ConcaveConfiguration.rotate_I₃] using hwI
    · intro z hz
      exact hunique₃ z (by simpa only [ConcaveConfiguration.rotate_I₁,
        ConcaveConfiguration.rotate_I₂] using hz)
    · intro z hz
      exact hunique₁ z (by simpa only [ConcaveConfiguration.rotate_I₁,
        ConcaveConfiguration.rotate_I₃] using hz)
    · intro z hz
      exact hunique₂ z (by simpa only [ConcaveConfiguration.rotate_I₂,
        ConcaveConfiguration.rotate_I₃] using hz)
    · exact K.rotate.rotateOne₂₁ (K.rotateOne₃₂ H₃)
    · exact K.rotate.rotateOne₃₂ (K.rotateOne₁₃ H₁)
    · exact K.rotate.rotateOne₁₃ (K.rotateOne₂₁ H₂)
    · exact hpr

/-- Complete elimination of the `(1,1,1)` cell distribution.  The
twenty-seven local beam choices split into the two perfect matchings, the
central triangle, six mixed path-plus-edge arrangements, nine four-vertex
paths, and nine outer-path arrangements. -/
theorem impossible_I₁_one_I₂_one_I₃_one
    (h₁ : K.I₁.card = 1) (h₂ : K.I₂.card = 1)
    (h₃ : K.I₃.card = 1) : False := by
  obtain ⟨r, hrSet⟩ := Finset.card_eq_one.mp h₁
  obtain ⟨w, hwSet⟩ := Finset.card_eq_one.mp h₂
  obtain ⟨p, hpSet⟩ := Finset.card_eq_one.mp h₃
  have hrI : r ∈ K.I₁ := by rw [hrSet]; simp
  have hwI : w ∈ K.I₂ := by rw [hwSet]; simp
  have hpI : p ∈ K.I₃ := by rw [hpSet]; simp
  have hunique₁ : ∀ z : P, z ∈ K.I₁ → z = r := by
    intro z hz
    rw [hrSet] at hz
    simpa using hz
  have hunique₂ : ∀ z : P, z ∈ K.I₂ → z = w := by
    intro z hz
    rw [hwSet] at hz
    simpa using hz
  have hunique₃ : ∀ z : P, z ∈ K.I₃ → z = p := by
    intro z hz
    rw [hpSet] at hz
    simpa using hz
  have H₁ := K.M₁.one_interior_pattern K.hfour (K.mem_I₁.mp hrI)
    (fun z hz ↦ hunique₁ z (K.mem_I₁.mpr hz))
  have H₂ := K.M₂.one_interior_pattern K.hfour (K.mem_I₂.mp hwI)
    (fun z hz ↦ hunique₂ z (K.mem_I₂.mpr hz))
  have H₃ := K.M₃.one_interior_pattern K.hfour (K.mem_I₃.mp hpI)
    (fun z hz ↦ hunique₃ z (K.mem_I₃.mpr hz))
  rcases H₁ with HX | HY | HZ
  · rcases H₂ with HA | HC | HB
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_matching_X_A_E hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HX HA HE
      · exact K.impossible_three_single_mixed_X_A_F hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HX HA HF
      · exact K.impossible_three_single_outer_path_A_D HX HA HD
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_mixed_X_C_E hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HX HC HE
      · exact K.impossible_three_single_path_X_C_F HX HC HF
      · exact K.impossible_three_single_path_X_C_D HX HC HD
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_outer_path_X_B HX HB HE
      · exact K.impossible_three_single_outer_path_X_B HX HB HF
      · exact K.impossible_three_single_outer_path_X_B HX HB HD
  · rcases H₂ with HA | HC | HB
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_mixed_Y_A_E hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HY HA HE
      · exact K.impossible_three_single_path_Y_A_F HY HA HF
      · exact K.impossible_three_single_outer_path_A_D HY HA HD
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_path_Y_C_E HY HC HE
      · exact K.impossible_three_single_central_Y_C_F hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HY HC HF
      · exact K.impossible_three_single_path_Y_C_D HY HC HD
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_path_Y_B_E HY HB HE
      · exact K.impossible_three_single_path_Y_B_F HY HB HF
      · exact K.impossible_three_single_mixed_Y_B_D hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HY HB HD
  · rcases H₂ with HA | HC | HB
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_outer_path_Z_E HZ HA HE
      · exact K.impossible_three_single_path_Z_A_F HZ HA HF
      · exact K.impossible_three_single_outer_path_A_D HZ HA HD
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_outer_path_Z_E HZ HC HE
      · exact K.impossible_three_single_path_Z_C_F HZ HC HF
      · exact K.impossible_three_single_mixed_Z_C_D hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HZ HC HD
    · rcases H₃ with HE | HF | HD
      · exact K.impossible_three_single_outer_path_Z_E HZ HB HE
      · exact K.impossible_three_single_mixed_Z_B_F hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HZ HB HF
      · exact K.impossible_three_single_matching_Z_B_D hrI hwI hpI
          hunique₁ hunique₂ hunique₃ HZ HB HD

/-- With all three cells empty, the six skeleton blockers have matching
colours `uᵢ,vᵢ`, and their three blocking incidences form one of the two
directed 3-cycles. -/
theorem empty_cells_incidence_cycles
    (h₁ : K.I₁ = ∅) (h₂ : K.I₂ = ∅) (h₃ : K.I₃ = ∅) :
    (((K.skeleton.u₂ : Point) ∈ openSegment ℝ
        (K.skeleton.u₁ : Point) (K.skeleton.v₁ : Point)) ∧
      ((K.skeleton.u₃ : Point) ∈ openSegment ℝ
        (K.skeleton.u₂ : Point) (K.skeleton.v₂ : Point)) ∧
      ((K.skeleton.u₁ : Point) ∈ openSegment ℝ
        (K.skeleton.u₃ : Point) (K.skeleton.v₃ : Point))) ∨
    (((K.skeleton.u₃ : Point) ∈ openSegment ℝ
        (K.skeleton.u₁ : Point) (K.skeleton.v₁ : Point)) ∧
      ((K.skeleton.u₁ : Point) ∈ openSegment ℝ
        (K.skeleton.u₂ : Point) (K.skeleton.v₂ : Point)) ∧
      ((K.skeleton.u₂ : Point) ∈ openSegment ℝ
        (K.skeleton.u₃ : Point) (K.skeleton.v₃ : Point))) := by
  have hp₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [h₁]))
  have hp₂ := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [h₂]))
  have hp₃ := K.M₃.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₃ (by simpa [h₃]))
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₁_side_two, K.T₁_side_one] using
      hp₁ (i := 2) (j := 1) (by decide)
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_two, K.T₂_side_one] using
      hp₂ (i := 2) (j := 1) (by decide)
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    simpa only [K.T₃_side_two, K.T₃_side_one] using
      hp₃ (i := 2) (j := 1) (by decide)
  have hu₁v₁ : colour K.skeleton.u₁ = colour K.skeleton.v₁ := by
    obtain ⟨i, hi⟩ := colour_eq_some_side K.T₁ hp₁ K.skeleton.u₁
      (K.skeleton.blocker_colour_ne 0)
    fin_cases i
    · simpa only [K.T₁_side_zero] using hi
    · exact (hu₃u₁ (by simpa only [K.T₁_side_one] using hi.symm)).elim
    · exact (hu₁u₂ (by simpa only [K.T₁_side_two] using hi)).elim
  have hu₂v₂ : colour K.skeleton.u₂ = colour K.skeleton.v₂ := by
    obtain ⟨i, hi⟩ := colour_eq_some_side K.T₂ hp₂ K.skeleton.u₂
      (K.skeleton.blocker_colour_ne 1)
    fin_cases i
    · simpa only [K.T₂_side_zero] using hi
    · exact (hu₁u₂ (by simpa only [K.T₂_side_one] using hi.symm)).elim
    · exact (hu₂u₃ (by simpa only [K.T₂_side_two] using hi)).elim
  have hu₃v₃ : colour K.skeleton.u₃ = colour K.skeleton.v₃ := by
    obtain ⟨i, hi⟩ := colour_eq_some_side K.T₃ hp₃ K.skeleton.u₃
      (K.skeleton.blocker_colour_ne 2)
    fin_cases i
    · simpa only [K.T₃_side_zero] using hi
    · exact (hu₂u₃ (by simpa only [K.T₃_side_one] using hi.symm)).elim
    · exact (hu₃u₁ (by simpa only [K.T₃_side_two] using hi)).elim

  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  have haHull : (a : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    vertex_mem_triangleHull _ _ _
  have hbHull : (b : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    subset_convexHull ℝ _ (by simp [triangleHull])
  have hcHull : (c : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) :=
    subset_convexHull ℝ _ (by simp [triangleHull])
  have hu₁Outer : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (K.skeleton.u₁ : Point) :=
    strict_outer_of_between_strict_hull habc K.inside haHull
      (by simpa only [openSegment_symm] using K.skeleton.hu₁)
  have hu₂Outer : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (K.skeleton.u₂ : Point) :=
    strict_outer_of_between_strict_hull habc K.inside hbHull
      (by simpa only [openSegment_symm] using K.skeleton.hu₂)
  have hu₃Outer : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (K.skeleton.u₃ : Point) :=
    strict_outer_of_between_strict_hull habc K.inside hcHull
      (by simpa only [openSegment_symm] using K.skeleton.hu₃)
  have hv₁red : colour K.skeleton.v₁ ≠ colour a := by
    simpa using K.skeleton.blocker_colour_ne 3
  have hv₂red : colour K.skeleton.v₂ ≠ colour a := by
    simpa using K.skeleton.blocker_colour_ne 4
  have hv₃red : colour K.skeleton.v₃ ≠ colour a := by
    simpa using K.skeleton.blocker_colour_ne 5
  have ha_v₁ : a ≠ K.skeleton.v₁ := by
    intro e
    apply hv₁red
    rw [← e]
  have hb_v₂ : b ≠ K.skeleton.v₂ := by
    intro e
    apply hv₂red
    rw [← e]
    exact K.monoB.symm
  have hc_v₃ : c ≠ K.skeleton.v₃ := by
    intro e
    apply hv₃red
    rw [← e]
    exact K.monoC.symm

  obtain ⟨s₁, hs₁⟩ := K.proper K.skeleton.u₁ K.skeleton.v₁
    (K.skeleton_ne 0 3 (by decide)) hu₁v₁
  have hs₁Cases : s₁ = K.skeleton.u₂ ∨ s₁ = K.skeleton.u₃ := by
    rcases K.strict_outer_chord_cases hu₁Outer (K.skeleton_mem_outer 3) hs₁ with
      hsd | hsu₁ | hsu₂ | hsu₃ | hsI₁ | hsI₂ | hsI₃
    · have hdOn : (d : Point) ∈ openSegment ℝ
          (K.skeleton.u₁ : Point) (K.skeleton.v₁ : Point) := by
        simpa only [hsd] using hs₁
      exact (not_nested_openSegments K.hfour ha_v₁ K.had
        (K.skeleton_ne 0 3 (by decide)) K.skeleton.hu₁ hdOn).elim
    · subst s₁
      have hm := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hs₁
      exact ((Subtype.val_injective.ne (K.skeleton_ne 0 3 (by decide))) hm).elim
    · exact Or.inl hsu₂
    · exact Or.inr hsu₃
    · have hm : s₁ ∈ (∅ : Finset P) := by simpa only [h₁] using hsI₁
      simp at hm
    · have hm : s₁ ∈ (∅ : Finset P) := by simpa only [h₂] using hsI₂
      simp at hm
    · have hm : s₁ ∈ (∅ : Finset P) := by simpa only [h₃] using hsI₃
      simp at hm

  obtain ⟨s₂, hs₂⟩ := K.proper K.skeleton.u₂ K.skeleton.v₂
    (K.skeleton_ne 1 4 (by decide)) hu₂v₂
  have hs₂Cases : s₂ = K.skeleton.u₁ ∨ s₂ = K.skeleton.u₃ := by
    rcases K.strict_outer_chord_cases hu₂Outer (K.skeleton_mem_outer 4) hs₂ with
      hsd | hsu₁ | hsu₂ | hsu₃ | hsI₁ | hsI₂ | hsI₃
    · have hdOn : (d : Point) ∈ openSegment ℝ
          (K.skeleton.u₂ : Point) (K.skeleton.v₂ : Point) := by
        simpa only [hsd] using hs₂
      exact (not_nested_openSegments K.hfour hb_v₂ K.hbd
        (K.skeleton_ne 1 4 (by decide)) K.skeleton.hu₂ hdOn).elim
    · exact Or.inl hsu₁
    · subst s₂
      have hm := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hs₂
      exact ((Subtype.val_injective.ne (K.skeleton_ne 1 4 (by decide))) hm).elim
    · exact Or.inr hsu₃
    · have hm : s₂ ∈ (∅ : Finset P) := by simpa only [h₁] using hsI₁
      simp at hm
    · have hm : s₂ ∈ (∅ : Finset P) := by simpa only [h₂] using hsI₂
      simp at hm
    · have hm : s₂ ∈ (∅ : Finset P) := by simpa only [h₃] using hsI₃
      simp at hm

  obtain ⟨s₃, hs₃⟩ := K.proper K.skeleton.u₃ K.skeleton.v₃
    (K.skeleton_ne 2 5 (by decide)) hu₃v₃
  have hs₃Cases : s₃ = K.skeleton.u₁ ∨ s₃ = K.skeleton.u₂ := by
    rcases K.strict_outer_chord_cases hu₃Outer (K.skeleton_mem_outer 5) hs₃ with
      hsd | hsu₁ | hsu₂ | hsu₃ | hsI₁ | hsI₂ | hsI₃
    · have hdOn : (d : Point) ∈ openSegment ℝ
          (K.skeleton.u₃ : Point) (K.skeleton.v₃ : Point) := by
        simpa only [hsd] using hs₃
      exact (not_nested_openSegments K.hfour hc_v₃ K.hcd
        (K.skeleton_ne 2 5 (by decide)) K.skeleton.hu₃ hdOn).elim
    · exact Or.inl hsu₁
    · exact Or.inr hsu₂
    · subst s₃
      have hm := (left_mem_openSegment_iff (𝕜 := ℝ)).mp hs₃
      exact ((Subtype.val_injective.ne (K.skeleton_ne 2 5 (by decide))) hm).elim
    · have hm : s₃ ∈ (∅ : Finset P) := by simpa only [h₁] using hsI₁
      simp at hm
    · have hm : s₃ ∈ (∅ : Finset P) := by simpa only [h₂] using hsI₂
      simp at hm
    · have hm : s₃ ∈ (∅ : Finset P) := by simpa only [h₃] using hsI₃
      simp at hm

  rcases hs₁Cases with hs₁u₂ | hs₁u₃ <;>
    rcases hs₂Cases with hs₂u₁ | hs₂u₃ <;>
    rcases hs₃Cases with hs₃u₁ | hs₃u₂
  · have hline := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 3 (by decide)) (K.skeleton_ne 1 4 (by decide))
      (K.skeleton_ne 0 1 (by decide)) (K.skeleton_ne 0 4 (by decide))
      (K.skeleton_ne 3 1 (by decide)) (K.skeleton_ne 3 4 (by decide))
      (by simpa only [hs₁u₂] using hs₁)
    exact (hline.1 (by simpa only [hs₂u₁] using hs₂)).elim
  · have hline := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 3 (by decide)) (K.skeleton_ne 1 4 (by decide))
      (K.skeleton_ne 0 1 (by decide)) (K.skeleton_ne 0 4 (by decide))
      (K.skeleton_ne 3 1 (by decide)) (K.skeleton_ne 3 4 (by decide))
      (by simpa only [hs₁u₂] using hs₁)
    exact (hline.1 (by simpa only [hs₂u₁] using hs₂)).elim
  · exact Or.inl ⟨by simpa only [hs₁u₂] using hs₁,
      by simpa only [hs₂u₃] using hs₂,
      by simpa only [hs₃u₁] using hs₃⟩
  · have hline := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 1 4 (by decide)) (K.skeleton_ne 2 5 (by decide))
      (K.skeleton_ne 1 2 (by decide)) (K.skeleton_ne 1 5 (by decide))
      (K.skeleton_ne 4 2 (by decide)) (K.skeleton_ne 4 5 (by decide))
      (by simpa only [hs₂u₃] using hs₂)
    exact (hline.1 (by simpa only [hs₃u₂] using hs₃)).elim
  · have hline := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 3 (by decide)) (K.skeleton_ne 2 5 (by decide))
      (K.skeleton_ne 0 2 (by decide)) (K.skeleton_ne 0 5 (by decide))
      (K.skeleton_ne 3 2 (by decide)) (K.skeleton_ne 3 5 (by decide))
      (by simpa only [hs₁u₃] using hs₁)
    exact (hline.1 (by simpa only [hs₃u₁] using hs₃)).elim
  · exact Or.inr ⟨by simpa only [hs₁u₃] using hs₁,
      by simpa only [hs₂u₁] using hs₂,
      by simpa only [hs₃u₂] using hs₃⟩
  · have hline := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 0 3 (by decide)) (K.skeleton_ne 2 5 (by decide))
      (K.skeleton_ne 0 2 (by decide)) (K.skeleton_ne 0 5 (by decide))
      (K.skeleton_ne 3 2 (by decide)) (K.skeleton_ne 3 5 (by decide))
      (by simpa only [hs₁u₃] using hs₁)
    exact (hline.1 (by simpa only [hs₃u₁] using hs₃)).elim
  · have hline := first_pair_points_do_not_block_second K.hfour
      (K.skeleton_ne 1 4 (by decide)) (K.skeleton_ne 2 5 (by decide))
      (K.skeleton_ne 1 2 (by decide)) (K.skeleton_ne 1 5 (by decide))
      (K.skeleton_ne 4 2 (by decide)) (K.skeleton_ne 4 5 (by decide))
      (by simpa only [hs₂u₃] using hs₂)
    exact (hline.1 (by simpa only [hs₃u₂] using hs₃)).elim

/-- The colour information used by both maximality orientations of the
empty-cell configuration. -/
private theorem empty_cells_colour_facts
    (h₁ : K.I₁ = ∅) (h₂ : K.I₂ = ∅) (h₃ : K.I₃ = ∅) :
    (colour K.skeleton.u₁ ≠ colour a ∧
      colour K.skeleton.u₂ ≠ colour a ∧
      colour K.skeleton.u₃ ≠ colour a) ∧
    (colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ ∧
      colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ ∧
      colour K.skeleton.u₃ ≠ colour K.skeleton.u₁) ∧
    (colour K.skeleton.u₁ = colour K.skeleton.v₁ ∧
      colour K.skeleton.u₂ = colour K.skeleton.v₂ ∧
      colour K.skeleton.u₃ = colour K.skeleton.v₃) := by
  have hp₁ := K.M₁.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₁ (by simpa [h₁]))
  have hp₂ := K.M₂.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₂ (by simpa [h₂]))
  have hp₃ := K.M₃.side_colours_pairwise_of_interior_empty
    (K.interiorPoints_empty₃ (by simpa [h₃]))
  have hu₂u₃ : colour K.skeleton.u₂ ≠ colour K.skeleton.u₃ := by
    simpa only [K.T₁_side_two, K.T₁_side_one] using
      hp₁ (i := 2) (j := 1) (by decide)
  have hu₃u₁ : colour K.skeleton.u₃ ≠ colour K.skeleton.u₁ := by
    simpa only [K.T₂_side_two, K.T₂_side_one] using
      hp₂ (i := 2) (j := 1) (by decide)
  have hu₁u₂ : colour K.skeleton.u₁ ≠ colour K.skeleton.u₂ := by
    simpa only [K.T₃_side_two, K.T₃_side_one] using
      hp₃ (i := 2) (j := 1) (by decide)
  have hu₁v₁ : colour K.skeleton.u₁ = colour K.skeleton.v₁ := by
    obtain ⟨i, hi⟩ := colour_eq_some_side K.T₁ hp₁ K.skeleton.u₁
      (K.skeleton.blocker_colour_ne 0)
    fin_cases i
    · simpa only [K.T₁_side_zero] using hi
    · exact (hu₃u₁ (by simpa only [K.T₁_side_one] using hi.symm)).elim
    · exact (hu₁u₂ (by simpa only [K.T₁_side_two] using hi)).elim
  have hu₂v₂ : colour K.skeleton.u₂ = colour K.skeleton.v₂ := by
    obtain ⟨i, hi⟩ := colour_eq_some_side K.T₂ hp₂ K.skeleton.u₂
      (K.skeleton.blocker_colour_ne 1)
    fin_cases i
    · simpa only [K.T₂_side_zero] using hi
    · exact (hu₁u₂ (by simpa only [K.T₂_side_one] using hi.symm)).elim
    · exact (hu₂u₃ (by simpa only [K.T₂_side_two] using hi)).elim
  have hu₃v₃ : colour K.skeleton.u₃ = colour K.skeleton.v₃ := by
    obtain ⟨i, hi⟩ := colour_eq_some_side K.T₃ hp₃ K.skeleton.u₃
      (K.skeleton.blocker_colour_ne 2)
    fin_cases i
    · simpa only [K.T₃_side_zero] using hi
    · exact (hu₂u₃ (by simpa only [K.T₃_side_one] using hi.symm)).elim
    · exact (hu₃u₁ (by simpa only [K.T₃_side_two] using hi)).elim
  exact ⟨⟨K.skeleton.blocker_colour_ne 0,
      K.skeleton.blocker_colour_ne 1, K.skeleton.blocker_colour_ne 2⟩,
    ⟨hu₁u₂, hu₂u₃, hu₃u₁⟩, ⟨hu₁v₁, hu₂v₂, hu₃v₃⟩⟩

/-- Under empty-cell hypotheses, these are all ambient points in the outer
triangle. -/
theorem empty_hull_point_cases
    (h₁ : K.I₁ = ∅) (h₂ : K.I₂ = ∅) (h₃ : K.I₃ = ∅)
    {x : P} (hx : (x : Point) ∈ triangleHull
      (a : Point) (b : Point) (c : Point)) :
    x = a ∨ x = b ∨ x = c ∨ x = d ∨
      x = K.skeleton.u₁ ∨ x = K.skeleton.u₂ ∨ x = K.skeleton.u₃ ∨
      x = K.skeleton.v₁ ∨ x = K.skeleton.v₂ ∨ x = K.skeleton.v₃ := by
  rcases concave_hull_point_cases K.hfour K.hab K.hac K.had K.hbc K.hbd K.hcd
      K.inside K.skeleton x hx with
      hxa | hxb | hxc | hxd | hxu₁ | hxu₂ | hxu₃ |
      hxv₁ | hxv₂ | hxv₃ | hx₁ | hx₂ | hx₃
  · exact Or.inl hxa
  · exact Or.inr (Or.inl hxb)
  · exact Or.inr (Or.inr (Or.inl hxc))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hxd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxu₁))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxu₂)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl hxu₃))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl hxv₁)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl hxv₂))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr hxv₃))))))))
  · have hm : x ∈ (∅ : Finset P) := by simpa only [h₁] using (K.mem_I₁.mpr hx₁)
    simp at hm
  · have hm : x ∈ (∅ : Finset P) := by simpa only [h₂] using (K.mem_I₂.mpr hx₂)
    simp at hm
  · have hm : x ∈ (∅ : Finset P) := by simpa only [h₃] using (K.mem_I₃.mpr hx₃)
    simp at hm

/-- Maximality of the positive directed empty-cell cycle, for an exterior
point having the colour of `u₁,v₁`. -/
private theorem impossible_minimal_exterior_positive_cycle_colour_u₁
    (h₁ : K.I₁ = ∅) (h₂ : K.I₂ = ∅) (h₃ : K.I₃ = ∅)
    (hcycle₁ : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.v₁ : Point))
    (hcycle₂ : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
      (K.skeleton.u₂ : Point) (K.skeleton.v₂ : Point))
    (hcycle₃ : (K.skeleton.u₁ : Point) ∈ openSegment ℝ
      (K.skeleton.u₃ : Point) (K.skeleton.v₃ : Point))
    {q : P}
    (hqOut : (q : Point) ∉ triangleHull (a : Point) (b : Point) (c : Point))
    (hqmin : ∀ x : P,
      (x : Point) ∉ triangleHull (a : Point) (b : Point) (c : Point) →
      Metric.infDist (q : Point) (triangleHull (a : Point) (b : Point) (c : Point)) ≤
        Metric.infDist (x : Point) (triangleHull (a : Point) (b : Point) (c : Point)))
    (hqColour : colour q = colour K.skeleton.u₁)
    (hu₁v₁ : colour K.skeleton.u₁ = colour K.skeleton.v₁) : False := by
  let Q := triangleHull (a : Point) (b : Point) (c : Point)
  have hfinite : ({(a : Point), (b : Point), (c : Point)} : Set Point).Finite := by
    simp
  have hcompact : IsCompact Q := by
    dsimp [Q, triangleHull]
    exact hfinite.isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty := by
    exact ⟨(a : Point), vertex_mem_triangleHull _ _ _⟩
  have blockerIn {y s : P}
      (hy : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
      (hs : (s : Point) ∈ openSegment ℝ (q : Point) (y : Point)) :
      (s : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    apply blocker_mem_of_minimal_exterior hcompact hconvex hne hqOut hqmin hy hs
  have hq_u₁ : q ≠ K.skeleton.u₁ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 0)
  have hq_v₁ : q ≠ K.skeleton.v₁ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 3)
  have hq_u₃ : q ≠ K.skeleton.u₃ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 2)
  have hq_v₂ : q ≠ K.skeleton.v₂ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 4)
  have hq_v₃ : q ≠ K.skeleton.v₃ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 5)
  have hq_a : q ≠ a := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ vertex_mem_triangleHull _ _ _)
  have hq_b : q ≠ b := by
    intro e
    apply hqOut
    rw [congrArg Subtype.val e]
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hq_c : q ≠ c := by
    intro e
    apply hqOut
    rw [congrArg Subtype.val e]
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hq_d : q ≠ d := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸
      strictlyInsideTriangle_mem_triangleHull K.inside)

  have hqbc : 0 ≤ turn (b : Point) (c : Point) (q : Point) := by
    by_contra hneg
    have hqneg : turn (b : Point) (c : Point) (q : Point) < 0 :=
      lt_of_not_ge hneg
    obtain ⟨s, hs⟩ := K.proper q K.skeleton.v₁ hq_v₁
      (hqColour.trans hu₁v₁)
    have hsHull := blockerIn (K.skeleton_mem_outer 3) hs
    have hsnonneg := (triangle_edge_nonneg
      (turn_pos_of_strictlyInsideTriangle K.inside).le hsHull).2.1
    have hsvzero : turn (b : Point) (c : Point)
        (K.skeleton.v₁ : Point) = 0 :=
      turn_eq_zero_of_between K.skeleton.hv₁
    have hsneg := turn_neg_of_between_nonpos hs hqneg hsvzero.le
    linarith

  obtain ⟨s, hs⟩ := K.proper q K.skeleton.u₁ hq_u₁ hqColour
  have hsHull := blockerIn (K.skeleton_mem_outer 0) hs
  have hsColour : colour s ≠ colour q :=
    blocker_colour_ne K.hfour K.proper hq_u₁ hqColour hs
  have hu₁bc : 0 < turn (b : Point) (c : Point)
      (K.skeleton.u₁ : Point) := by
    have hbca : 0 < turn (b : Point) (c : Point) (a : Point) := by
      simpa only [turn_rotate] using turn_pos_of_strictlyInsideTriangle K.inside
    exact turn_pos_of_between_nonneg K.skeleton.hu₁ hbca K.inside.2.1.le
  have hADLine := first_pair_points_do_not_block_second K.hfour K.had hq_u₁.symm
    (by
      intro e
      have hm : (a : Point) ∈ openSegment ℝ (a : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₁
      exact K.had (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_a.symm
    (by
      intro e
      have hm : (d : Point) ∈ openSegment ℝ (a : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₁
      exact K.had (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_d.symm K.skeleton.hu₁
  have hsEq : s = K.skeleton.v₂ := by
    rcases K.empty_hull_point_cases h₁ h₂ h₃ hsHull with
      hsa | hsb | hsc | hsd | hsu₁ | hsu₂ | hsu₃ | hsv₁ | hsv₂ | hsv₃
    · exact (hADLine.1 (by simpa only [hsa, openSegment_symm] using hs)).elim
    · have hbpos := turn_pos_of_between_nonneg
        (by simpa only [hsb, openSegment_symm] using hs) hu₁bc hqbc
      simp at hbpos
    · have hcpos := turn_pos_of_between_nonneg
        (by simpa only [hsc, openSegment_symm] using hs) hu₁bc hqbc
      simp at hcpos
    · exact (hADLine.2 (by simpa only [hsd, openSegment_symm] using hs)).elim
    · subst s
      have hm := (right_mem_openSegment_iff (𝕜 := ℝ)).mp hs
      exact (Subtype.val_injective.ne hq_u₁ hm).elim
    · have hu₂On : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
          (K.skeleton.u₁ : Point) (q : Point) := by
        simpa only [hsu₂, openSegment_symm] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 0 3 (by decide)) hq_u₁.symm hcycle₁ hu₂On
      exact (hq_v₁ heq.symm).elim
    · have hu₃On : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
          (q : Point) (K.skeleton.u₁ : Point) := by simpa only [hsu₃] using hs
      exact (not_nested_openSegments (p := q) (r := K.skeleton.u₃)
        (z := K.skeleton.u₁) (s := K.skeleton.v₃) K.hfour
        hq_v₃ hq_u₁ (K.skeleton_ne 2 5 (by decide)) hu₃On hcycle₃).elim
    · subst s
      exact (hsColour (hqColour.trans hu₁v₁).symm).elim
    · exact hsv₂
    · have hv₃On : (K.skeleton.v₃ : Point) ∈ openSegment ℝ
          (K.skeleton.u₁ : Point) (q : Point) := by
        simpa only [hsv₃, openSegment_symm] using hs
      exact (not_nested_openSegments (p := K.skeleton.u₃)
        (r := K.skeleton.u₁) (z := K.skeleton.v₃) (s := q) K.hfour
        hq_u₃.symm (K.skeleton_ne 2 5 (by decide)) hq_u₁.symm
        hcycle₃ hv₃On).elim
  have hv₂Between : (K.skeleton.v₂ : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (q : Point) := by
    simpa only [hsEq, openSegment_symm] using hs

  have hLpos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) := by
    simpa only [turn_rotate] using
      turn_pos_of_strictlyInsideTriangle K.red_center_strictly_inside_spoke_triangle
  have hv₂zero : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.v₂ : Point) = 0 := by
    have hz := turn_eq_zero_of_between hcycle₂
    rw [turn_swap_last] at hz
    linarith
  have hqneg := turn_neg_beyond_zero_from_pos hv₂Between hLpos hv₂zero
  have hv₁neg := K.v₁_spoke_side_neg
  have hdpos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (d : Point) := K.red_center_strictly_inside_spoke_triangle.2.1
  have hbneg : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (b : Point) < 0 := by
    have hcross := triangle_crosscut_signs K.inside.2.1
      K.skeleton.hu₂ K.skeleton.hu₃
    rw [turn_swap_first] at hcross
    linarith [hcross.1]
  have hcneg : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (c : Point) < 0 := by
    have hcross := triangle_crosscut_signs K.inside.2.1
      K.skeleton.hu₂ K.skeleton.hu₃
    have h := hcross.2.1
    rw [turn_swap_first] at h
    linarith
  have hapPos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (a : Point) := by
    by_contra hnot
    have hanonpos := le_of_not_gt hnot
    have hgen : ∀ x ∈ ({(a : Point), (b : Point), (c : Point)} : Set Point),
        turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point) x ≤ 0 := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hanonpos
      · exact hbneg.le
      · exact hcneg.le
    have hdnonpos := turn_nonpos_of_mem_convexHull hgen
      (by simpa only [triangleHull] using
        strictlyInsideTriangle_mem_triangleHull K.inside)
    linarith
  have hv₃pos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.v₃ : Point) :=
    turn_pos_of_right_of_positive_between_nonpos hcycle₃ (by simp) hLpos

  obtain ⟨t, ht⟩ := K.proper q K.skeleton.v₁ hq_v₁
    (hqColour.trans hu₁v₁)
  have htHull := blockerIn (K.skeleton_mem_outer 3) ht
  have htneg := turn_neg_of_between_nonpos ht hqneg hv₁neg.le
  have hBCLine := first_pair_points_do_not_block_second K.hfour K.hbc hq_v₁.symm
    (by
      intro e
      have hm : (b : Point) ∈ openSegment ℝ (b : Point) (c : Point) := by
        simpa only [e] using K.skeleton.hv₁
      exact K.hbc (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_b.symm
    (by
      intro e
      have hm : (c : Point) ∈ openSegment ℝ (b : Point) (c : Point) := by
        simpa only [e] using K.skeleton.hv₁
      exact K.hbc (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_c.symm K.skeleton.hv₁
  rcases K.empty_hull_point_cases h₁ h₂ h₃ htHull with
    hta | htb | htc | htd | htu₁ | htu₂ | htu₃ | htv₁ | htv₂ | htv₃
  · rw [hta] at htneg; linarith
  · exact (hBCLine.1 (by simpa only [htb, openSegment_symm] using ht)).elim
  · exact (hBCLine.2 (by simpa only [htc, openSegment_symm] using ht)).elim
  · rw [htd] at htneg; linarith
  · rw [htu₁] at htneg; linarith
  · rw [htu₂] at htneg; simp at htneg
  · rw [htu₃] at htneg; simp at htneg
  · subst t
    have hm := (right_mem_openSegment_iff (𝕜 := ℝ)).mp ht
    exact (Subtype.val_injective.ne hq_v₁ hm).elim
  · rw [htv₂, hv₂zero] at htneg
    linarith
  · rw [htv₃] at htneg
    linarith

/-- Maximality of the negative directed empty-cell cycle, for an exterior
point having the colour of `u₁,v₁`.  The separating line is again
`u₂u₃`; in this orientation `v₃` is the forced blocker of `q,u₁`. -/
private theorem impossible_minimal_exterior_negative_cycle_colour_u₁
    (h₁ : K.I₁ = ∅) (h₂ : K.I₂ = ∅) (h₃ : K.I₃ = ∅)
    (hcycle₁ : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (K.skeleton.v₁ : Point))
    (hcycle₂ : (K.skeleton.u₁ : Point) ∈ openSegment ℝ
      (K.skeleton.u₂ : Point) (K.skeleton.v₂ : Point))
    (hcycle₃ : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
      (K.skeleton.u₃ : Point) (K.skeleton.v₃ : Point))
    {q : P}
    (hqOut : (q : Point) ∉ triangleHull (a : Point) (b : Point) (c : Point))
    (hqmin : ∀ x : P,
      (x : Point) ∉ triangleHull (a : Point) (b : Point) (c : Point) →
      Metric.infDist (q : Point) (triangleHull (a : Point) (b : Point) (c : Point)) ≤
        Metric.infDist (x : Point) (triangleHull (a : Point) (b : Point) (c : Point)))
    (hqColour : colour q = colour K.skeleton.u₁)
    (hu₁v₁ : colour K.skeleton.u₁ = colour K.skeleton.v₁) : False := by
  let Q := triangleHull (a : Point) (b : Point) (c : Point)
  have hfinite : ({(a : Point), (b : Point), (c : Point)} : Set Point).Finite := by
    simp
  have hcompact : IsCompact Q := by
    dsimp [Q, triangleHull]
    exact hfinite.isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty := by
    exact ⟨(a : Point), vertex_mem_triangleHull _ _ _⟩
  have blockerIn {y s : P}
      (hy : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
      (hs : (s : Point) ∈ openSegment ℝ (q : Point) (y : Point)) :
      (s : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    apply blocker_mem_of_minimal_exterior hcompact hconvex hne hqOut hqmin hy hs
  have hq_u₁ : q ≠ K.skeleton.u₁ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 0)
  have hq_u₂ : q ≠ K.skeleton.u₂ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 1)
  have hq_u₃ : q ≠ K.skeleton.u₃ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 2)
  have hq_v₁ : q ≠ K.skeleton.v₁ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 3)
  have hq_v₂ : q ≠ K.skeleton.v₂ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 4)
  have hq_v₃ : q ≠ K.skeleton.v₃ := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ K.skeleton_mem_outer 5)
  have hq_a : q ≠ a := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ vertex_mem_triangleHull _ _ _)
  have hq_b : q ≠ b := by
    intro e
    apply hqOut
    rw [congrArg Subtype.val e]
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hq_c : q ≠ c := by
    intro e
    apply hqOut
    rw [congrArg Subtype.val e]
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hq_d : q ≠ d := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸
      strictlyInsideTriangle_mem_triangleHull K.inside)

  have hqbc : 0 ≤ turn (b : Point) (c : Point) (q : Point) := by
    by_contra hneg
    have hqneg : turn (b : Point) (c : Point) (q : Point) < 0 :=
      lt_of_not_ge hneg
    obtain ⟨s, hs⟩ := K.proper q K.skeleton.v₁ hq_v₁
      (hqColour.trans hu₁v₁)
    have hsHull := blockerIn (K.skeleton_mem_outer 3) hs
    have hsnonneg := (triangle_edge_nonneg
      (turn_pos_of_strictlyInsideTriangle K.inside).le hsHull).2.1
    have hsvzero : turn (b : Point) (c : Point)
        (K.skeleton.v₁ : Point) = 0 :=
      turn_eq_zero_of_between K.skeleton.hv₁
    have hsneg := turn_neg_of_between_nonpos hs hqneg hsvzero.le
    linarith

  obtain ⟨s, hs⟩ := K.proper q K.skeleton.u₁ hq_u₁ hqColour
  have hsHull := blockerIn (K.skeleton_mem_outer 0) hs
  have hsColour : colour s ≠ colour q :=
    blocker_colour_ne K.hfour K.proper hq_u₁ hqColour hs
  have hu₁bc : 0 < turn (b : Point) (c : Point)
      (K.skeleton.u₁ : Point) := by
    have hbca : 0 < turn (b : Point) (c : Point) (a : Point) := by
      simpa only [turn_rotate] using turn_pos_of_strictlyInsideTriangle K.inside
    exact turn_pos_of_between_nonneg K.skeleton.hu₁ hbca K.inside.2.1.le
  have hADLine := first_pair_points_do_not_block_second K.hfour K.had hq_u₁.symm
    (by
      intro e
      have hm : (a : Point) ∈ openSegment ℝ (a : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₁
      exact K.had (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_a.symm
    (by
      intro e
      have hm : (d : Point) ∈ openSegment ℝ (a : Point) (d : Point) := by
        simpa only [e] using K.skeleton.hu₁
      exact K.had (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_d.symm K.skeleton.hu₁
  have hsEq : s = K.skeleton.v₃ := by
    rcases K.empty_hull_point_cases h₁ h₂ h₃ hsHull with
      hsa | hsb | hsc | hsd | hsu₁ | hsu₂ | hsu₃ | hsv₁ | hsv₂ | hsv₃
    · exact (hADLine.1 (by simpa only [hsa, openSegment_symm] using hs)).elim
    · have hbpos := turn_pos_of_between_nonneg
        (by simpa only [hsb, openSegment_symm] using hs) hu₁bc hqbc
      simp at hbpos
    · have hcpos := turn_pos_of_between_nonneg
        (by simpa only [hsc, openSegment_symm] using hs) hu₁bc hqbc
      simp at hcpos
    · exact (hADLine.2 (by simpa only [hsd, openSegment_symm] using hs)).elim
    · subst s
      have hm := (right_mem_openSegment_iff (𝕜 := ℝ)).mp hs
      exact (Subtype.val_injective.ne hq_u₁ hm).elim
    · have hu₂On : (K.skeleton.u₂ : Point) ∈ openSegment ℝ
          (q : Point) (K.skeleton.u₁ : Point) := by simpa only [hsu₂] using hs
      exact (not_nested_openSegments (p := q) (r := K.skeleton.u₂)
        (z := K.skeleton.u₁) (s := K.skeleton.v₂) K.hfour
        hq_v₂ hq_u₁ (K.skeleton_ne 1 4 (by decide)) hu₂On hcycle₂).elim
    · have hu₃On : (K.skeleton.u₃ : Point) ∈ openSegment ℝ
          (K.skeleton.u₁ : Point) (q : Point) := by
        simpa only [hsu₃, openSegment_symm] using hs
      have heq := other_endpoint_eq_of_common_blocker K.hfour
        (K.skeleton_ne 0 3 (by decide)) hq_u₁.symm hcycle₁ hu₃On
      exact (hq_v₁ heq.symm).elim
    · subst s
      exact (hsColour (hqColour.trans hu₁v₁).symm).elim
    · have hv₂On : (K.skeleton.v₂ : Point) ∈ openSegment ℝ
          (K.skeleton.u₁ : Point) (q : Point) := by
        simpa only [hsv₂, openSegment_symm] using hs
      exact (not_nested_openSegments (p := K.skeleton.u₂)
        (r := K.skeleton.u₁) (z := K.skeleton.v₂) (s := q) K.hfour
        hq_u₂.symm (K.skeleton_ne 1 4 (by decide)) hq_u₁.symm
        hcycle₂ hv₂On).elim
    · exact hsv₃
  have hv₃Between : (K.skeleton.v₃ : Point) ∈ openSegment ℝ
      (K.skeleton.u₁ : Point) (q : Point) := by
    simpa only [hsEq, openSegment_symm] using hs

  have hLpos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.u₁ : Point) := by
    simpa only [turn_rotate] using
      turn_pos_of_strictlyInsideTriangle K.red_center_strictly_inside_spoke_triangle
  have hv₃zero : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.v₃ : Point) = 0 := by
    calc
      turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
          (K.skeleton.v₃ : Point) =
          turn (K.skeleton.u₃ : Point) (K.skeleton.v₃ : Point)
            (K.skeleton.u₂ : Point) :=
        (turn_rotate (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
          (K.skeleton.v₃ : Point)).symm
      _ = 0 := turn_eq_zero_of_between hcycle₃
  have hqneg := turn_neg_beyond_zero_from_pos hv₃Between hLpos hv₃zero
  have hv₁neg := K.v₁_spoke_side_neg
  have hdpos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (d : Point) := K.red_center_strictly_inside_spoke_triangle.2.1
  have hbneg : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (b : Point) < 0 := by
    have hcross := triangle_crosscut_signs K.inside.2.1
      K.skeleton.hu₂ K.skeleton.hu₃
    rw [turn_swap_first] at hcross
    linarith [hcross.1]
  have hcneg : turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (c : Point) < 0 := by
    have hcross := triangle_crosscut_signs K.inside.2.1
      K.skeleton.hu₂ K.skeleton.hu₃
    have h := hcross.2.1
    rw [turn_swap_first] at h
    linarith
  have hapPos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (a : Point) := by
    by_contra hnot
    have hanonpos := le_of_not_gt hnot
    have hgen : ∀ x ∈ ({(a : Point), (b : Point), (c : Point)} : Set Point),
        turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point) x ≤ 0 := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hanonpos
      · exact hbneg.le
      · exact hcneg.le
    have hdnonpos := turn_nonpos_of_mem_convexHull hgen
      (by simpa only [triangleHull] using
        strictlyInsideTriangle_mem_triangleHull K.inside)
    linarith
  have hv₂pos : 0 < turn (K.skeleton.u₂ : Point) (K.skeleton.u₃ : Point)
      (K.skeleton.v₂ : Point) :=
    turn_pos_of_right_of_positive_between_nonpos hcycle₂ (by simp) hLpos

  obtain ⟨t, ht⟩ := K.proper q K.skeleton.v₁ hq_v₁
    (hqColour.trans hu₁v₁)
  have htHull := blockerIn (K.skeleton_mem_outer 3) ht
  have htneg := turn_neg_of_between_nonpos ht hqneg hv₁neg.le
  have hBCLine := first_pair_points_do_not_block_second K.hfour K.hbc hq_v₁.symm
    (by
      intro e
      have hm : (b : Point) ∈ openSegment ℝ (b : Point) (c : Point) := by
        simpa only [e] using K.skeleton.hv₁
      exact K.hbc (Subtype.ext ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_b.symm
    (by
      intro e
      have hm : (c : Point) ∈ openSegment ℝ (b : Point) (c : Point) := by
        simpa only [e] using K.skeleton.hv₁
      exact K.hbc (Subtype.ext ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hm)))
    hq_c.symm K.skeleton.hv₁
  rcases K.empty_hull_point_cases h₁ h₂ h₃ htHull with
    hta | htb | htc | htd | htu₁ | htu₂ | htu₃ | htv₁ | htv₂ | htv₃
  · rw [hta] at htneg; linarith
  · exact (hBCLine.1 (by simpa only [htb, openSegment_symm] using ht)).elim
  · exact (hBCLine.2 (by simpa only [htc, openSegment_symm] using ht)).elim
  · rw [htd] at htneg; linarith
  · rw [htu₁] at htneg; linarith
  · rw [htu₂] at htneg; simp at htneg
  · rw [htu₃] at htneg; simp at htneg
  · subst t
    have hm := (right_mem_openSegment_iff (𝕜 := ℝ)).mp ht
    exact (Subtype.val_injective.ne hq_v₁ hm).elim
  · rw [htv₂] at htneg
    linarith
  · rw [htv₃, hv₃zero] at htneg
    linarith

/-- A nearest point outside the outer triangle cannot have the red colour.
One of the three oriented edge inequalities fails; a blocker of the
corresponding red vertex would be both strictly beyond that supporting line
and, by distance minimality, in the triangle. -/
private theorem minimal_exterior_colour_ne_red
    (K : ConcaveConfiguration P colour a b c d)
    {q : P}
    (hqOut : (q : Point) ∉ triangleHull (a : Point) (b : Point) (c : Point))
    (hqmin : ∀ x : P,
      (x : Point) ∉ triangleHull (a : Point) (b : Point) (c : Point) →
      Metric.infDist (q : Point) (triangleHull (a : Point) (b : Point) (c : Point)) ≤
        Metric.infDist (x : Point) (triangleHull (a : Point) (b : Point) (c : Point))) :
    colour q ≠ colour a := by
  let Q := triangleHull (a : Point) (b : Point) (c : Point)
  have hfinite : ({(a : Point), (b : Point), (c : Point)} : Set Point).Finite := by
    simp
  have hcompact : IsCompact Q := by
    dsimp [Q, triangleHull]
    exact hfinite.isCompact_convexHull ℝ
  have hconvex : Convex ℝ Q := convex_convexHull ℝ _
  have hne : Q.Nonempty := ⟨(a : Point), vertex_mem_triangleHull _ _ _⟩
  have blockerIn {y s : P}
      (hy : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
      (hs : (s : Point) ∈ openSegment ℝ (q : Point) (y : Point)) :
      (s : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
    exact blocker_mem_of_minimal_exterior hcompact hconvex hne hqOut hqmin hy hs
  have hqa : q ≠ a := by
    intro e
    exact hqOut (congrArg Subtype.val e ▸ vertex_mem_triangleHull _ _ _)
  have hqb : q ≠ b := by
    intro e
    apply hqOut
    rw [congrArg Subtype.val e]
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hqc : q ≠ c := by
    intro e
    apply hqOut
    rw [congrArg Subtype.val e]
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  intro hred
  have habc := turn_pos_of_strictlyInsideTriangle K.inside
  by_cases habq : 0 ≤ turn (a : Point) (b : Point) (q : Point)
  · by_cases hbcq : 0 ≤ turn (b : Point) (c : Point) (q : Point)
    · by_cases hcaq : 0 ≤ turn (c : Point) (a : Point) (q : Point)
      · exact hqOut (weaklyInsideTriangle_mem_triangleHull habc
          ⟨habq, hbcq, hcaq⟩)
      · have hqneg : turn (c : Point) (a : Point) (q : Point) < 0 :=
          lt_of_not_ge hcaq
        obtain ⟨s, hs⟩ := K.proper q c hqc (hred.trans K.monoC)
        have hsHull := blockerIn
          (subset_convexHull ℝ _ (by simp [triangleHull])) hs
        have hsnonneg := (triangle_edge_nonneg habc.le hsHull).2.2
        have hsneg := turn_neg_of_between_nonpos hs hqneg (by simp)
        linarith
    · have hqneg : turn (b : Point) (c : Point) (q : Point) < 0 :=
        lt_of_not_ge hbcq
      obtain ⟨s, hs⟩ := K.proper q b hqb (hred.trans K.monoB)
      have hsHull := blockerIn
        (subset_convexHull ℝ _ (by simp [triangleHull])) hs
      have hsnonneg := (triangle_edge_nonneg habc.le hsHull).2.1
      have hsneg := turn_neg_of_between_nonpos hs hqneg (by simp)
      linarith
  · have hqneg : turn (a : Point) (b : Point) (q : Point) < 0 :=
      lt_of_not_ge habq
    obtain ⟨s, hs⟩ := K.proper q a hqa hred
    have hsHull := blockerIn (vertex_mem_triangleHull _ _ _) hs
    have hsnonneg := (triangle_edge_nonneg habc.le hsHull).1
    have hsneg := turn_neg_of_between_nonpos hs hqneg (by simp)
    linarith

/-- If the three cells are empty, the ten-point concave pattern is maximal:
every ambient point already lies in the outer triangle. -/
theorem empty_cells_all_points_mem_hull
    (h₁ : K.I₁ = ∅) (h₂ : K.I₂ = ∅) (h₃ : K.I₃ = ∅)
    (x : P) :
    (x : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point) := by
  by_contra hxOut
  obtain ⟨q, hqOut, hqmin⟩ := exists_minimal_exterior_point
    (B := P) (Q := triangleHull (a : Point) (b : Point) (c : Point))
    ⟨x, hxOut⟩
  have hqRed := K.minimal_exterior_colour_ne_red hqOut hqmin
  rcases K.empty_cells_colour_facts h₁ h₂ h₃ with
    ⟨⟨hu₁Red, hu₂Red, hu₃Red⟩, ⟨hu₁u₂, hu₂u₃, hu₃u₁⟩,
      ⟨hu₁v₁, hu₂v₂, hu₃v₃⟩⟩
  have hqCases : colour q = colour K.skeleton.u₁ ∨
      colour q = colour K.skeleton.u₂ ∨
      colour q = colour K.skeleton.u₃ :=
    fin4_eq_one_of_three_of_avoid hqRed hu₁Red hu₂Red hu₃Red
      hu₁u₂ hu₂u₃ hu₃u₁
  have hQ₂ : triangleHull (c : Point) (a : Point) (b : Point) =
      triangleHull (a : Point) (b : Point) (c : Point) :=
    (triangleHull_rotate (b : Point) (c : Point) (a : Point)).trans
      (triangleHull_rotate (a : Point) (b : Point) (c : Point))
  rcases K.empty_cells_incidence_cycles h₁ h₂ h₃ with hpos | hneg
  · rcases hqCases with hqu₁ | hqu₂ | hqu₃
    · exact K.impossible_minimal_exterior_positive_cycle_colour_u₁
        h₁ h₂ h₃ hpos.1 hpos.2.1 hpos.2.2 hqOut hqmin hqu₁ hu₁v₁
    · apply K.rotate.impossible_minimal_exterior_positive_cycle_colour_u₁
        (by simpa only [K.rotate_I₁] using h₂)
        (by simpa only [K.rotate_I₂] using h₃)
        (by simpa only [K.rotate_I₃] using h₁)
        hpos.2.1 hpos.2.2 hpos.1
        (by simpa only [triangleHull_rotate] using hqOut)
        (by
          intro y hy
          have hy' : (y : Point) ∉
              triangleHull (a : Point) (b : Point) (c : Point) := by
            simpa only [triangleHull_rotate] using hy
          simpa only [triangleHull_rotate] using hqmin y hy')
        hqu₂ hu₂v₂
    · apply K.rotate.rotate.impossible_minimal_exterior_positive_cycle_colour_u₁
        (by simpa only [ConcaveConfiguration.rotate_I₁,
          ConcaveConfiguration.rotate_I₂] using h₃)
        (by simpa only [ConcaveConfiguration.rotate_I₂,
          ConcaveConfiguration.rotate_I₃] using h₁)
        (by simpa only [ConcaveConfiguration.rotate_I₃,
          ConcaveConfiguration.rotate_I₁] using h₂)
        hpos.2.2 hpos.1 hpos.2.1
        (by simpa only [hQ₂] using hqOut)
        (by
          intro y hy
          have hy' : (y : Point) ∉
              triangleHull (a : Point) (b : Point) (c : Point) := by
            simpa only [hQ₂] using hy
          simpa only [hQ₂] using hqmin y hy')
        hqu₃ hu₃v₃
  · rcases hqCases with hqu₁ | hqu₂ | hqu₃
    · exact K.impossible_minimal_exterior_negative_cycle_colour_u₁
        h₁ h₂ h₃ hneg.1 hneg.2.1 hneg.2.2 hqOut hqmin hqu₁ hu₁v₁
    · apply K.rotate.impossible_minimal_exterior_negative_cycle_colour_u₁
        (by simpa only [K.rotate_I₁] using h₂)
        (by simpa only [K.rotate_I₂] using h₃)
        (by simpa only [K.rotate_I₃] using h₁)
        hneg.2.1 hneg.2.2 hneg.1
        (by simpa only [triangleHull_rotate] using hqOut)
        (by
          intro y hy
          have hy' : (y : Point) ∉
              triangleHull (a : Point) (b : Point) (c : Point) := by
            simpa only [triangleHull_rotate] using hy
          simpa only [triangleHull_rotate] using hqmin y hy')
        hqu₂ hu₂v₂
    · apply K.rotate.rotate.impossible_minimal_exterior_negative_cycle_colour_u₁
        (by simpa only [ConcaveConfiguration.rotate_I₁,
          ConcaveConfiguration.rotate_I₂] using h₃)
        (by simpa only [ConcaveConfiguration.rotate_I₂,
          ConcaveConfiguration.rotate_I₃] using h₁)
        (by simpa only [ConcaveConfiguration.rotate_I₃,
          ConcaveConfiguration.rotate_I₁] using h₂)
        hneg.2.2 hneg.1 hneg.2.1
        (by simpa only [hQ₂] using hqOut)
        (by
          intro y hy
          have hy' : (y : Point) ∉
              triangleHull (a : Point) (b : Point) (c : Point) := by
            simpa only [hQ₂] using hy
          simpa only [hQ₂] using hqmin y hy')
        hqu₃ hu₃v₃

end ConcaveConfiguration

end Lax56Proofs.HKBDirectConcaveCases
