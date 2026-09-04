import Lax56Proofs.HKBDirectCells
import Lax56Proofs.HKBSixStructure
import Mathlib.Tactic

/-!
Local three-colour models and beam patterns in one triangular cell of the
concave four-point configuration.
-/

namespace Lax56Proofs.HKBDirectTrianglePatterns

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBConvexity
open Lax56Proofs.HKBDirectCells
open Lax56Proofs.HKBDirectConcave
open Lax56Proofs.HKBDirectCore
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBQuadrilateralMaximal
open Lax56Proofs.HKBSixStructure
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

/-- A positively oriented red triangle together with its three side
blockers, listed cyclically. -/
structure CellSkeleton
    (P : Finset Point) (colour : P → Fin 4) (red : Fin 4)
    (A B C : P) where
  s₀ : P
  s₁ : P
  s₂ : P
  hAB : A ≠ B
  hBC : B ≠ C
  hCA : C ≠ A
  hpos : 0 < turn (A : Point) (B : Point) (C : Point)
  hs₀ : (s₀ : Point) ∈ openSegment ℝ (A : Point) (B : Point)
  hs₁ : (s₁ : Point) ∈ openSegment ℝ (B : Point) (C : Point)
  hs₂ : (s₂ : Point) ∈ openSegment ℝ (C : Point) (A : Point)
  colourA : colour A = red
  colourB : colour B = red
  colourC : colour C = red
  colour_s₀ : colour s₀ ≠ red
  colour_s₁ : colour s₁ ≠ red
  colour_s₂ : colour s₂ ≠ red

private theorem three_points_pairwise
    {X : Type*} {a b c : X}
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    Function.Injective (![a, b, c] : Fin 3 → X) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem CellSkeleton.side_pairwise
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.s₀ ≠ T.s₁ ∧ T.s₁ ≠ T.s₂ ∧ T.s₂ ≠ T.s₀ := by
  have h := triangle_side_points_pairwise T.hpos T.hs₀ T.hs₁ T.hs₂
  exact ⟨fun e ↦ h.1 (congrArg Subtype.val e),
    fun e ↦ h.2.1 (congrArg Subtype.val e),
    fun e ↦ h.2.2 (congrArg Subtype.val e)⟩

theorem CellSkeleton.side_injective
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    Function.Injective (![T.s₀, T.s₁, T.s₂] : Fin 3 → P) := by
  obtain ⟨h₀₁, h₁₂, h₂₀⟩ := T.side_pairwise
  exact three_points_pairwise h₀₁ h₁₂ h₂₀

def CellSkeleton.side
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : Fin 3 → P :=
  ![T.s₀, T.s₁, T.s₂]

theorem CellSkeleton.side_injective'
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    Function.Injective T.side := T.side_injective

@[simp] theorem CellSkeleton.side_zero
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : T.side 0 = T.s₀ := rfl

@[simp] theorem CellSkeleton.side_one
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : T.side 1 = T.s₁ := rfl

@[simp] theorem CellSkeleton.side_two
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : T.side 2 = T.s₂ := rfl

def ConcaveSkeleton.cellOne
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (S : ConcaveSkeleton P colour a b c d)
    (hbc : b ≠ c) (hcd : c ≠ d) (hbd : b ≠ d)
    (hmonoB : colour a = colour b)
    (hmonoC : colour a = colour c)
    (hmonoD : colour a = colour d)
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point)) :
    CellSkeleton P colour (colour a) b c d where
  s₀ := S.v₁
  s₁ := S.u₃
  s₂ := S.u₂
  hAB := hbc
  hBC := hcd
  hCA := hbd.symm
  hpos := hd.2.1
  hs₀ := S.hv₁
  hs₁ := S.hu₃
  hs₂ := by simpa only [openSegment_symm] using S.hu₂
  colourA := hmonoB.symm
  colourB := hmonoC.symm
  colourC := hmonoD.symm
  colour_s₀ := by simpa using S.blocker_colour_ne 3
  colour_s₁ := by simpa using S.blocker_colour_ne 2
  colour_s₂ := by simpa using S.blocker_colour_ne 1

def ConcaveSkeleton.cellTwo
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (S : ConcaveSkeleton P colour a b c d)
    (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (hmonoC : colour a = colour c)
    (hmonoD : colour a = colour d)
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point)) :
    CellSkeleton P colour (colour a) c a d where
  s₀ := S.v₂
  s₁ := S.u₁
  s₂ := S.u₃
  hAB := hac.symm
  hBC := had
  hCA := hcd.symm
  hpos := hd.2.2
  hs₀ := by simpa only [openSegment_symm] using S.hv₂
  hs₁ := S.hu₁
  hs₂ := by simpa only [openSegment_symm] using S.hu₃
  colourA := hmonoC.symm
  colourB := rfl
  colourC := hmonoD.symm
  colour_s₀ := by simpa using S.blocker_colour_ne 4
  colour_s₁ := by simpa using S.blocker_colour_ne 0
  colour_s₂ := by simpa using S.blocker_colour_ne 2

def ConcaveSkeleton.cellThree
    {P : Finset Point} {colour : P → Fin 4} {a b c d : P}
    (S : ConcaveSkeleton P colour a b c d)
    (hab : a ≠ b) (hbd : b ≠ d) (had : a ≠ d)
    (hmonoB : colour a = colour b)
    (hmonoD : colour a = colour d)
    (hd : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point)) :
    CellSkeleton P colour (colour a) a b d where
  s₀ := S.v₃
  s₁ := S.u₂
  s₂ := S.u₁
  hAB := hab
  hBC := hbd
  hCA := had.symm
  hpos := hd.1
  hs₀ := S.hv₃
  hs₁ := S.hu₂
  hs₂ := by simpa only [openSegment_symm] using S.hu₁
  colourA := rfl
  colourB := hmonoB.symm
  colourC := hmonoD.symm
  colour_s₀ := by simpa using S.blocker_colour_ne 5
  colour_s₁ := by simpa using S.blocker_colour_ne 1
  colour_s₂ := by simpa using S.blocker_colour_ne 0

/-- The known side blocker is the only nonvertex point of `P` on each side
line; hence every point of the cell is a vertex, a side blocker, or strict
interior. -/
theorem CellSkeleton.hull_point_cases
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C)
    (p : P) (hp : (p : Point) ∈ triangleHull (A : Point) (B : Point) (C : Point)) :
    p = A ∨ p = B ∨ p = C ∨ p = T.s₀ ∨ p = T.s₁ ∨ p = T.s₂ ∨
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) := by
  have hedge := triangle_edge_nonneg T.hpos.le hp
  by_cases h₀ : turn (A : Point) (B : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour T.hAB T.hs₀ h₀ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  by_cases h₁ : turn (B : Point) (C : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour T.hBC T.hs₁ h₁ with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  by_cases h₂ : turn (C : Point) (A : Point) (p : Point) = 0
  · rcases point_eq_of_on_full_line hfour T.hCA T.hs₂ h₂ with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨lt_of_le_of_ne hedge.1 (Ne.symm h₀),
      lt_of_le_of_ne hedge.2.1 (Ne.symm h₁),
      lt_of_le_of_ne hedge.2.2 (Ne.symm h₂)⟩)))))

/-- A chord between side blockers on two different sides is strict interior
to the cell. -/
theorem CellSkeleton.strict_of_between_distinct_sides
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    {i j : Fin 3} (hij : i ≠ j) {p : Point}
    (hp : p ∈ openSegment ℝ (T.side i : Point) (T.side j : Point)) :
    StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) p := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact strictlyInside_between_adjacent_sides T.hpos T.hs₀ T.hs₁ hp
  · have hrot : 0 < turn (C : Point) (A : Point) (B : Point) := by
      simpa only [turn_rotate, turn_rotate] using T.hpos
    have hs := strictlyInside_between_adjacent_sides hrot T.hs₂ T.hs₀
      (by simpa [CellSkeleton.side, openSegment_symm] using hp)
    exact ⟨by simpa only [turn_rotate] using hs.2.1,
      by simpa only [turn_rotate] using hs.2.2,
      by simpa only [turn_rotate] using hs.1⟩
  · exact strictlyInside_between_adjacent_sides T.hpos T.hs₀ T.hs₁
      (by simpa [CellSkeleton.side, openSegment_symm] using hp)
  · exact (hij rfl).elim
  · have hrot : 0 < turn (B : Point) (C : Point) (A : Point) := by
      simpa only [turn_rotate] using T.hpos
    have hs := strictlyInside_between_adjacent_sides hrot T.hs₁ T.hs₂ hp
    exact ⟨by simpa only [turn_rotate, turn_rotate] using hs.2.2,
      by simpa only [turn_rotate, turn_rotate] using hs.1,
      by simpa only [turn_rotate] using hs.2.1⟩
  · have hrot : 0 < turn (C : Point) (A : Point) (B : Point) := by
      simpa only [turn_rotate, turn_rotate] using T.hpos
    have hs := strictlyInside_between_adjacent_sides hrot T.hs₂ T.hs₀ hp
    exact ⟨by simpa only [turn_rotate] using hs.2.1,
      by simpa only [turn_rotate] using hs.2.2,
      by simpa only [turn_rotate] using hs.1⟩
  · have hrot : 0 < turn (B : Point) (C : Point) (A : Point) := by
      simpa only [turn_rotate] using T.hpos
    have hs := strictlyInside_between_adjacent_sides hrot T.hs₁ T.hs₂
      (by simpa [CellSkeleton.side, openSegment_symm] using hp)
    exact ⟨by simpa only [turn_rotate, turn_rotate] using hs.2.2,
      by simpa only [turn_rotate, turn_rotate] using hs.1,
      by simpa only [turn_rotate] using hs.2.1⟩
  · exact (hij rfl).elim

/-- A chord from a side blocker to a strict-interior point remains strict
interior to the cell. -/
theorem CellSkeleton.strict_of_between_side_and_inside
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (i : Fin 3) {u p : Point}
    (hu : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) u)
    (hp : p ∈ openSegment ℝ (T.side i : Point) u) :
    StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) p := by
  fin_cases i
  · have hrot : 0 < turn (B : Point) (C : Point) (A : Point) := by
      simpa only [turn_rotate] using T.hpos
    have huRot : StrictlyInsideTriangle (B : Point) (C : Point) (A : Point) u :=
      ⟨by simpa only [turn_rotate] using hu.2.1,
        by simpa only [turn_rotate] using hu.2.2,
        by simpa only [turn_rotate, turn_rotate] using hu.1⟩
    have hs := strictlyInside_between_third_side_and_inside hrot T.hs₀ huRot hp
    exact ⟨by simpa only [turn_rotate] using hs.2.2,
      by simpa only [turn_rotate, turn_rotate] using hs.1,
      by simpa only [turn_rotate] using hs.2.1⟩
  · have hrot : 0 < turn (C : Point) (A : Point) (B : Point) := by
      simpa only [turn_rotate, turn_rotate] using T.hpos
    have huRot : StrictlyInsideTriangle (C : Point) (A : Point) (B : Point) u :=
      ⟨by simpa only [turn_rotate] using hu.2.2,
        by simpa only [turn_rotate] using hu.1,
        by simpa only [turn_rotate] using hu.2.1⟩
    have hs := strictlyInside_between_third_side_and_inside hrot T.hs₁ huRot hp
    exact ⟨by simpa only [turn_rotate, turn_rotate] using hs.2.1,
      by simpa only [turn_rotate] using hs.2.2,
      by simpa only [turn_rotate] using hs.1⟩
  · exact strictlyInside_between_third_side_and_inside T.hpos T.hs₂ hu hp

/-- A strict convex combination of two strict-interior points is again
strict interior. -/
theorem strictlyInside_between_inside_points
    {a b c x y p : Point}
    (hx : StrictlyInsideTriangle a b c x)
    (hy : StrictlyInsideTriangle a b c y)
    (hp : p ∈ openSegment ℝ x y) :
    StrictlyInsideTriangle a b c p := by
  exact ⟨
    edgeTurn_pos_of_mem_openSegment hp hx.1.le hy.1.le (Or.inl hx.1),
    edgeTurn_pos_of_mem_openSegment hp hx.2.1.le hy.2.1.le (Or.inl hx.2.1),
    edgeTurn_pos_of_mem_openSegment hp hx.2.2.le hy.2.2.le (Or.inl hx.2.2)⟩

noncomputable def CellSkeleton.sidePoints
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : Finset Point :=
  (Finset.univ : Finset (Fin 3)).image
    (fun i ↦ ((![T.s₀, T.s₁, T.s₂] : Fin 3 → P) i : Point))

@[simp] theorem CellSkeleton.mem_sidePoints
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} {T : CellSkeleton P colour red A B C} {p : Point} :
    p ∈ T.sidePoints ↔
      p = (T.s₀ : Point) ∨ p = (T.s₁ : Point) ∨ p = (T.s₂ : Point) := by
  classical
  constructor
  · intro hp
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr hi.symm)
  · intro hp
    rcases hp with rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩

theorem CellSkeleton.sidePoints_card
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.sidePoints.card = 3 := by
  classical
  rw [CellSkeleton.sidePoints, Finset.card_image_of_injective]
  · simp
  · exact Subtype.val_injective.comp T.side_injective

noncomputable def CellSkeleton.nonredPoints
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : Finset Point :=
  T.sidePoints ∪ cellInteriorPoints P (A : Point) (B : Point) (C : Point)

@[simp] theorem CellSkeleton.mem_nonredPoints
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} {T : CellSkeleton P colour red A B C} {p : Point} :
    p ∈ T.nonredPoints ↔
      p = (T.s₀ : Point) ∨ p = (T.s₁ : Point) ∨ p = (T.s₂ : Point) ∨
        (p ∈ P ∧ StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) p) := by
  classical
  rw [CellSkeleton.nonredPoints, Finset.mem_union, T.mem_sidePoints,
    mem_cellInteriorPoints]
  tauto

theorem CellSkeleton.sidePoints_disjoint_interior
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    Disjoint T.sidePoints
      (cellInteriorPoints P (A : Point) (B : Point) (C : Point)) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpSide hpInt
  have hi := mem_cellInteriorPoints.mp hpInt
  rcases T.mem_sidePoints.mp hpSide with rfl | rfl | rfl
  · have hz := turn_eq_zero_of_between T.hs₀
    linarith [hi.2.1]
  · have hz := turn_eq_zero_of_between T.hs₁
    linarith [hi.2.2.1]
  · have hz := turn_eq_zero_of_between T.hs₂
    linarith [hi.2.2.2]

theorem CellSkeleton.nonredPoints_card
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.nonredPoints.card =
      3 + (cellInteriorPoints P (A : Point) (B : Point) (C : Point)).card := by
  classical
  rw [CellSkeleton.nonredPoints,
    Finset.card_union_of_disjoint T.sidePoints_disjoint_interior,
    T.sidePoints_card]

/-- Every member of the local nonred set lies in the cell hull. -/
theorem CellSkeleton.nonredPoint_mem_hull
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    {p : Point} (hp : p ∈ T.nonredPoints) :
    p ∈ triangleHull (A : Point) (B : Point) (C : Point) := by
  rcases T.mem_nonredPoints.mp hp with rfl | rfl | rfl | hp
  · exact openSegment_subset_triangleHull_left T.hs₀
  · have h := openSegment_subset_triangleHull_left (c := (A : Point)) T.hs₁
    simpa only [triangleHull_rotate] using h
  · have h := openSegment_subset_triangleHull_left (c := (B : Point)) T.hs₂
    rw [triangleHull_rotate (B : Point) (C : Point) (A : Point),
      triangleHull_rotate (A : Point) (B : Point) (C : Point)] at h
    exact h
  · exact strictlyInsideTriangle_mem_triangleHull hp.2

/-- Every local nonred point is an ambient point of `P`. -/
theorem CellSkeleton.nonredPoint_mem_ambient
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    {p : Point} (hp : p ∈ T.nonredPoints) : p ∈ P := by
  rcases T.mem_nonredPoints.mp hp with rfl | rfl | rfl | hp
  · exact T.s₀.property
  · exact T.s₁.property
  · exact T.s₂.property
  · exact hp.1

/-- The canonical lift of a local point back to the ambient subtype `P`. -/
def CellSkeleton.toAmbient
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (p : T.nonredPoints) : P :=
  ⟨(p : Point), T.nonredPoint_mem_ambient p.property⟩

@[simp] theorem CellSkeleton.coe_toAmbient
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (p : T.nonredPoints) : (T.toAmbient p : Point) = (p : Point) := rfl

def CellSkeleton.sideLocal₀
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : T.nonredPoints :=
  ⟨(T.s₀ : Point), T.mem_nonredPoints.mpr (Or.inl rfl)⟩

def CellSkeleton.sideLocal₁
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : T.nonredPoints :=
  ⟨(T.s₁ : Point), T.mem_nonredPoints.mpr (Or.inr (Or.inl rfl))⟩

def CellSkeleton.sideLocal₂
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) : T.nonredPoints :=
  ⟨(T.s₂ : Point), T.mem_nonredPoints.mpr
    (Or.inr (Or.inr (Or.inl rfl)))⟩

def CellSkeleton.sideLocal
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (i : Fin 3) : T.nonredPoints :=
  (![T.sideLocal₀, T.sideLocal₁, T.sideLocal₂] : Fin 3 → T.nonredPoints) i

def CellSkeleton.interiorLocal
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (p : P)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point)) : T.nonredPoints :=
  ⟨(p : Point), T.mem_nonredPoints.mpr
    (Or.inr (Or.inr (Or.inr ⟨p.property, hp⟩)))⟩

@[simp] theorem CellSkeleton.toAmbient_sideLocal₀
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.toAmbient T.sideLocal₀ = T.s₀ := rfl

@[simp] theorem CellSkeleton.toAmbient_sideLocal₁
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.toAmbient T.sideLocal₁ = T.s₁ := rfl

@[simp] theorem CellSkeleton.toAmbient_sideLocal₂
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.toAmbient T.sideLocal₂ = T.s₂ := rfl

@[simp] theorem CellSkeleton.toAmbient_sideLocal
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (i : Fin 3) : T.toAmbient (T.sideLocal i) = T.side i := by
  fin_cases i <;> simp [CellSkeleton.sideLocal, CellSkeleton.side]

@[simp] theorem CellSkeleton.coe_sideLocal
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (i : Fin 3) : (T.sideLocal i : Point) = (T.side i : Point) := by
  change (T.toAmbient (T.sideLocal i) : Point) = (T.side i : Point)
  rw [T.toAmbient_sideLocal]

@[simp] theorem CellSkeleton.toAmbient_interiorLocal
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (p : P)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point)) :
    T.toAmbient (T.interiorLocal p hp) = p := rfl

theorem CellSkeleton.sideLocals_pairwise
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C) :
    T.sideLocal₀ ≠ T.sideLocal₁ ∧ T.sideLocal₁ ≠ T.sideLocal₂ ∧
      T.sideLocal₂ ≠ T.sideLocal₀ := by
  obtain ⟨h₀₁, h₁₂, h₂₀⟩ := T.side_pairwise
  exact ⟨fun h ↦ h₀₁ (congrArg T.toAmbient h),
    fun h ↦ h₁₂ (congrArg T.toAmbient h),
    fun h ↦ h₂₀ (congrArg T.toAmbient h)⟩

/-- All points in the local nonred set avoid `red`, provided strict cell
points do. -/
theorem CellSkeleton.nonredPoint_colour_ne
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4}
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (p : T.nonredPoints) : colour (T.toAmbient p) ≠ red := by
  rcases T.mem_nonredPoints.mp p.property with h | h | h | h
  · have e : T.toAmbient p = T.s₀ := Subtype.ext h
    simpa [e] using T.colour_s₀
  · have e : T.toAmbient p = T.s₁ := Subtype.ext h
    simpa [e] using T.colour_s₁
  · have e : T.toAmbient p = T.s₂ := Subtype.ext h
    simpa [e] using T.colour_s₂
  · exact hinterior (T.toAmbient p) (by simpa using h.2)

/-- A triangle vertex cannot lie strictly between two other points of its
hull when those points are not that vertex. -/
theorem first_triangle_vertex_not_between
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {A B C x y : P}
    (hpos : 0 < turn (A : Point) (B : Point) (C : Point))
    (hx : (x : Point) ∈ triangleHull (A : Point) (B : Point) (C : Point))
    (hy : (y : Point) ∈ triangleHull (A : Point) (B : Point) (C : Point))
    (hxA : x ≠ A) (hyA : y ≠ A) :
    (A : Point) ∉ openSegment ℝ (x : Point) (y : Point) := by
  intro hA
  have hxpos := triangle_vertex_exposing_sum_pos hfour A B C x hpos hx hxA
  have hypos := triangle_vertex_exposing_sum_pos hfour A B C y hpos hy hyA
  rw [openSegment_eq_image] at hA
  obtain ⟨t, ht, hAeq⟩ := hA
  have hAeq' : (1 - t) • (x : Point) + t • (y : Point) = (A : Point) := by
    simpa only using hAeq
  -- Add the two affine identities.  Their left sides vanish at `A`.
  have hAB0 :
      (1 - t) * turn (A : Point) (B : Point) (x : Point) +
        t * turn (A : Point) (B : Point) (y : Point) = 0 := by
    rw [← turn_convex_combo (A : Point) (B : Point) (x : Point) (y : Point)
      (1 - t) t (by ring), hAeq']
    simp
  have hCA0 :
      (1 - t) * turn (C : Point) (A : Point) (x : Point) +
        t * turn (C : Point) (A : Point) (y : Point) = 0 := by
    rw [← turn_convex_combo (C : Point) (A : Point) (x : Point) (y : Point)
      (1 - t) t (by ring), hAeq']
    simp
  have hxEdges := triangle_edge_nonneg hpos.le hx
  have hyEdges := triangle_edge_nonneg hpos.le hy
  have hxAB : 0 ≤ turn (A : Point) (B : Point) (x : Point) := hxEdges.1
  have hxCA : 0 ≤ turn (C : Point) (A : Point) (x : Point) := hxEdges.2.2
  have hyAB : 0 ≤ turn (A : Point) (B : Point) (y : Point) := hyEdges.1
  have hyCA : 0 ≤ turn (C : Point) (A : Point) (y : Point) := hyEdges.2.2
  have hxAB0 : turn (A : Point) (B : Point) (x : Point) = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) hxAB, mul_nonneg ht.1.le hyAB]
  have hxCA0 : turn (C : Point) (A : Point) (x : Point) = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) hxCA, mul_nonneg ht.1.le hyCA]
  linarith

/-- No red vertex can block a pair of local nonred points. -/
theorem CellSkeleton.vertex_not_between_nonred
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (x y : T.nonredPoints) :
    (A : Point) ∉ openSegment ℝ (x : Point) (y : Point) ∧
      (B : Point) ∉ openSegment ℝ (x : Point) (y : Point) ∧
      (C : Point) ∉ openSegment ℝ (x : Point) (y : Point) := by
  let xP := T.toAmbient x
  let yP := T.toAmbient y
  have hxHull := T.nonredPoint_mem_hull x.property
  have hyHull := T.nonredPoint_mem_hull y.property
  have hxRed := T.nonredPoint_colour_ne hinterior x
  have hyRed := T.nonredPoint_colour_ne hinterior y
  have hxA : xP ≠ A := fun e ↦ hxRed ((congrArg colour e).trans T.colourA)
  have hyA : yP ≠ A := fun e ↦ hyRed ((congrArg colour e).trans T.colourA)
  have hxB : xP ≠ B := fun e ↦ hxRed ((congrArg colour e).trans T.colourB)
  have hyB : yP ≠ B := fun e ↦ hyRed ((congrArg colour e).trans T.colourB)
  have hxC : xP ≠ C := fun e ↦ hxRed ((congrArg colour e).trans T.colourC)
  have hyC : yP ≠ C := fun e ↦ hyRed ((congrArg colour e).trans T.colourC)
  refine ⟨first_triangle_vertex_not_between hfour T.hpos hxHull hyHull hxA hyA,
    ?_, ?_⟩
  · have hpos' : 0 < turn (B : Point) (C : Point) (A : Point) := by
      simpa only [turn_rotate] using T.hpos
    have hx' : (x : Point) ∈ triangleHull (B : Point) (C : Point) (A : Point) := by
      simpa only [triangleHull_rotate] using hxHull
    have hy' : (y : Point) ∈ triangleHull (B : Point) (C : Point) (A : Point) := by
      simpa only [triangleHull_rotate] using hyHull
    exact first_triangle_vertex_not_between hfour hpos' hx' hy' hxB hyB
  · have hpos' : 0 < turn (C : Point) (A : Point) (B : Point) := by
      simpa only [turn_rotate, turn_rotate] using T.hpos
    have hx' : (x : Point) ∈ triangleHull (C : Point) (A : Point) (B : Point) := by
      rw [triangleHull_rotate (B : Point) (C : Point) (A : Point),
        triangleHull_rotate (A : Point) (B : Point) (C : Point)]
      exact hxHull
    have hy' : (y : Point) ∈ triangleHull (C : Point) (A : Point) (B : Point) := by
      rw [triangleHull_rotate (B : Point) (C : Point) (A : Point),
        triangleHull_rotate (A : Point) (B : Point) (C : Point)]
      exact hyHull
    exact first_triangle_vertex_not_between hfour hpos' hx' hy' hxC hyC

/-- A reduced three-colour model of the local nonred set. -/
structure CellModel
    {P : Finset Point} (colour : P → Fin 4) (red : Fin 4)
    {A B C : P} (T : CellSkeleton P colour red A B C) where
  colour3 : T.nonredPoints → Fin 3
  proper : ProperBlocking T.nonredPoints colour3
  colour_eq_iff : ∀ x y : T.nonredPoints,
    colour3 x = colour3 y ↔
      colour (T.toAmbient x) = colour (T.toAmbient y)

/-- The side blockers and strict-interior points form a closed properly
three-coloured blocking set. -/
theorem CellSkeleton.exists_model
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C)
    (hproper : ProperBlocking P colour)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red) :
    Nonempty (CellModel colour red T) := by
  classical
  let Q := T.nonredPoints
  have havoid (p : Q) : colour (T.toAmbient p) ≠ red :=
    T.nonredPoint_colour_ne hinterior p
  let colour3 : Q → Fin 3 := fun p ↦
    (finSuccAboveEquiv red).symm ⟨colour (T.toAmbient p), havoid p⟩
  have heq (x y : Q) :
      colour3 x = colour3 y ↔
        colour (T.toAmbient x) = colour (T.toAmbient y) := by
    constructor
    · intro h
      have h' := congrArg (finSuccAboveEquiv red) h
      have h'' :
          (⟨colour (T.toAmbient x), havoid x⟩ : {i : Fin 4 // i ≠ red}) =
            ⟨colour (T.toAmbient y), havoid y⟩ := by
        simpa only [colour3, Equiv.apply_symm_apply] using h'
      exact congrArg Subtype.val h''
    · intro h
      change
        (finSuccAboveEquiv red).symm ⟨colour (T.toAmbient x), havoid x⟩ =
          (finSuccAboveEquiv red).symm ⟨colour (T.toAmbient y), havoid y⟩
      exact congrArg (finSuccAboveEquiv red).symm (Subtype.ext h)
  have hproperQ : ProperBlocking Q colour3 := by
    intro x y hxy hcol
    have hxyP : T.toAmbient x ≠ T.toAmbient y := by
      intro h
      apply hxy
      apply Subtype.ext
      exact congrArg (fun z : P ↦ (z : Point)) h
    obtain ⟨z, hz⟩ := hproper (T.toAmbient x) (T.toAmbient y) hxyP
      ((heq x y).mp hcol)
    have hxHull := T.nonredPoint_mem_hull x.property
    have hyHull := T.nonredPoint_mem_hull y.property
    have hzHull := openSegment_mem_triangleHull_of_mem hxHull hyHull hz
    have hvertices := T.vertex_not_between_nonred hfour hinterior x y
    have hzA : z ≠ A := fun e ↦ hvertices.1 (e ▸ hz)
    have hzB : z ≠ B := fun e ↦ hvertices.2.1 (e ▸ hz)
    have hzC : z ≠ C := fun e ↦ hvertices.2.2 (e ▸ hz)
    have hzQ : (z : Point) ∈ Q := by
      rcases T.hull_point_cases hfour z hzHull with
          h | h | h | h | h | h | h
      · exact (hzA h).elim
      · exact (hzB h).elim
      · exact (hzC h).elim
      · exact T.mem_nonredPoints.mpr (Or.inl (congrArg Subtype.val h))
      · exact T.mem_nonredPoints.mpr
          (Or.inr (Or.inl (congrArg Subtype.val h)))
      · exact T.mem_nonredPoints.mpr
          (Or.inr (Or.inr (Or.inl (congrArg Subtype.val h))))
      · exact T.mem_nonredPoints.mpr
          (Or.inr (Or.inr (Or.inr ⟨z.property, h⟩)))
    exact ⟨⟨(z : Point), hzQ⟩, hz⟩
  exact ⟨⟨colour3, hproperQ, heq⟩⟩

theorem CellSkeleton.noFour_nonred
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C) :
    ¬HasFourCollinear T.nonredPoints := by
  rintro ⟨f, hf, hmem, hcol⟩
  exact hfour ⟨f, hf, fun i ↦ T.nonredPoint_mem_ambient (hmem i), hcol⟩

theorem CellModel.exists_blocker
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) {x y : T.nonredPoints}
    (hxy : x ≠ y)
    (hc : colour (T.toAmbient x) = colour (T.toAmbient y)) :
    ∃ z : T.nonredPoints, (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) := by
  exact M.proper x y hxy ((M.colour_eq_iff x y).mpr hc)

theorem CellModel.blocker_colour_ne
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) {x y z : T.nonredPoints}
    (hxy : x ≠ y)
    (hc : colour (T.toAmbient x) = colour (T.toAmbient y))
    (hz : (z : Point) ∈ openSegment ℝ (x : Point) (y : Point)) :
    colour (T.toAmbient z) ≠ colour (T.toAmbient x) := by
  have hne := Lax56Proofs.HKBBlocking.blocker_colour_ne
    (T.noFour_nonred hfour) M.proper hxy ((M.colour_eq_iff x y).mpr hc) hz
  intro heq
  exact hne ((M.colour_eq_iff z x).mpr heq)

theorem CellModel.card_le_six
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) : T.nonredPoints.card ≤ 6 := by
  have hfourQ : ¬HasFourCollinear T.nonredPoints := by
    exact T.noFour_nonred hfour
  exact card_le_six_of_three_coloured_blocking T.nonredPoints hfourQ
    M.colour3 M.proper

theorem CellModel.no_monoTriple
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    {x y z : T.nonredPoints}
    (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hcxy : colour (T.toAmbient x) = colour (T.toAmbient y))
    (hcyz : colour (T.toAmbient y) = colour (T.toAmbient z)) : False := by
  have hfourQ : ¬HasFourCollinear T.nonredPoints := by
    exact T.noFour_nonred hfour
  exact no_monoTriple_three_colours hfourQ M.proper
    ⟨hxy, hyz, hzx, (M.colour_eq_iff x y).mpr hcxy,
      (M.colour_eq_iff y z).mpr hcyz⟩

/-- With no strict-interior point, the three side blockers have distinct
colours. -/
theorem CellModel.side_colours_pairwise_of_interior_empty
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hempty : cellInteriorPoints P (A : Point) (B : Point) (C : Point) = ∅) :
    Pairwise fun i j : Fin 3 ↦ colour (T.side i) ≠ colour (T.side j) := by
  intro i j hij hc
  have hlocal : T.sideLocal i ≠ T.sideLocal j := by
    intro h
    have hsides : T.side i = T.side j := by
      simpa only [T.toAmbient_sideLocal] using congrArg T.toAmbient h
    exact hij (T.side_injective' hsides)
  obtain ⟨z, hz⟩ := M.exists_blocker hlocal (by simpa using hc)
  have hzStrict := T.strict_of_between_distinct_sides hij (by simpa using hz)
  have hzMem : (z : Point) ∈
      cellInteriorPoints P (A : Point) (B : Point) (C : Point) :=
    mem_cellInteriorPoints.mpr
      ⟨T.nonredPoint_mem_ambient z.property, hzStrict⟩
  rw [hempty] at hzMem
  simp at hzMem

theorem CellSkeleton.side_ne_strictInterior
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C) (i : Fin 3) {p : Point}
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) p) :
    (T.side i : Point) ≠ p := by
  intro h
  fin_cases i
  · have hz := turn_eq_zero_of_between T.hs₀
    have h' : (T.s₀ : Point) = p := by
      simpa [CellSkeleton.side] using h
    rw [h'] at hz
    linarith [hp.1]
  · have hz := turn_eq_zero_of_between T.hs₁
    have h' : (T.s₁ : Point) = p := by
      simpa [CellSkeleton.side] using h
    rw [h'] at hz
    linarith [hp.2.1]
  · have hz := turn_eq_zero_of_between T.hs₂
    have h' : (T.s₂ : Point) = p := by
      simpa [CellSkeleton.side] using h
    rw [h'] at hz
    linarith [hp.2.2]

/-- A unique strict-interior point sees every side blocker. -/
theorem CellModel.interior_colour_ne_side_of_unique
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) (p : P)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p)
    (i : Fin 3) : colour p ≠ colour (T.side i) := by
  intro hc
  let pL := T.interiorLocal p hp
  have hne : pL ≠ T.sideLocal i := by
    intro h
    exact T.side_ne_strictInterior i hp
      (by simpa only [T.coe_sideLocal] using congrArg Subtype.val h.symm)
  obtain ⟨z, hz⟩ := M.exists_blocker hne (by simpa [pL] using hc)
  have hzStrict := T.strict_of_between_side_and_inside i hp
    (by simpa [pL, openSegment_symm] using hz)
  have hzp : T.toAmbient z = p := hunique _ (by simpa using hzStrict)
  have hzpPoint : (z : Point) = (p : Point) :=
    congrArg (fun w : P ↦ (w : Point)) hzp
  have hz' : (z : Point) ∈
      openSegment ℝ (p : Point) (T.side i : Point) := by
    simpa [pL] using hz
  rw [hzpPoint] at hz'
  exact T.side_ne_strictInterior i hp
    ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hz').symm

/-- If two side blockers share a colour and the cell has a unique strict
interior point, that point is their blocker. -/
theorem CellModel.unique_interior_between_same_side_colour
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) (p : P)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p)
    {i j : Fin 3} (hij : i ≠ j)
    (hc : colour (T.side i) = colour (T.side j)) :
    (p : Point) ∈ openSegment ℝ (T.side i : Point) (T.side j : Point) := by
  have hlocal : T.sideLocal i ≠ T.sideLocal j := by
    intro h
    have hsides : T.side i = T.side j := by
      simpa only [T.toAmbient_sideLocal] using congrArg T.toAmbient h
    exact hij (T.side_injective' hsides)
  obtain ⟨z, hz⟩ := M.exists_blocker hlocal (by simpa using hc)
  have hzStrict := T.strict_of_between_distinct_sides hij (by simpa using hz)
  have hzp : T.toAmbient z = p := hunique _ (by simpa using hzStrict)
  have hzpPoint : (z : Point) = (p : Point) :=
    congrArg (fun w : P ↦ (w : Point)) hzp
  rw [← hzpPoint]
  simpa using hz

structure OneInteriorPatternAt
    {P : Finset Point} (colour : P → Fin 4) (red : Fin 4)
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (p : P) (i j k : Fin 3) : Prop where
  hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point)
  hij : i ≠ j
  hjk : j ≠ k
  hki : k ≠ i
  beam_colour : colour (T.side i) = colour (T.side j)
  beam_between : (p : Point) ∈
    openSegment ℝ (T.side i : Point) (T.side j : Point)
  p_colour_ne : ∀ l : Fin 3, colour p ≠ colour (T.side l)
  remaining_colour_ne : colour (T.side k) ≠ colour (T.side i)

/-- Classification of a cell with exactly one strict-interior point. -/
theorem CellModel.one_interior_pattern
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C p : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p) :
    OneInteriorPatternAt colour red T p 0 1 2 ∨
      OneInteriorPatternAt colour red T p 1 2 0 ∨
      OneInteriorPatternAt colour red T p 2 0 1 := by
  let pL := T.interiorLocal p hp
  have hpne (i : Fin 3) : colour p ≠ colour (T.side i) :=
    M.interior_colour_ne_side_of_unique p hp hunique i
  have hpne3 (i : Fin 3) : M.colour3 (T.sideLocal i) ≠ M.colour3 pL := by
    intro h
    apply hpne i
    simpa [pL] using ((M.colour_eq_iff (T.sideLocal i) pL).mp h).symm
  have hpigeon := fin3_three_avoiding_one_have_equal
    (hpne3 0) (hpne3 1) (hpne3 2)
  have hnotAll {i j k : Fin 3}
      (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
      (hcij : colour (T.side i) = colour (T.side j)) :
      colour (T.side k) ≠ colour (T.side i) := by
    intro hcki
    apply M.no_monoTriple hfour
      (x := T.sideLocal i) (y := T.sideLocal j) (z := T.sideLocal k)
    · intro h
      exact hij (T.side_injective' (by
        simpa only [T.toAmbient_sideLocal] using congrArg T.toAmbient h))
    · intro h
      exact hjk (T.side_injective' (by
        simpa only [T.toAmbient_sideLocal] using congrArg T.toAmbient h))
    · intro h
      exact hki (T.side_injective' (by
        simpa only [T.toAmbient_sideLocal] using congrArg T.toAmbient h))
    · simpa using hcij
    · simpa using hcij.symm.trans hcki.symm
  rcases hpigeon with h01 | h12 | h20
  · left
    have hc : colour (T.side 0) = colour (T.side 1) :=
      (M.colour_eq_iff (T.sideLocal 0) (T.sideLocal 1)).mp h01
    exact ⟨hp, by decide, by decide, by decide, hc,
      M.unique_interior_between_same_side_colour p hp hunique (by decide) hc,
      hpne, hnotAll (by decide) (by decide) (by decide) hc⟩
  · right; left
    have hc : colour (T.side 1) = colour (T.side 2) :=
      (M.colour_eq_iff (T.sideLocal 1) (T.sideLocal 2)).mp h12
    exact ⟨hp, by decide, by decide, by decide, hc,
      M.unique_interior_between_same_side_colour p hp hunique (by decide) hc,
      hpne, hnotAll (by decide) (by decide) (by decide) hc⟩
  · right; right
    have hc : colour (T.side 2) = colour (T.side 0) :=
      (M.colour_eq_iff (T.sideLocal 2) (T.sideLocal 0)).mp h20
    exact ⟨hp, by decide, by decide, by decide, hc,
      M.unique_interior_between_same_side_colour p hp hunique (by decide) hc,
      hpne, hnotAll (by decide) (by decide) (by decide) hc⟩

private theorem fin3_eq_one_of_three
    {a r s t : Fin 3}
    (hrs : r ≠ s) (hst : s ≠ t) (htr : t ≠ r) :
    a = r ∨ a = s ∨ a = t := by
  fin_cases a <;> fin_cases r <;> fin_cases s <;> fin_cases t <;> simp_all

private theorem fin3_eq_one_of_two_of_ne_first
    {a b c d : Fin 3}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hda : d ≠ a) :
    d = b ∨ d = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp_all

theorem CellModel.interior_colours_ne_of_two_unique
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) (p q : P)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (q : Point))
    (hpq : p ≠ q)
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p ∨ z = q) :
    colour p ≠ colour q := by
  intro hc
  let pL := T.interiorLocal p hp
  let qL := T.interiorLocal q hq
  have hpqL : pL ≠ qL := by
    intro h
    exact hpq (by simpa [pL, qL] using congrArg T.toAmbient h)
  obtain ⟨z, hz⟩ := M.exists_blocker hpqL (by simpa [pL, qL] using hc)
  have hzStrict := strictlyInside_between_inside_points hp hq
    (by simpa [pL, qL] using hz)
  rcases hunique (T.toAmbient z) (by simpa using hzStrict) with hzp | hzq
  · have hzpPoint : (z : Point) = (p : Point) :=
      congrArg (fun w : P ↦ (w : Point)) hzp
    have hz' : (z : Point) ∈ openSegment ℝ (p : Point) (q : Point) := by
      simpa [pL, qL] using hz
    rw [hzpPoint] at hz'
    apply hpq
    apply Subtype.ext
    exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp hz'
  · have hzqPoint : (z : Point) = (q : Point) :=
      congrArg (fun w : P ↦ (w : Point)) hzq
    have hz' : (z : Point) ∈ openSegment ℝ (p : Point) (q : Point) := by
      simpa [pL, qL] using hz
    rw [hzqPoint] at hz'
    apply hpq
    apply Subtype.ext
    exact (right_mem_openSegment_iff (𝕜 := ℝ)).mp hz'

/-- In a cell with exactly two strict-interior points, a same-coloured pair
consisting of one interior point and one side blocker is blocked by the
other interior point. -/
theorem CellModel.other_interior_between_same_side_colour
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T) (p q : P)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (q : Point))
    (hpq : p ≠ q)
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p ∨ z = q)
    (i : Fin 3) (hc : colour p = colour (T.side i)) :
    (q : Point) ∈ openSegment ℝ (p : Point) (T.side i : Point) := by
  let pL := T.interiorLocal p hp
  have hne : pL ≠ T.sideLocal i := by
    intro h
    exact T.side_ne_strictInterior i hp
      (congrArg Subtype.val (by
        simpa [pL] using congrArg T.toAmbient h.symm))
  obtain ⟨z, hz⟩ := M.exists_blocker hne (by simpa [pL] using hc)
  have hzStrict := T.strict_of_between_side_and_inside i hp
    (by simpa [pL, openSegment_symm] using hz)
  rcases hunique (T.toAmbient z) (by simpa using hzStrict) with hzp | hzq
  · have hzpPoint : (z : Point) = (p : Point) :=
      congrArg (fun w : P ↦ (w : Point)) hzp
    have hz' : (z : Point) ∈
        openSegment ℝ (p : Point) (T.side i : Point) := by
      simpa [pL] using hz
    rw [hzpPoint] at hz'
    exact (T.side_ne_strictInterior i hp
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hz').symm).elim
  · have hzqPoint : (z : Point) = (q : Point) :=
      congrArg (fun w : P ↦ (w : Point)) hzq
    rw [← hzqPoint]
    simpa [pL] using hz

structure TwoInteriorPatternAt
    {P : Finset Point} (colour : P → Fin 4) (red : Fin 4)
    {A B C : P} (T : CellSkeleton P colour red A B C)
    (p q : P) (i j k : Fin 3) : Prop where
  hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point)
  hq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (q : Point)
  hpq : p ≠ q
  hij : i ≠ j
  hjk : j ≠ k
  hki : k ≠ i
  beam_colour : colour (T.side i) = colour (T.side j)
  beam_between : (p : Point) ∈
    openSegment ℝ (T.side i : Point) (T.side j : Point)
  interior_colour_ne : colour p ≠ colour q
  p_colour_ne_beam : colour p ≠ colour (T.side i)
  q_colour_ne_beam : colour q ≠ colour (T.side i)
  secondary :
    (colour p = colour (T.side k) ∧
      (q : Point) ∈ openSegment ℝ (p : Point) (T.side k : Point)) ∨
    (colour q = colour (T.side k) ∧
      (p : Point) ∈ openSegment ℝ (q : Point) (T.side k : Point))

theorem CellModel.side_not_rainbow_of_two_interiors
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C p q : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (q : Point))
    (hpq : p ≠ q)
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p ∨ z = q) :
    colour (T.side 0) = colour (T.side 1) ∨
      colour (T.side 1) = colour (T.side 2) ∨
      colour (T.side 2) = colour (T.side 0) := by
  by_contra hnone
  push Not at hnone
  obtain ⟨h01, h12, h20⟩ := hnone
  let pL := T.interiorLocal p hp
  let qL := T.interiorLocal q hq
  have hpqColour := M.interior_colours_ne_of_two_unique p q hp hq hpq hunique
  have hs01 : M.colour3 (T.sideLocal 0) ≠ M.colour3 (T.sideLocal 1) := by
    intro h
    exact h01 ((M.colour_eq_iff _ _).mp h)
  have hs12 : M.colour3 (T.sideLocal 1) ≠ M.colour3 (T.sideLocal 2) := by
    intro h
    exact h12 ((M.colour_eq_iff _ _).mp h)
  have hs20 : M.colour3 (T.sideLocal 2) ≠ M.colour3 (T.sideLocal 0) := by
    intro h
    exact h20 ((M.colour_eq_iff _ _).mp h)
  have hpMatch := fin3_eq_one_of_three
    (a := M.colour3 pL) hs01 hs12 hs20
  have hqMatch := fin3_eq_one_of_three
    (a := M.colour3 qL) hs01 hs12 hs20
  obtain ⟨i, hpi⟩ : ∃ i : Fin 3,
      colour p = colour (T.side i) := by
    rcases hpMatch with h | h | h
    · exact ⟨0, (M.colour_eq_iff pL (T.sideLocal 0)).mp h⟩
    · exact ⟨1, (M.colour_eq_iff pL (T.sideLocal 1)).mp h⟩
    · exact ⟨2, (M.colour_eq_iff pL (T.sideLocal 2)).mp h⟩
  obtain ⟨j, hqj⟩ : ∃ j : Fin 3,
      colour q = colour (T.side j) := by
    rcases hqMatch with h | h | h
    · exact ⟨0, (M.colour_eq_iff qL (T.sideLocal 0)).mp h⟩
    · exact ⟨1, (M.colour_eq_iff qL (T.sideLocal 1)).mp h⟩
    · exact ⟨2, (M.colour_eq_iff qL (T.sideLocal 2)).mp h⟩
  have hij : i ≠ j := by
    intro e
    subst j
    exact hpqColour (hpi.trans hqj.symm)
  have hqBetween := M.other_interior_between_same_side_colour
    p q hp hq hpq hunique i hpi
  have hpBetween := M.other_interior_between_same_side_colour
    q p hq hp hpq.symm (by
      intro z hz
      rcases hunique z hz with h | h
      · exact Or.inr h
      · exact Or.inl h) j hqj
  exact not_nested_openSegments hfour
    (T.side_injective'.ne hij)
    (by
      intro e
      exact T.side_ne_strictInterior i hp (congrArg Subtype.val e))
    (by
      intro e
      exact T.side_ne_strictInterior j hq (congrArg Subtype.val e.symm))
    (by simpa only [openSegment_symm] using hqBetween) hpBetween

theorem CellModel.two_interior_pattern_of_beam
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C p q : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (q : Point))
    (hpq : p ≠ q)
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p ∨ z = q)
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    (hbeam : colour (T.side i) = colour (T.side j)) :
    TwoInteriorPatternAt colour red T p q i j k ∨
      TwoInteriorPatternAt colour red T q p i j k := by
  let iL := T.sideLocal i
  let jL := T.sideLocal j
  let kL := T.sideLocal k
  let pL := T.interiorLocal p hp
  let qL := T.interiorLocal q hq
  have hijL : iL ≠ jL := by
    intro h
    exact hij (T.side_injective' (by
      simpa [iL, jL] using congrArg T.toAmbient h))
  obtain ⟨z, hz⟩ := M.exists_blocker hijL (by simpa [iL, jL] using hbeam)
  have hzStrict := T.strict_of_between_distinct_sides hij
    (by simpa [iL, jL] using hz)
  have hpqColour := M.interior_colours_ne_of_two_unique p q hp hq hpq hunique
  have side_ne_third (r : P)
      (hr : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
        (r : Point))
      (hrBeam : colour r ≠ colour (T.side i)) :
      colour (T.side k) ≠ colour (T.side i) := by
    intro hkBeam
    apply M.no_monoTriple hfour
      (x := iL) (y := jL) (z := kL)
    · exact hijL
    · intro h
      exact hjk (T.side_injective' (by
        simpa [jL, kL] using congrArg T.toAmbient h))
    · intro h
      exact hki (T.side_injective' (by
        simpa [kL, iL] using congrArg T.toAmbient h))
    · simpa [iL, jL] using hbeam
    · simpa [jL, kL] using hbeam.symm.trans hkBeam.symm
  have other_ne_beam (r : P)
      (hr : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
        (r : Point)) : colour r ≠ colour (T.side i) := by
    intro hrcol
    let rL := T.interiorLocal r hr
    apply M.no_monoTriple hfour (x := iL) (y := jL) (z := rL)
    · exact hijL
    · intro h
      exact T.side_ne_strictInterior j hr (by
        exact congrArg Subtype.val (by
          simpa [jL, rL] using congrArg T.toAmbient h))
    · intro h
      exact T.side_ne_strictInterior i hr (by
        exact congrArg Subtype.val (by
          simpa [iL, rL] using congrArg T.toAmbient h.symm))
    · simpa [iL, jL] using hbeam
    · simpa [jL, rL] using hbeam.symm.trans hrcol.symm
  have makePattern (bp oq : P)
      (hbp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
        (bp : Point))
      (hoq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
        (oq : Point))
      (hbpoq : bp ≠ oq)
      (hbpOq : colour bp ≠ colour oq)
      (hunique' : ∀ z : P,
        StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
        z = bp ∨ z = oq)
      (hzbp : T.toAmbient z = bp) :
      TwoInteriorPatternAt colour red T bp oq i j k := by
    let bpL := T.interiorLocal bp hbp
    let oqL := T.interiorLocal oq hoq
    have hzPoint : (z : Point) = (bp : Point) :=
      congrArg (fun w : P ↦ (w : Point)) hzbp
    have hbetween : (bp : Point) ∈
        openSegment ℝ (T.side i : Point) (T.side j : Point) := by
      rw [← hzPoint]
      simpa [iL, jL] using hz
    have hbpBeam : colour bp ≠ colour (T.side i) := by
      have hn := M.blocker_colour_ne hfour hijL
        (by simpa [iL, jL] using hbeam) hz
      simpa [iL, hzbp] using hn
    have hoqBeam := other_ne_beam oq hoq
    have hkBeam := side_ne_third bp hbp hbpBeam
    have ha3 : M.colour3 iL ≠ M.colour3 bpL := by
      intro h
      exact hbpBeam (by
        simpa [iL, bpL] using ((M.colour_eq_iff iL bpL).mp h).symm)
    have hac3 : M.colour3 iL ≠ M.colour3 oqL := by
      intro h
      exact hoqBeam (by
        simpa [iL, oqL] using ((M.colour_eq_iff iL oqL).mp h).symm)
    have hbc3 : M.colour3 bpL ≠ M.colour3 oqL := by
      intro h
      exact hbpOq (by simpa [bpL, oqL] using (M.colour_eq_iff bpL oqL).mp h)
    have hda3 : M.colour3 kL ≠ M.colour3 iL := by
      intro h
      exact hkBeam (by simpa [kL, iL] using (M.colour_eq_iff kL iL).mp h)
    have hkEq := fin3_eq_one_of_two_of_ne_first ha3 hac3 hbc3 hda3
    have hsecondary :
        (colour bp = colour (T.side k) ∧
          (oq : Point) ∈ openSegment ℝ (bp : Point) (T.side k : Point)) ∨
        (colour oq = colour (T.side k) ∧
          (bp : Point) ∈ openSegment ℝ (oq : Point) (T.side k : Point)) := by
      rcases hkEq with h | h
      · left
        have hc : colour bp = colour (T.side k) := by
          simpa [bpL, kL] using (M.colour_eq_iff kL bpL).mp h |>.symm
        exact ⟨hc, M.other_interior_between_same_side_colour bp oq hbp hoq
          hbpoq hunique' k hc⟩
      · right
        have hc : colour oq = colour (T.side k) := by
          simpa [oqL, kL] using (M.colour_eq_iff kL oqL).mp h |>.symm
        exact ⟨hc, M.other_interior_between_same_side_colour oq bp hoq hbp
          hbpoq.symm (fun r hr ↦ (hunique' r hr).symm) k hc⟩
    exact ⟨hbp, hoq, hbpoq, hij, hjk, hki, hbeam, hbetween,
      hbpOq, hbpBeam, hoqBeam, hsecondary⟩
  rcases hunique (T.toAmbient z) (by simpa using hzStrict) with hzp | hzq
  · exact Or.inl (makePattern p q hp hq hpq hpqColour hunique hzp)
  · exact Or.inr (makePattern q p hq hp hpq.symm hpqColour.symm
      (fun r hr ↦ (hunique r hr).symm) hzq)

/-- Classification of a cell with exactly two strict-interior points. -/
theorem CellModel.two_interior_pattern
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C p q : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hp : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (p : Point))
    (hq : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (q : Point))
    (hpq : p ≠ q)
    (hunique : ∀ z : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      z = p ∨ z = q) :
    (TwoInteriorPatternAt colour red T p q 0 1 2 ∨
      TwoInteriorPatternAt colour red T q p 0 1 2) ∨
    (TwoInteriorPatternAt colour red T p q 1 2 0 ∨
      TwoInteriorPatternAt colour red T q p 1 2 0) ∨
    (TwoInteriorPatternAt colour red T p q 2 0 1 ∨
      TwoInteriorPatternAt colour red T q p 2 0 1) := by
  rcases M.side_not_rainbow_of_two_interiors hfour hp hq hpq hunique with
      h01 | h12 | h20
  · exact Or.inl (M.two_interior_pattern_of_beam hfour hp hq hpq hunique
      (by decide) (by decide) (by decide) h01)
  · exact Or.inr (Or.inl (M.two_interior_pattern_of_beam hfour hp hq hpq hunique
      (by decide) (by decide) (by decide) h12))
  · exact Or.inr (Or.inr (M.two_interior_pattern_of_beam hfour hp hq hpq hunique
      (by decide) (by decide) (by decide) h20))

/-- A unique zero of a supporting turn functional remains the unique zero on
the finite convex hull. -/
theorem eq_unique_zero_of_mem_convexHull
    (Q : Finset Point) (a b y x : Point)
    (hy : y ∈ Q)
    (hnonneg : ∀ p ∈ Q, 0 ≤ turn a b p)
    (hunique : ∀ p ∈ Q, turn a b p = 0 → p = y)
    (hx : x ∈ convexHull ℝ (Q : Set Point))
    (hxzero : turn a b x = 0) : x = y := by
  classical
  obtain ⟨w, hw0, hw1, hwcenter⟩ := (Finset.mem_convexHull').mp hx
  have hwzero : ∀ p ∈ Q, p ≠ y → w p = 0 := by
    intro p hp hpne
    have hpturn : 0 < turn a b p := by
      exact lt_of_le_of_ne (hnonneg p hp)
        (fun h ↦ hpne (hunique p hp h.symm))
    exact weight_eq_zero_of_turn_pos a b x Q w hw0 hw1 hwcenter hxzero
      hnonneg hp hpturn
  have hwy : w y = 1 := by
    have hsum := hw1
    rw [Finset.sum_eq_single y] at hsum
    · exact hsum
    · intro p hp hpne
      exact hwzero p hp hpne
    · exact fun h ↦ (h hy).elim
  rw [← hwcenter]
  calc
    (∑ p ∈ Q, w p • p) = w y • y := by
      apply Finset.sum_eq_single y
      · intro p hp hpne
        rw [hwzero p hp hpne, zero_smul]
      · intro h
        exact (h hy).elim
    _ = y := by rw [hwy, one_smul]

theorem mem_extremePoints_of_unique_support_zero
    (Q : Finset Point) (a b y : Point)
    (hy : y ∈ Q)
    (hyzero : turn a b y = 0)
    (hnonneg : ∀ p ∈ Q, 0 ≤ turn a b p)
    (hunique : ∀ p ∈ Q, turn a b p = 0 → p = y) :
    y ∈ (convexHull ℝ (Q : Set Point)).extremePoints ℝ := by
  refine ⟨subset_convexHull ℝ (Q : Set Point) hy, ?_⟩
  intro x hx z hz hyxz
  have hQsub : (Q : Set Point) ⊆ {p | 0 ≤ turn a b p} := by
    intro p hp
    exact hnonneg p hp
  have hconv : Convex ℝ {p : Point | 0 ≤ turn a b p} := by
    intro p hp q hq u v hu hv huv
    change 0 ≤ turn a b (u • p + v • q)
    rw [turn_convex_combo a b p q u v huv]
    exact add_nonneg (mul_nonneg hu hp) (mul_nonneg hv hq)
  have hxnonneg : 0 ≤ turn a b x := convexHull_min hQsub hconv hx
  have hznonneg : 0 ≤ turn a b z := convexHull_min hQsub hconv hz
  obtain ⟨t, ht, ht1, heq⟩ := turn_of_mem_openSegment (a := a) (b := b) hyxz
  have hxzero : turn a b x = 0 := by
    rw [hyzero] at heq
    nlinarith
  exact eq_unique_zero_of_mem_convexHull Q a b y x hy hnonneg hunique hx hxzero

/-- Each of the three side blockers is an exposed, hence extreme, point of
the local six-or-fewer point set. -/
theorem CellSkeleton.sideLocal_mem_extremePoints
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    (T : CellSkeleton P colour red A B C)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (i : Fin 3) :
    (T.sideLocal i : Point) ∈
      (convexHull ℝ (T.nonredPoints : Set Point)).extremePoints ℝ := by
  let edgeA : Fin 3 → Point := ![(A : Point), (B : Point), (C : Point)]
  let edgeB : Fin 3 → Point := ![(B : Point), (C : Point), (A : Point)]
  have hnonneg (p : Point) (hp : p ∈ T.nonredPoints) :
      0 ≤ turn (edgeA i) (edgeB i) p := by
    have he := triangle_edge_nonneg T.hpos.le (T.nonredPoint_mem_hull hp)
    fin_cases i
    · exact he.1
    · exact he.2.1
    · exact he.2.2
  have hunique (p : Point) (hp : p ∈ T.nonredPoints)
      (hz : turn (edgeA i) (edgeB i) p = 0) :
      p = (T.sideLocal i : Point) := by
    let pP : P := ⟨p, T.nonredPoint_mem_ambient hp⟩
    have hpNotRed := T.nonredPoint_colour_ne hinterior ⟨p, hp⟩
    fin_cases i
    · rcases point_eq_of_on_full_line (p := pP) hfour T.hAB T.hs₀
          (by simpa [edgeA, edgeB, pP] using hz) with h | h | h
      · exact (hpNotRed ((congrArg colour h).trans T.colourA)).elim
      · exact (hpNotRed ((congrArg colour h).trans T.colourB)).elim
      · exact congrArg Subtype.val h
    · rcases point_eq_of_on_full_line (p := pP) hfour T.hBC T.hs₁
          (by simpa [edgeA, edgeB, pP] using hz) with h | h | h
      · exact (hpNotRed ((congrArg colour h).trans T.colourB)).elim
      · exact (hpNotRed ((congrArg colour h).trans T.colourC)).elim
      · exact congrArg Subtype.val h
    · rcases point_eq_of_on_full_line (p := pP) hfour T.hCA T.hs₂
          (by simpa [edgeA, edgeB, pP] using hz) with h | h | h
      · exact (hpNotRed ((congrArg colour h).trans T.colourC)).elim
      · exact (hpNotRed ((congrArg colour h).trans T.colourA)).elim
      · exact congrArg Subtype.val h
  apply mem_extremePoints_of_unique_support_zero T.nonredPoints
    (edgeA i) (edgeB i) (T.sideLocal i : Point)
  · exact (T.sideLocal i).property
  · fin_cases i
    · simpa [edgeA, edgeB] using turn_eq_zero_of_between T.hs₀
    · simpa [edgeA, edgeB] using turn_eq_zero_of_between T.hs₁
    · simpa [edgeA, edgeB] using turn_eq_zero_of_between T.hs₂
  · exact hnonneg
  · exact hunique

/-- In the six-point local model the three exposed side blockers have
pairwise distinct colours. -/
theorem CellModel.side_colours_pairwise_of_card_eq_six
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (hcard : T.nonredPoints.card = 6) :
    Pairwise fun i j : Fin 3 ↦ colour (T.side i) ≠ colour (T.side j) := by
  intro i j hij hc
  have hiExt := T.sideLocal_mem_extremePoints hfour hinterior i
  have hjExt := T.sideLocal_mem_extremePoints hfour hinterior j
  have hijLocal : T.sideLocal i ≠ T.sideLocal j := by
    intro h
    exact hij (T.side_injective' (by
      simpa only [T.toAmbient_sideLocal] using congrArg T.toAmbient h))
  have hne := extremePoints_colour_ne_of_card_eq_six hcard
    (T.noFour_nonred hfour) M.proper hiExt hjExt hijLocal
  apply hne
  apply (M.colour_eq_iff _ _).mpr
  simpa using hc

/-- The second point in the colour class of a side blocker in a six-point
cell.  It is defined in the reduced three-colour model, where every colour
class has exactly two points. -/
noncomputable def CellModel.mateOfSix
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hfour : ¬HasFourCollinear P) (hcard : T.nonredPoints.card = 6)
    (i : Fin 3) : T.nonredPoints :=
  Classical.choose (exists_other_same_colour_of_card_eq_six hcard
    (T.noFour_nonred hfour) M.proper (T.sideLocal i))

theorem CellModel.mateOfSix_ne
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hfour : ¬HasFourCollinear P) (hcard : T.nonredPoints.card = 6)
    (i : Fin 3) : M.mateOfSix hfour hcard i ≠ T.sideLocal i :=
  (Classical.choose_spec (exists_other_same_colour_of_card_eq_six hcard
    (T.noFour_nonred hfour) M.proper (T.sideLocal i))).1

theorem CellModel.mateOfSix_colour3
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hfour : ¬HasFourCollinear P) (hcard : T.nonredPoints.card = 6)
    (i : Fin 3) :
    M.colour3 (M.mateOfSix hfour hcard i) = M.colour3 (T.sideLocal i) :=
  (Classical.choose_spec (exists_other_same_colour_of_card_eq_six hcard
    (T.noFour_nonred hfour) M.proper (T.sideLocal i))).2

theorem CellModel.mateOfSix_colour
    {P : Finset Point} {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hfour : ¬HasFourCollinear P) (hcard : T.nonredPoints.card = 6)
    (i : Fin 3) :
    colour (T.toAmbient (M.mateOfSix hfour hcard i)) = colour (T.side i) := by
  rw [← T.toAmbient_sideLocal]
  exact (M.colour_eq_iff _ _).mp (M.mateOfSix_colour3 hfour hcard i)

theorem CellModel.mateOfSix_ne_side
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (hcard : T.nonredPoints.card = 6) (i j : Fin 3) :
    M.mateOfSix hfour hcard i ≠ T.sideLocal j := by
  intro h
  have hc : colour (T.side i) = colour (T.side j) := by
    rw [← M.mateOfSix_colour hfour hcard i]
    simpa only [T.toAmbient_sideLocal] using congrArg colour
      (congrArg T.toAmbient h)
  have hij : i = j := by
    by_contra hij
    exact M.side_colours_pairwise_of_card_eq_six hfour hinterior hcard hij hc
  subst j
  exact M.mateOfSix_ne hfour hcard i h

theorem CellModel.mateOfSix_strict
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (hcard : T.nonredPoints.card = 6) (i : Fin 3) :
    StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (M.mateOfSix hfour hcard i : Point) := by
  rcases T.mem_nonredPoints.mp (M.mateOfSix hfour hcard i).property with
      h | h | h | h
  · exact (M.mateOfSix_ne_side hfour hinterior hcard i 0
      (Subtype.ext h)).elim
  · exact (M.mateOfSix_ne_side hfour hinterior hcard i 1
      (Subtype.ext h)).elim
  · exact (M.mateOfSix_ne_side hfour hinterior hcard i 2
      (Subtype.ext h)).elim
  · exact h.2

theorem CellModel.mateOfSix_injective
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (hcard : T.nonredPoints.card = 6) :
    Function.Injective (M.mateOfSix hfour hcard) := by
  intro i j h
  by_contra hij
  apply M.side_colours_pairwise_of_card_eq_six hfour hinterior hcard hij
  rw [← M.mateOfSix_colour hfour hcard i,
    ← M.mateOfSix_colour hfour hcard j]
  exact congrArg colour (congrArg T.toAmbient h)

/-- Every strict-interior local point is one of the three mates of the
exposed side blockers. -/
theorem CellModel.eq_mateOfSix_of_strict
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (hcard : T.nonredPoints.card = 6)
    (x : T.nonredPoints)
    (hx : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
      (x : Point)) :
    ∃ i : Fin 3, x = M.mateOfSix hfour hcard i := by
  have hpair := M.side_colours_pairwise_of_card_eq_six hfour hinterior hcard
  have h01 : M.colour3 (T.sideLocal 0) ≠ M.colour3 (T.sideLocal 1) := by
    intro h
    exact hpair (i := 0) (j := 1) (by decide)
      (by simpa using (M.colour_eq_iff _ _).mp h)
  have h12 : M.colour3 (T.sideLocal 1) ≠ M.colour3 (T.sideLocal 2) := by
    intro h
    exact hpair (i := 1) (j := 2) (by decide)
      (by simpa using (M.colour_eq_iff _ _).mp h)
  have h20 : M.colour3 (T.sideLocal 2) ≠ M.colour3 (T.sideLocal 0) := by
    intro h
    exact hpair (i := 2) (j := 0) (by decide)
      (by simpa using (M.colour_eq_iff _ _).mp h)
  rcases fin3_eq_one_of_three (a := M.colour3 x) h01 h12 h20 with
      hc | hc | hc
  · refine ⟨0, ?_⟩
    rcases colour_eq_cases_of_card_eq_six hcard (T.noFour_nonred hfour)
        M.proper (M.mateOfSix_ne hfour hcard 0).symm
        (M.mateOfSix_colour3 hfour hcard 0).symm hc with h | h
    · exact (T.side_ne_strictInterior 0 hx
        (congrArg Subtype.val h.symm)).elim
    · exact h
  · refine ⟨1, ?_⟩
    rcases colour_eq_cases_of_card_eq_six hcard (T.noFour_nonred hfour)
        M.proper (M.mateOfSix_ne hfour hcard 1).symm
        (M.mateOfSix_colour3 hfour hcard 1).symm hc with h | h
    · exact (T.side_ne_strictInterior 1 hx
        (congrArg Subtype.val h.symm)).elim
    · exact h
  · refine ⟨2, ?_⟩
    rcases colour_eq_cases_of_card_eq_six hcard (T.noFour_nonred hfour)
        M.proper (M.mateOfSix_ne hfour hcard 2).symm
        (M.mateOfSix_colour3 hfour hcard 2).symm hc with h | h
    · exact (T.side_ne_strictInterior 2 hx
        (congrArg Subtype.val h.symm)).elim
    · exact h

/-- The complete six-point pattern in a triangular cell.  `mate i` is the
strict-interior point having the colour of side blocker `i`; the three
blocking incidences form one of the two directed 3-cycles. -/
structure ThreeInteriorPattern
    {P : Finset Point} (colour : P → Fin 4) (red : Fin 4)
    {A B C : P} (T : CellSkeleton P colour red A B C) where
  mate : Fin 3 → P
  strict : ∀ i,
    StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (mate i : Point)
  mate_colour : ∀ i, colour (mate i) = colour (T.side i)
  injective : Function.Injective mate
  cover : ∀ z : P,
    StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (z : Point) →
      ∃ i, z = mate i
  cycle :
    (((mate 1 : Point) ∈ openSegment ℝ (T.side 0 : Point) (mate 0 : Point)) ∧
      ((mate 2 : Point) ∈ openSegment ℝ (T.side 1 : Point) (mate 1 : Point)) ∧
      ((mate 0 : Point) ∈ openSegment ℝ (T.side 2 : Point) (mate 2 : Point))) ∨
    (((mate 2 : Point) ∈ openSegment ℝ (T.side 0 : Point) (mate 0 : Point)) ∧
      ((mate 0 : Point) ∈ openSegment ℝ (T.side 1 : Point) (mate 1 : Point)) ∧
      ((mate 1 : Point) ∈ openSegment ℝ (T.side 2 : Point) (mate 2 : Point)))

private theorem fin3_cycle_of_no_fixed_no_two_cycle
    (f : Fin 3 → Fin 3)
    (hfixed : ∀ i, f i ≠ i)
    (htwo : ∀ i j, i ≠ j → f i = j → f j ≠ i) :
    (f 0 = 1 ∧ f 1 = 2 ∧ f 2 = 0) ∨
      (f 0 = 2 ∧ f 1 = 0 ∧ f 2 = 1) := by
  have h0 : f 0 = 1 ∨ f 0 = 2 := by
    rcases fin3_eq_one_of_three (a := f 0) (r := 0) (s := 1) (t := 2)
        (by decide) (by decide) (by decide) with h | h | h
    · exact (hfixed 0 h).elim
    · exact Or.inl h
    · exact Or.inr h
  rcases h0 with h01 | h02
  · left
    have h10 : f 1 ≠ 0 := htwo 0 1 (by decide) h01
    have h12 : f 1 = 2 := by
      rcases fin3_eq_one_of_three (a := f 1) (r := 0) (s := 1) (t := 2)
          (by decide) (by decide) (by decide) with h | h | h
      · exact (h10 h).elim
      · exact (hfixed 1 h).elim
      · exact h
    have h21 : f 2 ≠ 1 := htwo 1 2 (by decide) h12
    have h20 : f 2 = 0 := by
      rcases fin3_eq_one_of_three (a := f 2) (r := 0) (s := 1) (t := 2)
          (by decide) (by decide) (by decide) with h | h | h
      · exact h
      · exact (h21 h).elim
      · exact (hfixed 2 h).elim
    exact ⟨h01, h12, h20⟩
  · right
    have h10 : f 2 ≠ 0 := htwo 0 2 (by decide) h02
    have h21 : f 2 = 1 := by
      rcases fin3_eq_one_of_three (a := f 2) (r := 0) (s := 1) (t := 2)
          (by decide) (by decide) (by decide) with h | h | h
      · exact (h10 h).elim
      · exact h
      · exact (hfixed 2 h).elim
    have h12 : f 1 ≠ 2 := htwo 2 1 (by decide) h21
    have h10' : f 1 = 0 := by
      rcases fin3_eq_one_of_three (a := f 1) (r := 0) (s := 1) (t := 2)
          (by decide) (by decide) (by decide) with h | h | h
      · exact h
      · exact (hfixed 1 h).elim
      · exact (h12 h).elim
    exact ⟨h02, h10', h21⟩

/-- Lemma 3.1(4): in a six-point cell the three interior/side colour pairs
are linked by one of the two blocking 3-cycles. -/
theorem CellModel.three_interior_pattern
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 4} {red : Fin 4} {A B C : P}
    {T : CellSkeleton P colour red A B C}
    (M : CellModel colour red T)
    (hinterior : ∀ p : P,
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point) (p : Point) →
      colour p ≠ red)
    (hcard : T.nonredPoints.card = 6) :
    Nonempty (ThreeInteriorPattern colour red T) := by
  let mateL : Fin 3 → T.nonredPoints := M.mateOfSix hfour hcard
  let mateP : Fin 3 → P := fun i ↦ T.toAmbient (mateL i)
  have hstrict (i : Fin 3) :
      StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
        (mateP i : Point) := by
    simpa [mateP, mateL] using M.mateOfSix_strict hfour hinterior hcard i
  have hcolour (i : Fin 3) : colour (mateP i) = colour (T.side i) := by
    simpa [mateP, mateL] using M.mateOfSix_colour hfour hcard i
  have hinj : Function.Injective mateP := by
    intro i j h
    apply M.mateOfSix_injective hfour hinterior hcard
    apply Subtype.ext
    exact congrArg (fun z : P ↦ (z : Point)) h
  have hcover (z : P)
      (hz : StrictlyInsideTriangle (A : Point) (B : Point) (C : Point)
        (z : Point)) : ∃ i, z = mateP i := by
    let zL := T.interiorLocal z hz
    obtain ⟨i, hi⟩ := M.eq_mateOfSix_of_strict hfour hinterior hcard zL
      (by simpa [zL] using hz)
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact congrArg (fun w : P ↦ (w : Point)) (congrArg T.toAmbient hi)
  have hnext (i : Fin 3) : ∃ j : Fin 3,
      (mateP j : Point) ∈
        openSegment ℝ (T.side i : Point) (mateP i : Point) := by
    have hine : T.sideLocal i ≠ mateL i :=
      (M.mateOfSix_ne hfour hcard i).symm
    obtain ⟨z, hz⟩ := M.proper (T.sideLocal i) (mateL i) hine
      (M.mateOfSix_colour3 hfour hcard i).symm
    have hzStrict := T.strict_of_between_side_and_inside i (hstrict i)
      (by simpa [mateP, mateL] using hz)
    obtain ⟨j, hj⟩ := M.eq_mateOfSix_of_strict hfour hinterior hcard z hzStrict
    refine ⟨j, ?_⟩
    have hjPoint : (z : Point) = (mateP j : Point) := by
      simpa [mateP, mateL] using congrArg Subtype.val hj
    rw [← hjPoint]
    simpa [mateP, mateL] using hz
  let next : Fin 3 → Fin 3 := fun i ↦ Classical.choose (hnext i)
  have hbetween (i : Fin 3) :
      (mateP (next i) : Point) ∈
        openSegment ℝ (T.side i : Point) (mateP i : Point) :=
    Classical.choose_spec (hnext i)
  have hfixed (i : Fin 3) : next i ≠ i := by
    intro h
    have hi := hbetween i
    rw [h] at hi
    exact T.side_ne_strictInterior i (hstrict i)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hi)
  have htwo (i j : Fin 3) (hij : i ≠ j) (hijNext : next i = j) :
      next j ≠ i := by
    intro hjiNext
    have hsideMate (k : Fin 3) : T.side k ≠ mateP k := by
      intro e
      exact T.side_ne_strictInterior k (hstrict k) (congrArg Subtype.val e)
    have hsideSide : T.side i ≠ T.side j := T.side_injective'.ne hij
    have hmateMate : mateP i ≠ mateP j := hinj.ne hij
    have hsideIMateJ : T.side i ≠ mateP j := by
      intro e
      exact T.side_ne_strictInterior i (hstrict j) (congrArg Subtype.val e)
    have hmateISideJ : mateP i ≠ T.side j := by
      intro e
      exact T.side_ne_strictInterior j (hstrict i) (congrArg Subtype.val e.symm)
    have hcross := first_pair_points_do_not_block_second hfour
      (hsideMate i) (hsideMate j).symm hsideIMateJ hsideSide
      hmateMate hmateISideJ
      (by simpa [hijNext] using hbetween i)
    apply hcross.2
    simpa [hjiNext, openSegment_symm] using hbetween j
  rcases fin3_cycle_of_no_fixed_no_two_cycle next hfixed htwo with h | h
  · refine ⟨⟨mateP, hstrict, hcolour, hinj, hcover, Or.inl ?_⟩⟩
    exact ⟨by simpa [h.1] using hbetween 0,
      by simpa [h.2.1] using hbetween 1,
      by simpa [h.2.2] using hbetween 2⟩
  · refine ⟨⟨mateP, hstrict, hcolour, hinj, hcover, Or.inr ?_⟩⟩
    exact ⟨by simpa [h.1] using hbetween 0,
      by simpa [h.2.1] using hbetween 1,
      by simpa [h.2.2] using hbetween 2⟩
end Lax56Proofs.HKBDirectTrianglePatterns
