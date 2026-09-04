import Lax56Proofs.HKBDirectCore
import Mathlib.Tactic

/-!
The concave monochromatic four-set and its six red-edge blockers.
-/

namespace Lax56Proofs.HKBDirectConcave

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBDirectCore
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

noncomputable def cellInteriorPoints
    (P : Finset Point) (a b c : Point) : Finset Point := by
  classical
  exact P.filter fun p ↦ StrictlyInsideTriangle a b c p

@[simp] theorem mem_cellInteriorPoints
    {P : Finset Point} {a b c p : Point} :
    p ∈ cellInteriorPoints P a b c ↔
      p ∈ P ∧ StrictlyInsideTriangle a b c p := by
  classical
  simp [cellInteriorPoints]

/-- The six blockers on the edges of the planar straight-line `K₄`
formed by an outer triangle and one interior point. -/
structure ConcaveSkeleton
    (P : Finset Point) (colour : P → Fin 4)
    (a b c d : P) where
  u₁ : P
  u₂ : P
  u₃ : P
  v₁ : P
  v₂ : P
  v₃ : P
  hu₁ : (u₁ : Point) ∈ openSegment ℝ (a : Point) (d : Point)
  hu₂ : (u₂ : Point) ∈ openSegment ℝ (b : Point) (d : Point)
  hu₃ : (u₃ : Point) ∈ openSegment ℝ (c : Point) (d : Point)
  hv₁ : (v₁ : Point) ∈ openSegment ℝ (b : Point) (c : Point)
  hv₂ : (v₂ : Point) ∈ openSegment ℝ (a : Point) (c : Point)
  hv₃ : (v₃ : Point) ∈ openSegment ℝ (a : Point) (b : Point)
  blockers_injective : Function.Injective (![u₁, u₂, u₃, v₁, v₂, v₃] : Fin 6 → P)
  blocker_colour_ne : ∀ i,
    colour ((![u₁, u₂, u₃, v₁, v₂, v₃] : Fin 6 → P) i) ≠ colour a

private theorem four_points_pairwise
    {P : Finset Point} {a b c d : P}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a, b, c, d] : Fin 4 → P) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem six_points_pairwise
    {X : Type*} {a b c d e f : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective (![a, b, c, d, e, f] : Fin 6 → X) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Construct the skeleton from proper blocking. -/
theorem exists_concaveSkeleton
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    (colour : P → Fin 4) (hproper : ProperBlocking P colour)
    {a b c d : P}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hmonoB : colour a = colour b)
    (hmonoC : colour a = colour c)
    (hmonoD : colour a = colour d)
    (hinside : StrictlyInsideTriangle (a : Point) (b : Point) (c : Point)
      (d : Point)) :
    Nonempty (ConcaveSkeleton P colour a b c d) := by
  classical
  obtain ⟨u₁, hu₁⟩ := hproper a d had hmonoD
  obtain ⟨u₂, hu₂⟩ := hproper b d hbd (hmonoB.symm.trans hmonoD)
  obtain ⟨u₃, hu₃⟩ := hproper c d hcd (hmonoC.symm.trans hmonoD)
  obtain ⟨v₁, hv₁⟩ := hproper b c hbc (hmonoB.symm.trans hmonoC)
  obtain ⟨v₂, hv₂⟩ := hproper a c hac hmonoC
  obtain ⟨v₃, hv₃⟩ := hproper a b hab hmonoB
  have hshare : ∀ {x y z r s : P}, x ≠ y → x ≠ z → y ≠ z →
      (r : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      (s : Point) ∈ openSegment ℝ (x : Point) (z : Point) → r ≠ s := by
    intro x y z r s hxy hxz hyz hry hrs hrsEq
    apply hyz
    apply other_endpoint_eq_of_common_blocker hfour hxy hxz hry
    simpa only [hrsEq] using hrs
  have hu₁u₂ : u₁ ≠ u₂ := by
    apply hshare had.symm hbd.symm hab
    · simpa only [openSegment_symm] using hu₁
    · simpa only [openSegment_symm] using hu₂
  have hu₁u₃ : u₁ ≠ u₃ := by
    apply hshare had.symm hcd.symm hac
    · simpa only [openSegment_symm] using hu₁
    · simpa only [openSegment_symm] using hu₃
  have hu₂u₃ : u₂ ≠ u₃ := by
    apply hshare hbd.symm hcd.symm hbc
    · simpa only [openSegment_symm] using hu₂
    · simpa only [openSegment_symm] using hu₃
  have hu₁v₂ : u₁ ≠ v₂ := hshare had hac hcd.symm hu₁ hv₂
  have hu₁v₃ : u₁ ≠ v₃ := hshare had hab hbd.symm hu₁ hv₃
  have hu₂v₁ : u₂ ≠ v₁ := hshare hbd hbc hcd.symm hu₂ hv₁
  have hu₂v₃ : u₂ ≠ v₃ := by
    apply hshare hbd hab.symm had.symm
    · exact hu₂
    · simpa only [openSegment_symm] using hv₃
  have hu₃v₁ : u₃ ≠ v₁ := by
    apply hshare hcd hbc.symm hbd.symm
    · exact hu₃
    · simpa only [openSegment_symm] using hv₁
  have hu₃v₂ : u₃ ≠ v₂ := by
    apply hshare hcd hac.symm had.symm
    · exact hu₃
    · simpa only [openSegment_symm] using hv₂
  have hv₁v₂ : v₁ ≠ v₂ := by
    apply hshare hbc.symm hac.symm hab.symm
    · simpa only [openSegment_symm] using hv₁
    · simpa only [openSegment_symm] using hv₂
  have hv₁v₃ : v₁ ≠ v₃ := by
    apply hshare hbc hab.symm hac.symm
    · exact hv₁
    · simpa only [openSegment_symm] using hv₃
  have hv₂v₃ : v₂ ≠ v₃ := hshare hac hab hbc.symm hv₂ hv₃
  have habc : 0 < turn (a : Point) (b : Point) (c : Point) :=
    turn_pos_of_strictlyInsideTriangle hinside
  have hu₁v₁ : u₁ ≠ v₁ := by
    intro e
    have hbca : 0 < turn (b : Point) (c : Point) (a : Point) := by
      simpa only [turn_rotate] using habc
    have hpos := edgeTurn_pos_of_mem_openSegment hu₁
      hbca.le hinside.2.1.le (Or.inl hbca)
    have hz : turn (b : Point) (c : Point) (u₁ : Point) = 0 := by
      simpa [e] using turn_eq_zero_of_between hv₁
    linarith
  have hu₂v₂ : u₂ ≠ v₂ := by
    apply Ne.symm
    intro e
    have hcab : 0 < turn (c : Point) (a : Point) (b : Point) := by
      simpa only [turn_rotate, turn_rotate] using habc
    have hpos := edgeTurn_pos_of_mem_openSegment hu₂
      hcab.le hinside.2.2.le
      (Or.inl hcab)
    have hz : turn (c : Point) (a : Point) (v₂ : Point) = 0 := by
      rw [turn_swap_first, turn_eq_zero_of_between hv₂, neg_zero]
    rw [← e] at hpos
    linarith
  have hu₃v₃ : u₃ ≠ v₃ := by
    apply Ne.symm
    intro e
    have hpos := edgeTurn_pos_of_mem_openSegment hu₃
      habc.le hinside.1.le (Or.inl habc)
    have hz : turn (a : Point) (b : Point) (v₃ : Point) = 0 :=
      turn_eq_zero_of_between hv₃
    rw [← e] at hpos
    linarith
  let r : Fin 6 → P := ![u₁, u₂, u₃, v₁, v₂, v₃]
  have hr : Function.Injective r := by
    exact six_points_pairwise hu₁u₂ hu₁u₃ hu₁v₁ hu₁v₂ hu₁v₃
      hu₂u₃ hu₂v₁ hu₂v₂ hu₂v₃ hu₃v₁ hu₃v₂ hu₃v₃ hv₁v₂ hv₁v₃ hv₂v₃
  have hc (i : Fin 6) : colour (r i) ≠ colour a := by
    fin_cases i
    · exact blocker_colour_ne hfour hproper had hmonoD hu₁
    · intro h
      exact (blocker_colour_ne hfour hproper hbd
        (hmonoB.symm.trans hmonoD) hu₂) (h.trans hmonoB)
    · intro h
      exact (blocker_colour_ne hfour hproper hcd
        (hmonoC.symm.trans hmonoD) hu₃) (h.trans hmonoC)
    · intro h
      exact (blocker_colour_ne hfour hproper hbc
        (hmonoB.symm.trans hmonoC) hv₁) (h.trans hmonoB)
    · exact blocker_colour_ne hfour hproper hac hmonoC hv₂
    · exact blocker_colour_ne hfour hproper hab hmonoB hv₃
  exact ⟨⟨u₁, u₂, u₃, v₁, v₂, v₃,
    hu₁, hu₂, hu₃, hv₁, hv₂, hv₃, hr, hc⟩⟩

end Lax56Proofs.HKBDirectConcave
