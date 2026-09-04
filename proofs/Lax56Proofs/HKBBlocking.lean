import Lax56Proofs.HKBConvexity
import Mathlib.Tactic

/-!
Finite blocking-set lemmas used throughout the direct HKB proof.
-/

namespace Lax56Proofs.HKBBlocking

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.HKBGeometry

/-- Every equal-coloured pair has another point of the same finite set in its
open segment. -/
def ProperBlocking {k : ℕ} (B : Finset Point) (colour : B → Fin k) : Prop :=
  ∀ (x y : B), x ≠ y → colour x = colour y →
    ∃ z : B, (z : Point) ∈ openSegment ℝ (x : Point) (y : Point)

theorem right_mem_affineSpan_pair_of_between
    {x y z : Point} (hxy : x ≠ y) (hz : z ∈ openSegment ℝ x y) :
    y ∈ affineSpan ℝ {x, z} := by
  have hzline : z ∈ affineSpan ℝ {x, y} :=
    mem_affineSpan_pair_of_mem_openSegment hz
  have hzx : z ≠ x := by
    intro e
    subst z
    exact hxy ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hz)
  have heq : affineSpan ℝ {x, z} = affineSpan ℝ {x, y} :=
    affineSpan_pair_eq_of_right_mem_of_ne hzline hzx
  rw [heq]
  exact right_mem_affineSpan_pair ℝ x y

/-- Under the no-four-collinear hypothesis, a blocker of an equal-coloured
pair has a different color from the endpoints. -/
theorem blocker_colour_ne
    {k : ℕ} {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin k} (hproper : ProperBlocking B colour)
    {x y z : B} (hxy : x ≠ y) (hcolour : colour x = colour y)
    (hz : (z : Point) ∈ openSegment ℝ (x : Point) (y : Point)) :
    colour z ≠ colour x := by
  intro hzxcolour
  have hzx : z ≠ x := by
    intro e
    subst z
    apply hxy
    apply Subtype.ext
    exact (left_mem_openSegment_iff (𝕜 := ℝ)).mp hz
  obtain ⟨w, hw⟩ := hproper x z hzx.symm hzxcolour.symm
  have hwx : (w : Point) ≠ x := by
    intro e
    have : (x : Point) ∈ openSegment ℝ (x : Point) (z : Point) := e ▸ hw
    exact (Subtype.val_injective.ne hzx.symm)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hwz : (w : Point) ≠ z := by
    intro e
    have : (z : Point) ∈ openSegment ℝ (x : Point) (z : Point) := e ▸ hw
    exact (Subtype.val_injective.ne hzx.symm)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hyx : (y : Point) ≠ x := (Subtype.val_injective.ne hxy.symm)
  have hyz : (y : Point) ≠ z := by
    intro e
    have : (y : Point) ∈ openSegment ℝ (x : Point) (y : Point) := e.symm ▸ hz
    exact hyx ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this).symm
  have hwy : (w : Point) = y := third_point_unique hfour
    x.property z.property w.property y.property
    (Subtype.val_injective.ne hzx.symm) hwx hwz hyx hyz
    (mem_affineSpan_pair_of_mem_openSegment hw)
    (right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hxy) hz)
  exact not_two_mutual_openSegments (Subtype.val_injective.ne hxy)
    ⟨hz, hwy ▸ hw⟩

/-- Three equal-coloured points cannot occur with one strictly between the
other two. -/
theorem no_same_colour_between
    {k : ℕ} {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin k} (hproper : ProperBlocking B colour)
    {x y z : B} (hxy : x ≠ y)
    (hcxz : colour x = colour z) (hzy : colour z = colour y)
    (hz : (z : Point) ∈ openSegment ℝ (x : Point) (y : Point)) : False := by
  exact (blocker_colour_ne hfour hproper hxy (hcxz.trans hzy) hz) hcxz.symm

/-- If one point of a no-four-collinear set lies strictly on two segments
with a common endpoint, then the other endpoints coincide.  This is the
basic incidence fact used to show that blockers of edges sharing a vertex
are distinct. -/
theorem other_endpoint_eq_of_common_blocker
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a b c z : B} (hab : a ≠ b) (hac : a ≠ c)
    (hzab : (z : Point) ∈ openSegment ℝ (a : Point) (b : Point))
    (hzac : (z : Point) ∈ openSegment ℝ (a : Point) (c : Point)) :
    b = c := by
  have hza : (z : Point) ≠ a := by
    intro h
    have : (a : Point) ∈ openSegment ℝ (a : Point) (b : Point) := h ▸ hzab
    exact (Subtype.val_injective.ne hab)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hzb : (z : Point) ≠ b := by
    intro h
    have : (b : Point) ∈ openSegment ℝ (a : Point) (b : Point) := h ▸ hzab
    exact (Subtype.val_injective.ne hab)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  have hzc : (z : Point) ≠ c := by
    intro h
    have : (c : Point) ∈ openSegment ℝ (a : Point) (c : Point) := h ▸ hzac
    exact (Subtype.val_injective.ne hac)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp this)
  apply Subtype.ext
  apply third_point_unique hfour a.property z.property b.property c.property
    hza.symm
    (Subtype.val_injective.ne hab.symm) hzb.symm
    (Subtype.val_injective.ne hac.symm) hzc.symm
  · exact right_mem_affineSpan_pair_of_between
      (Subtype.val_injective.ne hab) hzab
  · exact right_mem_affineSpan_pair_of_between
      (Subtype.val_injective.ne hac) hzac

end Lax56Proofs.HKBBlocking
