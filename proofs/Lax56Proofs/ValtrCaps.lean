import Lax56Proofs.CyclicOrder
import Lax56Proofs.ValtrCounting

namespace Lax56Proofs.ValtrCaps

open Lax56.Geometry Lax56.ConvexLayers Lax56.HujterKisfaludiBak
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry Lax56Proofs.CyclicOrder
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrReduction Lax56Proofs.ValtrCounting

/-- Oriented area as an affine function of its third point. -/
def turnAffine (a b : Point) : Point →ᵃ[ℝ] ℝ where
  toFun p := turn a b p
  linear :=
    { toFun := fun p ↦ (b.1 - a.1) * p.2 - (b.2 - a.2) * p.1
      map_add' := by intros; simp; ring
      map_smul' := by intros; simp; ring }
  map_vadd' := by intros; simp [turn]; ring

/-- Index of a vertex inside a disjoint consecutive six-vertex block. -/
def blockIndex {m : ℕ} (i : Fin (m / 6)) (j : Fin 6) : Fin m :=
  ⟨6 * i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

theorem blockIndex_strictMono {m : ℕ} (i : Fin (m / 6)) : StrictMono (blockIndex i) := by
  intro j k hjk
  change 6 * i.val + j.val < 6 * i.val + k.val
  omega

theorem blockIndex_separated {m : ℕ} {i j : Fin (m / 6)} (hij : i < j) (a b : Fin 6) :
    blockIndex i a < blockIndex j b := by
  change 6 * i.val + a.val < 6 * j.val + b.val
  have := a.isLt
  omega

/-- Constructs precisely the cap/separation data used in the user's counting
argument. The cap equality is proved using the four-triangle fan of a hexagon. -/
theorem exists_sixCaps (Q : Finset Point) (hgen : ¬HasThreeCollinear Q)
    (hcard : 6 < (extremeLayer Q).card) : Nonempty (SixCaps Q) := by
  classical
  let X := extremeLayer Q
  have hXgen : ¬HasThreeCollinear X :=
    fun h ↦ hgen (hasThreeCollinear_mono (extremeLayer_subset Q) h)
  obtain ⟨v, hinj, hrange, htri⟩ := exists_cyclic_order_card X
    (Finset.card_pos.mp (by dsimp [X]; omega)) (extremeLayer_convexPosition Q) hXgen
  let bv : Fin (X.card / 6) → Fin 6 → Point := fun i j ↦ v (blockIndex i j)
  let B : Fin (X.card / 6) → Finset Point := fun i ↦ Finset.univ.image (bv i)
  let f : Fin (X.card / 6) → Point →ᵃ[ℝ] ℝ := fun i ↦ turnAffine (bv i 5) (bv i 0)
  have hbinj (i) : Function.Injective (bv i) := hinj.comp (blockIndex_strictMono i).injective
  have hbrange (i) : (B i : Set Point) = Set.range (bv i) := by simp [B]
  have hbsub (i) : B i ⊆ X := by
    intro p hp
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
    change v (blockIndex i j) ∈ (X : Set Point)
    rw [← hrange]
    exact Set.mem_range_self _
  have hbmem (i) (j) : bv i j ∈ X :=
    hbsub i (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  have hbstrict (i) : StrictConvexHexagon (bv i) := by
    apply strictConvexHexagon_of_triples _ (hbinj i)
    intro a b c hab hbc
    exact htri _ _ _ (blockIndex_strictMono i hab) (blockIndex_strictMono i hbc)
  have hnonneg (i) {p : Point} (hp : p ∈ convexHull ℝ (B i : Set Point)) : 0 ≤ f i p := by
    rw [hbrange] at hp
    have h := edgeTurn_nonneg_of_mem_convexHull (hbstrict i) hp 5
    exact h
  refine ⟨SixCaps.mk B f hbsub ?_ ?_ ?_ ?_⟩
  · intro i
    simp [B, Finset.card_image_of_injective _ (hbinj i)]
  · intro i
    ext p
    constructor
    · intro hp
      exact ⟨convexHull_mono (hbsub i) hp, hnonneg i hp⟩
    · rintro ⟨hpX, hpf⟩
      rw [hbrange]
      apply mem_convexHull_hexagon_of_edge_nonneg (hbstrict i)
      intro j
      by_cases hj : j = 5
      · subst j
        exact hpf
      · have hj5 : j.val < 5 := by omega
        have hadj : (blockIndex i j).val + 1 = (blockIndex i (j + 1)).val := by
          dsimp [blockIndex]
          omega
        apply turn_nonneg_of_mem_convexHull (A := (X : Set Point)) _ hpX
        intro q hq
        rw [← hrange] at hq
        obtain ⟨k, rfl⟩ := hq
        by_cases hkj : k = blockIndex i j
        · subst k
          change 0 ≤ turn (v (blockIndex i j)) (v (blockIndex i (j + 1))) (v (blockIndex i j))
          simp
        by_cases hkn : k = blockIndex i (j + 1)
        · subst k
          change 0 ≤ turn (v (blockIndex i j)) (v (blockIndex i (j + 1)))
            (v (blockIndex i (j + 1)))
          simp
        have h := turn_consecutive_pos v 1 (by simpa only [one_mul] using htri)
          (blockIndex i j) (blockIndex i (j + 1)) hadj k hkj hkn
        simpa only [one_mul] using h.le
  · intro i p hp hpB
    have hpp := Finset.mem_sdiff.mp hp
    have hfirst : bv i 0 ≠ p := fun h ↦ hpp.2 (h ▸ hbmem i 0)
    have hlast : bv i 5 ≠ p := fun h ↦ hpp.2 (h ▸ hbmem i 5)
    have hne := turn_ne_zero_of_generalPosition hgen
      (extremeLayer_subset Q (hbmem i 5)) (extremeLayer_subset Q (hbmem i 0)) hpp.1
      ((hbinj i).ne (by decide : (5 : Fin 6) ≠ 0)) hlast hfirst
    exact lt_of_le_of_ne (hnonneg i hpB) hne.symm
  · intro i j hij p hp
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    change turn (v (blockIndex i 5)) (v (blockIndex i 0)) (v (blockIndex j a)) < 0
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := htri (blockIndex i 0) (blockIndex i 5) (blockIndex j a)
        (blockIndex_strictMono i (by decide : (0 : Fin 6) < 5)) (blockIndex_separated hij 5 a)
      rw [turn_swap_first]
      exact neg_neg_of_pos h
    · have h := htri (blockIndex j a) (blockIndex i 0) (blockIndex i 5)
        (blockIndex_separated hji a 0) (blockIndex_strictMono i (by decide : (0 : Fin 6) < 5))
      rw [turn_reverse]
      exact neg_neg_of_pos h

/-- Lemma 2 is now unconditional: every hexagon-free general-position set
satisfies `|outer| ≤ 6 |next| + 5`. -/
theorem consecutive_layer_bound : ConsecutiveLayerBound :=
  consecutiveLayerBound_of_caps exists_sixCaps

/-- The complete unoptimized Valtr bound, with *only* the four-layer lemma
remaining as a geometric hypothesis. -/
theorem exists_emptyConvexHexagon_of_fourLayer (fourLayer : FourLayerLemma)
    (P : Finset Point) (hP : 2 ^ 428 + 1 ≤ P.card) (hgen : ¬HasThreeCollinear P) :
    ∃ h : Fin 6 → Point, EmptyConvexHexagon P h :=
  exists_emptyConvexHexagon_of_ingredients fourLayer consecutive_layer_bound
    Lax56Proofs.ErdosSzekeres.weak_erdos_szekeres ordered_hexagon_bridge P hP hgen

end Lax56Proofs.ValtrCaps
