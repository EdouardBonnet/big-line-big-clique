import Lax56Proofs.ValtrSectors

namespace Lax56Proofs.ValtrSplice

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle

/-- A supporting line through two ambient points certifies that either
endpoint is a vertex. General position excludes every other generator
from that line, so the closed boundary is handled without a perturbation. -/
theorem vertex_not_mem_hull_of_supporting_line {P X : Finset Point}
    (hgen : ¬HasThreeCollinear P) (hXP : X ⊆ P) {a b : Point}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
    (hside : ∀ p ∈ X, 0 ≤ turn a b p) :
    a ∉ convexHull ℝ ((X : Set Point) \ {a}) := by
  classical
  intro hh
  have hh' : a ∈ convexHull ℝ (X.erase a : Set Point) := by
    simpa only [Finset.coe_erase] using hh
  apply hab
  apply eq_of_mem_convexHull_of_unique_turn_zero
    (Finset.mem_erase.mpr ⟨hab.symm, hb⟩)
    (fun p hp ↦ hside p (Finset.mem_of_mem_erase hp)) _ hh' (by simp)
  intro p hp hz
  by_contra hpb
  have hpa := (Finset.mem_erase.mp hp).1
  exact turn_ne_zero_of_generalPosition hgen (hXP ha) (hXP hb)
    (hXP (Finset.mem_of_mem_erase hp)) hab hpa.symm (Ne.symm hpb) hz

/-- Retained outer vertices remain extreme automatically. To splice in
an inner chain, it suffices that each chain edge supports the chain and
all retained vertices. No orientation checks at the two joins to the
retained outer chain are needed. -/
theorem convexPosition_splice_of_edge_supports {S R : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hR : R ⊆ extremeLayer S)
    {m : ℕ} (v : Fin (m + 2) → Point) (hinj : Function.Injective v)
    (hmem : ∀ i, v i ∈ S)
    (hchain : ∀ i : Fin (m + 1), ∀ j,
      0 ≤ turn (v i.castSucc) (v i.succ) (v j))
    (hcross : ∀ i : Fin (m + 1), ∀ p ∈ R,
      0 ≤ turn (v i.castSucc) (v i.succ) p) :
    ConvexPosition (R ∪ Finset.univ.image v) := by
  classical
  let X := R ∪ Finset.univ.image v
  have hXS : X ⊆ S := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact extremeLayer_subset S (hR hp)
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact hmem i
  have hvX (i) : v i ∈ X :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hedge (i : Fin (m + 1)) :
      ∀ p ∈ X, 0 ≤ turn (v i.castSucc) (v i.succ) p := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hcross i p hp
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      exact hchain i j
  apply (convexPosition_iff X).mpr
  intro p hp
  by_cases hpR : p ∈ R
  · have hnot := extreme_not_mem_convexHull (hR hpR)
      ((Finset.erase_subset p X).trans hXS) (Finset.notMem_erase p X)
    simpa only [Finset.coe_erase] using hnot
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ((Finset.mem_union.mp hp).resolve_left hpR)
  by_cases hj : j.val + 1 < m + 2
  · let i : Fin (m + 1) := ⟨j.val, by omega⟩
    have hij : i.castSucc = j := Fin.ext rfl
    rw [← hij]
    exact vertex_not_mem_hull_of_supporting_line hgen hXS (hvX i.castSucc) (hvX i.succ)
      (hinj.ne (by intro h; have := congrArg Fin.val h; simp at this)) (hedge i)
  · let i : Fin (m + 1) := ⟨j.val - 1, by omega⟩
    have hij : i.succ = j := by apply Fin.ext; dsimp [i]; omega
    rw [← hij]
    have hne : v i.castSucc ≠ v i.succ :=
      hinj.ne (by intro h; have := congrArg Fin.val h; simp at this)
    intro hh
    have heq : v i.succ = v i.castSucc := by
      apply eq_of_mem_convexHull_of_unique_turn_zero
        (A := X.erase (v i.succ))
        (Finset.mem_erase.mpr ⟨hne, hvX i.castSucc⟩)
        (fun p hp ↦ hedge i p (Finset.mem_of_mem_erase hp)) _ _ (by simp)
      · intro p hp hz
        by_contra hpa
        have hpb := (Finset.mem_erase.mp hp).1
        exact turn_ne_zero_of_generalPosition hgen (hmem i.castSucc) (hmem i.succ)
          (hXS (Finset.mem_of_mem_erase hp)) hne (Ne.symm hpa) hpb.symm hz
      · simpa only [Finset.coe_erase] using hh
    exact hne heq.symm

/-- The counting and minimality part of a chain replacement: replacing at
most `m + 2` outer vertices by a supported chain of `m + 2` inner points
contradicts minimality. The supporting inequalities remain explicit inputs. -/
theorem not_minimal_of_supported_splice {S R : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hR : R ⊆ extremeLayer S)
    {m : ℕ} (v : Fin (m + 2) → Point) (hinj : Function.Injective v)
    (hmem : ∀ i, v i ∈ inner S)
    (hchain : ∀ i : Fin (m + 1), ∀ j,
      0 ≤ turn (v i.castSucc) (v i.succ) (v j))
    (hcross : ∀ i : Fin (m + 1), ∀ p ∈ R,
      0 ≤ turn (v i.castSucc) (v i.succ) p)
    (hremoved : (extremeLayer S \ R).card ≤ m + 2) : ¬MinimalOuter S := by
  classical
  intro hmin
  let H := Finset.univ.image v
  have hHinner : H ⊆ inner S := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hmem i
  have hdisj : Disjoint R H := by
    apply Finset.disjoint_left.mpr
    intro p hpR hpH
    exact (Finset.mem_sdiff.mp (hHinner hpH)).2 (hR hpR)
  have hHcard : H.card = m + 2 := by
    simp [H, Finset.card_image_of_injective _ hinj]
  have hcard : (extremeLayer S).card ≤ (R ∪ H).card := by
    rw [Finset.card_union_of_disjoint hdisj, hHcard]
    have hc := Finset.card_sdiff_add_card_eq_card hR
    omega
  have hconv := convexPosition_splice_of_edge_supports hgen hR v hinj
    (fun i ↦ inner_subset S (hmem i)) hchain hcross
  have hsub : R ∪ H ⊆ S :=
    Finset.union_subset (hR.trans (extremeLayer_subset S))
      (hHinner.trans (inner_subset S))
  have heq := hmin (R ∪ H) hsub hconv hcard
  have hv : v 0 ∈ R ∪ H :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  rw [heq] at hv
  exact (Finset.mem_sdiff.mp (hmem 0)).2 hv

end Lax56Proofs.ValtrSplice
