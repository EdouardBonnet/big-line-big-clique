import Lax56Proofs.ValtrRunInduction

namespace Lax56Proofs.ValtrExtremalRun

open scoped Classical

variable {α : Type*} [DecidableEq α]

theorem split_union (U : ℕ → Finset α) {t k : ℕ} (hk : k ≤ t) :
    ((Finset.range k).biUnion U) ∪ ((Finset.Ico k t).biUnion U) = (Finset.range t).biUnion U := by
  ext p
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro (⟨i, hi, hp⟩ | ⟨i, hi, hp⟩)
    · exact ⟨i, by omega, hp⟩
    · exact ⟨i, hi.2, hp⟩
  · rintro ⟨i, hi, hp⟩
    by_cases hik : i < k
    · exact Or.inl ⟨i, hik, hp⟩
    · exact Or.inr ⟨i, ⟨by omega, hi⟩, hp⟩

/-- At a saturated split, both shorter bounds are sharp and their
point sets are disjoint. -/
theorem saturated_split (U : ℕ → Finset α) {t k : ℕ} (hk : k ≤ t)
    (hcard : ((Finset.range t).biUnion U).card = t + 2)
    (hleft : ((Finset.range k).biUnion U).card ≤ k + 1)
    (hright : ((Finset.Ico k t).biUnion U).card ≤ t - k + 1) :
    ((Finset.range k).biUnion U).card = k + 1 ∧
    ((Finset.Ico k t).biUnion U).card = t - k + 1 ∧
    Disjoint ((Finset.range k).biUnion U) ((Finset.Ico k t).biUnion U) := by
  have hid := Finset.card_union_add_card_inter ((Finset.range k).biUnion U) ((Finset.Ico k t).biUnion U)
  rw [split_union U hk, hcard] at hid
  have hzero : (((Finset.range k).biUnion U) ∩ ((Finset.Ico k t).biUnion U)).card = 0 := by omega
  exact ⟨by omega, by omega, Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hzero)⟩

/-- A minimal run violating the `length + 1` bound has no overlaps
between any of its sector point sets. -/
theorem sectors_pairwise_disjoint (U : ℕ → Finset α) {t : ℕ}
    (hcard : ((Finset.range t).biUnion U).card = t + 2)
    (hleft : ∀ k, 1 ≤ k → k < t → ((Finset.range k).biUnion U).card ≤ k + 1)
    (hright : ∀ k, 1 ≤ k → k < t → ((Finset.Ico k t).biUnion U).card ≤ t - k + 1) :
    ∀ i j, i < t → j < t → i ≠ j → Disjoint (U i) (U j) := by
  have hordered (i j) (hij : i < j) (hjt : j < t) : Disjoint (U i) (U j) := by
    have hs := (saturated_split U (by omega : j ≤ t) hcard
      (hleft j (by omega) hjt) (hright j (by omega) hjt)).2.2
    apply hs.mono
    · intro p hp; exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij, hp⟩
    · intro p hp; exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Ico.mpr ⟨le_rfl, hjt⟩, hp⟩
  intro i j hit hjt hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact hordered i j hij hjt
  · exact (hordered j i hji hit).symm

theorem sector_card_pattern (U : ℕ → Finset α) {t : ℕ} (ht : 2 ≤ t)
    (hcard : ((Finset.range t).biUnion U).card = t + 2)
    (hleft : ∀ k, 1 ≤ k → k < t → ((Finset.range k).biUnion U).card ≤ k + 1)
    (hright : ∀ k, 1 ≤ k → k < t → ((Finset.Ico k t).biUnion U).card ≤ t - k + 1) :
    (U 0).card = 2 ∧ (U (t - 1)).card = 2 ∧
    ∀ i, 1 ≤ i → i < t - 1 → (U i).card = 1 := by
  have hprefix (k) (hk : 1 ≤ k) (hkt : k < t) : ((Finset.range k).biUnion U).card = k + 1 :=
    (saturated_split U (by omega) hcard (hleft k hk hkt) (hright k hk hkt)).1
  have hdisj := sectors_pairwise_disjoint U hcard hleft hright
  refine ⟨?_, ?_, ?_⟩
  · simpa using hprefix 1 (by decide) (by omega)
  · have hh := (saturated_split U (by omega : t - 1 ≤ t) hcard
      (hleft (t - 1) (by omega) (by omega)) (hright (t - 1) (by omega) (by omega))).2.1
    have heq : Finset.Ico (t - 1) t = {t - 1} := by
      ext i; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [heq] at hh
    simpa [show t - (t - 1) + 1 = 2 by omega] using hh
  · intro i hi hit
    have hP := hprefix i hi (by omega)
    have hQ := hprefix (i + 1) (by omega) (by omega)
    have hd : Disjoint (U i) ((Finset.range i).biUnion U) := by
      apply Finset.disjoint_left.mpr
      intro p hp hpU
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hpU
      exact Finset.disjoint_left.mp (hdisj i j (by omega) (by have := Finset.mem_range.mp hj; omega)
        (by have := Finset.mem_range.mp hj; omega)) hp hpj
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.card_union_of_disjoint hd] at hQ
    omega

end Lax56Proofs.ValtrExtremalRun

namespace Lax56Proofs.ValtrExtremalRun

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrRunSetup
open Lax56Proofs.ValtrCyclicRuns Lax56Proofs.ValtrRunReduction
open Lax56Proofs.ValtrEndpointDrop Lax56Proofs.ValtrRunInduction
open scoped Classical Fin.NatCast

/-- It is enough to exclude a both-convex run whose sector point sets
are disjoint and have the exact pattern two, one, ..., one, two. -/
def ExtremalRunObstruction (S : Finset Point) {n : ℕ} [NeZero n]
    (v c : Fin n → Point) (d : Point) : Prop :=
  ∀ (start : Fin n) (t : ℕ), 2 ≤ t → t < n →
    (∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k)) →
    ¬StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1) →
    ¬StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t) →
    let U := fun k ↦ sectorPoints S v c d (cyclicIndex start k)
    (∀ i j, i < t → j < t → i ≠ j → Disjoint (U i) (U j)) →
    (U 0).card = 2 → (U (t - 1)).card = 2 →
    (∀ i, 1 ≤ i → i < t - 1 → (U i).card = 1) → False

/-- Strong induction reduces the geometric run bound to the exact
extremal count pattern. All smaller runs are used to prove disjointness. -/
theorem run_bound_of_extremal_run_obstruction {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S) (hmin : MinimalOuter S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (hdoubly : ExtremalRunObstruction S v c d) :
    CyclicRunBounds (sectorPoints S v c d) (MeetsThirdLayer S v d) := by
  let U := sectorPoints S v c d
  intro start t
  induction t using Nat.strong_induction_on generalizing start with
  | h t ih =>
    intro ht htn hdefined
    change (runUnion U start t).card ≤ t + 1
    have hsingle (k) (hk : k < t) : (U (cyclicIndex start k)).card ≤ 2 := by
      have hd' : MeetsThirdLayer S v d (cyclicIndex start k) := hdefined k hk
      simpa only [U, sectorPoints, if_pos hd'] using (hdata _ hd').outer_card
    by_cases ht1 : t = 1
    · subst t
      simpa [runUnion, cyclicIndex] using hsingle 0 (by decide)
    have ht2 : 2 ≤ t := by omega
    have hprefix : (runUnion U start (t - 1)).card ≤ t := by
      have hh := ih (t - 1) (by omega) start (by omega) (by omega)
        (fun k hk ↦ hdefined k (by omega))
      change (runUnion U start (t - 1)).card ≤ t - 1 + 1 at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hh
    have htail : (runUnion U (start + 1) (t - 1)).card ≤ t := by
      have hD : ∀ k < t - 1, MeetsThirdLayer S v d ((start + 1) + (↑k : Fin n)) := by
        intro k hk
        have hh := hdefined (k + 1) (by omega)
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hh
      have hh := ih (t - 1) (by omega) (start + 1) (by omega) (by omega) hD
      change (runUnion U (start + 1) (t - 1)).card ≤ t - 1 + 1 at hh
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ t)] using hh
    have hupper : (runUnion U start t).card ≤ t + 2 := by
      have hsub : runUnion U start t ⊆
          runUnion U start (t - 1) ∪ U (cyclicIndex start (t - 1)) := by
        intro p hp
        obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
        have hkt := Finset.mem_range.mp hk
        by_cases hkp : k < t - 1
        · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkp, hp⟩)
        · have heq : k = t - 1 := by omega
          exact Finset.mem_union_right _ (heq ▸ hp)
      have hh := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hs := hsingle (t - 1) (by omega)
      omega
    by_cases hfirst : StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
        (runBase v start t 2) (runChain v c start t 1)
    · by_cases hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
          (runBase v start t (t + 1)) (runChain v c start t t)
      · exact (not_minimal_of_nonconvex_run_card_le hgen v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast hupper hmin).elim
      · have hdrop := last_drop_card_of_mixed_endpoints hgen hno v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast
        have hh := Finset.card_le_card_sdiff_add_card (s := runUnion U start t)
          (t := runUnion U (start + 1) (t - 1))
        change (runUnion U start t \ runUnion U (start + 1) (t - 1)).card ≤ 1 at hdrop
        omega
    · by_cases hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
          (runBase v start t (t + 1)) (runChain v c start t t)
      · have hdrop := first_drop_card_of_mixed_endpoints hgen hno v hinj hrange htri hd c hdata
          start ht2 htn hdefined hfirst hlast
        have hh := Finset.card_le_card_sdiff_add_card (s := runUnion U start t)
          (t := runUnion U start (t - 1))
        change (runUnion U start t \ runUnion U start (t - 1)).card ≤ 1 at hdrop
        omega
      · by_contra hfail
        have hcard : (runUnion U start t).card = t + 2 := by omega
        let V : ℕ → Finset Point := fun k ↦ U (cyclicIndex start k)
        have hleft (k) (hk : 1 ≤ k) (hkt : k < t) :
            ((Finset.range k).biUnion V).card ≤ k + 1 := by
          exact ih k hkt start (by omega) (by omega) (fun j hj ↦ hdefined j (by omega))
        have hright (k) (hk : 1 ≤ k) (hkt : k < t) :
            ((Finset.Ico k t).biUnion V).card ≤ t - k + 1 := by
          change ((Finset.Ico k t).biUnion (fun j ↦ U (start + (↑j : Fin n)))).card ≤ t - k + 1
          rw [shifted_interval_eq U start (by omega : k ≤ t)]
          apply ih (t - k) (by omega) (start + (↑k : Fin n)) (by omega) (by omega)
          intro j hj
          have hh := hdefined (k + j) (by omega)
          simpa only [cyclicIndex, Nat.cast_add, add_assoc] using hh
        change ((Finset.range t).biUnion V).card = t + 2 at hcard
        have hdisj := Lax56Proofs.ValtrExtremalRun.sectors_pairwise_disjoint V hcard hleft hright
        obtain ⟨hzero, hlastCard, hmiddle⟩ :=
          Lax56Proofs.ValtrExtremalRun.sector_card_pattern V ht2 hcard hleft hright
        exact hdoubly start t ht2 htn hdefined hfirst hlast hdisj hzero hlastCard hmiddle

/-- The structured both-convex obstruction is sufficient for the
four-layer theorem with outer threshold sixteen. -/
theorem four_layer_of_extremal_run_obstruction {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hmin : MinimalOuter S)
    (hlarge : 16 ≤ (extremeLayer S).card) (hfourth : (layer S 3).Nonempty)
    (hdoubly : ¬HasEmptyHexagon S → ∀ {n : ℕ} [NeZero n], 3 ≤ n → ∀ v : Fin n → Point,
      Function.Injective v → Set.range v = (extremeLayer (inner S) : Set Point) →
      (∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) →
      ∀ d ∈ layer S 3, ∀ c : Fin n → Point,
        (∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i)) → ExtremalRunObstruction S v c d) :
    HasEmptyHexagon S := by
  by_contra hno
  apply hno
  apply Lax56Proofs.ValtrFourLayerReduction.four_layer_of_run_bound hgen hmin hlarge hfourth
  intro n inst hn v hinj hrange htri d hd c hdata
  exact run_bound_of_extremal_run_obstruction hgen hno hmin v hinj hrange htri
    (extremeLayer_subset _ hd) c hdata (hdoubly hno hn v hinj hrange htri d hd c hdata)

end Lax56Proofs.ValtrExtremalRun
