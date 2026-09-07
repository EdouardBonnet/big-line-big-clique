import Lax56Proofs.ValtrSectorArcs

namespace Lax56Proofs.ValtrPrivateRuns

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrCoverSetup
open Lax56Proofs.ValtrRuns Lax56Proofs.ValtrRunSetup Lax56Proofs.ValtrRunReduction
open Lax56Proofs.ValtrPolygon Lax56Proofs.ValtrSectorArcs
open scoped Classical Fin.NatCast

/-- Among three disjoint five-element index blocks, at least one avoids
a forbidden set of at most two indices. -/
theorem exists_clean_five_block {n : ℕ} (hn : 15 ≤ n) (F : Finset (Fin n))
    (hF : F.card ≤ 2) :
    ∃ a, ∃ ha : a + 5 ≤ n, ∀ i : Fin 5, offsetIndex a ha i ∉ F := by
  have ha0 : 0 + 5 ≤ n := by omega
  have ha5 : 5 + 5 ≤ n := by omega
  have ha10 : 10 + 5 ≤ n := by omega
  by_cases h0 : ∀ i : Fin 5, offsetIndex 0 ha0 i ∉ F
  · exact ⟨0, ha0, h0⟩
  by_cases h5 : ∀ i : Fin 5, offsetIndex 5 ha5 i ∉ F
  · exact ⟨5, ha5, h5⟩
  by_cases h10 : ∀ i : Fin 5, offsetIndex 10 ha10 i ∉ F
  · exact ⟨10, ha10, h10⟩
  push Not at h0 h5 h10
  obtain ⟨i, hi⟩ := h0
  obtain ⟨j, hj⟩ := h5
  obtain ⟨k, hk⟩ := h10
  have hne (a b) (ha : a + 5 ≤ n) (hb : b + 5 ≤ n) (hab : a + 5 ≤ b)
      (r s : Fin 5) : offsetIndex a ha r ≠ offsetIndex b hb s := by
    intro heq
    have hh := congrArg Fin.val heq
    change a + r.val = b + s.val at hh
    omega
  exact (not_lt_of_ge hF (Finset.two_lt_card.mpr
    ⟨_, hi, _, hj, _, hk, hne 0 5 ha0 ha5 (by decide) i j,
      hne 0 10 ha0 ha10 (by decide) i k, hne 5 10 ha5 ha10 (by decide) j k⟩)).elim

/-- In a family with one private representative per index and one extra
point, any collection of sectors avoiding the extra point has at most as
many points as indices. -/
theorem private_union_card_le {α : Type*} [DecidableEq α] {n : ℕ}
    {A : Finset α} (U : Fin n → Finset α) (hU : ∀ i, U i ⊆ A)
    (u : Fin n → α) (hu : ∀ i, u i ∈ privateRegion A U i) {x : α}
    (hA : A = insert x (Finset.univ.image u)) (J : Finset (Fin n))
    (hout : ∀ i ∈ J, x ∉ U i) : (J.biUnion U).card ≤ J.card := by
  have hsub : J.biUnion U ⊆ J.image u := by
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    have hpA := hU i hp
    rw [hA] at hpA
    rcases Finset.mem_insert.mp hpA with heq | hpA
    · exact (hout i hi (heq ▸ hp)).elim
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hpA
    have hji : j = i := by
      by_contra hji
      apply (Finset.mem_sdiff.mp (hu j)).2
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_erase.mpr ⟨Ne.symm hji, Finset.mem_univ _⟩, hp⟩
    exact Finset.mem_image.mpr ⟨i, hi, congrArg u hji.symm⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le)

/-- The private-region geometry needed in the final argument, with a
deliberately weaker size threshold. Three disjoint five-sector runs are
enough, since the unique extra outer point belongs to at most two sectors. -/
theorem exists_five_run_card_le {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (hn : 15 ≤ n) (v : Fin n → Point)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (c : Fin n → Point) (d : Point) (hdata : ∀ i, ApexData S v d i (c i))
    (hcover : ∀ q ∈ extremeLayer S, ∃ i, q ∈ sectorPoints S v c d i)
    (hcard : (extremeLayer S).card = n + 1)
    (hprivate : ∀ i, (privateRegion (extremeLayer S) (sectorPoints S v c d) i).Nonempty) :
    ∃ a, ∃ ha : a + 5 ≤ n, ((Finset.range 5).biUnion (fun k ↦
      sectorPoints S v c d (cyclicIndex (⟨a, by omega⟩ : Fin n) k))).card ≤ 5 := by
  let U := sectorPoints S v c d
  have hU (i) : U i ⊆ extremeLayer S := fun p hp ↦ (mem_sectorPoints_iff.mp hp).2.1
  obtain ⟨u, huinj, hu, x, hx, hxnot, hA⟩ :=
    exists_private_representatives_and_extra U hcover hcard hprivate
  have hv (i) : v i ∈ inner S := by
    apply extremeLayer_subset
    change v i ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have huA (i) : u i ∈ extremeLayer S := (Finset.mem_sdiff.mp (hu i)).1
  have hux (i) : u i ≠ x := fun hh ↦ hxnot
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hh⟩)
  have huS (i) : u i ∈ sector ![v (i + 1), c i, v i] :=
    (mem_sectorPoints_iff.mp (privateRegion_subset hcover i (hu i))).2.2
  let F := Finset.univ.filter (fun i ↦ x ∈ sector ![v (i + 1), c i, v i])
  have hF : F.card ≤ 2 := sector_multiplicity_le_two hgen (by omega)
    (fun i ↦ v (i + 1)) c v u hx (fun i ↦ hv (i + 1))
    (fun i ↦ inner_subset _ (extremeLayer_subset _ (hdata i).mem_third)) hv
    (fun i ↦ (hdata i).oriented) huA huinj hux huS (fun i ↦ (hdata i).outer_card)
  obtain ⟨a, ha, hclean⟩ := exists_clean_five_block hn F hF
  let J : Finset (Fin n) := Finset.univ.image (offsetIndex a ha : Fin 5 → Fin n)
  have hout : ∀ i ∈ J, x ∉ U i := by
    intro i hi hxU
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    apply hclean j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (mem_sectorPoints_iff.mp hxU).2.2⟩
  have hJ : J.card ≤ 5 := by
    calc
      J.card ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
      _ = 5 := by decide
  have hbound : (J.biUnion U).card ≤ 5 :=
    (private_union_card_le U hU u hu hA J hout).trans hJ
  refine ⟨a, ha, ?_⟩
  have heq : (Finset.range 5).biUnion (fun k ↦ U (cyclicIndex (⟨a, by omega⟩ : Fin n) k)) =
      J.biUnion U := by
    ext p
    constructor
    · intro hp
      obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
      let i : Fin 5 := ⟨k, Finset.mem_range.mp hk⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨offsetIndex a ha i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
      simpa only [Lax56Proofs.ValtrShortSetup.offsetIndex_eq_cyclicIndex] using hp
    · intro hp
      obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_biUnion.mpr
      refine ⟨i.val, Finset.mem_range.mpr i.isLt, ?_⟩
      simpa only [Lax56Proofs.ValtrShortSetup.offsetIndex_eq_cyclicIndex] using hp
  rw [← heq] at hbound
  exact hbound

/-- The all-sectors endgame, including the private-region geometry,
center matching, cap selection, and shortened-chain support. -/
theorem not_minimal_of_all_sectors {S : Finset Point}
    (hgen : ¬HasThreeCollinear S) (hno : ¬HasEmptyHexagon S)
    {n : ℕ} [NeZero n] (hn : 15 ≤ n) (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, ApexData S v d i (c i))
    (hfull : Finset.univ.image c = extremeLayer (inner (inner S)))
    (hall : ∀ e ∈ layer S 3, ∀ i, MeetsThirdLayer S v e i)
    (hcover : ∀ q ∈ extremeLayer S, ∃ i, q ∈ sectorPoints S v c d i)
    (hcard : (extremeLayer S).card = n + 1)
    (hprivate : ∀ i, (privateRegion (extremeLayer S) (sectorPoints S v c d) i).Nonempty) :
    ¬MinimalOuter S := by
  obtain ⟨a, ha, hrun⟩ := exists_five_run_card_le hgen hn v hrange c d hdata hcover hcard hprivate
  exact Lax56Proofs.ValtrShortSetup.not_minimal_of_five_run_card_le hgen hno (by omega)
    v hinj hrange htri hd c hdata hfull hall a ha hrun

end Lax56Proofs.ValtrPrivateRuns
