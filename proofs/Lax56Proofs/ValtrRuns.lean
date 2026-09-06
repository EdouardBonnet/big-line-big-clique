import Mathlib.Tactic

/-!
Finite counting in the last part of Valtr's four-layer argument. The sector
sets and their geometric run bounds are explicit inputs; no geometric
statement is assumed as an axiom here.
-/

namespace Lax56Proofs.ValtrRuns

open scoped BigOperators

variable {α : Type*} [DecidableEq α] {n : ℕ}

/-- Points of `A` not covered by any sector other than sector `i`. -/
def privateRegion (A : Finset α) (U : Fin n → Finset α) (i : Fin n) : Finset α :=
  A \ (Finset.univ.erase i).biUnion U

theorem privateRegion_subset {A : Finset α} {U : Fin n → Finset α}
    (hcover : ∀ p ∈ A, ∃ i, p ∈ U i) (i : Fin n) : privateRegion A U i ⊆ U i := by
  intro p hp
  obtain ⟨hpA, hpother⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨j, hj⟩ := hcover p hpA
  by_cases hji : j = i
  · simpa [hji] using hj
  · exact (hpother (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, hj⟩)).elim

theorem privateRegions_disjoint {A : Finset α} {U : Fin n → Finset α}
    (hcover : ∀ p ∈ A, ∃ i, p ∈ U i) {i j : Fin n} (hij : i ≠ j) :
    Disjoint (privateRegion A U i) (privateRegion A U j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hi
  apply (Finset.mem_sdiff.mp hi).2
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩, privateRegion_subset hcover i hp⟩

theorem card_le_private_add_others (A : Finset α) (U : Fin n → Finset α) (i : Fin n) :
    A.card ≤ (privateRegion A U i).card + ((Finset.univ.erase i).biUnion U).card := by
  have hsub : A ⊆ privateRegion A U i ∪ (Finset.univ.erase i).biUnion U := by
    intro p hp
    by_cases h : p ∈ (Finset.univ.erase i).biUnion U
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp, h⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Valtr's all-sectors case: the run bounds force exactly one more outer
point than sectors, and every sector has a private outer point. The
apparently possible excess of two is excluded by disjoint private regions. -/
theorem card_eq_succ_and_private_nonempty [NeZero n] {A : Finset α}
    (U : Fin n → Finset α) (hn : 3 ≤ n)
    (hcover : ∀ p ∈ A, ∃ i, p ∈ U i)
    (hsingle : ∀ i, (U i).card ≤ 2)
    (hothers : ∀ i, ((Finset.univ.erase i).biUnion U).card ≤ n)
    (hlarge : n < A.card) :
    A.card = n + 1 ∧ ∀ i, (privateRegion A U i).Nonempty := by
  have hupper : A.card ≤ n + 2 := by
    have h := card_le_private_add_others A U 0
    have hprivate := (Finset.card_le_card (privateRegion_subset hcover 0)).trans (hsingle 0)
    have ho := hothers 0
    omega
  have hnot : A.card ≠ n + 2 := by
    intro heq
    have htwo (i) : 2 ≤ (privateRegion A U i).card := by
      have h := card_le_private_add_others A U i
      have ho := hothers i
      omega
    have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (privateRegion A U) := by
      intro i _ j _ hij
      exact privateRegions_disjoint hcover hij
    have hsub : Finset.univ.biUnion (privateRegion A U) ⊆ A := by
      intro p hp
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      exact (Finset.mem_sdiff.mp hi).1
    have hsum : 2 * n ≤ ∑ i : Fin n, (privateRegion A U i).card := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ htwo i)
      simpa [mul_comm] using h
    have hbound := Finset.card_le_card hsub
    rw [Finset.card_biUnion hdisj] at hbound
    omega
  have heq : A.card = n + 1 := by omega
  refine ⟨heq, ?_⟩
  intro i
  apply Finset.card_pos.mp
  have h := card_le_private_add_others A U i
  have ho := hothers i
  omega

/-- Choosing one point from each private region leaves exactly one extra
point in the all-sectors case. The chosen points are automatically distinct. -/
theorem exists_private_representatives_and_extra {A : Finset α}
    (U : Fin n → Finset α) (hcover : ∀ p ∈ A, ∃ i, p ∈ U i)
    (hcard : A.card = n + 1) (hprivate : ∀ i, (privateRegion A U i).Nonempty) :
    ∃ a : Fin n → α, Function.Injective a ∧
      (∀ i, a i ∈ privateRegion A U i) ∧
      ∃ p ∈ A, p ∉ Finset.univ.image a ∧ A = insert p (Finset.univ.image a) := by
  classical
  choose a ha using hprivate
  have hinj : Function.Injective a := by
    intro i j heq
    by_contra hij
    have hd := Finset.disjoint_left.mp (privateRegions_disjoint hcover hij)
    exact hd (ha i) (heq ▸ ha j)
  have hsub : Finset.univ.image a ⊆ A := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_sdiff.mp (ha i)).1
  have hc : (Finset.univ.image a).card = n := by
    simp [Finset.card_image_of_injective _ hinj]
  have hd : (A \ Finset.univ.image a).card = 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hd
  have hpA : p ∈ A \ Finset.univ.image a := by rw [hp]; simp
  refine ⟨a, hinj, ha, p, (Finset.mem_sdiff.mp hpA).1,
    (Finset.mem_sdiff.mp hpA).2, ?_⟩
  have heq := Finset.sdiff_union_of_subset hsub
  rw [hp] at heq
  simpa using heq.symm

/-- Cutting a cyclic sector family at a missing sector leaves disjoint
linear runs. If a defined run of length `t` covers at most `t + 1` points,
the entire cut family covers at most `n` points. The proof cuts at the last
missing sector and uses strong induction; no enumeration of all partitions
into runs is needed. -/
theorem card_union_le_of_run_bounds_with_initial_gap
    (U : ℕ → Finset α) (defined : ℕ → Prop)
    (hzero : ¬defined 0) (hempty : ∀ i, ¬defined i → U i = ∅)
    (n : ℕ)
    (hrun : ∀ a b, a < b → b ≤ n →
      (∀ i ∈ Finset.Ico a b, defined i) →
      ((Finset.Ico a b).biUnion U).card ≤ b - a + 1) :
    ((Finset.range n).biUnion U).card ≤ n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; simp
    let bad := (Finset.range n).filter (fun i ↦ ¬defined i)
    have hbad : bad.Nonempty :=
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hzero⟩⟩
    obtain ⟨j, hj, hmax⟩ := bad.exists_max_image id hbad
    have hjn : j < n := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    have hjbad : ¬defined j := (Finset.mem_filter.mp hj).2
    have hprefix : ((Finset.range j).biUnion U).card ≤ j := by
      apply ih j hjn
      intro a b hab hbj hD
      exact hrun a b hab (by omega) hD
    have hsuffix : ((Finset.Ico (j + 1) n).biUnion U).card ≤ n - j := by
      by_cases hjlast : j + 1 = n
      · rw [hjlast]
        simp
      · have hD : ∀ i ∈ Finset.Ico (j + 1) n, defined i := by
          intro i hi
          by_contra hdi
          obtain ⟨hji, hin⟩ := Finset.mem_Ico.mp hi
          have hm := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hin, hdi⟩)
          dsimp only [id] at hm
          omega
        have h := hrun (j + 1) n (by omega) le_rfl hD
        omega
    have hcover : (Finset.range n).biUnion U ⊆
        (Finset.range j).biUnion U ∪ (Finset.Ico (j + 1) n).biUnion U := by
      intro p hp
      obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
      have hin := Finset.mem_range.mp hi
      rcases lt_trichotomy i j with hij | hij | hij
      · exact Finset.mem_union_left _
          (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hij, hp⟩)
      · subst i
        rw [hempty j hjbad] at hp
        exact (Finset.notMem_empty p hp).elim
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨i, Finset.mem_Ico.mpr ⟨by omega, hin⟩, hp⟩)
    have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    omega

end Lax56Proofs.ValtrRuns
