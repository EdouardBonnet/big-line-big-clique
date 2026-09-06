import Lax56Proofs.ValtrRuns

namespace Lax56Proofs.ValtrCyclicRuns

open Lax56Proofs.ValtrRuns
open scoped Fin.NatCast

variable {α : Type*} [DecidableEq α] {n : ℕ} [NeZero n]

/-- The geometric input from Valtr's run lemma, kept explicit. -/
def CyclicRunBounds (U : Fin n → Finset α) (defined : Fin n → Prop) : Prop :=
  ∀ (start : Fin n) (t : ℕ), 0 < t → t < n →
    (∀ k < t, defined (start + (↑k : Fin n))) →
    ((Finset.range t).biUnion (fun k ↦ U (start + (↑k : Fin n)))).card ≤ t + 1

theorem shifted_interval_eq (U : Fin n → Finset α) (start : Fin n) {a b : ℕ}
    (hab : a ≤ b) :
    (Finset.Ico a b).biUnion (fun k ↦ U (start + (↑k : Fin n))) =
      (Finset.range (b - a)).biUnion (fun k ↦ U ((start + (↑a : Fin n)) + (↑k : Fin n))) := by
  ext p
  constructor
  · intro hp
    obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hak, hkb⟩ := Finset.mem_Ico.mp hk
    refine Finset.mem_biUnion.mpr ⟨k - a, Finset.mem_range.mpr (by omega), ?_⟩
    have hindex : (start + (↑a : Fin n)) + (↑(k - a) : Fin n) = start + (↑k : Fin n) := by
      rw [add_assoc, ← Nat.cast_add, Nat.add_sub_of_le hak]
    rwa [hindex]
  · intro hp
    obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
    have hk := Finset.mem_range.mp hk
    refine Finset.mem_biUnion.mpr ⟨a + k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa only [Nat.cast_add, add_assoc] using hp

/-- Cutting the finite cycle at a missing sector contradicts the strict
outer/inner cardinality inequality. -/
theorem all_defined_of_cyclic_run_bounds {A : Finset α}
    (U : Fin n → Finset α) (defined : Fin n → Prop)
    (hcover : ∀ p ∈ A, ∃ i, p ∈ U i)
    (hempty : ∀ i, ¬defined i → U i = ∅)
    (hlarge : n < A.card) (hrun : CyclicRunBounds U defined) : ∀ i, defined i := by
  classical
  intro gap
  by_contra hgap
  let V : ℕ → Finset α := fun k ↦ U (gap + (↑k : Fin n))
  let D : ℕ → Prop := fun k ↦ defined (gap + (↑k : Fin n))
  have hzero : ¬D 0 := by simpa only [D, Nat.cast_zero, add_zero] using hgap
  have hVempty : ∀ k, ¬D k → V k = ∅ := fun k hk ↦ hempty _ hk
  have hbound : ((Finset.range n).biUnion V).card ≤ n := by
    apply card_union_le_of_run_bounds_with_initial_gap V D hzero hVempty n
    intro a b hab hbn hD
    have hapos : 0 < a := by
      by_contra hh
      have ha : a = 0 := by omega
      subst a
      exact hzero (hD 0 (Finset.mem_Ico.mpr ⟨Nat.zero_le _, by omega⟩))
    have hD' : ∀ k < b - a, defined ((gap + (↑a : Fin n)) + (↑k : Fin n)) := by
      intro k hk
      have h := hD (a + k) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      simpa only [D, Nat.cast_add, add_assoc] using h
    have h := hrun (gap + (↑a : Fin n)) (b - a) (by omega) (by omega) hD'
    change ((Finset.Ico a b).biUnion (fun k ↦ U (gap + (↑k : Fin n)))).card ≤ b - a + 1
    rw [shifted_interval_eq U gap hab.le]
    exact h
  have hsub : A ⊆ (Finset.range n).biUnion V := by
    intro p hp
    obtain ⟨i, hi⟩ := hcover p hp
    let k := (i - gap).val
    have hkn : k < n := (i - gap).isLt
    have hkFin : (↑k : Fin n) = i - gap := Fin.natCast_eq_mk hkn
    have hindex : gap + (↑k : Fin n) = i := by rw [hkFin]; abel
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkn, ?_⟩
    dsimp only [V]
    rwa [hindex]
  have hcard := (Finset.card_le_card hsub).trans hbound
  omega

/-- All sectors except one form a cyclic run of length `n - 1`. -/
theorem cyclic_except_eq_run (U : Fin n → Finset α) (i : Fin n) :
    (Finset.univ.erase i).biUnion U =
      (Finset.range (n - 1)).biUnion (fun k ↦ U ((i + 1) + (↑k : Fin n))) := by
  have hindex_ne (k : ℕ) (hk : k < n - 1) : (i + 1) + (↑k : Fin n) ≠ i := by
    intro h
    have hz : (↑(1 + k) : Fin n) = 0 := by
      have h' : i + (1 + (↑k : Fin n)) = i + 0 := by simpa only [add_assoc, add_zero] using h
      simpa only [Nat.cast_add, Nat.cast_one] using (add_left_cancel h')
    have hlt : 1 + k < n := by omega
    rw [Fin.natCast_eq_mk hlt] at hz
    have hv := congrArg Fin.val hz
    simp only [Fin.val_zero] at hv
    omega
  ext p
  constructor
  · intro hp
    obtain ⟨j, hj, hp⟩ := Finset.mem_biUnion.mp hp
    have hji := (Finset.mem_erase.mp hj).1
    have hdpos : 0 < (j - i).val := by
      by_contra hh
      have heq : j - i = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
      exact hji (sub_eq_zero.mp heq)
    let k := (j - i).val - 1
    have hkn : k < n - 1 := by dsimp [k]; have := (j - i).isLt; omega
    have hindex : (i + 1) + (↑k : Fin n) = j := by
      have hk : 1 + k = (j - i).val := by dsimp [k]; omega
      calc
        (i + 1) + (↑k : Fin n) = i + (↑(1 + k) : Fin n) := by
          simp only [Nat.cast_add, Nat.cast_one, add_assoc]
        _ = i + (↑(j - i).val : Fin n) := by rw [hk]
        _ = i + (j - i) := by rw [Fin.natCast_eq_mk (j - i).isLt]
        _ = j := by abel
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkn, hindex.symm ▸ hp⟩
  · intro hp
    obtain ⟨k, hk, hp⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨(i + 1) + (↑k : Fin n),
      Finset.mem_erase.mpr ⟨hindex_ne k (Finset.mem_range.mp hk), Finset.mem_univ _⟩, hp⟩

/-- Once the geometric run bound is supplied, the finite counting forces
every sector to be defined, exactly one more outer point than sectors,
and a private outer point in each sector. -/
theorem all_defined_card_and_private {A : Finset α}
    (U : Fin n → Finset α) (defined : Fin n → Prop) (hn : 3 ≤ n)
    (hcover : ∀ p ∈ A, ∃ i, p ∈ U i)
    (hempty : ∀ i, ¬defined i → U i = ∅)
    (hlarge : n < A.card) (hrun : CyclicRunBounds U defined) :
    (∀ i, defined i) ∧ A.card = n + 1 ∧ ∀ i, (privateRegion A U i).Nonempty := by
  have hall := all_defined_of_cyclic_run_bounds U defined hcover hempty hlarge hrun
  have hsingle (i) : (U i).card ≤ 2 := by
    have h := hrun i 1 (by decide) (by omega) (fun k _ ↦ hall _)
    simpa only [Finset.range_one, Finset.singleton_biUnion, Nat.cast_zero, add_zero] using h
  have hothers (i) : ((Finset.univ.erase i).biUnion U).card ≤ n := by
    rw [cyclic_except_eq_run U i]
    have h := hrun (i + 1) (n - 1) (by omega) (by omega) (fun k _ ↦ hall _)
    omega
  exact ⟨hall, card_eq_succ_and_private_nonempty U hn hcover hsingle hothers hlarge⟩

end Lax56Proofs.ValtrCyclicRuns
