import Mathlib.Tactic

namespace Lax56Proofs.ValtrMaximum

/-- A forward ascent carrying an increasing outer value cannot terminate
at the common endpoint. Only existence of a larger neighbor is needed,
and the local conditions may start at an arbitrary positive index. -/
theorem scalar_no_forward_ascent_state (z a : ℕ → ℝ) {s m : ℕ}
    (hlast : z (m + 1) = a (m + 1) ∨ z (m + 1) < z m)
    (hlarge : ∀ k, s ≤ k → k ≤ m →
      z k < z (k - 1) ∨ z k < a k ∨ z k < a (k + 1) ∨ z k < z (k + 1))
    (ha_ne : ∀ k, s ≤ k → k ≤ m → z k ≠ a (k + 1))
    (hforbid : ∀ k, s ≤ k → k ≤ m → ¬(a k < z k ∧ z k < a (k + 1)))
    (k : ℕ) (hk : s ≤ k) (hkm : k ≤ m) :
    ¬(z (k - 1) < z k ∧ a k < z k) := by
  classical
  intro hstate
  let bad := (Finset.Icc s m).filter (fun j ↦ z (j - 1) < z j ∧ a j < z j)
  have hbad : bad.Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hkm⟩, hstate⟩⟩
  obtain ⟨j, hj, hmax⟩ := bad.exists_max_image id hbad
  obtain ⟨hjI, hprev, ha⟩ := Finset.mem_filter.mp hj
  obtain ⟨hjs, hjm⟩ := Finset.mem_Icc.mp hjI
  have hanext : a (j + 1) < z j := by
    have hn : ¬z j < a (j + 1) := fun h ↦ hforbid j hjs hjm ⟨ha, h⟩
    exact lt_of_le_of_ne (le_of_not_gt hn) (ha_ne j hjs hjm).symm
  have hnext : z j < z (j + 1) := by
    rcases hlarge j hjs hjm with h | h | h | h <;> linarith
  have hjlt : j < m := by
    by_contra hh
    have heq : j = m := by omega
    subst j
    rcases hlast with hlast | hlast
    · rw [hlast] at hnext; linarith
    · linarith
  have hjnext : j + 1 ∈ bad := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_, hanext.trans hnext⟩
    simpa only [Nat.add_sub_cancel] using hnext
  have hh := hmax (j + 1) hjnext
  dsimp only [id] at hh
  omega

/-- The backward counterpart: a local minimum carrying a larger outer
value propagates to the common first endpoint. -/
theorem scalar_no_backward_ascent_state (z a : ℕ → ℝ) {m : ℕ}
    (hfirst : z 0 = a 1 ∨ z 1 < z 0)
    (hsmall : ∀ k, 1 ≤ k → k ≤ m →
      z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k)
    (ha_ne : ∀ k, 1 ≤ k → k ≤ m → z k ≠ a k)
    (hforbid : ∀ k, 1 ≤ k → k ≤ m → ¬(a k < z k ∧ z k < a (k + 1)))
    (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) :
    ¬(z k < z (k + 1) ∧ z k < a (k + 1)) := by
  classical
  intro hstate
  let bad := (Finset.Icc 1 m).filter (fun j ↦ z j < z (j + 1) ∧ z j < a (j + 1))
  have hbad : bad.Nonempty :=
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hkm⟩, hstate⟩⟩
  obtain ⟨j, hj, hmin⟩ := bad.exists_min_image id hbad
  obtain ⟨hjI, hnext, ha⟩ := Finset.mem_filter.mp hj
  obtain ⟨hjpos, hjm⟩ := Finset.mem_Icc.mp hjI
  have haprev : z j < a j := by
    have hn : ¬a j < z j := fun h ↦ hforbid j hjpos hjm ⟨h, ha⟩
    exact lt_of_le_of_ne (le_of_not_gt hn) (ha_ne j hjpos hjm)
  have hprev : z (j - 1) < z j := by
    rcases hsmall j hjpos hjm with h | h | h | h <;> linarith
  have hjlt : 1 < j := by
    by_contra hh
    have heq : j = 1 := by omega
    subst j
    norm_num at hprev
    rcases hfirst with hfirst | hfirst
    · rw [hfirst] at hprev; linarith
    · linarith
  have hjprev : j - 1 ∈ bad := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]
    exact ⟨hprev, hprev.trans haprev⟩
  have hh := hmin (j - 1) hjprev
  dsimp only [id] at hh
  omega

/-- The scalar propagation principle supplied in the informal
chain-replacement proof. Local strict betweenness is expressed by
existence of a smaller and a larger neighbor, avoiding a choice of
parenthesization for four-way minima and maxima. -/
theorem scalar_chain_strictly_decreasing_of_endpoint_conditions
    (z a : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    (hlast : z (m + 1) = a (m + 1) ∨ z (m + 1) < z m)
    (hsmall : ∀ k, 1 ≤ k → k ≤ m →
      z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k)
    (hlarge : ∀ k, 1 ≤ k → k ≤ m →
      z k < z (k - 1) ∨ z k < a k ∨ z k < a (k + 1) ∨ z k < z (k + 1))
    (hnext_ne : ∀ k, k ≤ m → z k ≠ z (k + 1))
    (ha_ne : ∀ k, 1 ≤ k → k ≤ m → z k ≠ a k ∧ z k ≠ a (k + 1))
    (hforbid : ∀ k, 1 ≤ k → k ≤ m → ¬(a k < z k ∧ z k < a (k + 1)))
    (hfirst : z 0 = a 1 ∨ z 1 < z 0) :
    ∀ k, k ≤ m → z (k + 1) < z k := by
  classical
  have hnostate : ∀ k, 1 ≤ k → k ≤ m → ¬(z (k - 1) < z k ∧ a k < z k) := by
    exact scalar_no_forward_ascent_state z a hlast hlarge
      (fun k hk hkm ↦ (ha_ne k hk hkm).2) hforbid
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    by_contra hdesc
    have hasc : z r < z (r + 1) :=
      lt_of_le_of_ne (le_of_not_gt hdesc) (hnext_ne r hr)
    by_cases hrzero : r = 0
    · subst r
      have hstart : z 0 = a 1 := hfirst.resolve_right (by linarith)
      apply hnostate 1 (by decide) (by omega)
      constructor
      · simpa using hasc
      · rwa [← hstart]
    have hprev : z r < z (r - 1) := by
      have h := ih (r - 1) (by omega) (by omega)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ r)] using h
    have har : a (r + 1) < z r := by
      by_contra hh
      have hright : z r < a (r + 1) :=
        lt_of_le_of_ne (le_of_not_gt hh) (ha_ne r (by omega) hr).2
      have hleft : z r < a r := by
        have hn : ¬a r < z r := fun h ↦ hforbid r (by omega) hr ⟨h, hright⟩
        exact lt_of_le_of_ne (le_of_not_gt hn) (ha_ne r (by omega) hr).1
      rcases hsmall r (by omega) hr with h | h | h | h <;> linarith
    have hrlt : r < m := by
      by_contra hh
      have heq : r = m := by omega
      subst r
      rcases hlast with hlast | hlast
      · rw [hlast] at hasc; linarith
      · linarith
    apply hnostate (r + 1) (by omega) (by omega)
    exact ⟨by simpa only [Nat.add_sub_cancel] using hasc, har.trans hasc⟩

/-- The endpoint-equality version stated in the supplied informal proof. -/
theorem scalar_chain_strictly_decreasing (z a : ℕ → ℝ) {m : ℕ} (hm : 0 < m)
    (hlast : z (m + 1) = a (m + 1))
    (hsmall : ∀ k, 1 ≤ k → k ≤ m →
      z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k)
    (hlarge : ∀ k, 1 ≤ k → k ≤ m →
      z k < z (k - 1) ∨ z k < a k ∨ z k < a (k + 1) ∨ z k < z (k + 1))
    (hnext_ne : ∀ k, k ≤ m → z k ≠ z (k + 1))
    (ha_ne : ∀ k, 1 ≤ k → k ≤ m → z k ≠ a k ∧ z k ≠ a (k + 1))
    (hforbid : ∀ k, 1 ≤ k → k ≤ m → ¬(a k < z k ∧ z k < a (k + 1)))
    (hfirst : z 0 = a 1 ∨ z 1 < z 0) :
    ∀ k, k ≤ m → z (k + 1) < z k :=
  scalar_chain_strictly_decreasing_of_endpoint_conditions z a hm (Or.inl hlast)
    hsmall hlarge hnext_ne ha_ne hforbid hfirst

end Lax56Proofs.ValtrMaximum
