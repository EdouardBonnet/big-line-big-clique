import Lax56Proofs.ValtrSectors

namespace Lax56Proofs.ValtrCyclic

open Lax56.Geometry Lax56.ConvexLayers Lax56.HujterKisfaludiBak
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry Lax56Proofs.CyclicOrder
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrCaps Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSectors

theorem cyclic_next_val {n : ℕ} [NeZero n] (i : Fin n) :
    (i + 1).val = if i.val + 1 < n then i.val + 1 else 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [Fin.val_add_one]
  by_cases hi : i = Fin.last m
  · subst i; simp
  · have hlt : i.val + 1 < m.succ := by
      have hival : i.val ≠ m := fun h ↦ hi (Fin.ext h)
      omega
    simp only [if_neg hi, if_pos hlt]

theorem cyclic_next_cases {n : ℕ} [NeZero n] (i : Fin n) :
    (i.val + 1 = n ∧ (i + 1).val = 0) ∨
    (i.val + 1 < n ∧ (i + 1).val = i.val + 1) := by
  by_cases hi : i.val + 1 < n
  · exact Or.inr ⟨hi, by rw [cyclic_next_val, if_pos hi]⟩
  · exact Or.inl ⟨by omega, by rw [cyclic_next_val, if_neg hi]⟩

theorem cyclic_add_cases {n : ℕ} (i k : Fin n) :
    (i.val + k.val < n ∧ (i + k).val = i.val + k.val) ∨
    (n ≤ i.val + k.val ∧ (i + k).val = i.val + k.val - n) := by
  by_cases h : i.val + k.val < n
  · exact Or.inl ⟨h, by rw [Fin.val_add, Nat.mod_eq_of_lt h]⟩
  · have hn : n ≤ i.val + k.val := le_of_not_gt h
    refine Or.inr ⟨hn, ?_⟩
    rw [Fin.val_add, Nat.mod_eq_sub_mod hn, Nat.mod_eq_of_lt (by omega)]

/-- A change of the initial vertex preserves positive cyclic triples. -/
theorem cyclic_shift_triples {n : ℕ} {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (a : Fin n) : ∀ i j k, i < j → j < k →
      0 < turn (v (i + a)) (v (j + a)) (v (k + a)) := by
  intro i j k hij hjk
  have hi := cyclic_add_cases i a
  have hj := cyclic_add_cases j a
  have hk := cyclic_add_cases k a
  have hord : (i + a < j + a ∧ j + a < k + a) ∨
      (j + a < k + a ∧ k + a < i + a) ∨
      (k + a < i + a ∧ i + a < j + a) := by
    change ((i + a).val < (j + a).val ∧ (j + a).val < (k + a).val) ∨
      ((j + a).val < (k + a).val ∧ (k + a).val < (i + a).val) ∨
      ((k + a).val < (i + a).val ∧ (i + a).val < (j + a).val)
    rcases hi with hi | hi <;> rcases hj with hj | hj <;>
      rcases hk with hk | hk <;> omega
  rcases hord with ⟨hij, hjk⟩ | ⟨hjk, hki⟩ | ⟨hki, hij⟩
  · exact htri _ _ _ hij hjk
  · rw [← turn_rotate]
    exact htri _ _ _ hjk hki
  · rw [turn_rotate]
    exact htri _ _ _ hki hij

/-- Uniform positive triples give the supporting inequality on every
cyclic edge, including the edge from the last vertex back to the first. -/
theorem cyclic_edge_pos {n : ℕ} [NeZero n] {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (i j : Fin n) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    0 < turn (v i) (v (i + 1)) (v j) := by
  have hn := NeZero.pos n
  have hnext := cyclic_next_cases i
  have hzero : (0 : Fin n).val = 0 := Fin.val_zero n
  by_cases hi : i.val + 1 = n
  · have hi0 : i + 1 = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
    have hj0 : (0 : Fin n) < j := by rw [hi0] at hjnext; omega
    have hji' : j < i := by omega
    rw [hi0, ← turn_rotate (v i) (v 0) (v j)]
    exact htri 0 j i hj0 hji'
  · simpa only [one_mul] using turn_consecutive_pos v 1 (by simpa only [one_mul] using htri)
      i (i + 1) (by omega) j hji hjnext

theorem cyclic_edge_nonneg_of_mem_hull {n : ℕ} [NeZero n] {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {p : Point} (hp : p ∈ convexHull ℝ (Set.range v)) (i : Fin n) :
    0 ≤ turn (v i) (v (i + 1)) p := by
  apply turn_nonneg_of_mem_convexHull (A := Set.range v) _ hp
  rintro q ⟨j, rfl⟩
  by_cases hji : j = i
  · subst j; simp
  by_cases hjnext : j = i + 1
  · subst j; simp
  exact (cyclic_edge_pos htri i j hji hjnext).le

/-- A nonconstant predicate on a finite cycle has a true-to-false edge.
The proof is a finite extremum argument, not an enumeration certificate. -/
theorem exists_cyclic_transition {n : ℕ} [NeZero n] (A : Fin n → Prop)
    (hyes : ∃ i, A i) (hno : ∃ i, ¬A i) : ∃ i, A i ∧ ¬A (i + 1) := by
  classical
  have hn := NeZero.pos n
  by_cases hzero : A 0
  · let bad := Finset.univ.filter (fun i ↦ ¬A i)
    have hbad : bad.Nonempty := by
      obtain ⟨i, hi⟩ := hno
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨j, hj, hmin⟩ := bad.exists_min_image Fin.val hbad
    have hjno : ¬A j := (Finset.mem_filter.mp hj).2
    have hjpos : 0 < j.val := by
      by_contra h
      have hj0 : j = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
      exact hjno (hj0 ▸ hzero)
    let i : Fin n := ⟨j.val - 1, by omega⟩
    have hinext : i + 1 = j := by
      have h := cyclic_next_cases i
      apply Fin.ext
      dsimp [i] at h ⊢
      omega
    refine ⟨i, ?_, hinext ▸ hjno⟩
    by_contra hi
    have hm := hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    dsimp [i] at hm
    omega
  · let good := Finset.univ.filter A
    have hgood : good.Nonempty := by
      obtain ⟨i, hi⟩ := hyes
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨i, hi, hmax⟩ := good.exists_max_image Fin.val hgood
    refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
    intro hinext
    have hm := hmax (i + 1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinext⟩)
    have h := cyclic_next_cases i
    have hi0 : i + 1 = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
    exact hzero (hi0 ▸ hinext)

/-- The affine dependence of four planar points, evaluated by a line's
oriented-area functional. -/
theorem turn_affine_circuit (a b c d u w : Point) :
    turn b c d * turn u w a + turn a b d * turn u w c =
      turn a c d * turn u w b + turn a b c * turn u w d := by
  unfold turn
  ring

/-- Four cyclically ordered vertices of a strict convex polygon cannot
alternate between the two open half-planes of a line. -/
theorem not_alternating_line_sides {a b c d u w : Point}
    (habc : 0 < turn a b c) (habd : 0 < turn a b d)
    (hacd : 0 < turn a c d) (hbcd : 0 < turn b c d)
    (ha : 0 < turn u w a) (hb : turn u w b < 0)
    (hc : 0 < turn u w c) (hd : turn u w d < 0) : False := by
  have h := turn_affine_circuit a b c d u w
  have hleft : 0 < turn b c d * turn u w a + turn a b d * turn u w c :=
    add_pos (mul_pos hbcd ha) (mul_pos habd hc)
  have hright : turn a c d * turn u w b + turn a b c * turn u w d < 0 :=
    add_neg (mul_neg_of_pos_of_neg hacd hb) (mul_neg_of_pos_of_neg habc hd)
  linarith

private theorem cyclic_crossing_not_lt {n : ℕ} [NeZero n] {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {u w : Point} {i j : Fin n}
    (hi : 0 < turn u w (v i)) (hi' : turn u w (v (i + 1)) < 0)
    (hj : 0 < turn u w (v j)) (hj' : turn u w (v (j + 1)) < 0)
    (hij : i < j) : False := by
  have hni := cyclic_next_cases i
  have hnj := cyclic_next_cases j
  have hinext : i < i + 1 := by change i.val < (i + 1).val; omega
  have hnextj : i + 1 < j := by
    have hne : i + 1 ≠ j := by intro h; rw [h] at hi'; linarith
    change (i + 1).val < j.val
    have hnv : (i + 1).val ≠ j.val := fun h ↦ hne (Fin.ext h)
    omega
  by_cases hlast : j.val + 1 = n
  · have hj0 : j + 1 = 0 := by
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    have h0i : (0 : Fin n) < i := by
      have hi0 : i ≠ 0 := by intro h; rw [h] at hi; rw [hj0] at hj'; linarith
      have hz : (0 : Fin n).val = 0 := Fin.val_zero n
      have hv : i.val ≠ (0 : Fin n).val := fun h ↦ hi0 (Fin.ext h)
      omega
    have hneg0 : turn u w (v 0) < 0 := hj0 ▸ hj'
    apply not_alternating_line_sides
      (htri 0 i (i + 1) h0i hinext)
      (htri 0 i j h0i hij)
      (htri 0 (i + 1) j (h0i.trans hinext) hnextj)
      (htri i (i + 1) j hinext hnextj)
      (u := w) (w := u)
    · rw [turn_swap_first]; exact neg_pos.mpr hneg0
    · rw [turn_swap_first]; exact neg_neg_of_pos hi
    · rw [turn_swap_first]; exact neg_pos.mpr hi'
    · rw [turn_swap_first]; exact neg_neg_of_pos hj
  · have hjnext : j < j + 1 := by change j.val < (j + 1).val; omega
    exact not_alternating_line_sides
      (htri i (i + 1) j hinext hnextj)
      (htri i (i + 1) (j + 1) hinext (hnextj.trans hjnext))
      (htri i j (j + 1) hij hjnext)
      (htri (i + 1) j (j + 1) hnextj hjnext) hi hi' hj hj'

/-- There is at most one positive-to-negative crossing of a line along a
strict convex polygon. Combined with `exists_cyclic_transition`, this
provides uniqueness of the relevant edge without relying on a diagram. -/
theorem cyclic_line_crossing_unique {n : ℕ} [NeZero n] {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {u w : Point} {i j : Fin n}
    (hi : 0 < turn u w (v i)) (hi' : turn u w (v (i + 1)) < 0)
    (hj : 0 < turn u w (v j)) (hj' : turn u w (v (j + 1)) < 0) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (cyclic_crossing_not_lt htri hi hi' hj hj' h).elim
  · exact h
  · exact (cyclic_crossing_not_lt htri hj hj' hi hi' h).elim

/-- From an interior point, the directions to the polygon vertices cross
any nondegenerate radial line from positive to negative somewhere. -/
theorem exists_radial_sign_crossing {n : ℕ} [NeZero n] (v : Fin n → Point)
    {d q : Point} (hdHull : d ∈ convexHull ℝ (Set.range v))
    (hne : ∀ i, turn d (v i) q ≠ 0) :
    ∃ i, 0 < turn d (v i) q ∧ turn d (v (i + 1)) q < 0 := by
  have hyes : ∃ i, 0 < turn d (v i) q := by
    by_contra hall
    push Not at hall
    have hs : Set.range v ⊆ (turnAffine d q) ⁻¹' Set.Ioi 0 := by
      rintro p ⟨i, rfl⟩
      change 0 < turn d q (v i)
      rw [turn_swap_last]
      exact neg_pos.mpr (lt_of_le_of_ne (hall i) (hne i))
    have h := convexHull_min hs ((convex_Ioi (0 : ℝ)).affine_preimage
      (turnAffine d q)) hdHull
    change 0 < turn d q d at h
    simp at h
  have hno : ∃ i, ¬0 < turn d (v i) q := by
    by_contra hall
    push Not at hall
    have hs : Set.range v ⊆ (turnAffine d q) ⁻¹' Set.Iio 0 := by
      rintro p ⟨i, rfl⟩
      change turn d q (v i) < 0
      rw [turn_swap_last]
      exact neg_neg_of_pos (hall i)
    have h := convexHull_min hs ((convex_Iio (0 : ℝ)).affine_preimage
      (turnAffine d q)) hdHull
    change turn d q d < 0 at h
    simp at h
  obtain ⟨i, hipos, hinot⟩ := exists_cyclic_transition
    (fun i ↦ 0 < turn d (v i) q) hyes hno
  exact ⟨i, hipos, lt_of_le_of_ne (le_of_not_gt hinot) (hne (i + 1))⟩

/-- An ambient point in the polygon hull, but not a vertex, is strictly
inside each edge half-plane. General position handles the boundary. -/
theorem cyclic_edge_strict_of_mem_hull {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hmem : ∀ i, v i ∈ P) {p : Point} (hpP : p ∈ P)
    (hpHull : p ∈ convexHull ℝ (Set.range v)) (hpnot : p ∉ Set.range v)
    (i : Fin n) : 0 < turn (v i) (v (i + 1)) p := by
  have hinext : i ≠ i + 1 := by
    have h := cyclic_next_cases i
    intro hi
    have := congrArg Fin.val hi
    omega
  have hvp (j) : v j ≠ p := fun h ↦ hpnot ⟨j, h⟩
  exact lt_of_le_of_ne (cyclic_edge_nonneg_of_mem_hull htri hpHull i)
    (turn_ne_zero_of_generalPosition hgen (hmem i) (hmem (i + 1)) hpP
      (hinj.ne hinext) (hvp i) (hvp (i + 1))).symm

/-- The triangles from an interior point to the cyclic edges form a fan:
every other nonvertex ambient point in the polygon lies in exactly one
open fan triangle. -/
theorem exists_unique_radial_triangle {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hmem : ∀ i, v i ∈ P) {d q : Point} (hdP : d ∈ P) (hqP : q ∈ P)
    (hdHull : d ∈ convexHull ℝ (Set.range v)) (hdnot : d ∉ Set.range v)
    (hqHull : q ∈ convexHull ℝ (Set.range v)) (hqnot : q ∉ Set.range v)
    (hdq : d ≠ q) : ∃! i, StrictlyInsideTriangle d (v i) (v (i + 1)) q := by
  have hvd (i) : v i ≠ d := fun h ↦ hdnot ⟨i, h⟩
  have hvq (i) : v i ≠ q := fun h ↦ hqnot ⟨i, h⟩
  have hne (i) : turn d (v i) q ≠ 0 :=
    turn_ne_zero_of_generalPosition hgen hdP (hmem i) hqP (hvd i).symm hdq (hvq i)
  obtain ⟨i, hi, hi'⟩ := exists_radial_sign_crossing v hdHull hne
  have hqedge := cyclic_edge_strict_of_mem_hull hgen hn v hinj htri hmem hqP hqHull hqnot i
  refine ⟨i, ⟨hi, hqedge, ?_⟩, ?_⟩
  · rw [turn_swap_first]
    exact neg_pos.mpr hi'
  · intro j hj
    apply cyclic_line_crossing_unique htri (u := q) (w := d)
    · convert hj.1 using 1 <;> unfold turn <;> ring
    · have hh := hj.2.2
      rw [turn_swap_first] at hh
      have hneg : turn d (v (j + 1)) q < 0 := by linarith
      convert hneg using 1 <;> unfold turn <;> ring
    · convert hi using 1 <;> unfold turn <;> ring
    · convert hi' using 1 <;> unfold turn <;> ring

/-- The radial sectors based on a cyclic polygon and an interior point
cover every ambient point outside its hull. General position eliminates
the boundary rays; an adjacent sign change identifies the required edge. -/
theorem exists_radial_sector_of_not_mem_hull {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hmem : ∀ i, v i ∈ P) {d q : Point} (hdP : d ∈ P) (hqP : q ∈ P)
    (hdHull : d ∈ convexHull ℝ (Set.range v)) (hdnot : d ∉ Set.range v)
    (hqout : q ∉ convexHull ℝ (Set.range v)) :
    ∃ i, q ∈ sector ![v (i + 1), d, v i] := by
  classical
  have hdq : d ≠ q := by rintro rfl; exact hqout hdHull
  have hvd (i) : v i ≠ d := fun h ↦ hdnot ⟨i, h⟩
  have hvq (i) : v i ≠ q := fun h ↦ hqout
    (h ▸ subset_convexHull ℝ _ (Set.mem_range_self i))
  have hne (i) : turn d (v i) q ≠ 0 :=
    turn_ne_zero_of_generalPosition hgen hdP (hmem i) hqP (hvd i).symm hdq (hvq i)
  have hyes : ∃ i, 0 < turn d (v i) q := by
    by_contra hall
    push Not at hall
    have hs : Set.range v ⊆ (turnAffine d q) ⁻¹' Set.Ioi 0 := by
      rintro p ⟨i, rfl⟩
      change 0 < turn d q (v i)
      rw [turn_swap_last]
      exact neg_pos.mpr (lt_of_le_of_ne (hall i) (hne i))
    have h := convexHull_min hs ((convex_Ioi (0 : ℝ)).affine_preimage
      (turnAffine d q)) hdHull
    change 0 < turn d q d at h
    simp at h
  have hno : ∃ i, ¬0 < turn d (v i) q := by
    by_contra hall
    push Not at hall
    have hs : Set.range v ⊆ (turnAffine d q) ⁻¹' Set.Iio 0 := by
      rintro p ⟨i, rfl⟩
      change turn d q (v i) < 0
      rw [turn_swap_last]
      exact neg_neg_of_pos (hall i)
    have h := convexHull_min hs ((convex_Iio (0 : ℝ)).affine_preimage
      (turnAffine d q)) hdHull
    change turn d q d < 0 at h
    simp at h
  obtain ⟨i, hipos, hinot⟩ := exists_cyclic_transition
    (fun i ↦ 0 < turn d (v i) q) hyes hno
  have hineg : turn d (v (i + 1)) q < 0 :=
    lt_of_le_of_ne (le_of_not_gt hinot) (hne (i + 1))
  have hinext : i ≠ i + 1 := by
    have h := cyclic_next_cases i
    intro hi
    have := congrArg Fin.val hi
    omega
  have hinside : 0 < turn d (v i) (v (i + 1)) := by
    rw [← turn_rotate d (v i) (v (i + 1))]
    exact lt_of_le_of_ne (cyclic_edge_nonneg_of_mem_hull htri hdHull i)
      (turn_ne_zero_of_generalPosition hgen (hmem i) (hmem (i + 1)) hdP
        (hinj.ne hinext) (hvd i) (hvd (i + 1))).symm
  have hedge : turn (v i) (v (i + 1)) q < 0 := by
    by_contra h
    have hqT : q ∈ triangleHull d (v i) (v (i + 1)) := by
      apply weaklyInsideTriangle_mem_triangleHull hinside
      refine ⟨hipos.le, le_of_not_gt h, ?_⟩
      rw [turn_swap_first]
      exact (neg_pos.mpr hineg).le
    exact hqout (triangleHull_subset_of_mem (convex_convexHull ℝ _) hdHull
      (subset_convexHull ℝ _ (Set.mem_range_self i))
      (subset_convexHull ℝ _ (Set.mem_range_self (i + 1))) hqT)
  refine ⟨i, ?_⟩
  have h01 : 0 < turn (v (i + 1)) d q := by
    rw [turn_swap_first]
    exact neg_pos.mpr hineg
  have h02 : 0 < turn (v (i + 1)) (v i) q := by
    rw [turn_swap_first]
    exact neg_pos.mpr hedge
  intro j k hjk
  fin_cases j <;> fin_cases k <;> norm_num at hjk <;> assumption

end Lax56Proofs.ValtrCyclic
