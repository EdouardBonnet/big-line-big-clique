import Lax56Proofs.ValtrCaps

/-!
The empty-pentagon extension in Observation 2 of Valtr's *On Empty Hexagons*.
The auxiliary lemmas make the finite minimization and polygon decomposition
explicit. No four-layer theorem is used in this file.
-/

namespace Lax56Proofs.ValtrExtension

open Lax56.Geometry Lax56.ConvexLayers Lax56.HujterKisfaludiBak
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry Lax56Proofs.CyclicOrder
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrCaps

/-- The four triangles in the fan rooted at the first vertex cover the
closed hull of a strictly convex hexagon, including its boundary. -/
theorem hexagon_mem_fan {v : Fin 6 → Point} (hv : StrictConvexHexagon v)
    {p : Point} (hp : p ∈ convexHull ℝ (Set.range v)) :
    p ∈ triangleHull (v 0) (v 1) (v 2) ∨
    p ∈ triangleHull (v 0) (v 2) (v 3) ∨
    p ∈ triangleHull (v 0) (v 3) (v 4) ∨
    p ∈ triangleHull (v 0) (v 4) (v 5) := by
  have hedge := edgeTurn_nonneg_of_mem_convexHull hv hp
  have hfan (i j : Fin 6) (hi : 0 < i) (hij : i < j)
      (hleft : 0 ≤ turn (v 0) (v i) p)
      (hedge : 0 ≤ turn (v i) (v j) p)
      (hright : turn (v 0) (v j) p ≤ 0) :
      p ∈ triangleHull (v 0) (v i) (v j) := by
    apply weaklyInsideTriangle_mem_triangleHull (hv.2.2 0 i j hi hij)
    refine ⟨hleft, hedge, ?_⟩
    rw [turn_swap_first]
    linarith
  by_cases h₂ : turn (v 0) (v 2) p ≤ 0
  · exact Or.inl (hfan 1 2 (by decide) (by decide) (hedge 0) (hedge 1) h₂)
  by_cases h₃ : turn (v 0) (v 3) p ≤ 0
  · exact Or.inr (Or.inl (hfan 2 3 (by decide) (by decide)
      (le_of_not_ge h₂) (hedge 2) h₃))
  by_cases h₄ : turn (v 0) (v 4) p ≤ 0
  · exact Or.inr (Or.inr (Or.inl (hfan 3 4 (by decide) (by decide)
      (le_of_not_ge h₃) (hedge 3) h₄)))
  have h₅ : turn (v 0) (v 5) p ≤ 0 := by
    have h := hedge 5
    change 0 ≤ turn (v 5) (v 0) p at h
    rw [turn_swap_first] at h
    linarith
  exact Or.inr (Or.inr (Or.inr (hfan 4 5 (by decide) (by decide)
    (le_of_not_ge h₄) (hedge 4) h₅)))

/-- Strict cyclic edge supports certify convex independence without any
assumption on the first coordinates of the vertices. -/
theorem convexIndependent_hexagon {v : Fin 6 → Point} (hv : StrictConvexHexagon v) :
    ConvexIndependent ℝ v := by
  apply convexIndependent_iff_notMem_convexHull_diff.mpr
  intro i S
  let a : Fin 6 := i - 1
  let b : Fin 6 := i + 1
  have hai : a + 1 = i := by dsimp [a]; omega
  have hai' : a ≠ i := by dsimp [a]; omega
  have hbi' : b ≠ i := by dsimp [b]; omega
  have hab' : a ≠ b := by dsimp [a, b]; omega
  apply not_mem_convexHull_of_support _ (v i)
    (fun p ↦ turn (v a) (v i) p + turn (v i) (v b) p) (by simp)
  · intro x y u w huw
    rw [turn_convex_combo _ _ _ _ _ _ huw, turn_convex_combo _ _ _ _ _ _ huw]
    ring
  · rintro p ⟨j, hj, rfl⟩
    have hji : j ≠ i := hj.2
    have hleft : 0 ≤ turn (v a) (v i) (v j) := by
      by_cases hja : j = a
      · subst j; simp
      · simpa only [hai] using (hv.2.1 a j hja (hai ▸ hji)).le
    have hright : 0 ≤ turn (v i) (v b) (v j) := by
      by_cases hjb : j = b
      · subst j; simp
      · exact (hv.2.1 i j hji hjb).le
    by_cases hja : j = a
    · subst j
      exact add_pos_of_nonneg_of_pos hleft (hv.2.1 i a hai' hab')
    · have hpos := hv.2.1 a j hja (hai ▸ hji)
      rw [hai] at hpos
      exact add_pos_of_pos_of_nonneg hpos hright

/-- A nondegenerate triangle with a prescribed base contains an empty
triangle on that same base. Minimize the positive oriented height over a
finite set of candidate apices; general position excludes the three sides. -/
theorem exists_empty_triangle_on_base {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) {q a b : Point}
    (hq : q ∈ P) (ha : a ∈ P) (hb : b ∈ P) (hqab : 0 < turn a b q) :
    ∃ r ∈ P, r ∈ triangleHull q a b ∧ 0 < turn a b r ∧
      ∀ p ∈ P, p ∈ triangleHull r a b → p = r ∨ p = a ∨ p = b := by
  classical
  let candidates := P.filter (fun p ↦ p ∈ triangleHull q a b ∧ 0 < turn a b p)
  have hne : candidates.Nonempty :=
    ⟨q, Finset.mem_filter.mpr ⟨hq, vertex_mem_triangleHull q a b, hqab⟩⟩
  obtain ⟨r, hr, hmin⟩ := candidates.exists_min_image (fun p ↦ turn a b p) hne
  obtain ⟨hrP, hrT, hrpos⟩ := Finset.mem_filter.mp hr
  refine ⟨r, hrP, hrT, hrpos, ?_⟩
  intro p hp hpT
  by_cases hpr : p = r
  · exact Or.inl hpr
  by_cases hpa : p = a
  · exact Or.inr (Or.inl hpa)
  by_cases hpb : p = b
  · exact Or.inr (Or.inr hpb)
  have hab : a ≠ b := by rintro rfl; simp [turn] at hrpos
  have hra : r ≠ a := by rintro rfl; simp at hrpos
  have hrb : r ≠ b := by rintro rfl; simp at hrpos
  have hrab : 0 < turn r a b := by
    rw [← turn_rotate r a b]
    exact hrpos
  have hpedge := triangle_edge_nonneg hrab.le hpT
  have hppos : 0 < turn a b p := lt_of_le_of_ne hpedge.2.1
    (turn_ne_zero_of_generalPosition hgen ha hb hp hab (Ne.symm hpa) (Ne.symm hpb)).symm
  have hpside : 0 < turn r a p := lt_of_le_of_ne hpedge.1
    (turn_ne_zero_of_generalPosition hgen hrP ha hp hra (Ne.symm hpr) (Ne.symm hpa)).symm
  have hpT' : p ∈ triangleHull q a b := by
    apply triangleHull_subset_of_mem (convex_convexHull ℝ _) hrT
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hpT
  have hminp := hmin p (Finset.mem_filter.mpr ⟨hp, hpT', hppos⟩)
  have harea := turn_triangle_decompose r a b p
  rw [← turn_rotate r a b] at harea
  exfalso
  linarith [hpedge.2.2]

/-- The two endpoints of a cyclically ordered five-point chain lie on the
nonnegative side of every forward chord of that chain. -/
theorem pentagon_endpoints_nonneg {v : Fin 5 → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {i j : Fin 5} (hij : i < j) :
    0 ≤ turn (v i) (v j) (v 0) ∧ 0 ≤ turn (v i) (v j) (v 4) := by
  constructor
  · by_cases hi : i = 0
    · subst i; simp
    · have h := htri 0 i j (by omega) hij
      rw [turn_rotate]
      exact h.le
  · by_cases hj : j = 4
    · subst j; simp
    · exact (htri i j 4 hij (by omega)).le

/-- The extension argument when the proposed sixth point already gives a
strict convex hexagon. The new apex is chosen in its attached triangle,
and that triangle is made empty by finite height minimization. -/
theorem empty_pentagon_extend_of_hexagon {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) (v : Fin 5 → Point) {q : Point}
    (hmem : ∀ i, v i ∈ P) (hq : q ∈ P)
    (hhex : StrictConvexHexagon (Fin.snoc v q))
    (hempty : ∀ p ∈ P, p ∈ convexHull ℝ (Set.range v) → p ∈ Set.range v) :
    HasEmptyHexagon P := by
  classical
  have htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k) := by
    intro i j k hij hjk
    simpa only [Fin.snoc_castSucc] using
      hhex.2.2 i.castSucc j.castSucc k.castSucc hij hjk
  have hinj : Function.Injective v := (Fin.snoc_injective_iff.mp hhex.1).1
  have hqpos : 0 < turn (v 0) (v 4) q := by
    simpa using hhex.2.2 0 4 5 (by decide) (by decide)
  obtain ⟨r, hrP, hrT, hrpos, hrempty⟩ :=
    exists_empty_triangle_on_base hgen hq (hmem 0) (hmem 4) hqpos
  have hbase : ∀ i, turn (v 0) (v 4) (v i) ≤ 0 := by
    intro i
    by_cases hi0 : i = 0
    · subst i; simp
    by_cases hi4 : i = 4
    · subst i; simp
    have h := htri 0 i 4 (by omega) (by omega)
    rw [turn_swap_last]
    linarith
  have hrnot : r ∉ Set.range v := by
    rintro ⟨i, rfl⟩
    exact (not_le_of_gt hrpos) (hbase i)
  have hrt (i j : Fin 5) (hij : i < j) : 0 < turn (v i) (v j) r := by
    have hnonneg : 0 ≤ turn (v i) (v j) r := by
      apply turn_nonneg_of_mem_convexHull (A := ({q, v 0, v 4} : Set Point)) _ hrT
      intro p hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · have h := hhex.2.2 i.castSucc j.castSucc (Fin.last 5) hij
          (Fin.castSucc_lt_last j)
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using h.le
      · exact (pentagon_endpoints_nonneg htri hij).1
      · exact (pentagon_endpoints_nonneg htri hij).2
    have hne := turn_ne_zero_of_generalPosition hgen (hmem i) (hmem j) hrP
      (hinj.ne hij.ne) (fun h ↦ hrnot ⟨i, h⟩) (fun h ↦ hrnot ⟨j, h⟩)
    exact lt_of_le_of_ne hnonneg hne.symm
  let w : Fin 6 → Point := Fin.snoc v r
  have hw : StrictConvexHexagon w := by
    apply strictConvexHexagon_of_triples _ (Fin.snoc_injective_iff.mpr ⟨hinj, hrnot⟩)
    intro i j k hij hjk
    cases i using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
    | cast i =>
      cases j using Fin.lastCases with
      | last => exact (not_lt_of_ge (Fin.le_last k) hjk).elim
      | cast j =>
        cases k using Fin.lastCases with
        | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hrt i j hij
        | cast k => simpa only [Fin.snoc_castSucc] using htri i j k hij hjk
  let H := Finset.univ.image w
  have hHrange : (H : Set Point) = Set.range w := by simp [H]
  have hHmem : H ⊆ P := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact Fin.lastCases (by simpa [w] using hrP)
      (fun i ↦ by simpa only [w, Fin.snoc_castSucc] using hmem i) i
  refine ⟨H, hHmem, ?_, ?_, ?_⟩
  · simp [H, Finset.card_image_of_injective _ hw.1]
  · have hconv := (convexIndependent_hexagon hw).range
    rw [← hHrange] at hconv
    exact hconv
  · intro p hp hpH
    change p ∈ (H : Set Point)
    rw [hHrange] at hpH ⊢
    have hsub {i j k : Fin 5} : triangleHull (v i) (v j) (v k) ⊆
        convexHull ℝ (Set.range v) := by
      apply triangleHull_subset_of_mem (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (Set.mem_range_self i))
        (subset_convexHull ℝ _ (Set.mem_range_self j))
        (subset_convexHull ℝ _ (Set.mem_range_self k))
    have hfinish : p ∈ convexHull ℝ (Set.range v) → p ∈ Set.range w := by
      intro hh
      rw [Fin.range_snoc]
      exact Set.mem_insert_of_mem _ (hempty p hp hh)
    rcases hexagon_mem_fan hw hpH with ht | ht | ht | ht
    · exact hfinish (hsub ht)
    · exact hfinish (hsub ht)
    · exact hfinish (hsub ht)
    · have ht' : p ∈ triangleHull r (v 0) (v 4) := by
        change p ∈ triangleHull (v 0) (v 4) r at ht
        rwa [triangleHull_rotate] at ht
      rw [Fin.range_snoc]
      rcases hrempty p hp ht' with rfl | rfl | rfl
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_range_self 0)
      · exact Set.mem_insert_of_mem _ (Set.mem_range_self 4)

/-- For a positively ordered convex chain, this is its exterior sector:
adjoining `q` after the last vertex preserves every oriented triple. -/
def sector {n : ℕ} (v : Fin n → Point) : Set Point :=
  {q | ∀ i j, i < j → 0 < turn (v i) (v j) q}

/-- In the sector of the first two and last two pentagon vertices, the
omitted middle vertex causes no additional constraint. Four determinant
identities verify the four missing positive orientations. -/
theorem pentagon_sector_of_four_sector {v : Fin 5 → Point} {q : Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hq : q ∈ sector ![v 0, v 1, v 3, v 4]) : q ∈ sector v := by
  have h01 : 0 < turn (v 0) (v 1) q := hq 0 1 (by decide)
  have h03 : 0 < turn (v 0) (v 3) q := hq 0 2 (by decide)
  have h04 : 0 < turn (v 0) (v 4) q := hq 0 3 (by decide)
  have h13 : 0 < turn (v 1) (v 3) q := hq 1 2 (by decide)
  have h14 : 0 < turn (v 1) (v 4) q := hq 1 3 (by decide)
  have h34 : 0 < turn (v 3) (v 4) q := hq 2 3 (by decide)
  have h12 : 0 < turn (v 1) (v 2) q := by
    apply (mul_pos_iff_of_pos_left (htri 0 1 3 (by decide) (by decide))).mp
    have hid : turn (v 0) (v 1) (v 3) * turn (v 1) (v 2) q =
        turn (v 0) (v 1) (v 2) * turn (v 1) (v 3) q +
        turn (v 0) (v 1) q * turn (v 1) (v 2) (v 3) := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos (htri 0 1 2 (by decide) (by decide)) h13)
      (mul_pos h01 (htri 1 2 3 (by decide) (by decide)))
  have h23 : 0 < turn (v 2) (v 3) q := by
    apply (mul_pos_iff_of_pos_left (htri 1 3 4 (by decide) (by decide))).mp
    have hid : turn (v 1) (v 3) (v 4) * turn (v 2) (v 3) q =
        turn (v 2) (v 3) (v 4) * turn (v 1) (v 3) q +
        turn (v 3) (v 4) q * turn (v 1) (v 2) (v 3) := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos (htri 2 3 4 (by decide) (by decide)) h13)
      (mul_pos h34 (htri 1 2 3 (by decide) (by decide)))
  have h02 : 0 < turn (v 0) (v 2) q := by
    apply (mul_pos_iff_of_pos_left h13).mp
    have hid : turn (v 1) (v 3) q * turn (v 0) (v 2) q =
        turn (v 0) (v 1) q * turn (v 2) (v 3) q +
        turn (v 1) (v 2) q * turn (v 0) (v 3) q := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos h01 h23) (mul_pos h12 h03)
  have h24 : 0 < turn (v 2) (v 4) q := by
    apply (mul_pos_iff_of_pos_left h13).mp
    have hid : turn (v 1) (v 3) q * turn (v 2) (v 4) q =
        turn (v 1) (v 2) q * turn (v 3) (v 4) q +
        turn (v 1) (v 4) q * turn (v 2) (v 3) q := by unfold turn; ring
    rw [hid]
    exact add_pos (mul_pos h12 h34) (mul_pos h14 h23)
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- Valtr's Observation 2, with the exact four-sector hypothesis from the
paper, and no hidden geometric or emptiness assumptions. -/
theorem empty_pentagon_extension {P : Finset Point}
    (hgen : ¬HasThreeCollinear P) (v : Fin 5 → Point) {q : Point}
    (hinj : Function.Injective v)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (hmem : ∀ i, v i ∈ P) (hqP : q ∈ P)
    (hempty : ∀ p ∈ P, p ∈ convexHull ℝ (Set.range v) → p ∈ Set.range v)
    (hq : q ∈ sector ![v 0, v 1, v 3, v 4]) : HasEmptyHexagon P := by
  have hsector := pentagon_sector_of_four_sector htri hq
  have hqnot : q ∉ Set.range v := by
    rintro ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst i
      have h := hsector 0 4 (by decide)
      simp at h
    · have h := hsector 0 i (by omega)
      simp at h
  apply empty_pentagon_extend_of_hexagon hgen v hmem hqP _ hempty
  apply strictConvexHexagon_of_triples _ (Fin.snoc_injective_iff.mpr ⟨hinj, hqnot⟩)
  intro i j k hij hjk
  cases i using Fin.lastCases with
  | last => exact (not_lt_of_ge (Fin.le_last j) hij).elim
  | cast i =>
    cases j using Fin.lastCases with
    | last => exact (not_lt_of_ge (Fin.le_last k) hjk).elim
    | cast j =>
      cases k using Fin.lastCases with
      | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hsector i j hij
      | cast k => simpa only [Fin.snoc_castSucc] using htri i j k hij hjk

end Lax56Proofs.ValtrExtension
