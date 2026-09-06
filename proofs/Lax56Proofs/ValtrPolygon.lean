import Lax56Proofs.ValtrCyclic

namespace Lax56Proofs.ValtrPolygon

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrCaps Lax56Proofs.ValtrCounting
open Lax56Proofs.ValtrExtension

/-- The intersection of the edge half-planes of a strictly oriented
polygon is its convex hull. A finite minimum locates the appropriate
triangle in the fan from vertex zero. -/
theorem mem_convexHull_of_edge_nonneg {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    {v : Fin n → Point}
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {p : Point} (hp : ∀ i, 0 ≤ turn (v i) (v (i + 1)) p) :
    p ∈ convexHull ℝ (Set.range v) := by
  classical
  let last : Fin n := ⟨n - 1, by omega⟩
  have hlast : last + 1 = 0 := by
    have h := cyclic_next_cases last
    apply Fin.ext
    simp only [Fin.val_zero]
    dsimp [last] at h ⊢
    omega
  have hlastside : turn (v 0) (v last) p ≤ 0 := by
    have h := hp last
    rw [hlast, turn_swap_first] at h
    linarith
  let J := Finset.univ.filter (fun j : Fin n ↦ 2 ≤ j.val ∧ turn (v 0) (v j) p ≤ 0)
  have hJ : J.Nonempty := by
    refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hlastside⟩⟩
    dsimp [last]
    omega
  obtain ⟨j, hjJ, hjmin⟩ := J.exists_min_image Fin.val hJ
  obtain ⟨hjtwo, hjside⟩ := (Finset.mem_filter.mp hjJ).2
  let i : Fin n := ⟨j.val - 1, by omega⟩
  have hinext : i + 1 = j := by
    have h := cyclic_next_cases i
    apply Fin.ext
    dsimp [i] at h ⊢
    omega
  have hi0 : (0 : Fin n) < i := by
    change (0 : Fin n).val < i.val
    simp only [Fin.val_zero]
    dsimp [i]
    omega
  have hij : i < j := by change i.val < j.val; dsimp [i]; omega
  have hiside : 0 ≤ turn (v 0) (v i) p := by
    by_cases hi1 : i.val = 1
    · have hzero : (0 : Fin n) + 1 = i := by
        have h := cyclic_next_cases (0 : Fin n)
        have hz : (0 : Fin n).val = 0 := Fin.val_zero n
        apply Fin.ext
        omega
      simpa only [hzero] using hp 0
    · by_contra h
      have hiJ : i ∈ J := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, by have := i.isLt; dsimp [i] at *; omega,
          (lt_of_not_ge h).le⟩
      have hm := hjmin i hiJ
      change i.val < j.val at hij
      omega
  have hpTri : p ∈ triangleHull (v 0) (v i) (v j) := by
    apply weaklyInsideTriangle_mem_triangleHull (htri 0 i j hi0 hij)
    refine ⟨hiside, ?_, ?_⟩
    · simpa only [hinext] using hp i
    · rw [turn_swap_first]
      exact neg_nonneg.mpr hjside
  apply convexHull_mono (s := {v 0, v i, v j}) _ hpTri
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl <;> exact Set.mem_range_self _

/-- A linear, non-wrapping consecutive block of polygon vertices. -/
def offsetIndex {n t : ℕ} (a : ℕ) (h : a + t ≤ n) (i : Fin t) : Fin n :=
  ⟨a + i.val, by have := i.isLt; omega⟩

theorem offsetIndex_strictMono {n t : ℕ} (a : ℕ) (h : a + t ≤ n) :
    StrictMono (offsetIndex a h) := by
  intro i j hij
  change a + i.val < a + j.val
  omega

/-- A chord joining the endpoints of a consecutive block cuts off exactly
that block's convex hull. Unlike the earlier six-cap construction, this
works for every block size, including the five-vertex cap in Valtr's final
change-of-interior-point argument. -/
theorem consecutive_cap_eq {n t : ℕ} [NeZero t] (ht : 3 ≤ t)
    (v : Fin n → Point)
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (a : ℕ) (ha : a + t ≤ n) :
    let b := fun i : Fin t ↦ v (offsetIndex a ha i)
    let last : Fin t := ⟨t - 1, by omega⟩
    convexHull ℝ (Set.range b) =
      convexHull ℝ (Set.range v) ∩ {p | 0 ≤ turn (b last) (b 0) p} := by
  dsimp only
  let b := fun i : Fin t ↦ v (offsetIndex a ha i)
  let last : Fin t := ⟨t - 1, by omega⟩
  have hbtri : ∀ i j k, i < j → j < k → 0 < turn (b i) (b j) (b k) := by
    intro i j k hij hjk
    exact htri _ _ _ (offsetIndex_strictMono a ha hij) (offsetIndex_strictMono a ha hjk)
  have hlast : last + 1 = 0 := by
    have h := cyclic_next_cases last
    apply Fin.ext
    simp only [Fin.val_zero]
    dsimp [last] at h ⊢
    omega
  ext p
  constructor
  · intro hp
    refine ⟨convexHull_mono (Set.range_comp_subset_range _ _) hp, ?_⟩
    simpa only [hlast] using cyclic_edge_nonneg_of_mem_hull hbtri hp last
  · rintro ⟨hp, hside⟩
    apply mem_convexHull_of_edge_nonneg ht hbtri
    intro i
    by_cases hilast : i = last
    · subst i
      simpa only [hlast] using hside
    · have hnext := cyclic_next_cases i
      have hival : i.val ≠ t - 1 := fun h ↦ hilast (Fin.ext h)
      have hadj : (offsetIndex a ha i).val + 1 = (offsetIndex a ha (i + 1)).val := by
        dsimp [offsetIndex]
        omega
      apply turn_nonneg_of_mem_convexHull (A := Set.range v) _ hp
      rintro q ⟨j, rfl⟩
      by_cases hj : j = offsetIndex a ha i
      · subst j
        simp [b]
      by_cases hj' : j = offsetIndex a ha (i + 1)
      · subst j
        simp [b]
      have h := turn_consecutive_pos v 1 (by simpa only [one_mul] using htri)
        (offsetIndex a ha i) (offsetIndex a ha (i + 1)) hadj j hj hj'
      simpa only [one_mul] using h.le

/-- An inner ambient point outside a consecutive cap is in the exterior
sector of the cap's vertex chain. A wrong-side chord would place it in a
smaller cap contained in the original one. -/
theorem outside_consecutive_cap_mem_sector {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) {n t : ℕ} [NeZero t] (ht : 3 ≤ t)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer Q : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (a : ℕ) (ha : a + t ≤ n) {q : Point} (hq : q ∈ inner Q)
    (hqout : q ∉ convexHull ℝ (Set.range (fun i : Fin t ↦ v (offsetIndex a ha i)))) :
    q ∈ sector (fun i : Fin t ↦ v (offsetIndex a ha i)) := by
  have hmem (i) : v i ∈ extremeLayer Q := by
    change v i ∈ (extremeLayer Q : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hqHull : q ∈ convexHull ℝ (Set.range v) := by
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ (inner_subset Q hq)
  intro i j hij
  have hne : turn (v (offsetIndex a ha i)) (v (offsetIndex a ha j)) q ≠ 0 :=
    turn_ne_zero_of_generalPosition hgen
      (extremeLayer_subset Q (hmem _)) (extremeLayer_subset Q (hmem _))
      (inner_subset Q hq) (hinj.ne (offsetIndex_strictMono a ha hij).ne)
      (fun h ↦ (Finset.mem_sdiff.mp hq).2 (h ▸ hmem _))
      (fun h ↦ (Finset.mem_sdiff.mp hq).2 (h ▸ hmem _))
  by_cases hadj : i.val + 1 = j.val
  · apply lt_of_le_of_ne _ hne.symm
    apply turn_nonneg_of_mem_convexHull (A := Set.range v) _ hqHull
    rintro p ⟨k, rfl⟩
    by_cases hki : k = offsetIndex a ha i
    · subst k; simp
    by_cases hkj : k = offsetIndex a ha j
    · subst k; simp
    have h := turn_consecutive_pos v 1 (by simpa only [one_mul] using htri)
      (offsetIndex a ha i) (offsetIndex a ha j) (by dsimp [offsetIndex]; omega) k hki hkj
    simpa only [one_mul] using h.le
  · by_contra hpos
    have hnonpos := le_of_not_gt hpos
    let k := j.val - i.val + 1
    have hk : 3 ≤ k := by dsimp [k]; omega
    haveI : NeZero k := ⟨by omega⟩
    have hkbound : a + i.val + k ≤ n := by dsimp [k]; omega
    have hfirst : offsetIndex (a + i.val) hkbound (0 : Fin k) = offsetIndex a ha i := by
      apply Fin.ext
      simp [offsetIndex]
    let last : Fin k := ⟨k - 1, by omega⟩
    have hlast : offsetIndex (a + i.val) hkbound last = offsetIndex a ha j := by
      apply Fin.ext
      dsimp [offsetIndex, last, k]
      omega
    have hqsmall : q ∈ convexHull ℝ
        (Set.range (fun z : Fin k ↦ v (offsetIndex (a + i.val) hkbound z))) := by
      rw [consecutive_cap_eq hk v htri (a + i.val) hkbound]
      refine ⟨hqHull, ?_⟩
      change 0 ≤ turn (v (offsetIndex (a + i.val) hkbound last))
        (v (offsetIndex (a + i.val) hkbound 0)) q
      rw [hlast, hfirst, turn_swap_first]
      exact neg_nonneg.mpr hnonpos
    apply hqout
    apply convexHull_mono _ hqsmall
    rintro p ⟨z, rfl⟩
    refine ⟨⟨i.val + z.val, by have := z.isLt; dsimp [k] at this; omega⟩, ?_⟩
    dsimp only
    congr 1
    apply Fin.ext
    dsimp [offsetIndex]
    omega

/-- An inner point in a consecutive cap forces a vertex of the next
convex layer in the same cap. This is the precise vertex-extraction step
used to replace `d` by `d'` in Valtr's final pentagon. -/
theorem exists_next_layer_vertex_in_consecutive_cap {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) {n t : ℕ} [NeZero t] (ht : 3 ≤ t)
    (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer Q : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (a : ℕ) (ha : a + t ≤ n) {p : Point} (hp : p ∈ inner Q)
    (hpcap : p ∈ convexHull ℝ (Set.range (fun i : Fin t ↦ v (offsetIndex a ha i)))) :
    ∃ d ∈ extremeLayer (inner Q),
      d ∈ convexHull ℝ (Set.range (fun i : Fin t ↦ v (offsetIndex a ha i))) := by
  let b := fun i : Fin t ↦ v (offsetIndex a ha i)
  let last : Fin t := ⟨t - 1, by omega⟩
  let f := turnAffine (b last) (b 0)
  have hbmem (i) : b i ∈ extremeLayer Q := by
    change b i ∈ (extremeLayer Q : Set Point)
    rw [← hrange]
    exact Set.mem_range_self _
  have hblast : b last ≠ b 0 :=
    (hinj.comp (offsetIndex_strictMono a ha).injective).ne (by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      dsimp [last] at this
      omega)
  have hne : f p ≠ 0 := turn_ne_zero_of_generalPosition hgen
    (extremeLayer_subset Q (hbmem last)) (extremeLayer_subset Q (hbmem 0))
    (inner_subset Q hp) hblast
    (fun h ↦ (Finset.mem_sdiff.mp hp).2 (h ▸ hbmem last))
    (fun h ↦ (Finset.mem_sdiff.mp hp).2 (h ▸ hbmem 0))
  have hnonneg : 0 ≤ f p := by
    have hcap := (Set.ext_iff.mp (consecutive_cap_eq ht v htri a ha)) p
    exact (hcap.mp hpcap).2
  have hpHull : p ∈ convexHull ℝ (extremeLayer (inner Q) : Set Point) := by
    rw [convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hp
  obtain ⟨d, hd, hdf⟩ := exists_positive_vertex _ f hpHull (lt_of_le_of_ne hnonneg hne.symm)
  refine ⟨d, hd, ?_⟩
  rw [consecutive_cap_eq ht v htri a ha]
  refine ⟨?_, hdf.le⟩
  rw [hrange, convexHull_extremeLayer]
  exact subset_convexHull ℝ _ (inner_subset Q (extremeLayer_subset (inner Q) hd))

/-- In a hexagon-free set with a nonempty interior, every consecutive
five-vertex cap contains a vertex of the next layer. If the cap contained
no interior point, its empty pentagon could be extended towards any
interior point outside the cap. -/
theorem exists_next_layer_vertex_in_five_cap {Q : Finset Point}
    (hgen : ¬HasThreeCollinear Q) (hno : ¬HasEmptyHexagon Q)
    (hinner : (inner Q).Nonempty) {n : ℕ}
    (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer Q : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    (a : ℕ) (ha : a + 5 ≤ n) :
    ∃ d ∈ extremeLayer (inner Q),
      d ∈ convexHull ℝ (Set.range (fun i : Fin 5 ↦ v (offsetIndex a ha i))) := by
  classical
  let b := fun i : Fin 5 ↦ v (offsetIndex a ha i)
  have hbmem (i) : b i ∈ extremeLayer Q := by
    change b i ∈ (extremeLayer Q : Set Point)
    rw [← hrange]
    exact Set.mem_range_self _
  have hbsub : Finset.univ.image b ⊆ Q := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact extremeLayer_subset Q (hbmem i)
  by_cases hpoint : ∃ p ∈ inner Q, p ∈ convexHull ℝ (Set.range b)
  · obtain ⟨p, hp, hpcap⟩ := hpoint
    exact exists_next_layer_vertex_in_consecutive_cap hgen (by decide : 3 ≤ 5)
      v hinj hrange htri a ha hp hpcap
  · obtain ⟨q, hq⟩ := hinner
    have hqout : q ∉ convexHull ℝ (Set.range b) := fun h ↦ hpoint ⟨q, hq, h⟩
    have hsector := outside_consecutive_cap_mem_sector hgen (by decide : 3 ≤ 5)
      v hinj hrange htri a ha hq hqout
    have hempty : ∀ p ∈ Q, p ∈ convexHull ℝ (Set.range b) → p ∈ Set.range b := by
      intro p hp hpHull
      by_contra hpnot
      by_cases hpouter : p ∈ extremeLayer Q
      · apply extreme_not_mem_convexHull hpouter hbsub
          (by simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hpnot)
        simpa using hpHull
      · exact hpoint ⟨p, Finset.mem_sdiff.mpr ⟨hp, hpouter⟩, hpHull⟩
    apply (hno (empty_pentagon_extension hgen b
      (hinj.comp (offsetIndex_strictMono a ha).injective)
      (fun i j k hij hjk ↦ htri _ _ _
        (offsetIndex_strictMono a ha hij) (offsetIndex_strictMono a ha hjk))
      (fun i ↦ extremeLayer_subset Q (hbmem i)) (inner_subset Q hq) hempty ?_)).elim
    intro i j hij
    have h01 := hsector 0 1 (by decide)
    have h03 := hsector 0 3 (by decide)
    have h04 := hsector 0 4 (by decide)
    have h13 := hsector 1 3 (by decide)
    have h14 := hsector 1 4 (by decide)
    have h34 := hsector 3 4 (by decide)
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

end Lax56Proofs.ValtrPolygon
