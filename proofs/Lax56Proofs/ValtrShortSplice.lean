import Lax56Proofs.ValtrCompressedSupport

namespace Lax56Proofs.ValtrShortSplice

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrSelection Lax56Proofs.ValtrProjective
open Lax56Proofs.ValtrCompression Lax56Proofs.ValtrCompressedSupport
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrLocalSupport
open scoped Classical

def shortChain (b c : ℕ → Point) (d : Point) (k : ℕ) : Point :=
  if k = 0 then b 0 else if k = 1 then c 0 else if k = 2 then d
  else if k = 3 then c 4 else b 5

theorem neighbor_cases (h b : ℕ → Point) (k) (hk : 1 ≤ k) (hkm : k ≤ 3)
    {q : Point} (hq : q ∈ neighbors h b k) :
    q = h (k - 1) ∨ q = h (k + 1) ∨ ∃ j, k - 1 ≤ j ∧ j ≤ k + 2 ∧ q = b j := by
  interval_cases k <;> simp only [neighbors, ↓reduceIte, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hq
  all_goals rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr ⟨0, by decide, by decide, rfl⟩)
    | exact Or.inr (Or.inr ⟨1, by decide, by decide, rfl⟩)
    | exact Or.inr (Or.inr ⟨2, by decide, by decide, rfl⟩)
    | exact Or.inr (Or.inr ⟨3, by decide, by decide, rfl⟩)
    | exact Or.inr (Or.inr ⟨4, by decide, by decide, rfl⟩)
    | exact Or.inr (Or.inr ⟨5, by decide, by decide, rfl⟩)

/-- Raw geometric data for the final five-sector replacement. The
center-cap assumption is obtained by moving the deep point while
preserving the apices. Supporting inequalities are not assumptions. -/
structure FiveSectorConfig (S : Finset Point) (b c : ℕ → Point) (d : Point) : Prop where
  base_mem : ∀ i, i ≤ 5 → b i ∈ extremeLayer (inner S)
  apex_mem : ∀ i, i ≤ 4 → c i ∈ extremeLayer (inner (inner S))
  base_inj : ∀ i j, i ≤ 5 → j ≤ 5 → b i = b j → i = j
  apex_inj : ∀ i j, i ≤ 4 → j ≤ 4 → c i = c j → i = j
  base_support : ∀ i, i ≤ 4 → ∀ p ∈ inner S, turn (b i) (b (i + 1)) p ≤ 0
  apex_triples : ∀ i j k, i < j → j < k → k ≤ 4 → turn (c i) (c j) (c k) < 0
  fan : ∀ i, i ≤ 4 → StrictlyInsideTriangle d (b (i + 1)) (b i) (c i)
  deep : d ∈ inner (inner (inner S))
  center_cap : d ∈ convexHull ℝ (Set.range (fun i : Fin 5 ↦ c i))
  empty_triangle : ∀ i, i ≤ 4 → ∀ p ∈ inner S,
    p ∈ triangleHull (b i) (c i) (b (i + 1)) → p = b i ∨ p = c i ∨ p = b (i + 1)

namespace FiveSectorConfig

variable {S : Finset Point} {b c : ℕ → Point} {d : Point}
variable (cfg : FiveSectorConfig S b c d)
include cfg

theorem base_inner (i) (hi : i ≤ 5) : b i ∈ inner S :=
  extremeLayer_subset _ (cfg.base_mem i hi)

theorem apex_inner (i) (hi : i ≤ 4) : c i ∈ inner (inner S) :=
  extremeLayer_subset _ (cfg.apex_mem i hi)

theorem apex_ne_base (i j) (hi : i ≤ 4) (hj : j ≤ 5) : c i ≠ b j := by
  intro heq
  exact (Finset.mem_sdiff.mp (cfg.apex_inner i hi)).2 (heq.symm ▸ cfg.base_mem j hj)

theorem deep_ne_base (j) (hj : j ≤ 5) : d ≠ b j := by
  intro heq
  exact (Finset.mem_sdiff.mp (inner_subset _ cfg.deep)).2 (heq.symm ▸ cfg.base_mem j hj)

theorem deep_ne_apex (i) (hi : i ≤ 4) : d ≠ c i := by
  intro heq
  exact (Finset.mem_sdiff.mp cfg.deep).2 (heq.symm ▸ cfg.apex_mem i hi)

theorem chain_inner (i) (hi : i ≤ 4) : shortChain b c d i ∈ inner S := by
  interval_cases i <;> simp only [shortChain, ↓reduceIte]
  · exact cfg.base_inner 0 (by decide)
  · exact inner_subset _ (cfg.apex_inner 0 (by decide))
  · exact inner_subset _ (inner_subset _ cfg.deep)
  · exact inner_subset _ (cfg.apex_inner 4 (by decide))
  · exact cfg.base_inner 5 (by decide)

theorem chain_mem_hull (i) (hi : i ≤ 4) :
    shortChain b c d i ∈ convexHull ℝ (extremeLayer (inner S) : Set Point) := by
  rw [convexHull_extremeLayer]
  exact subset_convexHull ℝ _ (cfg.chain_inner i hi)

theorem base_mem_hull (i) (hi : i ≤ 5) :
    b i ∈ convexHull ℝ (extremeLayer (inner S) : Set Point) :=
  subset_convexHull ℝ _ (cfg.base_mem i hi)

theorem local_hulls (k) (hk : 1 ≤ k) (hkm : k ≤ 3) :
    shortChain b c d k ∈ convexHull ℝ (neighbors (shortChain b c d) b k) := by
  interval_cases k
  · simp only [neighbors, shortChain, ↓reduceIte]
    apply convexHull_mono (show ({d, b 1, b 0} : Set Point) ⊆ {b 0, b 0, b 1, d} by
      intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull (cfg.fan 0 (by decide))
  · simp only [neighbors, shortChain, ↓reduceIte]
    exact compressed_center_hull (fun i : Fin 6 ↦ b i) (fun i : Fin 5 ↦ c i)
      cfg.center_cap (fun i ↦ cfg.fan i (by omega))
  · simp only [neighbors, shortChain, ↓reduceIte]
    apply convexHull_mono (show ({d, b 5, b 4} : Set Point) ⊆ {d, b 4, b 5, b 5} by
      intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull (cfg.fan 4 (by decide))

theorem chain_inj (i j) (hi : i ≤ 4) (hj : j ≤ 4)
    (heq : shortChain b c d i = shortChain b c d j) : i = j := by
  have hb : b 0 ≠ b 5 := fun hh ↦ by
    have := cfg.base_inj 0 5 (by decide) (by decide) hh
    omega
  have hc : c 0 ≠ c 4 := fun hh ↦ by
    have := cfg.apex_inj 0 4 (by decide) (by decide) hh
    omega
  have hc00 := cfg.apex_ne_base 0 0 (by decide) (by decide)
  have hc05 := cfg.apex_ne_base 0 5 (by decide) (by decide)
  have hc40 := cfg.apex_ne_base 4 0 (by decide) (by decide)
  have hc45 := cfg.apex_ne_base 4 5 (by decide) (by decide)
  have hd0 := cfg.deep_ne_base 0 (by decide)
  have hd5 := cfg.deep_ne_base 5 (by decide)
  have hdc0 := cfg.deep_ne_apex 0 (by decide)
  have hdc4 := cfg.deep_ne_apex 4 (by decide)
  interval_cases i <;> interval_cases j <;> simp_all [shortChain, ne_comm]

theorem chain_ne (i j) (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≠ j) :
    shortChain b c d i ≠ shortChain b c d j := fun hh ↦ hij (cfg.chain_inj i j hi hj hh)

theorem internal_ne_base (i j) (hi : 1 ≤ i) (him : i ≤ 3) (hj : j ≤ 5) :
    shortChain b c d i ≠ b j := by
  interval_cases i <;> simp only [shortChain, ↓reduceIte]
  · exact cfg.apex_ne_base 0 j (by decide) hj
  · exact cfg.deep_ne_base j hj
  · exact cfg.apex_ne_base 4 j (by decide) hj

theorem base_strict (hgen : ¬HasThreeCollinear S) (i) (hi : i ≤ 4)
    {p : Point} (hp : p ∈ inner S) (hpa : p ≠ b i) (hpb : p ≠ b (i + 1)) :
    turn (b i) (b (i + 1)) p < 0 := by
  have hab : b i ≠ b (i + 1) := fun hh ↦ by
    have := cfg.base_inj i (i + 1) (by omega) (by omega) hh
    omega
  exact lt_of_le_of_ne (cfg.base_support i hi p hp)
    (turn_ne_zero_of_generalPosition hgen (inner_subset _ (cfg.base_inner i (by omega)))
      (inner_subset _ (cfg.base_inner (i + 1) (by omega))) (inner_subset _ hp)
      hab hpa.symm hpb.symm)

theorem chain_turn_ne (hgen : ¬HasThreeCollinear S) {x : Point} (hx : x ∈ S)
    (i) (hi : i ≤ 3) (ha : shortChain b c d i ≠ x)
    (hb : shortChain b c d (i + 1) ≠ x) :
    turn (shortChain b c d i) (shortChain b c d (i + 1)) x ≠ 0 :=
  turn_ne_zero_of_generalPosition hgen (inner_subset _ (cfg.chain_inner i (by omega)))
    (inner_subset _ (cfg.chain_inner (i + 1) (by omega))) hx
    (cfg.chain_ne i (i + 1) (by omega) (by omega) (by omega)) ha hb

theorem center_chord : turn (c 0) d (c 4) ≤ 0 := by
  have hall : ∀ p ∈ Set.range (fun i : Fin 5 ↦ c i), turn (c 4) (c 0) p ≤ 0 := by
    rintro p ⟨i, rfl⟩
    fin_cases i
    · simp
    · convert (cfg.apex_triples 0 1 4 (by decide) (by decide) (by decide)).le using 1 <;> unfold turn <;> ring
    · convert (cfg.apex_triples 0 2 4 (by decide) (by decide) (by decide)).le using 1 <;> unfold turn <;> ring
    · convert (cfg.apex_triples 0 3 4 (by decide) (by decide) (by decide)).le using 1 <;> unfold turn <;> ring
    · simp
  have hh := turn_nonpos_of_mem_convexHull hall cfg.center_cap
  convert hh using 1 <;> unfold turn <;> ring

theorem neighbor_mem_ne (k) (hk : 1 ≤ k) (hkm : k ≤ 3) {q : Point}
    (hq : q ∈ neighbors (shortChain b c d) b k) :
    q ∈ inner S ∧ shortChain b c d k ≠ q := by
  rcases neighbor_cases _ _ k hk hkm hq with rfl | rfl | ⟨j, hj, hjm, rfl⟩
  · exact ⟨cfg.chain_inner _ (by omega), cfg.chain_ne _ _ (by omega) (by omega) (by omega)⟩
  · exact ⟨cfg.chain_inner _ (by omega), cfg.chain_ne _ _ (by omega) (by omega) (by omega)⟩
  · exact ⟨cfg.base_inner j (by omega), cfg.internal_ne_base k j hk hkm (by omega)⟩

theorem neighbor_turn_ne (hgen : ¬HasThreeCollinear S) {x : Point} (hx : x ∈ S)
    (k) (hk : 1 ≤ k) (hkm : k ≤ 3) (hkx : shortChain b c d k ≠ x)
    {q : Point} (hq : q ∈ neighbors (shortChain b c d) b k) (hqx : q ≠ x) :
    turn (shortChain b c d k) q x ≠ 0 :=
  turn_ne_zero_of_generalPosition hgen (inner_subset _ (cfg.chain_inner k (by omega)))
    (inner_subset _ (cfg.neighbor_mem_ne k hk hkm hq).1) hx
    (cfg.neighbor_mem_ne k hk hkm hq).2 hkx hqx

/-- Retained outer vertices support all four edges of the shortened
chain. Exclusion of actual sectors excludes the smaller raw sectors. -/
theorem retained_support (hgen : ¬HasThreeCollinear S) {x : Point}
    (hx : x ∈ extremeLayer S)
    (hout : ∀ i, i ≤ 4 → x ∉ sector ![b i, c i, b (i + 1)]) :
    ∀ k, k ≤ 3 → turn (shortChain b c d k) (shortChain b c d (k + 1)) x < 0 := by
  have hnot (p) (hp : p ∈ inner S) : p ≠ x := by
    intro heq
    exact (Finset.mem_sdiff.mp hp).2 (heq.symm ▸ hx)
  apply exterior_support (B := extremeLayer (inner S)) (shortChain b c d) b
  · rw [convexHull_extremeLayer]
    exact extreme_not_mem_convexHull_inner hx
  · exact cfg.chain_mem_hull
  · exact cfg.base_mem_hull
  · exact cfg.local_hulls
  · intro k hk
    exact cfg.chain_turn_ne hgen (extremeLayer_subset _ hx) k hk
      (hnot _ (cfg.chain_inner k (by omega))) (hnot _ (cfg.chain_inner (k + 1) (by omega)))
  · intro k hk hkm q hq
    exact cfg.neighbor_turn_ne hgen (extremeLayer_subset _ hx) k hk hkm
      (hnot _ (cfg.chain_inner k (by omega))) hq (hnot _ (cfg.neighbor_mem_ne k hk hkm hq).1)
  · simpa [shortChain] using hout 0 (by decide)
  · intro k hk hkm hh
    apply hout k (by omega)
    have hcap : c k ∈ triangleHull d (b k) (b (k + 1)) := by
      rw [triangleHull_swap_last]
      exact strictlyInsideTriangle_mem_triangleHull (cfg.fan k (by omega))
    apply Lax56Proofs.ValtrSectors.sector_triangle_mono
      hcap
      (cfg.apex_ne_base k k (by omega) (by omega))
      (cfg.apex_ne_base k (k + 1) (by omega) (by omega))
    simpa [shortChain] using hh
  · simpa [shortChain] using hout 4 (by decide)
  · rfl
  · rfl

/-- The first base endpoint lies to the right of every chain edge. -/
theorem first_support (hgen : ¬HasThreeCollinear S) :
    ∀ k, k ≤ 3 → turn (shortChain b c d k) (shortChain b c d (k + 1)) (b 0) ≤ 0 := by
  let h := shortChain b c d
  have hB := extremeLayer_convexPosition (inner S)
  obtain ⟨l, hl⟩ := exists_strict_linear_support hB (cfg.base_mem 0 (by decide))
  have hhne (k) (hk : 1 ≤ k) (hkm : k ≤ 4) : h k ≠ b 0 :=
    cfg.chain_ne k 0 hkm (by decide) (by omega)
  have hbne (k) (hk : 1 ≤ k) (hkm : k ≤ 5) : b k ≠ b 0 := fun heq ↦ by
    have := cfg.base_inj k 0 hkm (by decide) heq
    omega
  have hY (k) (hk : 1 ≤ k) (hkm : k ≤ 4) : l (b 0) < l (h k) :=
    linear_support_strict_on_hull (cfg.base_mem 0 (by decide)) l hl
      (cfg.chain_mem_hull k hkm) (hhne k hk hkm)
  have hbY (k) (hk : 1 ≤ k) (hkm : k ≤ 5) : l (b 0) < l (b k) :=
    linear_support_strict_on_hull (cfg.base_mem 0 (by decide)) l hl
      (cfg.base_mem_hull k hkm) (hbne k hk hkm)
  have hqne (k) (hk : 2 ≤ k) (hkm : k ≤ 3) {q : Point}
      (hq : q ∈ neighbors h b k) : q ≠ b 0 := by
    rcases neighbor_cases _ _ k (by omega) hkm hq with rfl | rfl | ⟨j, hj, hjm, rfl⟩
    · exact hhne _ (by omega) (by omega)
    · exact hhne _ (by omega) (by omega)
    · exact hbne _ (by omega) (by omega)
  have hdesc : ∀ k, 1 ≤ k → k ≤ 3 → turn (h k) (h (k + 1)) (b 0) < 0 := by
    apply support_without_first_of_positive_height l h b (hY 1 (by decide) (by decide)) hY hbY
    · intro k hk hkm
      exact cfg.local_hulls k (by omega) hkm
    · intro k hk hkm
      exact cfg.chain_turn_ne hgen (inner_subset _ (cfg.base_inner 0 (by decide))) k hkm
        (hhne k hk (by omega)) (hhne (k + 1) (by omega) (by omega))
    · intro k hk hkm q hq
      exact cfg.neighbor_turn_ne hgen (inner_subset _ (cfg.base_inner 0 (by decide))) k
        (by omega) hkm (hhne k (by omega) (by omega)) hq (hqne k hk hkm hq)
    · intro k hk hkm hx
      have hp : 0 < turn (b k) (b (k + 1)) (b 0) := hx 0 2 (by decide)
      exact not_lt_of_ge (cfg.base_support k (by omega) _ (cfg.base_inner 0 (by decide))) hp
    · intro hx
      have hp : 0 < turn (b 4) (b 5) (b 0) := hx 0 2 (by decide)
      exact not_lt_of_ge (cfg.base_support 4 (by decide) _ (cfg.base_inner 0 (by decide))) hp
    · change turn (c 0) d (b 0) < 0
      convert neg_neg_of_pos (cfg.fan 0 (by decide)).2.2 using 1 <;> unfold turn <;> ring
    · rfl
  intro k hk
  by_cases hk0 : k = 0
  · subst k; simp [shortChain]
  · exact (hdesc k (by omega) hk).le

/-- The last base endpoint lies to the right of every chain edge. -/
theorem last_support (hgen : ¬HasThreeCollinear S) :
    ∀ k, k ≤ 3 → turn (shortChain b c d k) (shortChain b c d (k + 1)) (b 5) ≤ 0 := by
  let h := shortChain b c d
  have hB := extremeLayer_convexPosition (inner S)
  obtain ⟨l, hl⟩ := exists_strict_linear_support hB (cfg.base_mem 5 (by decide))
  have hhne (k) (hk : k ≤ 3) : h k ≠ b 5 :=
    cfg.chain_ne k 4 (by omega) (by decide) (by omega)
  have hbne (k) (hk : k ≤ 4) : b k ≠ b 5 := fun heq ↦ by
    have := cfg.base_inj k 5 (by omega) (by decide) heq
    omega
  have hY (k) (hk : k ≤ 3) : l (b 5) < l (h k) :=
    linear_support_strict_on_hull (cfg.base_mem 5 (by decide)) l hl
      (cfg.chain_mem_hull k (by omega)) (hhne k hk)
  have hbY (k) (hk : k ≤ 4) : l (b 5) < l (b k) :=
    linear_support_strict_on_hull (cfg.base_mem 5 (by decide)) l hl
      (cfg.base_mem_hull k (by omega)) (hbne k hk)
  have hqne (k) (hk : 1 ≤ k) (hkm : k ≤ 2) {q : Point}
      (hq : q ∈ neighbors h b k) : q ≠ b 5 := by
    rcases neighbor_cases _ _ k hk (by omega) hq with rfl | rfl | ⟨j, hj, hjm, rfl⟩
    · exact hhne _ (by omega)
    · exact hhne _ (by omega)
    · exact hbne _ (by omega)
  have hdesc : ∀ k, k ≤ 2 → turn (h k) (h (k + 1)) (b 5) < 0 := by
    apply support_without_last_of_positive_height l h b (hY 0 (by decide)) hY hbY
    · intro k hk hkm
      exact cfg.local_hulls k hk (by omega)
    · intro k hk
      exact cfg.chain_turn_ne hgen (inner_subset _ (cfg.base_inner 5 (by decide))) k (by omega)
        (hhne k (by omega)) (hhne (k + 1) (by omega))
    · intro k hk hkm q hq
      exact cfg.neighbor_turn_ne hgen (inner_subset _ (cfg.base_inner 5 (by decide))) k
        hk (by omega) (hhne k (by omega)) hq (hqne k hk hkm hq)
    · intro hx
      have hp : 0 < turn (b 0) (b 1) (b 5) := hx 0 2 (by decide)
      exact not_lt_of_ge (cfg.base_support 0 (by decide) _ (cfg.base_inner 5 (by decide))) hp
    · intro k hk hkm hx
      have hp : 0 < turn (b k) (b (k + 1)) (b 5) := hx 0 2 (by decide)
      exact not_lt_of_ge (cfg.base_support k (by omega) _ (cfg.base_inner 5 (by decide))) hp
    · rfl
    · change turn d (c 4) (b 5) < 0
      convert neg_neg_of_pos (cfg.fan 4 (by decide)).1 using 1 <;> unfold turn <;> ring
  intro k hk
  by_cases hk3 : k = 3
  · subst k; simp [shortChain]
  · exact (hdesc k (by omega)).le

theorem chain_support (hgen : ¬HasThreeCollinear S) :
    ∀ k, k ≤ 3 → ∀ j, j ≤ 4 →
      turn (shortChain b c d k) (shortChain b c d (k + 1)) (shortChain b c d j) ≤ 0 := by
  have hleftTri : StrictlyInsideTriangle (b 0) d (b 1) (c 0) :=
    ⟨(cfg.fan 0 (by decide)).2.2, (cfg.fan 0 (by decide)).1, (cfg.fan 0 (by decide)).2.1⟩
  have hrightTri : StrictlyInsideTriangle (b 4) d (b 5) (c 4) :=
    ⟨(cfg.fan 4 (by decide)).2.2, (cfg.fan 4 (by decide)).1, (cfg.fan 4 (by decide)).2.1⟩
  have hleft : turn (b 0) (c 0) (c 4) ≤ 0 := by
    apply first_edge_support_of_empty_triangle hleftTri cfg.center_chord
    · rw [turn_swap_first]
      exact neg_pos.mpr (cfg.base_strict hgen 0 (by decide)
        (inner_subset _ (cfg.apex_inner 4 (by decide)))
        (cfg.apex_ne_base 4 0 (by decide) (by decide))
        (cfg.apex_ne_base 4 1 (by decide) (by decide)))
    · exact cfg.empty_triangle 0 (by decide) _ (inner_subset _ (cfg.apex_inner 4 (by decide)))
  have hcenter : turn d (c 4) (c 0) ≤ 0 := by
    convert cfg.center_chord using 1 <;> unfold turn <;> ring
  have hright : turn (c 4) (b 5) (c 0) ≤ 0 := by
    apply last_edge_support_of_empty_triangle hrightTri hcenter
    · rw [turn_swap_first]
      exact neg_pos.mpr (cfg.base_strict hgen 4 (by decide)
        (inner_subset _ (cfg.apex_inner 0 (by decide)))
        (cfg.apex_ne_base 0 4 (by decide) (by decide))
        (cfg.apex_ne_base 0 5 (by decide) (by decide)))
    · exact cfg.empty_triangle 4 (by decide) _ (inner_subset _ (cfg.apex_inner 0 (by decide)))
  have hleftD : turn (b 0) (c 0) d ≤ 0 := by
    rw [turn_swap_last]
    exact (neg_neg_of_pos hleftTri.1).le
  have hrightD : turn (c 4) (b 5) d ≤ 0 := by
    convert (neg_neg_of_pos (cfg.fan 4 (by decide)).1).le using 1 <;> unfold turn <;> ring
  have hc := cfg.center_chord
  intro k hk j hj
  by_cases hj0 : j = 0
  · subst j; exact cfg.first_support hgen k hk
  by_cases hj4 : j = 4
  · subst j; exact cfg.last_support hgen k hk
  have hj1 : 1 ≤ j := by omega
  have hj3 : j ≤ 3 := by omega
  interval_cases k <;> interval_cases j <;> simp_all [shortChain]

/-- Replacing at most five deleted outer vertices by the supported
five-point shortened chain contradicts minimality of the outer layer. -/
theorem not_minimal_of_removed_card_le (hgen : ¬HasThreeCollinear S)
    {R : Finset Point} (hR : R ⊆ extremeLayer S)
    (hout : ∀ x ∈ R, ∀ i, i ≤ 4 → x ∉ sector ![b i, c i, b (i + 1)])
    (hcard : (extremeLayer S \ R).card ≤ 5) : ¬MinimalOuter S := by
  let v : Fin 5 → Point := fun i ↦ shortChain b c d i
  apply Lax56Proofs.ValtrSplice.not_minimal_of_supported_splice_clockwise hgen hR
    (m := 3) v
  · intro i j heq
    exact Fin.ext (cfg.chain_inj i j (by omega) (by omega) heq)
  · intro i
    exact cfg.chain_inner i (by omega)
  · intro i j
    exact cfg.chain_support hgen i (by omega) j (by omega)
  · intro i p hp
    exact (cfg.retained_support hgen (hR hp) (hout p hp) i (by omega)).le
  · exact hcard

end FiveSectorConfig
end Lax56Proofs.ValtrShortSplice
