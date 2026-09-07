import Lax56Proofs.ValtrProjective
import Lax56Proofs.ValtrLocalSupport
import Lax56Proofs.ValtrSplice

namespace Lax56Proofs.ValtrRunSupport

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrProjective
open Lax56Proofs.ValtrLocalSupport Lax56Proofs.ValtrSplice
open scoped Classical

/-- The geometric data of a clockwise run, before the endpoint case
split. No supporting-line or local hull conclusion is a field. -/
structure RunGeometry (S : Finset Point) (m : ℕ) (b h : ℕ → Point) (d : Point) : Prop where
  length : 2 ≤ m
  first : h 0 = b 1
  last : h (m + 1) = b (m + 1)
  base_mem : ∀ i, 1 ≤ i → i ≤ m + 1 → b i ∈ extremeLayer (inner S)
  apex_mem : ∀ i, 1 ≤ i → i ≤ m → h i ∈ extremeLayer (inner (inner S))
  chain_inj : ∀ i j, i ≤ m + 1 → j ≤ m + 1 → h i = h j → i = j
  base_inj : ∀ i j, 1 ≤ i → i ≤ m + 1 → 1 ≤ j → j ≤ m + 1 → b i = b j → i = j
  base_support : ∀ i, 1 ≤ i → i ≤ m → ∀ p ∈ inner S, turn (b i) (b (i + 1)) p ≤ 0
  apex_triples : ∀ i j k, 1 ≤ i → i < j → j < k → k ≤ m → turn (h i) (h j) (h k) < 0
  fan : ∀ i, 1 ≤ i → i ≤ m → StrictlyInsideTriangle d (b (i + 1)) (b i) (h i)
  deep : d ∈ inner (inner (inner S))
  empty_triangle : ∀ i, 1 ≤ i → i ≤ m → ∀ p ∈ inner S,
    p ∈ triangleHull (b i) (h i) (b (i + 1)) → p = b i ∨ p = h i ∨ p = b (i + 1)

/-- The nonconvex-endpoint branch of a run. Neither minimality nor
absence of a hexagon is a field. -/
structure RunConfig (S : Finset Point) (m : ℕ) (b h : ℕ → Point) (d : Point) : Prop
    extends RunGeometry S m b h d where
  first_interior : StrictlyInsideTriangle (b 1) (h 2) (b 2) (h 1)
  last_interior : StrictlyInsideTriangle (b m) (h (m - 1)) (b (m + 1)) (h m)

namespace RunGeometry

variable {S : Finset Point} {m : ℕ} {b h : ℕ → Point} {d : Point}
variable (cfg : RunGeometry S m b h d)
include cfg

theorem base_inner (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m + 1) : b i ∈ inner S :=
  extremeLayer_subset _ (cfg.base_mem i hi him)

theorem chain_inner (i : ℕ) (hi : i ≤ m + 1) : h i ∈ inner S := by
  by_cases hi0 : i = 0
  · subst i; rw [cfg.first]; exact cfg.base_inner 1 (by decide) (by omega)
  by_cases hiLast : i = m + 1
  · subst i; rw [cfg.last]; exact cfg.base_inner (m + 1) (by omega) le_rfl
  exact inner_subset _ (extremeLayer_subset _ (cfg.apex_mem i (by omega) (by omega)))

theorem chain_mem_hull (i : ℕ) (hi : i ≤ m + 1) :
    h i ∈ convexHull ℝ (extremeLayer (inner S) : Set Point) := by
  rw [convexHull_extremeLayer]
  exact subset_convexHull ℝ _ (cfg.chain_inner i hi)

theorem base_mem_hull (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m + 1) :
    b i ∈ convexHull ℝ (extremeLayer (inner S) : Set Point) :=
  subset_convexHull ℝ _ (cfg.base_mem i hi him)

theorem apex_ne_base (i j : ℕ) (hi : 1 ≤ i) (him : i ≤ m)
    (hj : 1 ≤ j) (hjm : j ≤ m + 1) : h i ≠ b j := by
  intro heq
  have hiI := extremeLayer_subset _ (cfg.apex_mem i hi him)
  exact (Finset.mem_sdiff.mp hiI).2 (heq.symm ▸ cfg.base_mem j hj hjm)

theorem chain_ne (i j : ℕ) (hi : i ≤ m + 1) (hj : j ≤ m + 1) (hij : i ≠ j) : h i ≠ h j :=
  fun heq ↦ hij (cfg.chain_inj i j hi hj heq)

theorem base_strict (hgen : ¬HasThreeCollinear S) (i : ℕ)
    (hi : 1 ≤ i) (him : i ≤ m) {p : Point} (hp : p ∈ inner S)
    (hpa : p ≠ b i) (hpb : p ≠ b (i + 1)) : turn (b i) (b (i + 1)) p < 0 := by
  have hab : b i ≠ b (i + 1) := by
    intro heq
    have hh := cfg.base_inj i (i + 1) hi (by omega) (by omega) (by omega) heq
    omega
  exact lt_of_le_of_ne (cfg.base_support i hi him p hp)
    (turn_ne_zero_of_generalPosition hgen
      (inner_subset S (cfg.base_inner i hi (by omega)))
      (inner_subset S (cfg.base_inner (i + 1) (by omega) (by omega)))
      (inner_subset S hp) hab hpa.symm hpb.symm)

theorem intermediate_left (i : ℕ) (hi : 1 ≤ i) (him : i < m) :
    0 < turn (h i) (h (i + 1)) (b (i + 1)) := by
  apply intermediate_vertex_left_of_chord (cfg.base_mem (i + 1) (by omega) (by omega))
    (inner_subset _ cfg.deep) (extremeLayer_subset _ (cfg.apex_mem i hi (by omega)))
    (extremeLayer_subset _ (cfg.apex_mem (i + 1) (by omega) (by omega)))
  · rw [turn_swap_last]
    exact neg_neg_of_pos (cfg.fan i hi (by omega)).1
  · rw [turn_swap_first]
    exact neg_neg_of_pos (cfg.fan (i + 1) (by omega) (by omega)).2.2

end RunGeometry

namespace RunConfig

variable {S : Finset Point} {m : ℕ} {b h : ℕ → Point} {d : Point}
variable (cfg : RunConfig S m b h d)
include cfg

theorem local_hulls (hgen : ¬HasThreeCollinear S) :
    ∀ k, 1 ≤ k → k ≤ m → h k ∈ convexHull ℝ
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point) := by
  apply local_hulls_of_run_signs h b cfg.length cfg.first_interior cfg.last_interior
    cfg.apex_triples cfg.intermediate_left
  · intro k hk hkm
    exact cfg.base_strict hgen k hk hkm (cfg.chain_inner k (by omega))
      (cfg.apex_ne_base k k hk hkm hk (by omega))
      (cfg.apex_ne_base k (k + 1) hk hkm (by omega) (by omega))
  · intro k hk hkm
    exact turn_ne_zero_of_generalPosition hgen
      (inner_subset S (cfg.chain_inner k (by omega)))
      (inner_subset S (cfg.chain_inner (k - 1) (by omega)))
      (inner_subset S (cfg.base_inner (k + 1) (by omega) (by omega)))
      (cfg.chain_ne k (k - 1) (by omega) (by omega) (by omega))
      (cfg.apex_ne_base k (k + 1) (by omega) (by omega) (by omega) (by omega))
      (cfg.apex_ne_base (k - 1) (k + 1) (by omega) (by omega) (by omega) (by omega))

end RunConfig

namespace RunGeometry

variable {S : Finset Point} {m : ℕ} {b h : ℕ → Point} {d : Point}
variable (cfg : RunGeometry S m b h d)
include cfg

theorem neighbor_mem_ne (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) {q : Point}
    (hq : q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point)) :
    q ∈ inner S ∧ h k ≠ q := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨cfg.chain_inner _ (by omega), cfg.chain_ne _ _ (by omega) (by omega) (by omega)⟩
  · exact ⟨cfg.base_inner _ hk (by omega), cfg.apex_ne_base _ _ hk hkm hk (by omega)⟩
  · exact ⟨cfg.base_inner _ (by omega) (by omega),
      cfg.apex_ne_base _ _ hk hkm (by omega) (by omega)⟩
  · exact ⟨cfg.chain_inner _ (by omega), cfg.chain_ne _ _ (by omega) (by omega) (by omega)⟩

theorem chain_turn_ne (hgen : ¬HasThreeCollinear S) {x : Point} (hx : x ∈ S)
    (i : ℕ) (hi : i ≤ m) (hix : h i ≠ x) (hinext : h (i + 1) ≠ x) :
    turn (h i) (h (i + 1)) x ≠ 0 :=
  turn_ne_zero_of_generalPosition hgen
    (inner_subset S (cfg.chain_inner i (by omega)))
    (inner_subset S (cfg.chain_inner (i + 1) (by omega))) hx
    (cfg.chain_ne _ _ (by omega) (by omega) (by omega)) hix hinext

theorem neighbor_turn_ne (hgen : ¬HasThreeCollinear S) {x : Point} (hx : x ∈ S)
    (i : ℕ) (hi : 1 ≤ i) (him : i ≤ m) (hix : h i ≠ x)
    (hnx : ∀ q ∈ ({h (i - 1), b i, b (i + 1), h (i + 1)} : Set Point), q ≠ x) :
    ∀ q ∈ ({h (i - 1), b i, b (i + 1), h (i + 1)} : Set Point), turn (h i) q x ≠ 0 := by
  intro q hq
  obtain ⟨hqI, hhiq⟩ := cfg.neighbor_mem_ne i hi him hq
  exact turn_ne_zero_of_generalPosition hgen
    (inner_subset S (cfg.chain_inner i (by omega))) (inner_subset S hqI) hx hhiq hix (hnx q hq)

theorem base_ne_first (k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m + 1) : b k ≠ h 0 := by
  intro hh
  rw [cfg.first] at hh
  have hh := cfg.base_inj k 1 (by omega) hkm (by decide) (by omega) hh
  omega

theorem base_ne_last (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ m) : b k ≠ h (m + 1) := by
  intro hh
  rw [cfg.last] at hh
  have hh := cfg.base_inj k (m + 1) hk (by omega) (by omega) le_rfl hh
  omega

theorem internal_local_hull (hgen : ¬HasThreeCollinear S)
    (k : ℕ) (hk : 2 ≤ k) (hkm : k < m) :
    h k ∈ convexHull ℝ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point) := by
  have hprev := cfg.intermediate_left (k - 1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at hprev
  have hnext := cfg.intermediate_left k (by omega) hkm
  apply mem_neighbor_hull_of_four_clockwise_turns
  · rw [turn_swap_first]; exact neg_neg_of_pos hprev
  · convert neg_neg_of_pos (cfg.fan k (by omega) (by omega)).2.1 using 1 <;>
      unfold turn <;> ring
  · rw [turn_swap_last]; exact neg_neg_of_pos hnext
  · convert cfg.apex_triples (k - 1) k (k + 1) (by omega) (by omega) (by omega) (by omega)
      using 1 <;> unfold turn <;> ring
  · exact turn_ne_zero_of_generalPosition hgen
      (inner_subset S (cfg.chain_inner k (by omega)))
      (inner_subset S (cfg.chain_inner (k - 1) (by omega)))
      (inner_subset S (cfg.base_inner (k + 1) (by omega) (by omega)))
      (cfg.chain_ne k (k - 1) (by omega) (by omega) (by omega))
      (cfg.apex_ne_base k (k + 1) (by omega) (by omega) (by omega) (by omega))
      (cfg.apex_ne_base (k - 1) (k + 1) (by omega) (by omega) (by omega) (by omega))

theorem tail_local_hulls (hgen : ¬HasThreeCollinear S)
    (hlast : StrictlyInsideTriangle (b m) (h (m - 1)) (b (m + 1)) (h m))
    (k : ℕ) (hk : 2 ≤ k) (hkm : k ≤ m) :
    h k ∈ convexHull ℝ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point) := by
  by_cases hlastIndex : k = m
  · subst k
    apply convexHull_mono (show ({b m, h (m - 1), b (m + 1)} : Set Point) ⊆
        {h (m - 1), b m, b (m + 1), h (m + 1)} by
      intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull hlast
  · exact cfg.internal_local_hull hgen k hk (by omega)

theorem head_local_hulls (hgen : ¬HasThreeCollinear S)
    (hfirst : StrictlyInsideTriangle (b 1) (h 2) (b 2) (h 1))
    (k : ℕ) (hk : 1 ≤ k) (hkm : k < m) :
    h k ∈ convexHull ℝ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point) := by
  by_cases hfirstIndex : k = 1
  · subst k
    apply convexHull_mono (show ({b 1, h 2, b 2} : Set Point) ⊆
        {h (1 - 1), b 1, b (1 + 1), h (1 + 1)} by
      intro p hp; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢; tauto)
    exact strictlyInsideTriangle_mem_triangleHull hfirst
  · exact cfg.internal_local_hull hgen k (by omega) hkm

end RunGeometry

namespace RunConfig

variable {S : Finset Point} {m : ℕ} {b h : ℕ → Point} {d : Point}
variable (cfg : RunConfig S m b h d)
include cfg

/-- The first base endpoint satisfies every chain-edge support. -/
theorem first_support (hgen : ¬HasThreeCollinear S) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) (h 0) ≤ 0 := by
  have h0B : h 0 ∈ extremeLayer (inner S) := by
    rw [cfg.first]; exact cfg.base_mem 1 (by decide) (by omega)
  have h0S : h 0 ∈ S := inner_subset S (cfg.chain_inner 0 (by omega))
  have hne0 (k) (hk : 1 ≤ k) (hkm : k ≤ m + 1) : h k ≠ h 0 :=
    cfg.chain_ne k 0 hkm (by omega) (by omega)
  have hNne (k) (hk : 2 ≤ k) (hkm : k ≤ m) :
      ∀ q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), q ≠ h 0 := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hne0 _ (by omega) (by omega)
    · exact cfg.base_ne_first _ hk (by omega)
    · exact cfg.base_ne_first _ (by omega) (by omega)
    · exact hne0 _ (by omega) (by omega)
  have hdesc : turn (h 1) (h 2) (h 0) < 0 := by
    rw [cfg.first]
    convert neg_neg_of_pos cfg.first_interior.1 using 1 <;> unfold turn <;> ring
  have hout (k) (hk : 2 ≤ k) (hkm : k ≤ m) :
      h 0 ∉ sector ![b k, h k, b (k + 1)] := by
    intro hs
    have hh := cfg.base_strict hgen k (by omega) hkm (cfg.chain_inner 0 (by omega))
      (cfg.base_ne_first k hk (by omega)).symm
      (cfg.base_ne_first (k + 1) (by omega) (by omega)).symm
    have hp : 0 < turn (b k) (b (k + 1)) (h 0) := hs 0 2 (by decide)
    linarith
  exact first_endpoint_chain_support (extremeLayer_convexPosition (inner S)) h b cfg.length h0B
    (fun k _ hk ↦ cfg.chain_mem_hull k hk) (fun k hk hkm ↦ cfg.base_mem_hull k (by omega) hkm)
    hne0 cfg.base_ne_first cfg.last hdesc
    (fun k hk hkm ↦ cfg.local_hulls hgen k (by omega) hkm)
    (fun k hk hkm ↦ cfg.chain_turn_ne hgen h0S k hkm
      (hne0 k hk (by omega)) (hne0 (k + 1) (by omega) (by omega)))
    (fun k hk hkm ↦ cfg.neighbor_turn_ne hgen h0S k (by omega) hkm
      (hne0 k (by omega) (by omega)) (hNne k hk hkm)) hout

/-- The last base endpoint satisfies every chain-edge support. -/
theorem last_support (hgen : ¬HasThreeCollinear S) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) (h (m + 1)) ≤ 0 := by
  have hmB : h (m + 1) ∈ extremeLayer (inner S) := by
    rw [cfg.last]; exact cfg.base_mem _ (by omega) le_rfl
  have hmS : h (m + 1) ∈ S := inner_subset S (cfg.chain_inner _ le_rfl)
  have hnem (k) (hkm : k ≤ m) : h k ≠ h (m + 1) :=
    cfg.chain_ne k (m + 1) (by omega) le_rfl (by omega)
  have hNne (k) (hk : 1 ≤ k) (hkm : k < m) :
      ∀ q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), q ≠ h (m + 1) := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hnem _ (by omega)
    · exact cfg.base_ne_last _ hk (by omega)
    · exact cfg.base_ne_last _ (by omega) (by omega)
    · exact hnem _ (by omega)
  have hdesc : turn (h (m - 1)) (h m) (h (m + 1)) < 0 := by
    rw [cfg.last]
    convert neg_neg_of_pos cfg.last_interior.2.1 using 1 <;> unfold turn <;> ring
  have hout (k) (hk : 1 ≤ k) (hkm : k < m) :
      h (m + 1) ∉ sector ![b k, h k, b (k + 1)] := by
    intro hs
    have hh := cfg.base_strict hgen k hk (by omega) (cfg.chain_inner _ le_rfl)
      (cfg.base_ne_last k hk (by omega)).symm
      (cfg.base_ne_last (k + 1) (by omega) (by omega)).symm
    have hp : 0 < turn (b k) (b (k + 1)) (h (m + 1)) := hs 0 2 (by decide)
    linarith
  exact last_endpoint_chain_support (extremeLayer_convexPosition (inner S)) h b cfg.length hmB
    (fun k hk ↦ cfg.chain_mem_hull k (by omega))
    (fun k hk hkm ↦ cfg.base_mem_hull k hk (by omega)) hnem cfg.base_ne_last cfg.first hdesc
    (fun k hk hkm ↦ cfg.local_hulls hgen k hk (by omega))
    (fun k hk ↦ cfg.chain_turn_ne hgen hmS k (by omega) (hnem k (by omega)) (hnem (k + 1) (by omega)))
    (fun k hk hkm ↦ cfg.neighbor_turn_ne hgen hmS k hk (by omega)
      (hnem k (by omega)) (hNne k hk hkm)) hout

theorem apex_edge_support (i j : ℕ) (hi : 1 ≤ i) (him : i < m)
    (hj : 1 ≤ j) (hjm : j ≤ m) : turn (h i) (h (i + 1)) (h j) ≤ 0 := by
  by_cases hji : j = i
  · subst j; simp
  by_cases hjnext : j = i + 1
  · subst j; simp
  by_cases hjlt : j < i
  · convert (cfg.apex_triples j i (i + 1) hj hjlt (by omega) (by omega)).le using 1 <;>
      unfold turn <;> ring
  · exact (cfg.apex_triples i (i + 1) j hi (by omega) (by omega) hjm).le

/-- Every chain vertex lies on the right of every open chain edge. The
two endpoint viewpoints and the empty end triangles are both included. -/
theorem chain_support (hgen : ¬HasThreeCollinear S) :
    ∀ i j, i ≤ m → j ≤ m + 1 → turn (h i) (h (i + 1)) (h j) ≤ 0 := by
  intro i j hi hj
  by_cases hj0 : j = 0
  · subst j; exact cfg.first_support hgen i hi
  by_cases hjlast : j = m + 1
  · subst j; exact cfg.last_support hgen i hi
  have hjpos : 1 ≤ j := by omega
  have hjm : j ≤ m := by omega
  have hbase (k) (hk : 1 ≤ k) (hkm : k ≤ m) : 0 < turn (b (k + 1)) (b k) (h j) := by
    rw [turn_swap_first]
    exact neg_pos.mpr (cfg.base_strict hgen k hk hkm (cfg.chain_inner j hj)
      (cfg.apex_ne_base j k hjpos hjm hk (by omega))
      (cfg.apex_ne_base j (k + 1) hjpos hjm (by omega) (by omega)))
  by_cases hi0 : i = 0
  · subst i
    rw [cfg.first]
    apply first_edge_support_of_empty_triangle cfg.first_interior
      (cfg.apex_edge_support 1 j (by decide) (by have := cfg.length; omega) hjpos hjm)
      (hbase 1 (by decide) (by have := cfg.length; omega))
    exact cfg.empty_triangle 1 (by decide) (by have := cfg.length; omega) _ (cfg.chain_inner j hj)
  by_cases him : i = m
  · subst i
    rw [cfg.last]
    apply last_edge_support_of_empty_triangle cfg.last_interior
      (by simpa only [Nat.sub_add_cancel (by have := cfg.length; omega : 1 ≤ m)] using
        cfg.apex_edge_support (m - 1) j (by have := cfg.length; omega) (by have := cfg.length; omega) hjpos hjm)
      (hbase m (by have := cfg.length; omega) le_rfl)
    exact cfg.empty_triangle m (by have := cfg.length; omega) le_rfl _ (cfg.chain_inner j hj)
  exact cfg.apex_edge_support i j (by omega) (by omega) hjpos hjm

/-- All retained outer vertices satisfy every strict chain support. -/
theorem retained_support (hgen : ¬HasThreeCollinear S) {x : Point}
    (hx : x ∈ extremeLayer S)
    (hout : ∀ k, 1 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)]) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) x < 0 := by
  have hxout : x ∉ convexHull ℝ (extremeLayer (inner S) : Set Point) := by
    rw [convexHull_extremeLayer]
    exact extreme_not_mem_convexHull_inner hx
  have hneX {p : Point} (hp : p ∈ inner S) : p ≠ x := by
    intro heq
    exact (Finset.mem_sdiff.mp hp).2 (heq.symm ▸ hx)
  apply exterior_chain_support h b (by have := cfg.length; omega) hxout
    cfg.chain_mem_hull cfg.base_mem_hull cfg.last cfg.first (cfg.local_hulls hgen) _ _ hout
  · intro k hk
    exact turn_ne_zero_of_generalPosition hgen
      (inner_subset S (cfg.chain_inner k (by omega)))
      (inner_subset S (cfg.chain_inner (k + 1) (by omega)))
      (extremeLayer_subset S hx) (cfg.chain_ne _ _ (by omega) (by omega) (by omega))
      (hneX (cfg.chain_inner k (by omega))) (hneX (cfg.chain_inner (k + 1) (by omega)))
  · intro k hk hkm q hq
    obtain ⟨hqI, hhkq⟩ := cfg.neighbor_mem_ne k hk hkm hq
    exact turn_ne_zero_of_generalPosition hgen
      (inner_subset S (cfg.chain_inner k (by omega))) (inner_subset S hqI)
      (extremeLayer_subset S hx) hhkq (hneX (cfg.chain_inner k (by omega))) (hneX hqI)

/-- The previously missing arbitrary-run replacement now contradicts
minimality, provided the counting step deletes at most `m + 2` vertices.
No chain-support inequality is left as a hypothesis. -/
theorem not_minimal_of_removed_card_le (hgen : ¬HasThreeCollinear S)
    {R : Finset Point} (hR : R ⊆ extremeLayer S)
    (hout : ∀ x ∈ R, ∀ k, 1 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)])
    (hremoved : (extremeLayer S \ R).card ≤ m + 2) : ¬MinimalOuter S := by
  apply not_minimal_of_supported_splice_clockwise hgen hR
    (fun i : Fin (m + 2) ↦ h i.val)
  · intro i j hij
    exact Fin.ext (cfg.chain_inj i.val j.val (by omega) (by omega) hij)
  · intro i; exact cfg.chain_inner i.val (by omega)
  · intro i j
    exact cfg.chain_support hgen i.val j.val (by omega) (by omega)
  · intro i x hx
    exact (cfg.retained_support hgen (hR hx) (hout x hx) i.val (by omega)).le
  · exact hremoved

end RunConfig

end Lax56Proofs.ValtrRunSupport
