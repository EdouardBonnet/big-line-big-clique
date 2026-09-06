import Lax56Proofs.FiniteIntervals
import Lax56Proofs.VertexRemovalStability
import Lax56Proofs.HujterKisfaludiBak
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Tactic

namespace Lax56Proofs.IntervalDensity

set_option exponentiation.threshold 512
set_option maxRecDepth 4096

open Lax56.Geometry
open Lax56Proofs.FiniteIntervals
open Lax56.VertexRemovalStability

/-- The Hujter--Kisfaludi-Bak threshold minus one. -/
def hkb : ℕ := 5 * 2 ^ 428

/-- The first interval length at which stability is applied. -/
def m₀ : ℕ := 10 * 2 ^ 428

/-- The stability parameter `ε₀/3500`. -/
noncomputable def eps₁ : ℝ := 1 / (3500 * (10 * 2 ^ 428 + 2))

/-- The non-edge density, strictly larger than `1/10`. -/
noncomputable def density : ℝ := 1 / 10 + eps₁

theorem hasFourCollinear_mono {A B : Finset Point} (hAB : A ⊆ B) :
    HasFourCollinear A → HasFourCollinear B := by
  rintro ⟨f, hf, hmem, hcol⟩
  exact ⟨f, hf, fun i ↦ hAB (hmem i), hcol⟩

theorem blockGraph_cliqueFree_six
    (P : Finset Point) (hvisible : ¬HasVisibleClique P 6)
    {s m : ℕ} (hs : s + m ≤ P.card) :
    (blockGraph P hs).CliqueFree 6 := by
  intro t ht
  apply hvisible
  let e : Fin 6 ≃ t := (Finset.equivFinOfCardEq ht.card_eq).symm
  let f : Fin 6 → Point := fun i ↦ blockPoint P hs (e i).1
  refine ⟨f, ?_, ?_, ?_⟩
  · exact (blockPoint_injective P hs).comp
      (Subtype.val_injective.comp e.injective)
  · intro i
    exact blockSet_subset P s m hs (blockPoint_mem P hs (e i).1)
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    have hij' : i ≠ j := by
      intro h
      apply hij
      exact congrArg f h
    have hadj : (blockGraph P hs).Adj (e i).1 (e j).1 :=
      ht.isClique (e i).2 (e j).2
        ((Subtype.val_injective.comp e.injective).ne hij')
    exact hadj

/-- A consecutive block of at least `5 * 2^428 + 1` points cannot have a 5-colourable
visibility graph. This is the direct block form of the HKB dependency. -/
theorem blockGraph_not_colorable_five
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    {s m : ℕ} (hs : s + m ≤ P.card) (hm : 5 * 2 ^ 428 + 1 ≤ m) :
    ¬(blockGraph P hs).Colorable 5 := by
  intro hc
  have hcard : 5 * 2 ^ 428 + 1 ≤ (blockSet P s m hs).card := by
    simpa using hm
  rcases Lax56Proofs.HujterKisfaludiBak.visibilityGraph_not_fiveColorable
      (blockSet P s m hs) hcard with hcol | hncol
  · exact hfour (hasFourCollinear_mono (blockSet_subset P s m hs) hcol)
  · apply hncol
    obtain ⟨C⟩ := hc
    exact ⟨C.comp (blockGraphIso P hs).symm.toHom⟩

/-- Lemma 2.2: deleting fewer than a `1/(10 * 2^428 + 2)` fraction of a sufficiently
long block cannot make its visibility graph 5-colourable. -/
private theorem window_gap {m L z : ℕ} (hLm : L ≤ m) (h : 2 * (z * L) < m) :
    z * L < m - L + 1 := by
  by_cases hz : z = 0
  · subst z
    omega
  · have hmul : L ≤ z * L := by
      simpa using Nat.mul_le_mul_right L (by omega : 1 ≤ z)
    omega

theorem deletion_distance_five
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    {s m : ℕ} (hs : s + m ≤ P.card) (hm : m₀ ≤ m)
    (Z : Set (Fin m))
    (hZ : (Nat.card Z : ℝ) < (m : ℝ) / (10 * 2 ^ 428 + 2)) :
    ¬((blockGraph P hs).induce Zᶜ).Colorable 5 := by
  intro hc
  have hNat : (10 * 2 ^ 428 + 2) * Nat.card Z < m := by
    have hR : (10 * 2 ^ 428 + 2 : ℝ) * Nat.card Z < m := by
      have : (0 : ℝ) < 10 * 2 ^ 428 + 2 := by positivity
      calc
        (10 * 2 ^ 428 + 2 : ℝ) * Nat.card Z <
            (10 * 2 ^ 428 + 2) * ((m : ℝ) / (10 * 2 ^ 428 + 2)) :=
          mul_lt_mul_of_pos_left hZ this
        _ = m := by
          norm_num
          ring
    exact_mod_cast hR
  have hLm : 5 * 2 ^ 428 + 1 ≤ m := by
    norm_num [m₀] at hm ⊢
    omega
  have hsmall : Nat.card Z * (5 * 2 ^ 428 + 1) < m - (5 * 2 ^ 428 + 1) + 1 := by
    apply window_gap hLm
    convert hNat using 1 <;> ring
  obtain ⟨w, hw⟩ := exists_disjoint_window (by norm_num) hLm Z hsmall
  have hsw : s + w.val + (5 * 2 ^ 428 + 1) ≤ P.card := by
    have hwlt := w.isLt
    omega
  apply blockGraph_not_colorable_five P hfour hsw (by norm_num)
  obtain ⟨C⟩ := hc
  refine ⟨SimpleGraph.Coloring.mk
    (fun i : Fin (5 * 2 ^ 428 + 1) ↦ C ⟨windowIndex hLm w i, by simpa using hw i⟩) ?_⟩
  intro i j hij
  apply C.valid
  rw [SimpleGraph.induce_adj]
  change (blockGraph P hs).Adj (windowIndex hLm w i) (windowIndex hLm w j)
  change Visible P (blockPoint P hs (windowIndex hLm w i))
    (blockPoint P hs (windowIndex hLm w j))
  simpa only [blockPoint_windowIndex P hs hLm w hsw] using hij

/-- For a graph on a finite type, the concept-layer edge count agrees with
Mathlib's finite edge set. -/
theorem edgeCount_eq_edgeFinset_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) : edgeCount G = G.edgeFinset.card := by
  rw [edgeCount, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
  rfl

/-- Edges and non-edges partition all unordered pairs of distinct vertices. -/
theorem edgeCount_add_compl {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeCount G + edgeCount Gᶜ = (Fintype.card V).choose 2 := by
  classical
  rw [edgeCount, edgeCount, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  rw [← Set.ncard_union_eq (SimpleGraph.disjoint_edgeSet.mpr disjoint_compl_right)]
  rw [← SimpleGraph.edgeSet_sup, sup_compl_eq_top, SimpleGraph.edgeSet_top]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact Sym2.card_diagSet_compl (α := V)

/-- The elementary upper bound `ex(m,K₆) ≤ (2/5)m²`. -/
theorem extremalNumber_six_le (m : ℕ) :
    (SimpleGraph.extremalNumber m (⊤ : SimpleGraph (Fin 6)) : ℝ) ≤
      (2 / 5 : ℝ) * (m : ℝ) ^ 2 := by
  rw [SimpleGraph.extremalNumber_top]
  change ((SimpleGraph.turanGraph m 5).edgeFinset.card : ℝ) ≤
    (2 / 5 : ℝ) * (m : ℝ) ^ 2
  have h := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := m) (r := 5)
  norm_num at h
  have hR : (10 : ℝ) * (SimpleGraph.turanGraph m 5).edgeFinset.card ≤
      4 * (m : ℝ) ^ 2 := by
    exact_mod_cast h
  nlinarith

/-- Stability and the HKB deletion obstruction force every sufficiently long
block visibility graph to lie a fixed positive distance below the Turán
number. -/
theorem visible_edge_upper
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6)
    {s m : ℕ} (hs : s + m ≤ P.card) (hm : m₀ ≤ m) :
    (edgeCount (blockGraph P hs) : ℝ) ≤
      SimpleGraph.extremalNumber m (⊤ : SimpleGraph (Fin 6)) -
        eps₁ * (m : ℝ) ^ 2 := by
  by_contra h
  push_neg at h
  have hm20 : 20 ≤ Fintype.card (Fin m) := by
    simp only [Fintype.card_fin]
    norm_num [m₀] at hm
    omega
  rcases Lax56Proofs.VertexRemovalStability.exists_fiveColorable_delete
      (blockGraph P hs) eps₁
      (by norm_num [eps₁]) (by norm_num [eps₁]) hm20
      (blockGraph_cliqueFree_six P hvisible hs)
      (by simpa only [Fintype.card_fin] using h) with ⟨Z, hZ, hcolor⟩
  apply deletion_distance_five P hfour hs hm Z
  · calc
      (Nat.card Z : ℝ) < 3500 * eps₁ * Fintype.card (Fin m) := hZ
      _ = (m : ℝ) / (10 * 2 ^ 428 + 2) := by
        simp only [Fintype.card_fin, eps₁]
        ring
  · exact hcolor

/-- Quantitative form of Lemma 2.2: at least
`(1/10+ε₁)m²-m/2` pairs in every long block are invisible. -/
theorem invisible_edge_lower
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6)
    {s m : ℕ} (hs : s + m ≤ P.card) (hm : m₀ ≤ m) :
    density * (m : ℝ) ^ 2 - (m : ℝ) / 2 ≤
      (edgeCount (blockGraph P hs)ᶜ : ℝ) := by
  let G := blockGraph P hs
  have hpartition := edgeCount_add_compl G
  have hpartitionR :
      (edgeCount G : ℝ) + (edgeCount Gᶜ : ℝ) =
        (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [← Nat.cast_add, hpartition, Nat.cast_choose_two]
    simp only [Fintype.card_fin, Nat.cast_ofNat]
  have hvis := visible_edge_upper P hfour hvisible hs hm
  have htur := extremalNumber_six_le m
  dsimp only [G] at hpartitionR
  unfold density
  nlinarith

end Lax56Proofs.IntervalDensity
