import Mathlib
import Lax56.VertexRemovalStability

open Finset Fintype
open SimpleGraph

namespace Lax56Proofs.VertexRemovalStability

universe u_1

noncomputable def ex5 (n : ℕ) : ℕ :=
  extremalNumber n (⊤ : SimpleGraph (Fin 6))

noncomputable def ecount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

lemma ecount_eq_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ecount G = #G.edgeFinset := by
  rw [ecount, @Nat.card_eq_fintype_card G.edgeSet G.fintypeEdgeSet,
    @card_edgeSet V G G.fintypeEdgeSet]

lemma ex5_formula (n : ℕ) : ex5 n = 2 * n ^ 2 / 5 := by
  rw [ex5, extremalNumber_top, card_edgeFinset_turanGraph]
  norm_num
  have hr : n % 5 < 5 := Nat.mod_lt _ (by omega)
  have hs : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by
    simpa only [pow_two] using Nat.mul_mod n n 5
  have hle : (n % 5) ^ 2 ≤ n ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.mod_le n 5) 2
  interval_cases h : n % 5 <;> norm_num [Nat.choose, h] at hs ⊢ <;> omega

lemma ex5_succ_diff (n : ℕ) (hn : 0 < n) :
    ex5 n = ex5 (n - 1) + 4 * n / 5 := by
  rw [ex5_formula, ex5_formula]
  have hid : n ^ 2 = (n - 1) ^ 2 + (2 * n - 1) := by
    have hn' : n = (n - 1) + 1 := by omega
    have htwo : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
    rw [htwo, hn']
    simp
    ring
  have hr : n % 5 < 5 := Nat.mod_lt _ (by omega)
  have hs : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by
    simpa only [pow_two] using Nat.mul_mod n n 5
  have hs' : (n - 1) ^ 2 % 5 = ((n - 1) % 5) ^ 2 % 5 := by
    simpa only [pow_two] using Nat.mul_mod (n - 1) (n - 1) 5
  interval_cases h : n % 5 <;> norm_num [h] at hs hs' ⊢ <;> omega

def gap (n : ℕ) : ℕ := 4 * n / 5 - 11 * n / 14

lemma gap_eq_zero_imp_le (n : ℕ) (h : gap n = 0) : n ≤ 56 := by
  unfold gap at h
  omega

lemma twice_le_mul_gap (n : ℕ) (h : 0 < gap n) : 2 * n ≤ 3500 * gap n := by
  unfold gap at h ⊢
  omega

lemma turanGraph_five_colorable (n : ℕ) : (turanGraph n 5).Colorable 5 := by
  let C : (turanGraph n 5).Coloring (Fin 5) :=
    SimpleGraph.Coloring.mk (fun v ↦ ⟨v % 5, Nat.mod_lt _ (by omega)⟩) (by
      intro v w hvw
      simpa [turanGraph_adj] using hvw)
  simpa using C.colorable

variable {V : Type*}

def liftDelete (v : V) (Z : Set ({v}ᶜ : Set V)) : Set V :=
  {v} ∪ Subtype.val '' Z

lemma ncard_liftDelete [Finite V] (v : V) (Z : Set ({v}ᶜ : Set V)) :
    (liftDelete v Z).ncard = Z.ncard + 1 := by
  have hd : Disjoint ({v} : Set V) (Subtype.val '' Z) := by
    rw [Set.disjoint_left]
    rintro _ rfl ⟨z, -, hz⟩
    exact z.property hz
  rw [liftDelete, Set.ncard_union_eq hd, Set.ncard_singleton,
    Set.ncard_image_of_injective Z Subtype.val_injective]
  omega

lemma colorable_liftDelete [Fintype V] (G : SimpleGraph V) (v : V)
    (Z : Set ({v}ᶜ : Set V))
    (hcol : ((G.induce ({v}ᶜ : Set V)).induce Zᶜ).Colorable 5) :
    (G.induce (liftDelete v Z)ᶜ).Colorable 5 := by
  apply SimpleGraph.Colorable.of_hom (G' := (G.induce ({v}ᶜ : Set V)).induce Zᶜ) ?_ hcol
  refine RelHom.mk (fun x ↦ ⟨⟨x.1, ?_⟩, ?_⟩) ?_
  · intro hxv
    exact x.property (Set.mem_union_left _ hxv)
  · intro hxZ
    apply x.property
    change x.1 ∈ ({v} : Set V) ∪ Subtype.val '' Z
    exact Set.mem_union_right _ ⟨_, hxZ, rfl⟩
  · intro a b hab
    exact hab

theorem deletion_bound : ∀ n : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
    Fintype.card V = n → G.CliqueFree 6 →
      ∃ Z : Set V,
        (G.induce Zᶜ).Colorable 5 ∧
          Z.ncard * n ≤ 3500 * (ex5 n - ecount G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V instV G hn hK6
      classical
      have hfree : (⊤ : SimpleGraph (Fin 6)).Free G := by
        exact (cliqueFree_iff_top_free (G := G) (β := Fin 6)).mp (by simpa using hK6)
      have hE : ecount G ≤ ex5 n := by
        rw [ecount_eq_edgeFinset]
        simpa [ex5, hn] using card_edgeFinset_le_extremalNumber hfree
      by_cases hcol : G.Colorable 5
      · refine ⟨∅, ?_, by simp⟩
        exact Colorable.of_hom (Copy.induce G (∅ : Set V)ᶜ).toHom hcol
      have hV : Nonempty V := by
        by_contra hne
        haveI : IsEmpty V := not_nonempty_iff.mp hne
        exact hcol (Colorable.of_isEmpty (G := G) 5)
      letI : Nonempty V := hV
      have hnpos : 0 < n := by
        rw [← hn]
        exact Fintype.card_pos
      have hmin : G.minDegree ≤ 11 * n / 14 := by
        by_contra! hlt
        apply hcol
        apply colorable_of_cliqueFree_lt_minDegree (r := 5) hK6
        norm_num [hn]
        exact hlt
      obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
      have hdeg : G.degree v ≤ 11 * n / 14 := by
        rw [← hv]
        exact hmin
      let S : Set V := {v}ᶜ
      let H : SimpleGraph S := G.induce S
      have hnH : Fintype.card S = n - 1 := by
        dsimp [S]
        rw [Fintype.card_compl_set]
        simp [hn]
      have hKH : H.CliqueFree 6 := by
        exact hK6.comap (Copy.induce G S).isContained
      obtain ⟨Z, hZcol, hZbound⟩ :=
        ih (n - 1) (by omega) S H hnH hKH
      let X : Set V := liftDelete v Z
      have hXcol : (G.induce Xᶜ).Colorable 5 := by
        exact colorable_liftDelete G v Z hZcol
      have hXcard : X.ncard = Z.ncard + 1 := by
        exact ncard_liftDelete v Z
      have hZcard : Z.ncard ≤ n - 1 := by
        calc
          Z.ncard ≤ (Set.univ : Set S).ncard :=
            Set.ncard_le_ncard (Set.subset_univ Z)
          _ = Fintype.card S := by simp [Nat.card_eq_fintype_card]
          _ = n - 1 := hnH
      have hedgeH : ecount H = ecount G - G.degree v := by
        rw [ecount_eq_edgeFinset, ecount_eq_edgeFinset]
        calc
          #H.edgeFinset = #(G.induce ({v}ᶜ : Set V)).edgeFinset := rfl
          _ = #(G.deleteIncidenceSet v).edgeFinset :=
            G.card_edgeFinset_induce_compl_singleton v
          _ = #G.edgeFinset - G.degree v := G.card_edgeFinset_deleteIncidenceSet v
      have hdegE : G.degree v ≤ ecount G := by
        rw [ecount_eq_edgeFinset]
        exact G.degree_le_card_edgeFinset v
      have hedgeSplit : ecount G = ecount H + G.degree v := by
        omega
      have hEH : ecount H ≤ ex5 (n - 1) := by
        have hfreeH : (⊤ : SimpleGraph (Fin 6)).Free H := by
          exact (cliqueFree_iff_top_free (G := H) (β := Fin 6)).mp (by simpa using hKH)
        rw [ecount_eq_edgeFinset]
        simpa [ex5, hnH] using card_edgeFinset_le_extremalNumber hfreeH
      have hdeficit :
          (ex5 (n - 1) - ecount H) + gap n ≤ ex5 n - ecount G := by
        rw [ex5_succ_diff n hnpos]
        unfold gap
        omega
      have hstrict : ecount G < ex5 n := by
        apply lt_of_le_of_ne hE
        intro heq
        have heq' : #G.edgeFinset = ex5 n := by
          rw [← ecount_eq_edgeFinset]
          exact heq
        have hiso : Nonempty (G ≃g turanGraph n 5) := by
          have :=
            (card_edgeFinset_eq_extremalNumber_top_iff_nonempty_iso_turanGraph
              (G := G) (α := Fin 6)).mp ⟨hfree, by simpa [ex5, hn] using heq'⟩
          rw [hn] at this
          exact this
        exact hcol (Colorable.of_hom hiso.some.toRelEmbedding.toRelHom
          (turanGraph_five_colorable n))
      have hdefpos : 0 < ex5 n - ecount G := by omega
      refine ⟨X, hXcol, ?_⟩
      by_cases hgap : gap n = 0
      · have hn56 := gap_eq_zero_imp_le n hgap
        have hXle : X.ncard ≤ n := by
          calc
            X.ncard ≤ (Set.univ : Set V).ncard :=
              Set.ncard_le_ncard (Set.subset_univ X)
            _ = Fintype.card V := by simp [Nat.card_eq_fintype_card]
            _ = n := hn
        calc
          X.ncard * n ≤ n * n := Nat.mul_le_mul_right n hXle
          _ ≤ 56 * 56 := Nat.mul_le_mul hn56 hn56
          _ ≤ 3500 := by norm_num
          _ ≤ 3500 * (ex5 n - ecount G) := by omega
      · have hgappos : 0 < gap n := Nat.pos_of_ne_zero hgap
        have htwice := twice_le_mul_gap n hgappos
        calc
          X.ncard * n = Z.ncard * (n - 1) + (Z.ncard + n) := by
            have hmul : Z.ncard * n = Z.ncard * (n - 1) + Z.ncard := by
              calc
                Z.ncard * n = Z.ncard * ((n - 1) + 1) := by
                  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
                _ = Z.ncard * (n - 1) + Z.ncard := by ring
            rw [hXcard, Nat.add_mul, Nat.one_mul, hmul]
            ring
          _ ≤ Z.ncard * (n - 1) + 2 * n := by omega
          _ ≤ 3500 * (ex5 (n - 1) - ecount H) + 3500 * gap n :=
            Nat.add_le_add hZbound htwice
          _ = 3500 * ((ex5 (n - 1) - ecount H) + gap n) := by ring
          _ ≤ 3500 * (ex5 n - ecount G) := by gcongr

/--
---
conclusion: Lax56.VertexRemovalStability.exists_fiveColorable_delete
---
The quantitative vertex-removal stability theorem used in the paper.
-/
theorem exists_fiveColorable_delete
    {W : Type u_1} [Fintype W] (G : SimpleGraph W) (eps : ℝ)
    (hepsPos : 0 < eps) (hepsSmall : eps < 1 / 3750)
    (hcard : 20 ≤ Fintype.card W) (hK6 : G.CliqueFree 6)
    (hedges :
      (SimpleGraph.extremalNumber (Fintype.card W) (⊤ : SimpleGraph (Fin 6)) : ℝ) -
          eps * (Fintype.card W : ℝ) ^ 2 <
        Lax56.VertexRemovalStability.edgeCount G) :
    ∃ Z : Set W,
      (Nat.card Z : ℝ) < 3500 * eps * Fintype.card W ∧
        (G.induce Zᶜ).Colorable 5 := by
  classical
  let n := Fintype.card W
  obtain ⟨Z, hZcol, hZbound⟩ := deletion_bound n W G rfl hK6
  have hfree : (⊤ : SimpleGraph (Fin 6)).Free G := by
    exact (cliqueFree_iff_top_free (G := G) (β := Fin 6)).mp (by simpa using hK6)
  have hE : ecount G ≤ ex5 n := by
    rw [ecount_eq_edgeFinset]
    simpa [ex5, n] using card_edgeFinset_le_extremalNumber hfree
  have hdeficit :
      ((ex5 n - ecount G : ℕ) : ℝ) < eps * (n : ℝ) ^ 2 := by
    rw [Nat.cast_sub hE]
    have hedges' :
        (ex5 n : ℝ) - eps * (n : ℝ) ^ 2 < (ecount G : ℝ) := by
      simpa [ex5, ecount, n, Lax56.VertexRemovalStability.edgeCount] using hedges
    linarith
  have hZboundReal :
      (Z.ncard : ℝ) * n ≤ 3500 * ((ex5 n - ecount G : ℕ) : ℝ) := by
    exact_mod_cast hZbound
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 20) hcard)
  refine ⟨Z, ?_, hZcol⟩
  simpa only [Nat.card_coe_set_eq] using
    (show (Z.ncard : ℝ) < 3500 * eps * n by nlinarith [hepsPos, hepsSmall])

end Lax56Proofs.VertexRemovalStability
