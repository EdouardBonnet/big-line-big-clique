import Lax56Proofs.ValtrRunSupport
import Lax56Proofs.ValtrRunReduction

namespace Lax56Proofs.ValtrRunSetup

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrExtension Lax56Proofs.ValtrCyclic Lax56Proofs.ValtrRadialOrder
open Lax56Proofs.ValtrSectorSetup Lax56Proofs.ValtrCoverSetup
open Lax56Proofs.ValtrRunSupport Lax56Proofs.ValtrRunReduction
open scoped Classical Fin.NatCast

def cyclicIndex {n : ℕ} [NeZero n] (start : Fin n) (k : ℕ) : Fin n := start + (↑k : Fin n)

theorem cyclicIndex_succ {n : ℕ} [NeZero n] (start : Fin n) (k : ℕ) :
    cyclicIndex start (k + 1) = cyclicIndex start k + 1 := by
  simp only [cyclicIndex, Nat.cast_add, Nat.cast_one, add_assoc]

theorem cyclicIndex_injective_below {n : ℕ} [NeZero n] (start : Fin n)
    {i j : ℕ} (hi : i < n) (hj : j < n) (heq : cyclicIndex start i = cyclicIndex start j) : i = j := by
  have hh : (↑i : Fin n) = (↑j : Fin n) := add_left_cancel heq
  rw [Fin.natCast_eq_mk hi, Fin.natCast_eq_mk hj] at hh
  exact congrArg Fin.val hh

/-- Clockwise listing of the base vertices of a positively indexed run. -/
def runBase {n : ℕ} [NeZero n] (v : Fin n → Point) (start : Fin n) (t k : ℕ) : Point :=
  v (cyclicIndex start (t + 1 - k))

/-- The open replacement chain, with its two base endpoints. -/
def runChain {n : ℕ} [NeZero n] (v c : Fin n → Point) (start : Fin n) (t k : ℕ) : Point :=
  if k = 0 then v (cyclicIndex start t)
  else if k = t + 1 then v start
  else c (cyclicIndex start (t - k))

theorem runChain_apex {n : ℕ} [NeZero n] (v c : Fin n → Point) (start : Fin n)
    {t k : ℕ} (hk : 1 ≤ k) (hkt : k ≤ t) :
    runChain v c start t k = c (cyclicIndex start (t - k)) := by
  simp only [runChain, if_neg (by omega : k ≠ 0), if_neg (by omega : k ≠ t + 1)]

theorem runBase_current {n : ℕ} [NeZero n] (v : Fin n → Point) (start : Fin n)
    {t k : ℕ} (_hk : 1 ≤ k) (hkt : k ≤ t) :
    runBase v start t k = v (cyclicIndex start (t - k) + 1) := by
  rw [← cyclicIndex_succ]
  unfold runBase
  congr 2
  omega

theorem runBase_next {n : ℕ} [NeZero n] (v : Fin n → Point) (start : Fin n)
    (t k : ℕ) : runBase v start t (k + 1) = v (cyclicIndex start (t - k)) := by
  unfold runBase
  congr 2
  omega

/-- All hypotheses of the support theorem are obtained from the actual
cyclic second layer and selected apex data. Only the two nonconvex
endpoint conditions distinguish this branch of the run argument. -/
theorem runConfig_of_apex_data {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (start : Fin n) {t : ℕ} (ht : 2 ≤ t) (htn : t < n)
    (hdefined : ∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k))
    (hfirst : StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1))
    (hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t)) :
    RunConfig S t (runBase v start t) (runChain v c start t) d := by
  let b := runBase v start t
  let h := runChain v c start t
  have hvB (i) : v i ∈ extremeLayer (inner S) := by
    change v i ∈ (extremeLayer (inner S) : Set Point)
    rw [← hrange]
    exact Set.mem_range_self i
  have hdatum (k) (hk : k < t) := hdata (cyclicIndex start k) (hdefined k hk)
  have hbase_mem (i) (_ : 1 ≤ i) (_ : i ≤ t + 1) : b i ∈ extremeLayer (inner S) := hvB _
  have hapex (i) (hi : 1 ≤ i) (hit : i ≤ t) : h i = c (cyclicIndex start (t - i)) :=
    runChain_apex v c start hi hit
  have hapex_mem (i) (hi : 1 ≤ i) (hit : i ≤ t) :
      h i ∈ extremeLayer (inner (inner S)) := by
    rw [hapex i hi hit]
    exact (hdatum (t - i) (by omega)).mem_third
  have hfirstEq : h 0 = b 1 := by simp [h, b, runChain, runBase]
  have hlastEq : h (t + 1) = b (t + 1) := by
    simp [h, b, runChain, runBase, cyclicIndex]
  have hb_inj (i j) (hi : 1 ≤ i) (hit : i ≤ t + 1)
      (hj : 1 ≤ j) (hjt : j ≤ t + 1) (heq : b i = b j) : i = j := by
    have hh := cyclicIndex_injective_below start (by omega : t + 1 - i < n)
      (by omega : t + 1 - j < n) (hinj heq)
    omega
  have hc_inj (i j) (hi : 1 ≤ i) (hit : i ≤ t)
      (hj : 1 ≤ j) (hjt : j ≤ t) (heq : h i = h j) : i = j := by
    rw [hapex i hi hit, hapex j hj hjt] at heq
    have hh := defined_apex_index_eq htri hdata
      (hdefined (t - i) (by omega)) (hdefined (t - j) (by omega)) heq
    have hh := cyclicIndex_injective_below start (by omega : t - i < n) (by omega : t - j < n) hh
    omega
  have hcb_ne (i j) (hi : 1 ≤ i) (hit : i ≤ t)
      (hj : 1 ≤ j) (hjt : j ≤ t + 1) : h i ≠ b j := by
    intro heq
    have hI := extremeLayer_subset _ (hapex_mem i hi hit)
    exact (Finset.mem_sdiff.mp hI).2 (heq.symm ▸ hbase_mem j hj hjt)
  have hchain_inj_le (i j) (hi : i ≤ t + 1) (hj : j ≤ t + 1)
      (hij : i ≤ j) (heq : h i = h j) : i = j := by
    by_cases he : i = j
    · exact he
    have hij' : i < j := by omega
    by_cases hi0 : i = 0
    · subst i
      by_cases hjlast : j = t + 1
      · subst j
        rw [hfirstEq, hlastEq] at heq
        have hh := hb_inj 1 (t + 1) (by decide) (by omega) (by omega) le_rfl heq
        omega
      · exact (hcb_ne j 1 (by omega) (by omega) (by decide) (by omega)
          (heq.symm.trans hfirstEq)).elim
    by_cases hjlast : j = t + 1
    · subst j
      exact (hcb_ne i (t + 1) (by omega) (by omega) (by omega) le_rfl
        (heq.trans hlastEq)).elim
    exact hc_inj i j (by omega) (by omega) (by omega) (by omega) heq
  have hchain_inj (i j) (hi : i ≤ t + 1) (hj : j ≤ t + 1) (heq : h i = h j) : i = j := by
    by_cases hij : i ≤ j
    · exact hchain_inj_le i j hi hj hij heq
    · exact (hchain_inj_le j i hj hi (by omega) heq.symm).symm
  have hbCurrent (k) (hk : 1 ≤ k) (hkt : k ≤ t) :
      b k = v (cyclicIndex start (t - k) + 1) := runBase_current v start hk hkt
  have hbNext (k) (_ : 1 ≤ k) (_ : k ≤ t) :
      b (k + 1) = v (cyclicIndex start (t - k)) := runBase_next v start t k
  have hctri (a b e : ℕ) (hab : a < b) (hbe : b < e) (het : e < t) :
      0 < turn (c (cyclicIndex start a)) (c (cyclicIndex start b)) (c (cyclicIndex start e)) := by
    let u : Fin n → Point := fun i ↦ v (start + i)
    have hutri : ∀ i j k, i < j → j < k → 0 < turn (u i) (u j) (u k) := by
      intro i j k hij hjk
      simpa only [u, add_comm] using cyclic_shift_triples htri start i j k hij hjk
    have hgenI : ¬HasThreeCollinear (inner (inner S)) := fun hh ↦ hgen
      (hasThreeCollinear_mono ((inner_subset (inner S)).trans (inner_subset S)) hh)
    have hfanAt (r : ℕ) (hrt : r < t) :
        StrictlyInsideTriangle d (u ⟨r, by omega⟩) (u (⟨r, by omega⟩ + 1))
          (c (cyclicIndex start r)) := by
      simpa only [u, cyclicIndex, Fin.natCast_eq_mk (by omega : r < n), add_assoc] using
        (hdatum r hrt).strict_triangle
    exact radial_extreme_triple hgenI hutri
      (i := ⟨a, by omega⟩) (j := ⟨b, by omega⟩) (k := ⟨e, by omega⟩) hab hbe hd
      (hdatum a (by omega)).mem_third (hdatum b (by omega)).mem_third (hdatum e het).mem_third
      (hfanAt a (by omega)) (hfanAt b (by omega)) (hfanAt e het)
  change RunConfig S t b h d
  refine ⟨ht, hfirstEq, hlastEq, hbase_mem, hapex_mem, hchain_inj, hb_inj, ?_, ?_, ?_, hd, ?_, hfirst, hlast⟩
  · intro k hk hkt p hp
    rw [hbCurrent k hk hkt, hbNext k hk hkt, turn_swap_first]
    apply neg_nonpos.mpr
    apply cyclic_edge_nonneg_of_mem_hull htri _ (cyclicIndex start (t - k))
    rw [hrange, convexHull_extremeLayer]
    exact subset_convexHull ℝ _ hp
  · intro i j k hi hij hjk hkt
    rw [hapex i hi (by omega), hapex j (by omega) (by omega), hapex k (by omega) hkt]
    convert neg_neg_of_pos (hctri (t - k) (t - j) (t - i) (by omega) (by omega) (by omega))
      using 1 <;> unfold turn <;> ring
  · intro k hk hkt
    rw [hbCurrent k hk hkt, hbNext k hk hkt, hapex k hk hkt]
    exact (hdatum (t - k) (by omega)).strict_triangle
  · intro k hk hkt p hp hptri
    rw [hbCurrent k hk hkt, hbNext k hk hkt, hapex k hk hkt] at hptri ⊢
    exact (hdatum (t - k) (by omega)).empty_triangle p hp hptri

/-- The full nonconvex-endpoint branch of the run induction, applied to
the actual finite sector union. The size bound `t + 2` is supplied by the
one-sector bound and the induction hypothesis for the shorter run. -/
theorem not_minimal_of_nonconvex_run_card_le {S : Finset Point} (hgen : ¬HasThreeCollinear S)
    {n : ℕ} [NeZero n] (v : Fin n → Point) (hinj : Function.Injective v)
    (hrange : Set.range v = (extremeLayer (inner S) : Set Point))
    (htri : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {d : Point} (hd : d ∈ inner (inner (inner S))) (c : Fin n → Point)
    (hdata : ∀ i, MeetsThirdLayer S v d i → ApexData S v d i (c i))
    (start : Fin n) {t : ℕ} (ht : 2 ≤ t) (htn : t < n)
    (hdefined : ∀ k < t, MeetsThirdLayer S v d (cyclicIndex start k))
    (hfirst : StrictlyInsideTriangle (runBase v start t 1) (runChain v c start t 2)
      (runBase v start t 2) (runChain v c start t 1))
    (hlast : StrictlyInsideTriangle (runBase v start t t) (runChain v c start t (t - 1))
      (runBase v start t (t + 1)) (runChain v c start t t))
    (hcard : ((Finset.range t).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))).card ≤ t + 2) :
    ¬MinimalOuter S := by
  have cfg := runConfig_of_apex_data hgen v hinj hrange htri hd c hdata start ht htn hdefined hfirst hlast
  let U := (Finset.range t).biUnion (fun k ↦ sectorPoints S v c d (cyclicIndex start k))
  let R := extremeLayer S \ U
  have hR : R ⊆ extremeLayer S := Finset.sdiff_subset
  have hout : ∀ x ∈ R, ∀ k, 1 ≤ k → k ≤ t →
      x ∉ sector ![runBase v start t k, runChain v c start t k, runBase v start t (k + 1)] := by
    intro x hx k hk hkt hs
    obtain ⟨hxA, hxU⟩ := Finset.mem_sdiff.mp hx
    apply hxU
    apply Finset.mem_biUnion.mpr
    refine ⟨t - k, Finset.mem_range.mpr (by omega), ?_⟩
    apply mem_sectorPoints_iff.mpr
    refine ⟨hdefined (t - k) (by omega), hxA, ?_⟩
    simpa only [runBase_current v start hk hkt, runBase_next,
      runChain_apex v c start hk hkt] using hs
  have hremoved : (extremeLayer S \ R).card ≤ t + 2 := by
    have hsub : extremeLayer S \ R ⊆ U := by
      intro x hx
      by_contra hxU
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, hxU⟩)
    exact (Finset.card_le_card hsub).trans hcard
  exact cfg.not_minimal_of_removed_card_le hgen hR hout hremoved

end Lax56Proofs.ValtrRunSetup
