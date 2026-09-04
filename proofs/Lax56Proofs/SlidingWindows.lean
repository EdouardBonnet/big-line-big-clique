import Lax56Proofs.IntervalDensity
import Lax56Proofs.WeightedPairs
import Mathlib.Data.Sym.Sym2.Order
import Mathlib.Tactic

namespace Lax56Proofs.SlidingWindows

open scoped BigOperators
open SimpleGraph
open Lax56.Geometry
open Lax56.VertexRemovalStability
open Lax56Proofs.OrderGeometry
open Lax56Proofs.FiniteIntervals
open Lax56Proofs.WeightedPairs
open Lax56Proofs.IntervalDensity

/-- Sort an unordered non-edge into increasing endpoint order. -/
noncomputable def orderedOfNonedge {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Gᶜ.edgeSet) : OrderedPair n := by
  let q := Sym2.sortEquiv x.1
  have hadj : Gᶜ.Adj q.1.1 q.1.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [← Sym2.sortEquiv_symm_apply q]
    change Sym2.sortEquiv.symm (Sym2.sortEquiv x.1) ∈ Gᶜ.edgeSet
    rw [Equiv.symm_apply_apply]
    exact x.2
  exact ⟨q.1, lt_of_le_of_ne q.2 hadj.ne⟩

theorem orderedOfNonedge_injective {n : ℕ} (G : SimpleGraph (Fin n)) :
    Function.Injective (orderedOfNonedge G) := by
  intro x y h
  dsimp only [orderedOfNonedge] at h
  have hv := congrArg Subtype.val h
  change (Sym2.sortEquiv x.1).1 = (Sym2.sortEquiv y.1).1 at hv
  apply Subtype.ext
  apply Sym2.sortEquiv.injective
  apply Subtype.ext
  exact hv

theorem orderedOfNonedge_not_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Gᶜ.edgeSet) :
    ¬G.Adj (orderedOfNonedge G x).left (orderedOfNonedge G x).right := by
  let q := Sym2.sortEquiv x.1
  have hadj : Gᶜ.Adj q.1.1 q.1.2 := by
    rw [← SimpleGraph.mem_edgeSet]
    rw [← Sym2.sortEquiv_symm_apply q]
    change Sym2.sortEquiv.symm (Sym2.sortEquiv x.1) ∈ Gᶜ.edgeSet
    rw [Equiv.symm_apply_apply]
    exact x.2
  have hn := (SimpleGraph.compl_adj G q.1.1 q.1.2).mp hadj |>.2
  simpa only [orderedOfNonedge, q, OrderedPair.left, OrderedPair.right] using hn

/-- Global bad pairs whose endpoints both lie in the window `[s,s+m)`. -/
abbrev Captured (P : Finset Point) (s m : ℕ) :=
  {e : BadPair P //
    s ≤ e.1.left.val ∧ e.1.right.val < s + m}

/-- A non-edge of a block gives a bad pair of the ambient set captured by
that block. -/
noncomputable def blockNonedgeToCaptured (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card)
    (x : (blockGraph P hs)ᶜ.edgeSet) : Captured P s m := by
  let e := orderedOfNonedge (blockGraph P hs) x
  let E : OrderedPair P.card := mkPair
    (blockIndex hs e.left) (blockIndex hs e.right)
    (by simpa [blockIndex] using e.left_lt_right)
  have hbad : ¬Visible P (orderedPoint P E.left) (orderedPoint P E.right) := by
    have hx := orderedOfNonedge_not_adj (blockGraph P hs) x
    change ¬Visible P (blockPoint P hs e.left) (blockPoint P hs e.right) at hx
    simpa only [E, mkPair, OrderedPair.left, OrderedPair.right, blockPoint] using hx
  refine ⟨⟨E, hbad⟩, ?_, ?_⟩
  · simp only [E, mkPair, OrderedPair.left, blockIndex]
    omega
  · simp only [E, mkPair, OrderedPair.right, blockIndex]
    have := e.right.isLt
    omega

theorem blockNonedgeToCaptured_injective (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) :
    Function.Injective (blockNonedgeToCaptured P hs) := by
  intro x y hxy
  have hbad := congrArg (fun z : Captured P s m ↦ z.1.1) hxy
  have hleft := congrArg (fun z : OrderedPair P.card ↦ z.left) hbad
  have hright := congrArg (fun z : OrderedPair P.card ↦ z.right) hbad
  dsimp only [blockNonedgeToCaptured] at hleft hright
  simp only [mkPair, OrderedPair.left, OrderedPair.right] at hleft hright
  have heleft : (orderedOfNonedge (blockGraph P hs) x).left =
      (orderedOfNonedge (blockGraph P hs) y).left :=
    blockIndex_injective hs hleft
  have heright : (orderedOfNonedge (blockGraph P hs) x).right =
      (orderedOfNonedge (blockGraph P hs) y).right :=
    blockIndex_injective hs hright
  apply orderedOfNonedge_injective (blockGraph P hs)
  exact OrderedPair.ext heleft heright

theorem block_nonedge_le_captured (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) :
    edgeCount (blockGraph P hs)ᶜ ≤ Nat.card (Captured P s m) := by
  simpa only [edgeCount, Nat.card_eq_fintype_card] using
    Fintype.card_le_of_injective (blockNonedgeToCaptured P hs)
      (blockNonedgeToCaptured_injective P hs)

/-- Starts of length-`m` windows which capture a given bad pair. -/
abbrev CapturingStart (P : Finset Point) (m : ℕ) (e : BadPair P) :=
  {s : Fin (P.card - m + 1) //
    s.val ≤ e.1.left.val ∧ e.1.right.val < s.val + m}

/-- A capturing start is encoded by its offset from the left endpoint. -/
def startOffset (P : Finset Point) (m : ℕ) (e : BadPair P)
    (x : CapturingStart P m e) : Fin (m - e.1.stretch) :=
  ⟨e.1.left.val - x.1.val, by
    have hl := x.2.1
    have hr := x.2.2
    have hij := e.1.left_lt_right
    have hsum :
        (e.1.right.val - e.1.left.val) +
          (e.1.left.val - x.1.val) = e.1.right.val - x.1.val := by
      omega
    have hlt : e.1.right.val - x.1.val < m := by omega
    simp only [OrderedPair.left, OrderedPair.right] at hl hr hij hsum hlt
    simp only [OrderedPair.stretch, OrderedPair.left, OrderedPair.right]
    omega⟩

theorem startOffset_injective (P : Finset Point) (m : ℕ) (e : BadPair P) :
    Function.Injective (startOffset P m e) := by
  intro x y hxy
  apply Subtype.ext
  apply Fin.ext
  have hv := congrArg Fin.val hxy
  simp only [startOffset] at hv
  have hx := x.2.1
  have hy := y.2.1
  omega

theorem card_capturingStart_le (P : Finset Point) (m : ℕ) (e : BadPair P) :
    Nat.card (CapturingStart P m e) ≤ m - e.1.stretch := by
  classical
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
    Fintype.card_le_of_injective (startOffset P m e)
      (startOffset_injective P m e)

def capturedSigmaEquiv (P : Finset Point) (m : ℕ) :
    (Σ s : Fin (P.card - m + 1), Captured P s.val m) ≃
      (Σ e : BadPair P, CapturingStart P m e) where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_card_captured_eq (P : Finset Point) (m : ℕ) :
    ∑ s : Fin (P.card - m + 1), Nat.card (Captured P s.val m) =
      ∑ e : BadPair P, Nat.card (CapturingStart P m e) := by
  rw [← Nat.card_sigma, ← Nat.card_sigma]
  exact Nat.card_congr (capturedSigmaEquiv P m)

/-- Total number of window starts available to all bad pairs, counted with
multiplicity.  A pair of stretch `d<m` contributes `m-d`. -/
noncomputable def deficit (P : Finset Point) (m : ℕ) : ℕ :=
  ∑ e : BadPair P, (m - e.1.stretch)

def windowFits (P : Finset Point) {m : ℕ} (hm : m ≤ P.card)
    (s : Fin (P.card - m + 1)) : s.val + m ≤ P.card := by
  have := s.isLt
  omega

/-- Sliding-window double counting: every block non-edge is charged to a
global bad pair, and a stretch-`d` pair is charged at most `m-d` times. -/
theorem sum_window_nonedge_le_deficit (P : Finset Point) {m : ℕ}
    (hm : m ≤ P.card) :
    (∑ s : Fin (P.card - m + 1),
        edgeCount (blockGraph P (windowFits P hm s))ᶜ) ≤ deficit P m := by
  calc
    (∑ s : Fin (P.card - m + 1),
        edgeCount (blockGraph P (windowFits P hm s))ᶜ) ≤
        ∑ s : Fin (P.card - m + 1), Nat.card (Captured P s.val m) := by
      exact Finset.sum_le_sum fun s _ ↦
        block_nonedge_le_captured P (windowFits P hm s)
    _ = ∑ e : BadPair P, Nat.card (CapturingStart P m e) :=
      sum_card_captured_eq P m
    _ ≤ ∑ e : BadPair P, (m - e.1.stretch) := by
      exact Finset.sum_le_sum fun e _ ↦ card_capturingStart_le P m e
    _ = deficit P m := rfl

/-- The local density estimate, averaged over all sliding windows.  This is
the lower bound on the scale-`m` truncated bad-pair mass used in Section 5. -/
theorem deficit_lower
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (hvisible : ¬HasVisibleClique P 6) {m : ℕ}
    (hm₀ : m₀ ≤ m) (hm : m ≤ P.card) :
    density * (m : ℝ) * P.card - density * (m : ℝ) ^ 2 - P.card / 2 ≤
      (deficit P m : ℝ) / m := by
  have hsumNat := sum_window_nonedge_le_deficit P hm
  have hsumR :
      (∑ s : Fin (P.card - m + 1),
        (edgeCount (blockGraph P (windowFits P hm s))ᶜ : ℝ)) ≤
          (deficit P m : ℝ) := by
    exact_mod_cast hsumNat
  have hlocal (s : Fin (P.card - m + 1)) :
      density * (m : ℝ) ^ 2 - (m : ℝ) / 2 ≤
        (edgeCount (blockGraph P (windowFits P hm s))ᶜ : ℝ) :=
    invisible_edge_lower P hfour hvisible (windowFits P hm s) hm₀
  have hlower :
      ((P.card - m + 1 : ℕ) : ℝ) *
          (density * (m : ℝ) ^ 2 - (m : ℝ) / 2) ≤
        ∑ s : Fin (P.card - m + 1),
          (edgeCount (blockGraph P (windowFits P hm s))ᶜ : ℝ) := by
    have hraw :
        (∑ _s : Fin (P.card - m + 1),
            (density * (m : ℝ) ^ 2 - (m : ℝ) / 2)) ≤
          ∑ s : Fin (P.card - m + 1),
            (edgeCount (blockGraph P (windowFits P hm s))ᶜ : ℝ) :=
      Finset.sum_le_sum fun s _ ↦ hlocal s
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] using hraw
  have hdef := hlower.trans hsumR
  have hmR : (0 : ℝ) < m := by
    have hm₀pos : 0 < m₀ := by unfold m₀; norm_num
    exact_mod_cast (lt_of_lt_of_le hm₀pos hm₀)
  have hdiv := (div_le_div_iff_of_pos_right hmR).2 hdef
  calc
    density * (m : ℝ) * P.card - density * (m : ℝ) ^ 2 - P.card / 2 ≤
        (((P.card - m + 1 : ℕ) : ℝ) *
          (density * (m : ℝ) ^ 2 - (m : ℝ) / 2)) / m := by
      have hcast : ((P.card - m + 1 : ℕ) : ℝ) =
          (P.card : ℝ) - m + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hm]
        norm_num
      rw [hcast]
      have hc : (0 : ℝ) < density := by norm_num [density, eps₁]
      have hcm : (0 : ℝ) < density * m := mul_pos hc hmR
      have hmone : (1 : ℝ) ≤ m := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
          (Nat.ne_of_gt (by exact_mod_cast hmR)))
      field_simp
      nlinarith
    _ ≤ (deficit P m : ℝ) / m := hdiv

end Lax56Proofs.SlidingWindows
