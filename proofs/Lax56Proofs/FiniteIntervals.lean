import Lax56Proofs.OrderGeometry
import Mathlib.Tactic

namespace Lax56Proofs.FiniteIntervals

open Lax56.Geometry
open Lax56Proofs.OrderGeometry

/-- Add a local block index to a starting position. -/
def blockIndex {n s m : ℕ} (hs : s + m ≤ n) (i : Fin m) : Fin n :=
  ⟨s + i, by omega⟩

theorem blockIndex_injective {n s m : ℕ} (hs : s + m ≤ n) :
    Function.Injective (blockIndex hs) := by
  intro i j hij
  apply Fin.ext
  simpa [blockIndex] using congrArg Fin.val hij

/-- The point at local position `i` in the block starting at `s`. -/
noncomputable def blockPoint (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) (i : Fin m) : Point :=
  orderedPoint P (blockIndex hs i)

theorem blockPoint_injective (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) : Function.Injective (blockPoint P hs) :=
  (orderedPoint_injective P).comp (blockIndex_injective hs)

/-- A consecutive block of the canonical point ordering. -/
noncomputable def blockSet (P : Finset Point) (s m : ℕ)
    (hs : s + m ≤ P.card) : Finset Point :=
  Finset.univ.image (blockPoint P hs)

@[simp] theorem card_blockSet (P : Finset Point) (s m : ℕ)
    (hs : s + m ≤ P.card) : (blockSet P s m hs).card = m := by
  classical
  rw [blockSet, Finset.card_image_of_injective _ (blockPoint_injective P hs)]
  simp

theorem blockPoint_mem (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) (i : Fin m) :
    blockPoint P hs i ∈ blockSet P s m hs := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem blockSet_subset (P : Finset Point) (s m : ℕ)
    (hs : s + m ≤ P.card) : blockSet P s m hs ⊆ P := by
  intro p hp
  classical
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hp
  exact orderedPoint_mem P _

/-- The local indices are in bijection with the points of their block. -/
noncomputable def blockEquiv (P : Finset Point) (s m : ℕ)
    (hs : s + m ≤ P.card) : Fin m ≃ blockSet P s m hs :=
  Equiv.ofBijective
    (fun i ↦ ⟨blockPoint P hs i, blockPoint_mem P hs i⟩)
    ⟨fun i j h ↦ by
      apply blockIndex_injective hs
      apply ((lexPoints P).orderIsoOfFin (card_lexPoints P)).injective
      apply Subtype.ext
      simpa [blockPoint, orderedPoint] using
        congrArg (fun p : blockSet P s m hs ↦ toLex (p : Point)) h, by
      intro p
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp p.property
      exact ⟨i, Subtype.ext hi⟩⟩

@[simp] theorem blockEquiv_apply_val (P : Finset Point) (s m : ℕ)
    (hs : s + m ≤ P.card) (i : Fin m) :
    ((blockEquiv P s m hs) i : Point) = blockPoint P hs i := rfl

/-- Observation 2.1 in start/length coordinates. -/
theorem visible_blockSet_iff
    (P : Finset Point) {s m : ℕ} (hs : s + m ≤ P.card)
    {i j : Fin m} (hij : i < j) :
    Visible (blockSet P s m hs) (blockPoint P hs i) (blockPoint P hs j) ↔
      Visible P (blockPoint P hs i) (blockPoint P hs j) := by
  constructor
  · intro hsmall
    refine ⟨(blockPoint_injective P hs).ne hij.ne, ?_⟩
    intro r hrP hrseg
    obtain ⟨k, rfl⟩ := orderedPoint_surjective P r hrP
    have hbetween := lex_between_of_mem_openSegment
      ((orderedPoint_strictMono P) (show blockIndex hs i < blockIndex hs j by
        simpa [blockIndex] using hij)) hrseg
    have hik : blockIndex hs i < k :=
      (orderedPoint_strictMono P).lt_iff_lt.mp hbetween.1
    have hkj : k < blockIndex hs j :=
      (orderedPoint_strictMono P).lt_iff_lt.mp hbetween.2
    have hikv : s + i.val < k.val := by simpa [blockIndex] using hik
    have hkjv : k.val < s + j.val := by simpa [blockIndex] using hkj
    let t : Fin m := ⟨k - s, by
      have := j.isLt
      omega⟩
    have hkt : blockIndex hs t = k := by
      apply Fin.ext
      simp only [blockIndex, t]
      have : s ≤ k.val := by omega
      omega
    exact hsmall.2 (blockPoint P hs t) (blockPoint_mem P hs t) (by simpa [blockPoint, hkt])
  · intro hlarge
    refine ⟨hlarge.1, ?_⟩
    intro r hr
    exact hlarge.2 r (blockSet_subset P s m hs hr)

/-- The visibility graph on a block, with local indices as vertices. -/
noncomputable def blockGraph (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) : SimpleGraph (Fin m) where
  Adj i j := Visible P (blockPoint P hs i) (blockPoint P hs j)
  symm := by
    intro i j h
    exact ⟨h.1.symm, by simpa only [openSegment_symm] using h.2⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

@[simp] theorem blockGraph_adj (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) (i j : Fin m) :
    (blockGraph P hs).Adj i j ↔ Visible P (blockPoint P hs i) (blockPoint P hs j) :=
  Iff.rfl

/-- Observation 2.1 as a graph isomorphism. -/
noncomputable def blockGraphIso (P : Finset Point) {s m : ℕ}
    (hs : s + m ≤ P.card) :
    blockGraph P hs ≃g visibilityGraph (blockSet P s m hs) where
  toEquiv := blockEquiv P s m hs
  map_rel_iff' := by
    intro i j
    change Visible (blockSet P s m hs)
        ((blockEquiv P s m hs) i : Point) ((blockEquiv P s m hs) j : Point) ↔
      Visible P (blockPoint P hs i) (blockPoint P hs j)
    rw [blockEquiv_apply_val, blockEquiv_apply_val]
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact visible_blockSet_iff P hs hij
    · simp [Visible]
    · have h := visible_blockSet_iff P hs hji
      constructor
      · intro hv
        have hv' : Visible (blockSet P s m hs) (blockPoint P hs j) (blockPoint P hs i) :=
          ⟨hv.1.symm, by simpa only [openSegment_symm] using hv.2⟩
        have hp := h.mp hv'
        exact ⟨hp.1.symm, by simpa only [openSegment_symm] using hp.2⟩
      · intro hp
        have hp' : Visible P (blockPoint P hs j) (blockPoint P hs i) :=
          ⟨hp.1.symm, by simpa only [openSegment_symm] using hp.2⟩
        have hv := h.mpr hp'
        exact ⟨hv.1.symm, by simpa only [openSegment_symm] using hv.2⟩

/-- A local index in a length-`L` window of `Fin m`. -/
def windowIndex {m L : ℕ} (hLm : L ≤ m)
    (s : Fin (m - L + 1)) (i : Fin L) : Fin m :=
  ⟨s + i, by omega⟩

theorem windowIndex_injective {m L : ℕ} (hLm : L ≤ m) (s : Fin (m - L + 1)) :
    Function.Injective (windowIndex hLm s) := by
  intro i j hij
  apply Fin.ext
  simpa [windowIndex] using congrArg Fin.val hij

theorem blockPoint_windowIndex
    (P : Finset Point) {s m L : ℕ} (hs : s + m ≤ P.card)
    (hLm : L ≤ m) (w : Fin (m - L + 1))
    (hsw : s + w.val + L ≤ P.card) (i : Fin L) :
    blockPoint P hs (windowIndex hLm w i) = blockPoint P hsw i := by
  unfold blockPoint
  apply congrArg (orderedPoint P)
  apply Fin.ext
  simp [blockIndex, windowIndex]
  omega

/-- A finite union-bound pigeonhole lemma: if fewer than `(m-L+1)/L`
positions are deleted, some length-`L` window avoids all deletions. -/
theorem exists_disjoint_window
    {m L : ℕ} (hL : 0 < L) (hLm : L ≤ m) (Z : Set (Fin m))
    (hsmall : Nat.card Z * L < m - L + 1) :
    ∃ s : Fin (m - L + 1), ∀ i : Fin L, windowIndex hLm s i ∉ Z := by
  classical
  by_contra h
  push_neg at h
  let hit (s : Fin (m - L + 1)) : Fin L := Classical.choose (h s)
  have hit_mem (s : Fin (m - L + 1)) : windowIndex hLm s (hit s) ∈ Z :=
    Classical.choose_spec (h s)
  let encode (s : Fin (m - L + 1)) : Z × Fin L :=
    (⟨windowIndex hLm s (hit s), hit_mem s⟩, hit s)
  have hencode : Function.Injective encode := by
    intro s t hst
    have hoff : hit s = hit t := congrArg Prod.snd hst
    have hpoint : windowIndex hLm s (hit s) = windowIndex hLm t (hit t) :=
      congrArg (fun x : Z × Fin L ↦ (x.1 : Fin m)) hst
    apply Fin.ext
    simpa [windowIndex, hoff] using congrArg Fin.val hpoint
  have hcard := Fintype.card_le_of_injective encode hencode
  have : m - L + 1 ≤ Nat.card Z * L := by
    simpa [Nat.card_eq_fintype_card] using hcard
  omega

end Lax56Proofs.FiniteIntervals
