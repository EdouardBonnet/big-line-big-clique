import Lax56Proofs.HKBFiniteMCSemantics
import Mathlib.Tactic

/-!
The geometric interpretation of the finite `mc₃(4) ≤ 12` certificate.
-/

namespace Lax56Proofs.HKBMcBridge

open Lax56.Geometry
open Lax56Proofs.Blockers
open Lax56Proofs.OrderGeometry
open Lax56Proofs.Orientation
open Lax56Proofs.HKBFiniteMC

/-- Rename four colours so the first two distinct values become `0,1` and
the third value is below `3`.  This is the symmetry normalization used by the
finite certificate. -/
private theorem exists_colourRenaming (a b c : Fin 4) (hab : a ≠ b) :
    ∃ e : Equiv.Perm (Fin 4),
      e a = 0 ∧ e b = 1 ∧ (e c).val < 3 := by
  let f : Fin 2 → Fin 4 := fun i => if i = 0 then a else b
  let g : Fin 2 → Fin 4 := fun i => if i = 0 then 0 else 1
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  have hσa : σ a = 0 := by simpa [f, g] using hσ 0
  have hσb : σ b = 1 := by simpa [f, g] using hσ 1
  by_cases hc : σ c = 3
  · let e := σ.trans (Equiv.swap (3 : Fin 4) 2)
    refine ⟨e, ?_, ?_, ?_⟩
    · simp [e, hσa, Equiv.swap_apply_def]
    · simp [e, hσb, Equiv.swap_apply_def]
    · simp [e, hc, Equiv.swap_apply_def]
  · refine ⟨σ, hσa, hσb, ?_⟩
    have hlt := (σ c).isLt
    have hne : (σ c).val ≠ 3 := by
      intro hval
      apply hc
      apply Fin.ext
      exact hval
    omega

set_option maxHeartbeats 0 in
/-- A four-coloured point set with no four collinear points, in which every
equal-coloured pair is blocked by a point of the set, has at most twelve
points.  This is the geometric `mc₃(4) ≤ 12` statement. -/
theorem card_le_twelve_of_four_coloured_blocking
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (colouring : P → Fin 4)
    (hblocked : ∀ (p q : P), p ≠ q → colouring p = colouring q →
      ∃ r ∈ P, r ∈ openSegment ℝ (p : Point) (q : Point)) :
    P.card ≤ 12 := by
  by_contra hcard
  have h13 : 13 ≤ P.card := by omega
  let index : Fin 13 → Fin P.card := Fin.castLE h13
  let point : Fin 13 → Point := fun i => orderedPoint P (index i)
  have point_mem (i : Fin 13) : point i ∈ P := orderedPoint_mem P (index i)
  have index_strict : StrictMono index := Fin.strictMono_castLE h13
  have point_injective : Function.Injective point :=
    (orderedPoint_injective P).comp index_strict.injective
  let rawColour : Fin 13 → Fin 4 :=
    fun i => colouring ⟨point i, point_mem i⟩
  have hzeroone : (0 : Fin 13) < 1 := by decide
  have h01 : rawColour 0 ≠ rawColour 1 := by
    intro hc
    have hc' : colouring ⟨point 0, point_mem 0⟩ =
        colouring ⟨point 1, point_mem 1⟩ := by
      simpa [rawColour] using hc
    obtain ⟨r, hrP, hr⟩ := hblocked ⟨point 0, point_mem 0⟩
      ⟨point 1, point_mem 1⟩
      (by
        intro he
        apply hzeroone.ne
        apply point_injective
        exact congrArg (fun x : P => (x : Point)) he) hc'
    obtain ⟨kP, hkP⟩ := orderedPoint_surjective P r hrP
    have hlex := lex_between_of_mem_openSegment
      ((orderedPoint_strictMono P) (index_strict hzeroone)) hr
    have h0k : index 0 < kP := by
      apply (orderedPoint_strictMono P).lt_iff_lt.mp
      simpa [point, hkP] using hlex.1
    have hk1 : kP < index 1 := by
      apply (orderedPoint_strictMono P).lt_iff_lt.mp
      simpa [point, hkP] using hlex.2
    have h0v : (index 0).val < kP.val := h0k
    change 0 < kP.val at h0v
    have hv1 : kP.val < (index 1).val := hk1
    change kP.val < 1 at hv1
    omega
  obtain ⟨perm, hren0, hren1, hren2⟩ :=
    exists_colourRenaming (rawColour 0) (rawColour 1) (rawColour 2) h01
  let colour : Fin 13 → BitVec 2 :=
    fun i => BitVec.ofFin (perm (rawColour i))
  let orient : Fin 13 → Fin 13 → Fin 13 → BitVec 2 := fun i j k =>
    signCode (turnSign (point i) (point j) (point k))
  apply noMc13Bits colour orient
  have hnorm0 : (colour 0 == BitVec.ofNat 2 0) = true := by
    simp [colour, hren0]
  have hnorm1 : (colour 1 == BitVec.ofNat 2 1) = true := by
    simp [colour, hren1]
  have hnorm2 : (colour 2).ult (BitVec.ofNat 2 3) = true := by
    simpa [colour, BitVec.ult] using hren2
  have hvalid (a b c : Fin 13) :
      validSignCode (orient a b c) = true := by
    exact validSignCode_signCode _
  have hquad (a b c d : Fin 13) (hab : a < b) (hbc : b < c)
      (hcd : c < d) :
      allowedQuadCode (orient a b c) (orient a b d)
        (orient a c d) (orient b c d) = true := by
    apply allowedQuadCode_of_allowedQuad
    apply allowedQuad_of_lex
    · exact (orderedPoint_strictMono P) (index_strict hab)
    · exact (orderedPoint_strictMono P) (index_strict hbc)
    · exact (orderedPoint_strictMono P) (index_strict hcd)
    · apply noTwoZero_of_noFour hfour <;>
        try exact point_mem _
      · exact point_injective.ne hab.ne
      · exact point_injective.ne (hab.trans hbc).ne
      · exact point_injective.ne (hab.trans (hbc.trans hcd)).ne
      · exact point_injective.ne hbc.ne
      · exact point_injective.ne (hbc.trans hcd).ne
      · exact point_injective.ne hcd.ne
  have hpair (a b : Fin 13) (hab : a < b) :
      blockedPairCode colour orient a b = true := by
    by_cases hc : colour a = colour b
    · have hc' : colouring ⟨point a, point_mem a⟩ =
          colouring ⟨point b, point_mem b⟩ := by
        have := congrArg BitVec.toFin hc
        have hren : perm (rawColour a) = perm (rawColour b) := by
          simpa [colour] using this
        have hraw := perm.injective hren
        simpa [rawColour] using hraw
      obtain ⟨r, hrP, hr⟩ := hblocked ⟨point a, point_mem a⟩
        ⟨point b, point_mem b⟩
        (fun he => point_injective.ne hab.ne
          (congrArg (fun x : P => (x : Point)) he)) hc'
      obtain ⟨kP, hkP⟩ := orderedPoint_surjective P r hrP
      have hlex := lex_between_of_mem_openSegment
        ((orderedPoint_strictMono P) (index_strict hab)) hr
      have hakP : index a < kP := by
        apply (orderedPoint_strictMono P).lt_iff_lt.mp
        simpa [point, hkP] using hlex.1
      have hkPb : kP < index b := by
        apply (orderedPoint_strictMono P).lt_iff_lt.mp
        simpa [point, hkP] using hlex.2
      let k : Fin 13 := ⟨kP.val, by
        have := (show kP.val < (index b).val from hkPb)
        exact lt_trans this b.isLt⟩
      have hkindex : index k = kP := by
        apply Fin.ext
        rfl
      have hak : a < k := by exact hakP
      have hkb : k < b := by exact hkPb
      have hzero : orient a k b = signCode .zero := by
        have hz : turn (point a) (point k) (point b) = 0 := by
          apply turn_eq_zero_of_mem_openSegment
          simpa [point, hkindex, hkP] using hr
        simp [orient, (turnSign_eq_zero_iff _ _ _).2 hz]
      exact blockedPairCode_of_candidate colour orient hc hak hkb hzero
    · exact blockedPairCode_of_ne colour orient hc
  simpa (disch := decide) only [hnorm0, hnorm1, hnorm2, hvalid, hquad, hpair,
    Bool.and_self, Bool.and_true, Bool.true_and]

/-- In particular, a proper four-colouring of a visibility graph under the
no-four-collinear hypothesis has at most twelve vertices. -/
theorem card_le_twelve_of_visibility_colouring
    (P : Finset Point) (hfour : ¬HasFourCollinear P)
    (C : (visibilityGraph P).Coloring (Fin 4)) :
    P.card ≤ 12 := by
  apply card_le_twelve_of_four_coloured_blocking P hfour C
  intro p q hpq hc
  have hnvis : ¬Visible P p q := by
    intro hv
    exact C.valid (show (visibilityGraph P).Adj p q from hv) hc
  exact exists_blocker (Subtype.val_injective.ne hpq) hnvis

end Lax56Proofs.HKBMcBridge
