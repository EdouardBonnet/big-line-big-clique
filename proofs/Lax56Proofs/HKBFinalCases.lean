import Lax56Proofs.HKBHexFinalGeometry
import Mathlib.Tactic

/-!
Direct, solver-free geometry for the eleven- and twelve-blocker cases in
the Hujter--Kisfaludi--Bak argument.
-/

namespace Lax56Proofs.HKBFinalCases

open Lax56.Geometry
open Lax56.HujterKisfaludiBak
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBColourClasses
open Lax56Proofs.HKBColourCoverage
open Lax56Proofs.HKBConvexity
open Lax56Proofs.HKBDiagonals
open Lax56Proofs.HKBGeometry
open Lax56Proofs.HKBHexFinalGeometry
open Lax56Proofs.HKBHexGeometry
open Lax56Proofs.HKBTriangle
open Lax56Proofs.Orientation

private def colourFiber {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) (c : Fin 4) : Finset X :=
  Finset.univ.filter fun p ↦ colour p = c

@[simp] private theorem mem_colourFiber
    {X : Type*} [Fintype X] [DecidableEq X]
    {colour : X → Fin 4} {c : Fin 4} {p : X} :
    p ∈ colourFiber colour c ↔ colour p = c := by
  simp [colourFiber]

private theorem card_eq_sum_colourFibers
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) :
    Fintype.card X = ∑ c : Fin 4, (colourFiber colour c).card := by
  simpa [colourFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset X))
      (t := (Finset.univ : Finset (Fin 4)))
      (f := colour) (by simp))

/-- In an eleven-point four-coloured set with classes of size at most three,
if one class has size two, every other class has size three. -/
private theorem other_colourFiber_card_three_of_eleven
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) (hcard : Fintype.card X = 11)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {c d : Fin 4} (hc : (colourFiber colour c).card = 2)
    (hdc : d ≠ c) : (colourFiber colour d).card = 3 := by
  have hsum := card_eq_sum_colourFibers colour
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  simp only [Fin.sum_univ_four] at hsum
  rw [hcard] at hsum
  fin_cases c
  · have hc0 : (colourFiber colour 0).card = 2 := by simpa using hc
    have hc1 : (colourFiber colour 1).card = 3 := by omega
    have hc2 : (colourFiber colour 2).card = 3 := by omega
    have hc3 : (colourFiber colour 3).card = 3 := by omega
    fin_cases d <;> simp_all

  · have hc1' : (colourFiber colour 1).card = 2 := by simpa using hc
    have hc0 : (colourFiber colour 0).card = 3 := by omega
    have hc2 : (colourFiber colour 2).card = 3 := by omega
    have hc3 : (colourFiber colour 3).card = 3 := by omega
    fin_cases d <;> simp_all
  · have hc2' : (colourFiber colour 2).card = 2 := by simpa using hc
    have hc0 : (colourFiber colour 0).card = 3 := by omega
    have hc1 : (colourFiber colour 1).card = 3 := by omega
    have hc3 : (colourFiber colour 3).card = 3 := by omega
    fin_cases d <;> simp_all
  · have hc3' : (colourFiber colour 3).card = 2 := by simpa using hc
    have hc0 : (colourFiber colour 0).card = 3 := by omega
    have hc1 : (colourFiber colour 1).card = 3 := by omega
    have hc2 : (colourFiber colour 2).card = 3 := by omega
    fin_cases d <;> simp_all

/-- With twelve points and four fibres of size at most three, every fibre
has size exactly three. -/
private theorem colourFiber_card_three_of_twelve
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) (hcard : Fintype.card X = 12)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    (c : Fin 4) : (colourFiber colour c).card = 3 := by
  have hsum := card_eq_sum_colourFibers colour
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  simp only [Fin.sum_univ_four] at hsum
  rw [hcard] at hsum
  have hc0 : (colourFiber colour 0).card = 3 := by omega
  have hc1 : (colourFiber colour 1).card = 3 := by omega
  have hc2 : (colourFiber colour 2).card = 3 := by omega
  have hc3 : (colourFiber colour 3).card = 3 := by omega
  fin_cases c <;> simp_all

/-- If a colour fiber of cardinality two contains two distinct named points,
those are all of its points. -/
private theorem eq_first_or_second_of_colourFiber_card_two
    {X : Type*} [Fintype X] [DecidableEq X]
    {colour : X → Fin 4} {c : Fin 4} {p q x : X}
    (hc : (colourFiber colour c).card = 2)
    (hp : colour p = c) (hq : colour q = c) (hpq : p ≠ q)
    (hx : colour x = c) : x = p ∨ x = q := by
  have hpMem : p ∈ colourFiber colour c := mem_colourFiber.mpr hp
  have hqMem : q ∈ colourFiber colour c := mem_colourFiber.mpr hq
  have hpair : ({p, q} : Finset X) = colourFiber colour c := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hpMem
      · exact hqMem
    · simpa [hpq, hc]
  have hxMem : x ∈ colourFiber colour c := mem_colourFiber.mpr hx
  rw [← hpair] at hxMem
  simpa [eq_comm] using hxMem

/-- A three-element colour fiber containing two distinct named points has a
unique third point.  We package the exhaustive description because the
eleven- and twelve-point arguments use it repeatedly. -/
private theorem exists_third_of_colourFiber_card_three
    {X : Type*} [Fintype X] [DecidableEq X]
    {colour : X → Fin 4} {c : Fin 4} {p q : X}
    (hc : (colourFiber colour c).card = 3)
    (hp : colour p = c) (hq : colour q = c) (hpq : p ≠ q) :
    ∃ r : X, r ≠ p ∧ r ≠ q ∧ colour r = c ∧
      ∀ x : X, colour x = c → x = p ∨ x = q ∨ x = r := by
  classical
  let C := colourFiber colour c
  have hpC : p ∈ C := mem_colourFiber.mpr hp
  have hqC : q ∈ C := mem_colourFiber.mpr hq
  have hex : ∃ r ∈ C, r ∉ ({p, q} : Finset X) := by
    by_contra hn
    push_neg at hn
    have hsub : C ⊆ ({p, q} : Finset X) := by
      intro x hx
      exact hn x hx
    have hle := Finset.card_le_card hsub
    have hpair : ({p, q} : Finset X).card = 2 := by simp [hpq]
    change C.card ≤ ({p, q} : Finset X).card at hle
    rw [hc, hpair] at hle
    omega
  obtain ⟨r, hrC, hrnot⟩ := hex
  have hrp : r ≠ p := by
    intro e
    subst r
    exact hrnot (by simp)
  have hrq : r ≠ q := by
    intro e
    subst r
    exact hrnot (by simp)
  have htriple : ({p, q, r} : Finset X) = C := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hpC
      · exact hqC
      · exact hrC
    · have hthree : ({p, q, r} : Finset X).card = 3 := by
        apply Finset.card_eq_three.mpr
        exact ⟨p, q, r, hpq, hrp.symm, hrq.symm, rfl⟩
      rw [hthree, hc]
  refine ⟨r, hrp, hrq, mem_colourFiber.mp hrC, ?_⟩
  intro x hx
  have hxC : x ∈ C := mem_colourFiber.mpr hx
  rw [← htriple] at hxC
  simpa [eq_comm] using hxC

/-- Removing one named point from a three-element colour fiber leaves two
distinct, explicitly named points of that same colour. -/
private theorem exists_two_others_of_colourFiber_card_three
    {X : Type*} [Fintype X] [DecidableEq X]
    {colour : X → Fin 4} {c : Fin 4} {v : X}
    (hc : (colourFiber colour c).card = 3) (hv : colour v = c) :
    ∃ x y : X, x ≠ y ∧ x ≠ v ∧ y ≠ v ∧
      colour x = c ∧ colour y = c := by
  classical
  let C := colourFiber colour c
  have hvC : v ∈ C := mem_colourFiber.mpr hv
  have herase : (C.erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hvC, hc]
  obtain ⟨x, y, hxy, hC⟩ := Finset.card_eq_two.mp herase
  have hxErase : x ∈ C.erase v := by rw [hC]; simp
  have hyErase : y ∈ C.erase v := by rw [hC]; simp
  have hx := Finset.mem_erase.mp hxErase
  have hy := Finset.mem_erase.mp hyErase
  exact ⟨x, y, hxy, hx.1, hy.1, mem_colourFiber.mp hx.2,
    mem_colourFiber.mp hy.2⟩

/-- A two-element colour fiber containing a named point has one other
point. -/
private theorem exists_other_of_colourFiber_card_two
    {X : Type*} [Fintype X] [DecidableEq X]
    {colour : X → Fin 4} {c : Fin 4} {v : X}
    (hc : (colourFiber colour c).card = 2) (hv : colour v = c) :
    ∃ x : X, x ≠ v ∧ colour x = c := by
  classical
  let C := colourFiber colour c
  have hvC : v ∈ C := mem_colourFiber.mpr hv
  have herase : (C.erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hvC, hc]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp herase
  have hxErase : x ∈ C.erase v := by rw [hx]; simp
  have hdata := Finset.mem_erase.mp hxErase
  exact ⟨x, hdata.1, mem_colourFiber.mp hdata.2⟩

/-- Four distinct colour names exhaust `Fin 4`. -/
private theorem fin4_exhaust_of_four_pairwise
    {a b c d x : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    x = a ∨ x = b ∨ x = c ∨ x = d := by
  omega

/-- If three non-`red` colours cover every colour other than `red`, then
they are pairwise distinct. -/
private theorem pairwise_ne_of_fin4_nonred_cover
    {red a b c : Fin 4}
    (har : a ≠ red) (hbr : b ≠ red) (hcr : c ≠ red)
    (hcover : ∀ d : Fin 4, d ≠ red → d = a ∨ d = b ∨ d = c) :
    a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  let S : Finset (Fin 4) := {a, b, c}
  have hsub : Finset.univ.erase red ⊆ S := by
    intro d hd
    have hdr : d ≠ red := (Finset.mem_erase.mp hd).1
    rcases hcover d hdr with rfl | rfl | rfl <;> simp [S]
  have hthree : (Finset.univ.erase red).card = 3 := by simp
  have hScard : S.card = 3 := by
    have hlo := Finset.card_le_card hsub
    have hhi : S.card ≤ 3 := by
      simpa [S] using (Finset.card_le_three (a := a) (b := b) (c := c))
    omega
  have habc : ({a, b, c} : Finset (Fin 4)).card = 3 := by simpa [S] using hScard
  constructor
  · intro hab
    subst b
    simp at habc
    have hle2 := Finset.card_le_two (a := a) (b := c)
    omega
  · constructor
    · intro hac
      subst c
      simp at habc
      have hle2 := Finset.card_le_two (a := b) (b := a)
      omega
    · intro hbc
      subst c
      simp at habc
      have hle2 := Finset.card_le_two (a := a) (b := b)
      omega

/-- In an eleven-element set with all colour classes of size at most three,
once one class has size three, any different class which is not of size
three has size two. -/
private theorem colourFiber_card_two_of_eleven
    {X : Type*} [Fintype X] [DecidableEq X]
    (colour : X → Fin 4) (hcard : Fintype.card X = 11)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {red blue : Fin 4} (hrb : red ≠ blue)
    (hred : (colourFiber colour red).card = 3)
    (hblue : (colourFiber colour blue).card ≠ 3) :
    (colourFiber colour blue).card = 2 := by
  let f : Fin 4 → ℕ := fun d ↦ (colourFiber colour d).card
  let R : Finset (Fin 4) := (Finset.univ.erase red).erase blue
  have hblueMem : blue ∈ Finset.univ.erase red := by
    exact Finset.mem_erase.mpr ⟨hrb.symm, Finset.mem_univ _⟩
  have hRcard : R.card = 2 := by
    dsimp [R]
    rw [Finset.card_erase_of_mem hblueMem,
      Finset.card_erase_of_mem (Finset.mem_univ red)]
    simp
  have hRle : (∑ d ∈ R, f d) ≤ 6 := by
    calc
      (∑ d ∈ R, f d) ≤ (∑ _d ∈ R, 3) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hle d
      _ = R.card * 3 := by simp
      _ = 6 := by rw [hRcard]
  have hdecomp : (∑ d : Fin 4, f d) =
      f red + f blue + (∑ d ∈ R, f d) := by
    rw [← Finset.add_sum_erase _ f (Finset.mem_univ red),
      ← Finset.add_sum_erase _ f hblueMem]
    simp [R, add_assoc]
  have hsum : (∑ d : Fin 4, f d) = 11 := by
    rw [← hcard]
    exact (card_eq_sum_colourFibers colour).symm
  have hblueLe := hle blue
  have hblueLeTwo : f blue ≤ 2 := by
    dsimp [f]
    omega
  have hblueGeTwo : 2 ≤ f blue := by
    have hfred : f red = 3 := by simpa [f] using hred
    rw [hdecomp, hfred] at hsum
    omega
  dsimp [f] at hblueLeTwo hblueGeTwo
  omega

/-- A five-element set cannot inject into four colours. -/
private theorem exists_same_colour_pair_of_card_five
    {X : Type*} [Fintype X] (hcard : Fintype.card X = 5)
    (colour : X → Fin 4) :
    ∃ p q : X, p ≠ q ∧ colour p = colour q := by
  by_contra hn
  push Not at hn
  have hinj : Function.Injective colour := by
    intro p q hpq
    by_contra hpqne
    exact hn p q hpqne hpq
  have hle := Fintype.card_le_of_injective colour hinj
  simp [hcard] at hle

/-- The only positive four-part partitions of six, with parts at most
three, are `3,1,1,1` and `2,2,1,1` up to permutation. -/
private theorem six_as_four_positive_parts
    (f : Fin 4 → ℕ)
    (hsum : (∑ c : Fin 4, f c) = 6)
    (hpos : ∀ c, 1 ≤ f c) (hle : ∀ c, f c ≤ 3) :
    (∃ c, f c = 3) ∨
      ∃ c d, c ≠ d ∧ f c = 2 ∧ f d = 2 := by
  simp only [Fin.sum_univ_four] at hsum
  by_cases h03 : f 0 = 3
  · exact Or.inl ⟨0, h03⟩
  by_cases h13 : f 1 = 3
  · exact Or.inl ⟨1, h13⟩
  by_cases h23 : f 2 = 3
  · exact Or.inl ⟨2, h23⟩
  by_cases h33 : f 3 = 3
  · exact Or.inl ⟨3, h33⟩
  have h0p := hpos 0
  have h1p := hpos 1
  have h2p := hpos 2
  have h3p := hpos 3
  have h0l := hle 0
  have h1l := hle 1
  have h2l := hle 2
  have h3l := hle 3
  by_cases h02 : f 0 = 2
  · by_cases h12 : f 1 = 2
    · exact Or.inr ⟨0, 1, by decide, h02, h12⟩
    by_cases h22 : f 2 = 2
    · exact Or.inr ⟨0, 2, by decide, h02, h22⟩
    by_cases h32 : f 3 = 2
    · exact Or.inr ⟨0, 3, by decide, h02, h32⟩
    omega
  · by_cases h12 : f 1 = 2
    · by_cases h22 : f 2 = 2
      · exact Or.inr ⟨1, 2, by decide, h12, h22⟩
      by_cases h32 : f 3 = 2
      · exact Or.inr ⟨1, 3, by decide, h12, h32⟩
      omega
    · have h22 : f 2 = 2 := by omega
      have h32 : f 3 = 2 := by omega
      exact Or.inr ⟨2, 3, by decide, h22, h32⟩

private theorem exists_fourth_fin4
    {a b c : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ d : Fin 4, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  classical
  let S : Finset (Fin 4) := {a, b, c}
  have hScard : S.card = 3 := by
    apply Finset.card_eq_three.mpr
    exact ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hnot : ¬(Finset.univ : Finset (Fin 4)) ⊆ S := by
    intro hsub
    have hc := Finset.card_le_card hsub
    simp [hScard] at hc
  obtain ⟨d, -, hdS⟩ := Finset.not_subset.mp hnot
  have hd : d ≠ a ∧ d ≠ b ∧ d ≠ c := by
    simpa [S, not_or] using hdS
  exact ⟨d, hd⟩

/-- Two different pairs cannot block one another: their four endpoints
would lie on the same line. -/
private theorem crossed_pairs_impossible
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a b c d : B}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hc : (c : Point) ∈ openSegment ℝ (a : Point) (b : Point))
    (ha : (a : Point) ∈ openSegment ℝ (c : Point) (d : Point)) : False := by
  have hbLine : (b : Point) ∈ affineSpan ℝ {(a : Point), (c : Point)} :=
    right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hab) hc
  have hdLine : (d : Point) ∈ affineSpan ℝ {(a : Point), (c : Point)} := by
    simpa only [Set.pair_comm] using
      right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hcd) ha
  have hbd' : b = d := by
    apply Subtype.ext
    exact Lax56Proofs.Blockers.third_point_unique hfour
      a.property c.property b.property d.property
      (Subtype.val_injective.ne hac)
      (Subtype.val_injective.ne hab.symm)
      (Subtype.val_injective.ne hbc)
      (Subtype.val_injective.ne had.symm)
      (Subtype.val_injective.ne hcd.symm)
      hbLine hdLine
  exact hbd hbd'

/-- A finite collection of points of the subtype `B` cannot be larger than
a point finset containing all of their underlying points. -/
private theorem card_le_of_val_mem
    {B I : Finset Point} {K : Finset B}
    (hsub : ∀ z : B, z ∈ K → (z : Point) ∈ I) :
    K.card ≤ I.card := by
  let f : K → I := fun z ↦ ⟨(z.1 : Point), hsub z.1 z.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : I ↦ (z : Point)) hxy
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective f hf

private theorem six_vector_injective
    {X : Type*} {a b c d e f : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    Function.Injective (![a, b, c, d, e, f] : Fin 6 → X) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Cyclic counterclockwise order on three distinct labels of a hexagon. -/
private def Cyclic3 (i j k : Fin 6) : Prop :=
  (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j)

private instance cyclic3Decidable (i j k : Fin 6) :
    Decidable (Cyclic3 i j k) := by
  unfold Cyclic3
  infer_instance

private theorem turn_pos_of_cyclic_of_increasing
    {f : Fin 6 → Point}
    (hinc : ∀ i j k : Fin 6, i < j → j < k →
      0 < turn (f i) (f j) (f k))
    {i j k : Fin 6} (hc : Cyclic3 i j k) :
    0 < turn (f i) (f j) (f k) := by
  rcases hc with ⟨hij, hjk⟩ | ⟨hjk, hki⟩ | ⟨hki, hij⟩
  · exact hinc i j k hij hjk
  · simpa only [turn_rotate] using hinc j k i hjk hki
  · simpa only [turn_rotate] using hinc k i j hki hij

private theorem turn_pos_of_cyclic
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {i j k : Fin 6} (hc : Cyclic3 i j k) :
    0 < turn (h i) (h j) (h k) :=
  turn_pos_of_cyclic_of_increasing hh.2.2 hc

private theorem cyclic_or_reverse
    {i j k : Fin 6} (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i) :
    Cyclic3 i j k ∨ Cyclic3 j i k := by
  unfold Cyclic3
  omega

private theorem turn_neg_of_reverse_cyclic
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {i j k : Fin 6} (hc : Cyclic3 j i k) :
    turn (h i) (h j) (h k) < 0 := by
  have hp := turn_pos_of_cyclic hh hc
  rw [turn_swap_first] at hp
  linarith

/-- Oriented area is affine in each of its three arguments. -/
private theorem turn_segment_combo_first
    (a a' b c : Point) (u : ℝ) :
    turn ((1 - u) • a + u • a') b c =
      (1 - u) * turn a b c + u * turn a' b c := by
  have h := turn_convex_combo b c a a' (1 - u) u (by ring)
  simpa only [turn_rotate] using h

private theorem turn_segment_combo_second
    (a b b' c : Point) (v : ℝ) :
    turn a ((1 - v) • b + v • b') c =
      (1 - v) * turn a b c + v * turn a b' c := by
  have h := turn_convex_combo c a b b' (1 - v) v (by ring)
  calc
    turn a ((1 - v) • b + v • b') c =
        turn c a ((1 - v) • b + v • b') :=
      turn_rotate c a ((1 - v) • b + v • b')
    _ = (1 - v) * turn c a b + v * turn c a b' := h
    _ = (1 - v) * turn a b c + v * turn a b' c := by
      rw [turn_rotate c a b, turn_rotate c a b']

private theorem turn_segment_combo_third
    (a b c c' : Point) (w : ℝ) :
    turn a b ((1 - w) • c + w • c') =
      (1 - w) * turn a b c + w * turn a b c' := by
  exact turn_convex_combo a b c c' (1 - w) w (by ring)

/-- Triaffinity of oriented area, expanded for three points on three
segments. -/
private theorem turn_three_lineMaps
    (a a' b b' c c' : Point) (u v w : ℝ) :
    turn ((1 - u) • a + u • a') ((1 - v) • b + v • b')
        ((1 - w) • c + w • c') =
      (1 - u) * (1 - v) * (1 - w) * turn a b c +
      (1 - u) * (1 - v) * w * turn a b c' +
      (1 - u) * v * (1 - w) * turn a b' c +
      (1 - u) * v * w * turn a b' c' +
      u * (1 - v) * (1 - w) * turn a' b c +
      u * (1 - v) * w * turn a' b c' +
      u * v * (1 - w) * turn a' b' c +
      u * v * w * turn a' b' c' := by
  simp only [turn_segment_combo_first, turn_segment_combo_second,
    turn_segment_combo_third]
  ring

/-- Endpoints chosen from three cyclically ordered sides occur in cyclic
order, except when two chosen endpoints coincide. -/
private theorem side_endpoints_cyclic_or_eq
    {i j k a b c : Fin 6} (hij : i < j) (hjk : j < k)
    (ha : a = i ∨ a = i + 1) (hb : b = j ∨ b = j + 1)
    (hc : c = k ∨ c = k + 1) :
    a = b ∨ b = c ∨ c = a ∨ Cyclic3 a b c := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc
  all_goals
    subst a
    subst b
    subst c
    unfold Cyclic3
    omega

private theorem hex_side_endpoint_turn_nonneg
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    {i j k a b c : Fin 6} (hij : i < j) (hjk : j < k)
    (ha : a = i ∨ a = i + 1) (hb : b = j ∨ b = j + 1)
    (hc : c = k ∨ c = k + 1) :
    0 ≤ turn (h a) (h b) (h c) := by
  rcases side_endpoints_cyclic_or_eq hij hjk ha hb hc with
    hab | hbc | hca | hcyc
  · subst b; simp only [turn]; ring_nf; norm_num
  · subst c; simp only [turn]; ring_nf; norm_num
  · subst c; simp only [turn]; ring_nf; norm_num
  · exact (turn_pos_of_cyclic hh hcyc).le

/-- Choosing one point in the relative interior of every side preserves the
strict cyclic convex order. -/
private theorem sideBlockers_strictConvexHexagon
    {B : Finset Point} {h : Fin 6 → Point}
    (hh : StrictConvexHexagon h)
    (hside : ∀ i : Fin 6, ∃ r ∈ B,
      r ∈ openSegment ℝ (h i) (h (i + 1))) :
    StrictConvexHexagon (sideBlocker hside) := by
  have hinc : ∀ i j k : Fin 6, i < j → j < k →
      0 < turn (sideBlocker hside i) (sideBlocker hside j)
        (sideBlocker hside k) := by
    intro i j k hij hjk
    have hui' := sideBlocker_between hside i
    have hvj' := sideBlocker_between hside j
    have hwk' := sideBlocker_between hside k
    rw [openSegment_eq_image] at hui' hvj' hwk'
    obtain ⟨u, hu, hui⟩ := hui'
    obtain ⟨v, hv, hvj⟩ := hvj'
    obtain ⟨w, hw, hwk⟩ := hwk'
    rcases hu with ⟨hu0, hu1⟩
    rcases hv with ⟨hv0, hv1⟩
    rcases hw with ⟨hw0, hw1⟩
    rw [← hui, ← hvj, ← hwk, turn_three_lineMaps]
    have h000 : 0 < (1 - u) * (1 - v) * (1 - w) *
        turn (h i) (h j) (h k) := by
      have hijk := hh.2.2 i j k hij hjk
      positivity
    have h001 : 0 ≤ (1 - u) * (1 - v) * w *
        turn (h i) (h j) (h (k + 1)) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i) (b := j) (c := k + 1)
        (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
      positivity
    have h010 : 0 ≤ (1 - u) * v * (1 - w) *
        turn (h i) (h (j + 1)) (h k) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i) (b := j + 1) (c := k)
        (Or.inl rfl) (Or.inr rfl) (Or.inl rfl)
      positivity
    have h011 : 0 ≤ (1 - u) * v * w *
        turn (h i) (h (j + 1)) (h (k + 1)) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i) (b := j + 1) (c := k + 1)
        (Or.inl rfl) (Or.inr rfl) (Or.inr rfl)
      positivity
    have h100 : 0 ≤ u * (1 - v) * (1 - w) *
        turn (h (i + 1)) (h j) (h k) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i + 1) (b := j) (c := k)
        (Or.inr rfl) (Or.inl rfl) (Or.inl rfl)
      positivity
    have h101 : 0 ≤ u * (1 - v) * w *
        turn (h (i + 1)) (h j) (h (k + 1)) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i + 1) (b := j) (c := k + 1)
        (Or.inr rfl) (Or.inl rfl) (Or.inr rfl)
      positivity
    have h110 : 0 ≤ u * v * (1 - w) *
        turn (h (i + 1)) (h (j + 1)) (h k) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i + 1) (b := j + 1) (c := k)
        (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
      positivity
    have h111 : 0 ≤ u * v * w *
        turn (h (i + 1)) (h (j + 1)) (h (k + 1)) := by
      have ht := hex_side_endpoint_turn_nonneg hh hij hjk
        (a := i + 1) (b := j + 1) (c := k + 1)
        (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      positivity
    linarith
  refine ⟨sideBlocker_injective hh hside, ?_, hinc⟩
  intro i j hji hjs
  apply turn_pos_of_cyclic_of_increasing hinc
  fin_cases i <;> fin_cases j <;> simp_all [Cyclic3]

private noncomputable def negativeSideIndices (f : Fin 6 → Point) (i j : Fin 6) :
    Finset (Fin 6) :=
  Finset.univ.filter fun k ↦ turn (f i) (f j) (f k) < 0

private def reverseCyclicIndices (i j : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter fun k ↦ Cyclic3 j i k

private theorem negativeSideIndices_eq_reverseCyclic
    {f : Fin 6 → Point} (hf : StrictConvexHexagon f)
    {i j : Fin 6} (hij : i ≠ j) :
    negativeSideIndices f i j = reverseCyclicIndices i j := by
  classical
  ext k
  simp only [negativeSideIndices, reverseCyclicIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hneg
    have hki : k ≠ i := by
      intro e
      subst k
      rw [turn_self_left] at hneg
      linarith
    have hkj : k ≠ j := by
      intro e
      subst k
      rw [turn_self_right] at hneg
      linarith
    rcases cyclic_or_reverse hij hkj.symm hki with hc | hc
    · exact (not_lt_of_ge (turn_pos_of_cyclic hf hc).le hneg).elim
    · exact hc
  · exact turn_neg_of_reverse_cyclic hf

/-- A chord of a cyclically labelled hexagon with exactly two vertices on
its negative side joins opposite labels. -/
private theorem eq_add_three_of_negativeSideIndices_card_two
    {f : Fin 6 → Point} (hf : StrictConvexHexagon f)
    {i j : Fin 6} (hij : i ≠ j)
    (hcard : (negativeSideIndices f i j).card = 2) :
    j = i + 3 := by
  classical
  rw [negativeSideIndices_eq_reverseCyclic hf hij] at hcard
  fin_cases i <;> fin_cases j <;>
    simp_all [reverseCyclicIndices, Cyclic3]
  all_goals
    revert hcard
    decide

/-- If `u` is strictly between `a` and `c`, then `a` cannot in turn be a
blocker strictly between `u` and a fourth point.  Otherwise no-four-collinear
first identifies that fourth point with `c`, and the two strict betweenness
relations have incompatible orders. -/
private theorem saturated_left_endpoint_not_between
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a c u x : B} (hac : a ≠ c)
    (hu : (u : Point) ∈ openSegment ℝ (a : Point) (c : Point)) :
    ¬((a : Point) ∈ openSegment ℝ (u : Point) (x : Point)) := by
  intro ha
  have hau : a ≠ u := by
    intro e
    subst u
    exact (Subtype.val_injective.ne hac)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hu)
  have hcu : c ≠ u := by
    intro e
    subst u
    exact (Subtype.val_injective.ne hac)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hu)
  have hux : u ≠ x := by
    intro e
    subst x
    exact hau (by simpa using ha)
  have hxa : x ≠ a := by
    intro e
    subst x
    have hua : u = a := by simpa using ha
    exact hau hua.symm
  have hcline : (c : Point) ∈ affineSpan ℝ {(a : Point), (u : Point)} :=
    right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hac) hu
  have hxline : (x : Point) ∈ affineSpan ℝ {(a : Point), (u : Point)} := by
    simpa only [Set.pair_comm] using
      right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hux) ha
  have hcx : c = x := by
    apply Subtype.ext
    exact Lax56Proofs.Blockers.third_point_unique hfour
      a.property u.property c.property x.property
      (Subtype.val_injective.ne hau) (Subtype.val_injective.ne hac.symm)
      (Subtype.val_injective.ne hcu)
      (Subtype.val_injective.ne hxa) (Subtype.val_injective.ne hux.symm)
      hcline hxline
  have ha' : (a : Point) ∈ openSegment ℝ (u : Point) (c : Point) := by
    simpa [hcx] using ha
  exact not_two_mutual_openSegments (Subtype.val_injective.ne hac.symm)
    ⟨by simpa only [openSegment_symm] using hu,
      by simpa only [openSegment_symm] using ha'⟩

/-- The symmetric endpoint version of
`saturated_left_endpoint_not_between`. -/
private theorem saturated_right_endpoint_not_between
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a c u x : B} (hac : a ≠ c)
    (hu : (u : Point) ∈ openSegment ℝ (a : Point) (c : Point)) :
    ¬((c : Point) ∈ openSegment ℝ (u : Point) (x : Point)) := by
  apply saturated_left_endpoint_not_between hfour hac.symm
  simpa only [openSegment_symm] using hu

/-- Once two points of a no-four-collinear set fix a line, any two further
points of the set on that line coincide. -/
private theorem extra_points_eq_on_saturated_line
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a b x y : B} (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b)
    (hya : y ≠ a) (hyb : y ≠ b)
    (hx : (x : Point) ∈ affineSpan ℝ {(a : Point), (b : Point)})
    (hy : (y : Point) ∈ affineSpan ℝ {(a : Point), (b : Point)}) :
    x = y := by
  apply Subtype.ext
  exact Lax56Proofs.Blockers.third_point_unique hfour
    a.property b.property x.property y.property
    (Subtype.val_injective.ne hab)
    (Subtype.val_injective.ne hxa) (Subtype.val_injective.ne hxb)
    (Subtype.val_injective.ne hya) (Subtype.val_injective.ne hyb) hx hy

/-- A no-four-collinear set has at most one point of the set in the open
segment between two fixed points of the set. -/
private theorem openSegment_point_unique
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a b x y : B} (hab : a ≠ b)
    (hx : (x : Point) ∈ openSegment ℝ (a : Point) (b : Point))
    (hy : (y : Point) ∈ openSegment ℝ (a : Point) (b : Point)) :
    x = y := by
  have hxa : x ≠ a := by
    intro e
    subst x
    exact (Subtype.val_injective.ne hab)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hx)
  have hxb : x ≠ b := by
    intro e
    subst x
    exact (Subtype.val_injective.ne hab)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hx)
  have hya : y ≠ a := by
    intro e
    subst y
    exact (Subtype.val_injective.ne hab)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hy)
  have hyb : y ≠ b := by
    intro e
    subst y
    exact (Subtype.val_injective.ne hab)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hy)
  apply Subtype.ext
  exact Lax56Proofs.Blockers.third_point_unique hfour
    a.property b.property x.property y.property
    (Subtype.val_injective.ne hab)
    (Subtype.val_injective.ne hxa) (Subtype.val_injective.ne hxb)
    (Subtype.val_injective.ne hya) (Subtype.val_injective.ne hyb)
    (Lax56Proofs.Blockers.mem_affineSpan_pair_of_mem_openSegment hx)
    (Lax56Proofs.Blockers.mem_affineSpan_pair_of_mem_openSegment hy)

/-- If a point between `x` and `y` is on an oriented line and `x` is on
its positive side, then `y` is on its negative side. -/
theorem turn_neg_of_between_of_turn_eq_zero_of_pos
    {a b x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hz0 : turn a b z = 0) (hx : 0 < turn a b x) :
    turn a b y < 0 := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := a) (b := b) hz
  rw [hz0] at heq
  nlinarith

/-- An open segment between two points in a strict negative half-plane
stays in that strict half-plane. -/
theorem turn_neg_of_mem_openSegment
    {a b x y z : Point} (hz : z ∈ openSegment ℝ x y)
    (hx : turn a b x < 0) (hy : turn a b y < 0) :
    turn a b z < 0 := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := a) (b := b) hz
  rw [heq]
  have hleft : 0 < 1 - t := sub_pos.mpr ht1
  nlinarith [mul_neg_of_pos_of_neg hleft hx, mul_neg_of_pos_of_neg ht0 hy]

/-- The crosscut joining points on `pr` and `qr` separates `r` from
`p,q`, and hence from every point strictly between `p` and `q`.  This is
Lemma 7.3 with all signs made explicit. -/
theorem triangle_crosscut_signs
    {p q r v g b : Point} (hpqr : 0 < turn p q r)
    (hv : v ∈ openSegment ℝ p q)
    (hg : g ∈ openSegment ℝ p r)
    (hb : b ∈ openSegment ℝ q r) :
    0 < turn b g p ∧ 0 < turn b g q ∧
      0 < turn b g v ∧ turn b g r < 0 := by
  have hrpq : 0 < turn r p q := by
    rw [turn_rotate, turn_rotate]
    exact hpqr
  have hrpb : 0 < turn r p b :=
    edgeTurn_pos_of_mem_openSegment hb hrpq.le (by simp) (Or.inl hrpq)
  have hpbr : 0 < turn p b r := by
    rw [turn_rotate r p b]
    exact hrpb
  have hpbg : 0 < turn p b g :=
    edgeTurn_pos_of_mem_openSegment hg (by simp) hpbr.le (Or.inr hpbr)
  have hbgp : 0 < turn b g p := by
    rw [turn_rotate p b g]
    exact hpbg
  have hbgr : turn b g r < 0 := by
    exact turn_neg_of_between_of_turn_eq_zero_of_pos hg (by simp) hbgp
  have hbgq : 0 < turn b g q := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := b) (b := g) hb
    simp only [turn_self_left] at heq
    nlinarith
  have hbgv : 0 < turn b g v :=
    edgeTurn_pos_of_mem_openSegment hv hbgp.le hbgq.le (Or.inl hbgp)
  exact ⟨hbgp, hbgq, hbgv, hbgr⟩

/-- Supporting-line signs for the three side points of an oriented
triangle.  These are the sign form of the radial-order facts used in the
eleven-point case. -/
theorem triangle_side_support_signs
    {p q r v g b : Point} (hpqr : 0 < turn p q r)
    (hv : v ∈ openSegment ℝ p q)
    (hg : g ∈ openSegment ℝ p r)
    (hb : b ∈ openSegment ℝ q r) :
    (turn p v p = 0 ∧ turn p v q = 0 ∧ turn p v v = 0 ∧
      0 < turn p v r ∧ 0 < turn p v g ∧ 0 < turn p v b) ∧
    (turn g p g = 0 ∧ turn g p p = 0 ∧ turn g p r = 0 ∧
      0 < turn g p q ∧ 0 < turn g p v ∧ 0 < turn g p b) ∧
    (turn v q p = 0 ∧ turn v q q = 0 ∧ turn v q v = 0 ∧
      0 < turn v q r ∧ 0 < turn v q g ∧ 0 < turn v q b) ∧
    (turn q b q = 0 ∧ turn q b b = 0 ∧ turn q b r = 0 ∧
      0 < turn q b p ∧ 0 < turn q b v ∧ 0 < turn q b g) := by
  have hpvq : turn p v q = 0 := by
    have hz := turn_eq_zero_of_between hv
    rw [turn_swap_last p q v, hz, neg_zero]
  have hpvr : 0 < turn p v r := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := p) (b := r) hv
    simp only [turn_self_left] at heq
    have hprq : turn p r q < 0 := by
      rw [turn_swap_last]
      linarith
    have hprv : turn p r v < 0 := by rw [heq]; nlinarith
    rw [turn_swap_last]
    linarith
  have hpvg : 0 < turn p v g :=
    edgeTurn_pos_of_mem_openSegment hg (by simp) hpvr.le (Or.inr hpvr)
  have hpvb : 0 < turn p v b :=
    edgeTurn_pos_of_mem_openSegment hb (by simpa [hpvq]) hpvr.le (Or.inr hpvr)
  have hgpr : turn g p r = 0 := by
    have hz := turn_eq_zero_of_between hg
    exact (turn_rotate g p r).symm.trans hz
  have hgpq : 0 < turn g p q := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := p) (b := q) hg
    simp only [turn_self_left] at heq
    have hpqg : 0 < turn p q g := by rw [heq]; nlinarith
    simpa only [turn_rotate] using hpqg
  have hgpv : 0 < turn g p v :=
    edgeTurn_pos_of_mem_openSegment hv (by simp) hgpq.le (Or.inr hgpq)
  have hgpb : 0 < turn g p b :=
    edgeTurn_pos_of_mem_openSegment hb hgpq.le (by simpa [hgpr]) (Or.inl hgpq)
  have hvqp : turn v q p = 0 := by
    have hz := turn_eq_zero_of_between hv
    rw [turn_reverse p q v, hz, neg_zero]
  have hvqr : 0 < turn v q r := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := q) (b := r) hv
    simp only [turn_self_left] at heq
    have hqrp : 0 < turn q r p := by
      rw [turn_rotate p q r]
      exact hpqr
    have hqrv : 0 < turn q r v := by rw [heq]; nlinarith
    rw [← turn_rotate v q r]
    exact hqrv
  have hvqg : 0 < turn v q g :=
    edgeTurn_pos_of_mem_openSegment hg (by simpa [hvqp]) hvqr.le (Or.inr hvqr)
  have hvqb : 0 < turn v q b :=
    edgeTurn_pos_of_mem_openSegment hb (by simp) hvqr.le (Or.inr hvqr)
  have hqbr : turn q b r = 0 := by
    have hz := turn_eq_zero_of_between hb
    rw [turn_swap_last, hz, neg_zero]
  have hqbp : 0 < turn q b p := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := q) (b := p) hb
    simp only [turn_self_left] at heq
    have hqrp : 0 < turn q r p := by
      simpa only [turn_rotate] using hpqr
    have hqpr : turn q p r < 0 := by rw [turn_swap_last]; linarith
    have hqpb : turn q p b < 0 := by rw [heq]; nlinarith
    rw [turn_swap_last]
    linarith
  have hqbv : 0 < turn q b v :=
    edgeTurn_pos_of_mem_openSegment hv hqbp.le (by simp) (Or.inl hqbp)
  have hqbg : 0 < turn q b g :=
    edgeTurn_pos_of_mem_openSegment hg hqbp.le (by simpa [hqbr]) (Or.inl hqbp)
  exact ⟨⟨by simp, hpvq, by simp, hpvr, hpvg, hpvb⟩,
    ⟨by simp, by simp, hgpr, hgpq, hgpv, hgpb⟩,
    ⟨hvqp, by simp, by simp, hvqr, hvqg, hvqb⟩,
    ⟨by simp, by simp, hqbr, hqbp, hqbv, hqbg⟩⟩

/-- A zero supporting determinant cuts the corresponding closed side out of
a nondegenerate triangle hull. -/
private theorem mem_segment_of_mem_triangleHull_of_turn_eq_zero
    {a b c x : Point} (habc : 0 < turn a b c)
    (hx : x ∈ triangleHull a b c) (hx0 : turn a b x = 0) :
    x ∈ segment ℝ a b := by
  have hweak := triangle_edge_nonneg habc.le hx
  have hsum := turn_triangle_decompose a b c x
  have hbc : 0 ≤ turn b c x := hweak.2.1
  have hca : 0 ≤ turn c a x := hweak.2.2
  let t : ℝ := turn c a x / turn a b c
  have ht0 : 0 ≤ t := div_nonneg hca habc.le
  have hca_le : turn c a x ≤ turn a b c := by
    rw [hsum, hx0]
    linarith
  have ht1 : t ≤ 1 := (div_le_one habc).mpr hca_le
  rw [segment_eq_image]
  refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
  apply Prod.ext
  · have hcoord :
        turn b c x * a.1 + turn c a x * b.1 + turn a b x * c.1 =
          turn a b c * x.1 := by
      simp only [turn]
      ring
    dsimp [t]
    rw [hx0] at hcoord hsum
    simp only [zero_mul, add_zero] at hcoord
    field_simp [habc.ne']
    linear_combination hcoord + a.1 * hsum
  · have hcoord :
        turn b c x * a.2 + turn c a x * b.2 + turn a b x * c.2 =
          turn a b c * x.2 := by
      simp only [turn]
      ring
    dsimp [t]
    rw [hx0] at hcoord hsum
    simp only [zero_mul, add_zero] at hcoord
    field_simp [habc.ne']
    linear_combination hcoord + a.2 * hsum

/-- A nonvertex point of the boundary of a nondegenerate triangle lies in
the relative interior of one of its three sides. -/
private theorem mem_openSide_of_mem_triangleHull_not_strict
    {a b c x : Point} (habc : 0 < turn a b c)
    (hx : x ∈ triangleHull a b c)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c)
    (hnot : ¬StrictlyInsideTriangle a b c x) :
    x ∈ openSegment ℝ a b ∨ x ∈ openSegment ℝ b c ∨
      x ∈ openSegment ℝ c a := by
  have hw := triangle_edge_nonneg habc.le hx
  by_cases hab : 0 < turn a b x
  · by_cases hbc : 0 < turn b c x
    · have hca : turn c a x = 0 := by
        by_contra hn
        have : 0 < turn c a x := lt_of_le_of_ne hw.2.2 (Ne.symm hn)
        exact hnot ⟨hab, hbc, this⟩
      right
      right
      apply mem_openSegment_of_ne_left_right hxc.symm hxa.symm
      apply mem_segment_of_mem_triangleHull_of_turn_eq_zero
        (a := c) (b := a) (c := b) (x := x)
        (by simpa only [turn_rotate, turn_rotate] using habc)
      · rw [triangleHull_rotate b c a, triangleHull_rotate a b c]
        exact hx
      · exact hca
    · have hbc0 : turn b c x = 0 := le_antisymm (le_of_not_gt hbc) hw.2.1
      right
      left
      apply mem_openSegment_of_ne_left_right hxb.symm hxc.symm
      apply mem_segment_of_mem_triangleHull_of_turn_eq_zero
        (a := b) (b := c) (c := a) (x := x)
        (by simpa only [turn_rotate] using habc)
      · rw [triangleHull_rotate a b c]
        exact hx
      · exact hbc0
  · have hab0 : turn a b x = 0 := le_antisymm (le_of_not_gt hab) hw.1
    left
    apply mem_openSegment_of_ne_left_right hxa.symm hxb.symm
    exact mem_segment_of_mem_triangleHull_of_turn_eq_zero habc hx hab0

/-- A vertex of a nondegenerate triangle cannot lie strictly between two
points of that triangle hull.  The proof exposes the vertex with its two
incident supporting lines. -/
private theorem triangle_vertex_not_between_hull_points
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {a b c x y : B} (habc : 0 < turn (a : Point) (b : Point) (c : Point))
    (hx : (x : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
    (hy : (y : Point) ∈ triangleHull (a : Point) (b : Point) (c : Point))
    (ha : (a : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) : False := by
  have hxw := triangle_edge_nonneg habc.le hx
  have hyw := triangle_edge_nonneg habc.le hy
  obtain ⟨t, ht0, ht1, habEq⟩ :=
    turn_of_mem_openSegment (a := (a : Point)) (b := (b : Point)) ha
  simp only [turn_self_left] at habEq
  have hxab0 : turn (a : Point) (b : Point) (x : Point) = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) hxw.1,
      mul_nonneg ht0.le hyw.1]
  obtain ⟨s, hs0, hs1, hcaEq⟩ :=
    turn_of_mem_openSegment (a := (c : Point)) (b := (a : Point)) ha
  simp only [turn_self_right] at hcaEq
  have hxca0 : turn (c : Point) (a : Point) (x : Point) = 0 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1.le) hxw.2.2,
      mul_nonneg hs0.le hyw.2.2]
  have hab : a ≠ b := by
    intro e
    subst b
    simpa [turn] using habc
  have hac : a ≠ c := by
    intro e
    subst c
    simpa using habc
  have hbc : b ≠ c := by
    intro e
    subst c
    simpa using habc
  have hxAB : (x : Point) ∈ affineSpan ℝ {(a : Point), (b : Point)} :=
    mem_line_of_turn_eq_zero (Subtype.val_injective.ne hab) hxab0
  have hxAC : (x : Point) ∈ affineSpan ℝ {(a : Point), (c : Point)} := by
    simpa only [Set.pair_comm] using
      mem_line_of_turn_eq_zero (Subtype.val_injective.ne hac.symm) hxca0
  have hbLine : (b : Point) ∈ affineSpan ℝ {(a : Point), (x : Point)} := by
    rw [affineSpan_pair_eq_of_right_mem_of_ne hxAB
      (Subtype.val_injective.ne hxa)]
    exact right_mem_affineSpan_pair ℝ (a : Point) (b : Point)
  have hcLine : (c : Point) ∈ affineSpan ℝ {(a : Point), (x : Point)} := by
    rw [affineSpan_pair_eq_of_right_mem_of_ne hxAC
      (Subtype.val_injective.ne hxa)]
    exact right_mem_affineSpan_pair ℝ (a : Point) (c : Point)
  have hbcEq : b = c := by
    apply Subtype.ext
    exact Lax56Proofs.Blockers.third_point_unique hfour
      a.property x.property b.property c.property
      (Subtype.val_injective.ne hxa.symm)
      (Subtype.val_injective.ne hab.symm) (Subtype.val_injective.ne hxb.symm)
      (Subtype.val_injective.ne hac.symm) (Subtype.val_injective.ne hxc.symm)
      hbLine hcLine
  exact hbc hbcEq

/-- A point of a triangle hull which is not one of its vertices is strictly
inside the ambient empty hexagon as soon as all three vertices are blockers.
This is the supporting-face lemma in the reusable form needed below. -/
private theorem triangleHull_nonvertex_strictlyInsideHexagon
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    {a b c x : hexBlockers P h}
    (hxHull : (x : Point) ∈
      triangleHull (a : Point) (b : Point) (c : Point))
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    StrictlyInsideHexagon h x := by
  by_contra hxNot
  obtain ⟨i, hxi⟩ :=
    (not_strictlyInside_iff_sideBlocker hfour hh hhP hside x.property).mp hxNot
  let A : Finset Point := {(a : Point), (b : Point), (c : Point)}
  have hAB : A ⊆ hexBlockers P h := by
    intro z hz
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> exact Subtype.property _
  have hsHull : sideBlocker hside i ∈ convexHull ℝ (A : Set Point) := by
    rw [← hxi]
    simpa [A, triangleHull] using hxHull
  have hsA := sideBlocker_mem_of_mem_convexHull
    hfour hh hhP hside hAB i hsHull
  have hxA : (x : Point) ∈ A := by simpa [hxi] using hsA
  simp only [A, Finset.mem_insert, Finset.mem_singleton] at hxA
  rcases hxA with h | h | h
  · exact hxa (Subtype.ext h)
  · exact hxb (Subtype.ext h)
  · exact hxc (Subtype.ext h)

/-- The rigid configuration produced by the size-two red branch at eleven
blockers. -/
private structure ElevenRedTwoStructure
    {P : Finset Point} {h : Fin 6 → Point}
    (colour : hexBlockers P h → Fin 4) where
  p : hexBlockers P h
  q : hexBlockers P h
  v : hexBlockers P h
  x : hexBlockers P h
  y : hexBlockers P h
  g : hexBlockers P h
  b : hexBlockers P h
  hpq : p ≠ q
  hvx : v ≠ x
  hxy : x ≠ y
  hyv : y ≠ v
  hred : colour p = colour q
  hredCard : (colourFiber colour (colour p)).card = 2
  hblueX : colour v = colour x
  hblueY : colour x = colour y
  hredBlue : colour p ≠ colour v
  htriangle : 0 < turn (v : Point) (x : Point) (y : Point)
  hpv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point)
  hpbase : (p : Point) ∈ openSegment ℝ (x : Point) (y : Point)
  hg : (g : Point) ∈ openSegment ℝ (v : Point) (y : Point)
  hb : (b : Point) ∈ openSegment ℝ (v : Point) (x : Point)
  hxBoundary : ¬StrictlyInsideHexagon h x
  hyBoundary : ¬StrictlyInsideHexagon h y
  hvgColour : colour v ≠ colour g
  hvbColour : colour v ≠ colour b
  hgbColour : colour g ≠ colour b
  hredGColour : colour p ≠ colour g
  hredBColour : colour p ≠ colour b
  insideCover : ∀ z : hexBlockers P h, StrictlyInsideHexagon h z →
    z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b

/-- Finish the red-two structure once the red point on the blue base and the
two remaining blue-side blockers have been identified. -/
private theorem finish_eleven_red_two_structure
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    {p q v x y g b : hexBlockers P h}
    (hpos : 0 < turn (v : Point) (x : Point) (y : Point))
    (hpq : p ≠ q) (hvx : v ≠ x) (hxy : x ≠ y) (hyv : y ≠ v)
    (hpI : StrictlyInsideHexagon h p) (hqI : StrictlyInsideHexagon h q)
    (hcq : colour q = colour p)
    (hredCard : (colourFiber colour (colour p)).card = 2)
    (hblueX : colour v = colour x) (hblueY : colour x = colour y)
    (hredBlue : colour p ≠ colour v)
    (hpv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hpbase : (p : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hg : (g : Point) ∈ openSegment ℝ (v : Point) (y : Point))
    (hb : (b : Point) ∈ openSegment ℝ (v : Point) (x : Point))
    (hxBoundary : ¬StrictlyInsideHexagon h x)
    (hyBoundary : ¬StrictlyInsideHexagon h y)
    (hvgColour : colour v ≠ colour g)
    (hvbColour : colour v ≠ colour b)
    (hqOut : (q : Point) ∉ triangleHull (v : Point) (x : Point) (y : Point)) :
    Nonempty (ElevenRedTwoStructure colour) := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hIcard : I.card = 5 := by
    simpa [I, B, hcard] using strictInteriorBlockers_card hfour hh hhP hside
  have hvI : StrictlyInsideHexagon h v :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      p.property q.property (Subtype.val_injective.ne hpq) hpv
  have hgI : StrictlyInsideHexagon h g :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      v.property y.property (Subtype.val_injective.ne hyv.symm) hg
  have hbI : StrictlyInsideHexagon h b :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      v.property x.property (Subtype.val_injective.ne hvx) hb
  have hsides := triangle_side_points_pairwise hpos hb hpbase
    (by simpa only [openSegment_symm] using hg)
  have hbp : b ≠ p := fun e ↦ hsides.1 (congrArg Subtype.val e)
  have hpg : p ≠ g := fun e ↦ hsides.2.1 (congrArg Subtype.val e)
  have hgb : g ≠ b := fun e ↦ hsides.2.2 (congrArg Subtype.val e)
  have hvp : v ≠ p := by
    intro e
    exact hredBlue (congrArg colour e |>.symm)
  have hvq : v ≠ q := by
    intro e
    exact hredBlue ((congrArg colour e).trans hcq).symm
  have hvg : v ≠ g := fun e ↦ hvgColour (congrArg colour e)
  have hvb : v ≠ b := fun e ↦ hvbColour (congrArg colour e)
  have hvHull : (v : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) :=
    vertex_mem_triangleHull _ _ _
  have hxHull : (x : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) := by
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hyHull : (y : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) := by
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hgHull := openSegment_mem_triangleHull_of_mem hvHull hyHull hg
  have hbHull := openSegment_mem_triangleHull_of_mem hvHull hxHull hb
  have hqg : q ≠ g := by intro e; subst q; exact hqOut hgHull
  have hqb : q ≠ b := by intro e; subst q; exact hqOut hbHull
  let K : Finset B := {p, q, v, g, b}
  let e : B ↪ Point := ⟨fun z ↦ (z : Point), Subtype.val_injective⟩
  let J : Finset Point := K.map e
  have hKcard : K.card = 5 := by
    simp [K, hpq, hvp.symm, hpg, hbp.symm, hvq.symm, hqg, hqb,
      hvg, hvb, hgb]
  have hJcard : J.card = 5 := by
    change (K.map e).card = 5
    simpa using hKcard
  have hJsub : J ⊆ I := by
    intro z hz
    change z ∈ K.map e at hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hwK, rfl⟩ := hz
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hwK
    rcases hwK with h | h | h | h | h
    · subst w; exact Finset.mem_filter.mpr ⟨p.property, hpI⟩
    · subst w; exact Finset.mem_filter.mpr ⟨q.property, hqI⟩
    · subst w; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
    · subst w; exact Finset.mem_filter.mpr ⟨g.property, hgI⟩
    · subst w; exact Finset.mem_filter.mpr ⟨b.property, hbI⟩
  have hJI : J = I :=
    Finset.eq_of_subset_of_card_le hJsub (by rw [hIcard, hJcard])
  have hIcover : ∀ z : B, StrictlyInsideHexagon h z →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b := by
    intro z hz
    have hzI : (z : Point) ∈ I := Finset.mem_filter.mpr ⟨z.property, hz⟩
    rw [← hJI] at hzI
    change (z : Point) ∈ K.map e at hzI
    rw [Finset.mem_map] at hzI
    obtain ⟨w, hwK, hwz⟩ := hzI
    have hwzB : w = z := Subtype.ext hwz
    subst w
    simpa only [K, Finset.mem_insert, Finset.mem_singleton] using hwK
  have hmono : MonoTriple colour v x y := ⟨hvx, hxy, hyv, hblueX, hblueY⟩
  have hcolourCover : ∀ d : Fin 4, d ≠ colour v →
      d = colour p ∨ d = colour g ∨ d = colour b := by
    intro d hdBlue
    by_cases hdRed : d = colour p
    · exact Or.inl hdRed
    obtain ⟨z, hzHull, hcz⟩ :=
      exists_colour_in_triangleHull hfourB hproper hmono d hdBlue
    have hzv : z ≠ v := by intro e; subst z; exact hdBlue hcz.symm
    have hzx : z ≠ x := by
      intro e
      subst z
      exact hdBlue (hcz.symm.trans hblueX.symm)
    have hzy : z ≠ y := by
      intro e
      subst z
      exact hdBlue (hcz.symm.trans (hblueY.symm.trans hblueX.symm))
    have hzI := triangleHull_nonvertex_strictlyInsideHexagon
      hfour hh hhP hside hzHull hzv hzx hzy
    rcases hIcover z hzI with rfl | rfl | rfl | rfl | rfl
    · exact (hdRed hcz.symm).elim
    · exact (hdRed (hcz.symm.trans hcq)).elim
    · exact (hdBlue hcz.symm).elim
    · exact Or.inr (Or.inl hcz.symm)
    · exact Or.inr (Or.inr hcz.symm)
  have hcols := pairwise_ne_of_fin4_nonred_cover hredBlue
    hvgColour.symm hvbColour.symm hcolourCover
  exact ⟨
    { p := p, q := q, v := v, x := x, y := y, g := g, b := b
      hpq := hpq, hvx := hvx, hxy := hxy, hyv := hyv
      hred := hcq.symm, hredCard := hredCard,
      hblueX := hblueX, hblueY := hblueY
      hredBlue := hredBlue, htriangle := hpos, hpv := hpv, hpbase := hpbase,
      hg := hg, hb := hb
      hxBoundary := hxBoundary, hyBoundary := hyBoundary
      hvgColour := hvgColour, hvbColour := hvbColour
      hgbColour := hcols.2.2, hredGColour := hcols.1,
      hredBColour := hcols.2.1, insideCover := hIcover }⟩

/-- Construct the rigid red-two configuration after orienting the blue
triangle. -/
private theorem build_eleven_red_two_oriented
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    {p q v x y : hexBlockers P h}
    (hpq : p ≠ q) (hvx : v ≠ x) (hxy : x ≠ y) (hyv : y ≠ v)
    (hpI : StrictlyInsideHexagon h p)
    (hqI : StrictlyInsideHexagon h q)
    (hcq : colour q = colour p)
    (hredCard : (colourFiber colour (colour p)).card = 2)
    (hblueX : colour v = colour x) (hblueY : colour x = colour y)
    (hredBlue : colour p ≠ colour v)
    (hpv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hpos : 0 < turn (v : Point) (x : Point) (y : Point)) :
    Nonempty (ElevenRedTwoStructure colour) := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hIcard : I.card = 5 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  obtain ⟨s₀, hs₀⟩ := hproper v x hvx hblueX
  obtain ⟨s₁, hs₁⟩ := hproper x y hxy hblueY
  obtain ⟨s₂, hs₂⟩ := hproper y v hyv (hblueY.symm.trans hblueX.symm)
  have hs₀I : StrictlyInsideHexagon h s₀ :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      v.property x.property (Subtype.val_injective.ne hvx) hs₀
  have hs₁I : StrictlyInsideHexagon h s₁ :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      x.property y.property (Subtype.val_injective.ne hxy) hs₁
  have hs₂I : StrictlyInsideHexagon h s₂ :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      y.property v.property (Subtype.val_injective.ne hyv) hs₂
  have hvI : StrictlyInsideHexagon h v :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      p.property q.property (Subtype.val_injective.ne hpq) hpv
  have hs₀Blue : colour s₀ ≠ colour v :=
    blocker_colour_ne hfourB hproper hvx hblueX hs₀
  have hs₁Blue : colour s₁ ≠ colour v := by
    have h := blocker_colour_ne hfourB hproper hxy hblueY hs₁
    exact h.trans_eq hblueX.symm
  have hs₂Blue : colour s₂ ≠ colour v :=
    (blocker_colour_ne (x := y) (y := v) (z := s₂) hfourB hproper hyv
      (hblueY.symm.trans hblueX.symm) hs₂).trans_eq
        (hblueX.trans hblueY).symm
  have hneColour {a b : B} (hc : colour a ≠ colour b) : a ≠ b := by
    intro e
    exact hc (congrArg colour e)
  have hs₀v : s₀ ≠ v := hneColour hs₀Blue
  have hs₀x : s₀ ≠ x := hneColour (hs₀Blue.trans_eq hblueX)
  have hs₀y : s₀ ≠ y := hneColour
    (hs₀Blue.trans_eq (hblueX.trans hblueY))
  have hs₁v : s₁ ≠ v := hneColour hs₁Blue
  have hs₁x : s₁ ≠ x := hneColour (hs₁Blue.trans_eq hblueX)
  have hs₁y : s₁ ≠ y := hneColour
    (hs₁Blue.trans_eq (hblueX.trans hblueY))
  have hs₂v : s₂ ≠ v := hneColour hs₂Blue
  have hs₂x : s₂ ≠ x := hneColour (hs₂Blue.trans_eq hblueX)
  have hs₂y : s₂ ≠ y := hneColour
    (hs₂Blue.trans_eq (hblueX.trans hblueY))
  have hsides := triangle_side_points_pairwise hpos hs₀ hs₁ hs₂
  have hs₀s₁ : s₀ ≠ s₁ := by
    exact fun e ↦ hsides.1 (congrArg Subtype.val e)
  have hs₁s₂ : s₁ ≠ s₂ := by
    exact fun e ↦ hsides.2.1 (congrArg Subtype.val e)
  have hs₂s₀ : s₂ ≠ s₀ := by
    exact fun e ↦ hsides.2.2 (congrArg Subtype.val e)
  have hvHull : (v : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) :=
    vertex_mem_triangleHull _ _ _
  have hxHull : (x : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) := by
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hyHull : (y : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) := by
    exact subset_convexHull ℝ _ (by simp [triangleHull])
  have hs₀Hull := openSegment_mem_triangleHull_of_mem hvHull hxHull hs₀
  have hs₁Hull := openSegment_mem_triangleHull_of_mem hxHull hyHull hs₁
  have hs₂Hull := openSegment_mem_triangleHull_of_mem hyHull hvHull hs₂
  have hpvNe : p ≠ v := hneColour hredBlue
  have hpx : p ≠ x := hneColour (hredBlue.trans_eq hblueX)
  have hpy : p ≠ y := hneColour
    (hredBlue.trans_eq (hblueX.trans hblueY))
  have hqv : q ≠ v := hneColour (hcq.trans_ne hredBlue)
  have hqx : q ≠ x := hneColour (hcq.trans_ne (hredBlue.trans_eq hblueX))
  have hqy : q ≠ y := hneColour
    (hcq.trans_ne (hredBlue.trans_eq (hblueX.trans hblueY)))
  have hnotBoth : ¬((p : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point) ∧
      (q : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point)) := by
    rintro ⟨hpHull, hqHull⟩
    exact triangle_vertex_not_between_hull_points hfourB hpos hpHull hqHull hpv
      hpvNe hpx hpy
  obtain ⟨w, hwI, hwOut⟩ : ∃ w : B, StrictlyInsideHexagon h w ∧
      (w : Point) ∉ triangleHull (v : Point) (x : Point) (y : Point) := by
    by_cases hpHull : (p : Point) ∈ triangleHull (v : Point) (x : Point) (y : Point)
    · exact ⟨q, hqI, fun hqHull ↦ hnotBoth ⟨hpHull, hqHull⟩⟩
    · exact ⟨p, hpI, hpHull⟩
  have hwv : w ≠ v := by intro e; subst w; exact hwOut hvHull
  have hwx : w ≠ x := by intro e; subst w; exact hwOut hxHull
  have hwy : w ≠ y := by intro e; subst w; exact hwOut hyHull
  have hws₀ : w ≠ s₀ := by intro e; subst w; exact hwOut hs₀Hull
  have hws₁ : w ≠ s₁ := by intro e; subst w; exact hwOut hs₁Hull
  have hws₂ : w ≠ s₂ := by intro e; subst w; exact hwOut hs₂Hull
  have hxBoundary : ¬StrictlyInsideHexagon h x := by
    intro hxI
    let K : Finset B := {v, x, s₀, s₁, s₂, w}
    have hKcard : K.card = 6 := by
      simp [K, hvx, hs₀v.symm, hs₁v.symm, hs₂v.symm, hwv.symm,
        hs₀x.symm, hs₁x.symm, hs₂x.symm, hwx.symm,
        hs₀s₁, hs₂s₀.symm, hws₀.symm, hs₁s₂,
        hws₁.symm, hws₂.symm]
    have hKsub : ∀ z : B, z ∈ K → (z : Point) ∈ I := by
      intro z hz
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h | h
      · subst z; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
      · subst z; exact Finset.mem_filter.mpr ⟨x.property, hxI⟩
      · subst z; exact Finset.mem_filter.mpr ⟨s₀.property, hs₀I⟩
      · subst z; exact Finset.mem_filter.mpr ⟨s₁.property, hs₁I⟩
      · subst z; exact Finset.mem_filter.mpr ⟨s₂.property, hs₂I⟩
      · subst z; exact Finset.mem_filter.mpr ⟨w.property, hwI⟩
    have hleKI := card_le_of_val_mem hKsub
    rw [hKcard, hIcard] at hleKI
    omega
  have hyBoundary : ¬StrictlyInsideHexagon h y := by
    intro hyI
    let K : Finset B := {v, y, s₀, s₁, s₂, w}
    have hKcard : K.card = 6 := by
      simp [K, hyv.symm, hs₀v.symm, hs₁v.symm, hs₂v.symm, hwv.symm,
        hs₀y.symm, hs₁y.symm, hs₂y.symm, hwy.symm,
        hs₀s₁, hs₂s₀.symm, hws₀.symm, hs₁s₂,
        hws₁.symm, hws₂.symm]
    have hKsub : ∀ z : B, z ∈ K → (z : Point) ∈ I := by
      intro z hz
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h | h | h | h | h
      · subst z; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
      · subst z; exact Finset.mem_filter.mpr ⟨y.property, hyI⟩
      · subst z; exact Finset.mem_filter.mpr ⟨s₀.property, hs₀I⟩
      · subst z; exact Finset.mem_filter.mpr ⟨s₁.property, hs₁I⟩
      · subst z; exact Finset.mem_filter.mpr ⟨s₂.property, hs₂I⟩
      · subst z; exact Finset.mem_filter.mpr ⟨w.property, hwI⟩
    have hleKI := card_le_of_val_mem hKsub
    rw [hKcard, hIcard] at hleKI
    omega
  have hmonoBlue : MonoTriple colour v x y :=
    ⟨hvx, hxy, hyv, hblueX, hblueY⟩
  obtain ⟨z, hzHull, hcz⟩ :=
    exists_colour_in_triangleHull hfourB hproper hmonoBlue (colour p) hredBlue
  have hzRed : z = p ∨ z = q :=
    eq_first_or_second_of_colourFiber_card_two hredCard rfl hcq hpq hcz
  have hzI : StrictlyInsideHexagon h z := by
    rcases hzRed with rfl | rfl
    · exact hpI
    · exact hqI
  have hzNotStrict : ¬StrictlyInsideTriangle (v : Point) (x : Point) (y : Point) z := by
    intro hzStrict
    have hzs₀ : z ≠ s₀ := by
      intro e
      have hz0 := turn_eq_zero_of_between hs₀
      rw [← e] at hz0
      linarith [hzStrict.1]
    have hzs₁ : z ≠ s₁ := by
      intro e
      have hz0 := turn_eq_zero_of_between hs₁
      rw [← e] at hz0
      linarith [hzStrict.2.1]
    have hzs₂ : z ≠ s₂ := by
      intro e
      have hz0 := turn_eq_zero_of_between hs₂
      rw [← e] at hz0
      linarith [hzStrict.2.2]
    obtain ⟨w', hw'I, hw'Out⟩ : ∃ w' : B, StrictlyInsideHexagon h w' ∧
        (w' : Point) ∉ triangleHull (v : Point) (x : Point) (y : Point) := by
      rcases hzRed with rfl | rfl
      · exact ⟨q, hqI, fun hqHull ↦ hnotBoth ⟨hzHull, hqHull⟩⟩
      · exact ⟨p, hpI, fun hpHull ↦ hnotBoth ⟨hpHull, hzHull⟩⟩
    have hw'v : w' ≠ v := by intro e; subst w'; exact hw'Out hvHull
    have hw's₀ : w' ≠ s₀ := by intro e; subst w'; exact hw'Out hs₀Hull
    have hw's₁ : w' ≠ s₁ := by intro e; subst w'; exact hw'Out hs₁Hull
    have hw's₂ : w' ≠ s₂ := by intro e; subst w'; exact hw'Out hs₂Hull
    have hw'z : w' ≠ z := by intro e; subst w'; exact hw'Out hzHull
    have hzv' : z ≠ v := hneColour (hcz.trans_ne hredBlue)
    let K : Finset B := {v, s₀, s₁, s₂, z, w'}
    have hKcard : K.card = 6 := by
      simp [K, hs₀v.symm, hs₁v.symm, hs₂v.symm, hzv'.symm,
        hw'v.symm, hs₀s₁, hs₂s₀.symm, hzs₀.symm,
        hw's₀.symm, hs₁s₂, hzs₁.symm, hw's₁.symm,
        hzs₂.symm, hw's₂.symm, hw'z.symm]
    have hKsub : ∀ u : B, u ∈ K → (u : Point) ∈ I := by
      intro u hu
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h | h | h | h
      · subst u; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
      · subst u; exact Finset.mem_filter.mpr ⟨s₀.property, hs₀I⟩
      · subst u; exact Finset.mem_filter.mpr ⟨s₁.property, hs₁I⟩
      · subst u; exact Finset.mem_filter.mpr ⟨s₂.property, hs₂I⟩
      · subst u; exact Finset.mem_filter.mpr ⟨z.property, hzI⟩
      · subst u; exact Finset.mem_filter.mpr ⟨w'.property, hw'I⟩
    have hleKI := card_le_of_val_mem hKsub
    rw [hKcard, hIcard] at hleKI
    omega
  have hzv : z ≠ v := hneColour (hcz.trans_ne hredBlue)
  have hzx : z ≠ x := hneColour (hcz.trans_ne (hredBlue.trans_eq hblueX))
  have hzy : z ≠ y := hneColour
    (hcz.trans_ne (hredBlue.trans_eq (hblueX.trans hblueY)))
  have hzSide := mem_openSide_of_mem_triangleHull_not_strict hpos hzHull
    (Subtype.val_injective.ne hzv) (Subtype.val_injective.ne hzx)
    (Subtype.val_injective.ne hzy) hzNotStrict
  rcases hzRed with hzP | hzQ
  · subst z
    have hpBase : (p : Point) ∈ openSegment ℝ (x : Point) (y : Point) := by
      rcases hzSide with hpvx | hpxy | hpyv
      · exact (saturated_left_endpoint_not_between hfourB hpq hpv hpvx).elim
      · exact hpxy
      · exact (saturated_left_endpoint_not_between hfourB hpq hpv
          (by simpa only [openSegment_symm] using hpyv)).elim
    have hs₁p : s₁ = p := openSegment_point_unique hfourB hxy hs₁ hpBase
    subst s₁
    have hqOut : (q : Point) ∉ triangleHull (v : Point) (x : Point) (y : Point) :=
      fun hqHull ↦ hnotBoth ⟨hzHull, hqHull⟩
    exact finish_eleven_red_two_structure hfour hh hhP hside hcard colour
      hproper hpos hpq hvx hxy hyv hpI hqI hcq hredCard
      hblueX hblueY hredBlue hpv hpBase
      (by simpa only [openSegment_symm] using hs₂) hs₀
      hxBoundary hyBoundary hs₂Blue.symm hs₀Blue.symm hqOut
  · subst z
    have hqBase : (q : Point) ∈ openSegment ℝ (x : Point) (y : Point) := by
      rcases hzSide with hqvx | hqxy | hqyv
      · exact (saturated_right_endpoint_not_between hfourB hpq hpv hqvx).elim
      · exact hqxy
      · exact (saturated_right_endpoint_not_between hfourB hpq hpv
          (by simpa only [openSegment_symm] using hqyv)).elim
    have hs₁q : s₁ = q := openSegment_point_unique hfourB hxy hs₁ hqBase
    subst s₁
    have hpOut : (p : Point) ∉ triangleHull (v : Point) (x : Point) (y : Point) :=
      fun hpHull ↦ hnotBoth ⟨hpHull, hzHull⟩
    exact finish_eleven_red_two_structure hfour hh hhP hside hcard colour
      hproper hpos hpq.symm hvx hxy hyv hqI hpI hcq.symm
      (by simpa [hcq] using hredCard) hblueX hblueY
      (hcq.trans_ne hredBlue) (by simpa only [openSegment_symm] using hpv)
      hqBase (by simpa only [openSegment_symm] using hs₂) hs₀
      hxBoundary hyBoundary hs₂Blue.symm hs₀Blue.symm hpOut

/-- Obtain the oriented red-two configuration from any same-coloured pair of
strict-interior points whose colour class has size two. -/
private theorem build_eleven_red_two
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {p q : hexBlockers P h} (hpq : p ≠ q)
    (hpI : StrictlyInsideHexagon h p) (hqI : StrictlyInsideHexagon h q)
    (hcq : colour q = colour p)
    (hredCard : (colourFiber colour (colour p)).card = 2) :
    Nonempty (ElevenRedTwoStructure colour) := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  obtain ⟨v, hv⟩ := hproper p q hpq hcq.symm
  have hredBlue : colour p ≠ colour v :=
    (blocker_colour_ne hfourB hproper hpq hcq.symm hv).symm
  have hblueCard : (colourFiber colour (colour v)).card = 3 :=
    other_colourFiber_card_three_of_eleven colour (by simpa [B, hcard]) hle
      hredCard hredBlue.symm
  obtain ⟨x, y, hxy, hxv, hyv, hcx, hcy⟩ :=
    exists_two_others_of_colourFiber_card_three hblueCard rfl
  have hturn : turn (v : Point) (x : Point) (y : Point) ≠ 0 :=
    turn_ne_zero_of_same_colour hfourB hproper hxv.symm hxy hyv
      hcx.symm (hcx.trans hcy.symm)
  by_cases hpos : 0 < turn (v : Point) (x : Point) (y : Point)
  · exact build_eleven_red_two_oriented hfour hh hhP hside hcard colour hproper
      hpq hxv.symm hxy hyv hpI hqI hcq hredCard hcx.symm
      (hcx.trans hcy.symm) hredBlue hv hpos
  · have hneg : turn (v : Point) (x : Point) (y : Point) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hturn
    have hpos' : 0 < turn (v : Point) (y : Point) (x : Point) := by
      rw [turn_swap_last]
      linarith
    exact build_eleven_red_two_oriented hfour hh hhP hside hcard colour hproper
      hpq hyv.symm hxy.symm hxv hpI hqI hcq hredCard hcy.symm
      (hcy.trans hcx.symm) hredBlue hv hpos'

/-- If `v` lies strictly between `p` and `q`, replacing the second point of
the oriented line `pv` by `q` preserves every strict side sign. -/
private theorem turn_relation_of_between
    {p q v z : Point} (hv : v ∈ openSegment ℝ p q) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ turn p v z = t * turn p q z := by
  obtain ⟨t, ht0, ht1, heq⟩ :=
    turn_of_mem_openSegment (a := p) (b := z) hv
  simp only [turn_self_left, mul_zero, zero_add] at heq
  refine ⟨t, ht0, ht1, ?_⟩
  rw [turn_swap_last p z v, turn_swap_last p z q, heq]
  ring

/-- All half-plane signs used in the red-two branch, extracted from its
rigid blue triangle. -/
private theorem eleven_red_two_signs
    {P : Finset Point} {h : Fin 6 → Point}
    {colour : hexBlockers P h → Fin 4}
    (C : ElevenRedTwoStructure colour) :
    turn (C.p : Point) (C.q : Point) C.p = 0 ∧
    turn (C.p : Point) (C.q : Point) C.q = 0 ∧
    turn (C.p : Point) (C.q : Point) C.v = 0 ∧
    0 < turn (C.p : Point) (C.q : Point) C.b ∧
    turn (C.p : Point) (C.q : Point) C.g < 0 ∧
    turn (C.x : Point) (C.y : Point) C.p = 0 ∧
    0 < turn (C.x : Point) (C.y : Point) C.v ∧
    0 < turn (C.x : Point) (C.y : Point) C.q ∧
    0 < turn (C.x : Point) (C.y : Point) C.g ∧
    0 < turn (C.x : Point) (C.y : Point) C.b := by
  have hvxp : 0 < turn (C.v : Point) (C.x : Point) C.p :=
    turn_pos_of_mem_next_side C.htriangle C.hpbase
  have hpvx : 0 < turn (C.p : Point) (C.v : Point) C.x := by
    simpa only [turn_rotate, turn_rotate] using hvxp
  have hpvb : 0 < turn (C.p : Point) (C.v : Point) C.b :=
    edgeTurn_pos_of_mem_openSegment C.hb (by simp) hpvx.le (Or.inr hpvx)
  have hvyp : turn (C.v : Point) (C.y : Point) C.p < 0 := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (C.v : Point)) (b := (C.y : Point)) C.hpbase
    have hvxyNeg : turn (C.v : Point) (C.y : Point) C.x < 0 := by
      rw [turn_swap_last]
      linarith [C.htriangle]
    simp only [turn_self_right, mul_zero, add_zero] at heq
    rw [heq]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hvxyNeg
  have hpvy : turn (C.p : Point) (C.v : Point) C.y < 0 := by
    simpa only [turn_rotate] using hvyp
  have hpvg : turn (C.p : Point) (C.v : Point) C.g < 0 := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (C.p : Point)) (b := (C.v : Point)) C.hg
    simp only [turn_self_right, mul_zero, zero_add] at heq
    rw [heq]
    exact mul_neg_of_pos_of_neg ht0 hpvy
  obtain ⟨tb, htb0, -, hbrel⟩ := turn_relation_of_between (z := (C.b : Point)) C.hpv
  obtain ⟨tg, htg0, -, hgrel⟩ := turn_relation_of_between (z := (C.g : Point)) C.hpv
  have hpqb : 0 < turn (C.p : Point) (C.q : Point) C.b := by
    nlinarith [hpvb]
  have hpqg : turn (C.p : Point) (C.q : Point) C.g < 0 := by
    nlinarith [hpvg]
  have hxyv : 0 < turn (C.x : Point) (C.y : Point) C.v := by
    simpa only [turn_rotate] using C.htriangle
  have hxyp : turn (C.x : Point) (C.y : Point) C.p = 0 :=
    turn_eq_zero_of_between C.hpbase
  have hxyq : 0 < turn (C.x : Point) (C.y : Point) C.q := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (C.x : Point)) (b := (C.y : Point)) C.hpv
    rw [hxyp] at heq
    nlinarith
  have hxyg : 0 < turn (C.x : Point) (C.y : Point) C.g :=
    edgeTurn_pos_of_mem_openSegment C.hg hxyv.le (by simp) (Or.inl hxyv)
  have hxyb : 0 < turn (C.x : Point) (C.y : Point) C.b :=
    edgeTurn_pos_of_mem_openSegment C.hb hxyv.le (by simp) (Or.inl hxyv)
  have hpqv : turn (C.p : Point) (C.q : Point) C.v = 0 :=
    turn_eq_zero_of_between C.hpv
  exact ⟨by simp, by simp, hpqv, hpqb, hpqg, hxyp, hxyv, hxyq, hxyg, hxyb⟩

private structure ElevenGreenWing
    {P : Finset Point} {h : Fin 6 → Point}
    {colour : hexBlockers P h → Fin 4}
    (C : ElevenRedTwoStructure colour) where
  u : hexBlockers P h
  w : hexBlockers P h
  huw : u ≠ w
  hug : u ≠ C.g
  hwg : w ≠ C.g
  hcu : colour u = colour C.g
  hcw : colour w = colour C.g
  huBoundary : ¬StrictlyInsideHexagon h u
  hwBoundary : ¬StrictlyInsideHexagon h w
  huPos : 0 < turn (C.p : Point) (C.q : Point) u
  hwPos : 0 < turn (C.p : Point) (C.q : Point) w
  hbase : (C.b : Point) ∈ openSegment ℝ (u : Point) (w : Point)
  incident :
    ((C.p : Point) ∈ openSegment ℝ (C.g : Point) (u : Point) ∧
      (C.q : Point) ∈ openSegment ℝ (C.g : Point) (w : Point)) ∨
    ((C.q : Point) ∈ openSegment ℝ (C.g : Point) (u : Point) ∧
      (C.p : Point) ∈ openSegment ℝ (C.g : Point) (w : Point))

/-- The green triangle forced by a red-two configuration. -/
private theorem build_eleven_green_wing
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    (C : ElevenRedTwoStructure colour)
    (hredCard : (colourFiber colour (colour C.p)).card = 2) :
    Nonempty (ElevenGreenWing C) := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hgreenCard : (colourFiber colour (colour C.g)).card = 3 :=
    other_colourFiber_card_three_of_eleven colour (by simpa [B, hcard]) hle
      hredCard C.hredGColour.symm
  obtain ⟨u, w, huw, hug, hwg, hcu, hcw⟩ :=
    exists_two_others_of_colourFiber_card_three hgreenCard rfl
  have hneColour {a b : B} (hc : colour a ≠ colour b) : a ≠ b := by
    intro e
    exact hc (congrArg colour e)
  have huBoundary : ¬StrictlyInsideHexagon h u := by
    intro huI
    rcases C.insideCover u huI with rfl | rfl | rfl | rfl | rfl
    · exact C.hredGColour hcu
    · exact C.hredGColour (C.hred.trans hcu)
    · exact C.hvgColour hcu
    · exact hug rfl
    · exact C.hgbColour (hcu.symm)
  have hwBoundary : ¬StrictlyInsideHexagon h w := by
    intro hwI
    rcases C.insideCover w hwI with rfl | rfl | rfl | rfl | rfl
    · exact C.hredGColour hcw
    · exact C.hredGColour (C.hred.trans hcw)
    · exact C.hvgColour hcw
    · exact hwg rfl
    · exact C.hgbColour (hcw.symm)
  rcases eleven_red_two_signs C with
    ⟨hpp, hpqq, hpqv, hpqb, hpqg, hxyp, hxyv, hxyq, hxyg, hxyb⟩
  have hzeroImpossible : ∀ z : B, colour z = colour C.g →
      turn (C.p : Point) (C.q : Point) z ≠ 0 := by
    intro z hcz hz0
    have hpvNe : C.p ≠ C.v := hneColour C.hredBlue
    have hqP : C.q ≠ C.p := C.hpq.symm
    have hqV : C.q ≠ C.v := hneColour (C.hred.symm.trans_ne C.hredBlue)
    have hzP : z ≠ C.p := hneColour (hcz.trans_ne C.hredGColour.symm)
    have hzV : z ≠ C.v := hneColour (hcz.trans_ne C.hvgColour.symm)
    obtain ⟨t, -, -, hrel⟩ := turn_relation_of_between (z := (z : Point)) C.hpv
    rw [hz0, mul_zero] at hrel
    have hzLine : (z : Point) ∈ affineSpan ℝ {(C.p : Point), (C.v : Point)} :=
      mem_line_of_turn_eq_zero (Subtype.val_injective.ne hpvNe) hrel
    have hqLine : (C.q : Point) ∈ affineSpan ℝ {(C.p : Point), (C.v : Point)} :=
      right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne C.hpq) C.hpv
    have heq := extra_points_eq_on_saturated_line hfourB hpvNe
      hqP hqV hzP hzV hqLine hzLine
    exact C.hredGColour (C.hred.trans ((congrArg colour heq).trans hcz))
  have hpositive : ∀ z : B, z ≠ C.g → colour z = colour C.g →
      0 < turn (C.p : Point) (C.q : Point) z := by
    intro z hzg hcz
    have hz0 := hzeroImpossible z hcz
    by_contra hn
    have hzneg : turn (C.p : Point) (C.q : Point) z < 0 :=
      lt_of_le_of_ne (le_of_not_gt hn) hz0
    obtain ⟨a, ha⟩ := hproper C.g z hzg.symm hcz.symm
    have haneg := turn_neg_of_mem_openSegment ha hpqg hzneg
    rcases C.insideCover a
      (openSegment_between_blockers_strictlyInside hfour hh hhP hside
        C.g.property z.property (Subtype.val_injective.ne hzg.symm) ha) with
      rfl | rfl | rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
    · have : (C.g : Point) ≠ (z : Point) := Subtype.val_injective.ne hzg.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp ha)).elim
    · linarith
  have huPos := hpositive u hug hcu
  have hwPos := hpositive w hwg hcw
  obtain ⟨a, ha⟩ := hproper u w huw (hcu.trans hcw.symm)
  have haPos := edgeTurn_pos_of_mem_openSegment ha huPos.le hwPos.le (Or.inl huPos)
  have hbase : (C.b : Point) ∈ openSegment ℝ (u : Point) (w : Point) := by
    rcases C.insideCover a
      (openSegment_between_blockers_strictlyInside hfour hh hhP hside
        u.property w.property (Subtype.val_injective.ne huw) ha) with
      rfl | rfl | rfl | rfl | h
    · linarith
    · linarith
    · linarith
    · linarith
    · simpa [h] using ha
  have hclassify : ∀ z : B, (z = u ∨ z = w) →
      z ≠ C.g → colour z = colour C.g →
      ((C.p : Point) ∈ openSegment ℝ (C.g : Point) (z : Point)) ∨
      ((C.q : Point) ∈ openSegment ℝ (C.g : Point) (z : Point)) := by
    intro z huzw hzg hcz
    obtain ⟨a, ha⟩ := hproper C.g z hzg.symm hcz.symm
    rcases C.insideCover a
      (openSegment_between_blockers_strictlyInside hfour hh hhP hside
        C.g.property z.property (Subtype.val_injective.ne hzg.symm) ha) with
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
    · exact (saturated_left_endpoint_not_between hfourB C.hyv.symm C.hg ha).elim
    · have : (C.g : Point) ≠ (z : Point) := Subtype.val_injective.ne hzg.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp ha)).elim
    · rcases huzw with hzu | hzw
      · subst z
        have heq := other_endpoint_eq_of_common_blocker
          (a := u) (b := w) (c := C.g) (z := C.b)
          hfourB huw hug hbase (by simpa only [openSegment_symm] using ha)
        exact (hwg heq).elim
      · subst z
        have heq := other_endpoint_eq_of_common_blocker
          (a := w) (b := u) (c := C.g) (z := C.b)
          hfourB huw.symm hwg (by simpa only [openSegment_symm] using hbase)
          (by simpa only [openSegment_symm] using ha)
        exact (hug heq).elim
  have huClass := hclassify u (Or.inl rfl) hug hcu
  have hwClass := hclassify w (Or.inr rfl) hwg hcw
  have hincident :
      (((C.p : Point) ∈ openSegment ℝ (C.g : Point) (u : Point)) ∧
        ((C.q : Point) ∈ openSegment ℝ (C.g : Point) (w : Point))) ∨
      (((C.q : Point) ∈ openSegment ℝ (C.g : Point) (u : Point)) ∧
        ((C.p : Point) ∈ openSegment ℝ (C.g : Point) (w : Point))) := by
    rcases huClass with hpu | hqu <;> rcases hwClass with hpw | hqw
    · have heq := other_endpoint_eq_of_common_blocker hfourB hug.symm hwg.symm hpu hpw
      exact (huw heq).elim
    · exact Or.inl ⟨hpu, hqw⟩
    · exact Or.inr ⟨hqu, hpw⟩
    · have heq := other_endpoint_eq_of_common_blocker hfourB hug.symm hwg.symm hqu hqw
      exact (huw heq).elim
  exact ⟨
    { u := u, w := w, huw := huw, hug := hug, hwg := hwg,
      hcu := hcu, hcw := hcw, huBoundary := huBoundary,
      hwBoundary := hwBoundary, huPos := huPos, hwPos := hwPos,
      hbase := hbase, incident := hincident }⟩

private structure ElevenBlackWing
    {P : Finset Point} {h : Fin 6 → Point}
    {colour : hexBlockers P h → Fin 4}
    (C : ElevenRedTwoStructure colour) where
  u : hexBlockers P h
  w : hexBlockers P h
  huw : u ≠ w
  hub : u ≠ C.b
  hwb : w ≠ C.b
  hcu : colour u = colour C.b
  hcw : colour w = colour C.b
  huBoundary : ¬StrictlyInsideHexagon h u
  hwBoundary : ¬StrictlyInsideHexagon h w
  huNeg : turn (C.p : Point) (C.q : Point) u < 0
  hwNeg : turn (C.p : Point) (C.q : Point) w < 0
  hbase : (C.g : Point) ∈ openSegment ℝ (u : Point) (w : Point)
  incident :
    ((C.p : Point) ∈ openSegment ℝ (C.b : Point) (u : Point) ∧
      (C.q : Point) ∈ openSegment ℝ (C.b : Point) (w : Point)) ∨
    ((C.q : Point) ∈ openSegment ℝ (C.b : Point) (u : Point) ∧
      (C.p : Point) ∈ openSegment ℝ (C.b : Point) (w : Point))

/-- The black triangle, symmetric to `build_eleven_green_wing`. -/
private theorem build_eleven_black_wing
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    (C : ElevenRedTwoStructure colour)
    (hredCard : (colourFiber colour (colour C.p)).card = 2) :
    Nonempty (ElevenBlackWing C) := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hblackCard : (colourFiber colour (colour C.b)).card = 3 :=
    other_colourFiber_card_three_of_eleven colour (by simpa [B, hcard]) hle
      hredCard C.hredBColour.symm
  obtain ⟨u, w, huw, hub, hwb, hcu, hcw⟩ :=
    exists_two_others_of_colourFiber_card_three hblackCard rfl
  have hneColour {a b : B} (hc : colour a ≠ colour b) : a ≠ b := by
    intro e
    exact hc (congrArg colour e)
  have huBoundary : ¬StrictlyInsideHexagon h u := by
    intro huI
    rcases C.insideCover u huI with rfl | rfl | rfl | rfl | rfl
    · exact C.hredBColour hcu
    · exact C.hredBColour (C.hred.trans hcu)
    · exact C.hvbColour hcu
    · exact C.hgbColour hcu
    · exact hub rfl
  have hwBoundary : ¬StrictlyInsideHexagon h w := by
    intro hwI
    rcases C.insideCover w hwI with rfl | rfl | rfl | rfl | rfl
    · exact C.hredBColour hcw
    · exact C.hredBColour (C.hred.trans hcw)
    · exact C.hvbColour hcw
    · exact C.hgbColour hcw
    · exact hwb rfl
  rcases eleven_red_two_signs C with
    ⟨hpp, hpqq, hpqv, hpqb, hpqg, hxyp, hxyv, hxyq, hxyg, hxyb⟩
  have hzeroImpossible : ∀ z : B, colour z = colour C.b →
      turn (C.p : Point) (C.q : Point) z ≠ 0 := by
    intro z hcz hz0
    have hpvNe : C.p ≠ C.v := hneColour C.hredBlue
    have hqP : C.q ≠ C.p := C.hpq.symm
    have hqV : C.q ≠ C.v := hneColour (C.hred.symm.trans_ne C.hredBlue)
    have hzP : z ≠ C.p := hneColour (hcz.trans_ne C.hredBColour.symm)
    have hzV : z ≠ C.v := hneColour (hcz.trans_ne C.hvbColour.symm)
    obtain ⟨t, -, -, hrel⟩ := turn_relation_of_between (z := (z : Point)) C.hpv
    rw [hz0, mul_zero] at hrel
    have hzLine : (z : Point) ∈ affineSpan ℝ {(C.p : Point), (C.v : Point)} :=
      mem_line_of_turn_eq_zero (Subtype.val_injective.ne hpvNe) hrel
    have hqLine : (C.q : Point) ∈ affineSpan ℝ {(C.p : Point), (C.v : Point)} :=
      right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne C.hpq) C.hpv
    have heq := extra_points_eq_on_saturated_line hfourB hpvNe
      hqP hqV hzP hzV hqLine hzLine
    exact C.hredBColour (C.hred.trans ((congrArg colour heq).trans hcz))
  have hnegative : ∀ z : B, z ≠ C.b → colour z = colour C.b →
      turn (C.p : Point) (C.q : Point) z < 0 := by
    intro z hzb hcz
    have hz0 := hzeroImpossible z hcz
    by_contra hn
    have hzpos : 0 < turn (C.p : Point) (C.q : Point) z :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz0)
    obtain ⟨a, ha⟩ := hproper C.b z hzb.symm hcz.symm
    have haPos := edgeTurn_pos_of_mem_openSegment ha hpqb.le hzpos.le (Or.inl hpqb)
    rcases C.insideCover a
      (openSegment_between_blockers_strictlyInside hfour hh hhP hside
        C.b.property z.property (Subtype.val_injective.ne hzb.symm) ha) with
      rfl | rfl | rfl | rfl | rfl
    · linarith
    · linarith
    · linarith
    · linarith
    · have : (C.b : Point) ≠ (z : Point) := Subtype.val_injective.ne hzb.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp ha)).elim
  have huNeg := hnegative u hub hcu
  have hwNeg := hnegative w hwb hcw
  obtain ⟨a, ha⟩ := hproper u w huw (hcu.trans hcw.symm)
  have haNeg := turn_neg_of_mem_openSegment ha huNeg hwNeg
  have hbase : (C.g : Point) ∈ openSegment ℝ (u : Point) (w : Point) := by
    rcases C.insideCover a
      (openSegment_between_blockers_strictlyInside hfour hh hhP hside
        u.property w.property (Subtype.val_injective.ne huw) ha) with
      rfl | rfl | rfl | h | rfl
    · linarith
    · linarith
    · linarith
    · simpa [h] using ha
    · linarith
  have hclassify : ∀ z : B, (z = u ∨ z = w) →
      z ≠ C.b → colour z = colour C.b →
      ((C.p : Point) ∈ openSegment ℝ (C.b : Point) (z : Point)) ∨
      ((C.q : Point) ∈ openSegment ℝ (C.b : Point) (z : Point)) := by
    intro z huzw hzb hcz
    obtain ⟨a, ha⟩ := hproper C.b z hzb.symm hcz.symm
    rcases C.insideCover a
      (openSegment_between_blockers_strictlyInside hfour hh hhP hside
        C.b.property z.property (Subtype.val_injective.ne hzb.symm) ha) with
      rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ha
    · exact Or.inr ha
    · exact (saturated_left_endpoint_not_between hfourB C.hvx C.hb ha).elim
    · rcases huzw with hzu | hzw
      · subst z
        have heq := other_endpoint_eq_of_common_blocker
          (a := u) (b := w) (c := C.b) (z := C.g)
          hfourB huw hub hbase (by simpa only [openSegment_symm] using ha)
        exact (hwb heq).elim
      · subst z
        have heq := other_endpoint_eq_of_common_blocker
          (a := w) (b := u) (c := C.b) (z := C.g)
          hfourB huw.symm hwb (by simpa only [openSegment_symm] using hbase)
          (by simpa only [openSegment_symm] using ha)
        exact (hub heq).elim
    · have : (C.b : Point) ≠ (z : Point) := Subtype.val_injective.ne hzb.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp ha)).elim
  have huClass := hclassify u (Or.inl rfl) hub hcu
  have hwClass := hclassify w (Or.inr rfl) hwb hcw
  have hincident :
      (((C.p : Point) ∈ openSegment ℝ (C.b : Point) (u : Point)) ∧
        ((C.q : Point) ∈ openSegment ℝ (C.b : Point) (w : Point))) ∨
      (((C.q : Point) ∈ openSegment ℝ (C.b : Point) (u : Point)) ∧
        ((C.p : Point) ∈ openSegment ℝ (C.b : Point) (w : Point))) := by
    rcases huClass with hpu | hqu <;> rcases hwClass with hpw | hqw
    · have heq := other_endpoint_eq_of_common_blocker hfourB hub.symm hwb.symm hpu hpw
      exact (huw heq).elim
    · exact Or.inl ⟨hpu, hqw⟩
    · exact Or.inr ⟨hqu, hpw⟩
    · have heq := other_endpoint_eq_of_common_blocker hfourB hub.symm hwb.symm hqu hqw
      exact (huw heq).elim
  exact ⟨
    { u := u, w := w, huw := huw, hub := hub, hwb := hwb,
      hcu := hcu, hcw := hcw, huBoundary := huBoundary,
      hwBoundary := hwBoundary, huNeg := huNeg, hwNeg := hwNeg,
      hbase := hbase, incident := hincident }⟩

/-- The two green boundary vertices lie on opposite sides of the blue base
line `xy`. -/
private theorem green_wing_straddles_blue_base
    {P : Finset Point} {h : Fin 6 → Point}
    {colour : hexBlockers P h → Fin 4}
    (C : ElevenRedTwoStructure colour) (G : ElevenGreenWing C) :
    (turn (C.x : Point) (C.y : Point) G.u < 0 ∧
        0 < turn (C.x : Point) (C.y : Point) G.w) ∨
      (0 < turn (C.x : Point) (C.y : Point) G.u ∧
        turn (C.x : Point) (C.y : Point) G.w < 0) := by
  rcases eleven_red_two_signs C with
    ⟨-, -, -, -, -, hxyp, -, hxyq, hxyg, hxyb⟩
  rcases G.incident with ⟨hpu, -⟩ | ⟨-, hpw⟩
  · have huNeg := turn_neg_of_between_of_turn_eq_zero_of_pos hpu hxyp hxyg
    obtain ⟨t, ht0, ht1, hrel⟩ :=
      turn_of_mem_openSegment
        (a := (C.x : Point)) (b := (C.y : Point)) G.hbase
    have hwPos : 0 < turn (C.x : Point) (C.y : Point) G.w := by
      rw [hrel] at hxyb
      nlinarith
    exact Or.inl ⟨huNeg, hwPos⟩
  · have hwNeg := turn_neg_of_between_of_turn_eq_zero_of_pos hpw hxyp hxyg
    obtain ⟨t, ht0, ht1, hrel⟩ :=
      turn_of_mem_openSegment
        (a := (C.x : Point)) (b := (C.y : Point)) G.hbase
    have huPos : 0 < turn (C.x : Point) (C.y : Point) G.u := by
      rw [hrel] at hxyb
      nlinarith
    exact Or.inr ⟨huPos, hwNeg⟩

/-- The two black boundary vertices also lie on opposite sides of the blue
base line `xy`. -/
private theorem black_wing_straddles_blue_base
    {P : Finset Point} {h : Fin 6 → Point}
    {colour : hexBlockers P h → Fin 4}
    (C : ElevenRedTwoStructure colour) (K : ElevenBlackWing C) :
    (turn (C.x : Point) (C.y : Point) K.u < 0 ∧
        0 < turn (C.x : Point) (C.y : Point) K.w) ∨
      (0 < turn (C.x : Point) (C.y : Point) K.u ∧
        turn (C.x : Point) (C.y : Point) K.w < 0) := by
  rcases eleven_red_two_signs C with
    ⟨-, -, -, -, -, hxyp, -, hxyq, hxyg, hxyb⟩
  rcases K.incident with ⟨hpu, -⟩ | ⟨-, hpw⟩
  · have huNeg := turn_neg_of_between_of_turn_eq_zero_of_pos hpu hxyp hxyb
    obtain ⟨t, ht0, ht1, hrel⟩ :=
      turn_of_mem_openSegment
        (a := (C.x : Point)) (b := (C.y : Point)) K.hbase
    have hwPos : 0 < turn (C.x : Point) (C.y : Point) K.w := by
      rw [hrel] at hxyg
      nlinarith
    exact Or.inl ⟨huNeg, hwPos⟩
  · have hwNeg := turn_neg_of_between_of_turn_eq_zero_of_pos hpw hxyp hxyb
    obtain ⟨t, ht0, ht1, hrel⟩ :=
      turn_of_mem_openSegment
        (a := (C.x : Point)) (b := (C.y : Point)) K.hbase
    have huPos : 0 < turn (C.x : Point) (C.y : Point) K.u := by
      rw [hrel] at hxyg
      nlinarith
    exact Or.inr ⟨huPos, hwNeg⟩

/-- Reindexing all six vertices cannot change the fact that exactly two of
them lie in a specified strict half-plane. -/
private theorem negativeSideIndices_card_two_of_enumeration
    {f : Fin 6 → Point} {idx : Fin 6 → Fin 6}
    (hinj : Function.Injective idx) (hsurj : Function.Surjective idx)
    {i j a b : Fin 6} (hab : a ≠ b)
    (ha : turn (f i) (f j) (f (idx a)) < 0)
    (hb : turn (f i) (f j) (f (idx b)) < 0)
    (hrest : ∀ t, t ≠ a → t ≠ b →
      0 ≤ turn (f i) (f j) (f (idx t))) :
    (negativeSideIndices f i j).card = 2 := by
  classical
  have hset : negativeSideIndices f i j = {idx a, idx b} := by
    ext k
    simp only [negativeSideIndices, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hk
      obtain ⟨t, rfl⟩ := hsurj k
      by_cases hta : t = a
      · exact Or.inl (congrArg idx hta)
      by_cases htb : t = b
      · exact Or.inr (congrArg idx htb)
      exact (not_lt_of_ge (hrest t hta htb) hk).elim
    · rintro (hk | hk)
      · rw [hk]
        exact ha
      · rw [hk]
        exact hb
  rw [hset]
  simp [hinj.ne hab]

/-- In the red-two eleven-point configuration, the blue side blockers lie
on opposite sides of the cyclically labelled hexagon. -/
private theorem red_two_blue_side_indices_opposite
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    {colour : hexBlockers P h → Fin 4}
    (C : ElevenRedTwoStructure colour)
    (G : ElevenGreenWing C) (K : ElevenBlackWing C) :
    ∃ i : Fin 6,
      (C.x : Point) = sideBlocker hside i ∧
      (C.y : Point) = sideBlocker hside (i + 3) := by
  classical
  let B := hexBlockers P h
  let e : Fin 6 → B := ![C.x, C.y, G.u, G.w, K.u, K.w]
  have hneColour {a b : B} (hc : colour a ≠ colour b) : a ≠ b := by
    intro hab
    exact hc (congrArg colour hab)
  have hBlueGreen {a b : B} (ha : colour a = colour C.v)
      (hb : colour b = colour C.g) : a ≠ b := by
    apply hneColour
    intro heq
    apply C.hvgColour
    calc
      colour C.v = colour a := ha.symm
      _ = colour b := heq
      _ = colour C.g := hb
  have hBlueBlack {a b : B} (ha : colour a = colour C.v)
      (hb : colour b = colour C.b) : a ≠ b := by
    apply hneColour
    intro heq
    apply C.hvbColour
    calc
      colour C.v = colour a := ha.symm
      _ = colour b := heq
      _ = colour C.b := hb
  have hGreenBlack {a b : B} (ha : colour a = colour C.g)
      (hb : colour b = colour C.b) : a ≠ b := by
    apply hneColour
    intro heq
    apply C.hgbColour
    calc
      colour C.g = colour a := ha.symm
      _ = colour b := heq
      _ = colour C.b := hb
  have hcxv : colour C.x = colour C.v := C.hblueX.symm
  have hcyv : colour C.y = colour C.v :=
    C.hblueY.symm.trans C.hblueX.symm
  have hxgu := hBlueGreen hcxv G.hcu
  have hxgw := hBlueGreen hcxv G.hcw
  have hygu := hBlueGreen hcyv G.hcu
  have hygw := hBlueGreen hcyv G.hcw
  have hxku := hBlueBlack hcxv K.hcu
  have hxkw := hBlueBlack hcxv K.hcw
  have hyku := hBlueBlack hcyv K.hcu
  have hykw := hBlueBlack hcyv K.hcw
  have hguku := hGreenBlack G.hcu K.hcu
  have hgukw := hGreenBlack G.hcu K.hcw
  have hgwku := hGreenBlack G.hcw K.hcu
  have hgwkw := hGreenBlack G.hcw K.hcw
  have heInj : Function.Injective e := by
    simpa only [e] using six_vector_injective C.hxy hxgu hxgw hxku hxkw
      hygu hygw hyku hykw G.huw hguku hgukw hgwku hgwkw K.huw
  have heBoundary : ∀ t : Fin 6, ¬StrictlyInsideHexagon h (e t) := by
    intro t
    fin_cases t <;> simp [e, C.hxBoundary, C.hyBoundary,
      G.huBoundary, G.hwBoundary, K.huBoundary, K.hwBoundary]
  have hindexExists : ∀ t : Fin 6, ∃ i : Fin 6,
      ((e t : B) : Point) = sideBlocker hside i := by
    intro t
    exact (not_strictlyInside_iff_sideBlocker hfour hh hhP hside
      (e t).property).mp (heBoundary t)
  let idx : Fin 6 → Fin 6 := fun t ↦ Classical.choose (hindexExists t)
  have hidx : ∀ t : Fin 6,
      ((e t : B) : Point) = sideBlocker hside (idx t) := by
    intro t
    exact Classical.choose_spec (hindexExists t)
  have hidxInj : Function.Injective idx := by
    intro i j hij
    apply heInj
    apply Subtype.ext
    rw [hidx i, hidx j, hij]
  have hidxSurj : Function.Surjective idx :=
    Finite.surjective_of_injective hidxInj
  let s : Fin 6 → Point := sideBlocker hside
  have hsStrict : StrictConvexHexagon s :=
    sideBlockers_strictConvexHexagon hh hside
  have hturnEq : ∀ t : Fin 6,
      turn (s (idx 0)) (s (idx 1)) (s (idx t)) =
        turn (C.x : Point) (C.y : Point) (e t : Point) := by
    intro t
    dsimp only [s]
    rw [← hidx 0, ← hidx 1, ← hidx t]
    rfl
  have hnegCard : (negativeSideIndices s (idx 0) (idx 1)).card = 2 := by
    rcases green_wing_straddles_blue_base C G with hG | hG <;>
      rcases black_wing_straddles_blue_base C K with hK | hK
    · apply negativeSideIndices_card_two_of_enumeration hidxInj hidxSurj
        (a := (2 : Fin 6)) (b := (4 : Fin 6)) (by decide)
      · rw [hturnEq]
        simpa [e] using hG.1
      · rw [hturnEq]
        simpa [e] using hK.1
      · intro t ht2 ht4
        rw [hturnEq]
        fin_cases t
        · simp [e]
        · simp [e]
        · exact (ht2 rfl).elim
        · simpa [e] using hG.2.le
        · exact (ht4 rfl).elim
        · simpa [e] using hK.2.le
    · apply negativeSideIndices_card_two_of_enumeration hidxInj hidxSurj
        (a := (2 : Fin 6)) (b := (5 : Fin 6)) (by decide)
      · rw [hturnEq]
        simpa [e] using hG.1
      · rw [hturnEq]
        simpa [e] using hK.2
      · intro t ht2 ht5
        rw [hturnEq]
        fin_cases t
        · simp [e]
        · simp [e]
        · exact (ht2 rfl).elim
        · simpa [e] using hG.2.le
        · simpa [e] using hK.1.le
        · exact (ht5 rfl).elim
    · apply negativeSideIndices_card_two_of_enumeration hidxInj hidxSurj
        (a := (3 : Fin 6)) (b := (4 : Fin 6)) (by decide)
      · rw [hturnEq]
        simpa [e] using hG.2
      · rw [hturnEq]
        simpa [e] using hK.1
      · intro t ht3 ht4
        rw [hturnEq]
        fin_cases t
        · simp [e]
        · simp [e]
        · simpa [e] using hG.1.le
        · exact (ht3 rfl).elim
        · exact (ht4 rfl).elim
        · simpa [e] using hK.2.le
    · apply negativeSideIndices_card_two_of_enumeration hidxInj hidxSurj
        (a := (3 : Fin 6)) (b := (5 : Fin 6)) (by decide)
      · rw [hturnEq]
        simpa [e] using hG.2
      · rw [hturnEq]
        simpa [e] using hK.2
      · intro t ht3 ht5
        rw [hturnEq]
        fin_cases t
        · simp [e]
        · simp [e]
        · simpa [e] using hG.1.le
        · exact (ht3 rfl).elim
        · simpa [e] using hK.1.le
        · exact (ht5 rfl).elim
  have hidx01 : idx 0 ≠ idx 1 := hidxInj.ne (by decide)
  have hopp := eq_add_three_of_negativeSideIndices_card_two
    hsStrict hidx01 hnegCard
  refine ⟨idx 0, ?_, ?_⟩
  · simpa [e] using hidx 0
  · rw [← hopp]
    simpa [e] using hidx 1

/-- If two side blockers have opposite labels, the short diagonal joining
the two intervening hexagon vertices lies strictly on the reverse side of
their line. -/
private theorem opposite_sideBlocker_diagonal_endpoints_neg
    {B : Finset Point} {h : Fin 6 → Point}
    (hh : StrictConvexHexagon h)
    (hside : ∀ i : Fin 6, ∃ s ∈ B,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (i : Fin 6) :
    turn (sideBlocker hside i) (sideBlocker hside (i + 3)) (h (i + 1)) < 0 ∧
      turn (sideBlocker hside i) (sideBlocker hside (i + 3)) (h (i + 3)) < 0 := by
  have h30 : i + 3 ≠ i := by fin_cases i <;> decide
  have h31 : i + 3 ≠ i + 1 := by fin_cases i <;> decide
  have h40 : (i + 3) + 1 ≠ i := by fin_cases i <;> decide
  have h41 : (i + 3) + 1 ≠ i + 1 := by fin_cases i <;> decide
  have h03 : i ≠ i + 3 := h30.symm
  have h04 : i ≠ (i + 3) + 1 := h40.symm
  have h13 : i + 1 ≠ i + 3 := h31.symm
  have h14 : i + 1 ≠ (i + 3) + 1 := h41.symm
  have hfarPos :
      0 < turn (h i) (h (i + 1)) (sideBlocker hside (i + 3)) := by
    apply edgeTurn_pos_of_mem_openSegment (sideBlocker_between hside (i + 3))
      (hh.2.1 i (i + 3) h30 h31).le
      (hh.2.1 i ((i + 3) + 1) h40 h41).le
    exact Or.inl (hh.2.1 i (i + 3) h30 h31)
  have hnearPos :
      0 < turn (h (i + 3)) (h ((i + 3) + 1)) (sideBlocker hside i) := by
    apply edgeTurn_pos_of_mem_openSegment (sideBlocker_between hside i)
      (hh.2.1 (i + 3) i h03 h04).le
      (hh.2.1 (i + 3) (i + 1) h13 h14).le
    exact Or.inl (hh.2.1 (i + 3) i h03 h04)
  constructor
  · obtain ⟨t, ht0, ht1, hrel⟩ :=
      turn_of_mem_openSegment
        (a := sideBlocker hside (i + 3)) (b := h (i + 1))
        (sideBlocker_between hside i)
    have hbase :
        turn (sideBlocker hside (i + 3)) (h (i + 1)) (h i) < 0 := by
      have hrot :
          0 < turn (sideBlocker hside (i + 3)) (h i) (h (i + 1)) := by
        simpa only [turn_rotate] using hfarPos
      rw [turn_swap_last]
      linarith
    rw [turn_rotate, turn_rotate, hrel]
    simp only [turn_self_right, mul_zero, add_zero]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hbase
  · obtain ⟨t, ht0, ht1, hrel⟩ :=
      turn_of_mem_openSegment
        (a := sideBlocker hside i) (b := h (i + 3))
        (sideBlocker_between hside (i + 3))
    have hbase :
        0 < turn (sideBlocker hside i) (h (i + 3)) (h ((i + 3) + 1)) := by
      simpa only [turn_rotate] using hnearPos
    rw [turn_swap_last, hrel]
    simp only [turn_self_right, mul_zero, zero_add]
    exact neg_neg_of_pos (mul_pos ht0 hbase)

/-- The short diagonal between the two vertices immediately following an
opposite pair of side labels is one of the nine listed diagonals. -/
private theorem exists_blocker_on_intervening_diagonal
    {B : Finset Point} {h : Fin 6 → Point}
    (hdiag : ∀ d : Fin 9, ∃ r ∈ B,
      r ∈ openSegment ℝ
        (h (diagonalEnds d).1) (h (diagonalEnds d).2))
    (i : Fin 6) :
    ∃ r ∈ B, r ∈ openSegment ℝ (h (i + 1)) (h (i + 3)) := by
  fin_cases i
  · simpa [diagonalEnds] using hdiag 3
  · simpa [diagonalEnds] using hdiag 6
  · simpa [diagonalEnds] using hdiag 8
  · simpa [diagonalEnds, openSegment_symm] using hdiag 2
  · simpa [diagonalEnds, openSegment_symm] using hdiag 5
  · simpa [diagonalEnds] using hdiag 0

/-- The red-class-of-size-two branch at eleven blockers ends with an
unblocked short diagonal. -/
private theorem no_eleven_of_interior_pair_colour_two
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hdiag : ∀ d : Fin 9, ∃ r ∈ hexBlockers P h,
      r ∈ openSegment ℝ
        (h (diagonalEnds d).1) (h (diagonalEnds d).2))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {p q : hexBlockers P h} (hpq : p ≠ q)
    (hpI : StrictlyInsideHexagon h p)
    (hqI : StrictlyInsideHexagon h q)
    (hcq : colour q = colour p)
    (hredCard : (colourFiber colour (colour p)).card = 2) : False := by
  obtain ⟨C⟩ := build_eleven_red_two hfour hh hhP hside hcard colour
    hproper hle hpq hpI hqI hcq hredCard
  obtain ⟨G⟩ := build_eleven_green_wing hfour hh hhP hside hcard colour
    hproper hle C C.hredCard
  obtain ⟨K⟩ := build_eleven_black_wing hfour hh hhP hside hcard colour
    hproper hle C C.hredCard
  obtain ⟨i, hxi, hyi⟩ :=
    red_two_blue_side_indices_opposite hfour hh hhP hside C G K
  obtain ⟨z, hzB, hzseg⟩ := exists_blocker_on_intervening_diagonal hdiag i
  let zB : hexBlockers P h := ⟨z, hzB⟩
  have hend := opposite_sideBlocker_diagonal_endpoints_neg hh hside i
  have hzneg : turn (C.x : Point) (C.y : Point) zB < 0 := by
    rw [hxi, hyi]
    exact turn_neg_of_mem_openSegment hzseg hend.1 hend.2
  have hzI : StrictlyInsideHexagon h zB := by
    intro side
    apply diagonalPoint_edgeTurn_pos hh
      (j := i + 1) (k := i + 3)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      (by fin_cases i <;> decide)
      hzseg side
  rcases eleven_red_two_signs C with
    ⟨-, -, -, -, -, hxyp, hxyv, hxyq, hxyg, hxyb⟩
  rcases C.insideCover zB hzI with hz | hz | hz | hz | hz
  · rw [hz] at hzneg
    linarith
  · rw [hz] at hzneg
    linarith
  · rw [hz] at hzneg
    linarith
  · rw [hz] at hzneg
    linarith
  · rw [hz] at hzneg
    linarith

/-- In the oriented eleven-point configuration, the colour of the blocker
`v` of `pq` cannot occur three times.  The crosscut `bg` puts both other
points of that colour in its negative half-plane, while every possible
blocker of their pair is in its nonnegative half-plane. -/
private theorem crosscut_colourFiber_ne_three
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {p q r v g b : B}
    (hpq : p ≠ q) (hpqr : 0 < turn (p : Point) (q : Point) (r : Point))
    (hv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hg : (g : Point) ∈ openSegment ℝ (p : Point) (r : Point))
    (hb : (b : Point) ∈ openSegment ℝ (q : Point) (r : Point))
    (hvp : colour v ≠ colour p)
    (hinside : ∀ {x y z : B}, x ≠ y →
      (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b) :
    (colourFiber colour (colour v)).card ≠ 3 := by
  intro hthree
  obtain ⟨x, y, hxy, hxv, hyv, hcx, hcy⟩ :=
    exists_two_others_of_colourFiber_card_three hthree rfl
  have hcross := triangle_crosscut_signs hpqr hv hg hb
  have hnegative : ∀ z : B, z ≠ v → colour z = colour v →
      turn (b : Point) (g : Point) (z : Point) < 0 := by
    intro z hzv hcz
    obtain ⟨w, hw⟩ := hproper v z hzv.symm hcz.symm
    have hwcases := hinside hzv.symm hw
    rcases hwcases with hwp | hwq | hwv | hwg | hwb
    · subst w
      exact ((saturated_left_endpoint_not_between hfour hpq hv) hw).elim
    · subst w
      exact ((saturated_right_endpoint_not_between hfour hpq hv) hw).elim
    · subst w
      have : (v : Point) ≠ (z : Point) := Subtype.val_injective.ne hzv.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hw)).elim
    · subst w
      exact turn_neg_of_between_of_turn_eq_zero_of_pos hw (by simp) hcross.2.2.1
    · subst w
      exact turn_neg_of_between_of_turn_eq_zero_of_pos hw (by simp) hcross.2.2.1
  have hxneg := hnegative x hxv hcx
  have hyneg := hnegative y hyv hcy
  obtain ⟨z, hz⟩ := hproper x y hxy (hcx.trans hcy.symm)
  have hzneg := turn_neg_of_mem_openSegment hz hxneg hyneg
  rcases hinside hxy hz with rfl | rfl | rfl | rfl | rfl
  · linarith [hcross.1]
  · linarith [hcross.2.1]
  · linarith [hcross.2.2.1]
  · simpa using hzneg
  · simpa using hzneg

/-- A supporting line cannot have two same-coloured points beyond an anchor
when their two anchor segments meet that line in zero-turn blockers and every
possible blocker of the pair is on the nonnegative side. -/
private theorem same_colour_pair_impossible_across_support
    {B : Finset Point} (colour : B → Fin 4)
    (hproper : ProperBlocking B colour)
    {p q v g b anchor x y z₁ z₂ : B} {a c : Point}
    (hinside : ∀ {u w z : B}, u ≠ w →
      (z : Point) ∈ openSegment ℝ (u : Point) (w : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b)
    (hxy : x ≠ y) (hcxy : colour x = colour y)
    (hz₁ : (z₁ : Point) ∈ openSegment ℝ (anchor : Point) (x : Point))
    (hz₂ : (z₂ : Point) ∈ openSegment ℝ (anchor : Point) (y : Point))
    (hz₁0 : turn a c z₁ = 0) (hz₂0 : turn a c z₂ = 0)
    (hanchor : 0 < turn a c anchor)
    (hp0 : 0 ≤ turn a c p) (hq0 : 0 ≤ turn a c q)
    (hv0 : 0 ≤ turn a c v) (hg0 : 0 ≤ turn a c g)
    (hb0 : 0 ≤ turn a c b) : False := by
  have hxneg := turn_neg_of_between_of_turn_eq_zero_of_pos hz₁ hz₁0 hanchor
  have hyneg := turn_neg_of_between_of_turn_eq_zero_of_pos hz₂ hz₂0 hanchor
  obtain ⟨z, hz⟩ := hproper x y hxy hcxy
  have hzneg := turn_neg_of_mem_openSegment hz hxneg hyneg
  rcases hinside hxy hz with rfl | rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- Six-point interior-cover version of the preceding supporting-line
visibility lemma. -/
private theorem same_colour_pair_impossible_across_support_six
    {B : Finset Point} (colour : B → Fin 4)
    (hproper : ProperBlocking B colour)
    {p q r v g b anchor x y z₁ z₂ : B} {a c : Point}
    (hinside : ∀ {u w z : B}, u ≠ w →
      (z : Point) ∈ openSegment ℝ (u : Point) (w : Point) →
      z = p ∨ z = q ∨ z = r ∨ z = v ∨ z = g ∨ z = b)
    (hxy : x ≠ y) (hcxy : colour x = colour y)
    (hz₁ : (z₁ : Point) ∈ openSegment ℝ (anchor : Point) (x : Point))
    (hz₂ : (z₂ : Point) ∈ openSegment ℝ (anchor : Point) (y : Point))
    (hz₁0 : turn a c z₁ = 0) (hz₂0 : turn a c z₂ = 0)
    (hanchor : 0 < turn a c anchor)
    (hp0 : 0 ≤ turn a c p) (hq0 : 0 ≤ turn a c q)
    (hr0 : 0 ≤ turn a c r) (hv0 : 0 ≤ turn a c v)
    (hg0 : 0 ≤ turn a c g) (hb0 : 0 ≤ turn a c b) : False := by
  have hxneg := turn_neg_of_between_of_turn_eq_zero_of_pos hz₁ hz₁0 hanchor
  have hyneg := turn_neg_of_between_of_turn_eq_zero_of_pos hz₂ hz₂0 hanchor
  obtain ⟨z, hz⟩ := hproper x y hxy hcxy
  have hzneg := turn_neg_of_mem_openSegment hz hxneg hyneg
  rcases hinside hxy hz with rfl | rfl | rfl | rfl | rfl | rfl
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith
  · linarith

/-- The two points other than `b` in the colour class of `b` lie on the two
lines `bv` and `bg`.  The apparent third option `bp` is eliminated by the
two supporting lines `pv` and `gp`. -/
private theorem black_other_points_on_two_lines
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {p q r v g b x y : B}
    (hpqr : 0 < turn (p : Point) (q : Point) (r : Point))
    (hv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hg : (g : Point) ∈ openSegment ℝ (p : Point) (r : Point))
    (hb : (b : Point) ∈ openSegment ℝ (q : Point) (r : Point))
    (hinside : ∀ {u w z : B}, u ≠ w →
      (z : Point) ∈ openSegment ℝ (u : Point) (w : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b)
    (hxy : x ≠ y) (hxb : x ≠ b) (hyb : y ≠ b)
    (hcx : colour x = colour b) (hcy : colour y = colour b) :
    ((x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(b : Point), (g : Point)}) ∧
    ((y : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (y : Point) ∈ affineSpan ℝ {(b : Point), (g : Point)}) := by
  have hqr : q ≠ r := by
    intro e
    subst r
    simpa using hpqr
  have hsides := triangle_side_support_signs hpqr hv hg hb
  rcases hsides with
    ⟨⟨hpvp, hpvq, hpvv, hpvr, hpvg, hpvb⟩,
      ⟨hgpg, hgpp, hgpr, hgpq, hgpv, hgpb⟩,
      hvq, hqb⟩
  have hcandidates : ∀ {z : B}, z ≠ b → colour z = colour b →
      ((p : Point) ∈ openSegment ℝ (b : Point) (z : Point)) ∨
      ((v : Point) ∈ openSegment ℝ (b : Point) (z : Point)) ∨
      ((g : Point) ∈ openSegment ℝ (b : Point) (z : Point)) := by
    intro z hzb hcz
    obtain ⟨w, hw⟩ := hproper b z hzb.symm hcz.symm
    rcases hinside hzb.symm hw with hwp | hwq | hwv | hwg | hwb'
    · subst w
      exact Or.inl hw
    · subst w
      exact ((saturated_left_endpoint_not_between hfour hqr hb) hw).elim
    · subst w
      exact Or.inr (Or.inl hw)
    · subst w
      exact Or.inr (Or.inr hw)
    · subst w
      have : (b : Point) ≠ (z : Point) := Subtype.val_injective.ne hzb.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hw)).elim
  have hnoP : ∀ {z w : B}, z ≠ w → z ≠ b → w ≠ b →
      colour z = colour b → colour w = colour b →
      ¬((p : Point) ∈ openSegment ℝ (b : Point) (z : Point)) := by
    intro z w hzw hzb hwb hcz hcw hpz
    rcases hcandidates hwb hcw with hpw | hvw | hgw
    · have heq := other_endpoint_eq_of_common_blocker hfour
        hzb.symm hwb.symm hpz hpw
      exact hzw heq
    · exact same_colour_pair_impossible_across_support colour hproper hinside
        hzw (hcz.trans hcw.symm) hpz hvw hpvp hpvv hpvb
        hpvp.ge hpvq.ge hpvv.ge hpvg.le hpvb.le
    · exact same_colour_pair_impossible_across_support colour hproper hinside
        hzw (hcz.trans hcw.symm) hpz hgw hgpp hgpg hgpb
        hgpp.ge hgpq.le hgpv.le hgpg.ge hgpb.le
  have hxCand := hcandidates hxb hcx
  have hyCand := hcandidates hyb hcy
  have hxNo := hnoP hxy hxb hyb hcx hcy
  have hyNo := hnoP hxy.symm hyb hxb hcy hcx
  constructor
  · rcases hxCand with hp | hvx | hgx
    · exact (hxNo hp).elim
    · left
      simpa only [Set.pair_comm] using
        right_mem_affineSpan_pair_of_between
          (Subtype.val_injective.ne hxb.symm) hvx
    · right
      exact right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hxb.symm) hgx
  · rcases hyCand with hp | hvy | hgy
    · exact (hyNo hp).elim
    · left
      simpa only [Set.pair_comm] using
        right_mem_affineSpan_pair_of_between
          (Subtype.val_injective.ne hyb.symm) hvy
    · right
      exact right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hyb.symm) hgy

/-- Symmetrically, the two points other than `g` in the colour class of `g`
lie on `gv` and `gb`; the option `gq` is excluded by the supporting lines
`vq` and `qb`. -/
private theorem green_other_points_on_two_lines
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {p q r v g b x y : B}
    (hpqr : 0 < turn (p : Point) (q : Point) (r : Point))
    (hv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hg : (g : Point) ∈ openSegment ℝ (p : Point) (r : Point))
    (hb : (b : Point) ∈ openSegment ℝ (q : Point) (r : Point))
    (hinside : ∀ {u w z : B}, u ≠ w →
      (z : Point) ∈ openSegment ℝ (u : Point) (w : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hcx : colour x = colour g) (hcy : colour y = colour g) :
    ((x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(g : Point), (b : Point)}) ∧
    ((y : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)} ∨
      (y : Point) ∈ affineSpan ℝ {(g : Point), (b : Point)}) := by
  have hpr : p ≠ r := by
    intro e
    subst r
    simpa using hpqr
  have hsides := triangle_side_support_signs hpqr hv hg hb
  rcases hsides with
    ⟨hpv, hgp,
      ⟨hvqp, hvqq, hvqv, hvqr, hvqg, hvqb⟩,
      ⟨hqbq, hqbb, hqbr, hqbp, hqbv, hqbg⟩⟩
  have hcandidates : ∀ {z : B}, z ≠ g → colour z = colour g →
      ((q : Point) ∈ openSegment ℝ (g : Point) (z : Point)) ∨
      ((v : Point) ∈ openSegment ℝ (g : Point) (z : Point)) ∨
      ((b : Point) ∈ openSegment ℝ (g : Point) (z : Point)) := by
    intro z hzg hcz
    obtain ⟨w, hw⟩ := hproper g z hzg.symm hcz.symm
    rcases hinside hzg.symm hw with hwp | hwq | hwv | hwg' | hwb
    · subst w
      exact ((saturated_left_endpoint_not_between hfour hpr hg) hw).elim
    · subst w
      exact Or.inl hw
    · subst w
      exact Or.inr (Or.inl hw)
    · subst w
      have : (g : Point) ≠ (z : Point) := Subtype.val_injective.ne hzg.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hw)).elim
    · subst w
      exact Or.inr (Or.inr hw)
  have hnoQ : ∀ {z w : B}, z ≠ w → z ≠ g → w ≠ g →
      colour z = colour g → colour w = colour g →
      ¬((q : Point) ∈ openSegment ℝ (g : Point) (z : Point)) := by
    intro z w hzw hzg hwg hcz hcw hqz
    rcases hcandidates hwg hcw with hqw | hvw | hbw
    · have heq := other_endpoint_eq_of_common_blocker hfour
        hzg.symm hwg.symm hqz hqw
      exact hzw heq
    · exact same_colour_pair_impossible_across_support colour hproper hinside
        hzw (hcz.trans hcw.symm) hqz hvw hvqq hvqv hvqg
        hvqp.ge hvqq.ge hvqv.ge hvqg.le hvqb.le
    · exact same_colour_pair_impossible_across_support colour hproper hinside
        hzw (hcz.trans hcw.symm) hqz hbw hqbq hqbb hqbg
        hqbp.le hqbq.ge hqbv.le hqbg.le hqbb.ge
  have hxCand := hcandidates hxg hcx
  have hyCand := hcandidates hyg hcy
  have hxNo := hnoQ hxy hxg hyg hcx hcy
  have hyNo := hnoQ hxy.symm hyg hxg hcy hcx
  constructor
  · rcases hxCand with hq | hvx | hbx
    · exact (hxNo hq).elim
    · left
      simpa only [Set.pair_comm] using
        right_mem_affineSpan_pair_of_between
          (Subtype.val_injective.ne hxg.symm) hvx
    · right
      exact right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hxg.symm) hbx
  · rcases hyCand with hq | hvy | hby
    · exact (hyNo hq).elim
    · left
      simpa only [Set.pair_comm] using
        right_mem_affineSpan_pair_of_between
          (Subtype.val_injective.ne hyg.symm) hvy
    · right
      exact right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hyg.symm) hby

/-- Any other point of the colour of `v` lies on `vb` or `vg`, because the
saturated line `p-v-q` excludes `p` and `q` as blockers. -/
private theorem blue_other_point_on_two_lines
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {p q v g b x : B} (hpq : p ≠ q)
    (hv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hinside : ∀ {u w z : B}, u ≠ w →
      (z : Point) ∈ openSegment ℝ (u : Point) (w : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b)
    (hxv : x ≠ v) (hcx : colour x = colour v) :
    (x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)} := by
  obtain ⟨w, hw⟩ := hproper v x hxv.symm hcx.symm
  rcases hinside hxv.symm hw with hwp | hwq | hwv | hwg | hwb
  · subst w
    exact ((saturated_left_endpoint_not_between hfour hpq hv) hw).elim
  · subst w
    exact ((saturated_right_endpoint_not_between hfour hpq hv) hw).elim
  · subst w
    have : (v : Point) ≠ (x : Point) := Subtype.val_injective.ne hxv.symm
    exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hw)).elim
  · subst w
    right
    exact right_mem_affineSpan_pair_of_between
      (Subtype.val_injective.ne hxv.symm) hw
  · subst w
    left
    exact right_mem_affineSpan_pair_of_between
      (Subtype.val_injective.ne hxv.symm) hw

/-- In the six-point interior pattern of a monochromatic triangle, the two
other points of the colour of the blocker on `pq` lie on `vb` or `vg`.
The third apparent ray `vr` is separated from each adjacent ray by a side
line of the triangle. -/
private theorem triangle_side_colour_other_points_on_adjacent_lines
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {p q r v g b x y : B}
    (hpq : p ≠ q) (hpqr : 0 < turn (p : Point) (q : Point) (r : Point))
    (hv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hg : (g : Point) ∈ openSegment ℝ (p : Point) (r : Point))
    (hb : (b : Point) ∈ openSegment ℝ (q : Point) (r : Point))
    (hinside : ∀ {u w z : B}, u ≠ w →
      (z : Point) ∈ openSegment ℝ (u : Point) (w : Point) →
      z = p ∨ z = q ∨ z = r ∨ z = v ∨ z = g ∨ z = b)
    (hxy : x ≠ y) (hxv : x ≠ v) (hyv : y ≠ v)
    (hcx : colour x = colour v) (hcy : colour y = colour v) :
    ((x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)}) ∧
    ((y : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (y : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)}) := by
  have hsides := triangle_side_support_signs hpqr hv hg hb
  rcases hsides with
    ⟨hpv,
      ⟨hgpg, hgpp, hgpr, hgpq, hgpv, hgpb⟩,
      hvq,
      ⟨hqbq, hqbb, hqbr, hqbp, hqbv, hqbg⟩⟩
  have hcandidates : ∀ {z : B}, z ≠ v → colour z = colour v →
      ((r : Point) ∈ openSegment ℝ (v : Point) (z : Point)) ∨
      ((g : Point) ∈ openSegment ℝ (v : Point) (z : Point)) ∨
      ((b : Point) ∈ openSegment ℝ (v : Point) (z : Point)) := by
    intro z hzv hcz
    obtain ⟨w, hw⟩ := hproper v z hzv.symm hcz.symm
    rcases hinside hzv.symm hw with hwp | hwq | hwr | hwv | hwg | hwb
    · subst w
      exact ((saturated_left_endpoint_not_between hfour hpq hv) hw).elim
    · subst w
      exact ((saturated_right_endpoint_not_between hfour hpq hv) hw).elim
    · subst w
      exact Or.inl hw
    · subst w
      have : (v : Point) ≠ (z : Point) := Subtype.val_injective.ne hzv.symm
      exact (this ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hw)).elim
    · subst w
      exact Or.inr (Or.inl hw)
    · subst w
      exact Or.inr (Or.inr hw)
  have hnoR : ∀ {z w : B}, z ≠ w → z ≠ v → w ≠ v →
      colour z = colour v → colour w = colour v →
      ¬((r : Point) ∈ openSegment ℝ (v : Point) (z : Point)) := by
    intro z w hzw hzv hwv hcz hcw hrz
    rcases hcandidates hwv hcw with hrw | hgw | hbw
    · have heq := other_endpoint_eq_of_common_blocker hfour
        hzv.symm hwv.symm hrz hrw
      exact hzw heq
    · exact same_colour_pair_impossible_across_support_six
        (p := p) (q := q) (r := r) (v := v) (g := g) (b := b)
        colour hproper hinside hzw (hcz.trans hcw.symm)
        hrz hgw hgpr hgpg hgpv
        hgpp.ge hgpq.le hgpr.ge hgpv.le hgpg.ge hgpb.le
    · exact same_colour_pair_impossible_across_support_six
        (p := p) (q := q) (r := r) (v := v) (g := g) (b := b)
        colour hproper hinside hzw (hcz.trans hcw.symm)
        hrz hbw hqbr hqbb hqbv
        hqbp.le hqbq.ge hqbr.ge hqbv.le hqbg.le hqbb.ge
  have hxCand := hcandidates hxv hcx
  have hyCand := hcandidates hyv hcy
  have hxNo := hnoR hxy hxv hyv hcx hcy
  have hyNo := hnoR hxy.symm hyv hxv hcy hcx
  constructor
  · rcases hxCand with hrx | hgx | hbx
    · exact (hxNo hrx).elim
    · exact Or.inr (right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hxv.symm) hgx)
    · exact Or.inl (right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hxv.symm) hbx)
  · rcases hyCand with hry | hgy | hby
    · exact (hyNo hry).elim
    · exact Or.inr (right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hyv.symm) hgy)
    · exact Or.inl (right_mem_affineSpan_pair_of_between
        (Subtype.val_injective.ne hyv.symm) hby)

/-- Three lines, each already containing two points of `B`, can contain at
most three further points of a set with no four collinear points. -/
private theorem extras_not_on_three_saturated_lines
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {v b g : B} (hvb : v ≠ b) (hvg : v ≠ g) (hbg : b ≠ g)
    (E : Finset B) (hEcard : 4 ≤ E.card)
    (hnew : ∀ x ∈ E, x ≠ v ∧ x ≠ b ∧ x ≠ g)
    (hcover : ∀ x ∈ E,
      (x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(b : Point), (g : Point)}) : False := by
  classical
  let L₀ : Finset B := E.filter fun x : B ↦
    (x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)}
  let L₁ : Finset B := E.filter fun x : B ↦
    (x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)}
  let L₂ : Finset B := E.filter fun x : B ↦
    (x : Point) ∈ affineSpan ℝ {(b : Point), (g : Point)}
  have hL₀ : L₀.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact extra_points_eq_on_saturated_line hfour hvb
      (hnew x hx'.1).1 (hnew x hx'.1).2.1
      (hnew y hy'.1).1 (hnew y hy'.1).2.1 hx'.2 hy'.2
  have hL₁ : L₁.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact extra_points_eq_on_saturated_line hfour hvg
      (hnew x hx'.1).1 (hnew x hx'.1).2.2
      (hnew y hy'.1).1 (hnew y hy'.1).2.2 hx'.2 hy'.2
  have hL₂ : L₂.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    exact extra_points_eq_on_saturated_line hfour hbg
      (hnew x hx'.1).2.1 (hnew x hx'.1).2.2
      (hnew y hy'.1).2.1 (hnew y hy'.1).2.2 hx'.2 hy'.2
  have hsub : E ⊆ (L₀ ∪ L₁) ∪ L₂ := by
    intro x hx
    rcases hcover x hx with h₀ | h₁ | h₂
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h₀⟩))
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h₁⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h₂⟩)
  have hcardSub := Finset.card_le_card hsub
  have h01 := Finset.card_union_le L₀ L₁
  have h012 := Finset.card_union_le (L₀ ∪ L₁) L₂
  omega

/-- The complete oriented form of the `|B| = 11`, red-class-of-size-three
subcase.  All geometric input has been reduced to the five-point interior
exhaustion `hinside`; the conclusion is the five-points/three-lines
contradiction above. -/
private theorem no_eleven_red_three_oriented
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    (hcard : Fintype.card B = 11)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {p q r v g b : B}
    (hpq : p ≠ q) (hpqr : 0 < turn (p : Point) (q : Point) (r : Point))
    (hv : (v : Point) ∈ openSegment ℝ (p : Point) (q : Point))
    (hg : (g : Point) ∈ openSegment ℝ (p : Point) (r : Point))
    (hb : (b : Point) ∈ openSegment ℝ (q : Point) (r : Point))
    (hcq : colour q = colour p) (hcr : colour r = colour p)
    (hvp : colour v ≠ colour p) (hgp : colour g ≠ colour p)
    (hbp : colour b ≠ colour p)
    (hvgb : colour v ≠ colour g ∧ colour v ≠ colour b ∧
      colour g ≠ colour b)
    (hred : (colourFiber colour (colour p)).card = 3)
    (hinside : ∀ {x y z : B}, x ≠ y →
      (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b) : False := by
  classical
  have hblueNot := crosscut_colourFiber_ne_three hfour colour hproper
    hpq hpqr hv hg hb hvp hinside
  have hblue : (colourFiber colour (colour v)).card = 2 :=
    colourFiber_card_two_of_eleven colour hcard hle hvp.symm hred hblueNot
  have hgreen : (colourFiber colour (colour g)).card = 3 :=
    other_colourFiber_card_three_of_eleven colour hcard hle hblue
      hvgb.1.symm
  have hblack : (colourFiber colour (colour b)).card = 3 :=
    other_colourFiber_card_three_of_eleven colour hcard hle hblue
      hvgb.2.1.symm
  obtain ⟨xv, hxvv, hcxv⟩ :=
    exists_other_of_colourFiber_card_two hblue rfl
  obtain ⟨xb₀, xb₁, hb₀b₁, hb₀b, hb₁b, hcb₀, hcb₁⟩ :=
    exists_two_others_of_colourFiber_card_three hblack rfl
  obtain ⟨xg₀, xg₁, hg₀g₁, hg₀g, hg₁g, hcg₀, hcg₁⟩ :=
    exists_two_others_of_colourFiber_card_three hgreen rfl
  have hxvLine := blue_other_point_on_two_lines hfour colour hproper hpq hv
    hinside hxvv hcxv
  have hbLines := black_other_points_on_two_lines hfour colour hproper
    hpqr hv hg hb hinside hb₀b₁ hb₀b hb₁b hcb₀ hcb₁
  have hgLines := green_other_points_on_two_lines hfour colour hproper
    hpqr hv hg hb hinside hg₀g₁ hg₀g hg₁g hcg₀ hcg₁
  have hneColour {x y : B} (hxy : colour x ≠ colour y) : x ≠ y := by
    intro e
    exact hxy (congrArg colour e)
  have hxv_b₀ : xv ≠ xb₀ := hneColour (by
    intro heq
    exact hvgb.2.1 (hcxv.symm.trans (heq.trans hcb₀)))
  have hxv_b₁ : xv ≠ xb₁ := hneColour (by
    intro heq
    exact hvgb.2.1 (hcxv.symm.trans (heq.trans hcb₁)))
  have hxv_g₀ : xv ≠ xg₀ := hneColour (by
    intro heq
    exact hvgb.1 (hcxv.symm.trans (heq.trans hcg₀)))
  have hxv_g₁ : xv ≠ xg₁ := hneColour (by
    intro heq
    exact hvgb.1 (hcxv.symm.trans (heq.trans hcg₁)))
  have hb₀_g₀ : xb₀ ≠ xg₀ := hneColour (by
    intro heq
    exact hvgb.2.2 (hcb₀.symm.trans (heq.trans hcg₀)).symm)
  have hb₀_g₁ : xb₀ ≠ xg₁ := hneColour (by
    intro heq
    exact hvgb.2.2 (hcb₀.symm.trans (heq.trans hcg₁)).symm)
  have hb₁_g₀ : xb₁ ≠ xg₀ := hneColour (by
    intro heq
    exact hvgb.2.2 (hcb₁.symm.trans (heq.trans hcg₀)).symm)
  have hb₁_g₁ : xb₁ ≠ xg₁ := hneColour (by
    intro heq
    exact hvgb.2.2 (hcb₁.symm.trans (heq.trans hcg₁)).symm)
  let E : Finset B := {xv, xb₀, xb₁, xg₀, xg₁}
  have hEcard : E.card = 5 := by
    simp [E, hxv_b₀, hxv_b₁, hxv_g₀, hxv_g₁, hb₀b₁,
      hb₀_g₀, hb₀_g₁, hb₁_g₀, hb₁_g₁, hg₀g₁]
  have hnew : ∀ x ∈ E, x ≠ v ∧ x ≠ b ∧ x ≠ g := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨hxvv, hneColour (hcxv.trans_ne hvgb.2.1),
        hneColour (hcxv.trans_ne hvgb.1)⟩
    · exact ⟨hneColour (hcb₀.trans_ne hvgb.2.1.symm), hb₀b,
        hneColour (hcb₀.trans_ne hvgb.2.2.symm)⟩
    · exact ⟨hneColour (hcb₁.trans_ne hvgb.2.1.symm), hb₁b,
        hneColour (hcb₁.trans_ne hvgb.2.2.symm)⟩
    · exact ⟨hneColour (hcg₀.trans_ne hvgb.1.symm),
        hneColour (hcg₀.trans_ne hvgb.2.2), hg₀g⟩
    · exact ⟨hneColour (hcg₁.trans_ne hvgb.1.symm),
        hneColour (hcg₁.trans_ne hvgb.2.2), hg₁g⟩
  have hcover : ∀ x ∈ E,
      (x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(b : Point), (g : Point)} := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact hxvLine.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
    · exact hbLines.1.elim Or.inl (fun h ↦ Or.inr (Or.inr h))
    · exact hbLines.2.elim Or.inl (fun h ↦ Or.inr (Or.inr h))
    · exact hgLines.1.elim (fun h ↦ Or.inr (Or.inl h))
        (fun h ↦ Or.inr (Or.inr (by simpa only [Set.pair_comm] using h)))
    · exact hgLines.2.elim (fun h ↦ Or.inr (Or.inl h))
        (fun h ↦ Or.inr (Or.inr (by simpa only [Set.pair_comm] using h)))
  exact extras_not_on_three_saturated_lines hfour
    (hneColour hvgb.2.1) (hneColour hvgb.1) (hneColour hvgb.2.2.symm)
    E (by omega) hnew hcover

/-- Geometric setup for the size-three branch of the eleven-point case. -/
private theorem no_eleven_of_interior_pair_colour_three
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {p q : hexBlockers P h} (hpq : p ≠ q)
    (hpI : StrictlyInsideHexagon h p)
    (hqI : StrictlyInsideHexagon h q)
    (hcq : colour q = colour p)
    (hred : (colourFiber colour (colour p)).card = 3) : False := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hIcard : I.card = 5 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  obtain ⟨r, hrp, hrq, hcr, -⟩ :=
    exists_third_of_colourFiber_card_three hred rfl hcq hpq
  obtain ⟨v, hv⟩ := hproper p q hpq hcq.symm
  obtain ⟨g, hg⟩ := hproper p r hrp.symm hcr.symm
  obtain ⟨b, hb⟩ := hproper q r hrq.symm (hcq.trans hcr.symm)
  have hvp : colour v ≠ colour p :=
    blocker_colour_ne hfourB hproper hpq hcq.symm hv
  have hgp : colour g ≠ colour p :=
    blocker_colour_ne (x := p) (y := r) (z := g)
      hfourB hproper hrp.symm hcr.symm hg
  have hbp : colour b ≠ colour p :=
    (blocker_colour_ne (x := q) (y := r) (z := b)
      hfourB hproper hrq.symm (hcq.trans hcr.symm) hb).trans_eq hcq
  have hvI : StrictlyInsideHexagon h v :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      p.property q.property (Subtype.val_injective.ne hpq) hv
  have hgI : StrictlyInsideHexagon h g :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      p.property r.property (Subtype.val_injective.ne hrp.symm) hg
  have hbI : StrictlyInsideHexagon h b :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      q.property r.property (Subtype.val_injective.ne hrq.symm) hb
  have hneColour {x y : B} (hxy : colour x ≠ colour y) : x ≠ y := by
    intro e
    exact hxy (congrArg colour e)
  have hvp' : v ≠ p := hneColour hvp
  have hvq : v ≠ q := hneColour (hvp.trans_eq hcq.symm)
  have hvr : v ≠ r := hneColour (hvp.trans_eq hcr.symm)
  have hgp' : g ≠ p := hneColour hgp
  have hgq : g ≠ q := hneColour (hgp.trans_eq hcq.symm)
  have hgr : g ≠ r := hneColour (hgp.trans_eq hcr.symm)
  have hbp' : b ≠ p := hneColour hbp
  have hbq : b ≠ q := hneColour (hbp.trans_eq hcq.symm)
  have hbr : b ≠ r := hneColour (hbp.trans_eq hcr.symm)
  have hvg : v ≠ g := by
    intro e
    subst g
    have hqr' := other_endpoint_eq_of_common_blocker hfourB hpq hrp.symm hv hg
    exact hrq hqr'.symm
  have hvb : v ≠ b := by
    intro e
    subst b
    have hpr' := other_endpoint_eq_of_common_blocker hfourB hpq.symm hrq.symm
      (by simpa only [openSegment_symm] using hv) hb
    exact hrp hpr'.symm
  have hgb : g ≠ b := by
    intro e
    subst b
    have hpq' := other_endpoint_eq_of_common_blocker hfourB hrp hrq
      (by simpa only [openSegment_symm] using hg)
      (by simpa only [openSegment_symm] using hb)
    exact hpq hpq'
  let e : B ↪ Point := ⟨fun z ↦ (z : Point), Subtype.val_injective⟩
  have hrNot : ¬StrictlyInsideHexagon h r := by
    intro hrI
    let K : Finset B := {p, q, r, v, g, b}
    have hKcard : K.card = 6 := by
      simp [K, hpq, hrp.symm, hvp'.symm, hgp'.symm, hbp'.symm,
        hrq.symm, hvq.symm, hgq.symm, hbq.symm, hvr.symm,
        hgr.symm, hbr.symm, hvg, hvb, hgb]
    have hKsub : ∀ x : B, x ∈ K → (x : Point) ∈ I := by
      intro x hx
      simp only [K, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h | h | h | h | h
      · subst x; exact Finset.mem_filter.mpr ⟨p.property, hpI⟩
      · subst x; exact Finset.mem_filter.mpr ⟨q.property, hqI⟩
      · subst x; exact Finset.mem_filter.mpr ⟨r.property, hrI⟩
      · subst x; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
      · subst x; exact Finset.mem_filter.mpr ⟨g.property, hgI⟩
      · subst x; exact Finset.mem_filter.mpr ⟨b.property, hbI⟩
    have hleK := card_le_of_val_mem hKsub
    rw [hKcard, hIcard] at hleK
    omega
  let K : Finset B := {p, q, v, g, b}
  let J : Finset Point := K.map e
  have hKcard : K.card = 5 := by
    simp [K, hpq, hvp'.symm, hgp'.symm, hbp'.symm,
      hvq.symm, hgq.symm, hbq.symm, hvg, hvb, hgb]
  have hJcard : J.card = 5 := by
    change (K.map e).card = 5
    simpa using hKcard
  have hJsub : J ⊆ I := by
    intro x hx
    change x ∈ K.map e at hx
    rw [Finset.mem_map] at hx
    obtain ⟨z, hzK, rfl⟩ := hx
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hzK
    rcases hzK with h | h | h | h | h
    · subst z; exact Finset.mem_filter.mpr ⟨p.property, hpI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨q.property, hqI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨g.property, hgI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨b.property, hbI⟩
  have hJI : J = I :=
    Finset.eq_of_subset_of_card_le hJsub (by rw [hIcard, hJcard])
  have hIcover : ∀ z : B, StrictlyInsideHexagon h z →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b := by
    intro z hz
    have hzI : (z : Point) ∈ I := Finset.mem_filter.mpr ⟨z.property, hz⟩
    rw [← hJI] at hzI
    change (z : Point) ∈ K.map e at hzI
    rw [Finset.mem_map] at hzI
    obtain ⟨w, hwK, hwz⟩ := hzI
    have hwzB : w = z := Subtype.ext hwz
    subst w
    simpa only [K, Finset.mem_insert, Finset.mem_singleton] using hwK
  have hinside : ∀ {x y z : B}, x ≠ y →
      (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      z = p ∨ z = q ∨ z = v ∨ z = g ∨ z = b := by
    intro x y z hxy hz
    apply hIcover z
    exact openSegment_between_blockers_strictlyInside hfour hh hhP hside
      x.property y.property (Subtype.val_injective.ne hxy) hz
  have hmono : MonoTriple colour p q r :=
    ⟨hpq, hrq.symm, hrp, hcq.symm, hcq.trans hcr.symm⟩
  have hcolourCover : ∀ d : Fin 4, d ≠ colour p →
      d = colour v ∨ d = colour g ∨ d = colour b := by
    intro d hd
    obtain ⟨x, hxHull, hcxd⟩ :=
      exists_colour_in_triangleHull hfourB hproper hmono d hd
    have hxI : StrictlyInsideHexagon h x := by
      by_contra hxNot
      obtain ⟨i, hxi⟩ :=
        (not_strictlyInside_iff_sideBlocker hfour hh hhP hside x.property).mp hxNot
      let A : Finset Point := {(p : Point), (q : Point), (r : Point)}
      have hAB : A ⊆ B := by
        intro z hz
        simp only [A, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> exact Subtype.property _
      have hsHull : sideBlocker hside i ∈ convexHull ℝ (A : Set Point) := by
        rw [← hxi]
        simpa [A, triangleHull] using hxHull
      have hsA := sideBlocker_mem_of_mem_convexHull
        hfour hh hhP hside hAB i hsHull
      have hxA : (x : Point) ∈ A := by simpa [hxi] using hsA
      simp only [A, Finset.mem_insert, Finset.mem_singleton] at hxA
      rcases hxA with hxp | hxq | hxr
      · have ex : x = p := Subtype.ext hxp
        exact hd (hcxd ▸ congrArg colour ex)
      · have ex : x = q := Subtype.ext hxq
        exact hd (hcxd ▸ (congrArg colour ex).trans hcq)
      · have ex : x = r := Subtype.ext hxr
        exact hd (hcxd ▸ (congrArg colour ex).trans hcr)
    rcases hIcover x hxI with rfl | rfl | rfl | rfl | rfl
    · exact (hd hcxd.symm).elim
    · exact (hd (hcxd.symm.trans hcq)).elim
    · exact Or.inl hcxd.symm
    · exact Or.inr (Or.inl hcxd.symm)
    · exact Or.inr (Or.inr hcxd.symm)
  have hvgb := pairwise_ne_of_fin4_nonred_cover hvp hgp hbp hcolourCover
  have hturn : turn (p : Point) (q : Point) (r : Point) ≠ 0 :=
    turn_ne_zero_of_same_colour hfourB hproper
      hmono.1 hmono.2.1 hmono.2.2.1 hmono.2.2.2.1 hmono.2.2.2.2
  by_cases hpos : 0 < turn (p : Point) (q : Point) (r : Point)
  · exact no_eleven_red_three_oriented hfourB colour hproper
      (by simpa [B, hcard]) hle hpq hpos hv hg hb hcq hcr
      hvp hgp hbp hvgb hred hinside
  · have hneg : turn (p : Point) (q : Point) (r : Point) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hturn
    have hpos' : 0 < turn (q : Point) (p : Point) (r : Point) := by
      rw [turn_swap_first]
      linarith
    have hinside' : ∀ {x y z : B}, x ≠ y →
        (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
        z = q ∨ z = p ∨ z = v ∨ z = b ∨ z = g := by
      intro x y z hxy hz
      rcases hinside hxy hz with rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    exact no_eleven_red_three_oriented hfourB colour hproper
      (by simpa [B, hcard]) hle hpq.symm hpos'
      (by simpa only [openSegment_symm] using hv) hb hg hcq.symm
      (hcr.trans hcq.symm) (hvp.trans_eq hcq.symm) (hbp.trans_eq hcq.symm)
      (hgp.trans_eq hcq.symm) ⟨hvgb.2.1, hvgb.1, hvgb.2.2.symm⟩
      (by simpa [hcq] using hred) hinside'

/-- Every colour has a strict-interior representative in a twelve-blocker
configuration.  Its three global representatives form a monochromatic
triangle, which cannot have all three vertices on the boundary. -/
private theorem exists_strictInterior_point_of_colour_twelve
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 12)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    (d : Fin 4) :
    ∃ z : hexBlockers P h,
      StrictlyInsideHexagon h z ∧ colour z = d := by
  classical
  let B := hexBlockers P h
  have hd : (colourFiber colour d).card = 3 :=
    colourFiber_card_three_of_twelve colour
      (by simpa [B, hcard]) hle d
  obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Finset.card_eq_three.mp hd
  have haMem : a ∈ colourFiber colour d := by rw [hset]; simp
  have hbMem : b ∈ colourFiber colour d := by rw [hset]; simp
  have hcMem : c ∈ colourFiber colour d := by rw [hset]; simp
  have hca : colour a = d := mem_colourFiber.mp haMem
  have hcb : colour b = d := mem_colourFiber.mp hbMem
  have hcc : colour c = d := mem_colourFiber.mp hcMem
  have hmono : MonoTriple colour a b c :=
    ⟨hab, hbc, hac.symm, hca.trans hcb.symm, hcb.trans hcc.symm⟩
  have hle' : ∀ c,
      ((Finset.univ : Finset B).filter fun p ↦ colour p = c).card ≤ 3 := by
    intro c
    simpa [B, colourFiber] using hle c
  rcases monoTriangle_has_strictInterior_vertex hfour hh hhP hside
      colour hproper hle' (by simpa [B, hcard]) hmono with h₀ | h₁ | h₂
  · exact ⟨a, h₀, hca⟩
  · exact ⟨b, h₁, hcb⟩
  · exact ⟨c, h₂, hcc⟩

private structure TwelveTwoTwoStructure
    {P : Finset Point} {h : Fin 6 → Point}
    (colour : hexBlockers P h → Fin 4) where
  r₁ : hexBlockers P h
  r₂ : hexBlockers P h
  v₁ : hexBlockers P h
  v₂ : hexBlockers P h
  g : hexBlockers P h
  b : hexBlockers P h
  hr : r₁ ≠ r₂
  hv : v₁ ≠ v₂
  hred : colour r₂ = colour r₁
  hblue : colour v₂ = colour v₁
  hredBlue : colour r₁ ≠ colour v₁
  hredG : colour r₁ ≠ colour g
  hblueG : colour v₁ ≠ colour g
  hredB : colour r₁ ≠ colour b
  hblueB : colour v₁ ≠ colour b
  hgb : colour g ≠ colour b
  hg : (g : Point) ∈ openSegment ℝ (r₁ : Point) (r₂ : Point)
  hr₁I : StrictlyInsideHexagon h r₁
  hr₂I : StrictlyInsideHexagon h r₂
  hv₁I : StrictlyInsideHexagon h v₁
  hv₂I : StrictlyInsideHexagon h v₂
  hgI : StrictlyInsideHexagon h g
  hbI : StrictlyInsideHexagon h b
  insideCover : ∀ z : hexBlockers P h, StrictlyInsideHexagon h z →
    z = r₁ ∨ z = r₂ ∨ z = v₁ ∨ z = v₂ ∨ z = g ∨ z = b
  allCard : ∀ d, (colourFiber colour d).card = 3

private theorem finish_twelve_two_two_structure
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 12)
    (colour : hexBlockers P h → Fin 4)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    (hinner : ∀ d : Fin 4, ∃ z : hexBlockers P h,
      StrictlyInsideHexagon h z ∧ colour z = d)
    {r₁ r₂ v₁ v₂ g : hexBlockers P h}
    (hr : r₁ ≠ r₂) (hv : v₁ ≠ v₂)
    (hred : colour r₂ = colour r₁)
    (hblue : colour v₂ = colour v₁)
    (hredBlue : colour r₁ ≠ colour v₁)
    (hredG : colour r₁ ≠ colour g)
    (hblueG : colour v₁ ≠ colour g)
    (hg : (g : Point) ∈ openSegment ℝ (r₁ : Point) (r₂ : Point))
    (hr₁I : StrictlyInsideHexagon h r₁)
    (hr₂I : StrictlyInsideHexagon h r₂)
    (hv₁I : StrictlyInsideHexagon h v₁)
    (hv₂I : StrictlyInsideHexagon h v₂)
    (hgI : StrictlyInsideHexagon h g) :
    Nonempty (TwelveTwoTwoStructure colour) := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hIcard : I.card = 6 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  obtain ⟨d, hdR, hdV, hdG⟩ :=
    exists_fourth_fin4 hredBlue hredG hblueG
  obtain ⟨b, hbI, hcb⟩ := hinner d
  have hredB : colour r₁ ≠ colour b := by simpa [hcb] using hdR.symm
  have hblueB : colour v₁ ≠ colour b := by simpa [hcb] using hdV.symm
  have hgb : colour g ≠ colour b := by simpa [hcb] using hdG.symm
  have hneColour {x y : B} (hxy : colour x ≠ colour y) : x ≠ y := by
    intro e
    exact hxy (congrArg colour e)
  have hr₁v₁ := hneColour hredBlue
  have hr₁v₂ := hneColour (by
    intro heq
    exact hredBlue (heq.trans hblue))
  have hr₂v₁ := hneColour (by
    intro heq
    exact hredBlue (hred.symm.trans heq))
  have hr₂v₂ := hneColour (by
    intro heq
    exact hredBlue (hred.symm.trans (heq.trans hblue)))
  have hr₁g := hneColour hredG
  have hr₂g := hneColour (by
    intro heq
    exact hredG (hred.symm.trans heq))
  have hv₁g := hneColour hblueG
  have hv₂g := hneColour (by
    intro heq
    exact hblueG (hblue.symm.trans heq))
  have hr₁b := hneColour hredB
  have hr₂b := hneColour (by
    intro heq
    exact hredB (hred.symm.trans heq))
  have hv₁b := hneColour hblueB
  have hv₂b := hneColour (by
    intro heq
    exact hblueB (hblue.symm.trans heq))
  have hgb' := hneColour hgb
  let e : B ↪ Point := ⟨fun z ↦ (z : Point), Subtype.val_injective⟩
  let K : Finset B := {r₁, r₂, v₁, v₂, g, b}
  let J : Finset Point := K.map e
  have hKcard : K.card = 6 := by
    simp [K, hr, hr₁v₁, hr₁v₂, hr₁g, hr₁b,
      hr₂v₁, hr₂v₂, hr₂g, hr₂b, hv, hv₁g, hv₁b,
      hv₂g, hv₂b, hgb']
  have hJcard : J.card = 6 := by
    change (K.map e).card = 6
    simpa using hKcard
  have hJsub : J ⊆ I := by
    intro x hx
    change x ∈ K.map e at hx
    rw [Finset.mem_map] at hx
    obtain ⟨z, hzK, rfl⟩ := hx
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hzK
    rcases hzK with h | h | h | h | h | h
    · subst z; exact Finset.mem_filter.mpr ⟨r₁.property, hr₁I⟩
    · subst z; exact Finset.mem_filter.mpr ⟨r₂.property, hr₂I⟩
    · subst z; exact Finset.mem_filter.mpr ⟨v₁.property, hv₁I⟩
    · subst z; exact Finset.mem_filter.mpr ⟨v₂.property, hv₂I⟩
    · subst z; exact Finset.mem_filter.mpr ⟨g.property, hgI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨b.property, hbI⟩
  have hJI : J = I :=
    Finset.eq_of_subset_of_card_le hJsub (by rw [hIcard, hJcard])
  have hcover : ∀ z : B, StrictlyInsideHexagon h z →
      z = r₁ ∨ z = r₂ ∨ z = v₁ ∨ z = v₂ ∨ z = g ∨ z = b := by
    intro z hz
    have hzI : (z : Point) ∈ I := Finset.mem_filter.mpr ⟨z.property, hz⟩
    rw [← hJI] at hzI
    change (z : Point) ∈ K.map e at hzI
    rw [Finset.mem_map] at hzI
    obtain ⟨w, hwK, hwz⟩ := hzI
    have hwzB : w = z := Subtype.ext hwz
    subst w
    simpa only [K, Finset.mem_insert, Finset.mem_singleton] using hwK
  exact ⟨{
    r₁ := r₁, r₂ := r₂, v₁ := v₁, v₂ := v₂, g := g, b := b,
    hr := hr, hv := hv, hred := hred, hblue := hblue,
    hredBlue := hredBlue, hredG := hredG, hblueG := hblueG,
    hredB := hredB, hblueB := hblueB, hgb := hgb, hg := hg,
    hr₁I := hr₁I, hr₂I := hr₂I, hv₁I := hv₁I, hv₂I := hv₂I,
    hgI := hgI, hbI := hbI, insideCover := hcover,
    allCard := fun d ↦ colourFiber_card_three_of_twelve colour
      (by simpa [B, hcard]) hle d }⟩

private theorem build_twelve_two_two_structure
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 12)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    (hinner : ∀ d : Fin 4, ∃ z : hexBlockers P h,
      StrictlyInsideHexagon h z ∧ colour z = d)
    {p q u v : hexBlockers P h}
    (hpq : p ≠ q) (huv : u ≠ v)
    (hred : colour q = colour p) (hblue : colour v = colour u)
    (hredBlue : colour p ≠ colour u)
    (hpI : StrictlyInsideHexagon h p)
    (hqI : StrictlyInsideHexagon h q)
    (huI : StrictlyInsideHexagon h u)
    (hvI : StrictlyInsideHexagon h v)
    (hredCover : ∀ z : hexBlockers P h, StrictlyInsideHexagon h z →
      colour z = colour p → z = p ∨ z = q)
    (hblueCover : ∀ z : hexBlockers P h, StrictlyInsideHexagon h z →
      colour z = colour u → z = u ∨ z = v) :
    Nonempty (TwelveTwoTwoStructure colour) := by
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  obtain ⟨s, hs⟩ := hproper p q hpq hred.symm
  obtain ⟨t, ht⟩ := hproper u v huv hblue.symm
  have hsI := openSegment_between_blockers_strictlyInside
    hfour hh hhP hside p.property q.property
      (Subtype.val_injective.ne hpq) hs
  have htI := openSegment_between_blockers_strictlyInside
    hfour hh hhP hside u.property v.property
      (Subtype.val_injective.ne huv) ht
  have hsRed : colour s ≠ colour p :=
    blocker_colour_ne hfourB hproper hpq hred.symm hs
  have htBlue : colour t ≠ colour u :=
    blocker_colour_ne hfourB hproper huv hblue.symm ht
  have hneColour {x y : B} (hxy : colour x ≠ colour y) : x ≠ y := by
    intro e
    exact hxy (congrArg colour e)
  have hpu := hneColour hredBlue
  have hpv := hneColour (by
    intro heq
    exact hredBlue (heq.trans hblue))
  have hqu := hneColour (by
    intro heq
    exact hredBlue (hred.symm.trans heq))
  have hqv := hneColour (by
    intro heq
    exact hredBlue (hred.symm.trans (heq.trans hblue)))
  by_cases hsBlue : colour s = colour u
  · by_cases htRed : colour t = colour p
    · have hsCases := hblueCover s hsI hsBlue
      have htCases := hredCover t htI htRed
      rcases hsCases with hsu | hsv <;> rcases htCases with htp | htq
      · subst s; subst t
        exact (crossed_pairs_impossible hfourB hpq hpu hpv hqu hqv huv hs ht).elim
      · subst s; subst t
        exact (crossed_pairs_impossible hfourB hpq.symm hqu hqv hpu hpv huv
          (by simpa only [openSegment_symm] using hs) ht).elim
      · subst s; subst t
        exact (crossed_pairs_impossible hfourB hpq hpv hpu hqv hqu huv.symm
          hs (by simpa only [openSegment_symm] using ht)).elim
      · subst s; subst t
        exact (crossed_pairs_impossible hfourB hpq.symm hqv hqu hpv hpu huv.symm
          (by simpa only [openSegment_symm] using hs)
          (by simpa only [openSegment_symm] using ht)).elim
    · exact finish_twelve_two_two_structure hfour hh hhP hside hcard colour hle
        hinner huv hpq hblue hred hredBlue.symm htBlue.symm (Ne.symm htRed) ht
        huI hvI hpI hqI htI
  · exact finish_twelve_two_two_structure hfour hh hhP hside hcard colour hle
      hinner hpq huv hred hblue hredBlue hsRed.symm (Ne.symm hsBlue) hs
      hpI hqI huI hvI hsI

/-- Analytic form of Lemma 8.1.  If `x` is inside `ABC`, `A` lies
strictly between `x,y`, and `u,v,w` lie on `AB,AC,BC` with `x` between
`u,v`, then a further point cannot have both of its joins to `u,v`
blocked by the six named points. -/
private theorem neighbouring_side_blockers_impossible
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y u v w X : B}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hx : StrictlyInsideTriangle (A : Point) (B₀ : Point) (C₀ : Point) x)
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hu : (u : Point) ∈ openSegment ℝ (A : Point) (B₀ : Point))
    (hv : (v : Point) ∈ openSegment ℝ (A : Point) (C₀ : Point))
    (hw : (w : Point) ∈ openSegment ℝ (B₀ : Point) (C₀ : Point))
    (hxuv : (x : Point) ∈ openSegment ℝ (u : Point) (v : Point))
    (huv : u ≠ v) (hXu : X ≠ u) (hXv : X ≠ v) (hXx : X ≠ x)
    (hcXu : colour X = colour u) (hcXv : colour X = colour v)
    (hinside : ∀ {a b z : B}, a ≠ b →
      (z : Point) ∈ openSegment ℝ (a : Point) (b : Point) →
      z = x ∨ z = y ∨ z = u ∨ z = v ∨ z = A ∨ z = w) : False := by
  have hAB : A ≠ B₀ := by
    intro e
    subst B₀
    simpa [turn] using habc
  have hAC : A ≠ C₀ := by
    intro e
    subst C₀
    simpa [turn] using habc
  have hxu : x ≠ u := by
    intro e
    subst x
    exact (Subtype.val_injective.ne huv)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hxuv)
  have hxv : x ≠ v := by
    intro e
    subst x
    exact (Subtype.val_injective.ne huv)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hxuv)
  have hblockU : ∀ {z : B},
      (z : Point) ∈ openSegment ℝ (X : Point) (u : Point) →
      z = y ∨ z = w := by
    intro z hz
    rcases hinside hXu hz with hzx | hzy | hzu | hzv | hzA | hzw
    · subst z
      have hEq := other_endpoint_eq_of_common_blocker hfour huv hXu.symm
          hxuv (by simpa only [openSegment_symm] using hz)
      exact (hXv hEq.symm).elim
    · exact Or.inl hzy
    · subst z
      have heq : (X : Point) = (u : Point) :=
        (right_mem_openSegment_iff (𝕜 := ℝ)).mp hz
      exact (hXu (Subtype.ext heq)).elim
    · subst z
      have hXline : (X : Point) ∈
          affineSpan ℝ {(u : Point), (v : Point)} :=
        right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hXu.symm)
          (by simpa only [openSegment_symm] using hz)
      have hxline := Lax56Proofs.Blockers.mem_affineSpan_pair_of_mem_openSegment hxuv
      have hxX := extra_points_eq_on_saturated_line hfour huv hxu hxv
        hXu hXv hxline hXline
      exact (hXx hxX.symm).elim
    · subst z
      exact ((saturated_left_endpoint_not_between hfour hAB hu)
        (by simpa only [openSegment_symm] using hz)).elim
    · exact Or.inr hzw
  have hblockV : ∀ {z : B},
      (z : Point) ∈ openSegment ℝ (X : Point) (v : Point) →
      z = y ∨ z = w := by
    intro z hz
    rcases hinside hXv hz with hzx | hzy | hzu | hzv | hzA | hzw
    · subst z
      have hEq := other_endpoint_eq_of_common_blocker hfour huv.symm hXv.symm
          (by simpa only [openSegment_symm] using hxuv)
          (by simpa only [openSegment_symm] using hz)
      exact (hXu hEq.symm).elim
    · exact Or.inl hzy
    · subst z
      have hXline : (X : Point) ∈
          affineSpan ℝ {(v : Point), (u : Point)} :=
        right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hXv.symm)
          (by simpa only [openSegment_symm] using hz)
      have hxline : (x : Point) ∈ affineSpan ℝ {(v : Point), (u : Point)} :=
        Lax56Proofs.Blockers.mem_affineSpan_pair_of_mem_openSegment
          (by simpa only [openSegment_symm] using hxuv)
      have hxX := extra_points_eq_on_saturated_line hfour huv.symm hxv hxu
        hXv hXu hxline hXline
      exact (hXx hxX.symm).elim
    · subst z
      have heq : (X : Point) = (v : Point) :=
        (right_mem_openSegment_iff (𝕜 := ℝ)).mp hz
      exact (hXv (Subtype.ext heq)).elim
    · subst z
      exact ((saturated_left_endpoint_not_between hfour hAC hv)
        (by simpa only [openSegment_symm] using hz)).elim
    · exact Or.inr hzw
  obtain ⟨z₁, hz₁⟩ := hproper X u hXu hcXu
  obtain ⟨z₂, hz₂⟩ := hproper X v hXv hcXv
  have hz₁c := hblockU hz₁
  have hz₂c := hblockV hz₂
  have hz₁₂ : z₁ ≠ z₂ := by
    intro e
    subst z₂
    have huv' := other_endpoint_eq_of_common_blocker hfour hXu hXv hz₁ hz₂
    exact huv huv'
  have hBCA : turn (B₀ : Point) (C₀ : Point) (A : Point) =
      turn (A : Point) (B₀ : Point) (C₀ : Point) := by
    rw [turn_rotate, turn_rotate]
  have hBCu : 0 < turn (B₀ : Point) (C₀ : Point) (u : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hu
    · rw [hBCA]; exact habc.le
    · simp
    · left; rw [hBCA]; exact habc
  have hBCv : 0 < turn (B₀ : Point) (C₀ : Point) (v : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hv
    · rw [hBCA]; exact habc.le
    · simp
    · left; rw [hBCA]; exact habc
  have hBCw : turn (B₀ : Point) (C₀ : Point) (w : Point) = 0 :=
    turn_eq_zero_of_between hw
  have hBCxlt : turn (B₀ : Point) (C₀ : Point) (x : Point) <
      turn (B₀ : Point) (C₀ : Point) (A : Point) := by
    have hsum := turn_triangle_decompose
      (A : Point) (B₀ : Point) (C₀ : Point) (x : Point)
    rw [hBCA]
    linarith [hx.1, hx.2.2]
  have hBCult : turn (B₀ : Point) (C₀ : Point) (u : Point) <
      turn (B₀ : Point) (C₀ : Point) (A : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hu
    simp only [turn_self_left] at heq
    rw [hBCA] at heq
    nlinarith [mul_pos ht0 habc]
  have hBCvlt : turn (B₀ : Point) (C₀ : Point) (v : Point) <
      turn (B₀ : Point) (C₀ : Point) (A : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hv
    simp only [turn_self_right] at heq
    rw [hBCA] at heq
    nlinarith [mul_pos ht0 habc]
  have hBCy : turn (B₀ : Point) (C₀ : Point) (A : Point) <
      turn (B₀ : Point) (C₀ : Point) (y : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hA
    nlinarith [mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hBCxlt)]
  rcases hz₁c with hz₁y | hz₁w <;> rcases hz₂c with hz₂y | hz₂w
  · exact (hz₁₂ (hz₁y.trans hz₂y.symm)).elim
  · have hz₁' : (y : Point) ∈ openSegment ℝ (X : Point) (u : Point) := by
      simpa only [hz₁y] using hz₁
    have hz₂' : (w : Point) ∈ openSegment ℝ (X : Point) (v : Point) := by
      simpa only [hz₂w] using hz₂
    have hXneg := turn_neg_of_between_of_turn_eq_zero_of_pos
      (a := (B₀ : Point)) (b := (C₀ : Point))
      (x := (v : Point)) (y := (X : Point)) (z := (w : Point))
      (by simpa only [openSegment_symm] using hz₂') hBCw hBCv
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point))
        (by simpa only [openSegment_symm] using hz₁')
    nlinarith [hBCult, hBCy]
  · have hz₁' : (w : Point) ∈ openSegment ℝ (X : Point) (u : Point) := by
      simpa only [hz₁w] using hz₁
    have hz₂' : (y : Point) ∈ openSegment ℝ (X : Point) (v : Point) := by
      simpa only [hz₂y] using hz₂
    have hXneg := turn_neg_of_between_of_turn_eq_zero_of_pos
      (a := (B₀ : Point)) (b := (C₀ : Point))
      (x := (u : Point)) (y := (X : Point)) (z := (w : Point))
      (by simpa only [openSegment_symm] using hz₁') hBCw hBCu
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point))
        (by simpa only [openSegment_symm] using hz₂')
    nlinarith [hBCvlt, hBCy]
  · exact (hz₁₂ (hz₁w.trans hz₂w.symm)).elim

/-- Analytic form of Lemma 8.2.  In the non-neighbouring side pattern the
only possible blocker of `xR` is `w`; the oriented side `CA` then puts both
`y,R` strictly on its negative side while every possible blocker is
nonnegative. -/
private theorem nonneighboring_side_visible_pair
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y u v w R : B}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hx : StrictlyInsideTriangle (A : Point) (B₀ : Point) (C₀ : Point) x)
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hu : (u : Point) ∈ openSegment ℝ (B₀ : Point) (C₀ : Point))
    (hv : (v : Point) ∈ openSegment ℝ (A : Point) (B₀ : Point))
    (hw : (w : Point) ∈ openSegment ℝ (A : Point) (C₀ : Point))
    (hxuv : (x : Point) ∈ openSegment ℝ (u : Point) (v : Point))
    (huv : u ≠ v) (hRx : R ≠ x) (hRy : R ≠ y)
    (hRu : R ≠ u) (hRv : R ≠ v)
    (hcxR : colour x = colour R) (hcyx : colour y = colour x)
    (hinside : ∀ {a b z : B}, a ≠ b →
      (z : Point) ∈ openSegment ℝ (a : Point) (b : Point) →
      z = x ∨ z = y ∨ z = u ∨ z = v ∨ z = A ∨ z = w) : False := by
  have hxy : x ≠ y := by
    intro e
    subst y
    have hAx : (A : Point) ≠ (x : Point) :=
      (strictlyInsideTriangle_ne_vertices hx).1.symm
    exact hAx (by simpa using hA)
  have hxu : x ≠ u := by
    intro e
    subst x
    exact (Subtype.val_injective.ne huv)
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hxuv)
  have hxv : x ≠ v := by
    intro e
    subst x
    exact (Subtype.val_injective.ne huv)
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hxuv)
  obtain ⟨z, hz⟩ := hproper x R hRx.symm hcxR
  have hzColour : colour z ≠ colour x :=
    blocker_colour_ne hfour hproper hRx.symm hcxR hz
  have hzw : z = w := by
    rcases hinside hRx.symm hz with hzx | hzy | hzu | hzv | hzA | hzw
    · subst z
      have heq : (x : Point) = (R : Point) :=
        (left_mem_openSegment_iff (𝕜 := ℝ)).mp hz
      exact (hRx (Subtype.ext heq.symm)).elim
    · exact (hzColour ((congrArg colour hzy).trans hcyx)).elim
    · subst z
      exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
        hfour hRv.symm huv.symm hRx.symm
        (by simpa only [openSegment_symm] using hxuv) hz).elim
    · subst z
      exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
        hfour hRu.symm huv hRx.symm hxuv hz).elim
    · subst z
      have hyR := other_endpoint_eq_of_common_blocker hfour hxy hRx.symm hA hz
      exact (hRy hyR.symm).elim
    · exact hzw
  have hwxR : (w : Point) ∈ openSegment ℝ (x : Point) (R : Point) := by
    simpa only [hzw] using hz
  have hCAx : 0 < turn (C₀ : Point) (A : Point) (x : Point) := hx.2.2
  have hCAw : turn (C₀ : Point) (A : Point) (w : Point) = 0 :=
    turn_eq_zero_of_between (by simpa only [openSegment_symm] using hw)
  have hCAy : turn (C₀ : Point) (A : Point) (y : Point) < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hA (by simp) hCAx
  have hCAR : turn (C₀ : Point) (A : Point) (R : Point) < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hwxR hCAw hCAx
  have hCAB : turn (C₀ : Point) (A : Point) (B₀ : Point) =
      turn (A : Point) (B₀ : Point) (C₀ : Point) := by
    rw [turn_rotate, turn_rotate]
  have hCAu : 0 < turn (C₀ : Point) (A : Point) (u : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hu
    · rw [hCAB]; exact habc.le
    · simp
    · left; rw [hCAB]; exact habc
  have hCAv : 0 < turn (C₀ : Point) (A : Point) (v : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hv
    · simp
    · rw [hCAB]; exact habc.le
    · right; rw [hCAB]; exact habc
  obtain ⟨z', hz'⟩ := hproper y R hRy.symm (hcyx.trans hcxR)
  have hz'neg := turn_neg_of_mem_openSegment hz' hCAy hCAR
  rcases hinside hRy.symm hz' with hz'x | hz'y | hz'u | hz'v | hz'A | hz'w
  · rw [hz'x] at hz'neg; linarith
  · have hyR : (y : Point) = (R : Point) := by
      apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
      simpa only [hz'y] using hz'
    exact (hRy (Subtype.ext hyR.symm)).elim
  · rw [hz'u] at hz'neg; linarith
  · rw [hz'v] at hz'neg; linarith
  · rw [hz'A] at hz'neg; simp at hz'neg
  · rw [hz'w, hCAw] at hz'neg
    exact (lt_irrefl 0 hz'neg).elim

/-- The support-line core of the preceding lemma.  This symmetric form is
used for either of the two sides incident with `A`. -/
private theorem nonneighboring_support_visible_pair
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A x y u v w R : B} {L₀ L₁ : Point}
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hxuv : (x : Point) ∈ openSegment ℝ (u : Point) (v : Point))
    (huv : u ≠ v) (hRx : R ≠ x) (hRy : R ≠ y)
    (hRu : R ≠ u) (hRv : R ≠ v)
    (hcxR : colour x = colour R) (hcyx : colour y = colour x)
    (hLx : 0 < turn L₀ L₁ x) (hLA : turn L₀ L₁ A = 0)
    (hLw : turn L₀ L₁ w = 0)
    (hLu : 0 < turn L₀ L₁ u) (hLv : 0 < turn L₀ L₁ v)
    (hinside : ∀ {a b z : B}, a ≠ b →
      (z : Point) ∈ openSegment ℝ (a : Point) (b : Point) →
      z = x ∨ z = y ∨ z = u ∨ z = v ∨ z = A ∨ z = w) : False := by
  have hxy : x ≠ y := by
    intro e
    subst y
    have hAx : (A : Point) ≠ (x : Point) := by
      intro hEq
      rw [hEq] at hLA
      linarith
    exact hAx (by simpa using hA)
  obtain ⟨z, hz⟩ := hproper x R hRx.symm hcxR
  have hzColour : colour z ≠ colour x :=
    blocker_colour_ne hfour hproper hRx.symm hcxR hz
  have hzw : z = w := by
    rcases hinside hRx.symm hz with hzx | hzy | hzu | hzv | hzA | hzw
    · subst z
      have heq : (x : Point) = (R : Point) :=
        (left_mem_openSegment_iff (𝕜 := ℝ)).mp hz
      exact (hRx (Subtype.ext heq.symm)).elim
    · exact (hzColour ((congrArg colour hzy).trans hcyx)).elim
    · subst z
      exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
        hfour hRv.symm huv.symm hRx.symm
        (by simpa only [openSegment_symm] using hxuv) hz).elim
    · subst z
      exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
        hfour hRu.symm huv hRx.symm hxuv hz).elim
    · subst z
      have hyR := other_endpoint_eq_of_common_blocker hfour hxy hRx.symm hA hz
      exact (hRy hyR.symm).elim
    · exact hzw
  have hwxR : (w : Point) ∈ openSegment ℝ (x : Point) (R : Point) := by
    simpa only [hzw] using hz
  have hLy : turn L₀ L₁ y < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hA hLA hLx
  have hLR : turn L₀ L₁ R < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hwxR hLw hLx
  obtain ⟨z', hz'⟩ := hproper y R hRy.symm (hcyx.trans hcxR)
  have hz'neg := turn_neg_of_mem_openSegment hz' hLy hLR
  rcases hinside hRy.symm hz' with hz'x | hz'y | hz'u | hz'v | hz'A | hz'w
  · rw [hz'x] at hz'neg; linarith
  · have hyR : (y : Point) = (R : Point) := by
      apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
      simpa only [hz'y] using hz'
    exact (hRy (Subtype.ext hyR.symm)).elim
  · rw [hz'u] at hz'neg; linarith
  · rw [hz'v] at hz'neg; linarith
  · rw [hz'A, hLA] at hz'neg
    exact (lt_irrefl 0 hz'neg).elim
  · rw [hz'w, hLw] at hz'neg
    exact (lt_irrefl 0 hz'neg).elim

/-- Three distinct objects covered by three distinct labels occur in one of
the six possible orders. -/
private theorem three_cover_permutations
    {X : Type*} {s₀ s₁ s₂ a b c : X}
    (hs₀₁ : s₀ ≠ s₁) (hs₀₂ : s₀ ≠ s₂) (hs₁₂ : s₁ ≠ s₂)
    (h₀ : s₀ = a ∨ s₀ = b ∨ s₀ = c)
    (h₁ : s₁ = a ∨ s₁ = b ∨ s₁ = c)
    (h₂ : s₂ = a ∨ s₂ = b ∨ s₂ = c) :
    (s₀ = a ∧ s₁ = b ∧ s₂ = c) ∨
    (s₀ = a ∧ s₁ = c ∧ s₂ = b) ∨
    (s₀ = b ∧ s₁ = a ∧ s₂ = c) ∨
    (s₀ = b ∧ s₁ = c ∧ s₂ = a) ∨
    (s₀ = c ∧ s₁ = a ∧ s₂ = b) ∨
    (s₀ = c ∧ s₁ = b ∧ s₂ = a) := by
  rcases h₀ with h₀ | h₀ | h₀ <;>
    rcases h₁ with h₁ | h₁ | h₁ <;>
    rcases h₂ with h₂ | h₂ | h₂ <;>
    simp_all

/-- In the strict-interior branch, the blocker of the doubled-colour pair
on two different sides is the red point `x`.  The other red point is
outside the triangle, the vertex `A` is exposed, and the third side point
is excluded by a supporting determinant. -/
private theorem doubled_side_pair_blocked_by_x
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y v₁ v₂ b : B} {L₀ L₁ : Point}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hyOut : (y : Point) ∉ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (hv₁Hull : (v₁ : Point) ∈ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (hv₂Hull : (v₂ : Point) ∈ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (hv₁A : v₁ ≠ A) (hv₁B : v₁ ≠ B₀) (hv₁C : v₁ ≠ C₀)
    (hv₁v₂ : v₁ ≠ v₂) (hcv : colour v₁ = colour v₂)
    (hb₀ : turn L₀ L₁ b = 0)
    (hv₁pos : 0 < turn L₀ L₁ v₁)
    (hv₂pos : 0 < turn L₀ L₁ v₂)
    (hinside : ∀ {a c z : B}, a ≠ c →
      (z : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      z = x ∨ z = y ∨ z = v₁ ∨ z = v₂ ∨ z = A ∨ z = b) :
    (x : Point) ∈ openSegment ℝ (v₁ : Point) (v₂ : Point) := by
  obtain ⟨z, hz⟩ := hproper v₁ v₂ hv₁v₂ hcv
  rcases hinside hv₁v₂ hz with hzx | hzy | hzv₁ | hzv₂ | hzA | hzb
  · simpa only [hzx] using hz
  · apply (hyOut ?_).elim
    rw [← hzy]
    exact openSegment_mem_triangleHull_of_mem hv₁Hull hv₂Hull hz
  · have heq : (v₁ : Point) = (v₂ : Point) := by
      apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
      simpa only [hzv₁] using hz
    exact (Subtype.val_injective.ne hv₁v₂ heq).elim
  · have heq : (v₁ : Point) = (v₂ : Point) := by
      apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
      simpa only [hzv₂] using hz
    exact (Subtype.val_injective.ne hv₁v₂ heq).elim
  · exact (triangle_vertex_not_between_hull_points hfour habc
      hv₁Hull hv₂Hull (by simpa only [hzA] using hz)
      hv₁A hv₁B hv₁C).elim
  · have hbpos : 0 < turn L₀ L₁ b := by
      rw [← hzb]
      exact edgeTurn_pos_of_mem_openSegment hz hv₁pos.le hv₂pos.le
        (Or.inl hv₁pos)
    linarith

/-- The strict-interior subcase in which the two doubled-colour points lie
on the two sides incident with the green vertex. -/
private theorem strict_neighbor_configuration_impossible
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y u v b : B}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hx : StrictlyInsideTriangle (A : Point) (B₀ : Point) (C₀ : Point) x)
    (hyOut : (y : Point) ∉ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hu : (u : Point) ∈ openSegment ℝ (A : Point) (B₀ : Point))
    (hv : (v : Point) ∈ openSegment ℝ (A : Point) (C₀ : Point))
    (hb : (b : Point) ∈ openSegment ℝ (B₀ : Point) (C₀ : Point))
    (huv : u ≠ v) (hcy : colour y = colour x)
    (hcv : colour v = colour u) (hxuColour : colour x ≠ colour u)
    (hinside : ∀ {a c z : B}, a ≠ c →
      (z : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      z = x ∨ z = y ∨ z = u ∨ z = v ∨ z = A ∨ z = b)
    (allCard : ∀ d, (colourFiber colour d).card = 3) : False := by
  have huHull : (u : Point) ∈ triangleHull (A : Point) (B₀ : Point) (C₀ : Point) :=
    openSegment_subset_triangleHull_left hu
  have hvHull : (v : Point) ∈ triangleHull (A : Point) (B₀ : Point) (C₀ : Point) := by
    have h := openSegment_subset_triangleHull_left (c := (B₀ : Point)) hv
    rw [triangleHull_swap_last] at h
    exact h
  have huA : u ≠ A := by
    intro e; subst u
    exact (Subtype.val_injective.ne (by
      intro h; subst B₀; simpa [turn] using habc))
      ((left_mem_openSegment_iff (𝕜 := ℝ)).mp hu)
  have huB : u ≠ B₀ := by
    intro e; subst u
    exact (Subtype.val_injective.ne (by
      intro h; subst B₀; simpa [turn] using habc))
      ((right_mem_openSegment_iff (𝕜 := ℝ)).mp hu)
  have huC : u ≠ C₀ := by
    intro e
    have hu0 := turn_eq_zero_of_between hu
    rw [e] at hu0
    linarith
  have hBCA : turn (B₀ : Point) (C₀ : Point) (A : Point) =
      turn (A : Point) (B₀ : Point) (C₀ : Point) := by
    rw [turn_rotate, turn_rotate]
  have hBCu : 0 < turn (B₀ : Point) (C₀ : Point) (u : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hu
    · rw [hBCA]; exact habc.le
    · simp
    · left; rw [hBCA]; exact habc
  have hBCv : 0 < turn (B₀ : Point) (C₀ : Point) (v : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hv
    · rw [hBCA]; exact habc.le
    · simp
    · left; rw [hBCA]; exact habc
  have hb0 : turn (B₀ : Point) (C₀ : Point) (b : Point) = 0 :=
    turn_eq_zero_of_between hb
  have hxuv := doubled_side_pair_blocked_by_x hfour colour hproper habc hyOut
    huHull hvHull huA huB huC huv hcv.symm hb0 hBCu hBCv hinside
  obtain ⟨X, hXu, hXv, hcX, -⟩ :=
    exists_third_of_colourFiber_card_three (allCard (colour u)) rfl hcv huv
  have hXx : X ≠ x := by
    intro e
    exact hxuColour ((congrArg colour e).symm.trans hcX)
  exact neighbouring_side_blockers_impossible hfour colour hproper habc hx hA
    hu hv hb hxuv huv hXu hXv hXx hcX (hcX.trans hcv.symm) hinside

/-- Support-line version of the strict-interior non-neighbouring subcase.
It is invariant under reflection of the two sides incident with `A`. -/
private theorem strict_nonneighbor_configuration_impossible
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y u v b : B} {L₀ L₁ : Point}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hyOut : (y : Point) ∉ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (huHull : (u : Point) ∈ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (hvHull : (v : Point) ∈ triangleHull (A : Point) (B₀ : Point) (C₀ : Point))
    (huA : u ≠ A) (huB : u ≠ B₀) (huC : u ≠ C₀)
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (huv : u ≠ v) (hcy : colour y = colour x)
    (hcv : colour v = colour u) (hxuColour : colour x ≠ colour u)
    (hLx : 0 < turn L₀ L₁ x) (hLA : turn L₀ L₁ A = 0)
    (hLb : turn L₀ L₁ b = 0)
    (hLu : 0 < turn L₀ L₁ u) (hLv : 0 < turn L₀ L₁ v)
    (hinside : ∀ {a c z : B}, a ≠ c →
      (z : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      z = x ∨ z = y ∨ z = u ∨ z = v ∨ z = A ∨ z = b)
    (allCard : ∀ d, (colourFiber colour d).card = 3) : False := by
  have hxuv := doubled_side_pair_blocked_by_x hfour colour hproper habc hyOut
    huHull hvHull huA huB huC huv hcv.symm hLb hLu hLv hinside
  obtain ⟨R, hRx, hRy, hcR, -⟩ :=
    exists_third_of_colourFiber_card_three (allCard (colour x)) rfl hcy
      (by
        intro e
        subst y
        have hAx : (A : Point) ≠ (x : Point) := by
          intro hEq; rw [hEq] at hLA; linarith
        exact hAx (by simpa using hA))
  have hRu : R ≠ u := by
    intro e
    exact hxuColour (hcR.symm.trans (congrArg colour e))
  have hRv : R ≠ v := by
    intro e
    exact hxuColour (hcR.symm.trans ((congrArg colour e).trans hcv))
  exact nonneighboring_support_visible_pair hfour colour hproper hA hxuv huv
    hRx hRy hRu hRv hcR.symm hcy hLx hLA hLb hLu hLv hinside

/-- The complete strict-interior half of the `2,2,1,1` case. -/
private theorem no_twelve_two_two_strict_green_core
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {x y v₁ v₂ A b G₁ G₂ : B}
    (habc : 0 < turn (A : Point) (G₁ : Point) (G₂ : Point))
    (hx : StrictlyInsideTriangle (A : Point) (G₁ : Point) (G₂ : Point) x)
    (hyOut : (y : Point) ∉ triangleHull (A : Point) (G₁ : Point) (G₂ : Point))
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hG₁A : G₁ ≠ A) (hG₂A : G₂ ≠ A) (hG₁G₂ : G₁ ≠ G₂)
    (hcG₁ : colour G₁ = colour A) (hcG₂ : colour G₂ = colour A)
    (hv₁v₂ : v₁ ≠ v₂) (hcv₂ : colour v₂ = colour v₁)
    (hcy : colour y = colour x) (hxv₁Colour : colour x ≠ colour v₁)
    (hv₁AColour : colour v₁ ≠ colour A)
    (hinside : ∀ {a c z : B}, a ≠ c →
      (z : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      z = x ∨ z = y ∨ z = v₁ ∨ z = v₂ ∨ z = A ∨ z = b)
    (allCard : ∀ d, (colourFiber colour d).card = 3) : False := by
  have hAG₁ : A ≠ G₁ := hG₁A.symm
  have hG₂A' : G₂ ≠ A := hG₂A
  obtain ⟨s₀, hs₀⟩ := hproper A G₁ hAG₁ hcG₁.symm
  obtain ⟨s₁, hs₁⟩ := hproper G₁ G₂ hG₁G₂ (hcG₁.trans hcG₂.symm)
  obtain ⟨s₂, hs₂⟩ := hproper G₂ A hG₂A' hcG₂
  have hs₀Hull : (s₀ : Point) ∈ triangleHull (A : Point) (G₁ : Point) (G₂ : Point) :=
    openSegment_subset_triangleHull_left hs₀
  have hs₁Hull : (s₁ : Point) ∈ triangleHull (A : Point) (G₁ : Point) (G₂ : Point) := by
    have h := openSegment_subset_triangleHull_left (c := (A : Point)) hs₁
    rw [triangleHull_rotate (A : Point) (G₁ : Point) (G₂ : Point)] at h
    exact h
  have hs₂Hull : (s₂ : Point) ∈ triangleHull (A : Point) (G₁ : Point) (G₂ : Point) := by
    have h := openSegment_subset_triangleHull_left (c := (G₁ : Point)) hs₂
    rw [triangleHull_rotate (G₁ : Point) (G₂ : Point) (A : Point),
      triangleHull_rotate (A : Point) (G₁ : Point) (G₂ : Point)] at h
    exact h
  have hs₀case : s₀ = v₁ ∨ s₀ = v₂ ∨ s₀ = b := by
    rcases hinside hAG₁ hs₀ with h | h | h | h | h | h
    · subst s₀
      have hz := turn_eq_zero_of_between hs₀
      linarith [hx.1]
    · exact (hyOut (h ▸ hs₀Hull)).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst s₀
      have heq : (A : Point) = (G₁ : Point) :=
        (left_mem_openSegment_iff (𝕜 := ℝ)).mp hs₀
      exact (hG₁A (Subtype.ext heq.symm)).elim
    · exact Or.inr (Or.inr h)
  have hs₁case : s₁ = v₁ ∨ s₁ = v₂ ∨ s₁ = b := by
    rcases hinside hG₁G₂ hs₁ with h | h | h | h | h | h
    · subst s₁
      have hz := turn_eq_zero_of_between hs₁
      linarith [hx.2.1]
    · exact (hyOut (h ▸ hs₁Hull)).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst s₁
      have hz := turn_eq_zero_of_between hs₁
      have hrot : turn (G₁ : Point) (G₂ : Point) (A : Point) =
          turn (A : Point) (G₁ : Point) (G₂ : Point) := by
        rw [turn_rotate, turn_rotate]
      linarith
    · exact Or.inr (Or.inr h)
  have hs₂case : s₂ = v₁ ∨ s₂ = v₂ ∨ s₂ = b := by
    rcases hinside hG₂A' hs₂ with h | h | h | h | h | h
    · subst s₂
      have hz := turn_eq_zero_of_between hs₂
      linarith [hx.2.2]
    · exact (hyOut (h ▸ hs₂Hull)).elim
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst s₂
      have heq : (G₂ : Point) = (A : Point) :=
        (right_mem_openSegment_iff (𝕜 := ℝ)).mp hs₂
      exact (hG₂A (Subtype.ext heq)).elim
    · exact Or.inr (Or.inr h)
  have hs₀₁ : s₀ ≠ s₁ := by
    intro e
    subst s₁
    have hEq := other_endpoint_eq_of_common_blocker hfour hG₁A hG₁G₂
      (by simpa only [openSegment_symm] using hs₀) hs₁
    exact hG₂A hEq.symm
  have hs₁₂ : s₁ ≠ s₂ := by
    intro e
    subst s₂
    have hEq := other_endpoint_eq_of_common_blocker hfour hG₁G₂.symm hG₂A'
      (by simpa only [openSegment_symm] using hs₁) hs₂
    exact hG₁A hEq
  have hs₀₂ : s₀ ≠ s₂ := by
    intro e
    subst s₂
    have hEq := other_endpoint_eq_of_common_blocker hfour hAG₁ hG₂A'.symm
      hs₀ (by simpa only [openSegment_symm] using hs₂)
    exact hG₁G₂ hEq
  have hperm := three_cover_permutations hs₀₁ hs₀₂ hs₁₂
    hs₀case hs₁case hs₂case
  have hneColour {p q : B} (hpq : colour p ≠ colour q) : p ≠ q := by
    intro e; exact hpq (congrArg colour e)
  have hv₁A := hneColour hv₁AColour
  have hv₁G₁ := hneColour (by
    intro e; exact hv₁AColour (e.trans hcG₁))
  have hv₁G₂ := hneColour (by
    intro e; exact hv₁AColour (e.trans hcG₂))
  have hv₂A := hneColour (by
    intro e; exact hv₁AColour (hcv₂.symm.trans e))
  have hv₂G₁ := hneColour (by
    intro e; exact hv₁AColour (hcv₂.symm.trans (e.trans hcG₁)))
  have hv₂G₂ := hneColour (by
    intro e; exact hv₁AColour (hcv₂.symm.trans (e.trans hcG₂)))
  have hxv₂Colour : colour x ≠ colour v₂ := by
    intro e; exact hxv₁Colour (e.trans hcv₂)
  have hinsideSwap : ∀ {a c z : B}, a ≠ c →
      (z : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      z = x ∨ z = y ∨ z = v₂ ∨ z = v₁ ∨ z = A ∨ z = b := by
    intro a c z hac hz
    rcases hinside hac hz with h | h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hABSigns : ∀ {z : B},
      (z : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) →
      turn (A : Point) (G₁ : Point) z = 0 ∧
      0 < turn (G₁ : Point) (G₂ : Point) z ∧
      0 < turn (G₂ : Point) (A : Point) z := by
    intro z hz
    refine ⟨turn_eq_zero_of_between hz, ?_, ?_⟩
    · apply edgeTurn_pos_of_mem_openSegment hz
      · simpa only [turn_rotate, turn_rotate] using habc.le
      · simp
      · left; simpa only [turn_rotate, turn_rotate] using habc
    · apply edgeTurn_pos_of_mem_openSegment hz
      · simp
      · simpa only [turn_rotate, turn_rotate] using habc.le
      · right; simpa only [turn_rotate, turn_rotate] using habc
  have hBCSigns : ∀ {z : B},
      (z : Point) ∈ openSegment ℝ (G₁ : Point) (G₂ : Point) →
      0 < turn (A : Point) (G₁ : Point) z ∧
      turn (G₁ : Point) (G₂ : Point) z = 0 ∧
      0 < turn (G₂ : Point) (A : Point) z := by
    intro z hz
    refine ⟨turn_pos_of_mem_next_side habc hz, turn_eq_zero_of_between hz, ?_⟩
    apply edgeTurn_pos_of_mem_openSegment hz
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hCASigns : ∀ {z : B},
      (z : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point) →
      0 < turn (A : Point) (G₁ : Point) z ∧
      0 < turn (G₁ : Point) (G₂ : Point) z ∧
      turn (G₂ : Point) (A : Point) z = 0 := by
    intro z hz
    refine ⟨?_, ?_, turn_eq_zero_of_between hz⟩
    · apply edgeTurn_pos_of_mem_openSegment hz habc.le (by simp)
      exact Or.inl habc
    · apply turn_pos_of_mem_next_side
      · simpa only [turn_rotate, turn_rotate] using habc
      · exact hz
  rcases hperm with h | h | h | h | h | h
  · rcases h with ⟨h₀, h₁, h₂⟩
    have hv₁AB : (v₁ : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) := by simpa only [h₀] using hs₀
    have hv₂BC : (v₂ : Point) ∈ openSegment ℝ (G₁ : Point) (G₂ : Point) := by simpa only [h₁] using hs₁
    have hbCA : (b : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point) := by simpa only [h₂] using hs₂
    exact strict_nonneighbor_configuration_impossible hfour colour hproper habc
      hyOut (h₁ ▸ hs₁Hull) (h₀ ▸ hs₀Hull)
      hv₂A hv₂G₁ hv₂G₂ hA hv₁v₂.symm hcy hcv₂.symm
      hxv₂Colour hx.2.2 (by simp) (hCASigns hbCA).2.2
      (hBCSigns hv₂BC).2.2 (hABSigns hv₁AB).2.2 hinsideSwap allCard
  · rcases h with ⟨h₀, h₁, h₂⟩
    exact strict_neighbor_configuration_impossible hfour colour hproper habc hx hyOut hA
      (by simpa only [h₀] using hs₀)
      (by simpa only [openSegment_symm, h₂] using hs₂)
      (by simpa only [h₁] using hs₁) hv₁v₂ hcy hcv₂
      hxv₁Colour hinside allCard
  · rcases h with ⟨h₀, h₁, h₂⟩
    have hv₂AB : (v₂ : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) := by simpa only [h₀] using hs₀
    have hv₁BC : (v₁ : Point) ∈ openSegment ℝ (G₁ : Point) (G₂ : Point) := by simpa only [h₁] using hs₁
    have hbCA : (b : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point) := by simpa only [h₂] using hs₂
    exact strict_nonneighbor_configuration_impossible hfour colour hproper habc
      hyOut (h₁ ▸ hs₁Hull) (h₀ ▸ hs₀Hull)
      hv₁A hv₁G₁ hv₁G₂ hA hv₁v₂ hcy hcv₂
      hxv₁Colour hx.2.2 (by simp) (hCASigns hbCA).2.2
      (hBCSigns hv₁BC).2.2 (hABSigns hv₂AB).2.2 hinside allCard
  · rcases h with ⟨h₀, h₁, h₂⟩
    exact strict_neighbor_configuration_impossible hfour colour hproper habc hx hyOut hA
      (by simpa only [h₀] using hs₀)
      (by simpa only [openSegment_symm, h₂] using hs₂)
      (by simpa only [h₁] using hs₁) hv₁v₂.symm hcy hcv₂.symm
      hxv₂Colour hinsideSwap allCard
  · rcases h with ⟨h₀, h₁, h₂⟩
    have hv₁BC : (v₁ : Point) ∈ openSegment ℝ (G₁ : Point) (G₂ : Point) := by simpa only [h₁] using hs₁
    have hv₂CA : (v₂ : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point) := by simpa only [h₂] using hs₂
    have hbAB : (b : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) := by simpa only [h₀] using hs₀
    exact strict_nonneighbor_configuration_impossible hfour colour hproper habc
      hyOut (h₁ ▸ hs₁Hull) (h₂ ▸ hs₂Hull)
      hv₁A hv₁G₁ hv₁G₂ hA hv₁v₂ hcy hcv₂
      hxv₁Colour hx.1 (by simp) (hABSigns hbAB).1
      (hBCSigns hv₁BC).1 (hCASigns hv₂CA).1 hinside allCard
  · rcases h with ⟨h₀, h₁, h₂⟩
    have hv₂BC : (v₂ : Point) ∈ openSegment ℝ (G₁ : Point) (G₂ : Point) := by simpa only [h₁] using hs₁
    have hv₁CA : (v₁ : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point) := by simpa only [h₂] using hs₂
    have hbAB : (b : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) := by simpa only [h₀] using hs₀
    exact strict_nonneighbor_configuration_impossible hfour colour hproper habc
      hyOut (h₁ ▸ hs₁Hull) (h₂ ▸ hs₂Hull)
      hv₂A hv₂G₁ hv₂G₂ hA hv₁v₂.symm hcy hcv₂.symm
      hxv₂Colour hx.1 (by simp) (hABSigns hbAB).1
      (hBCSigns hv₂BC).1 (hCASigns hv₁CA).1 hinsideSwap allCard

/-- Analytic form of Lemma 8.3.  The proof uses the chord `zp` as a
supporting crosscut; it avoids the coordinate denominators in the paper's
barycentric calculation. -/
private theorem double_triangle_visibility_impossible
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y p q z R : B}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hxSide : (x : Point) ∈ openSegment ℝ (B₀ : Point) (C₀ : Point))
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hpSide : (p : Point) ∈ openSegment ℝ (A : Point) (C₀ : Point))
    (hzSide : (z : Point) ∈ openSegment ℝ (A : Point) (B₀ : Point))
    (hzq : z ≠ q) (hRz : R ≠ z) (hRy : R ≠ y) (hRx : R ≠ x)
    (hincidence :
      ((p : Point) ∈ openSegment ℝ (x : Point) (R : Point) ∧
        (q : Point) ∈ openSegment ℝ (y : Point) (R : Point)) ∨
      ((p : Point) ∈ openSegment ℝ (y : Point) (R : Point) ∧
        (q : Point) ∈ openSegment ℝ (x : Point) (R : Point)))
    (hcolour : colour z = colour p ∨ colour z = colour q)
    (hinside : ∀ {a c w : B}, a ≠ c →
      (w : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      w = x ∨ w = y ∨ w = A ∨ w = p ∨ w = q ∨ w = z) : False := by
  have hAB : A ≠ B₀ := by
    intro e; subst B₀; simpa [turn] using habc
  have hpCA : (p : Point) ∈ openSegment ℝ (C₀ : Point) (A : Point) := by
    simpa only [openSegment_symm] using hpSide
  have hsideNe := triangle_side_points_pairwise habc hzSide hxSide hpCA
  have hzp : z ≠ p := by
    intro e
    exact hsideNe.2.2 (congrArg Subtype.val e).symm
  have hABx : 0 < turn (A : Point) (B₀ : Point) (x : Point) :=
    turn_pos_of_mem_next_side habc hxSide
  have hBCx : turn (B₀ : Point) (C₀ : Point) (x : Point) = 0 :=
    turn_eq_zero_of_between hxSide
  have hCAx : 0 < turn (C₀ : Point) (A : Point) (x : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hxSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hABz : turn (A : Point) (B₀ : Point) (z : Point) = 0 :=
    turn_eq_zero_of_between hzSide
  have hBCz : 0 < turn (B₀ : Point) (C₀ : Point) (z : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hzSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hCAz : 0 < turn (C₀ : Point) (A : Point) (z : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hzSide
    · simp
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · right; simpa only [turn_rotate, turn_rotate] using habc
  have hABp : 0 < turn (A : Point) (B₀ : Point) (p : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hpSide (by simp) habc.le
    exact Or.inr habc
  have hBCp : 0 < turn (B₀ : Point) (C₀ : Point) (p : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hpSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hCAp : turn (C₀ : Point) (A : Point) (p : Point) = 0 :=
    turn_eq_zero_of_between hpCA
  have hzpx : turn (z : Point) (p : Point) (x : Point) < 0 := by
    have hthree := turn_side_points_pos habc hzSide hxSide hpCA
    rw [turn_swap_last]
    linarith
  have hzpA : 0 < turn (z : Point) (p : Point) (A : Point) := by
    have hACz : turn (A : Point) (C₀ : Point) (z : Point) < 0 := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (A : Point)) (b := (C₀ : Point)) hzSide
      simp only [turn_self_left] at heq
      have hACB : turn (A : Point) (C₀ : Point) (B₀ : Point) < 0 := by
        rw [turn_swap_last]
        linarith
      nlinarith [mul_neg_of_pos_of_neg ht0 hACB]
    have hAzC : 0 < turn (A : Point) (z : Point) (C₀ : Point) := by
      rw [turn_swap_last]
      linarith
    have hAzp : 0 < turn (A : Point) (z : Point) (p : Point) :=
      edgeTurn_pos_of_mem_openSegment hpSide (by simp) hAzC.le (Or.inr hAzC)
    simpa only [turn_rotate] using hAzp
  have hzpy : 0 < turn (z : Point) (p : Point) (y : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (z : Point)) (b := (p : Point)) hA
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hzpx]
  have hABy : turn (A : Point) (B₀ : Point) (y : Point) < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hA (by simp) hABx
  have hCAy : turn (C₀ : Point) (A : Point) (y : Point) < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hA (by simp) hCAx
  have hBCy : 0 < turn (B₀ : Point) (C₀ : Point) (y : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hA
    rw [hBCx] at heq
    have hBCA : turn (B₀ : Point) (C₀ : Point) (A : Point) =
        turn (A : Point) (B₀ : Point) (C₀ : Point) := by
      rw [turn_rotate, turn_rotate]
    rw [hBCA] at heq
    nlinarith [mul_pos ht0 habc]
  rcases hincidence with hI | hII
  · have hzpR : 0 < turn (z : Point) (p : Point) (R : Point) := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (z : Point)) (b := (p : Point)) hI.1
      simp only [turn_self_right] at heq
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hzpx]
    have hzpQ : 0 < turn (z : Point) (p : Point) (q : Point) :=
      edgeTurn_pos_of_mem_openSegment hI.2 hzpy.le hzpR.le (Or.inl hzpy)
    have hCAR : turn (C₀ : Point) (A : Point) (R : Point) < 0 :=
      turn_neg_of_between_of_turn_eq_zero_of_pos hI.1 hCAp hCAx
    have hCAq : turn (C₀ : Point) (A : Point) (q : Point) < 0 :=
      turn_neg_of_mem_openSegment hI.2 hCAy hCAR
    have hBCR : 0 < turn (B₀ : Point) (C₀ : Point) (R : Point) := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hI.1
      rw [hBCx] at heq
      nlinarith [hBCp]
    have hBCq : 0 < turn (B₀ : Point) (C₀ : Point) (q : Point) :=
      edgeTurn_pos_of_mem_openSegment hI.2 hBCy.le hBCR.le (Or.inl hBCy)
    have noZP (hc : colour z = colour p) : False := by
      obtain ⟨w, hw⟩ := hproper z p hzp hc
      have hw0 := turn_eq_zero_of_between hw
      rcases hinside hzp hw with hwx | hwy | hwA | hwp | hwq | hwz
      · rw [hwx] at hw0; linarith
      · rw [hwy] at hw0; linarith
      · rw [hwA] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwp] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
      · rw [hwq] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
    have noZQ (hc : colour z = colour q) : False := by
      obtain ⟨w, hw⟩ := hproper z q hzq hc
      rcases hinside hzq hw with hwx | hwy | hwA | hwp | hwq | hwz
      · have hwpos := edgeTurn_pos_of_mem_openSegment hw hBCz.le hBCq.le
            (Or.inl hBCz)
        rw [hwx, hBCx] at hwpos
        linarith
      · exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
          hfour hRz.symm hzq hRy.symm
          (by simpa only [hwy] using hw) hI.2).elim
      · subst w
        exact ((saturated_left_endpoint_not_between hfour hAB hzSide) hw).elim
      · have hw0 := turn_eq_zero_of_between hw
        rw [hwp, turn_swap_last] at hw0
        linarith
      · have heq : (z : Point) = (q : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwq] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
      · have heq : (z : Point) = (q : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
    exact hcolour.elim noZP noZQ
  · have hzpR : turn (z : Point) (p : Point) (R : Point) < 0 := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (z : Point)) (b := (p : Point)) hII.1
      simp only [turn_self_right] at heq
      nlinarith [mul_pos (sub_pos.mpr ht1) hzpy]
    have hzpQ : turn (z : Point) (p : Point) (q : Point) < 0 :=
      turn_neg_of_mem_openSegment hII.2 hzpx hzpR
    have hCAR : 0 < turn (C₀ : Point) (A : Point) (R : Point) := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (C₀ : Point)) (b := (A : Point)) hII.1
      rw [hCAp] at heq
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hCAy]
    have hCAq : 0 < turn (C₀ : Point) (A : Point) (q : Point) :=
      edgeTurn_pos_of_mem_openSegment hII.2 hCAx.le hCAR.le (Or.inl hCAx)
    have noZP (hc : colour z = colour p) : False := by
      obtain ⟨w, hw⟩ := hproper z p hzp hc
      have hw0 := turn_eq_zero_of_between hw
      rcases hinside hzp hw with hwx | hwy | hwA | hwp | hwq | hwz
      · rw [hwx] at hw0; linarith
      · rw [hwy] at hw0; linarith
      · rw [hwA] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwp] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
      · rw [hwq] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
    have noZQ (hc : colour z = colour q) : False := by
      obtain ⟨w, hw⟩ := hproper z q hzq hc
      have hwpos := edgeTurn_pos_of_mem_openSegment hw hCAz.le hCAq.le
        (Or.inl hCAz)
      rcases hinside hzq hw with hwx | hwy | hwA | hwp | hwq | hwz
      · exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
          hfour hRz.symm hzq hRx.symm
          (by simpa only [hwx] using hw) hII.2).elim
      · rw [hwy] at hwpos; linarith
      · rw [hwA] at hwpos; simp at hwpos
      · rw [hwp, hCAp] at hwpos; linarith
      · have heq : (z : Point) = (q : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwq] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
      · have heq : (z : Point) = (q : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
    exact hcolour.elim noZP noZQ

/-- Reflected form of `double_triangle_visibility_impossible`, with the
red side blocker on `AB` and the remaining doubled-colour point on `AC`. -/
private theorem double_triangle_visibility_impossible_mirror
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    (colour : B → Fin 4) (hproper : ProperBlocking B colour)
    {A B₀ C₀ x y p q z R : B}
    (habc : 0 < turn (A : Point) (B₀ : Point) (C₀ : Point))
    (hxSide : (x : Point) ∈ openSegment ℝ (B₀ : Point) (C₀ : Point))
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hpSide : (p : Point) ∈ openSegment ℝ (A : Point) (B₀ : Point))
    (hzSide : (z : Point) ∈ openSegment ℝ (A : Point) (C₀ : Point))
    (hzq : z ≠ q) (hRz : R ≠ z) (hRy : R ≠ y) (hRx : R ≠ x)
    (hincidence :
      ((p : Point) ∈ openSegment ℝ (x : Point) (R : Point) ∧
        (q : Point) ∈ openSegment ℝ (y : Point) (R : Point)) ∨
      ((p : Point) ∈ openSegment ℝ (y : Point) (R : Point) ∧
        (q : Point) ∈ openSegment ℝ (x : Point) (R : Point)))
    (hcolour : colour z = colour p ∨ colour z = colour q)
    (hinside : ∀ {a c w : B}, a ≠ c →
      (w : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      w = x ∨ w = y ∨ w = A ∨ w = p ∨ w = q ∨ w = z) : False := by
  have hAC : A ≠ C₀ := by
    intro e; subst C₀; simpa [turn] using habc
  have hzCA : (z : Point) ∈ openSegment ℝ (C₀ : Point) (A : Point) := by
    simpa only [openSegment_symm] using hzSide
  have hsideNe := triangle_side_points_pairwise habc hpSide hxSide hzCA
  have hzp : z ≠ p := by
    intro e
    exact hsideNe.2.2 (congrArg Subtype.val e)
  have hABx : 0 < turn (A : Point) (B₀ : Point) (x : Point) :=
    turn_pos_of_mem_next_side habc hxSide
  have hBCx : turn (B₀ : Point) (C₀ : Point) (x : Point) = 0 :=
    turn_eq_zero_of_between hxSide
  have hCAx : 0 < turn (C₀ : Point) (A : Point) (x : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hxSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hABz : 0 < turn (A : Point) (B₀ : Point) (z : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hzSide (by simp) habc.le
    exact Or.inr habc
  have hBCz : 0 < turn (B₀ : Point) (C₀ : Point) (z : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hzSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hCAz : turn (C₀ : Point) (A : Point) (z : Point) = 0 :=
    turn_eq_zero_of_between hzCA
  have hABp : turn (A : Point) (B₀ : Point) (p : Point) = 0 :=
    turn_eq_zero_of_between hpSide
  have hBCp : 0 < turn (B₀ : Point) (C₀ : Point) (p : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hpSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hCAp : 0 < turn (C₀ : Point) (A : Point) (p : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hpSide
    · simp
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · right; simpa only [turn_rotate, turn_rotate] using habc
  have hpzx : turn (p : Point) (z : Point) (x : Point) < 0 := by
    have hthree := turn_side_points_pos habc hpSide hxSide hzCA
    rw [turn_swap_last]
    linarith
  have hpzA : 0 < turn (p : Point) (z : Point) (A : Point) := by
    have hACp : turn (A : Point) (C₀ : Point) (p : Point) < 0 := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (A : Point)) (b := (C₀ : Point)) hpSide
      simp only [turn_self_left] at heq
      have hACB : turn (A : Point) (C₀ : Point) (B₀ : Point) < 0 := by
        rw [turn_swap_last]
        linarith
      nlinarith [mul_neg_of_pos_of_neg ht0 hACB]
    have hApC : 0 < turn (A : Point) (p : Point) (C₀ : Point) := by
      rw [turn_swap_last]
      linarith
    have hApz : 0 < turn (A : Point) (p : Point) (z : Point) :=
      edgeTurn_pos_of_mem_openSegment hzSide (by simp) hApC.le (Or.inr hApC)
    simpa only [turn_rotate] using hApz
  have hpzy : 0 < turn (p : Point) (z : Point) (y : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (p : Point)) (b := (z : Point)) hA
    nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hpzx]
  have hABy : turn (A : Point) (B₀ : Point) (y : Point) < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hA (by simp) hABx
  have hCAy : turn (C₀ : Point) (A : Point) (y : Point) < 0 :=
    turn_neg_of_between_of_turn_eq_zero_of_pos hA (by simp) hCAx
  have hBCy : 0 < turn (B₀ : Point) (C₀ : Point) (y : Point) := by
    obtain ⟨t, ht0, ht1, heq⟩ :=
      turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hA
    rw [hBCx] at heq
    have hBCA : turn (B₀ : Point) (C₀ : Point) (A : Point) =
        turn (A : Point) (B₀ : Point) (C₀ : Point) := by
      rw [turn_rotate, turn_rotate]
    rw [hBCA] at heq
    nlinarith [mul_pos ht0 habc]
  rcases hincidence with hI | hII
  · have hpzR : 0 < turn (p : Point) (z : Point) (R : Point) := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (p : Point)) (b := (z : Point)) hI.1
      simp only [turn_self_left] at heq
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hpzx]
    have hpzQ : 0 < turn (p : Point) (z : Point) (q : Point) :=
      edgeTurn_pos_of_mem_openSegment hI.2 hpzy.le hpzR.le (Or.inl hpzy)
    have hBCR : 0 < turn (B₀ : Point) (C₀ : Point) (R : Point) := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (B₀ : Point)) (b := (C₀ : Point)) hI.1
      rw [hBCx] at heq
      nlinarith [hBCp]
    have hBCq : 0 < turn (B₀ : Point) (C₀ : Point) (q : Point) :=
      edgeTurn_pos_of_mem_openSegment hI.2 hBCy.le hBCR.le (Or.inl hBCy)
    have noZP (hc : colour z = colour p) : False := by
      obtain ⟨w, hw⟩ := hproper z p hzp hc
      have hw0 := turn_eq_zero_of_between
        (by simpa only [openSegment_symm] using hw)
      rcases hinside hzp hw with hwx | hwy | hwA | hwp | hwq | hwz
      · rw [hwx] at hw0; linarith
      · rw [hwy] at hw0; linarith
      · rw [hwA] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwp] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
      · rw [hwq] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
    have noZQ (hc : colour z = colour q) : False := by
      obtain ⟨w, hw⟩ := hproper z q hzq hc
      rcases hinside hzq hw with hwx | hwy | hwA | hwp | hwq | hwz
      · have hwpos := edgeTurn_pos_of_mem_openSegment hw hBCz.le hBCq.le
            (Or.inl hBCz)
        rw [hwx, hBCx] at hwpos
        linarith
      · exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
          hfour hRz.symm hzq hRy.symm
          (by simpa only [hwy] using hw) hI.2).elim
      · subst w
        exact ((saturated_left_endpoint_not_between hfour hAC hzSide) hw).elim
      · have hw0 := turn_eq_zero_of_between hw
        rw [hwp] at hw0
        have hpzq0 : turn (p : Point) (z : Point) (q : Point) = 0 := by
          simpa only [turn_rotate, turn_rotate] using hw0
        linarith
      · have heq : (z : Point) = (q : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwq] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
      · have heq : (z : Point) = (q : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
    exact hcolour.elim noZP noZQ
  · have hpzR : turn (p : Point) (z : Point) (R : Point) < 0 := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (p : Point)) (b := (z : Point)) hII.1
      simp only [turn_self_left] at heq
      nlinarith [mul_pos (sub_pos.mpr ht1) hpzy]
    have hpzQ : turn (p : Point) (z : Point) (q : Point) < 0 :=
      turn_neg_of_mem_openSegment hII.2 hpzx hpzR
    have hABR : 0 < turn (A : Point) (B₀ : Point) (R : Point) := by
      obtain ⟨t, ht0, ht1, heq⟩ :=
        turn_of_mem_openSegment (a := (A : Point)) (b := (B₀ : Point)) hII.1
      rw [hABp] at heq
      nlinarith [mul_neg_of_pos_of_neg (sub_pos.mpr ht1) hABy]
    have hABq : 0 < turn (A : Point) (B₀ : Point) (q : Point) :=
      edgeTurn_pos_of_mem_openSegment hII.2 hABx.le hABR.le (Or.inl hABx)
    have noZP (hc : colour z = colour p) : False := by
      obtain ⟨w, hw⟩ := hproper z p hzp hc
      have hw0 := turn_eq_zero_of_between
        (by simpa only [openSegment_symm] using hw)
      rcases hinside hzp hw with hwx | hwy | hwA | hwp | hwq | hwz
      · rw [hwx] at hw0; linarith
      · rw [hwy] at hw0; linarith
      · rw [hwA] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwp] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
      · rw [hwq] at hw0; linarith
      · have heq : (z : Point) = (p : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzp heq).elim
    have noZQ (hc : colour z = colour q) : False := by
      obtain ⟨w, hw⟩ := hproper z q hzq hc
      have hwpos := edgeTurn_pos_of_mem_openSegment hw hABz.le hABq.le
        (Or.inl hABz)
      rcases hinside hzq hw with hwx | hwy | hwA | hwp | hwq | hwz
      · exact (Lax56Proofs.HKBQuadrilateralMaximal.not_nested_openSegments
          hfour hRz.symm hzq hRx.symm
          (by simpa only [hwx] using hw) hII.2).elim
      · rw [hwy] at hwpos; linarith
      · rw [hwA] at hwpos; simp at hwpos
      · rw [hwp, hABp] at hwpos; linarith
      · have heq : (z : Point) = (q : Point) := by
          apply (right_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwq] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
      · have heq : (z : Point) = (q : Point) := by
          apply (left_mem_openSegment_iff (𝕜 := ℝ)).mp
          simpa only [hwz] using hw
        exact (Subtype.val_injective.ne hzq heq).elim
    exact hcolour.elim noZP noZQ

/-- The boundary half of the `2,2,1,1` distribution.  Here the red point
inside the green triangle lies on the side opposite the green vertex.  The
proof makes the last diagram in Hujter--Kisfaludi--Bak explicit: one of the
two incident green-side blockers is outside the red triangle, so the other
is one of its two remaining side blockers; Lemma 8.3 then supplies the
visible doubled-colour pair. -/
private theorem no_twelve_two_two_boundary_green_core
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    {x y v₁ v₂ A b G₁ G₂ : hexBlockers P h}
    (habc : 0 < turn (A : Point) (G₁ : Point) (G₂ : Point))
    (hxSide : (x : Point) ∈ openSegment ℝ (G₁ : Point) (G₂ : Point))
    (hA : (A : Point) ∈ openSegment ℝ (x : Point) (y : Point))
    (hyOut : (y : Point) ∉ triangleHull (A : Point) (G₁ : Point) (G₂ : Point))
    (hG₁A : G₁ ≠ A) (hG₂A : G₂ ≠ A) (hG₁G₂ : G₁ ≠ G₂)
    (hcG₁ : colour G₁ = colour A) (hcG₂ : colour G₂ = colour A)
    (hv₁v₂ : v₁ ≠ v₂) (hblue : colour v₂ = colour v₁)
    (hcy : colour y = colour x)
    (hredBlue : colour x ≠ colour v₁)
    (hredA : colour x ≠ colour A)
    (hredB : colour x ≠ colour b)
    (hblueA : colour v₁ ≠ colour A)
    (hblueB : colour v₁ ≠ colour b)
    (hABcolour : colour A ≠ colour b)
    (hinside : ∀ {a c z : hexBlockers P h}, a ≠ c →
      (z : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
      z = x ∨ z = y ∨ z = v₁ ∨ z = v₂ ∨ z = A ∨ z = b)
    (hstrictCover : ∀ z : hexBlockers P h, StrictlyInsideHexagon h z →
      z = x ∨ z = y ∨ z = v₁ ∨ z = v₂ ∨ z = A ∨ z = b)
    (allCard : ∀ d, (colourFiber colour d).card = 3) : False := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h₄
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h₄)
  have hneColour {u v : B} (huv : colour u ≠ colour v) : u ≠ v := by
    intro e
    exact huv (congrArg colour e)
  have hxA : x ≠ A := hneColour hredA
  have hxy : x ≠ y := by
    intro e
    subst y
    have hAx : A = x := by
      apply Subtype.ext
      simpa using hA
    exact hxA hAx.symm
  have hyA : y ≠ A := hneColour (by
    intro e
    exact hredA (hcy.symm.trans e))
  have hAG₁ : A ≠ G₁ := hG₁A.symm
  have hG₂A' : G₂ ≠ A := hG₂A
  obtain ⟨R, hRx, hRy, hcR, -⟩ :=
    exists_third_of_colourFiber_card_three (allCard (colour x)) rfl hcy hxy
  have hRA : R ≠ A := hneColour (by
    intro e
    exact hredA (hcR.symm.trans e))
  obtain ⟨p, hp⟩ := hproper x R hRx.symm hcR.symm
  obtain ⟨q, hq⟩ := hproper y R hRy.symm (hcy.trans hcR.symm)
  have hpRed : colour p ≠ colour x :=
    blocker_colour_ne hfourB hproper hRx.symm hcR.symm hp
  have hqRed : colour q ≠ colour x := by
    have hqRed' := blocker_colour_ne hfourB hproper hRy.symm
      (hcy.trans hcR.symm) hq
    exact hqRed'.trans_eq hcy
  have hpHull : (p : Point) ∈
      triangleHull (x : Point) (y : Point) (R : Point) := by
    have hp' := openSegment_subset_triangleHull_left
      (c := (y : Point)) hp
    rw [triangleHull_swap_last] at hp'
    exact hp'
  have hqHull : (q : Point) ∈
      triangleHull (x : Point) (y : Point) (R : Point) := by
    have hq' := openSegment_subset_triangleHull_left
      (c := (x : Point)) hq
    rw [triangleHull_rotate (x : Point) (y : Point) (R : Point)] at hq'
    exact hq'
  have hpCase : p = v₁ ∨ p = v₂ ∨ p = b := by
    rcases hinside hRx.symm hp with e | e | e | e | e | e
    · subst p; exact (hpRed rfl).elim
    · subst p; exact (hpRed hcy).elim
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · subst p
      have hyR := other_endpoint_eq_of_common_blocker hfourB hxy hRx.symm hA hp
      exact (hRy hyR.symm).elim
    · exact Or.inr (Or.inr e)
  have hqCase : q = v₁ ∨ q = v₂ ∨ q = b := by
    rcases hinside hRy.symm hq with e | e | e | e | e | e
    · subst q; exact (hqRed rfl).elim
    · subst q; exact (hqRed hcy).elim
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · subst q
      have hxR := other_endpoint_eq_of_common_blocker hfourB hxy.symm hRy.symm
        (by simpa only [openSegment_symm] using hA) hq
      exact (hRx hxR.symm).elim
    · exact Or.inr (Or.inr e)
  have hpq : p ≠ q := by
    intro e
    subst q
    have hxy' := other_endpoint_eq_of_common_blocker hfourB hRx hRy
      (by simpa only [openSegment_symm] using hp)
      (by simpa only [openSegment_symm] using hq)
    exact hxy hxy'
  obtain ⟨s₀, hs₀⟩ := hproper A G₁ hAG₁ hcG₁.symm
  obtain ⟨s₂, hs₂⟩ := hproper G₂ A hG₂A' hcG₂
  have hs₀Hull : (s₀ : Point) ∈
      triangleHull (A : Point) (G₁ : Point) (G₂ : Point) :=
    openSegment_subset_triangleHull_left hs₀
  have hs₂Hull : (s₂ : Point) ∈
      triangleHull (A : Point) (G₁ : Point) (G₂ : Point) := by
    have hs₂' := openSegment_subset_triangleHull_left
      (c := (G₁ : Point)) hs₂
    rw [triangleHull_rotate (G₁ : Point) (G₂ : Point) (A : Point),
      triangleHull_rotate (A : Point) (G₁ : Point) (G₂ : Point)] at hs₂'
    exact hs₂'
  have hABx : 0 < turn (A : Point) (G₁ : Point) (x : Point) :=
    turn_pos_of_mem_next_side habc hxSide
  have hCAx : 0 < turn (G₂ : Point) (A : Point) (x : Point) := by
    apply edgeTurn_pos_of_mem_openSegment hxSide
    · simpa only [turn_rotate, turn_rotate] using habc.le
    · simp
    · left; simpa only [turn_rotate, turn_rotate] using habc
  have hs₀Case : s₀ = v₁ ∨ s₀ = v₂ ∨ s₀ = b := by
    rcases hinside hAG₁ hs₀ with e | e | e | e | e | e
    · subst s₀
      have hz := turn_eq_zero_of_between hs₀
      linarith
    · exact (hyOut (e ▸ hs₀Hull)).elim
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · subst s₀
      have heq : (A : Point) = (G₁ : Point) :=
        (left_mem_openSegment_iff (𝕜 := ℝ)).mp hs₀
      exact (hG₁A (Subtype.ext heq.symm)).elim
    · exact Or.inr (Or.inr e)
  have hs₂Case : s₂ = v₁ ∨ s₂ = v₂ ∨ s₂ = b := by
    rcases hinside hG₂A' hs₂ with e | e | e | e | e | e
    · subst s₂
      have hz := turn_eq_zero_of_between hs₂
      linarith
    · exact (hyOut (e ▸ hs₂Hull)).elim
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · subst s₂
      have heq : (G₂ : Point) = (A : Point) :=
        (right_mem_openSegment_iff (𝕜 := ℝ)).mp hs₂
      exact (hG₂A (Subtype.ext heq)).elim
    · exact Or.inr (Or.inr e)
  have hs₀s₂ : s₀ ≠ s₂ := by
    intro e
    subst s₂
    have hEq := other_endpoint_eq_of_common_blocker hfourB hAG₁
      hG₂A'.symm hs₀ (by simpa only [openSegment_symm] using hs₂)
    exact hG₁G₂ hEq
  have hxAG₁ : 0 < turn (x : Point) (A : Point) (G₁ : Point) := by
    simpa only [turn_rotate, turn_rotate] using hABx
  have hAxG₂ : 0 < turn (A : Point) (x : Point) (G₂ : Point) := by
    rw [turn_rotate, turn_rotate] at hCAx
    exact hCAx
  have hs₀Pos : 0 < turn (x : Point) (A : Point) (s₀ : Point) :=
    edgeTurn_pos_of_mem_openSegment hs₀ (by simp) hxAG₁.le (Or.inr hxAG₁)
  have hs₂Neg : turn (x : Point) (A : Point) (s₂ : Point) < 0 := by
    have hpos : 0 < turn (A : Point) (x : Point) (s₂ : Point) :=
      edgeTurn_pos_of_mem_openSegment hs₂ hAxG₂.le (by simp) (Or.inl hAxG₂)
    rw [turn_swap_first]
    linarith
  have hXAy : turn (x : Point) (A : Point) (y : Point) = 0 := by
    have hzero := turn_eq_zero_of_between hA
    rw [turn_swap_last, hzero, neg_zero]
  have hXAR : turn (x : Point) (A : Point) (R : Point) ≠ 0 := by
    intro hzero
    have hyLine : (y : Point) ∈
        affineSpan ℝ {(x : Point), (A : Point)} :=
      right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne hxy) hA
    have hRLine : (R : Point) ∈
        affineSpan ℝ {(x : Point), (A : Point)} :=
      mem_line_of_turn_eq_zero (Subtype.val_injective.ne hxA) hzero
    have heq := extra_points_eq_on_saturated_line hfourB hxA hxy.symm hyA
      hRx hRA hyLine hRLine
    exact hRy heq.symm
  have finish {t u : B}
      (htOut : (t : Point) ∉ triangleHull (x : Point) (y : Point) (R : Point))
      (htCase : t = v₁ ∨ t = v₂ ∨ t = b)
      (huCase : u = v₁ ∨ u = v₂ ∨ u = b)
      (htu : t ≠ u)
      (hsideOrder :
        ((u : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) ∧
          (t : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point)) ∨
        ((t : Point) ∈ openSegment ℝ (A : Point) (G₁ : Point) ∧
          (u : Point) ∈ openSegment ℝ (G₂ : Point) (A : Point))) : False := by
    have hpt : p ≠ t := by
      intro e
      subst t
      exact htOut hpHull
    have hqt : q ≠ t := by
      intro e
      subst t
      exact htOut hqHull
    have hperm := three_cover_permutations hpq hpt hqt hpCase hqCase htCase
    have hcandidateExhaust : ∀ w : B,
        (w = v₁ ∨ w = v₂ ∨ w = b) → w = p ∨ w = q ∨ w = t := by
      intro w hw
      rcases hperm with h | h | h | h | h | h
      · rcases h with ⟨hpv₁, hqv₂, htb⟩
        rcases hw with hw | hw | hw
        · exact Or.inl (hw.trans hpv₁.symm)
        · exact Or.inr (Or.inl (hw.trans hqv₂.symm))
        · exact Or.inr (Or.inr (hw.trans htb.symm))
      · rcases h with ⟨hpv₁, hqb, htv₂⟩
        rcases hw with hw | hw | hw
        · exact Or.inl (hw.trans hpv₁.symm)
        · exact Or.inr (Or.inr (hw.trans htv₂.symm))
        · exact Or.inr (Or.inl (hw.trans hqb.symm))
      · rcases h with ⟨hpv₂, hqv₁, htb⟩
        rcases hw with hw | hw | hw
        · exact Or.inr (Or.inl (hw.trans hqv₁.symm))
        · exact Or.inl (hw.trans hpv₂.symm)
        · exact Or.inr (Or.inr (hw.trans htb.symm))
      · rcases h with ⟨hpv₂, hqb, htv₁⟩
        rcases hw with hw | hw | hw
        · exact Or.inr (Or.inr (hw.trans htv₁.symm))
        · exact Or.inl (hw.trans hpv₂.symm)
        · exact Or.inr (Or.inl (hw.trans hqb.symm))
      · rcases h with ⟨hpb, hqv₁, htv₂⟩
        rcases hw with hw | hw | hw
        · exact Or.inr (Or.inl (hw.trans hqv₁.symm))
        · exact Or.inr (Or.inr (hw.trans htv₂.symm))
        · exact Or.inl (hw.trans hpb.symm)
      · rcases h with ⟨hpb, hqv₂, htv₁⟩
        rcases hw with hw | hw | hw
        · exact Or.inr (Or.inr (hw.trans htv₁.symm))
        · exact Or.inr (Or.inl (hw.trans hqv₂.symm))
        · exact Or.inl (hw.trans hpb.symm)
    have hmono : MonoTriple colour x y R :=
      ⟨hxy, hRy.symm, hRx, hcy.symm, hcy.trans hcR.symm⟩
    have hcolourCover : ∀ d : Fin 4, d ≠ colour x →
        d = colour A ∨ d = colour p ∨ d = colour q := by
      intro d hd
      obtain ⟨w, hwHull, hcw⟩ :=
        exists_colour_in_triangleHull hfourB hproper hmono d hd
      have hwx : w ≠ x := by
        intro e; subst w; exact hd hcw.symm
      have hwy : w ≠ y := by
        intro e; subst w; exact hd (hcw.symm.trans hcy)
      have hwR : w ≠ R := by
        intro e; subst w; exact hd (hcw.symm.trans hcR)
      have hwI := triangleHull_nonvertex_strictlyInsideHexagon
        hfour hh hhP hside hwHull hwx hwy hwR
      rcases hstrictCover w hwI with e | e | e | e | e | e
      · exact (hwx e).elim
      · exact (hwy e).elim
      · rcases hcandidateExhaust w (Or.inl e) with ep | eq | et
        · exact Or.inr (Or.inl (hcw.symm.trans (congrArg colour ep)))
        · exact Or.inr (Or.inr (hcw.symm.trans (congrArg colour eq)))
        · exact (htOut (et ▸ hwHull)).elim
      · rcases hcandidateExhaust w (Or.inr (Or.inl e)) with ep | eq | et
        · exact Or.inr (Or.inl (hcw.symm.trans (congrArg colour ep)))
        · exact Or.inr (Or.inr (hcw.symm.trans (congrArg colour eq)))
        · exact (htOut (et ▸ hwHull)).elim
      · exact Or.inl (hcw.symm.trans (congrArg colour e))
      · rcases hcandidateExhaust w (Or.inr (Or.inr e)) with ep | eq | et
        · exact Or.inr (Or.inl (hcw.symm.trans (congrArg colour ep)))
        · exact Or.inr (Or.inr (hcw.symm.trans (congrArg colour eq)))
        · exact (htOut (et ▸ hwHull)).elim
    have hcolours := pairwise_ne_of_fin4_nonred_cover hredA.symm hpRed hqRed
      hcolourCover
    have hpqColour : colour p ≠ colour q := hcolours.2.2
    have htColour : colour t = colour p ∨ colour t = colour q := by
      rcases hperm with h | h | h | h | h | h
      · rcases h with ⟨h₀, h₁, h₂⟩
        exfalso
        exact hpqColour (by simpa only [h₀, h₁] using hblue.symm)
      · rcases h with ⟨h₀, h₁, h₂⟩
        exact Or.inl (by simpa only [h₀, h₂] using hblue)
      · rcases h with ⟨h₀, h₁, h₂⟩
        exfalso
        exact hpqColour (by simpa only [h₀, h₁] using hblue)
      · rcases h with ⟨h₀, h₁, h₂⟩
        exact Or.inl (by simpa only [h₀, h₂] using hblue.symm)
      · rcases h with ⟨h₀, h₁, h₂⟩
        exact Or.inr (by simpa only [h₁, h₂] using hblue)
      · rcases h with ⟨h₀, h₁, h₂⟩
        exact Or.inr (by simpa only [h₁, h₂] using hblue.symm)
    have huPQ : u = p ∨ u = q := by
      rcases hcandidateExhaust u huCase with e | e | e
      · exact Or.inl e
      · exact Or.inr e
      · exact (htu e.symm).elim
    have hinsidePQT : ∀ {a c w : B}, a ≠ c →
        (w : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
        w = x ∨ w = y ∨ w = A ∨ w = p ∨ w = q ∨ w = t := by
      intro a c w hac hw
      rcases hinside hac hw with e | e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · rcases hcandidateExhaust w (Or.inl e) with ep | eq | et
        · exact Or.inr (Or.inr (Or.inr (Or.inl ep)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eq))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr et))))
      · rcases hcandidateExhaust w (Or.inr (Or.inl e)) with ep | eq | et
        · exact Or.inr (Or.inr (Or.inr (Or.inl ep)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eq))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr et))))
      · exact Or.inr (Or.inr (Or.inl e))
      · rcases hcandidateExhaust w (Or.inr (Or.inr e)) with ep | eq | et
        · exact Or.inr (Or.inr (Or.inr (Or.inl ep)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl eq))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr et))))
    have hinsideQPT : ∀ {a c w : B}, a ≠ c →
        (w : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
        w = x ∨ w = y ∨ w = A ∨ w = q ∨ w = p ∨ w = t := by
      intro a c w hac hw
      rcases hinsidePQT hac hw with e | e | e | e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))
    have hRt : R ≠ t := by
      intro e
      subst t
      apply htOut
      exact subset_convexHull ℝ _ (by simp [triangleHull])
    rcases hsideOrder with hUT | hTU
    · rcases huPQ with hup | huq
      · subst u
        exact double_triangle_visibility_impossible_mirror hfourB colour hproper
          habc hxSide hA hUT.1 (by simpa only [openSegment_symm] using hUT.2)
          hqt.symm hRt hRy hRx (Or.inl ⟨hp, hq⟩) htColour hinsidePQT
      · subst u
        exact double_triangle_visibility_impossible_mirror hfourB colour hproper
          habc hxSide hA hUT.1 (by simpa only [openSegment_symm] using hUT.2)
          hpt.symm hRt hRy hRx (Or.inr ⟨hq, hp⟩) htColour.symm hinsideQPT
    · rcases huPQ with hup | huq
      · subst u
        exact double_triangle_visibility_impossible hfourB colour hproper habc
          hxSide hA (by simpa only [openSegment_symm] using hTU.2) hTU.1
          hqt.symm hRt hRy hRx (Or.inl ⟨hp, hq⟩) htColour hinsidePQT
      · subst u
        exact double_triangle_visibility_impossible hfourB colour hproper habc
          hxSide hA (by simpa only [openSegment_symm] using hTU.2) hTU.1
          hpt.symm hRt hRy hRx (Or.inr ⟨hq, hp⟩) htColour.symm hinsideQPT
  by_cases hRpos : 0 < turn (x : Point) (A : Point) (R : Point)
  · have hs₂Out : (s₂ : Point) ∉
        triangleHull (x : Point) (y : Point) (R : Point) := by
      intro hsHull
      have hsNonneg : 0 ≤ turn (x : Point) (A : Point) (s₂ : Point) := by
        apply turn_nonneg_of_mem_convexHull
          (A := ({(x : Point), (y : Point), (R : Point)} : Set Point))
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp
          · rw [hXAy]
          · exact hRpos.le
        · simpa [triangleHull] using hsHull
      linarith
    exact finish hs₂Out hs₂Case hs₀Case hs₀s₂.symm
      (Or.inl ⟨hs₀, hs₂⟩)
  · have hRneg : turn (x : Point) (A : Point) (R : Point) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hRpos) hXAR
    have hs₀Out : (s₀ : Point) ∉
        triangleHull (x : Point) (y : Point) (R : Point) := by
      intro hsHull
      have hsNonpos : turn (x : Point) (A : Point) (s₀ : Point) ≤ 0 := by
        apply turn_nonpos_of_mem_convexHull
          (A := ({(x : Point), (y : Point), (R : Point)} : Set Point))
        · intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl
          · simp
          · rw [hXAy]
          · exact hRneg.le
        · simpa [triangleHull] using hsHull
      linarith
    exact finish hs₀Out hs₀Case hs₂Case hs₀s₂
      (Or.inr ⟨hs₀, hs₂⟩)

/-- Once the singleton green interior point and its two boundary mates are
oriented positively, colour coverage puts one red point in their triangle.
It is either strict-interior (Lemma 8.1/8.2) or on the opposite side
(Lemma 8.3). -/
private theorem no_twelve_two_two_oriented_green
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (C : TwelveTwoTwoStructure colour)
    {G₁ G₂ : hexBlockers P h}
    (hG₁G₂ : G₁ ≠ G₂) (hG₁g : G₁ ≠ C.g) (hG₂g : G₂ ≠ C.g)
    (hcG₁ : colour G₁ = colour C.g)
    (hcG₂ : colour G₂ = colour C.g)
    (habc : 0 < turn (C.g : Point) (G₁ : Point) (G₂ : Point)) : False := by
  classical
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h₄
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h₄)
  have hmono : MonoTriple colour C.g G₁ G₂ :=
    ⟨hG₁g.symm, hG₁G₂, hG₂g, hcG₁.symm,
      hcG₁.trans hcG₂.symm⟩
  obtain ⟨z, hzHull, hcz⟩ := exists_colour_in_triangleHull hfourB
    hproper hmono (colour C.r₁) C.hredG
  have hzg : z ≠ C.g := by
    intro e
    subst z
    exact C.hredG hcz.symm
  have hzG₁ : z ≠ G₁ := by
    intro e
    subst z
    exact C.hredG (hcz.symm.trans hcG₁)
  have hzG₂ : z ≠ G₂ := by
    intro e
    subst z
    exact C.hredG (hcz.symm.trans hcG₂)
  have hzI := triangleHull_nonvertex_strictlyInsideHexagon
    hfour hh hhP hside hzHull hzg hzG₁ hzG₂
  have hzRed : z = C.r₁ ∨ z = C.r₂ := by
    rcases C.insideCover z hzI with e | e | e | e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · subst z; exact (C.hredBlue hcz.symm).elim
    · subst z; exact (C.hredBlue (hcz.symm.trans C.hblue)).elim
    · subst z; exact (C.hredG hcz.symm).elim
    · subst z; exact (C.hredB hcz.symm).elim
  have finish {x y : B}
      (hxy : x ≠ y) (hcy : colour y = colour x)
      (hxRed : colour x = colour C.r₁)
      (hA : (C.g : Point) ∈ openSegment ℝ (x : Point) (y : Point))
      (hxHull : (x : Point) ∈
        triangleHull (C.g : Point) (G₁ : Point) (G₂ : Point))
      (hcover : ∀ w : B, StrictlyInsideHexagon h w →
        w = x ∨ w = y ∨ w = C.v₁ ∨ w = C.v₂ ∨ w = C.g ∨ w = C.b) : False := by
    have hredBlueX : colour x ≠ colour C.v₁ := by
      intro e
      exact C.hredBlue (hxRed.symm.trans e)
    have hredAX : colour x ≠ colour C.g := by
      intro e
      exact C.hredG (hxRed.symm.trans e)
    have hredBX : colour x ≠ colour C.b := by
      intro e
      exact C.hredB (hxRed.symm.trans e)
    have hneColour {u v : B} (huv : colour u ≠ colour v) : u ≠ v := by
      intro e
      exact huv (congrArg colour e)
    have hxg : x ≠ C.g := hneColour hredAX
    have hxG₁ : x ≠ G₁ := hneColour (by
      intro e
      exact hredAX (e.trans hcG₁))
    have hxG₂ : x ≠ G₂ := hneColour (by
      intro e
      exact hredAX (e.trans hcG₂))
    have hyOut : (y : Point) ∉
        triangleHull (C.g : Point) (G₁ : Point) (G₂ : Point) := by
      intro hyHull
      exact triangle_vertex_not_between_hull_points hfourB habc hxHull hyHull
        hA hxg hxG₁ hxG₂
    have hinside : ∀ {a c w : B}, a ≠ c →
        (w : Point) ∈ openSegment ℝ (a : Point) (c : Point) →
        w = x ∨ w = y ∨ w = C.v₁ ∨ w = C.v₂ ∨ w = C.g ∨ w = C.b := by
      intro a c w hac hw
      exact hcover w (openSegment_between_blockers_strictlyInside
        hfour hh hhP hside a.property c.property
        (Subtype.val_injective.ne hac) hw)
    by_cases hxStrict : StrictlyInsideTriangle
        (C.g : Point) (G₁ : Point) (G₂ : Point) x
    · exact no_twelve_two_two_strict_green_core hfourB colour hproper habc
        hxStrict hyOut hA hG₁g hG₂g hG₁G₂ hcG₁ hcG₂ C.hv C.hblue
        hcy hredBlueX C.hblueG hinside C.allCard
    · rcases mem_openSide_of_mem_triangleHull_not_strict habc hxHull
          (Subtype.val_injective.ne hxg) (Subtype.val_injective.ne hxG₁)
          (Subtype.val_injective.ne hxG₂) hxStrict with hxAG₁ | hxG₁G₂ | hxG₂A
      · exact ((saturated_left_endpoint_not_between hfourB hG₁g.symm hxAG₁) hA).elim
      · exact no_twelve_two_two_boundary_green_core hfour hh hhP hside
          colour hproper habc hxG₁G₂ hA hyOut hG₁g hG₂g hG₁G₂
          hcG₁ hcG₂ C.hv C.hblue hcy hredBlueX hredAX hredBX
          C.hblueG C.hblueB C.hgb hinside hcover C.allCard
      · exact ((saturated_right_endpoint_not_between hfourB hG₂g hxG₂A) hA).elim
  rcases hzRed with hz | hz
  · subst z
    exact finish C.hr C.hred rfl C.hg hzHull C.insideCover
  · subst z
    have hcoverSwap : ∀ w : B, StrictlyInsideHexagon h w →
        w = C.r₂ ∨ w = C.r₁ ∨ w = C.v₁ ∨ w = C.v₂ ∨
          w = C.g ∨ w = C.b := by
      intro w hw
      rcases C.insideCover w hw with e | e | e | e | e | e
      · exact Or.inr (Or.inl e)
      · exact Or.inl e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))
    exact finish C.hr.symm C.hred.symm C.hred
      (by simpa only [openSegment_symm] using C.hg) hzHull hcoverSwap

/-- The complete `2,2,1,1` interior distribution. -/
private theorem no_twelve_two_two_structure
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (C : TwelveTwoTwoStructure colour) : False := by
  let B := hexBlockers P h
  have hfourB : ¬HasFourCollinear B := by
    intro h₄
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h₄)
  obtain ⟨G₁, G₂, hG₁G₂, hG₁g, hG₂g, hcG₁, hcG₂⟩ :=
    exists_two_others_of_colourFiber_card_three (C.allCard (colour C.g)) rfl
  have hturn : turn (C.g : Point) (G₁ : Point) (G₂ : Point) ≠ 0 :=
    turn_ne_zero_of_same_colour hfourB hproper hG₁g.symm hG₁G₂ hG₂g
      hcG₁.symm (hcG₁.trans hcG₂.symm)
  by_cases hpos : 0 < turn (C.g : Point) (G₁ : Point) (G₂ : Point)
  · exact no_twelve_two_two_oriented_green hfour hh hhP hside colour hproper C
      hG₁G₂ hG₁g hG₂g hcG₁ hcG₂ hpos
  · have hneg : turn (C.g : Point) (G₁ : Point) (G₂ : Point) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hturn
    have hpos' : 0 < turn (C.g : Point) (G₂ : Point) (G₁ : Point) := by
      rw [turn_swap_last]
      linarith
    exact no_twelve_two_two_oriented_green hfour hh hhP hside colour hproper C
      hG₁G₂.symm hG₂g hG₁g hcG₂ hcG₁ hpos'

/-- The `3,1,1,1` interior distribution at twelve blockers.  A
monochromatic interior triangle and its three side blockers exhaust the
six interior points.  The six remaining points are forced onto three
already saturated lines. -/
private theorem no_twelve_of_oriented_interior_mono_triple
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 12)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour)
    (hle : ∀ d, (colourFiber colour d).card ≤ 3)
    {p q r : hexBlockers P h}
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p)
    (hpqr : 0 < turn (p : Point) (q : Point) (r : Point))
    (hcq : colour q = colour p) (hcr : colour r = colour p)
    (hpI : StrictlyInsideHexagon h p)
    (hqI : StrictlyInsideHexagon h q)
    (hrI : StrictlyInsideHexagon h r) : False := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hfourB : ¬HasFourCollinear B := by
    intro h4
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h4)
  have hIcard : I.card = 6 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  obtain ⟨v, hv⟩ := hproper p q hpq hcq.symm
  obtain ⟨g, hg⟩ := hproper p r hrp.symm hcr.symm
  obtain ⟨b, hb⟩ := hproper q r hqr (hcq.trans hcr.symm)
  have hvp : colour v ≠ colour p :=
    blocker_colour_ne hfourB hproper hpq hcq.symm hv
  have hgp : colour g ≠ colour p :=
    blocker_colour_ne (x := p) (y := r) (z := g)
      hfourB hproper hrp.symm hcr.symm hg
  have hbp : colour b ≠ colour p :=
    (blocker_colour_ne (x := q) (y := r) (z := b)
      hfourB hproper hqr (hcq.trans hcr.symm) hb).trans_eq hcq
  have hvI : StrictlyInsideHexagon h v :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      p.property q.property (Subtype.val_injective.ne hpq) hv
  have hgI : StrictlyInsideHexagon h g :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      p.property r.property (Subtype.val_injective.ne hrp.symm) hg
  have hbI : StrictlyInsideHexagon h b :=
    openSegment_between_blockers_strictlyInside hfour hh hhP hside
      q.property r.property (Subtype.val_injective.ne hqr) hb
  have hneColour {x y : B} (hxy : colour x ≠ colour y) : x ≠ y := by
    intro e
    exact hxy (congrArg colour e)
  have hvp' : v ≠ p := hneColour hvp
  have hvq : v ≠ q := hneColour (hvp.trans_eq hcq.symm)
  have hvr : v ≠ r := hneColour (hvp.trans_eq hcr.symm)
  have hgp' : g ≠ p := hneColour hgp
  have hgq : g ≠ q := hneColour (hgp.trans_eq hcq.symm)
  have hgr : g ≠ r := hneColour (hgp.trans_eq hcr.symm)
  have hbp' : b ≠ p := hneColour hbp
  have hbq : b ≠ q := hneColour (hbp.trans_eq hcq.symm)
  have hbr : b ≠ r := hneColour (hbp.trans_eq hcr.symm)
  have hvg : v ≠ g := by
    intro e
    subst g
    have hqr' := other_endpoint_eq_of_common_blocker hfourB hpq hrp.symm hv hg
    exact hqr hqr'
  have hvb : v ≠ b := by
    intro e
    subst b
    have hpr' := other_endpoint_eq_of_common_blocker hfourB hpq.symm hqr
      (by simpa only [openSegment_symm] using hv) hb
    exact hrp hpr'.symm
  have hgb : g ≠ b := by
    intro e
    subst b
    have hpq' := other_endpoint_eq_of_common_blocker hfourB hrp hqr.symm
      (by simpa only [openSegment_symm] using hg)
      (by simpa only [openSegment_symm] using hb)
    exact hpq hpq'
  let e : B ↪ Point := ⟨fun z ↦ (z : Point), Subtype.val_injective⟩
  let K₀ : Finset B := {p, q, r, v, g, b}
  let J : Finset Point := K₀.map e
  have hK₀card : K₀.card = 6 := by
    simp [K₀, hpq, hrp.symm, hvp'.symm, hgp'.symm, hbp'.symm,
      hqr, hvq.symm, hgq.symm, hbq.symm, hvr.symm,
      hgr.symm, hbr.symm, hvg, hvb, hgb]
  have hJcard : J.card = 6 := by
    change (K₀.map e).card = 6
    simpa using hK₀card
  have hJsub : J ⊆ I := by
    intro x hx
    change x ∈ K₀.map e at hx
    rw [Finset.mem_map] at hx
    obtain ⟨z, hzK, rfl⟩ := hx
    simp only [K₀, Finset.mem_insert, Finset.mem_singleton] at hzK
    rcases hzK with h | h | h | h | h | h
    · subst z; exact Finset.mem_filter.mpr ⟨p.property, hpI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨q.property, hqI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨r.property, hrI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨v.property, hvI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨g.property, hgI⟩
    · subst z; exact Finset.mem_filter.mpr ⟨b.property, hbI⟩
  have hJI : J = I :=
    Finset.eq_of_subset_of_card_le hJsub (by rw [hIcard, hJcard])
  have hIcover : ∀ z : B, StrictlyInsideHexagon h z →
      z = p ∨ z = q ∨ z = r ∨ z = v ∨ z = g ∨ z = b := by
    intro z hz
    have hzI : (z : Point) ∈ I := Finset.mem_filter.mpr ⟨z.property, hz⟩
    rw [← hJI] at hzI
    change (z : Point) ∈ K₀.map e at hzI
    rw [Finset.mem_map] at hzI
    obtain ⟨w, hwK, hwz⟩ := hzI
    have hwzB : w = z := Subtype.ext hwz
    subst w
    simpa only [K₀, Finset.mem_insert, Finset.mem_singleton] using hwK
  have hinside : ∀ {x y z : B}, x ≠ y →
      (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      z = p ∨ z = q ∨ z = r ∨ z = v ∨ z = g ∨ z = b := by
    intro x y z hxy hz
    exact hIcover z (openSegment_between_blockers_strictlyInside
      hfour hh hhP hside x.property y.property
      (Subtype.val_injective.ne hxy) hz)
  have hmono : MonoTriple colour p q r :=
    ⟨hpq, hqr, hrp, hcq.symm, hcq.trans hcr.symm⟩
  have hcolourCover : ∀ d : Fin 4, d ≠ colour p →
      d = colour v ∨ d = colour g ∨ d = colour b := by
    intro d hd
    obtain ⟨x, hxHull, hcxd⟩ :=
      exists_colour_in_triangleHull hfourB hproper hmono d hd
    have hxp : x ≠ p := by intro ex; subst x; exact hd hcxd.symm
    have hxq : x ≠ q := by
      intro ex; subst x; exact hd (hcxd.symm.trans hcq)
    have hxr : x ≠ r := by
      intro ex; subst x; exact hd (hcxd.symm.trans hcr)
    have hxI := triangleHull_nonvertex_strictlyInsideHexagon
      hfour hh hhP hside hxHull hxp hxq hxr
    rcases hIcover x hxI with ex | ex | ex | ex | ex | ex
    · exact (hxp ex).elim
    · exact (hxq ex).elim
    · exact (hxr ex).elim
    · exact Or.inl (hcxd.symm.trans (congrArg colour ex))
    · exact Or.inr (Or.inl (hcxd.symm.trans (congrArg colour ex)))
    · exact Or.inr (Or.inr (hcxd.symm.trans (congrArg colour ex)))
  have hvgb := pairwise_ne_of_fin4_nonred_cover hvp hgp hbp hcolourCover
  have hBcard : Fintype.card B = 12 := by simpa [B, hcard]
  have hvCard := colourFiber_card_three_of_twelve colour hBcard hle (colour v)
  have hgCard := colourFiber_card_three_of_twelve colour hBcard hle (colour g)
  have hbCard := colourFiber_card_three_of_twelve colour hBcard hle (colour b)
  obtain ⟨xv₀, xv₁, hv₀₁, hv₀v, hv₁v, hcv₀, hcv₁⟩ :=
    exists_two_others_of_colourFiber_card_three hvCard rfl
  obtain ⟨xg₀, xg₁, hg₀₁, hg₀g, hg₁g, hcg₀, hcg₁⟩ :=
    exists_two_others_of_colourFiber_card_three hgCard rfl
  obtain ⟨xb₀, xb₁, hb₀₁, hb₀b, hb₁b, hcb₀, hcb₁⟩ :=
    exists_two_others_of_colourFiber_card_three hbCard rfl
  have hvLines := triangle_side_colour_other_points_on_adjacent_lines
    hfourB colour hproper hpq hpqr hv hg hb hinside
    hv₀₁ hv₀v hv₁v hcv₀ hcv₁
  have hinsideG : ∀ {x y z : B}, x ≠ y →
      (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      z = r ∨ z = p ∨ z = q ∨ z = g ∨ z = b ∨ z = v := by
    intro x y z hxy hz
    rcases hinside hxy hz with ex | ex | ex | ex | ex | ex
    · exact Or.inr (Or.inl ex)
    · exact Or.inr (Or.inr (Or.inl ex))
    · exact Or.inl ex
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ex))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ex)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ex))))
  have hgLines := triangle_side_colour_other_points_on_adjacent_lines
    hfourB colour hproper hrp
    (by simpa only [turn_rotate, turn_rotate] using hpqr)
    (by simpa only [openSegment_symm] using hg)
    (by simpa only [openSegment_symm] using hb) hv hinsideG
    hg₀₁ hg₀g hg₁g hcg₀ hcg₁
  have hinsideB : ∀ {x y z : B}, x ≠ y →
      (z : Point) ∈ openSegment ℝ (x : Point) (y : Point) →
      z = q ∨ z = r ∨ z = p ∨ z = b ∨ z = v ∨ z = g := by
    intro x y z hxy hz
    rcases hinside hxy hz with ex | ex | ex | ex | ex | ex
    · exact Or.inr (Or.inr (Or.inl ex))
    · exact Or.inl ex
    · exact Or.inr (Or.inl ex)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ex))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ex))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ex)))
  have hbLines := triangle_side_colour_other_points_on_adjacent_lines
    hfourB colour hproper hqr
    (by simpa only [turn_rotate] using hpqr) hb
    (by simpa only [openSegment_symm] using hv)
    (by simpa only [openSegment_symm] using hg) hinsideB
    hb₀₁ hb₀b hb₁b hcb₀ hcb₁
  have hneCross {a b c d : B} (hac : colour a = colour c)
      (hbd : colour b = colour d) (hcd : colour c ≠ colour d) : a ≠ b := by
    intro eab
    exact hcd (hac.symm.trans ((congrArg colour eab).trans hbd))
  have hv₀g₀ := hneCross hcv₀ hcg₀ hvgb.1
  have hv₀g₁ := hneCross hcv₀ hcg₁ hvgb.1
  have hv₁g₀ := hneCross hcv₁ hcg₀ hvgb.1
  have hv₁g₁ := hneCross hcv₁ hcg₁ hvgb.1
  have hv₀b₀ := hneCross hcv₀ hcb₀ hvgb.2.1
  have hv₀b₁ := hneCross hcv₀ hcb₁ hvgb.2.1
  have hv₁b₀ := hneCross hcv₁ hcb₀ hvgb.2.1
  have hv₁b₁ := hneCross hcv₁ hcb₁ hvgb.2.1
  have hg₀b₀ := hneCross hcg₀ hcb₀ hvgb.2.2
  have hg₀b₁ := hneCross hcg₀ hcb₁ hvgb.2.2
  have hg₁b₀ := hneCross hcg₁ hcb₀ hvgb.2.2
  have hg₁b₁ := hneCross hcg₁ hcb₁ hvgb.2.2
  let E : Finset B := {xv₀, xv₁, xg₀, xg₁, xb₀, xb₁}
  have hEcard : E.card = 6 := by
    simp [E, hv₀₁, hv₀g₀, hv₀g₁, hv₀b₀, hv₀b₁,
      hv₁g₀, hv₁g₁, hv₁b₀, hv₁b₁, hg₀₁,
      hg₀b₀, hg₀b₁, hg₁b₀, hg₁b₁, hb₀₁]
  have hnew : ∀ x ∈ E, x ≠ v ∧ x ≠ b ∧ x ≠ g := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨hv₀v, hneCross hcv₀ rfl hvgb.2.1,
        hneCross hcv₀ rfl hvgb.1⟩
    · exact ⟨hv₁v, hneCross hcv₁ rfl hvgb.2.1,
        hneCross hcv₁ rfl hvgb.1⟩
    · exact ⟨hneCross hcg₀ rfl hvgb.1.symm,
        hneCross hcg₀ rfl hvgb.2.2, hg₀g⟩
    · exact ⟨hneCross hcg₁ rfl hvgb.1.symm,
        hneCross hcg₁ rfl hvgb.2.2, hg₁g⟩
    · exact ⟨hneCross hcb₀ rfl hvgb.2.1.symm, hb₀b,
        hneCross hcb₀ rfl hvgb.2.2.symm⟩
    · exact ⟨hneCross hcb₁ rfl hvgb.2.1.symm, hb₁b,
        hneCross hcb₁ rfl hvgb.2.2.symm⟩
  have hcover : ∀ x ∈ E,
      (x : Point) ∈ affineSpan ℝ {(v : Point), (b : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(v : Point), (g : Point)} ∨
      (x : Point) ∈ affineSpan ℝ {(b : Point), (g : Point)} := by
    intro x hx
    simp only [E, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hvLines.1.elim Or.inl (fun hline ↦ Or.inr (Or.inl hline))
    · exact hvLines.2.elim Or.inl (fun hline ↦ Or.inr (Or.inl hline))
    · exact hgLines.1.elim
        (fun hline ↦ Or.inr (Or.inl (by simpa only [Set.pair_comm] using hline)))
        (fun hline ↦ Or.inr (Or.inr (by simpa only [Set.pair_comm] using hline)))
    · exact hgLines.2.elim
        (fun hline ↦ Or.inr (Or.inl (by simpa only [Set.pair_comm] using hline)))
        (fun hline ↦ Or.inr (Or.inr (by simpa only [Set.pair_comm] using hline)))
    · exact hbLines.1.elim (fun hline ↦ Or.inr (Or.inr hline))
        (fun hline ↦ Or.inl (by simpa only [Set.pair_comm] using hline))
    · exact hbLines.2.elim (fun hline ↦ Or.inr (Or.inr hline))
        (fun hline ↦ Or.inl (by simpa only [Set.pair_comm] using hline))
  exact extras_not_on_three_saturated_lines hfourB hvb hvg hgb.symm
    E (by omega) hnew hcover

/-- The complete eleven-blocker case. -/
theorem no_eleven_hexBlockers
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hdiag : ∀ d : Fin 9, ∃ r ∈ hexBlockers P h,
      r ∈ openSegment ℝ
        (h (diagonalEnds d).1) (h (diagonalEnds d).2))
    (hcard : (hexBlockers P h).card = 11)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour) : False := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hIcard : I.card = 5 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  have hle : ∀ d, (colourFiber colour d).card ≤ 3 := by
    intro d
    simpa [colourFiber] using colour_class_card_le_three
      hfour hh hhP hside (by omega : (hexBlockers P h).card ≤ 12)
      colour hproper d
  let toB : I → B := fun z ↦
    ⟨(z : Point), (Finset.mem_filter.mp z.property).1⟩
  have htoBInj : Function.Injective toB := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : B ↦ (z : Point)) hxy
  let innerColour : I → Fin 4 := fun z ↦ colour (toB z)
  have hItypeCard : Fintype.card I = 5 := by
    simpa only [Fintype.card_coe] using hIcard
  obtain ⟨pI, qI, hpqI, hcI⟩ :=
    exists_same_colour_pair_of_card_five hItypeCard innerColour
  let p : B := toB pI
  let q : B := toB qI
  have hpq : p ≠ q := by
    intro hpq'
    exact hpqI (htoBInj hpq')
  have hpI : StrictlyInsideHexagon h p := by
    exact (Finset.mem_filter.mp pI.property).2
  have hqI : StrictlyInsideHexagon h q := by
    exact (Finset.mem_filter.mp qI.property).2
  have hcq : colour q = colour p := by
    simpa [innerColour, p, q] using hcI.symm
  have hpMem : p ∈ colourFiber colour (colour p) := by simp
  have hqMem : q ∈ colourFiber colour (colour p) := by simpa using hcq
  have htwo : 2 ≤ (colourFiber colour (colour p)).card := by
    have hsub : ({p, q} : Finset B) ⊆ colourFiber colour (colour p) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hpMem
      · exact hqMem
    have hleCard := Finset.card_le_card hsub
    simpa [hpq] using hleCard
  have hclass : (colourFiber colour (colour p)).card = 2 ∨
      (colourFiber colour (colour p)).card = 3 := by
    have hupper := hle (colour p)
    omega
  rcases hclass with htwoEq | hthreeEq
  · exact no_eleven_of_interior_pair_colour_two hfour hh hhP hside hdiag
      hcard colour hproper hle hpq hpI hqI hcq htwoEq
  · exact no_eleven_of_interior_pair_colour_three hfour hh hhP hside hcard
      colour hproper hle hpq hpI hqI hcq hthreeEq

/-- The complete twelve-blocker case.  The six strict-interior blockers
have positive colour counts summing to six.  Thus their distribution is
`3,1,1,1` or `2,2,1,1`, and the two direct geometric cores above apply. -/
theorem no_twelve_hexBlockers
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {h : Fin 6 → Point} (hh : StrictConvexHexagon h)
    (hhP : ∀ i, h i ∈ P)
    (hside : ∀ i : Fin 6, ∃ s ∈ hexBlockers P h,
      s ∈ openSegment ℝ (h i) (h (i + 1)))
    (hcard : (hexBlockers P h).card = 12)
    (colour : hexBlockers P h → Fin 4)
    (hproper : ProperBlocking (hexBlockers P h) colour) : False := by
  classical
  let B := hexBlockers P h
  let I := B.filter (StrictlyInsideHexagon h)
  have hfourB : ¬HasFourCollinear B := by
    intro h₄
    exact hfour (hasFourCollinear_mono (hexBlockers_subset P h) h₄)
  have hIcard : I.card = 6 := by
    simpa [I, B, hcard] using
      strictInteriorBlockers_card hfour hh hhP hside
  have hle : ∀ d, (colourFiber colour d).card ≤ 3 := by
    intro d
    simpa [colourFiber] using colour_class_card_le_three
      hfour hh hhP hside (by omega : (hexBlockers P h).card ≤ 12)
      colour hproper d
  have hinner : ∀ d : Fin 4, ∃ z : B,
      StrictlyInsideHexagon h z ∧ colour z = d :=
    exists_strictInterior_point_of_colour_twelve hfour hh hhP hside hcard
      colour hproper hle
  let toB : I → B := fun z ↦
    ⟨(z : Point), (Finset.mem_filter.mp z.property).1⟩
  have htoBInj : Function.Injective toB := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : B ↦ (z : Point)) hxy
  let innerColour : I → Fin 4 := fun z ↦ colour (toB z)
  let f : Fin 4 → ℕ := fun d ↦ (colourFiber innerColour d).card
  have hItypeCard : Fintype.card I = 6 := by
    simpa only [Fintype.card_coe] using hIcard
  have hsum : (∑ d : Fin 4, f d) = 6 := by
    simpa [f, hItypeCard] using (card_eq_sum_colourFibers innerColour).symm
  have hfpos : ∀ d, 1 ≤ f d := by
    intro d
    obtain ⟨z, hzI, hcz⟩ := hinner d
    let zI : I := ⟨(z : Point), Finset.mem_filter.mpr ⟨z.property, hzI⟩⟩
    have hzColour : innerColour zI = d := by
      simpa [innerColour, toB, zI] using hcz
    apply Finset.one_le_card.mpr
    exact ⟨zI, mem_colourFiber.mpr hzColour⟩
  let e : I ↪ B := ⟨toB, htoBInj⟩
  have hfle : ∀ d, f d ≤ 3 := by
    intro d
    have hsub : (colourFiber innerColour d).map e ⊆ colourFiber colour d := by
      intro z hz
      rw [Finset.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      apply mem_colourFiber.mpr
      simpa [innerColour, e] using mem_colourFiber.mp hw
    calc
      f d = ((colourFiber innerColour d).map e).card := by
        simp [f]
      _ ≤ (colourFiber colour d).card := Finset.card_le_card hsub
      _ ≤ 3 := hle d
  rcases six_as_four_positive_parts f hsum hfpos hfle with hthree | htwoTwo
  · obtain ⟨c, hc⟩ := hthree
    obtain ⟨pI, qI, rI, hpqI, hprI, hqrI, hset⟩ :=
      Finset.card_eq_three.mp hc
    have hpMem : pI ∈ colourFiber innerColour c := by rw [hset]; simp
    have hqMem : qI ∈ colourFiber innerColour c := by rw [hset]; simp
    have hrMem : rI ∈ colourFiber innerColour c := by rw [hset]; simp
    let p : B := toB pI
    let q : B := toB qI
    let r : B := toB rI
    have hpq : p ≠ q := by
      intro e'
      exact hpqI (htoBInj e')
    have hpr : p ≠ r := by
      intro e'
      exact hprI (htoBInj e')
    have hqr : q ≠ r := by
      intro e'
      exact hqrI (htoBInj e')
    have hcp : colour p = c := by
      simpa [p, innerColour] using mem_colourFiber.mp hpMem
    have hcq : colour q = c := by
      simpa [q, innerColour] using mem_colourFiber.mp hqMem
    have hcr : colour r = c := by
      simpa [r, innerColour] using mem_colourFiber.mp hrMem
    have hpI : StrictlyInsideHexagon h p :=
      (Finset.mem_filter.mp pI.property).2
    have hqI : StrictlyInsideHexagon h q :=
      (Finset.mem_filter.mp qI.property).2
    have hrI : StrictlyInsideHexagon h r :=
      (Finset.mem_filter.mp rI.property).2
    have hpqColour : colour q = colour p := hcq.trans hcp.symm
    have hprColour : colour r = colour p := hcr.trans hcp.symm
    have hturn : turn (p : Point) (q : Point) (r : Point) ≠ 0 :=
      turn_ne_zero_of_same_colour hfourB hproper hpq hqr hpr.symm
        hpqColour.symm (hpqColour.trans hprColour.symm)
    by_cases hpos : 0 < turn (p : Point) (q : Point) (r : Point)
    · exact no_twelve_of_oriented_interior_mono_triple hfour hh hhP hside
        hcard colour hproper hle hpq hqr hpr.symm hpos hpqColour hprColour
        hpI hqI hrI
    · have hneg : turn (p : Point) (q : Point) (r : Point) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) hturn
      have hpos' : 0 < turn (q : Point) (p : Point) (r : Point) := by
        rw [turn_swap_first]
        linarith
      exact no_twelve_of_oriented_interior_mono_triple hfour hh hhP hside
        hcard colour hproper hle hpq.symm hpr hqr.symm hpos'
        hpqColour.symm (hprColour.trans hpqColour.symm)
        hqI hpI hrI
  · obtain ⟨c, d, hcd, hc, hd⟩ := htwoTwo
    obtain ⟨pI, qI, hpqI, hpSet⟩ := Finset.card_eq_two.mp hc
    obtain ⟨uI, vI, huvI, huSet⟩ := Finset.card_eq_two.mp hd
    have hpMem : pI ∈ colourFiber innerColour c := by rw [hpSet]; simp
    have hqMem : qI ∈ colourFiber innerColour c := by rw [hpSet]; simp
    have huMem : uI ∈ colourFiber innerColour d := by rw [huSet]; simp
    have hvMem : vI ∈ colourFiber innerColour d := by rw [huSet]; simp
    have hcpI := mem_colourFiber.mp hpMem
    have hcqI := mem_colourFiber.mp hqMem
    have hcuI := mem_colourFiber.mp huMem
    have hcvI := mem_colourFiber.mp hvMem
    let p : B := toB pI
    let q : B := toB qI
    let u : B := toB uI
    let v : B := toB vI
    have hpq : p ≠ q := by intro e'; exact hpqI (htoBInj e')
    have huv : u ≠ v := by intro e'; exact huvI (htoBInj e')
    have hcp : colour p = c := by simpa [p, innerColour] using hcpI
    have hcq : colour q = c := by simpa [q, innerColour] using hcqI
    have hcu : colour u = d := by simpa [u, innerColour] using hcuI
    have hcv : colour v = d := by simpa [v, innerColour] using hcvI
    have hred : colour q = colour p := hcq.trans hcp.symm
    have hblue : colour v = colour u := hcv.trans hcu.symm
    have hredBlue : colour p ≠ colour u := by
      intro ecu
      exact hcd (hcp.symm.trans (ecu.trans hcu))
    have hpI : StrictlyInsideHexagon h p := (Finset.mem_filter.mp pI.property).2
    have hqI : StrictlyInsideHexagon h q := (Finset.mem_filter.mp qI.property).2
    have huI : StrictlyInsideHexagon h u := (Finset.mem_filter.mp uI.property).2
    have hvI : StrictlyInsideHexagon h v := (Finset.mem_filter.mp vI.property).2
    have hredCover : ∀ z : B, StrictlyInsideHexagon h z →
        colour z = colour p → z = p ∨ z = q := by
      intro z hzI hcz
      let zI : I := ⟨(z : Point), Finset.mem_filter.mpr ⟨z.property, hzI⟩⟩
      have hzColour : innerColour zI = c := by
        simpa [innerColour, toB, zI, hcp] using hcz
      have hzCase := eq_first_or_second_of_colourFiber_card_two hc
        hcpI hcqI hpqI hzColour
      rcases hzCase with e' | e'
      · exact Or.inl (congrArg toB e')
      · exact Or.inr (congrArg toB e')
    have hblueCover : ∀ z : B, StrictlyInsideHexagon h z →
        colour z = colour u → z = u ∨ z = v := by
      intro z hzI hcz
      let zI : I := ⟨(z : Point), Finset.mem_filter.mpr ⟨z.property, hzI⟩⟩
      have hzColour : innerColour zI = d := by
        simpa [innerColour, toB, zI, hcu] using hcz
      have hzCase := eq_first_or_second_of_colourFiber_card_two hd
        hcuI hcvI huvI hzColour
      rcases hzCase with e' | e'
      · exact Or.inl (congrArg toB e')
      · exact Or.inr (congrArg toB e')
    obtain ⟨C⟩ := build_twelve_two_two_structure hfour hh hhP hside hcard
      colour hproper hle hinner hpq huv hred hblue hredBlue hpI hqI huI hvI
      hredCover hblueCover
    exact no_twelve_two_two_structure hfour hh hhP hside colour hproper C

end Lax56Proofs.HKBFinalCases
