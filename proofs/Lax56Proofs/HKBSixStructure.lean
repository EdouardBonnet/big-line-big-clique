import Lax56Proofs.HKBTriangle
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Tactic

/-!
The structure of a six-point properly three-coloured blocking set.
-/

namespace Lax56Proofs.HKBSixStructure

open Lax56.Geometry
open Lax56Proofs.HKBBlocking
open Lax56Proofs.HKBTriangle

noncomputable def colourFiber {B : Finset Point} (colour : B → Fin 3)
    (d : Fin 3) : Finset B := by
  classical
  exact Finset.univ.filter fun p ↦ colour p = d

@[simp] theorem mem_colourFiber
    {B : Finset Point} {colour : B → Fin 3} {d : Fin 3} {p : B} :
    p ∈ colourFiber colour d ↔ colour p = d := by
  classical
  simp [colourFiber]

theorem colourFiber_card_le_two
    {B : Finset Point} (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 3} (hproper : ProperBlocking B colour)
    (d : Fin 3) :
    (colourFiber colour d).card ≤ 2 := by
  classical
  by_contra hle
  have hlt : 2 < (colourFiber colour d).card := Nat.lt_of_not_ge hle
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hlt
  have hcab : colour a = colour b :=
    (mem_colourFiber.mp ha).trans (mem_colourFiber.mp hb).symm
  have hcbc : colour b = colour c :=
    (mem_colourFiber.mp hb).trans (mem_colourFiber.mp hc).symm
  exact no_monoTriple_three_colours hfour hproper
    ⟨hab, hbc, hac.symm, hcab, hcbc⟩

/-- In a six-point properly three-coloured blocking set, every colour occurs
exactly twice. -/
theorem colourFiber_card_eq_two_of_card_eq_six
    {B : Finset Point} (hcard : B.card = 6)
    (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 3} (hproper : ProperBlocking B colour)
    (d : Fin 3) : (colourFiber colour d).card = 2 := by
  let F : Fin 3 → Finset B := colourFiber colour
  have hFle : ∀ e : Fin 3, (F e).card ≤ 2 := fun e ↦
    colourFiber_card_le_two hfour hproper e
  have htotal : 6 = ∑ e ∈ (Finset.univ : Finset (Fin 3)), (F e).card := by
    calc
      6 = B.card := hcard.symm
      _ = (Finset.univ : Finset B).card := by simp
      _ = ∑ e ∈ (Finset.univ : Finset (Fin 3)),
          ((Finset.univ : Finset B).filter fun p ↦ colour p = e).card := by
            apply Finset.card_eq_sum_card_fiberwise
            intro p hp
            simp
      _ = ∑ e ∈ (Finset.univ : Finset (Fin 3)), (F e).card := by rfl
  have hsum : (F 0).card + (F 1).card + (F 2).card = 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using htotal.symm
  have h0 := hFle 0
  have h1 := hFle 1
  have h2 := hFle 2
  have hF0 : (F 0).card = 2 := by omega
  have hF1 : (F 1).card = 2 := by omega
  have hF2 : (F 2).card = 2 := by omega
  fin_cases d
  · exact hF0
  · exact hF1
  · exact hF2

theorem colour_eq_cases_of_card_eq_six
    {B : Finset Point} (hcard : B.card = 6)
    (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 3} (hproper : ProperBlocking B colour)
    {x y z : B} (hxy : x ≠ y)
    (hxyColour : colour x = colour y)
    (hzColour : colour z = colour x) : z = x ∨ z = y := by
  classical
  let F := colourFiber colour (colour x)
  have hFcard : F.card = 2 :=
    colourFiber_card_eq_two_of_card_eq_six hcard hfour hproper (colour x)
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.mp hFcard
  have hx : x ∈ F := by simp [F]
  have hy : y ∈ F := by simp [F, hxyColour]
  have hz : z ∈ F := by simp [F, hzColour]
  rw [hF] at hx hy hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy hz
  aesop

theorem exists_other_same_colour_of_card_eq_six
    {B : Finset Point} (hcard : B.card = 6)
    (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 3} (hproper : ProperBlocking B colour)
    (x : B) : ∃ y : B, y ≠ x ∧ colour y = colour x := by
  classical
  let F := colourFiber colour (colour x)
  have hFcard : F.card = 2 :=
    colourFiber_card_eq_two_of_card_eq_six hcard hfour hproper (colour x)
  obtain ⟨a, b, hab, hF⟩ := Finset.card_eq_two.mp hFcard
  have hx : x ∈ F := by simp [F]
  rw [hF] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab.symm, by
      have hb : b ∈ F := by rw [hF]; simp
      exact mem_colourFiber.mp hb⟩
  · exact ⟨a, hab, by
      have : a ∈ F := by rw [hF]; simp
      exact mem_colourFiber.mp this⟩

/-- Four distinct points cannot realize two blocked pairs in the crossing
pattern used in the six-point structure argument. -/
theorem first_pair_points_do_not_block_second
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {a a' b b' : P}
    (haa' : a ≠ a') (hbb' : b ≠ b')
    (hab : a ≠ b) (hab' : a ≠ b')
    (ha'b : a' ≠ b) (ha'b' : a' ≠ b')
    (hb : (b : Point) ∈ openSegment ℝ (a : Point) (a' : Point)) :
    (a : Point) ∉ openSegment ℝ (b : Point) (b' : Point) ∧
      (a' : Point) ∉ openSegment ℝ (b : Point) (b' : Point) := by
  constructor
  · intro ha
    have ha'line : (a' : Point) ∈ affineSpan ℝ {(a : Point), (b : Point)} :=
      right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne haa') hb
    have hb'line0 : (b' : Point) ∈ affineSpan ℝ {(b : Point), (a : Point)} :=
      right_mem_affineSpan_pair_of_between
        (x := (b : Point)) (y := (b' : Point)) (z := (a : Point))
        (Subtype.val_injective.ne hbb') ha
    have hb'line : (b' : Point) ∈ affineSpan ℝ {(a : Point), (b : Point)} := by
      simpa [Set.pair_comm] using hb'line0
    have heq : (a' : Point) = (b' : Point) :=
      Lax56Proofs.Blockers.third_point_unique hfour a.property b.property
        a'.property b'.property (Subtype.val_injective.ne hab)
        (Subtype.val_injective.ne haa'.symm) (Subtype.val_injective.ne ha'b)
        (Subtype.val_injective.ne hab'.symm) (Subtype.val_injective.ne hbb'.symm)
        ha'line hb'line
    exact ha'b' (Subtype.ext heq)
  · intro ha'
    have hb' : (b : Point) ∈ openSegment ℝ (a' : Point) (a : Point) := by
      simpa only [openSegment_symm] using hb
    have haline : (a : Point) ∈ affineSpan ℝ {(a' : Point), (b : Point)} :=
      right_mem_affineSpan_pair_of_between (Subtype.val_injective.ne haa'.symm) hb'
    have hb'line0 : (b' : Point) ∈ affineSpan ℝ {(b : Point), (a' : Point)} :=
      right_mem_affineSpan_pair_of_between
        (x := (b : Point)) (y := (b' : Point)) (z := (a' : Point))
        (Subtype.val_injective.ne hbb') ha'
    have hb'line : (b' : Point) ∈ affineSpan ℝ {(a' : Point), (b : Point)} := by
      simpa [Set.pair_comm] using hb'line0
    have heq : (a : Point) = (b' : Point) :=
      Lax56Proofs.Blockers.third_point_unique hfour a'.property b.property
        a.property b'.property (Subtype.val_injective.ne ha'b)
        (Subtype.val_injective.ne haa') (Subtype.val_injective.ne hab)
        (Subtype.val_injective.ne ha'b'.symm) (Subtype.val_injective.ne hbb'.symm)
        haline hb'line
    exact hab' (Subtype.ext heq)

/-- Distinct extreme points of a six-point properly three-coloured blocking
set have different colours.  The proof follows the three colour-pairs around
their forced blocking cycle; a two-cycle would put four points on one line. -/
theorem extremePoints_colour_ne_of_card_eq_six
    {B : Finset Point} (hcard : B.card = 6)
    (hfour : ¬HasFourCollinear B)
    {colour : B → Fin 3} (hproper : ProperBlocking B colour)
    {x y : B}
    (hx : (x : Point) ∈ (convexHull ℝ (B : Set Point)).extremePoints ℝ)
    (hy : (y : Point) ∈ (convexHull ℝ (B : Set Point)).extremePoints ℝ)
    (hxy : x ≠ y) : colour x ≠ colour y := by
  intro hxyColour
  obtain ⟨z, hz⟩ := hproper x y hxy hxyColour
  have hzNotX : colour z ≠ colour x :=
    blocker_colour_ne hfour hproper hxy hxyColour hz
  obtain ⟨z', hzz', hz'Colour⟩ :=
    exists_other_same_colour_of_card_eq_six hcard hfour hproper z
  have hxz : x ≠ z := by
    intro e
    exact hzNotX (congrArg colour e.symm)
  have hxz' : x ≠ z' := by
    intro e
    apply hzNotX
    rw [← hz'Colour, ← e]
  have hyz : y ≠ z := by
    intro e
    apply hzNotX
    exact (congrArg colour e).symm.trans hxyColour.symm
  have hyz' : y ≠ z' := by
    intro e
    apply hzNotX
    exact hz'Colour.symm.trans (congrArg colour e).symm |>.trans hxyColour.symm
  obtain ⟨w, hw⟩ := hproper z z' hzz'.symm hz'Colour.symm
  have hwNotZ : colour w ≠ colour z :=
    blocker_colour_ne hfour hproper hzz'.symm hz'Colour.symm hw
  have hcross := first_pair_points_do_not_block_second hfour hxy hzz'.symm
    hxz hxz' hyz hyz' hz
  have hwx : w ≠ x := by
    intro e
    apply hcross.1
    simpa [e] using hw
  have hwy : w ≠ y := by
    intro e
    apply hcross.2
    simpa [e] using hw
  have hwNotX : colour w ≠ colour x := by
    intro hwc
    rcases colour_eq_cases_of_card_eq_six hcard hfour hproper hxy hxyColour
        hwc with h | h
    · exact hwx h
    · exact hwy h
  obtain ⟨w', hww', hw'Colour⟩ :=
    exists_other_same_colour_of_card_eq_six hcard hfour hproper w
  have hzw : z ≠ w := by
    intro e
    exact hwNotZ (congrArg colour e.symm)
  have hzw' : z ≠ w' := by
    intro e
    apply hwNotZ
    rw [← hw'Colour, ← e]
  have hz'w : z' ≠ w := by
    intro e
    apply hwNotZ
    rw [← hz'Colour, e]
  have hz'w' : z' ≠ w' := by
    intro e
    apply hwNotZ
    rw [← hz'Colour, e, hw'Colour]
  obtain ⟨t, ht⟩ := hproper w w' hww'.symm hw'Colour.symm
  have htNotW : colour t ≠ colour w :=
    blocker_colour_ne hfour hproper hww'.symm hw'Colour.symm ht
  have hcross' := first_pair_points_do_not_block_second hfour hzz'.symm hww'.symm
    hzw hzw' hz'w hz'w' hw
  have htz : t ≠ z := by
    intro e
    apply hcross'.1
    simpa [e] using ht
  have htz' : t ≠ z' := by
    intro e
    apply hcross'.2
    simpa [e] using ht
  have htNotZ : colour t ≠ colour z := by
    intro htc
    rcases colour_eq_cases_of_card_eq_six hcard hfour hproper hzz'.symm
        hz'Colour.symm htc with h | h
    · exact htz h
    · exact htz' h
  have hzxColour : colour z ≠ colour x := hzNotX
  have hwzColour : colour w ≠ colour z := hwNotZ
  have hwxColour : colour w ≠ colour x := hwNotX
  have htColour : colour t = colour x :=
    fin3_eq_of_avoids_two hwzColour hwxColour.symm hzxColour.symm
      htNotW htNotZ
  rcases colour_eq_cases_of_card_eq_six hcard hfour hproper hxy hxyColour
      htColour with htx | hty
  · have hxt : (x : Point) ∈ openSegment ℝ (w : Point) (w' : Point) := by
      simpa [htx] using ht
    have heq := hx.2 (subset_convexHull ℝ (B : Set Point) w.property)
      (subset_convexHull ℝ (B : Set Point) w'.property) hxt
    exact hwx (Subtype.ext heq)
  · have hyt : (y : Point) ∈ openSegment ℝ (w : Point) (w' : Point) := by
      simpa [hty] using ht
    have heq := hy.2 (subset_convexHull ℝ (B : Set Point) w.property)
      (subset_convexHull ℝ (B : Set Point) w'.property) hyt
    exact hwy (Subtype.ext heq)
/-- If one point in each of three pairs lies strictly between the preceding
pair, only the other three points can be extreme. -/
theorem extremePoints_subset_of_blocking_cycle
    {P : Finset Point} {a a' b b' c c' : P}
    (hcover : ∀ x : P,
      x = a ∨ x = a' ∨ x = b ∨ x = b' ∨ x = c ∨ x = c')
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hb : (b : Point) ∈ openSegment ℝ (a : Point) (a' : Point))
    (hc : (c : Point) ∈ openSegment ℝ (b : Point) (b' : Point))
    (ha : (a : Point) ∈ openSegment ℝ (c : Point) (c' : Point)) :
    (convexHull ℝ (P : Set Point)).extremePoints ℝ ⊆
      ({(a' : Point), (b' : Point), (c' : Point)} : Set Point) := by
  intro x hx
  have hxP : x ∈ (P : Set Point) := extremePoints_convexHull_subset hx
  let xs : P := ⟨x, hxP⟩
  rcases hcover xs with h | h | h | h | h | h
  · have hxa : x = (a : Point) := congrArg Subtype.val h
    subst x
    have heq := hx.2
      (subset_convexHull ℝ _ c.property)
      (subset_convexHull ℝ _ c'.property) ha
    exact (hca (Subtype.ext heq)).elim
  · have : x = (a' : Point) := congrArg Subtype.val h
    simp [this]
  · have hxb : x = (b : Point) := congrArg Subtype.val h
    subst x
    have heq := hx.2
      (subset_convexHull ℝ _ a.property)
      (subset_convexHull ℝ _ a'.property) hb
    exact (hab (Subtype.ext heq)).elim
  · have : x = (b' : Point) := congrArg Subtype.val h
    simp [this]
  · have hxc : x = (c : Point) := congrArg Subtype.val h
    subst x
    have heq := hx.2
      (subset_convexHull ℝ _ b.property)
      (subset_convexHull ℝ _ b'.property) hc
    exact (hbc (Subtype.ext heq)).elim
  · have : x = (c' : Point) := congrArg Subtype.val h
    simp [this]

theorem point_ne_of_colour_ne
    {B : Finset Point} {colour : B → Fin 3} {x y : B}
    (h : colour x ≠ colour y) : x ≠ y := by
  intro e
  exact h (congrArg colour e)

/-- Complete the blocking cycle once blockers in the second and third colour
classes have been fixed. -/
theorem extremePoints_subset_three_of_two_blockers
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 3} (hproper : ProperBlocking P colour)
    {a a' b b' c c' : P}
    (haa' : a ≠ a') (hbb' : b ≠ b') (hcc' : c ≠ c')
    (hcaa' : colour a = colour a')
    (hcbb' : colour b = colour b')
    (hccc' : colour c = colour c')
    (hcab : colour a ≠ colour b)
    (hcac : colour a ≠ colour c)
    (hcbc : colour b ≠ colour c)
    (hcover : ∀ x : P,
      x = a ∨ x = a' ∨ x = b ∨ x = b' ∨ x = c ∨ x = c')
    (hb : (b : Point) ∈ openSegment ℝ (a : Point) (a' : Point))
    (hc : (c : Point) ∈ openSegment ℝ (b : Point) (b' : Point)) :
    ∃ x y z : P,
      (convexHull ℝ (P : Set Point)).extremePoints ℝ ⊆
        ({(x : Point), (y : Point), (z : Point)} : Set Point) := by
  classical
  obtain ⟨e, he⟩ := hproper c c' hcc' hccc'
  have heNotC : colour e ≠ colour c :=
    blocker_colour_ne hfour hproper hcc' hccc' he
  have hbcross := first_pair_points_do_not_block_second hfour hbb' hcc'
    (point_ne_of_colour_ne hcbc)
    (point_ne_of_colour_ne (hcbc.trans_eq hccc'))
    (point_ne_of_colour_ne (hcbb'.symm.trans_ne hcbc))
    (point_ne_of_colour_ne (hcbb'.symm.trans_ne (hcbc.trans_eq hccc'))) hc
  rcases hcover e with hea | hea' | heb | heb' | hec | hec'
  · subst e
    refine ⟨a', b', c', ?_⟩
    exact extremePoints_subset_of_blocking_cycle hcover
      (point_ne_of_colour_ne hcab)
      (point_ne_of_colour_ne hcbc)
      (point_ne_of_colour_ne hcac.symm) hb hc he
  · subst e
    have hcover' : ∀ x : P,
        x = a' ∨ x = a ∨ x = b ∨ x = b' ∨ x = c ∨ x = c' := by
      intro x
      rcases hcover x with h | h | h | h | h | h <;> aesop
    refine ⟨a, b', c', ?_⟩
    exact extremePoints_subset_of_blocking_cycle hcover'
      (point_ne_of_colour_ne (hcaa'.symm.trans_ne hcab))
      (point_ne_of_colour_ne hcbc)
      (point_ne_of_colour_ne (hcaa'.symm.trans_ne hcac).symm)
      (by simpa only [openSegment_symm] using hb) hc he
  · subst e
    exact (hbcross.1 he).elim
  · subst e
    exact (hbcross.2 he).elim
  · subst e
    exact (heNotC rfl).elim
  · subst e
    exact (heNotC hccc'.symm).elim

/-- Complete the six-point structure once a blocker of the first colour pair
has been named in the second colour class. -/
theorem extremePoints_subset_three_of_first_blocker
    {P : Finset Point} (hfour : ¬HasFourCollinear P)
    {colour : P → Fin 3} (hproper : ProperBlocking P colour)
    {a a' b b' c c' : P}
    (haa' : a ≠ a') (hbb' : b ≠ b') (hcc' : c ≠ c')
    (hcaa' : colour a = colour a')
    (hcbb' : colour b = colour b')
    (hccc' : colour c = colour c')
    (hcab : colour a ≠ colour b)
    (hcac : colour a ≠ colour c)
    (hcbc : colour b ≠ colour c)
    (hcover : ∀ x : P,
      x = a ∨ x = a' ∨ x = b ∨ x = b' ∨ x = c ∨ x = c')
    (hb : (b : Point) ∈ openSegment ℝ (a : Point) (a' : Point)) :
    ∃ x y z : P,
      (convexHull ℝ (P : Set Point)).extremePoints ℝ ⊆
        ({(x : Point), (y : Point), (z : Point)} : Set Point) := by
  classical
  obtain ⟨d, hd⟩ := hproper b b' hbb' hcbb'
  have hdNotB : colour d ≠ colour b :=
    blocker_colour_ne hfour hproper hbb' hcbb' hd
  have hacross := first_pair_points_do_not_block_second hfour haa' hbb'
    (point_ne_of_colour_ne hcab)
    (point_ne_of_colour_ne (hcab.trans_eq hcbb'))
    (point_ne_of_colour_ne (hcaa'.symm.trans_ne hcab))
    (point_ne_of_colour_ne (hcaa'.symm.trans_ne (hcab.trans_eq hcbb'))) hb
  rcases hcover d with hda | hda' | hdb | hdb' | hdc | hdc'
  · subst d
    exact (hacross.1 hd).elim
  · subst d
    exact (hacross.2 hd).elim
  · subst d
    exact (hdNotB rfl).elim
  · subst d
    exact (hdNotB hcbb'.symm).elim
  · subst d
    exact extremePoints_subset_three_of_two_blockers hfour hproper
      haa' hbb' hcc' hcaa' hcbb' hccc' hcab hcac hcbc hcover hb hd
  · subst d
    have hcover' : ∀ x : P,
        x = a ∨ x = a' ∨ x = b ∨ x = b' ∨ x = c' ∨ x = c := by
      intro x
      rcases hcover x with h | h | h | h | h | h <;> aesop
    exact extremePoints_subset_three_of_two_blockers hfour hproper
      haa' hbb' hcc'.symm hcaa' hcbb' hccc'.symm hcab
      (hcac.trans_eq hccc') (hcbc.trans_eq hccc') hcover' hb hd

/-- Lemma 2.3: the convex hull of a properly three-coloured six-point
blocking set has at most three extreme points, stated as containment in an
explicit three-point set. -/
theorem extremePoints_subset_three_of_card_eq_six
    (P : Finset Point) (hcard : P.card = 6)
    (hfour : ¬HasFourCollinear P)
    (colour : P → Fin 3) (hproper : ProperBlocking P colour) :
    ∃ x y z : P,
      (convexHull ℝ (P : Set Point)).extremePoints ℝ ⊆
        ({(x : Point), (y : Point), (z : Point)} : Set Point) := by
  classical
  let F : Fin 3 → Finset P := colourFiber colour
  have hFle : ∀ d : Fin 3, (F d).card ≤ 2 := by
    intro d
    exact colourFiber_card_le_two hfour hproper d
  have htotal : 6 = ∑ d ∈ (Finset.univ : Finset (Fin 3)), (F d).card := by
    calc
      6 = P.card := hcard.symm
      _ = (Finset.univ : Finset P).card := by simp
      _ = ∑ d ∈ (Finset.univ : Finset (Fin 3)),
          ((Finset.univ : Finset P).filter fun p ↦ colour p = d).card := by
            apply Finset.card_eq_sum_card_fiberwise
            intro p hp
            simp
      _ = ∑ d ∈ (Finset.univ : Finset (Fin 3)), (F d).card := by
            rfl
  have hsum : (F 0).card + (F 1).card + (F 2).card = 6 := by
    simpa [Fin.sum_univ_succ, add_assoc] using htotal.symm
  have hFcard : ∀ d : Fin 3, (F d).card = 2 := by
    have h0 := hFle 0
    have h1 := hFle 1
    have h2 := hFle 2
    have hF0 : (F 0).card = 2 := by omega
    have hF1 : (F 1).card = 2 := by omega
    have hF2 : (F 2).card = 2 := by omega
    intro d
    fin_cases d
    · simpa using hF0
    · simpa using hF1
    · simpa using hF2
  obtain ⟨a, a', haa', hFa⟩ := Finset.card_eq_two.mp (hFcard 0)
  obtain ⟨b, b', hbb', hFb⟩ := Finset.card_eq_two.mp (hFcard 1)
  obtain ⟨c, c', hcc', hFc⟩ := Finset.card_eq_two.mp (hFcard 2)
  have hca : colour a = 0 := by
    apply mem_colourFiber.mp
    change a ∈ F 0
    rw [hFa]
    simp
  have hca' : colour a' = 0 := by
    apply mem_colourFiber.mp
    change a' ∈ F 0
    rw [hFa]
    simp
  have hcb : colour b = 1 := by
    apply mem_colourFiber.mp
    change b ∈ F 1
    rw [hFb]
    simp
  have hcb' : colour b' = 1 := by
    apply mem_colourFiber.mp
    change b' ∈ F 1
    rw [hFb]
    simp
  have hcc : colour c = 2 := by
    apply mem_colourFiber.mp
    change c ∈ F 2
    rw [hFc]
    simp
  have hcolc' : colour c' = 2 := by
    apply mem_colourFiber.mp
    change c' ∈ F 2
    rw [hFc]
    simp
  have hcover : ∀ x : P,
      x = a ∨ x = a' ∨ x = b ∨ x = b' ∨ x = c ∨ x = c' := by
    intro x
    generalize hxcol : colour x = d
    have hx : x ∈ F d := by
      change x ∈ colourFiber colour d
      exact mem_colourFiber.mpr hxcol
    fin_cases d
    · have hx0 : x ∈ F 0 := by simpa using hx
      rw [hFa] at hx0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx0
      rcases hx0 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hx1 : x ∈ F 1 := by simpa using hx
      rw [hFb] at hx1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx1
      rcases hx1 with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · have hx2 : x ∈ F 2 := by simpa using hx
      rw [hFc] at hx2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  have hcaa' : colour a = colour a' := hca.trans hca'.symm
  have hcbb' : colour b = colour b' := hcb.trans hcb'.symm
  have hccc' : colour c = colour c' := hcc.trans hcolc'.symm
  have hcab : colour a ≠ colour b := by rw [hca, hcb]; decide
  have hcac : colour a ≠ colour c := by rw [hca, hcc]; decide
  have hcbc : colour b ≠ colour c := by rw [hcb, hcc]; decide
  obtain ⟨d, hd⟩ := hproper a a' haa' hcaa'
  have hdNotA : colour d ≠ colour a :=
    blocker_colour_ne hfour hproper haa' hcaa' hd
  rcases hcover d with hda | hda' | hdb | hdb' | hdc | hdc'
  · subst d
    exact (hdNotA rfl).elim
  · subst d
    exact (hdNotA hcaa'.symm).elim
  · subst d
    exact extremePoints_subset_three_of_first_blocker hfour hproper
      haa' hbb' hcc' hcaa' hcbb' hccc' hcab hcac hcbc hcover hd
  · subst d
    have hcover' : ∀ x : P,
        x = a ∨ x = a' ∨ x = b' ∨ x = b ∨ x = c ∨ x = c' := by
      intro x
      rcases hcover x with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    exact extremePoints_subset_three_of_first_blocker hfour hproper
      haa' hbb'.symm hcc' hcaa' hcbb'.symm hccc'
      (hcab.trans_eq hcbb') hcac (hcbb'.symm.trans_ne hcbc)
      hcover' hd
  · subst d
    have hcover' : ∀ x : P,
        x = a ∨ x = a' ∨ x = c ∨ x = c' ∨ x = b ∨ x = b' := by
      intro x
      rcases hcover x with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    exact extremePoints_subset_three_of_first_blocker hfour hproper
      haa' hcc' hbb' hcaa' hccc' hcbb' hcac hcab hcbc.symm
      hcover' hd
  · subst d
    have hcover' : ∀ x : P,
        x = a ∨ x = a' ∨ x = c' ∨ x = c ∨ x = b ∨ x = b' := by
      intro x
      rcases hcover x with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inl h))
    exact extremePoints_subset_three_of_first_blocker hfour hproper
      haa' hcc'.symm hbb' hcaa' hccc'.symm hcbb'
      (hcac.trans_eq hccc') hcab (hccc'.symm.trans_ne hcbc.symm)
      hcover' hd

end Lax56Proofs.HKBSixStructure
