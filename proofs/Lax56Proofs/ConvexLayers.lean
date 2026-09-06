import Lax56.ConvexLayers
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

namespace Lax56Proofs.ConvexLayers

open Lax56.Geometry Lax56.ConvexLayers
open scoped Classical

theorem convexPosition_iff (P : Finset Point) :
    ConvexPosition P ↔ ∀ p ∈ P, p ∉ convexHull ℝ ((P : Set Point) \ {p}) :=
  convexIndependent_set_iff_notMem_convexHull_diff

theorem convexPosition_mono {P Q : Finset Point} (hP : ConvexPosition P) (hQP : Q ⊆ P) :
    ConvexPosition Q := hP.mono hQP

@[simp] theorem coe_extremeLayer (P : Finset Point) :
    (extremeLayer P : Set Point) = (convexHull ℝ (P : Set Point)).extremePoints ℝ := by
  classical
  ext p
  simp only [extremeLayer, Finset.mem_coe, Finset.mem_filter]
  exact ⟨And.right, fun h ↦ ⟨extremePoints_convexHull_subset h, h⟩⟩

theorem extremeLayer_subset (P : Finset Point) : extremeLayer P ⊆ P :=
  Finset.filter_subset _ _

/-- The finite-dimensional finite-set form of Krein--Milman, with no closure left over. -/
@[simp] theorem convexHull_extremeLayer (P : Finset Point) :
    convexHull ℝ (extremeLayer P : Set Point) = convexHull ℝ (P : Set Point) := by
  have h := closure_convexHull_extremePoints
    (P.finite_toSet.isCompact_convexHull ℝ) (convex_convexHull ℝ (P : Set Point))
  rw [← coe_extremeLayer, (extremeLayer P).finite_toSet.isClosed_convexHull ℝ |>.closure_eq] at h
  exact h

theorem extremeLayer_convexPosition (P : Finset Point) : ConvexPosition (extremeLayer P) := by
  have h := (convex_convexHull ℝ (P : Set Point)).convexIndependent_extremePoints
  rw [← coe_extremeLayer] at h
  exact h

theorem extremeLayer_eq_self {P : Finset Point} (hP : ConvexPosition P) :
    extremeLayer P = P := by
  apply Finset.Subset.antisymm (extremeLayer_subset P)
  intro p hp
  exact (convexIndependent_set_iff_inter_convexHull_subset.mp hP)
    (extremeLayer P) (extremeLayer_subset P)
    ⟨hp, by rw [convexHull_extremeLayer]; exact subset_convexHull ℝ _ hp⟩

@[simp] theorem extremeLayer_eq_empty_iff (P : Finset Point) :
    extremeLayer P = ∅ ↔ P = ∅ := by
  constructor
  · intro h
    have heq := convexHull_extremeLayer P
    rw [h, Finset.coe_empty, convexHull_empty] at heq
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have := subset_convexHull ℝ (P : Set Point) hp
    rw [← heq] at this
    exact this
  · rintro rfl
    exact Finset.filter_empty _

theorem inner_subset (P : Finset Point) : inner P ⊆ P := Finset.sdiff_subset

/-- A removed vertex cannot lie in the convex hull of the remaining points. -/
theorem extreme_not_mem_convexHull_inner {P : Finset Point} {p : Point}
    (hp : p ∈ extremeLayer P) : p ∉ convexHull ℝ (inner P : Set Point) := by
  have hext : p ∈ (convexHull ℝ (P : Set Point)).extremePoints ℝ := by
    rwa [← coe_extremeLayer]
  have hdiff := ((convex_convexHull ℝ (P : Set Point)).mem_extremePoints_iff_convex_diff.mp
    hext).2
  intro h
  have hsub : (inner P : Set Point) ⊆ convexHull ℝ (P : Set Point) \ {p} := by
    intro q hq
    have hq' := Finset.mem_sdiff.mp hq
    refine ⟨subset_convexHull ℝ _ hq'.1, ?_⟩
    rintro rfl
    exact hq'.2 hp
  exact (convexHull_min hsub hdiff h).2 rfl

theorem inner_hullClosedIn (P : Finset Point) : HullClosedIn P (inner P) := by
  refine ⟨inner_subset P, ?_⟩
  intro p hp hh
  exact Finset.mem_sdiff.mpr ⟨hp, fun he ↦ extreme_not_mem_convexHull_inner he hh⟩

theorem hullClosedIn_trans {P Q R : Finset Point}
    (hPQ : HullClosedIn P Q) (hQR : HullClosedIn Q R) : HullClosedIn P R := by
  refine ⟨hQR.1.trans hPQ.1, ?_⟩
  intro p hp hh
  exact hQR.2 p (hPQ.2 p hp (convexHull_mono hQR.1 hh)) hh

theorem remainder_hullClosedIn (P : Finset Point) (n : ℕ) : HullClosedIn P (remainder P n) := by
  induction n with
  | zero => exact ⟨Finset.Subset.refl _, fun _ hp _ ↦ hp⟩
  | succ n ih => exact hullClosedIn_trans ih (inner_hullClosedIn _)

theorem emptyPolygon_transfer {P Q H : Finset Point} {k : ℕ}
    (hPQ : HullClosedIn P Q) (hH : EmptyPolygon Q H k) : EmptyPolygon P H k := by
  refine ⟨hH.1.trans hPQ.1, hH.2.1, hH.2.2.1, ?_⟩
  intro p hp hh
  exact hH.2.2.2 p (hPQ.2 p hp (convexHull_mono hH.1 hh)) hh

theorem hasEmptyHexagon_transfer {P Q : Finset Point}
    (hPQ : HullClosedIn P Q) (hQ : HasEmptyHexagon Q) : HasEmptyHexagon P := by
  obtain ⟨H, hH⟩ := hQ
  exact ⟨H, emptyPolygon_transfer hPQ hH⟩

/-- Any six vertices of a convex-position set form an empty hexagon of that set. -/
theorem hasEmptyHexagon_of_convexPosition {P : Finset Point}
    (hP : ConvexPosition P) (hcard : 6 ≤ P.card) : HasEmptyHexagon P := by
  obtain ⟨H, hHP, hHcard⟩ := Finset.exists_subset_card_eq hcard
  refine ⟨H, hHP, hHcard, convexPosition_mono hP hHP, ?_⟩
  intro p hp hh
  exact (convexIndependent_set_iff_inter_convexHull_subset.mp hP) H hHP ⟨hp, hh⟩

theorem hasThreeCollinear_mono {P Q : Finset Point} (hQP : Q ⊆ P)
    (hQ : HasThreeCollinear Q) : HasThreeCollinear P := by
  obtain ⟨f, hf, hmem, hcol⟩ := hQ
  exact ⟨f, hf, fun i ↦ hQP (hmem i), hcol⟩

@[simp] theorem mem_hullClosure {P A : Finset Point} {p : Point} :
    p ∈ hullClosure P A ↔ p ∈ P ∧ p ∈ convexHull ℝ (A : Set Point) :=
  Finset.mem_filter

theorem hullClosure_subset (P A : Finset Point) : hullClosure P A ⊆ P :=
  Finset.filter_subset _ _

theorem subset_hullClosure {P A : Finset Point} (hAP : A ⊆ P) : A ⊆ hullClosure P A := by
  intro p hp
  exact mem_hullClosure.mpr ⟨hAP hp, subset_convexHull ℝ _ hp⟩

theorem convexHull_hullClosure {P A : Finset Point} (hAP : A ⊆ P) :
    convexHull ℝ (hullClosure P A : Set Point) = convexHull ℝ (A : Set Point) := by
  apply Set.Subset.antisymm
  · exact convexHull_min (fun _ h ↦ (mem_hullClosure.mp h).2) (convex_convexHull ℝ _)
  · exact convexHull_mono (subset_hullClosure hAP)

theorem hullClosure_hullClosedIn (P A : Finset Point) : HullClosedIn P (hullClosure P A) := by
  refine ⟨hullClosure_subset P A, ?_⟩
  intro p hp hh
  refine mem_hullClosure.mpr ⟨hp, ?_⟩
  exact convexHull_min (fun _ h ↦ (mem_hullClosure.mp h).2) (convex_convexHull ℝ _) hh

theorem extremeLayer_hullClosure {P A : Finset Point} (hAP : A ⊆ P)
    (hA : ConvexPosition A) : extremeLayer (hullClosure P A) = A := by
  have h := extremeLayer_eq_self hA
  apply Finset.coe_injective
  rw [coe_extremeLayer, convexHull_hullClosure hAP, ← coe_extremeLayer, h]

/-- Extremality excludes a vertex from the hull of *any* subset omitting it,
including subsets which contain non-vertex points. -/
theorem extreme_not_mem_convexHull {S Y : Finset Point} {a : Point}
    (ha : a ∈ extremeLayer S) (hYS : Y ⊆ S) (haY : a ∉ Y) :
    a ∉ convexHull ℝ (Y : Set Point) := by
  have hext : a ∈ (convexHull ℝ (S : Set Point)).extremePoints ℝ := by
    rwa [← coe_extremeLayer]
  have hdiff := ((convex_convexHull ℝ (S : Set Point)).mem_extremePoints_iff_convex_diff.mp
    hext).2
  intro hh
  have hsub : (Y : Set Point) ⊆ convexHull ℝ (S : Set Point) \ {a} := by
    intro y hy
    refine ⟨subset_convexHull ℝ _ (hYS hy), ?_⟩
    rintro rfl
    exact haY hy
  exact (convexHull_min hsub hdiff hh).2 rfl

/-- Lemma 1 of the proposed formalization: minimize the *integer* number of
ambient points in the closed hull. The strict descent has an explicit omitted
outer vertex as witness; no area minimization or general position is needed. -/
theorem exists_minimal_polygon (P : Finset Point) (k : ℕ)
    (hex : ∃ A ⊆ P, A.card = k ∧ ConvexPosition A) :
    ∃ A ⊆ P, A.card = k ∧ ConvexPosition A ∧
      extremeLayer (hullClosure P A) = A ∧ MinimalOuter (hullClosure P A) := by
  classical
  let choices := P.powerset.filter (fun A ↦ A.card = k ∧ ConvexPosition A)
  have hchoices : choices.Nonempty := by
    obtain ⟨A, hAP, hAk, hA⟩ := hex
    exact ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hAP, hAk, hA⟩⟩
  obtain ⟨A, hAc, hmin⟩ := choices.exists_min_image (fun A ↦ (hullClosure P A).card) hchoices
  obtain ⟨hAP, hAk, hA⟩ : A ⊆ P ∧ A.card = k ∧ ConvexPosition A := by
    simpa only [choices, Finset.mem_filter, Finset.mem_powerset] using hAc
  have hext := extremeLayer_hullClosure hAP hA
  refine ⟨A, hAP, hAk, hA, hext, ?_⟩
  intro X hXS hX hcard
  rw [hext] at hcard ⊢
  by_contra hXA
  have hnot : ¬A ⊆ X := by
    intro hAX
    apply hXA
    apply Finset.Subset.antisymm _ hAX
    intro x hx
    exact (convexIndependent_set_iff_inter_convexHull_subset.mp hX) A hAX
      ⟨hx, (mem_hullClosure.mp (hXS hx)).2⟩
  obtain ⟨a, haA, haX⟩ := Finset.not_subset.mp hnot
  obtain ⟨Y, hYX, hYk⟩ := Finset.exists_subset_card_eq (hAk ▸ hcard)
  have hYP : Y ⊆ P := hYX.trans (hXS.trans (hullClosure_subset P A))
  have hYc : Y ∈ choices :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYP, hYk, convexPosition_mono hX hYX⟩
  have hsub : hullClosure P Y ⊆ hullClosure P A := by
    intro p hp
    obtain ⟨hpP, hpY⟩ := mem_hullClosure.mp hp
    refine mem_hullClosure.mpr ⟨hpP, ?_⟩
    exact convexHull_min (fun y hy ↦ (mem_hullClosure.mp (hXS (hYX hy))).2)
      (convex_convexHull ℝ _) hpY
  have haS : a ∈ hullClosure P A := subset_hullClosure hAP haA
  have haY : a ∉ hullClosure P Y := by
    intro h
    apply extreme_not_mem_convexHull (hext.symm ▸ haA) (hYX.trans hXS)
      (fun hy ↦ haX (hYX hy))
    exact (mem_hullClosure.mp h).2
  have hlt : (hullClosure P Y).card < (hullClosure P A).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun heq ↦ haY (heq.symm ▸ haS)⟩)
  exact (not_lt_of_ge (hmin Y hYc)) hlt

@[simp] theorem remainder_add (P : Finset Point) (i j : ℕ) :
    remainder P (i + j) = remainder (remainder P i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change inner (remainder P (i + j)) = inner (remainder (remainder P i) j)
    rw [ih]

theorem remainder_subset_inner (P : Finset Point) (n : ℕ) :
    remainder P (n + 1) ⊆ inner P := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (inner_subset _).trans ih

/-- A later layer contains none of the vertices removed at an earlier step. -/
theorem layer_disjoint {P : Finset Point} {i j : ℕ} (hij : i < j) :
    Disjoint (layer P i) (layer P j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hp : p ∈ inner (remainder P i) := by
    apply remainder_subset_inner (remainder P i) n
    have h := extremeLayer_subset _ hpj
    simpa only [layer, remainder_add, Nat.add_assoc] using h
  exact (Finset.mem_sdiff.mp hp).2 hpi

/-- Minimality strictly bounds every different convex-position subset. -/
theorem card_lt_outer_of_convexPosition {S X : Finset Point}
    (hmin : MinimalOuter S) (hXS : X ⊆ S) (hX : ConvexPosition X)
    (hne : X ≠ extremeLayer S) : X.card < (extremeLayer S).card := by
  by_contra h
  exact hne (hmin X hXS hX (Nat.le_of_not_gt h))

/-- In particular every non-outer layer has fewer vertices than a nonempty
minimal outer layer. This is the cardinality contradiction used by Valtr. -/
theorem layer_card_lt_outer {S : Finset Point} (hmin : MinimalOuter S)
    (hS : S.Nonempty) {n : ℕ} (hn : 0 < n) :
    (layer S n).card < (extremeLayer S).card := by
  apply card_lt_outer_of_convexPosition hmin
    ((extremeLayer_subset _).trans (remainder_hullClosedIn S n).1)
    (extremeLayer_convexPosition _) _
  intro heq
  have hd := layer_disjoint (P := S) hn
  change Disjoint (extremeLayer S) (extremeLayer (remainder S n)) at hd
  rw [heq] at hd
  have he : extremeLayer S = ∅ := disjoint_self.mp hd
  exact hS.ne_empty ((extremeLayer_eq_empty_iff S).mp he)

/-- Valtr's Observation 1 in a boundary-safe form: after excluding the
outer vertices and the closed hull of the fourth layer, only layers two
and three can remain. No general-position assumption is needed. -/
theorem mem_middle_layers_of_not_mem_fourth_hull {S : Finset Point} {p : Point}
    (hp : p ∈ S) (hpouter : p ∉ extremeLayer S)
    (hpfourth : p ∉ convexHull ℝ (layer S 3 : Set Point)) :
    p ∈ layer S 1 ∨ p ∈ layer S 2 := by
  by_cases hpone : p ∈ layer S 1
  · exact Or.inl hpone
  by_cases hptwo : p ∈ layer S 2
  · exact Or.inr hptwo
  have hpfirst : p ∈ remainder S 1 := Finset.mem_sdiff.mpr ⟨hp, hpouter⟩
  have hpsecond : p ∈ remainder S 2 := Finset.mem_sdiff.mpr ⟨hpfirst, hpone⟩
  have hpthird : p ∈ remainder S 3 := Finset.mem_sdiff.mpr ⟨hpsecond, hptwo⟩
  apply (hpfourth _).elim
  change p ∈ convexHull ℝ (extremeLayer (remainder S 3) : Set Point)
  rw [convexHull_extremeLayer]
  exact subset_convexHull ℝ _ hpthird

end Lax56Proofs.ConvexLayers
