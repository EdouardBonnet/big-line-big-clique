import Lax56Proofs.CupsCaps
import Lax56Proofs.ConvexLayers
import Lax56Proofs.HKBGeometry

namespace Lax56Proofs.CupsCapsGeometry

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.Orientation Lax56Proofs.HKBGeometry
open Lax56Proofs.CupsCaps

/-- The two weighted-area identities behind cup/cap transitivity. -/
theorem turn_four_point_identities (a b c d : Point) (σ : ℝ) :
    (c.1 - b.1) * (σ * turn a b d) =
        (d.1 - b.1) * (σ * turn a b c) + (b.1 - a.1) * (σ * turn b c d) ∧
    (c.1 - b.1) * (σ * turn a c d) =
        (d.1 - c.1) * (σ * turn a b c) + (c.1 - a.1) * (σ * turn b c d) := by
  constructor <;> unfold turn <;> ring

theorem turn_four_point_pos {a b c d : Point} (σ : ℝ)
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : 0 < σ * turn a b c) (h₂ : 0 < σ * turn b c d) :
    0 < σ * turn a b d ∧ 0 < σ * turn a c d := by
  obtain ⟨heq₁, heq₂⟩ := turn_four_point_identities a b c d σ
  have hden : 0 < c.1 - b.1 := sub_pos.mpr hbc
  constructor
  · apply (mul_pos_iff_of_pos_left hden).mp
    rw [heq₁]
    exact add_pos (mul_pos (sub_pos.mpr (hbc.trans hcd)) h₁)
      (mul_pos (sub_pos.mpr hab) h₂)
  · apply (mul_pos_iff_of_pos_left hden).mp
    rw [heq₂]
    exact add_pos (mul_pos (sub_pos.mpr hcd) h₁)
      (mul_pos (sub_pos.mpr (hab.trans hbc)) h₂)

theorem turn_four_point_nonpos {a b c d : Point}
    (hab : a.1 < b.1) (hbc : b.1 < c.1) (hcd : c.1 < d.1)
    (h₁ : turn a b c ≤ 0) (h₂ : turn b c d ≤ 0) :
    turn a b d ≤ 0 ∧ turn a c d ≤ 0 := by
  obtain ⟨heq₁, heq₂⟩ := turn_four_point_identities a b c d 1
  simp only [one_mul] at heq₁ heq₂
  have hden : 0 < c.1 - b.1 := sub_pos.mpr hbc
  constructor
  · have hp : (c.1 - b.1) * turn a b d ≤ 0 := by
      rw [heq₁]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hbc.trans hcd).le) h₁)
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hab.le) h₂)
    nlinarith
  · have hp : (c.1 - b.1) * turn a c d ≤ 0 := by
      rw [heq₂]
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hcd.le) h₁)
        (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hab.trans hbc).le) h₂)
    nlinarith

/-- A strict affine supporting function excludes a point from a convex hull. -/
theorem not_mem_convexHull_of_support (Y : Set Point) (p : Point) (f : Point → ℝ)
    (hzero : f p = 0)
    (hcomb : ∀ x y : Point, ∀ u v : ℝ, u + v = 1 →
      f (u • x + v • y) = u * f x + v * f y)
    (hpos : ∀ y ∈ Y, 0 < f y) : p ∉ convexHull ℝ Y := by
  have hconv : Convex ℝ {y | 0 < f y} := by
    intro x hx y hy u v hu hv huv
    change 0 < f (u • x + v • y)
    rw [hcomb _ _ _ _ huv]
    rcases hu.eq_or_lt with rfl | hu
    · have hv1 : v = 1 := by linarith
      simpa [hv1] using hy
    · exact add_pos_of_pos_of_nonneg (mul_pos hu hx) (mul_nonneg hv hy.le)
  intro hp
  have := convexHull_min hpos hconv hp
  change 0 < f p at this
  rw [hzero] at this
  exact lt_irrefl _ this

theorem turn_consecutive_pos {n : ℕ} (v : Fin n → Point) (σ : ℝ)
    (htri : ∀ i j k, i < j → j < k → 0 < σ * turn (v i) (v j) (v k))
    (a b : Fin n) (hab : a.val + 1 = b.val)
    (j : Fin n) (hja : j ≠ a) (hjb : j ≠ b) : 0 < σ * turn (v a) (v b) (v j) := by
  have hab' : a < b := by omega
  by_cases haj : a < j
  · exact htri a b j hab' (by omega)
  · have h := htri j a b (by omega) hab'
    simpa only [turn_rotate] using h

/-- An increasing cup or cap with a consistent strict orientation is in
convex position. Internal vertices have a supporting function obtained by
adding the two incident edge functions; endpoints are separated by their
first coordinates. -/
theorem convexIndependent_of_strict_x_triples {n : ℕ} (v : Fin n → Point) (σ : ℝ)
    (hx : StrictMono (fun i ↦ (v i).1))
    (htri : ∀ i j k, i < j → j < k → 0 < σ * turn (v i) (v j) (v k)) :
    ConvexIndependent ℝ v := by
  apply convexIndependent_iff_notMem_convexHull_diff.mpr
  intro i S
  have hmem {p : Point} (hp : p ∈ v '' (S \ {i})) : ∃ j, j ≠ i ∧ p = v j := by
    obtain ⟨j, hj, rfl⟩ := hp
    exact ⟨j, hj.2, rfl⟩
  by_cases hi0 : i.val = 0
  · apply not_mem_convexHull_of_support _ (v i) (fun p ↦ p.1 - (v i).1) (by ring)
    · intro x y u w huw
      have hw : w = 1 - u := by linarith
      subst w
      simp
      ring
    · intro p hp
      obtain ⟨j, hji, rfl⟩ := hmem hp
      exact sub_pos.mpr (hx (by omega))
  by_cases hilast : i.val + 1 = n
  · apply not_mem_convexHull_of_support _ (v i) (fun p ↦ (v i).1 - p.1) (by ring)
    · intro x y u w huw
      have hw : w = 1 - u := by linarith
      subst w
      simp
      ring
    · intro p hp
      obtain ⟨j, hji, rfl⟩ := hmem hp
      exact sub_pos.mpr (hx (by omega))
  let a : Fin n := ⟨i.val - 1, by omega⟩
  let b : Fin n := ⟨i.val + 1, by omega⟩
  have hai : a.val + 1 = i.val := by dsimp [a]; omega
  have hib : i.val + 1 = b.val := rfl
  have hai' : a ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hbi' : b ≠ i := by intro h; have := congrArg Fin.val h; omega
  have hab' : a ≠ b := by intro h; have := congrArg Fin.val h; omega
  apply not_mem_convexHull_of_support _ (v i)
    (fun p ↦ σ * (turn (v a) (v i) p + turn (v i) (v b) p)) (by simp)
  · intro x y u w huw
    rw [turn_convex_combo _ _ _ _ _ _ huw, turn_convex_combo _ _ _ _ _ _ huw]
    ring
  · intro p hp
    obtain ⟨j, hji, rfl⟩ := hmem hp
    have hleft : 0 ≤ σ * turn (v a) (v i) (v j) := by
      by_cases hja : j = a
      · subst j; simp
      · exact (turn_consecutive_pos v σ htri a i hai j hja hji).le
    have hright : 0 ≤ σ * turn (v i) (v b) (v j) := by
      by_cases hjb : j = b
      · subst j; simp
      · exact (turn_consecutive_pos v σ htri i b hib j hji hjb).le
    by_cases hja : j = a
    · subst j
      have hpos := turn_consecutive_pos v σ htri i b hib a hai' hab'
      nlinarith
    · have hpos := turn_consecutive_pos v σ htri a i hai j hja hji
      nlinarith

theorem turn_ne_zero_of_generalPosition {P : Finset Point} (hgen : ¬HasThreeCollinear P)
    {a b c : Point} (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : turn a b c ≠ 0 := by
  intro hz
  apply hgen
  let f : Fin 3 → Point := ![c, a, b]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  · intro i
    fin_cases i <;> simp_all [f]
  · have hcol := collinear_insert_of_mem_affineSpan_pair (mem_line_of_turn_eq_zero hab hz)
    convert hcol using 1
    ext p
    simp [f, or_comm, or_left_comm, or_assoc]

/-- Converts a uniformly oriented list into a finite convex-position subset. -/
theorem convex_subset_of_oriented_list {P : Finset Point} (l : List P) (σ : ℝ)
    (hx : StrictMono (fun i : Fin l.length ↦ (l.get i).val.1))
    (htri : ∀ i j k : Fin l.length, i < j → j < k →
      0 < σ * turn (l.get i).val (l.get j).val (l.get k).val) :
    ∃ A ⊆ P, A.card = l.length ∧ ConvexPosition A := by
  classical
  let v : Fin l.length → Point := fun i ↦ (l.get i).val
  have hconv := convexIndependent_of_strict_x_triples v σ hx htri
  let A := Finset.univ.image v
  refine ⟨A, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (l.get i).property
  · simp [A, Finset.card_image_of_injective _ hconv.injective]
  · have heq : (A : Set Point) = Set.range v := by simp [A]
    have hr := hconv.range
    rw [← heq] at hr
    exact hr

/-- The geometric weak Erdős--Szekeres theorem when first coordinates are
distinct. Both the combinatorial recurrence and the cup/cap convexity bridge
are proved here; neither is an assumed Erdős--Szekeres theorem. -/
theorem exists_convex_of_strict_x (P : Finset Point) (k : ℕ) (hk : 2 ≤ k)
    (hgen : ¬HasThreeCollinear P)
    (hxinj : ∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p = q)
    (hcard : 2 ^ (2 * k - 4) < P.card) :
    ∃ A ⊆ P, A.card = k ∧ ConvexPosition A := by
  classical
  letI : LinearOrder P := LinearOrder.lift' (fun p : P ↦ p.val.1)
    (fun p q h ↦ Subtype.ext (hxinj p.val p.property q.val q.property h))
  let R : P → P → P → Prop := fun a b c ↦ 0 < turn a.val b.val c.val
  have htrans : TransitiveTriples R := by
    intro a b c d hab hbc hcd h₁ h₂
    simpa only [one_mul] using turn_four_point_pos 1 hab hbc hcd
      (by simpa only [one_mul] using h₁) (by simpa only [one_mul] using h₂)
  have htrans' : TransitiveTriples (fun a b c ↦ ¬R a b c) := by
    intro a b c d hab hbc hcd h₁ h₂
    simpa only [R, not_lt] using
      turn_four_point_nonpos hab hbc hcd (le_of_not_gt h₁) (le_of_not_gt h₂)
  have hbound : 2 ^ ((k - 2) + (k - 2)) < (Finset.univ : Finset P).card := by
    simpa only [Finset.card_univ, Fintype.card_coe,
      show k - 2 + (k - 2) = 2 * k - 4 by omega] using hcard
  rcases exists_chain_of_card_gt R Finset.univ (k - 2) (k - 2) hbound with hcup | hcap
  · obtain ⟨p, q, hc⟩ := hcup
    obtain ⟨l, hlen, _, hord, htri⟩ := hc.exists_list htrans
    have hx : StrictMono (fun i : Fin (p :: q :: l).length ↦ ((p :: q :: l).get i).val.1) :=
      List.pairwise_iff_get.mp hord
    obtain ⟨A, hAP, hAc, hA⟩ := convex_subset_of_oriented_list (p :: q :: l) 1 hx (by
      intro i j t hij hjt
      simpa only [one_mul, List.get_eq_getElem] using
        List.triplewise_iff_getElem.mp htri i.val j.val t.val hij hjt t.isLt)
    exact ⟨A, hAP, by omega, hA⟩
  · obtain ⟨p, q, hc⟩ := hcap
    obtain ⟨l, hlen, _, hord, htri⟩ := hc.exists_list htrans'
    have hx : StrictMono (fun i : Fin (p :: q :: l).length ↦ ((p :: q :: l).get i).val.1) :=
      List.pairwise_iff_get.mp hord
    obtain ⟨A, hAP, hAc, hA⟩ := convex_subset_of_oriented_list (p :: q :: l) (-1) hx (by
      intro i j t hij hjt
      let a := ((p :: q :: l).get i).val
      let b := ((p :: q :: l).get j).val
      let c := ((p :: q :: l).get t).val
      have hle : turn a b c ≤ 0 := le_of_not_gt
        (List.triplewise_iff_getElem.mp htri i.val j.val t.val hij hjt t.isLt)
      have hab : a ≠ b := fun h ↦ (ne_of_lt (hx hij)) (congrArg Prod.fst h)
      have hbc : b ≠ c := fun h ↦ (ne_of_lt (hx hjt)) (congrArg Prod.fst h)
      have hac : a ≠ c := fun h ↦ (ne_of_lt (hx (hij.trans hjt))) (congrArg Prod.fst h)
      have hne := turn_ne_zero_of_generalPosition hgen
        ((p :: q :: l).get i).property ((p :: q :: l).get j).property
        ((p :: q :: l).get t).property hab hac hbc
      change 0 < -1 * turn a b c
      change turn a b c ≠ 0 at hne
      simpa only [neg_one_mul] using neg_pos.mpr (lt_of_le_of_ne hle hne))
    exact ⟨A, hAP, by omega, hA⟩

end Lax56Proofs.CupsCapsGeometry
