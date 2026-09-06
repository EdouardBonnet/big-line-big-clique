import Lax56Proofs.ValtrSelection
import Lax56Proofs.ValtrMaximum

namespace Lax56Proofs.ValtrProjective

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrCaps Lax56Proofs.ValtrExtension Lax56Proofs.ValtrSelection
open Lax56Proofs.ValtrMaximum
open scoped Classical

/-- A projective coordinate viewed from `x`, with a strictly positive
height functional on the polygon and a positive-height reference `r`.
Only this real-valued function is used, not a projective transformation. -/
noncomputable def projectiveValue (l : Point →ₗ[ℝ] ℝ) (x r p : Point) : ℝ :=
  turn x r p / (l p - l x)

theorem projective_determinant_identity (l : Point →ₗ[ℝ] ℝ) (x r u v : Point) :
    (l r - l x) * turn u v x =
      (l u - l x) * turn x r v - (l v - l x) * turn x r u := by
  have h := linear_triangle_identity l u x v r
  have h₁ : turn u x v = -turn u v x := by rw [turn_swap_last]
  have h₂ : turn x v r = -turn x r v := by rw [turn_swap_last]
  have h₃ : turn u x r = turn x r u := by unfold turn; ring
  rw [h₁, h₂, h₃] at h
  nlinarith

theorem projectiveValue_lt_iff (l : Point →ₗ[ℝ] ℝ) {x r u v : Point}
    (hr : l x < l r) (hu : l x < l u) (hv : l x < l v) :
    projectiveValue l x r u < projectiveValue l x r v ↔ 0 < turn u v x := by
  unfold projectiveValue
  rw [div_lt_div_iff₀ (sub_pos.mpr hu) (sub_pos.mpr hv)]
  have h := projective_determinant_identity l x r u v
  constructor
  · intro hh
    apply (mul_pos_iff_of_pos_left (sub_pos.mpr hr)).mp
    nlinarith
  · intro hh
    have hp := mul_pos (sub_pos.mpr hr) hh
    nlinarith

theorem projectiveValue_ne (l : Point →ₗ[ℝ] ℝ) {x r u v : Point}
    (hr : l x < l r) (hu : l x < l u) (hv : l x < l v)
    (hne : turn u v x ≠ 0) : projectiveValue l x r u ≠ projectiveValue l x r v := by
  intro heq
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hpos' : 0 < turn v u x := by rw [turn_swap_first]; exact neg_pos.mpr hneg
    have hlt := (projectiveValue_lt_iff l hr hv hu).mpr hpos'
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  · exact (ne_of_lt ((projectiveValue_lt_iff l hr hu hv).mpr hpos)) heq

/-- A hull point cannot be a strict projective maximum or minimum of
its generators. This is the weighted-average step of the informal
argument, proved using an affine half-plane and convex-hull minimality. -/
theorem projectiveValue_between_generators (l : Point →ₗ[ℝ] ℝ)
    {x r p : Point} {N : Set Point} (hr : l x < l r) (hpY : l x < l p)
    (hNY : ∀ q ∈ N, l x < l q) (hp : p ∈ convexHull ℝ N)
    (hne : ∀ q ∈ N, turn p q x ≠ 0) :
    (∃ q ∈ N, projectiveValue l x r q < projectiveValue l x r p) ∧
      ∃ q ∈ N, projectiveValue l x r p < projectiveValue l x r q := by
  let Y : Point →ᵃ[ℝ] ℝ := l.toAffineMap - AffineMap.const ℝ Point (l x)
  let f : Point →ᵃ[ℝ] ℝ := turnAffine x r - projectiveValue l x r p • Y
  have hf (q) : f q = turn x r q - projectiveValue l x r p * (l q - l x) := rfl
  have hfp : f p = 0 := by
    rw [hf]
    unfold projectiveValue
    rw [div_mul_cancel₀ _ (sub_pos.mpr hpY).ne']
    ring
  have hneq (q) (hq : q ∈ N) :
      projectiveValue l x r p ≠ projectiveValue l x r q :=
    projectiveValue_ne l hr hpY (hNY q hq) (hne q hq)
  constructor
  · by_contra hh
    push Not at hh
    have hpos : ∀ q ∈ N, 0 < f q := by
      intro q hq
      have hlt : projectiveValue l x r p < projectiveValue l x r q :=
        lt_of_le_of_ne (hh q hq) (hneq q hq)
      have h := (lt_div_iff₀ (sub_pos.mpr (hNY q hq))).mp hlt
      rw [hf]
      linarith
    have h := convexHull_min hpos ((convex_Ioi (0 : ℝ)).affine_preimage f) hp
    change 0 < f p at h
    rw [hfp] at h
    exact (lt_irrefl _ h)
  · by_contra hh
    push Not at hh
    have hneg : ∀ q ∈ N, f q < 0 := by
      intro q hq
      have hlt : projectiveValue l x r q < projectiveValue l x r p :=
        lt_of_le_of_ne (hh q hq) (hneq q hq).symm
      have h := (div_lt_iff₀ (sub_pos.mpr (hNY q hq))).mp hlt
      rw [hf]
      linarith
    have h := convexHull_min hneg ((convex_Iio (0 : ℝ)).affine_preimage f) hp
    change f p < 0 at h
    rw [hfp] at h
    exact (lt_irrefl _ h)

theorem exists_positive_height_of_not_mem_hull {B : Finset Point} {x : Point}
    (hx : x ∉ convexHull ℝ (B : Set Point)) :
    ∃ l : Point →ₗ[ℝ] ℝ, ∀ p ∈ convexHull ℝ (B : Set Point), l x < l p := by
  obtain ⟨l, a, hxa, ha⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (B : Set Point)) (B.finite_toSet.isClosed_convexHull ℝ) hx
  exact ⟨l.toLinearMap, fun p hp ↦ hxa.trans (ha p hp)⟩

/-- In a common positive-height chart, the three determinant tests for
a sector are exactly an increasing interval of projective values. -/
theorem sector_iff_projective_interval (l : Point →ₗ[ℝ] ℝ) {x r a c b : Point}
    (hr : l x < l r) (ha : l x < l a) (hc : l x < l c) (hb : l x < l b) :
    x ∈ sector ![a, c, b] ↔
      projectiveValue l x r a < projectiveValue l x r c ∧
      projectiveValue l x r c < projectiveValue l x r b := by
  constructor
  · intro hx
    exact ⟨(projectiveValue_lt_iff l hr ha hc).mpr (hx 0 1 (by decide)),
      (projectiveValue_lt_iff l hr hc hb).mpr (hx 1 2 (by decide))⟩
  · rintro ⟨hac, hcb⟩
    have h₁ := (projectiveValue_lt_iff l hr ha hc).mp hac
    have h₂ := (projectiveValue_lt_iff l hr hc hb).mp hcb
    have h₃ := (projectiveValue_lt_iff l hr ha hb).mp (hac.trans hcb)
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> assumption

/-- The geometric maximum principle in a positive-height chart. The
only local geometric assumption is membership in the hull of the four
neighbors. The initial condition also allows a known first descent,
which is needed when the viewpoint is a chain endpoint. -/
theorem chain_support_of_positive_height (l : Point →ₗ[ℝ] ℝ)
    (h b : ℕ → Point) {m : ℕ} (hm : 0 < m) {x r : Point}
    (hr : l x < l r)
    (hY : ∀ k, k ≤ m + 1 → l x < l (h k))
    (hbY : ∀ k, 1 ≤ k → k ≤ m + 1 → l x < l (b k))
    (hlast : h (m + 1) = b (m + 1) ∨ turn (h m) (h (m + 1)) x < 0)
    (hfirst : h 0 = b 1 ∨ turn (h 0) (h 1) x < 0)
    (hlocal : ∀ k, 1 ≤ k → k ≤ m → h k ∈ convexHull ℝ
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point))
    (hnext : ∀ k, k ≤ m → turn (h k) (h (k + 1)) x ≠ 0)
    (hne : ∀ k, 1 ≤ k → k ≤ m → ∀ q ∈
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), turn (h k) q x ≠ 0)
    (hout : ∀ k, 1 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)]) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) x < 0 := by
  let z : ℕ → ℝ := fun k ↦ projectiveValue l x r (h k)
  let a : ℕ → ℝ := fun k ↦ projectiveValue l x r (b k)
  have hbetween (k) (hk : 1 ≤ k) (hkm : k ≤ m) :
      (z (k - 1) < z k ∨ a k < z k ∨ a (k + 1) < z k ∨ z (k + 1) < z k) ∧
      (z k < z (k - 1) ∨ z k < a k ∨ z k < a (k + 1) ∨ z k < z (k + 1)) := by
    have hNY : ∀ q ∈ ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), l x < l q := by
      intro q hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact hY _ (by omega)
      · exact hbY _ hk (by omega)
      · exact hbY _ (by omega) (by omega)
      · exact hY _ (by omega)
    obtain ⟨⟨q, hq, hqz⟩, ⟨p, hp, hzp⟩⟩ := projectiveValue_between_generators l hr
      (hY k (by omega)) hNY (hlocal k hk hkm) (hne k hk hkm)
    constructor
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl | rfl
      · exact Or.inl hqz
      · exact Or.inr (Or.inl hqz)
      · exact Or.inr (Or.inr (Or.inl hqz))
      · exact Or.inr (Or.inr (Or.inr hqz))
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact Or.inl hzp
      · exact Or.inr (Or.inl hzp)
      · exact Or.inr (Or.inr (Or.inl hzp))
      · exact Or.inr (Or.inr (Or.inr hzp))
  have hlast' : z (m + 1) = a (m + 1) ∨ z (m + 1) < z m := by
    rcases hlast with hh | hh
    · exact Or.inl (by dsimp only [z, a]; rw [hh])
    · apply Or.inr
      apply (projectiveValue_lt_iff l hr (hY (m + 1) le_rfl) (hY m (by omega))).mpr
      rw [turn_swap_first]
      exact neg_pos.mpr hh
  have hfirst' : z 0 = a 1 ∨ z 1 < z 0 := by
    rcases hfirst with hh | hh
    · exact Or.inl (by dsimp only [z, a]; rw [hh])
    · apply Or.inr
      apply (projectiveValue_lt_iff l hr (hY 1 (by omega)) (hY 0 (by omega))).mpr
      rw [turn_swap_first]
      exact neg_pos.mpr hh
  have hdescent := scalar_chain_strictly_decreasing_of_endpoint_conditions z a hm hlast'
    (fun k hk hkm ↦ (hbetween k hk hkm).1)
    (fun k hk hkm ↦ (hbetween k hk hkm).2)
    (fun k hk ↦ projectiveValue_ne l hr (hY k (by omega)) (hY (k + 1) (by omega)) (hnext k hk))
    (fun k hk hkm ↦ ⟨projectiveValue_ne l hr (hY k (by omega)) (hbY k hk (by omega))
      (hne k hk hkm _ (by simp)),
      projectiveValue_ne l hr (hY k (by omega)) (hbY (k + 1) (by omega) (by omega))
      (hne k hk hkm _ (by simp))⟩)
    (fun k hk hkm hh ↦ hout k hk hkm
      ((sector_iff_projective_interval l hr (hbY k hk (by omega))
        (hY k (by omega)) (hbY (k + 1) (by omega) (by omega))).mpr hh)) hfirst'
  intro k hk
  have hpos := (projectiveValue_lt_iff l hr (hY (k + 1) (by omega))
    (hY k (by omega))).mp (hdescent k hk)
  rw [turn_swap_first] at hpos
  exact neg_pos.mp hpos

/-- Every exterior point outside the removed sectors is strictly right
of every directed chain edge. Strict separation supplies the positive
chart; no minimality or hexagon-free assumption is used. -/
theorem exterior_chain_support {B : Finset Point} (h b : ℕ → Point)
    {m : ℕ} (hm : 0 < m) {x : Point}
    (hx : x ∉ convexHull ℝ (B : Set Point))
    (hmem : ∀ k, k ≤ m + 1 → h k ∈ convexHull ℝ (B : Set Point))
    (hbmem : ∀ k, 1 ≤ k → k ≤ m + 1 → b k ∈ convexHull ℝ (B : Set Point))
    (hlast : h (m + 1) = b (m + 1)) (hfirst : h 0 = b 1)
    (hlocal : ∀ k, 1 ≤ k → k ≤ m → h k ∈ convexHull ℝ
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point))
    (hnext : ∀ k, k ≤ m → turn (h k) (h (k + 1)) x ≠ 0)
    (hne : ∀ k, 1 ≤ k → k ≤ m → ∀ q ∈
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), turn (h k) q x ≠ 0)
    (hout : ∀ k, 1 ≤ k → k ≤ m → x ∉ sector ![b k, h k, b (k + 1)]) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) x < 0 := by
  obtain ⟨l, hl⟩ := exists_positive_height_of_not_mem_hull hx
  exact chain_support_of_positive_height l h b hm (hl _ (hmem 0 (by omega)))
    (fun k hk ↦ hl _ (hmem k hk)) (fun k hk hkm ↦ hl _ (hbmem k hk hkm))
    (Or.inl hlast) (Or.inl hfirst) hlocal hnext hne hout

/-- An endpoint viewpoint can be handled by dropping that endpoint
from the scalar chain. Its strict supporting functional is positive on
all remaining vertices; a known first descent replaces the first
endpoint equality. -/
theorem first_endpoint_chain_support {B : Finset Point} (hB : ConvexPosition B)
    (h b : ℕ → Point) {m : ℕ} (hm : 2 ≤ m) (hzero : h 0 ∈ B)
    (hmem : ∀ k, 1 ≤ k → k ≤ m + 1 → h k ∈ convexHull ℝ (B : Set Point))
    (hbmem : ∀ k, 2 ≤ k → k ≤ m + 1 → b k ∈ convexHull ℝ (B : Set Point))
    (hhne : ∀ k, 1 ≤ k → k ≤ m + 1 → h k ≠ h 0)
    (hbne : ∀ k, 2 ≤ k → k ≤ m + 1 → b k ≠ h 0)
    (hlast : h (m + 1) = b (m + 1))
    (hfirst : turn (h 1) (h 2) (h 0) < 0)
    (hlocal : ∀ k, 2 ≤ k → k ≤ m → h k ∈ convexHull ℝ
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point))
    (hnext : ∀ k, 1 ≤ k → k ≤ m → turn (h k) (h (k + 1)) (h 0) ≠ 0)
    (hne : ∀ k, 2 ≤ k → k ≤ m → ∀ q ∈
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), turn (h k) q (h 0) ≠ 0)
    (hout : ∀ k, 2 ≤ k → k ≤ m → h 0 ∉ sector ![b k, h k, b (k + 1)]) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) (h 0) ≤ 0 := by
  obtain ⟨l, hl⟩ := exists_strict_linear_support hB hzero
  have hY (k) (hk : 1 ≤ k) (hkm : k ≤ m + 1) : l (h 0) < l (h k) :=
    linear_support_strict_on_hull hzero l hl (hmem k hk hkm) (hhne k hk hkm)
  have hbY (k) (hk : 2 ≤ k) (hkm : k ≤ m + 1) : l (h 0) < l (b k) :=
    linear_support_strict_on_hull hzero l hl (hbmem k hk hkm) (hbne k hk hkm)
  have hend : m - 1 + 1 = m := by omega
  have hhlocal (k) (hk : 1 ≤ k) (hkm : k ≤ m - 1) :
      h (k + 1) ∈ convexHull ℝ
        ({h (k - 1 + 1), b (k + 1), b (k + 1 + 1), h (k + 1 + 1)} : Set Point) := by
    simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel hk] using
      hlocal (k + 1) (by omega) (by omega)
  have hhnext (k) (hk : k ≤ m - 1) :
      turn (h (k + 1)) (h (k + 1 + 1)) (h 0) ≠ 0 := hnext _ (by omega) (by omega)
  have hhne' (k) (hk : 1 ≤ k) (hkm : k ≤ m - 1) : ∀ q ∈
      ({h (k - 1 + 1), b (k + 1), b (k + 1 + 1), h (k + 1 + 1)} : Set Point),
      turn (h (k + 1)) q (h 0) ≠ 0 := by
    simpa only [Nat.add_sub_cancel, Nat.sub_add_cancel hk] using
      hne (k + 1) (by omega) (by omega)
  have hdescent := chain_support_of_positive_height l (fun k ↦ h (k + 1))
    (fun k ↦ b (k + 1)) (m := m - 1) (by omega) (hY 1 (by decide) (by omega))
    (fun k hk ↦ hY _ (by omega) (by omega))
    (fun k hk hkm ↦ hbY _ (by omega) (by omega))
    (Or.inl (by simpa only [hend] using hlast)) (Or.inr hfirst)
    hhlocal hhnext hhne' (fun k hk hkm ↦ hout _ (by omega) (by omega))
  intro k hk
  by_cases hk0 : k = 0
  · subst k; simp
  have h := hdescent (k - 1) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using h.le

/-- The last endpoint is handled by the terminal-descent form of the
same scalar maximum principle. No limiting argument or reflected
geometric configuration is required. -/
theorem last_endpoint_chain_support {B : Finset Point} (hB : ConvexPosition B)
    (h b : ℕ → Point) {m : ℕ} (hm : 2 ≤ m) (hend : h (m + 1) ∈ B)
    (hmem : ∀ k, k ≤ m → h k ∈ convexHull ℝ (B : Set Point))
    (hbmem : ∀ k, 1 ≤ k → k ≤ m → b k ∈ convexHull ℝ (B : Set Point))
    (hhne : ∀ k, k ≤ m → h k ≠ h (m + 1))
    (hbne : ∀ k, 1 ≤ k → k ≤ m → b k ≠ h (m + 1))
    (hfirst : h 0 = b 1)
    (hlast : turn (h (m - 1)) (h m) (h (m + 1)) < 0)
    (hlocal : ∀ k, 1 ≤ k → k < m → h k ∈ convexHull ℝ
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point))
    (hnext : ∀ k, k < m → turn (h k) (h (k + 1)) (h (m + 1)) ≠ 0)
    (hne : ∀ k, 1 ≤ k → k < m → ∀ q ∈
      ({h (k - 1), b k, b (k + 1), h (k + 1)} : Set Point), turn (h k) q (h (m + 1)) ≠ 0)
    (hout : ∀ k, 1 ≤ k → k < m → h (m + 1) ∉ sector ![b k, h k, b (k + 1)]) :
    ∀ k, k ≤ m → turn (h k) (h (k + 1)) (h (m + 1)) ≤ 0 := by
  obtain ⟨l, hl⟩ := exists_strict_linear_support hB hend
  have hY (k) (hk : k ≤ m) : l (h (m + 1)) < l (h k) :=
    linear_support_strict_on_hull hend l hl (hmem k hk) (hhne k hk)
  have hbY (k) (hk : 1 ≤ k) (hkm : k ≤ m) : l (h (m + 1)) < l (b k) :=
    linear_support_strict_on_hull hend l hl (hbmem k hk hkm) (hbne k hk hkm)
  have hidx : m - 1 + 1 = m := by omega
  have hdescent := chain_support_of_positive_height l h b (m := m - 1) (by omega)
    (hY 0 (by omega)) (fun k hk ↦ hY k (by omega))
    (fun k hk hkm ↦ hbY k hk (by omega))
    (Or.inr (by simpa only [hidx] using hlast)) (Or.inl hfirst)
    (fun k hk hkm ↦ hlocal k hk (by omega))
    (fun k hk ↦ hnext k (by omega))
    (fun k hk hkm ↦ hne k hk (by omega))
    (fun k hk hkm ↦ hout k hk (by omega))
  intro k hk
  by_cases hkm : k = m
  · subst k; simp
  exact (hdescent k (by omega)).le

end Lax56Proofs.ValtrProjective
