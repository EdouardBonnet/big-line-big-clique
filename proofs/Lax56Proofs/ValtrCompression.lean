import Lax56Proofs.ValtrMatching

namespace Lax56Proofs.ValtrCompression

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrSelection Lax56Proofs.ValtrProjective
open scoped Classical

/-- A point in the hull of nontrivial points of its own star lies in
the hull of the star's other generators. Strict separation eliminates
the apparent self-reference in the containing star triangles. -/
theorem mem_hull_of_star_generators {P N : Finset Point} {d : Point}
    (hd : d ∈ convexHull ℝ (P : Set Point))
    (hP : ∀ p ∈ P, p ∈ convexHull ℝ ((insert d N : Finset Point) : Set Point))
    (hne : ∀ p ∈ P, p ≠ d) : d ∈ convexHull ℝ (N : Set Point) := by
  by_contra hh
  obtain ⟨l, hl⟩ := exists_positive_height_of_not_mem_hull hh
  have hs : ∀ p ∈ insert d N, p ≠ d → l d < l p := by
    intro p hp hpd
    have hpN := (Finset.mem_insert.mp hp).resolve_left hpd
    exact hl p (subset_convexHull ℝ _ hpN)
  have hstrict : ∀ p ∈ P, l d < l p := fun p hp ↦
    linear_support_strict_on_hull (by simp : d ∈ insert d N) l hs (hP p hp) (hne p hp)
  have h := convexHull_min hstrict ((convex_Ioi (l d)).affine_preimage l.toAffineMap) hd
  change l d < l d at h
  exact (lt_irrefl _ h)

/-- For the final five-sector run, the deep point is in the hull of
the two end apices and the four middle base vertices. The middle apices
are eliminated through their radial triangles. -/
theorem compressed_center_hull (b : Fin 6 → Point) (c : Fin 5 → Point) {d : Point}
    (hd : d ∈ convexHull ℝ (Set.range c))
    (hfan : ∀ i, StrictlyInsideTriangle d (b i.succ) (b i.castSucc) (c i)) :
    d ∈ convexHull ℝ ({c 0, b 1, b 2, b 3, b 4, c 4} : Set Point) := by
  let N : Finset Point := {c 0, b 1, b 2, b 3, b 4, c 4}
  have hP : ∀ p ∈ Finset.univ.image c, p ∈ convexHull ℝ ((insert d N : Finset Point) : Set Point) := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases hi0 : i = 0
    · subst i
      exact subset_convexHull ℝ _ (by simp [N])
    by_cases hi4 : i = 4
    · subst i
      exact subset_convexHull ℝ _ (by simp [N])
    have hb : b i.succ ∈ N ∧ b i.castSucc ∈ N := by
      fin_cases i <;> simp_all [N]
    have hsub : triangleHull d (b i.succ) (b i.castSucc) ⊆
        convexHull ℝ ((insert d N : Finset Point) : Set Point) :=
      triangleHull_subset_of_mem (convex_convexHull ℝ _)
        (subset_convexHull ℝ _ (by simp))
        (subset_convexHull ℝ _ (Finset.mem_insert_of_mem hb.1))
        (subset_convexHull ℝ _ (Finset.mem_insert_of_mem hb.2))
    exact hsub (strictlyInsideTriangle_mem_triangleHull (hfan i))
  have hne : ∀ p ∈ Finset.univ.image c, p ≠ d := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (strictlyInsideTriangle_ne_vertices (hfan i)).1
  have hh := mem_hull_of_star_generators (N := N) (by simpa using hd) hP hne
  simpa only [N, Finset.coe_insert, Finset.coe_singleton] using hh

def BetweenValues (z : ℝ) (N : Set ℝ) : Prop :=
  (∃ p ∈ N, p < z) ∧ ∃ p ∈ N, z < p

theorem below_of_no_upcross {a b z : ℝ} (hb : b ≠ z)
    (hno : ¬(a < z ∧ z < b)) (ha : a < z) : b < z :=
  lt_of_le_of_ne (le_of_not_gt (fun hh ↦ hno ⟨ha, hh⟩)) hb

theorem above_of_no_upcross {a b z : ℝ} (ha : a ≠ z)
    (hno : ¬(a < z ∧ z < b)) (hb : z < b) : z < a :=
  lt_of_le_of_ne (le_of_not_gt (fun hh ↦ hno ⟨hh, hb⟩)) ha.symm

/-- When the intermediate raw sectors are excluded, the four middle
base values can be reduced to their two end values for the maximum
principle. A below-threshold value propagates forward; an above-threshold
value propagates backward. -/
theorem compress_between_values {z l r a b c d : ℝ}
    (hbetween : BetweenValues z {l, a, b, c, d, r})
    (ha : a ≠ z) (hb : b ≠ z) (hc : c ≠ z) (hd : d ≠ z)
    (hab : ¬(a < z ∧ z < b)) (hbc : ¬(b < z ∧ z < c)) (hcd : ¬(c < z ∧ z < d)) :
    BetweenValues z {l, a, d, r} ∧ ¬(a < z ∧ z < d) := by
  have hbd (h : b < z) : d < z := below_of_no_upcross hd hcd (below_of_no_upcross hc hbc h)
  have hca (h : z < c) : z < a := above_of_no_upcross ha hab (above_of_no_upcross hb hbc h)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · obtain ⟨p, hp, hpz⟩ := hbetween.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpl | hpa | hpb | hpc | hpd | hpr
    · exact ⟨p, by simp [hpl], hpz⟩
    · exact ⟨p, by simp [hpa], hpz⟩
    · exact ⟨d, by simp, hbd (hpb ▸ hpz)⟩
    · exact ⟨d, by simp, below_of_no_upcross hd hcd (hpc ▸ hpz)⟩
    · exact ⟨p, by simp [hpd], hpz⟩
    · exact ⟨p, by simp [hpr], hpz⟩
  · obtain ⟨p, hp, hzp⟩ := hbetween.2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with hpl | hpa | hpb | hpc | hpd | hpr
    · exact ⟨p, by simp [hpl], hzp⟩
    · exact ⟨p, by simp [hpa], hzp⟩
    · exact ⟨a, by simp, above_of_no_upcross ha hab (hpb ▸ hzp)⟩
    · exact ⟨a, by simp, hca (hpc ▸ hzp)⟩
    · exact ⟨p, by simp [hpd], hzp⟩
    · exact ⟨p, by simp [hpr], hzp⟩
  · rintro ⟨hlow, hhigh⟩
    exact (lt_asymm (hbd (below_of_no_upcross hb hab hlow)) hhigh)

theorem betweenValues_four_iff (z a b c d : ℝ) :
    BetweenValues z {a, b, c, d} ↔
      (a < z ∨ b < z ∨ c < z ∨ d < z) ∧ (z < a ∨ z < b ∨ z < c ∨ z < d) := by
  simp [BetweenValues]

/-- The scalar maximum principle for the shortened five-sector chain.
The middle node has six geometric neighbors, but the three excluded raw
sectors compress their four base values to the two boundary values. -/
theorem compressed_scalar_chain (z a : ℕ → ℝ)
    (hleft : BetweenValues (z 1) {z 0, a 0, a 1, z 2})
    (hmiddle : BetweenValues (z 2) {z 1, a 1, a 2, a 3, a 4, z 3})
    (hright : BetweenValues (z 3) {z 2, a 4, a 5, z 4})
    (hnext_ne : ∀ k, k ≤ 3 → z k ≠ z (k + 1))
    (hleft_ne : z 1 ≠ a 0 ∧ z 1 ≠ a 1)
    (hmiddle_ne : z 2 ≠ a 1 ∧ z 2 ≠ a 2 ∧ z 2 ≠ a 3 ∧ z 2 ≠ a 4)
    (hright_ne : z 3 ≠ a 4 ∧ z 3 ≠ a 5)
    (hleft_out : ¬(a 0 < z 1 ∧ z 1 < a 1))
    (hmiddle_out : ∀ k, 1 ≤ k → k ≤ 3 → ¬(a k < z 2 ∧ z 2 < a (k + 1)))
    (hright_out : ¬(a 4 < z 3 ∧ z 3 < a 5))
    (hfirst : z 0 = a 0 ∨ z 1 < z 0)
    (hlast : z 4 = a 5 ∨ z 4 < z 3) :
    ∀ k, k ≤ 3 → z (k + 1) < z k := by
  obtain ⟨hmid, hmid_out⟩ := compress_between_values hmiddle hmiddle_ne.1.symm
    hmiddle_ne.2.1.symm hmiddle_ne.2.2.1.symm hmiddle_ne.2.2.2.symm
    (hmiddle_out 1 (by decide) (by decide)) (hmiddle_out 2 (by decide) (by decide))
    (hmiddle_out 3 (by decide) (by decide))
  have h₁ := (betweenValues_four_iff _ _ _ _ _).mp hleft
  have h₂ := (betweenValues_four_iff _ _ _ _ _).mp hmid
  have h₃ := (betweenValues_four_iff _ _ _ _ _).mp hright
  let A : ℕ → ℝ := fun k ↦ if k ≤ 2 then a (k - 1) else a (k + 1)
  apply Lax56Proofs.ValtrMaximum.scalar_chain_strictly_decreasing_of_endpoint_conditions
    z A (m := 3) (by decide) (by simpa [A] using hlast)
  · intro k hk hkm
    interval_cases k
    · simpa [A] using h₁.1
    · simpa [A] using h₂.1
    · simpa [A] using h₃.1
  · intro k hk hkm
    interval_cases k
    · simpa [A] using h₁.2
    · simpa [A] using h₂.2
    · simpa [A] using h₃.2
  · exact hnext_ne
  · intro k hk hkm
    interval_cases k
    · simpa [A] using hleft_ne
    · simpa [A] using And.intro hmiddle_ne.1 hmiddle_ne.2.2.2
    · simpa [A] using hright_ne
  · intro k hk hkm
    interval_cases k
    · simpa [A] using hleft_out
    · simpa [A] using hmid_out
    · simpa [A] using hright_out
  · simpa [A] using hfirst

/-- The endpoint-viewpoint version omits the first point, replacing its
endpoint equality by the known descent from the first apex to the center. -/
theorem compressed_scalar_chain_without_first (z a : ℕ → ℝ)
    (hmiddle : BetweenValues (z 2) {z 1, a 1, a 2, a 3, a 4, z 3})
    (hright : BetweenValues (z 3) {z 2, a 4, a 5, z 4})
    (hnext_ne : ∀ k, 1 ≤ k → k ≤ 3 → z k ≠ z (k + 1))
    (hmiddle_ne : z 2 ≠ a 1 ∧ z 2 ≠ a 2 ∧ z 2 ≠ a 3 ∧ z 2 ≠ a 4)
    (hright_ne : z 3 ≠ a 4 ∧ z 3 ≠ a 5)
    (hmiddle_out : ∀ k, 1 ≤ k → k ≤ 3 → ¬(a k < z 2 ∧ z 2 < a (k + 1)))
    (hright_out : ¬(a 4 < z 3 ∧ z 3 < a 5))
    (hfirst : z 2 < z 1) (hlast : z 4 = a 5 ∨ z 4 < z 3) :
    ∀ k, 1 ≤ k → k ≤ 3 → z (k + 1) < z k := by
  obtain ⟨hmid, hmid_out⟩ := compress_between_values hmiddle hmiddle_ne.1.symm
    hmiddle_ne.2.1.symm hmiddle_ne.2.2.1.symm hmiddle_ne.2.2.2.symm
    (hmiddle_out 1 (by decide) (by decide)) (hmiddle_out 2 (by decide) (by decide))
    (hmiddle_out 3 (by decide) (by decide))
  have h₁ := (betweenValues_four_iff _ _ _ _ _).mp hmid
  have h₂ := (betweenValues_four_iff _ _ _ _ _).mp hright
  let Z : ℕ → ℝ := fun k ↦ z (k + 1)
  let A : ℕ → ℝ := fun k ↦ if k = 1 then a 1 else a (k + 2)
  have hh : ∀ k, k ≤ 2 → Z (k + 1) < Z k := by
    apply Lax56Proofs.ValtrMaximum.scalar_chain_strictly_decreasing_of_endpoint_conditions
      Z A (m := 2) (by decide) (by simpa [Z, A] using hlast)
    · intro k hk hkm
      interval_cases k
      · simpa [Z, A] using h₁.1
      · simpa [Z, A] using h₂.1
    · intro k hk hkm
      interval_cases k
      · simpa [Z, A] using h₁.2
      · simpa [Z, A] using h₂.2
    · exact fun k hk ↦ hnext_ne (k + 1) (by omega) (by omega)
    · intro k hk hkm
      interval_cases k
      · simpa [Z, A] using And.intro hmiddle_ne.1 hmiddle_ne.2.2.2
      · simpa [Z, A] using hright_ne
    · intro k hk hkm
      interval_cases k
      · simpa [Z, A] using hmid_out
      · simpa [Z, A] using hright_out
    · exact Or.inr hfirst
  intro k hk hkm
  have hh' := hh (k - 1) (by omega)
  simpa only [Z, Nat.sub_add_cancel hk] using hh'

/-- The symmetric endpoint-viewpoint version omits the last point and
uses the known descent from the center to the last apex. -/
theorem compressed_scalar_chain_without_last (z a : ℕ → ℝ)
    (hleft : BetweenValues (z 1) {z 0, a 0, a 1, z 2})
    (hmiddle : BetweenValues (z 2) {z 1, a 1, a 2, a 3, a 4, z 3})
    (hnext_ne : ∀ k, k ≤ 2 → z k ≠ z (k + 1))
    (hleft_ne : z 1 ≠ a 0 ∧ z 1 ≠ a 1)
    (hmiddle_ne : z 2 ≠ a 1 ∧ z 2 ≠ a 2 ∧ z 2 ≠ a 3 ∧ z 2 ≠ a 4)
    (hleft_out : ¬(a 0 < z 1 ∧ z 1 < a 1))
    (hmiddle_out : ∀ k, 1 ≤ k → k ≤ 3 → ¬(a k < z 2 ∧ z 2 < a (k + 1)))
    (hfirst : z 0 = a 0 ∨ z 1 < z 0) (hlast : z 3 < z 2) :
    ∀ k, k ≤ 2 → z (k + 1) < z k := by
  obtain ⟨hmid, hmid_out⟩ := compress_between_values hmiddle hmiddle_ne.1.symm
    hmiddle_ne.2.1.symm hmiddle_ne.2.2.1.symm hmiddle_ne.2.2.2.symm
    (hmiddle_out 1 (by decide) (by decide)) (hmiddle_out 2 (by decide) (by decide))
    (hmiddle_out 3 (by decide) (by decide))
  have h₁ := (betweenValues_four_iff _ _ _ _ _).mp hleft
  have h₂ := (betweenValues_four_iff _ _ _ _ _).mp hmid
  let A : ℕ → ℝ := fun k ↦ if k ≤ 2 then a (k - 1) else a 4
  apply Lax56Proofs.ValtrMaximum.scalar_chain_strictly_decreasing_of_endpoint_conditions
    z A (m := 2) (by decide) (Or.inr hlast)
  · intro k hk hkm
    interval_cases k
    · simpa [A] using h₁.1
    · simpa [A] using h₂.1
  · intro k hk hkm
    interval_cases k
    · simpa [A] using h₁.2
    · simpa [A] using h₂.2
  · exact hnext_ne
  · intro k hk hkm
    interval_cases k
    · simpa [A] using hleft_ne
    · simpa [A] using And.intro hmiddle_ne.1 hmiddle_ne.2.2.2
  · intro k hk hkm
    interval_cases k
    · simpa [A] using hleft_out
    · simpa [A] using hmid_out
  · simpa [A] using hfirst

end Lax56Proofs.ValtrCompression
