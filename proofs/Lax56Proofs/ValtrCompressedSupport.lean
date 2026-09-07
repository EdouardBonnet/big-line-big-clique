import Lax56Proofs.ValtrCompression

namespace Lax56Proofs.ValtrCompressedSupport

open Lax56.Geometry Lax56.ConvexLayers
open Lax56Proofs.ConvexLayers Lax56Proofs.CupsCapsGeometry
open Lax56Proofs.Orientation Lax56Proofs.HKBGeometry Lax56Proofs.HKBTriangle
open Lax56Proofs.ValtrSelection Lax56Proofs.ValtrProjective
open Lax56Proofs.ValtrCompression Lax56Proofs.ValtrExtension
open scoped Classical

def neighbors (h b : ℕ → Point) (k : ℕ) : Set Point :=
  if k = 1 then {h 0, b 0, b 1, h 2}
  else if k = 2 then {h 1, b 1, b 2, b 3, b 4, h 3}
  else {h 2, b 4, b 5, h 4}

theorem projective_between_image (l : Point →ₗ[ℝ] ℝ) {x r p : Point}
    {N : Set Point} (hr : l x < l r) (hpY : l x < l p)
    (hNY : ∀ q ∈ N, l x < l q) (hp : p ∈ convexHull ℝ N)
    (hne : ∀ q ∈ N, turn p q x ≠ 0) :
    BetweenValues (projectiveValue l x r p) (projectiveValue l x r '' N) := by
  obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hpv⟩⟩ :=
    projectiveValue_between_generators l hr hpY hNY hp hne
  exact ⟨⟨_, ⟨u, hu, rfl⟩, hup⟩, ⟨_, ⟨v, hv, rfl⟩, hpv⟩⟩

/-- The three local hull relations of the shortened five-sector chain
imply all its exterior supporting inequalities. The three middle tests
are the raw sectors with the deep point as apex. -/
theorem support_of_positive_height (l : Point →ₗ[ℝ] ℝ)
    (h b : ℕ → Point) {x r : Point} (hr : l x < l r)
    (hY : ∀ k, k ≤ 4 → l x < l (h k))
    (hbY : ∀ k, k ≤ 5 → l x < l (b k))
    (hlocal : ∀ k, 1 ≤ k → k ≤ 3 → h k ∈ convexHull ℝ (neighbors h b k))
    (hnext : ∀ k, k ≤ 3 → turn (h k) (h (k + 1)) x ≠ 0)
    (hne : ∀ k, 1 ≤ k → k ≤ 3 → ∀ q ∈ neighbors h b k, turn (h k) q x ≠ 0)
    (hleft : x ∉ sector ![b 0, h 1, b 1])
    (hmiddle : ∀ k, 1 ≤ k → k ≤ 3 → x ∉ sector ![b k, h 2, b (k + 1)])
    (hright : x ∉ sector ![b 4, h 3, b 5])
    (hfirst : h 0 = b 0 ∨ turn (h 0) (h 1) x < 0)
    (hlast : h 4 = b 5 ∨ turn (h 3) (h 4) x < 0) :
    ∀ k, k ≤ 3 → turn (h k) (h (k + 1)) x < 0 := by
  let σ := projectiveValue l x r
  let z : ℕ → ℝ := fun k ↦ σ (h k)
  let a : ℕ → ℝ := fun k ↦ σ (b k)
  have hNY (k) (hk : 1 ≤ k) (hkm : k ≤ 3) : ∀ q ∈ neighbors h b k, l x < l q := by
    intro q hq
    interval_cases k <;> simp only [neighbors, ↓reduceIte, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    all_goals rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hY _ (by decide) | exact hbY _ (by decide)
  have hbet (k) (hk : 1 ≤ k) (hkm : k ≤ 3) :
      BetweenValues (z k) (σ '' neighbors h b k) :=
    projective_between_image l hr (hY k (by omega)) (hNY k hk hkm)
      (hlocal k hk hkm) (hne k hk hkm)
  have h₁ : BetweenValues (z 1) {z 0, a 0, a 1, z 2} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 1 (by decide) (by decide)
  have h₂ : BetweenValues (z 2) {z 1, a 1, a 2, a 3, a 4, z 3} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 2 (by decide) (by decide)
  have h₃ : BetweenValues (z 3) {z 2, a 4, a 5, z 4} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 3 (by decide) (by decide)
  have hneq (k) (hk : 1 ≤ k) (hkm : k ≤ 3) (j) (hj : j ≤ 5)
      (hjk : b j ∈ neighbors h b k) : z k ≠ a j :=
    projectiveValue_ne l hr (hY k (by omega)) (hbY j hj) (hne k hk hkm _ hjk)
  have hfirst' : z 0 = a 0 ∨ z 1 < z 0 := by
    rcases hfirst with heq | hh
    · exact Or.inl (by dsimp only [z, a]; rw [heq])
    · apply Or.inr
      apply (projectiveValue_lt_iff l hr (hY 1 (by decide)) (hY 0 (by decide))).mpr
      rw [turn_swap_first]
      exact neg_pos.mpr hh
  have hlast' : z 4 = a 5 ∨ z 4 < z 3 := by
    rcases hlast with heq | hh
    · exact Or.inl (by dsimp only [z, a]; rw [heq])
    · apply Or.inr
      apply (projectiveValue_lt_iff l hr (hY 4 (by decide)) (hY 3 (by decide))).mpr
      rw [turn_swap_first]
      exact neg_pos.mpr hh
  have hdesc := compressed_scalar_chain z a h₁ h₂ h₃
    (fun k hk ↦ projectiveValue_ne l hr (hY k (by omega))
      (hY (k + 1) (by omega)) (hnext k hk))
    ⟨hneq 1 (by decide) (by decide) 0 (by decide) (by simp [neighbors]),
      hneq 1 (by decide) (by decide) 1 (by decide) (by simp [neighbors])⟩
    ⟨hneq 2 (by decide) (by decide) 1 (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 2 (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 3 (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 4 (by decide) (by simp [neighbors])⟩
    ⟨hneq 3 (by decide) (by decide) 4 (by decide) (by simp [neighbors]),
      hneq 3 (by decide) (by decide) 5 (by decide) (by simp [neighbors])⟩
    (fun hh ↦ hleft ((sector_iff_projective_interval l hr (hbY 0 (by decide))
      (hY 1 (by decide)) (hbY 1 (by decide))).mpr hh))
    (fun k hk hkm hh ↦ hmiddle k hk hkm
      ((sector_iff_projective_interval l hr (hbY k (by omega)) (hY 2 (by decide))
        (hbY (k + 1) (by omega))).mpr hh))
    (fun hh ↦ hright ((sector_iff_projective_interval l hr (hbY 4 (by decide))
      (hY 3 (by decide)) (hbY 5 (by decide))).mpr hh)) hfirst' hlast'
  intro k hk
  have hpos := (projectiveValue_lt_iff l hr (hY (k + 1) (by omega))
    (hY k (by omega))).mp (hdesc k hk)
  rw [turn_swap_first] at hpos
  exact neg_pos.mp hpos

theorem exterior_support {B : Finset Point} (h b : ℕ → Point) {x : Point}
    (hx : x ∉ convexHull ℝ (B : Set Point))
    (hmem : ∀ k, k ≤ 4 → h k ∈ convexHull ℝ (B : Set Point))
    (hbmem : ∀ k, k ≤ 5 → b k ∈ convexHull ℝ (B : Set Point))
    (hlocal : ∀ k, 1 ≤ k → k ≤ 3 → h k ∈ convexHull ℝ (neighbors h b k))
    (hnext : ∀ k, k ≤ 3 → turn (h k) (h (k + 1)) x ≠ 0)
    (hne : ∀ k, 1 ≤ k → k ≤ 3 → ∀ q ∈ neighbors h b k, turn (h k) q x ≠ 0)
    (hleft : x ∉ sector ![b 0, h 1, b 1])
    (hmiddle : ∀ k, 1 ≤ k → k ≤ 3 → x ∉ sector ![b k, h 2, b (k + 1)])
    (hright : x ∉ sector ![b 4, h 3, b 5])
    (hfirst : h 0 = b 0) (hlast : h 4 = b 5) :
    ∀ k, k ≤ 3 → turn (h k) (h (k + 1)) x < 0 := by
  obtain ⟨l, hl⟩ := exists_positive_height_of_not_mem_hull hx
  exact support_of_positive_height l h b (hl _ (hmem 0 (by decide)))
    (fun k hk ↦ hl _ (hmem k hk)) (fun k hk ↦ hl _ (hbmem k hk))
    hlocal hnext hne hleft hmiddle hright (Or.inl hfirst) (Or.inl hlast)

/-- The positive-height argument after omitting the first endpoint.
Only the center and last-apex hull relations are needed. -/
theorem support_without_first_of_positive_height (l : Point →ₗ[ℝ] ℝ)
    (h b : ℕ → Point) {x r : Point} (hr : l x < l r)
    (hY : ∀ k, 1 ≤ k → k ≤ 4 → l x < l (h k))
    (hbY : ∀ k, 1 ≤ k → k ≤ 5 → l x < l (b k))
    (hlocal : ∀ k, 2 ≤ k → k ≤ 3 → h k ∈ convexHull ℝ (neighbors h b k))
    (hnext : ∀ k, 1 ≤ k → k ≤ 3 → turn (h k) (h (k + 1)) x ≠ 0)
    (hne : ∀ k, 2 ≤ k → k ≤ 3 → ∀ q ∈ neighbors h b k, turn (h k) q x ≠ 0)
    (hmiddle : ∀ k, 1 ≤ k → k ≤ 3 → x ∉ sector ![b k, h 2, b (k + 1)])
    (hright : x ∉ sector ![b 4, h 3, b 5])
    (hfirst : turn (h 1) (h 2) x < 0) (hlast : h 4 = b 5) :
    ∀ k, 1 ≤ k → k ≤ 3 → turn (h k) (h (k + 1)) x < 0 := by
  let σ := projectiveValue l x r
  let z : ℕ → ℝ := fun k ↦ σ (h k)
  let a : ℕ → ℝ := fun k ↦ σ (b k)
  have hNY (k) (hk : 2 ≤ k) (hkm : k ≤ 3) : ∀ q ∈ neighbors h b k, l x < l q := by
    intro q hq
    interval_cases k <;> simp only [neighbors, ↓reduceIte, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    all_goals rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hY _ (by decide) (by decide) | exact hbY _ (by decide) (by decide)
  have hbet (k) (hk : 2 ≤ k) (hkm : k ≤ 3) :
      BetweenValues (z k) (σ '' neighbors h b k) :=
    projective_between_image l hr (hY k (by omega) (by omega)) (hNY k hk hkm)
      (hlocal k hk hkm) (hne k hk hkm)
  have h₂ : BetweenValues (z 2) {z 1, a 1, a 2, a 3, a 4, z 3} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 2 (by decide) (by decide)
  have h₃ : BetweenValues (z 3) {z 2, a 4, a 5, z 4} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 3 (by decide) (by decide)
  have hneq (k) (hk : 2 ≤ k) (hkm : k ≤ 3) (j) (hj : 1 ≤ j) (hjm : j ≤ 5)
      (hjk : b j ∈ neighbors h b k) : z k ≠ a j :=
    projectiveValue_ne l hr (hY k (by omega) (by omega)) (hbY j hj hjm) (hne k hk hkm _ hjk)
  have hfirst' : z 2 < z 1 := by
    apply (projectiveValue_lt_iff l hr (hY 2 (by decide) (by decide))
      (hY 1 (by decide) (by decide))).mpr
    rw [turn_swap_first]
    exact neg_pos.mpr hfirst
  have hdesc := compressed_scalar_chain_without_first z a h₂ h₃
    (fun k hk hkm ↦ projectiveValue_ne l hr (hY k hk (by omega))
      (hY (k + 1) (by omega) (by omega)) (hnext k hk hkm))
    ⟨hneq 2 (by decide) (by decide) 1 (by decide) (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 2 (by decide) (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 3 (by decide) (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 4 (by decide) (by decide) (by simp [neighbors])⟩
    ⟨hneq 3 (by decide) (by decide) 4 (by decide) (by decide) (by simp [neighbors]),
      hneq 3 (by decide) (by decide) 5 (by decide) (by decide) (by simp [neighbors])⟩
    (fun k hk hkm hh ↦ hmiddle k hk hkm
      ((sector_iff_projective_interval l hr (hbY k hk (by omega))
        (hY 2 (by decide) (by decide)) (hbY (k + 1) (by omega) (by omega))).mpr hh))
    (fun hh ↦ hright ((sector_iff_projective_interval l hr (hbY 4 (by decide) (by decide))
      (hY 3 (by decide) (by decide)) (hbY 5 (by decide) (by decide))).mpr hh)) hfirst'
    (Or.inl (by dsimp only [z, a]; rw [hlast]))
  intro k hk hkm
  have hpos := (projectiveValue_lt_iff l hr (hY (k + 1) (by omega) (by omega))
    (hY k hk (by omega))).mp (hdesc k hk hkm)
  rw [turn_swap_first] at hpos
  exact neg_pos.mp hpos

/-- The symmetric chart omits the last endpoint. -/
theorem support_without_last_of_positive_height (l : Point →ₗ[ℝ] ℝ)
    (h b : ℕ → Point) {x r : Point} (hr : l x < l r)
    (hY : ∀ k, k ≤ 3 → l x < l (h k))
    (hbY : ∀ k, k ≤ 4 → l x < l (b k))
    (hlocal : ∀ k, 1 ≤ k → k ≤ 2 → h k ∈ convexHull ℝ (neighbors h b k))
    (hnext : ∀ k, k ≤ 2 → turn (h k) (h (k + 1)) x ≠ 0)
    (hne : ∀ k, 1 ≤ k → k ≤ 2 → ∀ q ∈ neighbors h b k, turn (h k) q x ≠ 0)
    (hleft : x ∉ sector ![b 0, h 1, b 1])
    (hmiddle : ∀ k, 1 ≤ k → k ≤ 3 → x ∉ sector ![b k, h 2, b (k + 1)])
    (hfirst : h 0 = b 0) (hlast : turn (h 2) (h 3) x < 0) :
    ∀ k, k ≤ 2 → turn (h k) (h (k + 1)) x < 0 := by
  let σ := projectiveValue l x r
  let z : ℕ → ℝ := fun k ↦ σ (h k)
  let a : ℕ → ℝ := fun k ↦ σ (b k)
  have hNY (k) (hk : 1 ≤ k) (hkm : k ≤ 2) : ∀ q ∈ neighbors h b k, l x < l q := by
    intro q hq
    interval_cases k <;> simp only [neighbors, ↓reduceIte, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    all_goals rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact hY _ (by decide) | exact hbY _ (by decide)
  have hbet (k) (hk : 1 ≤ k) (hkm : k ≤ 2) :
      BetweenValues (z k) (σ '' neighbors h b k) :=
    projective_between_image l hr (hY k (by omega)) (hNY k hk hkm)
      (hlocal k hk hkm) (hne k hk hkm)
  have h₁ : BetweenValues (z 1) {z 0, a 0, a 1, z 2} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 1 (by decide) (by decide)
  have h₂ : BetweenValues (z 2) {z 1, a 1, a 2, a 3, a 4, z 3} := by
    simpa [neighbors, z, a, Set.image_insert_eq] using hbet 2 (by decide) (by decide)
  have hneq (k) (hk : 1 ≤ k) (hkm : k ≤ 2) (j) (hj : j ≤ 4)
      (hjk : b j ∈ neighbors h b k) : z k ≠ a j :=
    projectiveValue_ne l hr (hY k (by omega)) (hbY j hj) (hne k hk hkm _ hjk)
  have hlast' : z 3 < z 2 := by
    apply (projectiveValue_lt_iff l hr (hY 3 (by decide)) (hY 2 (by decide))).mpr
    rw [turn_swap_first]
    exact neg_pos.mpr hlast
  have hdesc := compressed_scalar_chain_without_last z a h₁ h₂
    (fun k hk ↦ projectiveValue_ne l hr (hY k (by omega))
      (hY (k + 1) (by omega)) (hnext k hk))
    ⟨hneq 1 (by decide) (by decide) 0 (by decide) (by simp [neighbors]),
      hneq 1 (by decide) (by decide) 1 (by decide) (by simp [neighbors])⟩
    ⟨hneq 2 (by decide) (by decide) 1 (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 2 (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 3 (by decide) (by simp [neighbors]),
      hneq 2 (by decide) (by decide) 4 (by decide) (by simp [neighbors])⟩
    (fun hh ↦ hleft ((sector_iff_projective_interval l hr (hbY 0 (by decide))
      (hY 1 (by decide)) (hbY 1 (by decide))).mpr hh))
    (fun k hk hkm hh ↦ hmiddle k hk hkm
      ((sector_iff_projective_interval l hr (hbY k (by omega)) (hY 2 (by decide))
        (hbY (k + 1) (by omega))).mpr hh))
    (Or.inl (by dsimp only [z, a]; rw [hfirst])) hlast'
  intro k hk
  have hpos := (projectiveValue_lt_iff l hr (hY (k + 1) (by omega))
    (hY k (by omega))).mp (hdesc k hk)
  rw [turn_swap_first] at hpos
  exact neg_pos.mp hpos

end Lax56Proofs.ValtrCompressedSupport
