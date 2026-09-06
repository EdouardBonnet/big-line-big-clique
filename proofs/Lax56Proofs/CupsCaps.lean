import Mathlib.Tactic
import Mathlib.Data.List.Triplewise

/-!
The elementary cups-and-caps recurrence, separated from planar geometry.
`Chain R P n p q` has `n + 2` increasing vertices, starts with `p,q`, and
every consecutive triple satisfies `R`. Taking `R` to be increasing slope
gives cups; its complement gives caps when collinear triples are excluded.

We partition by *first* points of cups, the left-right reflection of the
last-point partition in the supplied informal proof.
-/

namespace Lax56Proofs.CupsCaps

variable {α : Type*} [LinearOrder α]

inductive Chain (R : α → α → α → Prop) (P : Finset α) : ℕ → α → α → Prop
  | pair {p q : α} : p ∈ P → q ∈ P → p < q → Chain R P 0 p q
  | cons {n : ℕ} {p q r : α} : p ∈ P → p < q → R p q r →
      Chain R P n q r → Chain R P (n + 1) p q

def HasChain (R : α → α → α → Prop) (P : Finset α) (n : ℕ) : Prop :=
  ∃ p q, Chain R P n p q

theorem Chain.first_mem {R : α → α → α → Prop} {P : Finset α} {n : ℕ} {p q : α}
    (h : Chain R P n p q) : p ∈ P := by
  cases h <;> assumption

theorem Chain.second_mem {R : α → α → α → Prop} {P : Finset α} {n : ℕ} {p q : α}
    (h : Chain R P n p q) : q ∈ P := by
  cases h with
  | pair _ hq _ => exact hq
  | cons _ _ _ tail => exact tail.first_mem

theorem Chain.first_lt {R : α → α → α → Prop} {P : Finset α} {n : ℕ} {p q : α}
    (h : Chain R P n p q) : p < q := by
  cases h <;> assumption

theorem Chain.mono {R : α → α → α → Prop} {P Q : Finset α} {n : ℕ} {p q : α}
    (h : Chain R P n p q) (hPQ : P ⊆ Q) : Chain R Q n p q := by
  induction h with
  | pair hp hq hpq => exact .pair (hPQ hp) (hPQ hq) hpq
  | cons hp hpq hR _ ih => exact .cons (hPQ hp) hpq hR ih

theorem hasChain_mono {R : α → α → α → Prop} {P Q : Finset α} {n : ℕ}
    (hPQ : P ⊆ Q) (h : HasChain R P n) : HasChain R Q n := by
  obtain ⟨p, q, h⟩ := h
  exact ⟨p, q, h.mono hPQ⟩

theorem card_le_one_of_no_pair (R : α → α → α → Prop) (P : Finset α)
    (hno : ¬HasChain R P 0) : P.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rcases lt_trichotomy p q with hpq | hpq | hqp
  · exact (hno ⟨p, q, .pair hp hq hpq⟩).elim
  · exact hpq
  · exact (hno ⟨q, p, .pair hq hp hqp⟩).elim

/-- If every point of `E` begins an `n+2`-cup but no `n+3`-cup exists,
every cap in `E` extends by one vertex in the ambient set. -/
theorem extend_complement
    (R : α → α → α → Prop) {P E : Finset α} (hEP : E ⊆ P) (n : ℕ)
    (hno : ¬HasChain R P (n + 1))
    (hE : ∀ p ∈ E, ∃ q, Chain R P n p q)
    {m : ℕ} {p q : α} (hcap : Chain (fun a b c ↦ ¬R a b c) E m p q) :
    Chain (fun a b c ↦ ¬R a b c) P (m + 1) p q := by
  induction hcap with
  | pair hp hq hpq =>
    obtain ⟨r, hr⟩ := hE _ hq
    have hnR : ¬R _ _ r := fun hR ↦ hno ⟨_, _, .cons (hEP hp) hpq hR hr⟩
    exact .cons (hEP hp) hpq hnR (.pair (hEP hq) hr.second_mem hr.first_lt)
  | cons hp hpq hR _ ih => exact .cons (hEP hp) hpq hR ih

/-- The full double induction: no `(r+2)`-cup and no `(s+2)`-cap
implies at most `2^(r+s)` points. This theorem has no geometric assumptions. -/
theorem card_le_pow_of_no_chains
    (R : α → α → α → Prop) (P : Finset α) (r s : ℕ)
    (hcup : ¬HasChain R P r) (hcap : ¬HasChain (fun a b c ↦ ¬R a b c) P s) :
    P.card ≤ 2 ^ (r + s) := by
  classical
  induction r generalizing s P with
  | zero =>
    exact (card_le_one_of_no_pair R P hcup).trans (Nat.one_le_pow _ _ (by omega))
  | succ r ihr =>
    induction s generalizing P with
    | zero =>
      exact (card_le_one_of_no_pair _ P hcap).trans (Nat.one_le_pow _ _ (by omega))
    | succ s ihs =>
      let E := P.filter (fun p ↦ ∃ q, Chain R P r p q)
      let F := P \ E
      have hEP : E ⊆ P := Finset.filter_subset _ _
      have hFP : F ⊆ P := Finset.sdiff_subset
      have hE : ∀ p ∈ E, ∃ q, Chain R P r p q := fun _ hp ↦ (Finset.mem_filter.mp hp).2
      have hFcup : ¬HasChain R F r := by
        rintro ⟨p, q, h⟩
        have hp := Finset.mem_sdiff.mp h.first_mem
        exact hp.2 (Finset.mem_filter.mpr ⟨hp.1, q, h.mono hFP⟩)
      have hEcap : ¬HasChain (fun a b c ↦ ¬R a b c) E s := by
        rintro ⟨p, q, h⟩
        exact hcap ⟨p, q, extend_complement R hEP r hcup hE h⟩
      have hFb := ihr F (s + 1) hFcup (fun h ↦ hcap (hasChain_mono hFP h))
      have hEb := ihs E (fun h ↦ hcup (hasChain_mono hEP h)) hEcap
      have hsum : F.card + E.card = P.card := Finset.card_sdiff_add_card_eq_card hEP
      have hexp : r + 1 + s = r + (s + 1) := by omega
      rw [hexp] at hEb
      calc
        P.card = F.card + E.card := hsum.symm
        _ ≤ 2 ^ (r + (s + 1)) + 2 ^ (r + (s + 1)) := Nat.add_le_add hFb hEb
        _ = 2 ^ (r + 1 + (s + 1)) := by
          rw [show r + 1 + (s + 1) = (r + (s + 1)) + 1 by omega, pow_succ]
          omega

theorem exists_chain_of_card_gt
    (R : α → α → α → Prop) (P : Finset α) (r s : ℕ)
    (hcard : 2 ^ (r + s) < P.card) :
    HasChain R P r ∨ HasChain (fun a b c ↦ ¬R a b c) P s := by
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (card_le_pow_of_no_chains R P r s h.1 h.2)) hcard

/-- The four-point transitivity property of cup and cap orientations. -/
def TransitiveTriples (R : α → α → α → Prop) : Prop :=
  ∀ a b c d, a < b → b < c → c < d → R a b c → R b c d → R a b d ∧ R a c d

theorem triplewise_prepend {R : α → α → α → Prop} (htrans : TransitiveTriples R)
    {a b c : α} {l : List α} (hab : a < b) (habc : R a b c)
    (hord : (b :: c :: l).Pairwise (· < ·))
    (htri : (b :: c :: l).Triplewise R) : (a :: b :: c :: l).Triplewise R := by
  have hbc := (List.pairwise_cons.mp hord).1 c (by simp)
  have hbAll := (List.pairwise_cons.mp hord).1
  have hcAll := (List.pairwise_cons.mp (List.pairwise_cons.mp hord).2).1
  have hbPairs := (List.triplewise_cons.mp htri).1
  have hhead : ∀ d ∈ c :: l, R a b d := by
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact habc
    · exact (htrans a b c d hab hbc (hcAll d hd) habc
        ((List.pairwise_cons.mp hbPairs).1 d hd)).1
  have hrest : (c :: l).Pairwise (R a) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    have himem := List.getElem_mem hi
    have hjmem := List.getElem_mem hj
    exact (htrans a b (c :: l)[i] (c :: l)[j] hab (hbAll _ himem)
      (List.pairwise_iff_getElem.mp (List.pairwise_cons.mp hord).2 i j hi hj hij)
      (hhead _ himem) (List.pairwise_iff_getElem.mp hbPairs i j hi hj hij)).2
  exact .cons (List.pairwise_cons.mpr ⟨hhead, hrest⟩) htri

/-- For transitive planar orientations, a consecutive-triple chain actually
has the same orientation on *all* increasing triples. -/
theorem Chain.exists_list {R : α → α → α → Prop} (htrans : TransitiveTriples R)
    {P : Finset α} {n : ℕ} {p q : α} (h : Chain R P n p q) :
    ∃ l : List α, (p :: q :: l).length = n + 2 ∧
      (∀ x ∈ p :: q :: l, x ∈ P) ∧
      (p :: q :: l).Pairwise (· < ·) ∧ (p :: q :: l).Triplewise R := by
  induction h with
  | pair hp hq hpq =>
    refine ⟨[], rfl, ?_, ?_, List.triplewise_pair _ _ _⟩
    · simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        using And.intro hp hq
    · simpa using hpq
  | @cons n p q r hp hpq hR tail ih =>
    obtain ⟨l, hlen, hmem, hord, htri⟩ := ih
    refine ⟨r :: l, ?_, ?_, ?_, triplewise_prepend htrans hpq hR hord htri⟩
    · simp only [List.length_cons] at hlen ⊢
      omega
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hp
      · exact hmem x hx
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hord⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hpq
      · exact hpq.trans ((List.pairwise_cons.mp hord).1 x hx)

end Lax56Proofs.CupsCaps
