module

public import Mathlib

@[expose] public section

/-!
A verified finite certificate for `mc₃(4) ≤ 12`.  The elaborator below only
constructs a Boolean formula.  `raw_bv_decide` bit-blasts that formula, asks
CaDiCaL for LRAT, and has Lean's LRAT checker verify the returned certificate.
-/

namespace Lax56Proofs.HKBFiniteMC

local notation "Code" => BitVec 2

/-- A two-bit value is one of the three orientation codes. -/
def validSignCode (s : Code) : Bool := s.ult (BitVec.ofNat 2 3)

/-- Boolean disjunction expressed through the primitive operations supported
directly by the bit-vector certificate checker. -/
def boolOr (x y : Bool) : Bool := !(!x && !y)

/-- The local rank-three signotope and no-four-collinear constraints for one
ordered quadruple.  Keeping the twenty primitive clauses in this named group
lets the geometric proof use the certificate without a second, enormous
Boolean reassociation proof. -/
def allowedQuadCode (a b c d : Code) : Bool :=
  let neg := BitVec.ofNat 2 0
  let zero := BitVec.ofNat 2 1
  let pos := BitVec.ofNat 2 2
  let az := a == zero; let bz := b == zero
  let cz := c == zero; let dz := d == zero
  let an := a == neg; let bn := b == neg
  let cn := c == neg; let dn := d == neg
  let ap := a == pos; let bp := b == pos
  let cp := c == pos; let dp := d == pos
  !(az && bz) && !(az && cz) && !(az && dz) &&
  !(bz && cz) && !(bz && dz) && !(cz && dz) &&
  boolOr (!(an && cn)) bn && boolOr (!(an && cz)) bn &&
  boolOr (!(az && cn)) bn && boolOr (!(ap && cp)) bp &&
  boolOr (!(ap && cz)) bp && boolOr (!(az && cp)) bp &&
  boolOr (!(bn && dn)) cn && boolOr (!(bn && dz)) cn &&
  boolOr (!(bz && dn)) cn && boolOr (!(bp && dp)) cp &&
  boolOr (!(bp && dz)) cp && boolOr (!(bz && dp)) cp &&
  boolOr (boolOr (boolOr ap dp) bn) cn &&
  boolOr (boolOr (boolOr an dn) bp) cp

def blockerCandidate (o : Fin 13 → Fin 13 → Fin 13 → Code)
    (a b k : Fin 13) : Bool :=
  decide (a < k) && decide (k < b) &&
    (o a k b == (BitVec.ofNat 2 1 : Code))

/-- Equal colours force a zero triple at an intermediate ordered point. -/
def blockedPairCode (colour : Fin 13 → Code)
    (o : Fin 13 → Fin 13 → Fin 13 → Code) (a b : Fin 13) : Bool :=
  boolOr (!(colour a == colour b))
    (boolOr (blockerCandidate o a b 0)
    (boolOr (blockerCandidate o a b 1)
    (boolOr (blockerCandidate o a b 2)
    (boolOr (blockerCandidate o a b 3)
    (boolOr (blockerCandidate o a b 4)
    (boolOr (blockerCandidate o a b 5)
    (boolOr (blockerCandidate o a b 6)
    (boolOr (blockerCandidate o a b 7)
    (boolOr (blockerCandidate o a b 8)
    (boolOr (blockerCandidate o a b 9)
    (boolOr (blockerCandidate o a b 10)
    (boolOr (blockerCandidate o a b 11)
      (blockerCandidate o a b 12)))))))))))))

open Lean Elab Term Meta
open Lean.Elab.Tactic
open Lean.Elab.Tactic.BVDecide.Frontend

private meta def bnot (x : Expr) : Expr := mkApp (mkConst ``Bool.not) x
private meta def band (x y : Expr) : Expr := mkApp2 (mkConst ``Bool.and) x y
private meta def bor (x y : Expr) : Expr := bnot (band (bnot x) (bnot y))

private meta partial def andTree (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi <= lo then mkConst ``Bool.true
  else if hi = lo + 1 then xs[lo]!
  else
    let mid := lo + (hi - lo) / 2
    band (andTree xs lo mid) (andTree xs mid hi)

private meta partial def orTree (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi <= lo then mkConst ``Bool.false
  else if hi = lo + 1 then xs[lo]!
  else
    let mid := lo + (hi - lo) / 2
    bor (orTree xs lo mid) (orTree xs mid hi)

private meta partial def andChainAux
    (xs : Array Expr) (i : Nat) (acc : Expr) : Expr :=
  if i = xs.size then acc
  else andChainAux xs (i + 1) (band acc xs[i]!)

private meta def andChain (xs : Array Expr) : Expr :=
  andChainAux xs 1 xs[0]!

private meta partial def orChain (xs : Array Expr) (i : Nat) : Expr :=
  if i + 1 = xs.size then xs[i]!
  else bor xs[i]! (orChain xs (i + 1))

/-- The bit-vector formula saying that thirteen ordered points form a properly
four-coloured generalized rank-three signotope. -/
elab "mc13_formula%(" colourStx:term ", " oStx:term ")" : term => do
  let finTy := mkApp (mkConst ``Fin) (mkNatLit 13)
  let mut idx : Array Expr := #[]
  for n in [0:13] do
    idx := idx.push (← Term.elabTermEnsuringType
      (Syntax.mkNumLit (toString n)) finTy)
  let colour ← Term.elabTerm colourStx none
  let o ← Term.elabTerm oStx none
  let sc (n : Nat) : Expr := toExpr (BitVec.ofNat 2 n)
  let neg := sc 0
  let zero := sc 1
  let three := sc 3
  let eqv (x y : Expr) : TermElabM Expr := mkAppM ``BEq.beq #[x, y]
  let ult (x y : Expr) := mkApp3 (mkConst ``BitVec.ult) (mkNatLit 2) x y
  let oval (a b c : Nat) := mkAppN o #[idx[a]!, idx[b]!, idx[c]!]
  let cval (a : Nat) := mkApp colour idx[a]!
  let mut clauses : Array Expr := #[]
  -- Colour names are immaterial.  Use the restricted-growth normalization
  -- on the first three positions.
  clauses := clauses.push (← eqv (cval 0) neg)
  clauses := clauses.push (← eqv (cval 1) zero)
  clauses := clauses.push (ult (cval 2) three)
  -- Values 0,1,2 encode negative, zero, positive.
  for a in [0:13] do
    for b in [a+1:13] do
      for c in [b+1:13] do
        clauses := clauses.push
          (mkApp (mkConst ``validSignCode) (oval a b c))
  -- Generalized signotope rule, including the no-four-collinear condition.
  for a in [0:13] do
    for b in [a+1:13] do
      for c in [b+1:13] do
        for d in [c+1:13] do
          clauses := clauses.push (mkAppN (mkConst ``allowedQuadCode) #[
            oval a b c, oval a b d, oval a c d, oval b c d])
  -- Equal colours force a zero triple at an intermediate ordered point.
  for a in [0:13] do
    for b in [a+1:13] do
      clauses := clauses.push (mkAppN (mkConst ``blockedPairCode)
        #[colour, o, idx[a]!, idx[b]!])
  return andTree clauses 0 clauses.size

/-- Primitive expansion of `mc13_formula%`, used only as the input to the
bit-vector checker.  It has the same outer grouping as the readable formula,
so the two are definitionally equal. -/
elab "mc13_raw_formula%(" colourStx:term ", " oStx:term ")" : term => do
  let finTy := mkApp (mkConst ``Fin) (mkNatLit 13)
  let mut idx : Array Expr := #[]
  for n in [0:13] do
    idx := idx.push (← Term.elabTermEnsuringType
      (Syntax.mkNumLit (toString n)) finTy)
  let colour ← Term.elabTerm colourStx none
  let o ← Term.elabTerm oStx none
  let sc (n : Nat) : Expr := toExpr (BitVec.ofNat 2 n)
  let neg := sc 0
  let zero := sc 1
  let pos := sc 2
  let three := sc 3
  let eqv (x y : Expr) : TermElabM Expr := mkAppM ``BEq.beq #[x, y]
  let ult (x y : Expr) := mkApp3 (mkConst ``BitVec.ult) (mkNatLit 2) x y
  let oval (a b c : Nat) := mkAppN o #[idx[a]!, idx[b]!, idx[c]!]
  let cval (a : Nat) := mkApp colour idx[a]!
  let allowedRaw (av bv cv dv : Expr) : TermElabM Expr := do
    let az ← eqv av zero; let bz ← eqv bv zero
    let cz ← eqv cv zero; let dz ← eqv dv zero
    let an ← eqv av neg; let bn ← eqv bv neg
    let cn ← eqv cv neg; let dn ← eqv dv neg
    let ap ← eqv av pos; let bp ← eqv bv pos
    let cp ← eqv cv pos; let dp ← eqv dv pos
    let qclauses := #[
      bnot (band az bz), bnot (band az cz), bnot (band az dz),
      bnot (band bz cz), bnot (band bz dz), bnot (band cz dz),
      bor (bnot (band an cn)) bn, bor (bnot (band an cz)) bn,
      bor (bnot (band az cn)) bn, bor (bnot (band ap cp)) bp,
      bor (bnot (band ap cz)) bp, bor (bnot (band az cp)) bp,
      bor (bnot (band bn dn)) cn, bor (bnot (band bn dz)) cn,
      bor (bnot (band bz dn)) cn, bor (bnot (band bp dp)) cp,
      bor (bnot (band bp dz)) cp, bor (bnot (band bz dp)) cp,
      bor (bor (bor ap dp) bn) cn, bor (bor (bor an dn) bp) cp]
    return andChain qclauses
  let blockerRaw (a b k : Nat) : TermElabM Expr := do
    let hz ← eqv (oval a k b) zero
    return band (band (toExpr (decide (a < k)))
      (toExpr (decide (k < b)))) hz
  let mut clauses : Array Expr := #[]
  clauses := clauses.push (← eqv (cval 0) neg)
  clauses := clauses.push (← eqv (cval 1) zero)
  clauses := clauses.push (ult (cval 2) three)
  for a in [0:13] do
    for b in [a+1:13] do
      for c in [b+1:13] do
        clauses := clauses.push (ult (oval a b c) three)
  for a in [0:13] do
    for b in [a+1:13] do
      for c in [b+1:13] do
        for d in [c+1:13] do
          clauses := clauses.push (← allowedRaw
            (oval a b c) (oval a b d) (oval a c d) (oval b c d))
  for a in [0:13] do
    for b in [a+1:13] do
      let mut candidates : Array Expr := #[]
      for k in [0:13] do
        candidates := candidates.push (← blockerRaw a b k)
      clauses := clauses.push
        (bor (bnot (← eqv (cval a) (cval b))) (orChain candidates 0))
  return andTree clauses 0 clauses.size

elab "raw_bv_decide" : tactic => do
  let cfg : BVDecideConfig := {
    timeout := 300, maxSteps := 10000000
  }
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile cfg
    liftMetaFinishingTactic fun g => do
      match ← bvUnsat g ctx with
      | .ok _ => pure ()
      | .error counterExample =>
          counterExample.goal.withContext do
            throwError (← explainCounterExampleQuality counterExample)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- There is no normalized 13-point, four-coloured generalized signotope in
which every equal-coloured pair has a zero triple at an intermediate point. -/
theorem noMc13Bits (colour : Fin 13 → Code)
    (o : Fin 13 → Fin 13 → Fin 13 → Code)
    (hfinite : mc13_formula%(colour, o) = true) : False := by
  change mc13_raw_formula%(colour, o) = true at hfinite
  raw_bv_decide

end Lax56Proofs.HKBFiniteMC
