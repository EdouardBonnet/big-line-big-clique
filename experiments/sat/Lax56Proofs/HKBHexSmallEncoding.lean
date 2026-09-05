import Mathlib

/-! Generic finite encoding for a convex hexagon with fewer than twelve blockers. -/

namespace Lax56Proofs.HKBHexSmallEncoding

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

open Lean Elab Term Meta

private def bnot (x : Expr) : Expr := mkApp (mkConst ``Bool.not) x
private def band (x y : Expr) : Expr := mkApp2 (mkConst ``Bool.and) x y
private def bor (x y : Expr) : Expr := bnot (band (bnot x) (bnot y))
private def bimp (x y : Expr) : Expr := bor (bnot x) y

private partial def andTree (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi <= lo then mkConst ``Bool.true
  else if hi = lo + 1 then xs[lo]!
  else
    let mid := lo + (hi - lo) / 2
    band (andTree xs lo mid) (andTree xs mid hi)

private partial def orTree (xs : Array Expr) (lo hi : Nat) : Expr :=
  if hi <= lo then mkConst ``Bool.false
  else if hi = lo + 1 then xs[lo]!
  else
    let mid := lo + (hi - lo) / 2
    bor (orTree xs lo mid) (orTree xs mid hi)

private partial def chooseFrom (start n k : Nat) : Array (Array Nat) :=
  if k == 0 then #[#[]]
  else Id.run do
    let mut out := #[]
    for x in [start:n] do
      if k - 1 ≤ n - (x + 1) then
        for tail in chooseFrom (x + 1) n (k - 1) do
          out := out.push (#[x] ++ tail)
    return out

private def parity3 (a b c : Nat) : Bool :=
  (((if a > b then 1 else 0) + (if a > c then 1 else 0) +
    (if b > c then 1 else 0)) % 2) == 1

private def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  (lo, a + b + c - lo - hi, hi)

/-- `n` is six plus the exact blocker count.  The strict-interior count is
therefore `n-12`, since a no-four-collinear blocked strict hexagon has exactly
one boundary blocker on each of its six sides. -/
elab "hexSmall_formula%(" nStx:num ", " roleStx:term ", " colourStx:term ", "
    oStx:term ", " innerStx:term ")" : term => do
  let n := nStx.getNat
  if n < 12 || 18 < n then
    throwError "hexSmall_formula expects 12 ≤ n ≤ 18"
  let finTy := mkApp (mkConst ``Fin) (mkNatLit n)
  let mut idx : Array Expr := #[]
  for p in [0:n] do
    idx := idx.push (← Term.elabTermEnsuringType
      (Syntax.mkNumLit (toString p)) finTy)
  let sc (x : Nat) : Expr := toExpr (BitVec.ofNat 2 x)
  let rc (x : Nat) : Expr := toExpr (BitVec.ofNat 3 x)
  let neg := sc 0
  let zero := sc 1
  let pos := sc 2
  let three := sc 3
  let six := rc 6
  let seven := rc 7
  let role ← Term.elabTerm roleStx none
  let colour ← Term.elabTerm colourStx none
  let o ← Term.elabTerm oStx none
  let inner ← Term.elabTerm innerStx none
  let eqv (x y : Expr) : TermElabM Expr := mkAppM ``BEq.beq #[x, y]
  let ult2 (x y : Expr) := mkApp3 (mkConst ``BitVec.ult) (mkNatLit 2) x y
  let ult3 (x y : Expr) := mkApp3 (mkConst ``BitVec.ult) (mkNatLit 3) x y
  let oval (a b c : Nat) := mkAppN o #[idx[a]!, idx[b]!, idx[c]!]
  let rval (p : Nat) := mkApp role idx[p]!
  let cval (p : Nat) := mkApp colour idx[p]!
  let ival (p : Nat) := mkApp inner idx[p]!
  let req (p r : Nat) : TermElabM Expr := eqv (rval p) (rc r)
  let ceq (p c : Nat) : TermElabM Expr := eqv (cval p) (sc c)
  let block (p : Nat) : TermElabM Expr := req p 6
  let hull (p : Nat) : Expr := ult3 (rval p) six
  let oeq (a b c s : Nat) : TermElabM Expr := do
    let (x, y, z) := sort3 a b c
    let s := if parity3 a b c then
      if s == 0 then 2 else if s == 2 then 0 else s
    else s
    eqv (oval x y z) (sc s)
  let mut clauses : Array Expr := #[]
  clauses := clauses.push (bnot (← oeq 0 1 2 0))
  for p in [0:n] do
    clauses := clauses.push (ult3 (rval p) seven)
  for r in [0:6] do
    let mut witnesses : Array Expr := #[]
    for p in [0:n] do
      witnesses := witnesses.push (← req p r)
    clauses := clauses.push (orTree witnesses 0 witnesses.size)
    for p in [0:n] do
      for q in [p+1:n] do
        clauses := clauses.push (bnot (band (← req p r) (← req q r)))
  for p in [0:n] do
    for q in [0:p] do
      clauses := clauses.push (bor (bnot (← req p 0)) (bnot (hull q)))
  -- Canonical restricted-growth naming for the four colours.
  for later in [1:4] do
    for p in [0:n] do
      let mut earlier : Array Expr := #[]
      for q in [0:p] do
        earlier := earlier.push (band (← block q) (← ceq q (later - 1)))
      clauses := clauses.push (bimp
        (band (← block p) (← ceq p later))
        (orTree earlier 0 earlier.size))
  -- Strict-interior flags and their exact global count.
  for p in [0:n] do
    clauses := clauses.push (bimp (ival p) (← block p))
    for i in [0:6] do
      let j := (i + 1) % 6
      for a in [0:n] do
        for b in [0:n] do
          if a != b && p != a && p != b then
            let edge := band (← req a i) (← req b j)
            clauses := clauses.push
              (bimp (band (ival p) edge) (← oeq a b p 2))
  let kInner := n - 12
  let mut atLeast : Array Expr := #[]
  for ss in chooseFrom 0 n kInner do
    let terms := ss.map fun p => ival p
    atLeast := atLeast.push (andTree terms 0 terms.size)
  clauses := clauses.push (orTree atLeast 0 atLeast.size)
  for ss in chooseFrom 0 n (kInner + 1) do
    let terms := ss.map fun p => ival p
    clauses := clauses.push (bnot (andTree terms 0 terms.size))
  -- Generalized signotope.
  for a in [0:n] do
    for b in [a+1:n] do
      for c in [b+1:n] do
        clauses := clauses.push (ult2 (oval a b c) three)
  for a in [0:n] do
    for b in [a+1:n] do
      for c in [b+1:n] do
        for d in [c+1:n] do
          let av := oval a b c
          let bv := oval a b d
          let cv := oval a c d
          let dv := oval b c d
          let az ← eqv av zero; let bz ← eqv bv zero
          let cz ← eqv cv zero; let dz ← eqv dv zero
          let an ← eqv av neg; let bn ← eqv bv neg
          let cn ← eqv cv neg; let dn ← eqv dv neg
          let ap ← eqv av pos; let bp ← eqv bv pos
          let cp ← eqv cv pos; let dp ← eqv dv pos
          let quadClauses := #[
            bnot (band az bz), bnot (band az cz), bnot (band az dz),
            bnot (band bz cz), bnot (band bz dz), bnot (band cz dz),
            bor (bnot (band an cn)) bn, bor (bnot (band an cz)) bn,
            bor (bnot (band az cn)) bn, bor (bnot (band ap cp)) bp,
            bor (bnot (band ap cz)) bp, bor (bnot (band az cp)) bp,
            bor (bnot (band bn dn)) cn, bor (bnot (band bn dz)) cn,
            bor (bnot (band bz dn)) cn, bor (bnot (band bp dp)) cp,
            bor (bnot (band bp dz)) cp, bor (bnot (band bz dp)) cp,
            orTree #[ap, dp, bn, cn] 0 4,
            orTree #[an, dn, bp, cp] 0 4]
          clauses := clauses.push (andTree quadClauses 0 quadClauses.size)
  -- Closed hull and strict hull vertices.
  for i in [0:6] do
    let j := (i + 1) % 6
    for a in [0:n] do
      for b in [0:n] do
        if a != b then
          let edge := band (← req a i) (← req b j)
          for p in [0:n] do
            if p != a && p != b then
              clauses := clauses.push (bimp (band edge (← block p))
                (bor (← oeq a b p 2) (← oeq a b p 1)))
              let otherHull := andTree #[hull p,
                bnot (← req p i), bnot (← req p j)] 0 3
              clauses := clauses.push
                (bimp (band edge otherHull) (← oeq a b p 2))
  -- Block all hull pairs, tracking boundary versus interior.
  for i in [0:6] do
    for j in [i+1:6] do
      let isEdge := j == i + 1 || (i == 0 && j == 5)
      for a in [0:n] do
        for b in [0:n] do
          if a != b then
            let lo := min a b; let hi := max a b
            let mut witnesses : Array Expr := #[]
            for q in [lo+1:hi] do
              let loc := if isEdge then bnot (ival q) else ival q
              witnesses := witnesses.push (andTree #[← block q,
                ← oeq lo q hi 1, loc] 0 3)
            clauses := clauses.push (bimp
              (band (← req a i) (← req b j))
              (orTree witnesses 0 witnesses.size))
  -- Proper colouring of blockers.
  for a in [0:n] do
    for b in [a+1:n] do
      let mut witnesses : Array Expr := #[]
      for q in [a+1:b] do
        witnesses := witnesses.push (andTree #[← block q,
          ← oeq a q b 1, bnot (← eqv (cval q) (cval a)),
          bimp (bor (ival a) (ival b)) (ival q)] 0 4)
      let blocked := orTree witnesses 0 witnesses.size
      for c in [0:4] do
        clauses := clauses.push (bimp (andTree #[← block a, ← block b,
          ← ceq a c, ← ceq b c] 0 4) blocked)
  return andTree clauses 0 clauses.size

open Lean.Elab.Tactic
open Lean.Elab.Tactic.BVDecide.Frontend

elab "hexSmall_bv_decide" : tactic => do
  let cfg : BVDecideConfig := { timeout := 300, maxSteps := 10000000 }
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile cfg
    liftMetaFinishingTactic fun g => do
      match ← bvUnsat g ctx with
      | .ok _ => pure ()
      | .error _ => throwError "finite small-hexagon certificate has a counterexample"

end Lax56Proofs.HKBHexSmallEncoding
