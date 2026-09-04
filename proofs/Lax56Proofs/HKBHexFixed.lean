module

public import Lax56Proofs.HKBFiniteMC

@[expose] public section

/-!
A fixed-label finite encoding for a four-colour-blocked convex hexagon.

Indices `0,...,5` are the cyclic hull vertices.  The next six indices are the
chosen blockers on the six sides, in cyclic order, and any remaining indices
are strict-interior blockers.  Unlike the earlier lexicographic encoding, this
one uses the coordinate-free three-term Grassmann--Plücker identity.  It thus
needs neither hull-role variables nor an unknown permutation of the points.
-/

namespace Lax56Proofs.HKBHexFixed

open Lax56Proofs.HKBFiniteMC

local notation "Code" => BitVec 2

def flipCode (s : Code) : Code :=
  bif s == BitVec.ofNat 2 0 then BitVec.ofNat 2 2
  else bif s == BitVec.ofNat 2 2 then BitVec.ofNat 2 0
  else s

def mulSignCode (a b : Code) : Code :=
  bif boolOr (a == BitVec.ofNat 2 1) (b == BitVec.ofNat 2 1) then
    BitVec.ofNat 2 1
  else bif a == b then BitVec.ofNat 2 2
  else BitVec.ofNat 2 0

/-- The sign consequence of `A + B + C = 0`: either all three terms vanish,
or a positive and a negative term both occur. -/
def sumThreeZeroCode (a b c : Code) : Bool :=
  let neg := BitVec.ofNat 2 0
  let zero := BitVec.ofNat 2 1
  let pos := BitVec.ofNat 2 2
  let hasNeg := boolOr (boolOr (a == neg) (b == neg)) (c == neg)
  let hasPos := boolOr (boolOr (a == pos) (b == pos)) (c == pos)
  let allZero := (a == zero) && (b == zero) && (c == zero)
  boolOr (hasNeg && hasPos) allZero

/-- Boolean Grassmann--Plücker rule for the six determinants occurring in
`D(x,a,b)D(x,c,d) - D(x,a,c)D(x,b,d) + D(x,a,d)D(x,b,c)=0`. -/
def grassmannPlueckerCode (xab xcd xac xbd xad xbc : Code) : Bool :=
  sumThreeZeroCode (mulSignCode xab xcd)
    (flipCode (mulSignCode xac xbd)) (mulSignCode xad xbc)

/-- At most one of the four triples of four distinct points is collinear. -/
def noTwoZeroCode (a b c d : Code) : Bool :=
  let z := BitVec.ofNat 2 1
  !(a == z && b == z) && !(a == z && c == z) &&
  !(a == z && d == z) && !(b == z && c == z) &&
  !(b == z && d == z) && !(c == z && d == z)

/-- `q` is certified to lie between `a` and `b`, using a reference point off
their line.  The first argument is `χ(a,q,b)` and the next three are
`χ(a,q,r)`, `χ(q,b,r)`, and `χ(a,b,r)`. -/
def betweenCode (aqb aqr qbr abr : Code) : Bool :=
  aqb == BitVec.ofNat 2 1 && aqr == abr && qbr == abr

open Lean Elab Term Meta

private meta def bnot (x : Expr) : Expr := mkApp (mkConst ``Bool.not) x
private meta def band (x y : Expr) : Expr := mkApp2 (mkConst ``Bool.and) x y
private meta def bor (x y : Expr) : Expr := bnot (band (bnot x) (bnot y))
private meta def bimp (x y : Expr) : Expr := bor (bnot x) y

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

private meta partial def chooseFrom (start n k : Nat) : Array (Array Nat) :=
  if k == 0 then #[#[]]
  else Id.run do
    let mut out := #[]
    for x in [start:n] do
      if k - 1 ≤ n - (x + 1) then
        for tail in chooseFrom (x + 1) n (k - 1) do
          out := out.push (#[x] ++ tail)
    return out

private meta def parity3 (a b c : Nat) : Bool :=
  (((if a > b then 1 else 0) + (if a > c then 1 else 0) +
    (if b > c then 1 else 0)) % 2) == 1

private meta def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  (lo, a + b + c - lo - hi, hi)

private meta def fixedHexExpr (blockersStx kindStx : TSyntax `num)
    (colourStx oStx : TSyntax `term)
    (raw : Bool) : TermElabM Expr := do
  let blockers := blockersStx.getNat
  let kind := kindStx.getNat
  if blockers < 6 || 12 < blockers then
    throwError "fixedHex_formula expects 6 ≤ blockers ≤ 12"
  let targets : Array Nat :=
    if blockers == 10 && kind == 0 then #[3, 3, 3, 1]
    else if blockers == 10 && kind == 1 then #[3, 3, 2, 2]
    else if blockers == 11 && kind == 0 then #[3, 3, 3, 2]
    else if blockers == 12 && kind == 0 then #[3, 3, 3, 3]
    else #[]
  if targets.isEmpty then
    throwError "unsupported blocker-count / colour-distribution case"
  let n := blockers + 6
  let finTy := mkApp (mkConst ``Fin) (mkNatLit n)
  let blockerTy := mkApp (mkConst ``Fin) (mkNatLit blockers)
  let mut idx : Array Expr := #[]
  for p in [0:n] do
    idx := idx.push (← Term.elabTermEnsuringType
      (Syntax.mkNumLit (toString p)) finTy)
  let mut bidx : Array Expr := #[]
  for p in [0:blockers] do
    bidx := bidx.push (← Term.elabTermEnsuringType
      (Syntax.mkNumLit (toString p)) blockerTy)
  let colour ← Term.elabTerm colourStx none
  let o ← Term.elabTerm oStx none
  let sc (x : Nat) : Expr := toExpr (BitVec.ofNat 2 x)
  let zero := sc 1
  let pos := sc 2
  let three := sc 3
  let codeTy := mkApp (mkConst ``BitVec) (mkNatLit 2)
  let beqInst ← synthInstance (mkApp (mkConst ``BEq [.zero]) codeTy)
  let eqv (x y : Expr) : Expr :=
    mkApp4 (mkConst ``BEq.beq [.zero]) codeTy beqInst x y
  let bcond (c t e : Expr) : Expr :=
    mkApp4 (mkConst ``cond [.succ .zero]) codeTy c t e
  let flipRaw (s : Expr) : Expr :=
    bcond (eqv s (sc 0)) (sc 2) (bcond (eqv s (sc 2)) (sc 0) s)
  let mulRaw (a b : Expr) : Expr :=
    bcond (bor (eqv a zero) (eqv b zero)) zero
      (bcond (eqv a b) pos (sc 0))
  let sumRaw (a b c : Expr) : Expr :=
    let hasNeg := bor (bor (eqv a (sc 0)) (eqv b (sc 0))) (eqv c (sc 0))
    let hasPos := bor (bor (eqv a pos) (eqv b pos)) (eqv c pos)
    let allZero := band (band (eqv a zero) (eqv b zero)) (eqv c zero)
    bor (band hasNeg hasPos) allZero
  let gpRaw (xab xcd xac xbd xad xbc : Expr) : Expr :=
    sumRaw (mulRaw xab xcd) (flipRaw (mulRaw xac xbd)) (mulRaw xad xbc)
  let noTwoRaw (a b c d : Expr) : Expr :=
    let xs := #[bnot (band (eqv a zero) (eqv b zero)),
      bnot (band (eqv a zero) (eqv c zero)),
      bnot (band (eqv a zero) (eqv d zero)),
      bnot (band (eqv b zero) (eqv c zero)),
      bnot (band (eqv b zero) (eqv d zero)),
      bnot (band (eqv c zero) (eqv d zero))]
    xs[1...*].foldl (init := xs[0]!) band
  let betweenRaw (aqb aqr qbr abr : Expr) : Expr :=
    band (band (eqv aqb zero) (eqv aqr abr)) (eqv qbr abr)
  let ult (x y : Expr) := mkApp3 (mkConst ``BitVec.ult) (mkNatLit 2) x y
  let ovalSorted (a b c : Nat) := mkAppN o #[idx[a]!, idx[b]!, idx[c]!]
  let oval (a b c : Nat) : Expr :=
    let (x, y, z) := sort3 a b c
    let v := ovalSorted x y z
    if parity3 a b c then
      if raw then flipRaw v else mkApp (mkConst ``flipCode) v
    else v
  let cval (k : Nat) := mkApp colour bidx[k]!
  let between (a q b r : Nat) :=
    let aqb := oval a q b; let aqr := oval a q r
    let qbr := oval q b r; let abr := oval a b r
    if raw then betweenRaw aqb aqr qbr abr
    else mkAppN (mkConst ``betweenCode) #[aqb, aqr, qbr, abr]
  let mut clauses : Array Expr := #[]
  -- Exact colour-class sizes.  The two ten-blocker distributions are split
  -- into separate certificates; eleven and twelve blockers have one each.
  for c in [0:4] do
    let target := targets[c]!
    let mut enough : Array Expr := #[]
    for ss in chooseFrom 0 blockers target do
      let same := ss.map fun p => eqv (cval p) (sc c)
      enough := enough.push (andTree same 0 same.size)
    clauses := clauses.push (orTree enough 0 enough.size)
    for ss in chooseFrom 0 blockers (target + 1) do
      let same := ss.map fun p => eqv (cval p) (sc c)
      clauses := clauses.push (bnot (andTree same 0 same.size))
  -- Equal-size colour classes are named by their first occurrences.
  for later in [1:4] do
    if targets[later - 1]! == targets[later]! then
      for p in [0:blockers] do
        let mut earlier : Array Expr := #[]
        for q in [0:p] do
          earlier := earlier.push (eqv (cval q) (sc (later - 1)))
        clauses := clauses.push (bimp (eqv (cval p) (sc later))
          (orTree earlier 0 earlier.size))
  -- Every stored orientation is one of negative, zero, positive.
  for a in [0:n] do
    for b in [a+1:n] do
      for c in [b+1:n] do
        clauses := clauses.push (ult (ovalSorted a b c) three)
  -- No four points are collinear.
  for a in [0:n] do
    for b in [a+1:n] do
      for c in [b+1:n] do
        for d in [c+1:n] do
          let av := ovalSorted a b c; let bv := ovalSorted a b d
          let cv := ovalSorted a c d; let dv := ovalSorted b c d
          clauses := clauses.push (if raw then noTwoRaw av bv cv dv
            else mkAppN (mkConst ``noTwoZeroCode) #[av, bv, cv, dv])
  -- Rank-three Grassmann--Plücker identities.  Group the five pivot choices
  -- belonging to one five-set to keep the reflection proof shallow.
  for ss in chooseFrom 0 n 5 do
    let mut gps : Array Expr := #[]
    for pivotPos in [0:5] do
      let x := ss[pivotPos]!
      let mut rest : Array Nat := #[]
      for t in [0:5] do
        if t != pivotPos then rest := rest.push ss[t]!
      let a := rest[0]!; let b := rest[1]!
      let c := rest[2]!; let d := rest[3]!
      let xab := oval x a b; let xcd := oval x c d
      let xac := oval x a c; let xbd := oval x b d
      let xad := oval x a d; let xbc := oval x b c
      gps := gps.push (if raw then gpRaw xab xcd xac xbd xad xbc
        else mkAppN (mkConst ``grassmannPlueckerCode)
          #[xab, xcd, xac, xbd, xad, xbc])
    clauses := clauses.push (andTree gps 0 gps.size)
  -- Strict counterclockwise cyclic convexity of the six hull vertices, and
  -- closed-hull membership of every blocker.
  for i in [0:6] do
    let j := (i + 1) % 6
    for v in [0:6] do
      if v != i && v != j then
        clauses := clauses.push (eqv (oval i j v) pos)
    for k in [0:blockers] do
      clauses := clauses.push (bor (eqv (oval i j (6 + k)) pos)
        (eqv (oval i j (6 + k)) zero))
  -- The first six blockers lie on the corresponding hull sides.
  for i in [0:6] do
    let j := (i + 1) % 6
    let r := (i + 2) % 6
    clauses := clauses.push (between i (6 + i) j r)
  -- Every diagonal has a strict-interior blocker.  Labels 6,...,11 are the
  -- side blockers, so strict-interior blocker labels begin at 12.
  for i in [0:6] do
    for j in [i+1:6] do
      let isEdge := j == i + 1 || (i == 0 && j == 5)
      if !isEdge then
        let r := Id.run do
          for t in [0:6] do
            if t != i && t != j then return t
          return 0
        let mut witnesses : Array Expr := #[]
        for k in [6:blockers] do
          witnesses := witnesses.push (between i (6 + k) j r)
        clauses := clauses.push (orTree witnesses 0 witnesses.size)
  -- Proper four-colouring of the blocker set.  If either endpoint is strict
  -- interior, convexity forces its blocker to be strict interior as well.
  for a in [0:blockers] do
    for b in [a+1:blockers] do
      let mut witnesses : Array Expr := #[]
      for k in [0:blockers] do
        if k != a && k != b then
          let location := if a >= 6 || b >= 6 then toExpr (decide (6 ≤ k))
            else mkConst ``Bool.true
          witnesses := witnesses.push (andTree #[
            between (6 + a) (6 + k) (6 + b) 0,
            bnot (eqv (cval k) (cval a)), location] 0 3)
      clauses := clauses.push (bimp (eqv (cval a) (cval b))
        (orTree witnesses 0 witnesses.size))
  return andTree clauses 0 clauses.size

/-- Readable finite formula, with named local determinant predicates. -/
elab "fixedHex_formula%(" blockersStx:num ", " kindStx:num ", " colourStx:term ", "
    oStx:term ")" : term =>
  fixedHexExpr blockersStx kindStx colourStx oStx false

/-- Definitionally equal primitive expansion used by the bit-vector checker. -/
elab "fixedHex_raw_formula%(" blockersStx:num ", " kindStx:num ", " colourStx:term ", "
    oStx:term ")" : term =>
  fixedHexExpr blockersStx kindStx colourStx oStx true

open Lean.Elab.Tactic
open Lean.Elab.Tactic.BVDecide.Frontend

elab "fixed_hex_bv_decide" : tactic => do
  let cfg : BVDecideConfig := { timeout := 300, maxSteps := 10000000 }
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile cfg
    liftMetaFinishingTactic fun g => do
      match ← bvUnsat g ctx with
      | .ok _ => pure ()
      | .error counterExample =>
          counterExample.goal.withContext do
            throwError (← explainCounterExampleQuality counterExample)

end Lax56Proofs.HKBHexFixed
