import Mathlib

/-!
Primitive Boolean encoding used by the finite convex-hexagon certificates.
The six hull vertices and twelve blockers are represented in lexicographic
order.  `kind = 0` is the interior distribution `3,1,1,1`; kinds 1--5 are
the exhaustive blocker-colour subcases of `2,2,1,1`.
-/

namespace Lax56Proofs.HKBHexEncoding

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

private def parity3 (a b c : Nat) : Bool :=
  (((if a > b then 1 else 0) + (if a > c then 1 else 0) +
    (if b > c then 1 else 0)) % 2) == 1

private def sort3 (a b c : Nat) : Nat × Nat × Nat :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  (lo, a + b + c - lo - hi, hi)

elab "hex18_formula%(" roleStx:term ", " colourStx:term ", " oStx:term ", "
    innerStx:term ", " kindStx:num ")" : term => do
  let finTy := mkApp (mkConst ``Fin) (mkNatLit 18)
  let mut idx : Array Expr := #[]
  for n in [0:18] do
    idx := idx.push (← Term.elabTermEnsuringType
      (Syntax.mkNumLit (toString n)) finTy)
  let sc (n : Nat) : Expr := toExpr (BitVec.ofNat 2 n)
  let rc (n : Nat) : Expr := toExpr (BitVec.ofNat 3 n)
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
  let kind := kindStx.getNat
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

  -- Reflect the whole configuration if necessary.
  clauses := clauses.push (bnot (← oeq 0 1 2 0))
  -- Six hull roles and one blocker role.
  for p in [0:18] do
    clauses := clauses.push (ult3 (rval p) seven)
  for r in [0:6] do
    let mut witnesses : Array Expr := #[]
    for p in [0:18] do
      witnesses := witnesses.push (← req p r)
    clauses := clauses.push (orTree witnesses 0 witnesses.size)
    for p in [0:18] do
      for q in [p+1:18] do
        clauses := clauses.push (bnot (band (← req p r) (← req q r)))
  -- Rotate cyclic labels so hull role zero occurs first.
  for p in [0:18] do
    for q in [0:p] do
      clauses := clauses.push (bor (bnot (← req p 0)) (bnot (hull q)))

  -- Lemma 12 and the resulting exact class sizes.
  for c in [0:4] do
    for a in [0:18] do
      for b in [a+1:18] do
        for d in [b+1:18] do
          for e in [d+1:18] do
            clauses := clauses.push (bnot (andTree #[
              band (← block a) (← ceq a c),
              band (← block b) (← ceq b c),
              band (← block d) (← ceq d c),
              band (← block e) (← ceq e c)] 0 4))
    let mut triples : Array Expr := #[]
    for a in [0:18] do
      for b in [a+1:18] do
        for d in [b+1:18] do
          triples := triples.push (andTree #[
            band (← block a) (← ceq a c),
            band (← block b) (← ceq b c),
            band (← block d) (← ceq d c)] 0 3)
    clauses := clauses.push (orTree triples 0 triples.size)
  -- Remaining colour-name symmetry.
  let colourOrders : Array (Nat × Nat) :=
    if kind == 0 then #[(1, 2), (2, 3)] else #[(0, 1), (2, 3)]
  for (earlier, later) in colourOrders do
    for p in [0:18] do
      let mut witnesses : Array Expr := #[]
      for q in [0:p] do
        witnesses := witnesses.push (band (← block q) (← ceq q earlier))
      clauses := clauses.push (bimp
        (band (← block p) (← ceq p later))
        (orTree witnesses 0 witnesses.size))

  -- Strict-interior flags.
  for p in [0:18] do
    clauses := clauses.push (bimp (ival p) (← block p))
    for i in [0:6] do
      let j := (i + 1) % 6
      for a in [0:18] do
        for b in [0:18] do
          if a != b && p != a && p != b then
            let edge := band (← req a i) (← req b j)
            clauses := clauses.push
              (bimp (band (ival p) edge) (← oeq a b p 2))
  -- Exact per-colour interior counts, encoded extensionally to keep the
  -- resulting proof term shallow.
  for c in [0:4] do
    let mut members : Array Expr := #[]
    for p in [0:18] do
      members := members.push (andTree #[← block p, ← ceq p c, ival p] 0 3)
    let target := if kind == 0 then (#[3, 1, 1, 1] : Array Nat)[c]!
      else (#[2, 2, 1, 1] : Array Nat)[c]!
    let mut witnesses : Array Expr := #[]
    if target == 1 then
      witnesses := members
      for a in [0:18] do
        for b in [a+1:18] do
          clauses := clauses.push (bnot (band members[a]! members[b]!))
    else if target == 2 then
      for a in [0:18] do
        for b in [a+1:18] do
          witnesses := witnesses.push (band members[a]! members[b]!)
          for d in [b+1:18] do
            clauses := clauses.push
              (bnot (andTree #[members[a]!, members[b]!, members[d]!] 0 3))
    else
      for a in [0:18] do
        for b in [a+1:18] do
          for d in [b+1:18] do
            witnesses := witnesses.push
              (andTree #[members[a]!, members[b]!, members[d]!] 0 3)
            for e in [d+1:18] do
              clauses := clauses.push (bnot (andTree
                #[members[a]!, members[b]!, members[d]!, members[e]!] 0 4))
    clauses := clauses.push (orTree witnesses 0 witnesses.size)

  -- The five exhaustive subcases of the `2,2,1,1` distribution.  Under the
  -- colour normalization above, kinds 1--3 mean that the colour-0 pair is
  -- blocked by colour 1 and the colour-1 pair by 0,2,3 respectively; kinds
  -- 4 and 5 mean that the colour-0 pair is blocked by colour 2 or 3.
  if kind != 0 then
    let target0 := if kind <= 3 then 1 else if kind == 4 then 2 else 3
    for a in [0:18] do
      for b in [a+1:18] do
        let antecedent := andTree #[← block a, ← block b,
          ← ceq a 0, ← ceq b 0, ival a, ival b] 0 6
        let mut witnesses : Array Expr := #[]
        for k in [a+1:b] do
          witnesses := witnesses.push (andTree #[← block k,
            ← ceq k target0, ← oeq a k b 1, ival k] 0 4)
        clauses := clauses.push
          (bimp antecedent (orTree witnesses 0 witnesses.size))
    if kind <= 3 then
      let target1 := if kind == 1 then 0 else if kind == 2 then 2 else 3
      for a in [0:18] do
        for b in [a+1:18] do
          let antecedent := andTree #[← block a, ← block b,
            ← ceq a 1, ← ceq b 1, ival a, ival b] 0 6
          let mut witnesses : Array Expr := #[]
          for k in [a+1:b] do
            witnesses := witnesses.push (andTree #[← block k,
              ← ceq k target1, ← oeq a k b 1, ival k] 0 4)
          clauses := clauses.push
            (bimp antecedent (orTree witnesses 0 witnesses.size))

  -- Three-valued generalized signotope constraints.
  for a in [0:18] do
    for b in [a+1:18] do
      for c in [b+1:18] do
        clauses := clauses.push (ult2 (oval a b c) three)
  for a in [0:18] do
    for b in [a+1:18] do
      for c in [b+1:18] do
        for d in [c+1:18] do
          let av := oval a b c
          let bv := oval a b d
          let cv := oval a c d
          let dv := oval b c d
          let az ← eqv av zero
          let bz ← eqv bv zero
          let cz ← eqv cv zero
          let dz ← eqv dv zero
          let an ← eqv av neg
          let bn ← eqv bv neg
          let cn ← eqv cv neg
          let dn ← eqv dv neg
          let ap ← eqv av pos
          let bp ← eqv bv pos
          let cp ← eqv cv pos
          let dp ← eqv dv pos
          clauses := clauses.push (bnot (band az bz))
          clauses := clauses.push (bnot (band az cz))
          clauses := clauses.push (bnot (band az dz))
          clauses := clauses.push (bnot (band bz cz))
          clauses := clauses.push (bnot (band bz dz))
          clauses := clauses.push (bnot (band cz dz))
          clauses := clauses.push (bor (bnot (band an cn)) bn)
          clauses := clauses.push (bor (bnot (band an cz)) bn)
          clauses := clauses.push (bor (bnot (band az cn)) bn)
          clauses := clauses.push (bor (bnot (band ap cp)) bp)
          clauses := clauses.push (bor (bnot (band ap cz)) bp)
          clauses := clauses.push (bor (bnot (band az cp)) bp)
          clauses := clauses.push (bor (bnot (band bn dn)) cn)
          clauses := clauses.push (bor (bnot (band bn dz)) cn)
          clauses := clauses.push (bor (bnot (band bz dn)) cn)
          clauses := clauses.push (bor (bnot (band bp dp)) cp)
          clauses := clauses.push (bor (bnot (band bp dz)) cp)
          clauses := clauses.push (bor (bnot (band bz dp)) cp)
          clauses := clauses.push (orTree #[ap, dp, bn, cn] 0 4)
          clauses := clauses.push (orTree #[an, dn, bp, cp] 0 4)

  -- Convex hull half-planes.
  for i in [0:6] do
    let j := (i + 1) % 6
    for a in [0:18] do
      for b in [0:18] do
        if a != b then
          let edge := band (← req a i) (← req b j)
          for p in [0:18] do
            if p != a && p != b then
              let nonneg := bor (← oeq a b p 2) (← oeq a b p 1)
              clauses := clauses.push
                (bimp (band edge (← block p)) nonneg)
              let otherHull := andTree #[hull p,
                bnot (← req p i), bnot (← req p j)] 0 3
              clauses := clauses.push
                (bimp (band edge otherHull) (← oeq a b p 2))

  -- Hull sides are blocked on the boundary; all non-side chords are blocked
  -- by strict-interior points.
  for i in [0:6] do
    for j in [i+1:6] do
      let isEdge := j == i + 1 || (i == 0 && j == 5)
      for a in [0:18] do
        for b in [0:18] do
          if a != b then
            let antecedent := band (← req a i) (← req b j)
            let lo := min a b
            let hi := max a b
            let mut blockers : Array Expr := #[]
            for k in [lo+1:hi] do
              let location := if isEdge then bnot (ival k) else ival k
              blockers := blockers.push (andTree #[← block k,
                ← oeq lo k hi 1, location] 0 3)
            clauses := clauses.push
              (bimp antecedent (orTree blockers 0 blockers.size))

  -- Proper four-colouring of the blocker set.  A blocker between a strict
  -- interior endpoint and any hull point is again strict interior.
  for a in [0:18] do
    for b in [a+1:18] do
      let mut blockers : Array Expr := #[]
      for k in [a+1:b] do
        let different := bnot (← eqv (cval k) (cval a))
        blockers := blockers.push (andTree #[← block k,
          ← oeq a k b 1, different,
          bimp (bor (ival a) (ival b)) (ival k)] 0 4)
      let blocked := orTree blockers 0 blockers.size
      for c in [0:4] do
        let antecedent := andTree #[← block a, ← block b,
          ← ceq a c, ← ceq b c] 0 4
        clauses := clauses.push (bimp antecedent blocked)
  return andTree clauses 0 clauses.size

open Lean.Elab.Tactic
open Lean.Elab.Tactic.BVDecide.Frontend

/-- Run the external search and verify its LRAT certificate inside Lean. -/
elab "hex_bv_decide" : tactic => do
  let cfg : BVDecideConfig := {
    timeout := 300, maxSteps := 10000000
  }
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile cfg
    liftMetaFinishingTactic fun g => do
      match ← bvUnsat g ctx with
      | .ok _ => pure ()
      | .error _ => throwError "finite hexagon certificate has a counterexample"

end Lax56Proofs.HKBHexEncoding
