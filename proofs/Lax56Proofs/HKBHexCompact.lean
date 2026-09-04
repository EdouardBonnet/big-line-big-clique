module

public import Lax56Proofs.HKBFiniteMC

@[expose] public section

/-!
A compact, semantics-oriented Boolean encoding of the finite hexagon-blocking
problem.  All finite quantifiers are represented by `List.ofFn`; after the
cardinality parameter is instantiated, `bv_decide` unfolds them to a finite
circuit.  Keeping the logical families behind named definitions avoids the
enormous elaboration stack of a fully unrolled source term.
-/

namespace Lax56Proofs.HKBHexCompact

open Lax56Proofs.HKBFiniteMC

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

def allFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.ofFn f).all id

def anyFin {n : Nat} (f : Fin n → Bool) : Bool :=
  (List.ofFn f).any id

def boolImp (x y : Bool) : Bool := boolOr (!x) y

def roleCode (i : Fin 6) : RoleCode := BitVec.ofNat 3 i.val

def isHull {n : Nat} (role : Fin n → RoleCode) (p : Fin n) : Bool :=
  (role p).ult (BitVec.ofNat 3 6)

def isBlocker {n : Nat} (role : Fin n → RoleCode) (p : Fin n) : Bool :=
  role p == BitVec.ofNat 3 6

def flipSignCode (s : SignCode) : SignCode :=
  if s == BitVec.ofNat 2 0 then BitVec.ofNat 2 2
  else if s == BitVec.ofNat 2 2 then BitVec.ofNat 2 0
  else s

/-- Read the sign of an arbitrarily ordered triple from values stored only on
increasing triples.  The callers below guard all uses by distinctness. -/
def orderedOrientation {n : Nat}
    (o : Fin n → Fin n → Fin n → SignCode)
    (a b c : Fin n) : SignCode :=
  if a < b then
    if b < c then o a b c
    else if a < c then flipSignCode (o a c b)
    else o c a b
  else
    if a < c then flipSignCode (o b a c)
    else if b < c then o b c a
    else flipSignCode (o c b a)

def orientationIs {n : Nat}
    (o : Fin n → Fin n → Fin n → SignCode)
    (a b c : Fin n) (s : SignCode) : Bool :=
  orderedOrientation o a b c == s

def roleConstraints {n : Nat} (role : Fin n → RoleCode) : Bool :=
  allFin fun p => (role p).ult (BitVec.ofNat 3 7) &&
  allFin fun i : Fin 6 =>
    anyFin (fun p => role p == roleCode i) &&
    allFin fun p => allFin fun q =>
      boolImp (decide (p ≠ q))
        (!(role p == roleCode i && role q == roleCode i))

/-- Rotate the cyclic hull labels so role zero is the first hull point in the
ambient order. -/
def hullRotationConstraint {n : Nat} (role : Fin n → RoleCode) : Bool :=
  allFin fun p => allFin fun q =>
    boolImp (decide (q < p) && (role p == BitVec.ofNat 3 0)) (!isHull role q)

/-- Restricted-growth naming removes the permutation symmetry of the four
blocker colours. -/
def colourNamingConstraint {n : Nat}
    (role : Fin n → RoleCode) (colour : Fin n → ColourCode) : Bool :=
  allFin fun later : Fin 4 =>
    if later.val = 0 then true
    else allFin fun p =>
      boolImp (isBlocker role p &&
          (colour p == BitVec.ofNat 2 later.val))
        (anyFin fun q => decide (q < p) && isBlocker role q &&
          (colour q == BitVec.ofNat 2 (later.val - 1)))

def interiorConstraint {n : Nat}
    (role : Fin n → RoleCode)
    (o : Fin n → Fin n → Fin n → SignCode)
    (inner : Fin n → Bool) : Bool :=
  allFin fun p =>
    boolImp (inner p) (isBlocker role p) &&
    allFin fun i : Fin 6 => allFin fun a => allFin fun b =>
      boolImp (inner p && decide (p ≠ a) && decide (p ≠ b) &&
          decide (a ≠ b) && (role a == roleCode i) &&
          (role b == roleCode (i + 1)))
        (orientationIs o a b p (BitVec.ofNat 2 2))

def innerCount {n : Nat} (inner : Fin n → Bool) : BitVec 5 :=
  (List.ofFn inner).foldl
    (fun acc b => acc + if b then BitVec.ofNat 5 1 else BitVec.ofNat 5 0)
    (BitVec.ofNat 5 0)

def exactInteriorConstraint {n : Nat} (k : Nat)
    (inner : Fin n → Bool) : Bool :=
  innerCount inner == BitVec.ofNat 5 k

def orientationConstraints {n : Nat}
    (o : Fin n → Fin n → Fin n → SignCode) : Bool :=
  allFin fun a => allFin fun b => allFin fun c =>
    boolImp (decide (a < b) && decide (b < c))
      (validSignCode (o a b c)) &&
  allFin fun a => allFin fun b => allFin fun c => allFin fun d =>
    boolImp (decide (a < b) && decide (b < c) && decide (c < d))
      (allowedQuadCode (o a b c) (o a b d) (o a c d) (o b c d))

def hullConstraint {n : Nat}
    (role : Fin n → RoleCode)
    (o : Fin n → Fin n → Fin n → SignCode) : Bool :=
  allFin fun i : Fin 6 => allFin fun a => allFin fun b => allFin fun p =>
    let edge := decide (a ≠ b) && (role a == roleCode i) &&
      (role b == roleCode (i + 1))
    let away := decide (p ≠ a) && decide (p ≠ b)
    boolImp (edge && away && isBlocker role p)
        (boolOr (orientationIs o a b p (BitVec.ofNat 2 2))
          (orientationIs o a b p (BitVec.ofNat 2 1))) &&
      boolImp (edge && away && isHull role p &&
          !(role p == roleCode i) && !(role p == roleCode (i + 1)))
        (orientationIs o a b p (BitVec.ofNat 2 2))

def isHexEdge (i j : Fin 6) : Bool :=
  decide (j = i + 1 ∨ (i = 0 ∧ j = 5))

def betweenBlocker {n : Nat}
    (role : Fin n → RoleCode)
    (o : Fin n → Fin n → Fin n → SignCode)
    (inner : Fin n → Bool) (edge : Bool)
    (a b k : Fin n) : Bool :=
  decide (min a b < k) && decide (k < max a b) && isBlocker role k &&
    orientationIs o a k b (BitVec.ofNat 2 1) &&
    (if edge then !inner k else inner k)

def hullPairsBlocked {n : Nat}
    (role : Fin n → RoleCode)
    (o : Fin n → Fin n → Fin n → SignCode)
    (inner : Fin n → Bool) : Bool :=
  allFin fun i : Fin 6 => allFin fun j : Fin 6 =>
    allFin fun a => allFin fun b =>
      boolImp (decide (i < j) && decide (a ≠ b) &&
          (role a == roleCode i) && (role b == roleCode j))
        (anyFin fun k => betweenBlocker role o inner (isHexEdge i j) a b k)

def colouredPairBlocker {n : Nat}
    (role : Fin n → RoleCode) (colour : Fin n → ColourCode)
    (o : Fin n → Fin n → Fin n → SignCode)
    (inner : Fin n → Bool) (a b k : Fin n) : Bool :=
  decide (a < k) && decide (k < b) && isBlocker role k &&
    orientationIs o a k b (BitVec.ofNat 2 1) && !(colour k == colour a) &&
    boolImp (boolOr (inner a) (inner b)) (inner k)

def properBlockerColouring {n : Nat}
    (role : Fin n → RoleCode) (colour : Fin n → ColourCode)
    (o : Fin n → Fin n → Fin n → SignCode)
    (inner : Fin n → Bool) : Bool :=
  allFin fun a => allFin fun b =>
    boolImp (decide (a < b) && isBlocker role a && isBlocker role b &&
        (colour a == colour b))
      (anyFin fun k => colouredPairBlocker role colour o inner a b k)

def hexFormula {n : Nat} (kInner : Nat) (first second third : Fin n)
    (role : Fin n → RoleCode) (colour : Fin n → ColourCode)
    (o : Fin n → Fin n → Fin n → SignCode)
    (inner : Fin n → Bool) : Bool :=
  !(orientationIs o first second third (BitVec.ofNat 2 0)) &&
  roleConstraints role && hullRotationConstraint role &&
  colourNamingConstraint role colour && interiorConstraint role o inner &&
  exactInteriorConstraint kInner inner && orientationConstraints o &&
  hullConstraint role o && hullPairsBlocked role o inner &&
  properBlockerColouring role colour o inner

attribute [bv_normalize] allFin anyFin boolImp roleCode isHull isBlocker
  flipSignCode orderedOrientation orientationIs roleConstraints
  hullRotationConstraint colourNamingConstraint interiorConstraint innerCount
  exactInteriorConstraint orientationConstraints hullConstraint isHexEdge
  betweenBlocker hullPairsBlocked colouredPairBlocker properBlockerColouring
  hexFormula

open Lean.Elab.Tactic
open Lean.Elab.Tactic.BVDecide.Frontend

elab "hex_compact_bv_decide" : tactic => do
  let cfg : BVDecideConfig := { timeout := 300, maxSteps := 10000000 }
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
theorem noHex10BlockersCompact
    (role : Fin 16 → RoleCode) (colour : Fin 16 → ColourCode)
    (o : Fin 16 → Fin 16 → Fin 16 → SignCode)
    (inner : Fin 16 → Bool)
    (hfinite : hexFormula 4 0 1 2 role colour o inner = true) : False := by
  bv_decide (timeout := 300) (maxSteps := 10000000)

end Lax56Proofs.HKBHexCompact
