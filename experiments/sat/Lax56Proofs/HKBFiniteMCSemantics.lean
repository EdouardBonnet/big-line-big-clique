import Lax56Proofs.HKBFiniteMCBridge
import Lax56Proofs.Orientation

/-! Readable predicates used to connect geometry to the primitive finite
certificate in `HKBFiniteMC`. -/

namespace Lax56Proofs.HKBFiniteMC

local notation "Code" => BitVec 2

open Lax56Proofs.Orientation

/-- Primitive encoding of the three orientation signs used by the finite
certificate. -/
def signCode : Sign → Code
  | .neg => BitVec.ofNat 2 0
  | .zero => BitVec.ofNat 2 1
  | .pos => BitVec.ofNat 2 2

@[simp] theorem validSignCode_signCode (s : Sign) :
    validSignCode (signCode s) = true := by
  cases s <;> decide

theorem allowedQuadCode_of_allowedQuad (a b c d : Sign)
    (h : AllowedQuad a b c d) :
    allowedQuadCode (signCode a) (signCode b) (signCode c) (signCode d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [AllowedQuad, coneRule, weakNeg, weakPos, signCode, allowedQuadCode,
      boolOr]

theorem blockedPairCode_of_candidate
    (colour : Fin 13 → Code) (o : Fin 13 → Fin 13 → Fin 13 → Code)
    {a b k : Fin 13} (hc : colour a = colour b)
    (hak : a < k) (hkb : k < b) (hz : o a k b = signCode .zero) :
    blockedPairCode colour o a b = true := by
  fin_cases k <;>
    simp_all [blockedPairCode, blockerCandidate, boolOr, signCode]

theorem blockedPairCode_of_ne
    (colour : Fin 13 → Code) (o : Fin 13 → Fin 13 → Fin 13 → Code)
    {a b : Fin 13} (hc : colour a ≠ colour b) :
    blockedPairCode colour o a b = true := by
  simp [blockedPairCode, boolOr, hc]

end Lax56Proofs.HKBFiniteMC
