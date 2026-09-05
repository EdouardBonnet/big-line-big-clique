import Lax56Proofs.HKBHexSmallEncoding

namespace Lax56Proofs.HKBHexSmallEncoding

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex6Blockers
    (role : Fin 12 → RoleCode) (colour : Fin 12 → ColourCode)
    (o : Fin 12 → Fin 12 → Fin 12 → SignCode) (inner : Fin 12 → Bool)
    (hfinite : hexSmall_formula%(12, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex7Blockers
    (role : Fin 13 → RoleCode) (colour : Fin 13 → ColourCode)
    (o : Fin 13 → Fin 13 → Fin 13 → SignCode) (inner : Fin 13 → Bool)
    (hfinite : hexSmall_formula%(13, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex8Blockers
    (role : Fin 14 → RoleCode) (colour : Fin 14 → ColourCode)
    (o : Fin 14 → Fin 14 → Fin 14 → SignCode) (inner : Fin 14 → Bool)
    (hfinite : hexSmall_formula%(14, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex9Blockers
    (role : Fin 15 → RoleCode) (colour : Fin 15 → ColourCode)
    (o : Fin 15 → Fin 15 → Fin 15 → SignCode) (inner : Fin 15 → Bool)
    (hfinite : hexSmall_formula%(15, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

end Lax56Proofs.HKBHexSmallEncoding
