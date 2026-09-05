import Lax56Proofs.HKBHexSmallEncoding

namespace Lax56Proofs.HKBHexSmallEncoding

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex10Blockers
    (role : Fin 16 → RoleCode) (colour : Fin 16 → ColourCode)
    (o : Fin 16 → Fin 16 → Fin 16 → SignCode) (inner : Fin 16 → Bool)
    (hfinite : hexSmall_formula%(16, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

end Lax56Proofs.HKBHexSmallEncoding
