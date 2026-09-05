import Lax56Proofs.HKBHexSmallEncoding

namespace Lax56Proofs.HKBHexSmallEncoding

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex11Blockers
    (role : Fin 17 → RoleCode) (colour : Fin 17 → ColourCode)
    (o : Fin 17 → Fin 17 → Fin 17 → SignCode) (inner : Fin 17 → Bool)
    (hfinite : hexSmall_formula%(17, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

end Lax56Proofs.HKBHexSmallEncoding
