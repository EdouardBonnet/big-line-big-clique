import Lax56Proofs.HKBHexSmallEncoding

namespace Lax56Proofs.HKBHexSmallEncoding

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
theorem noHex12BlockersFull
    (role : Fin 18 → RoleCode) (colour : Fin 18 → ColourCode)
    (o : Fin 18 → Fin 18 → Fin 18 → SignCode) (inner : Fin 18 → Bool)
    (hfinite : hexSmall_formula%(18, role, colour, o, inner) = true) : False := by
  hexSmall_bv_decide

end Lax56Proofs.HKBHexSmallEncoding
