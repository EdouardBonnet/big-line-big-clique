import Lax56Proofs.HKBHexEncoding

namespace Lax56Proofs.HKBHexEncoding

local notation "SignCode" => BitVec 2
local notation "RoleCode" => BitVec 3
local notation "ColourCode" => BitVec 2

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- `2,2,1,1`: doubled class 0 is blocked by class 1, and doubled class 1
is blocked by class 0. -/
theorem noHex12_2211_A
    (role : Fin 18 → RoleCode) (colour : Fin 18 → ColourCode)
    (o : Fin 18 → Fin 18 → Fin 18 → SignCode) (inner : Fin 18 → Bool)
    (hfinite : hex18_formula%(role, colour, o, inner, 1) = true) : False := by
  hex_bv_decide

end Lax56Proofs.HKBHexEncoding
