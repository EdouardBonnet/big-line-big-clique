module

public import Lax56Proofs.HKBFiniteMC

@[expose] public section

/-!
Compatibility import for the finite `mc₃(4) ≤ 12` interface.

The readable predicates now occur directly in `mc13_formula%`.  Consequently
the geometric proof and the checked bit-vector certificate share one formula,
and no separate large Boolean reassociation theorem is required.
-/
