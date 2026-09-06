# Status of the convex-layer route

The supplied argument is formalized **conditional on Valtr's four-layer
lemma**, the geometric ingredient explicitly left unexpanded in the informal
proof. This is not yet an assumption-free proof of the headline theorem.

The only nonstandard axiom used by the main Lean proof is
`Lax56.ValtrFourLayer.exists_emptyHexagon_of_four_layers`:

> A finite general-position set with a minimal outer layer of at least nine
> vertices and a nonempty fourth layer contains an empty convex hexagon.

The remaining work is the sector/chain-replacement proof of this lemma in
Valtr, *On Empty Hexagons*, Section 3 (Section 2 of the
[author's preprint](https://kam.mff.cuni.cz/~valtr/h.ps)).

## What is proved

- `ConvexLayers.lean`: finite extreme layers, hull closure, transfer of
  emptiness through layer removal, and selection of a minimal polygon by
  minimizing the number of ambient points in its closed convex hull.
- `CupsCaps.lean`: the full cups/caps counting recurrence.
- `CupsCapsGeometry.lean` and `ErdosSzekeres.lean`: the weak planar
  Erdős–Szekeres bound, including the finite forbidden-parameter shear and
  supporting-function proof of convex position.
- `CyclicOrder.lean`: cyclic ordering of a convex-position set, the ordered
  hexagon bridge, and the supporting-half-plane description of a hexagon.
- `ValtrCaps.lean` and `ValtrCounting.lean`: construction of consecutive
  six-vertex caps and the inequality `|outer| ≤ 6 |next| + 5`.
- `ValtrReduction.lean`: the contradiction `216 ≤ 215` after the four-layer
  lemma empties the fourth layer.
- `EmptyHexagon.lean`: the resulting labelled empty-hexagon theorem, with
  just the four-layer lemma as its external assumption.
- The existing blocker, stability, interval, and analytic proofs, with the
  larger constants propagated all the way to `MainTheorem.lean`.

The new elementary proofs use only Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` proofs,
SAT calls, or `native_decide` proofs in the convex-layer development.

## Constants

| Quantity | Value |
| --- | --- |
| Convex-position target | `216` |
| Empty-hexagon threshold | `2^428 + 1` |
| Five-colouring threshold | `5 * 2^428 + 1` |
| Initial interval length | `10 * 2^428` |
| Deletion-fraction denominator | `10 * 2^428 + 2` |
| Density improvement | `1 / (3500 * (10 * 2^428 + 2))` |
| Headline point-set threshold | `10^(2^450)` |

The final exponent is deliberately generous, not optimized. The enormous
outer power of ten is kept symbolic in the numerical proof.

## Verification

From `proofs/`, build with `lake build Lax56Proofs`. From the submission root,
`lax build --profile --replay` additionally checks packaging and kernel replay.
The decisive axiom audit is:

```lean
import Lax56Proofs
#print axioms Lax56Proofs.MainTheorem.large_point_set_four_collinear_or_visible_six
```

The concept-layer declarations for the empty-hexagon theorem and the main
theorem are Lax theorem specifications. The proof no longer invokes the
empty-hexagon specification as an external assumption: it invokes its proved
reduction to the explicitly isolated four-layer lemma.
