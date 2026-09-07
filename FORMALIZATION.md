# Completed convex-layer proof

The proof includes Valtr's four-layer implication and the headline theorem.
Its Lax proof tree is fully grounded: composing the modular proof declarations
leaves only Lean's standard logical axioms, `propext`, `Classical.choice`, and
`Quot.sound`.

The previously external geometric input is proved as
`Lax56Proofs.ValtrFourLayer.exists_emptyHexagon_of_four_layers`:

> A finite general-position set with a minimal outer layer of at least sixteen
> vertices and a nonempty fourth layer contains an empty convex hexagon.

The relaxed local threshold 16 is sufficient for the convex 216-point
application. The empty-hexagon and headline constants do not increase.
The final both-convex endpoint argument is recorded in
[the geometric resolution](VALTR_REMAINING.md).

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
- `ValtrExtension.lean`: Valtr's empty-pentagon extension (Observation 2),
  including the exact four-sector hypothesis, finite empty-triangle selection,
  and verification of convexity and emptiness of the resulting hexagon.
- `ValtrSectors.lean` and `ValtrCyclic.lean`: convex sectors, enlargement when
  the interior apex moves toward its base, and coverage of exterior ambient
  points by radial sectors, including the cyclic wrap-around. Also proved:
  uniqueness of a line crossing, unique radial-fan triangles, preservation
  of cyclic order under rotation, and the two-sector chain's convexity and
  supporting inequalities in the nonconvex endpoint case.
- `ValtrSplice.lean`: a chain-splicing criterion from explicit supporting-edge
  inequalities, and the resulting cardinality/minimality contradiction.
  The generic criterion takes supporting inequalities as hypotheses; their
  arbitrary-length geometric application is proved in `ValtrRunSetup`.
- `ValtrSectorBounds.lean`: the single-sector bound of two outer vertices,
  and the nonconvex endpoint branch of the two-sector run bound, including
  the geometric supporting inequalities rather than assuming them.
- `ValtrPolygon.lean`: supporting-half-plane and consecutive-cap identities
  for arbitrary polygon sizes. In a hexagon-free set with nonempty interior,
  every consecutive five-vertex cap contains a vertex of the next layer.
  This proves the vertex-extraction step for Valtr's final pentagon.
- `ValtrSelection.lean` and `ValtrSectorSetup.lean`: third-layer apex
  selection, with base-triangle emptiness also against deeper layers,
  and construction of the complete initial sector data.
- `ValtrMissing.lean`: Valtr's Observation 3. Disjoint open radial sectors
  and connectedness prove the unique-edge assertion; two consecutive
  missing third-layer triangles would force an empty hexagon.
- `ValtrConvexRun.lean`: ordered empty pentagons from two outer sector
  points, and the convex-quadrilateral obstruction with its separating-side
  condition explicit, in both orientations.
- `ValtrMissingExtension.lean`, `ValtrCoverage.lean`, and `ValtrCoverSetup.lean`:
  the crossed-edge four-sector obstruction, endpoint containments proved
  from extremality and empty triangles, coverage of every outer vertex by
  a defined sector, and exhaustion of the third layer by the apices when
  every apex exists and `|A| = |B| + 1`.
- `ValtrRuns.lean`: the private-region counting that forces `|A| = |B| + 1`
  once the geometric sector-run bounds are supplied, and selection of
  private representatives with exactly one extra outer point.
- `ValtrCyclicRuns.lean` and `ValtrRunReduction.lean`: the cyclic counting
  is connected to the actual sectors. Given the run bound, it forces all
  sectors to be defined, the outer cardinality, private points, and
  exhaustion of the third layer.
- `ValtrRadialOrder.lean`: the selected apices inherit the cyclic order of
  their fan triangles, including partial selections and cyclic wrap-around.
- `ValtrMaximum.lean`, `ValtrProjective.lean`, and `ValtrLocalSupport.lean`:
  the supplied scalar maximum principle, its projective determinant
  interpretation, the local neighbor-hull relations, both endpoint
  viewpoints, and the empty-triangle support arguments.
- `ValtrRunSupport.lean` and `ValtrRunSetup.lean`: the full arbitrary-length
  nonconvex-endpoint chain replacement, constructed from the actual cyclic
  apex data and applied to the finite sector union. Neither the chain
  supports nor the local hull containments remain hypotheses of that
  application.
- `ValtrMatching.lean`: a common indexed vertex fixes the cyclic matching;
  moving the deep viewpoint preserves all apices. Under the all-fans
  condition, a fourth-layer point in a consecutive five-apex cap preserves
  the entire sector configuration.
- `ValtrCompression.lean`, `ValtrCompressedSupport.lean`,
  `ValtrShortSplice.lean`, and `ValtrShortSetup.lean`: the final shortened
  chain through the deep point has all required supports. Moving the
  center into a five-apex cap and replacing at most five outer vertices
  by this chain contradicts minimality. The five-sector cardinality bound
  is an explicit input to this helper and is supplied in the final assembly.

- `ValtrSectorArcs.lean` and `ValtrPrivateRuns.lean`: a two-point sector
  joins neighboring outer vertices, so the unique extra outer point
  belongs to at most two sectors. Among three disjoint five-sector runs,
  one therefore contains only its five private representatives. This
  completes the all-sectors endgame when there are at least 15 sectors.
- `ValtrFourLayerReduction.lean` and `ValtrRunInduction.lean`: the entire
  four-layer argument, with outer-layer threshold 16, is reduced to the
  both-convex endpoint run bound. This ordinary explicit hypothesis is
  discharged by `ValtrFourLayer`; it is not an external assumption.
  The 216-point application and all downstream numerical bounds are unchanged.
- `ValtrEndpointGeometry.lean`: the endpoint case splits yield exactly
  the indicated strictly convex quadrilaterals when the corresponding
  interior-triangle conditions fail.
- `ValtrEndpointDrop.lean`: when the opposite endpoint is nonconvex,
  forward/backward projective propagation supplies the side test for the
  empty-pentagon extension. Both mixed endpoint cases have their complete
  one-point drop bounds, including the finite cyclic index conversions.
- `ValtrExtremalRun.lean`: in a smallest failing run, the sector point
  sets are disjoint and their counts are exactly `2,1,...,1,2`. Excluding
  this structured both-convex configuration suffices for the four-layer
  theorem; the strong-induction connection is proved.

- `ValtrEdgeCaps.lean`: an inner supporting edge has at most three outer
  vertices beyond it in a hexagon-free set. Also proved: the local transfer
  of a neighboring sector into that edge's cap, using a triangle-containment
  contradiction to outer extremality.
- `ValtrEndpointCompletion.lean`: backward propagation carries a bad
  last-endpoint point beyond every base edge. Together with the cap transfer,
  this forces four distinct outer vertices into the first cap and excludes
  the both-convex pattern `2,1,...,1,2`.
- `ValtrFourLayer.lean`: the new obstruction is connected to the actual
  cyclic apex data and the existing strong induction, proving the complete
  four-layer implication with outer-layer threshold 16.

The already completed downstream reduction consists of:

- `ValtrReduction.lean`: the contradiction `216 ≤ 215` after the four-layer
  lemma empties the fourth layer.
- `EmptyHexagon.lean`: the resulting labelled empty-hexagon theorem, invoking
  the four-layer theorem interface whose proof is supplied in this package.
- The existing blocker, stability, interval, and analytic proofs, with the
  larger constants propagated all the way to `MainTheorem.lean`.

The new elementary proofs use only Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` proofs,
SAT calls, or `native_decide` proofs in the convex-layer development.

Lax concept-layer `axiom` declarations are theorem interfaces, each matched
by a proof declaration. Consumers use these interfaces so the archive can
display their dependencies, rather than importing and embedding the entire
upstream proofs. The dependency tree is:

```text
Main theorem
├── Empty-hexagon bound
│   └── Valtr's four-layer lemma
└── Vertex-removal stability
```

The two leaves use only standard logical axioms. The empty-hexagon proof
has exactly the four-layer interface as its Lax assumption. The main proof
has exactly the empty-hexagon and stability interfaces as its Lax assumptions;
it does not also inherit the four-layer interface as a direct dependency.
All three dependency edges are inferred from the checked Lean proof terms,
and the `assumptions` annotations assert that the inferred sets match this
tree. No geometric statement is left unproved.

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
The modular dependency audit is:

```lean
import Lax56Proofs
#print axioms Lax56Proofs.MainTheorem.large_point_set_four_collinear_or_visible_six
#print axioms Lax56Proofs.EmptyHexagon.exists_emptyConvexHexagon
#print axioms Lax56Proofs.ValtrFourLayer.exists_emptyHexagon_of_four_layers
#print axioms Lax56Proofs.VertexRemovalStability.exists_fiveColorable_delete
```

Besides the three standard logical axioms, these report precisely the Lax
interfaces described above. After submission, compose and audit the complete
archive proof tree with:

```sh
lax generate-prooftree lax-56 --output /tmp/lax56-proof-tree
```

The composer replaces each interface by its proof, checks the generated
theorems in Lean's kernel, and verifies the standalone module in a fresh
process. All four composed theorems must have only standard logical axioms.

Verified after the dependency-interface refactor on 2026-09-07: the full Lake
build passed (8574 jobs), and `lax build --profile --replay` passed compilation,
kernel replay, and statement inspection (6 concepts, 4 proofs). The exported
metadata was checked to contain exactly the four-node, three-edge rooted tree
above and the shortened two-sentence abstract.

The Lax composer then kernel-checked all four composed theorems. Its standalone
module passed fresh-process verification, and an independent `#print axioms`
audit of each generated theorem reported exactly `propext`, `Classical.choice`,
and `Quot.sound`.
