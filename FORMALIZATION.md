# Status of the convex-layer route

The supplied argument is formalized **conditional on Valtr's four-layer
lemma**, the geometric ingredient explicitly left unexpanded in the informal
proof. This is not yet an assumption-free proof of the headline theorem.

The only nonstandard axiom used by the main Lean proof is
`Lax56.ValtrFourLayer.exists_emptyHexagon_of_four_layers`:

> A finite general-position set with a minimal outer layer of at least nine
> vertices and a nonempty fourth layer contains an empty convex hexagon.

The remaining work is the both-convex endpoint case of the sector-run bound in
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
  is still an explicit input to this application.

- `ValtrSectorArcs.lean` and `ValtrPrivateRuns.lean`: a two-point sector
  joins neighboring outer vertices, so the unique extra outer point
  belongs to at most two sectors. Among three disjoint five-sector runs,
  one therefore contains only its five private representatives. This
  completes the all-sectors endgame when there are at least 15 sectors.
- `ValtrFourLayerReduction.lean` and `ValtrRunInduction.lean`: the entire
  four-layer argument, with outer-layer threshold 16, is reduced to the
  both-convex endpoint run bound. This remains an ordinary explicit
  hypothesis, not a new axiom. The 216-point application and all downstream
  numerical bounds are unchanged.
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

The both-convex endpoint counting estimate is **not yet proved**. All other
endpoint cases, the run induction, and subsequent geometric steps are
proved. `four_layer_of_doubly_convex_run_bound` isolates the remaining case,
including the available bounds on both shorter runs.
`ValtrExtremalRun.four_layer_of_extremal_run_obstruction` narrows the
remaining input further to that disjoint exact-count configuration.
See [the remaining gap](VALTR_REMAINING.md).

The already completed downstream reduction consists of:

- `ValtrReduction.lean`: the contradiction `216 ≤ 215` after the four-layer
  lemma empties the fourth layer.
- `EmptyHexagon.lean`: the resulting labelled empty-hexagon theorem, with
  just the four-layer lemma as its external assumption.
- The existing blocker, stability, interval, and analytic proofs, with the
  larger constants propagated all the way to `MainTheorem.lean`.

The new elementary proofs use only Lean's standard logical axioms
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry` proofs,
SAT calls, or `native_decide` proofs in the convex-layer development.

The new four-layer preparatory lemmas do not discharge the four-layer axiom
and are not used to claim that the main theorem is now assumption-free.

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
