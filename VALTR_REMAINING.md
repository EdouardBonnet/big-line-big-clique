# Current geometric gap in Valtr's argument

Reference: Pavel Valtr, *On Empty Hexagons*, Section 3.3 of the published
paper, Section 2.3 of the [author's preprint](https://kam.mff.cuni.cz/~valtr/h.ps).

This file records a formalization gap, not a claim that the published
mathematical argument is incorrect. The four-layer theorem is still an
explicit external axiom in the main proof.

## Newly proved in Lean

- Observation 1, in a boundary-safe form: a point outside the outer layer
  and outside the closed hull of the fourth layer belongs to the second
  or third layer (`ConvexLayers.mem_middle_layers_of_not_mem_fourth_hull`).
- Observation 2, with the paper's four-sector condition:
  `ValtrExtension.empty_pentagon_extension`. The point nearest the closing
  edge is chosen by a finite minimum. All boundary, convexity, and emptiness
  checks are proved; no empty-polygon theorem is assumed.
- Sector convexity and the inclusion
  `sector(a,d,b) ⊆ sector(a,c,b)` when `c` lies in the triangle `dab` and is
  different from its base vertices (`ValtrSectors.sector_triangle_mono`).
- Radial-sector coverage of every ambient point outside an inner polygon
  (`ValtrCyclic.exists_radial_sector_of_not_mem_hull`). General position
  eliminates the boundary rays, and a finite cyclic sign transition selects
  the relevant edge.
- A supported-chain replacement is in convex position and contradicts
  minimality when no more vertices are deleted than inserted
  (`ValtrSplice.convexPosition_splice_of_edge_supports` and
  `ValtrSplice.not_minimal_of_supported_splice`).
- The one-sector bound of two outer points, and both the convexity and
  supporting inequalities of the replacement in the two-sector nonconvex
  endpoint case (`ValtrSectorBounds` and `ValtrSectors.two_sector_chain_support`).
- Uniqueness of the line crossing and radial fan triangle, including cyclic
  wrap-around (`ValtrCyclic`).
- Selection of every defined apex in the third layer, including exclusion
  of deeper-layer points from its base triangle (`ValtrSelection`), and
  construction of the full initial sector configuration (`ValtrSectorSetup`).
- Observation 3: two consecutive radial triangles cannot both miss the
  third layer (`ValtrMissing.meetsThirdLayer_or_next`). The unique-edge
  assertion is proved using disjoint open radial sectors and connectedness
  of an outer edge; the resulting three-vertex obstruction is reduced to
  the verified empty-triangle sector bound.
- The defined sectors cover every outer-layer vertex
  (`ValtrCoverSetup.outer_vertex_mem_defined_sector`). Missing sectors are
  handled using the actual crossed third-layer edge: its four-sector is
  empty of ambient points, its endpoints lie in the triangles determined
  by the neighboring selected apices, and exclusion from both neighboring
  sectors forces membership in that forbidden four-sector
  (`ValtrMissingExtension`, `ValtrCoverage`). This supplies the coverage
  consequence of Observation 4 without assuming the paper's diagram.
- The convex-quadrilateral endpoint obstruction, with its required
  separating-side condition explicit (`ValtrConvexRun.convex_quad_side_card_le_one`).
  Deriving that side condition for the private part of an arbitrary run
  is still outstanding.
- All defined apices have different indices, and in the `|A| = |B| + 1`
  case with every apex defined they exhaust the third layer
  (`ValtrCoverSetup.third_layer_eq_all_apices`).
- The cap identity for every consecutive vertex block, and existence of a
  next-layer vertex inside every consecutive five-vertex cap of a
  hexagon-free set with nonempty interior (`ValtrPolygon`).
- The private-region counting that excludes `|A| = |B| + 2`, forces
  `|A| = |B| + 1`, and chooses distinct private representatives with exactly
  one extra point, conditional on the sector-run cardinality bounds
  (`ValtrRuns`).

## Closed gap: the supporting inequalities for the replacement

Use Valtr's configuration in a finite general-position set with no empty
hexagon: a minimal outer layer `A` and successive layers `B, C, D`, a fixed
`d ∈ D`, clockwise vertices `b₁,...,bβ` of `B`, and selected points
`cᵢ ∈ C ∩ conv{d,bᵢ,bᵢ₊₁}` whose base triangles are empty. Write

```
Sᵢ = sector(bᵢ,cᵢ,bᵢ₊₁),
U  = S₁ ∪ ... ∪ Sₜ,
R  = A \ U,
H  = [b₁,c₁,...,cₜ,bₜ₊₁],       2 ≤ t < β.
```

In the nonconvex-quadrilateral branch of Lemma 2, the two endpoint conditions
are that `c₁` is inside `conv{b₁,b₂,c₂}` and `cₜ` is inside
`conv{bₜ,bₜ₊₁,cₜ₋₁}`. The paper then asserts that `H` is convex and that
replacing `A ∩ U` by its vertices gives a convex-position set.

The formal splice criterion reduces this assertion to the following explicit
inequalities. Orient the chain counterclockwise (reverse the paper's clockwise
listing). For every chain edge `uv`, excluding the closing chord of `H`, prove

```
turn u v w ≥ 0   for every vertex w of H,     -- hchain
turn u v a ≥ 0   for every retained a ∈ R.    -- hcross
```

For every `t ≥ 2`, both groups of inequalities are now proved. The key
local relation places each `cᵢ` in the hull of its two chain neighbors and
the two base vertices. From an exterior viewpoint, a positive affine
height functional turns oriented-edge signs into comparisons of real
projective coordinates. The scalar maximum principle propagates any
ascent until it either encounters a removed sector or contradicts an
endpoint condition. Strict supporting functionals handle the two endpoint
viewpoints, and the empty base triangles handle the end edges against `C`.

`ValtrRunSetup.not_minimal_of_nonconvex_run_card_le` constructs the entire
configuration from the actual cyclic layers and apex data and proves the
minimality contradiction from `|A ∩ U| ≤ t + 2`. It does not take `hchain`,
`hcross`, or the local neighbor-hull relations as hypotheses.

The supporting modules are `ValtrMaximum`, `ValtrProjective`,
`ValtrLocalSupport`, `ValtrRunSupport`, and `ValtrRunSetup`.
`ValtrRadialOrder` proves cyclic order of partial apex selections.
`ValtrCyclicRuns` and `ValtrRunReduction` connect the assumed run bound
to the actual sector counting and all-sectors conclusions.

## Next geometric gap: the convex-endpoint branch

For a clockwise run `S₁,...,Sₜ`, set

```
W = (A ∩ S₁) \ (S₂ ∪ ... ∪ Sₜ).
```

When `b₁,c₁,c₂,b₂` is a strictly convex quadrilateral in that order,
Valtr's proof asserts `|W| ≤ 1`, using an empty pentagon formed from two
points of `W` and applying Observation 2 with `c₂`. The detailed
four-sector justification for this invocation is not yet formalized.
The existing `convex_quad_side_card_le_one` proves a restricted version
with an explicit separating-side condition; it does not yet prove the
full claim about `W`. An informal expansion has been requested.

## Other parts of the four-layer argument still to formalize

This is the current obstacle, not the final outstanding line of the theorem.
Also remaining are completion of the sector-run induction, geometric
identification of the private regions, and the final chain replacement
and matching argument with `d′`. Radial order of the apices themselves is
now proved, but the final matching argument is not yet assembled.
The private-region cardinality calculation and extraction of a next-layer
vertex from a five-vertex cap are now separately proved.

None of these statements has been added as a new axiom or represented by
`sorry`. The only nonstandard assumption of the main proof remains the
explicit four-layer declaration.
