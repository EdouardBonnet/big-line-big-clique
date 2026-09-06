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

## Exact current obstacle: the supporting inequalities for the replacement

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

Deriving these inequalities from the nested layers, the radial choices of
the `cᵢ`, sector exclusion, and the two endpoint conditions remains unproved.
In particular, convexity of `C` alone does not supply `hcross`, since the
retained vertices are outside `conv(C)`. A detailed supporting-line argument
for these inequalities is the most useful next informal input.

With these inequalities and the counting input `|A ∩ U| ≤ t + 2`, the new
Lean splice theorem already handles the
outer vertices, both chain endpoints, closed boundaries, cardinality, and
the contradiction with minimality. Retained outer vertices remain extreme
because the entire replacement set lies in the original hull.

## Other parts of the four-layer argument still to formalize

This is the current obstacle, not the final outstanding line of the theorem.
Also remaining are the full selection of `cᵢ` in layer `C`, Observations 3
and 4 and the associated missing-sector coverage, the other branches of
the sector-run induction, the counting of runs/private regions, and the
final change-of-interior-point argument with `d′`.

None of these statements has been added as a new axiom or represented by
`sorry`. The only nonstandard assumption of the main proof remains the
explicit four-layer declaration.
