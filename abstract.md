We formalize the theorem that every finite set of at least
$10^{2^{450}}$ points in the real plane contains either four collinear
points or six points that are pairwise visible with respect to the whole
set.  Visibility means that the open segment joining a pair contains no
point of the ambient finite set.

The proof follows Bonnet's interval-and-harmonic-weight argument. The
quantitative Hujter--Kisfaludi-Bak bound for 5-colourable point-visibility
graphs and the vertex-removal form of Erdős--Simonovits stability for
$K_6$-free graphs are proved in Lean in this package. We also prove Valtr's
four-layer implication for a minimal outer layer of at least sixteen
vertices. From it we derive the empty-convex-hexagon bound
$h(6) \le 2^{428}+1$, using 216 points in convex position. The minimum-polygon
selection, the consecutive-layer inequality, the weak Erdős--Szekeres theorem,
and the cyclic-order bridge are formalized in Lean. The last endpoint case
is resolved by a supporting-edge cap bound and projective propagation.
The headline theorem uses only Lean's standard logical axioms, with no
external geometric assumption, `sorry`, or SAT-based proof step.
