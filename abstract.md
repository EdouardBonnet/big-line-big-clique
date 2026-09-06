We formalize the theorem that every finite set of at least
$10^{2^{450}}$ points in the real plane contains either four collinear
points or six points that are pairwise visible with respect to the whole
set.  Visibility means that the open segment joining a pair contains no
point of the ambient finite set.

The proof follows Bonnet's interval-and-harmonic-weight argument. The
quantitative Hujter--Kisfaludi-Bak bound for 5-colourable point-visibility
graphs and the vertex-removal form of Erdős--Simonovits stability for
$K_6$-free graphs are proved in Lean in this package. The remaining external
assumption is Valtr's four-layer lemma for a minimal outer layer of at least
nine vertices. From it we prove the empty-convex-hexagon bound
$h(6) \le 2^{428}+1$, using 216 points in convex position. The minimum-polygon
selection, the consecutive-layer inequality, the weak Erdős--Szekeres theorem,
and the cyclic-order bridge are formalized in Lean. The four-layer lemma itself
is not yet formalized, so the headline result remains conditional on that input.
