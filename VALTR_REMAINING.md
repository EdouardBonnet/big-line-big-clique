# Resolution of the final Valtr endpoint case

The geometric gap previously recorded in this file is closed.
The proof is in `ValtrEdgeCaps.lean`, `ValtrEndpointCompletion.lean`,
and `ValtrFourLayer.lean`. The final four-layer theorem uses only
`propext`, `Classical.choice`, and `Quot.sound`.

Reference: Pavel Valtr, *On Empty Hexagons*, Section 3.3 of the published
paper, Section 2.3 of the [author's preprint](https://kam.mff.cuni.cz/~valtr/h.ps).
The following argument supplies the previously missing both-convex case.

## Setting

Let \(A,B,C,D\) be successive convex layers of a finite general-position
set \(P\), with \(A\) minimal and \(D\) nonempty. Assume that \(P\) has no
empty convex hexagon. In a clockwise run of \(t\ge2\) defined sectors,
write
\[
 S_i=\{x:[b_i,c_i,x]>0,\ [c_i,b_{i+1},x]>0,\
                     [b_i,b_{i+1},x]>0\},\qquad U_i=A\cap S_i.
\]
Here \(c_i\in C\) lies strictly in the fan triangle \(d b_i b_{i+1}\),
and the triangle \(b_i c_i b_{i+1}\) is empty.

The verified strong induction reduces failure of the run bound to:
the \(U_i\) are pairwise disjoint, their counts are \(2,1,\ldots,1,2\),
and both endpoint quadrilaterals
\[
 (b_1,c_1,c_2,b_2),\qquad(b_t,c_{t-1},c_t,b_{t+1})
\]
are strictly convex in the displayed counterclockwise order.

No disjointness of the planar sectors is assumed. The selected \(C\)-points
need not be consecutive or exhaust \(C\).

## 1. An edge cap contains at most three outer vertices

For each base edge let
\[
 E_i=\{x\in A:[b_i,b_{i+1},x]>0\}.
\]
Then \(|E_i|\le3\).

Indeed, four points of \(E_i\), together with \(b_i,b_{i+1}\), are in
convex position: outer vertices remain extreme, and the base line supports
both new endpoints. Their hull is empty. Every inner point lies on the
opposite side of the base line, while an unselected outer vertex cannot
belong to the hull of other ambient points. General position leaves only
the two base endpoints on the line.

This is `emptyHexagon_of_four_outer_edge_points`.

## 2. The local transfer into the preceding cap

The following elementary implication is central. For consecutive
clockwise base vertices \(a,b,f\), an inner point \(e\), and \(x\in P\),
suppose
\[
 [a,b,x]>0,\quad[b,e,x]>0,\quad x\notin S(b,e,f).
\]
Then every outer vertex \(y\in S(b,e,f)\) satisfies \([a,b,y]>0\).

To verify it, the inner supporting inequalities give
\[
 [a,b,e]<0,\quad[a,b,f]<0,\quad[b,e,f]>0.
\]
The determinant identity
\[
 -[a,b,f]\,[b,e,x]
 =-[a,b,e]\,[b,f,x]-[b,e,f]\,[a,b,x]
\]
first implies \([b,f,x]>0\). Sector exclusion then gives
\([e,f,x]\le0\).

For \(y\in S(b,e,f)\), another determinant identity gives
\[
 [b,e,f]\,[f,x,y]
 =-[e,f,x]\,[b,f,y]+[b,f,x]\,[e,f,y]>0.
\]
If \([a,b,y]\le0\), then
\[
 -[a,b,e]\,[x,b,y]
 =[a,b,x]\,[b,e,y]-[a,b,y]\,[b,e,x]>0.
\]
Together with \([b,f,y]>0\), these put \(y\) strictly inside the triangle
\(bfx\), contrary to outer extremality.

This is `next_sector_in_previous_cap`.

## 3. A first-endpoint point puts the second sector in \(E_1\)

The already proved empty-pentagon extension implies that at most one point
of \(U_1\) satisfies \([c_2,b_2,x]>0\). Since \(|U_1|=2\), choose
\(x\in U_1\) with \([c_2,b_2,x]<0\); general position makes the inequality
strict.

Thus \([b_1,b_2,x]>0\) and \([b_2,c_2,x]>0\). Disjointness gives
\(x\notin S_2\). Apply Section 2 with
\[
 (a,b,e,f)=(b_1,b_2,c_2,b_3)
\]
to obtain \(U_2\subseteq E_1\). Also \(U_1\subseteq E_1\).

If \(t=2\), the four distinct points of \(U_1\cup U_2\) already contradict
\(|E_1|\le3\).

## 4. A last-endpoint point propagates into every base cap

Suppose \(t\ge3\). The mirrored empty-pentagon extension and \(|U_t|=2\)
give \(y\in U_t\) with \([b_t,c_{t-1},y]<0\).

View the inner polygon from \(y\), using a positive-height projective
coordinate \(\sigma\). Write \(z_i=\sigma(c_i)\), \(a_i=\sigma(b_i)\).
Then
\[
 z_{t-1}<a_t<z_t<a_{t+1}.
\]
For every internal index \(2\le i<t\), the local convex-hull relation
\[
 c_i\in\operatorname{conv}\{c_{i-1},b_i,b_{i+1},c_{i+1}\}
\]
provides a strictly smaller projective neighbor. Sector exclusion forbids
\(a_i<z_i<a_{i+1}\). Backward induction consequently gives
\[
 z_i<z_{i+1},\qquad z_i<a_{i+1}\quad(1\le i<t).
\]
No endpoint local-hull condition is used here.

These inequalities say \([c_i,b_{i+1},y]>0\). Starting with
\([b_t,b_{t+1},y]>0\), the reversed base-edge implication
`previous_base_pos` carries positivity backward:
\[
 [b_i,b_{i+1},y]>0\quad(1\le i\le t).
\]
In particular, \(y\in E_1\). This is
`last_bad_point_beyond_bases`.

Now \(E_1\) contains the two points of \(U_1\), the point of \(U_2\), and
the point \(y\in U_t\). They are distinct by the extremal disjointness
pattern. This again contradicts \(|E_1|\le3\).

## Consequence

`extremal_run_impossible` closes the last geometric case.
`ValtrFourLayer.extremal_run_obstruction` connects the clockwise
indices to the existing cyclic strong induction. The resulting theorem
proves the four-layer implication for a minimal outer layer of at least
16 vertices.

The 216-point application is unchanged: \(16\le216\), and the three
successive counting bounds are still \(5,35,215\). Hence the empty-hexagon
threshold remains \(2^{428}+1\), and the headline threshold remains
\(10^{2^{450}}\).
