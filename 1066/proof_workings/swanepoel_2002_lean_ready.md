# Swanepoel 2002 Lamport-style proof plan

Source: `../Proof_Files/Sw02.pdf`

Paper: K. J. Swanepoel, "Independence Numbers of Planar Contact Graphs",
Discrete & Computational Geometry 28 (2002), 649-670.

Current-status note, 2026-05-19: this is a source-paper roadmap, not the live
Lean handoff.  It should be read for paper structure and obligations; check
`theorem_dependency_map.md` for current Lean route status before starting work.

Purpose of this file: give a numbered Markdown proof plan whose numbered
claims can be transcribed later into Lean lemmas.  This is not Lean code.
Unproved Lean theorem targets are written as comments only.

```lean
-- Euclidean Erdos 1066 target.
-- theorem swanepoel_lower_bound_8_31
--     (n : Nat) (C : UDConfig n) :
--     exists s : Finset (Fin n),
--       C.IsIndep s and 31 * s.card >= 8 * n

-- Separate target from Section 5 of Swanepoel.
-- theorem nonparalleloid_contact_graph_has_linear_improvement
--     (C : ConvexDisc)
--     (hC : NotParalleloid C) :
--     exists c : Real, 1 / 4 < c and
--       forall n (packing : PackingOfTranslates C n),
--         c * n <= alpha (contactGraph packing)
```

## 0. Scope and corrections

0.1. The Euclidean theorem is Swanepoel Theorem 1.

Statement:

```text
For every n-point Euclidean set P with minimum distance 1, there is a subset
S of size at least 8n/31 such that every two distinct points of S have
distance greater than 1.
```

Lean form:

```text
forall (C : UDConfig n), exists s, C.IsIndep s and 31 * s.card >= 8 * n.
```

0.2. The nonparalleloid theorem is Swanepoel Theorem 2.

Statement:

```text
If C is not a paralleloid, then there exists c > 1/4 such that every contact
graph of a packing of n translates of C has independence number at least c*n.
```

0.3. Separation rule.

The Euclidean proof uses:

```text
Sections 1-3: general minimum-distance/broken-lattice machinery.
Section 4: Euclidean Lemma 10 and the m=8 contradiction.
```

The Euclidean proof does not use:

```text
Section 5, Lemmas 11-15, proper Brass compactness, or nonparalleloid geometry.
```

0.4. Corrected audit items.

0.4.1. The Euclidean `8/31` proof does not use a penny-graph edge bound.
Any note claiming a dependency on an edge bound such as
`3n - sqrt(12n - 3)` is incorrect for this paper's proof.

0.4.2. Contact graphs reduce through the difference body:

```text
C + x1 and C + x2 touch/overlap/are disjoint
iff x1 - x2 is on/in/outside C - C.
```

A formal proof must choose one scale:

```text
unit ball = C - C: contact edge distance = 1;
unit ball = (1/2) * (C - C): contact edge distance = 2.
```

Use the first convention unless a later API makes the second cheaper.

0.4.3. Lemma 8 gives `r_i,s_i` for `i = 1,...,2m-5`.  Swanepoel Theorem 4
summarizes only the internal range needed in the theorem statement, but
Euclidean Lemma 10 uses the full Lemma 8 range.

0.4.4. Lemma 9 is a late-triple lemma:

```text
if s_i = r_{i+1} for i = a,a+1,a+2, then a >= 2m - 10.
```

For `m=8`, this lower bound is `6`.

## 1. Euclidean theorem E

### E. Theorem: Euclidean lower bound `8/31`

Assumptions:

E.A1. `n : Nat`.

E.A2. `C : UDConfig n`; i.e. `C.pts : Fin n -> R2` and distinct points have
Euclidean distance at least `1`.

Conclusion:

E.C1. There exists `s : Finset (Fin n)` such that:

```text
C.IsIndep s
31 * s.card >= 8 * n.
```

Proof dependencies:

```text
E1-E3: Euclidean geometric graph facts.
E4-E7: minimal-counterexample graph machinery.
E8-E13: boundary angle and arc machinery.
E14-E16: long nonconcave arc.
E17-E20: broken-lattice obstruction.
E21-E24: Euclidean Lemma 10 and m=8 contradiction.
```

Lean transcription notes:

Use integer inequality `31 * s.card >= 8 * n`; avoid real-valued cardinal
bounds in the final theorem.

## 2. Euclidean geometric graph obligations

### E1. Claim: Euclidean unit-distance graph

Statement:

Given `C : UDConfig n`, define a finite simple graph `G_C` on `Fin n` by:

```text
Adj(i,j) iff i != j and eucDist (C.pts i) (C.pts j) = 1.
```

Then `C.IsIndep s` is equivalent to `s` being graph-independent in `G_C`.

Dependencies:

```text
UDConfig.sep;
definition of UDConfig.IsIndep.
```

Proof:

1. Expand `G_C.Adj`.
2. Expand graph independence on `s`.
3. Use the `i != j` side condition to match the definition of `C.IsIndep`.
4. No geometric inequality beyond `UDConfig.sep` is needed.

Lean transcription notes:

Make this a simp lemma after deciding the graph representation.

### E2. Claim: Planarity and degree bound

Statement:

For a Euclidean minimum-distance graph `G_C`:

```text
G_C has a planar straight-line embedding;
forall v, degree_G_C(v) <= 6.
```

Dependencies:

```text
Euclidean noncrossing lemma for unit-distance/minimum-distance edges;
Euclidean kissing-number-in-plane bound <= 6.
```

Proof obligations:

1. Noncrossing: if segments `ab` and `cd` are distinct unit edges between
   minimum-distance points, their relative interiors do not cross.
2. Degree bound: neighbours of a vertex lie on the Euclidean unit circle and
   are pairwise at Euclidean distance at least `1`; the circular angle gaps
   are at least `pi/3`, hence at most six neighbours exist.

Lean transcription notes:

This may be proved directly in Euclidean geometry.  Do not import the
nonparalleloid theorem.  A future normed-plane generalization can replace this
with Swanepoel Proposition 2.

### E3. Claim: Euclidean angle facts used by Section 3

Statement:

The Euclidean proof needs the following facts for the straight-line embedding:

```text
E3.1. A simple closed n-gon has angle sum pi*(n-2).
E3.2. If pq = qr <= pr, then angle pqr >= pi/3.
E3.3. If abcd is a simple quadrilateral with
      ab = bc = cd <= ad, ac, bd,
      then angle_b + angle_c >= pi.
E3.4. Every face angle of a Euclidean minimum-distance graph is at least pi/3.
E3.5. In a nontriangular face, any two consecutive face angles sum to at least pi.
```

Dependencies:

```text
Euclidean angle API;
law of cosines;
polygon angle sum;
minimum-distance condition.
```

Proof obligations:

1. Prove E3.2 from the cosine rule:
   `pr^2 = pq^2 + qr^2 - 2*pq*qr*cos(angle pqr)`.
2. Prove E3.3 either by Swanepoel Proposition 4 specialized to Euclidean
   geometry or by direct Euclidean case analysis.
3. Derive E3.4 and E3.5 from E3.2 and E3.3 applied to face boundaries.

Lean transcription notes:

These are the Euclidean replacements for Brass-measure Proposition 4.

### E4. Claim: Four-cycle and `K_{2,3}` exclusions

Statement:

For a Euclidean minimum-distance graph:

```text
E4.1. Every graph four-cycle is drawn as a convex quadrilateral.
E4.2. K_{2,3} is not a subgraph.
```

Dependencies:

```text
E2 noncrossing;
E3 quadrilateral angle/convexity facts;
minimum-distance condition.
```

Proof obligations:

1. If a four-cycle were nonconvex, one vertex would lie in the triangle formed
   by the other three.  Use unit edge lengths and minimum-distance constraints
   to derive a contradiction.
2. If `K_{2,3}` existed with bipartition `{a,b}` and `{p,q,r}`, then the three
   quadrilaterals `apbq`, `apbr`, `aqbr` could not all be convex without
   crossing or violating E4.1.

Lean transcription notes:

Make E4.2 available as both a noninduced-subgraph exclusion and a local
"two vertices cannot have three common neighbours" corollary.

## 3. Minimal-counterexample machinery

Throughout this section fix:

```text
m : Nat, m >= 5
c = m / (4m - 1)
```

and suppose `G` is a smallest counterexample to:

```text
alpha(G) >= c * n.
```

Use this formal counterexample package:

```text
MC.G          : finite minimum-distance graph
MC.n          : vertex count
MC.bad        : alpha(MC.G) < c * MC.n
MC.minimal    : every smaller relevant minimum-distance graph satisfies
                alpha >= c * vertex_count
```

If a smaller graph has no edges and therefore is not represented as a
minimum-distance graph by the chosen API, use the independent set containing
all its vertices.

### E5. Claim: Lemma 1, small independent sets have many neighbours

Statement:

If `S` is independent in `G`, `|S| = k`, and `k <= m`, then the set of vertices
outside `S` adjacent to some vertex of `S` has cardinality at least `3k`.

Dependencies:

```text
MC.bad;
MC.minimal;
finite graph induced subgraph;
independent set union.
```

Proof:

1. Assume the outside-neighbour set `N(S)` has size `< 3k`.
2. Delete `S union N(S)` from `G`; call the remaining induced graph `G'`.
3. Vertex count:

   ```text
   |V(G')| >= n - (4k - 1).
   ```

4. By minimality, or by the edge-free branch, choose an independent set `S'`
   in `G'` with:

   ```text
   |S'| >= c * |V(G')|.
   ```

5. `S union S'` is independent in `G`, because all neighbours of `S` outside
   `S` were deleted before forming `G'`.
6. Cardinal arithmetic:

   ```text
   |S union S'|
     >= c * (n - 4k + 1) + k
      = c*n + (m-k)/(4m-1)
     >= c*n.
   ```

7. This contradicts `MC.bad`.

Lean transcription notes:

Clear denominators.  Prove a natural-number version of the cardinal estimate:

```text
(4*m - 1) * |S union S'| >= m * n.
```

### E6. Claim: Lemma 2, minimum degree at least three

Statement:

Every vertex of `G` has degree at least `3`.

Dependencies:

```text
E5 with k = 1.
```

Proof:

1. Let `S = {v}`.
2. `S` is independent.
3. E5 says `S` has at least `3` outside neighbours.
4. These outside neighbours are exactly the neighbours of `v`.

Lean transcription notes:

This is a one-line consequence after E5 is stated over singleton finsets.

### E7. Claim: Lemma 3, two-connectedness

Statement:

`G` is connected and has no cut vertex.

Dependencies:

```text
MC.minimal;
MC.bad;
finite graph connected components;
finite graph cut vertices;
independence number of induced subgraphs.
```

Proof:

1. Connectedness.
   1. If `G` is disconnected, decompose it into connected components.
   2. Apply minimality to each component or use the edge-free branch.
   3. Union the component independent sets.
   4. The union has size at least `c*n`, contradicting `MC.bad`.
2. No cut vertex.
   1. Suppose `x` is a cut vertex.
   2. Let `G1,G2` be two separated parts of `G - x`.
   3. Let `G1' = G - G2` and `G2' = G - G1`.
   4. If `alpha(G1') = alpha(G1)`, choose a maximum independent set of
      `G1'` avoiding `x`, and combine it with a minimality independent set in
      `G2`.
   5. If `alpha(G1') != alpha(G1)`, then every maximum independent set of
      `G1'` uses `x`; remove `x` and combine with a minimality independent set
      in `G2'`.
   6. In both cases obtain an independent set in `G` of size at least `c*n`,
      contradicting `MC.bad`.

Lean transcription notes:

This requires a graph API for cut vertices and induced subgraphs.  Do not tie
this lemma to geometry except through the fact that smaller pieces remain
within the class handled by `MC.minimal`, or are edge-free.

## 4. Boundary cycle, turns, and local counting

### E8. Claim: Boundary polygon exists

Statement:

From E2 and E7, `G` has a simple outer boundary cycle

```text
p_1, p_2, ..., p_t
```

in counterclockwise order.

Dependencies:

```text
E2 planarity;
E7 two-connectedness;
plane embedding/outer face theorem.
```

Proof obligations:

1. In a two-connected plane graph, every face boundary is a simple cycle.
2. Choose the outer face and orient its boundary counterclockwise.

Lean transcription notes:

This is one of the largest infrastructure obligations.  Abstract planarity is
not enough; later claims need cyclic order and inside/outside of subpolygons.

### E9. Claim: Boundary edge classification and unique `q_i`

Statement:

For each boundary edge `p_i p_{i+1}`:

```text
triangle edge: p_i and p_{i+1} have a common neighbour q_i;
nontriangle edge: otherwise.
```

If the edge is a triangle edge, the common neighbour `q_i` is unique.

Dependencies:

```text
E4 four-cycle convexity;
E4 K_{2,3} exclusion.
```

Proof:

1. Suppose `p_i` and `p_{i+1}` have two distinct common neighbours `q,q'`.
2. If one common neighbour lies inside the equilateral triangle formed by the
   other, the resulting four-cycle is nonconvex, contradicting E4.1.
3. Otherwise the two endpoints and the two common neighbours form the forbidden
   local `K_{2,3}` pattern, contradicting E4.2.
4. Hence the common neighbour is unique.

Lean transcription notes:

Represent this as a uniqueness lemma returning `existsUnique q`.

### E10. Claim: Boundary counts and turn definitions

Statement:

Define:

```text
b   = number of nontriangle boundary edges;
d_i = number of boundary vertices of degree i in G, for i = 3,4,5,6;
N   = b + d_5 + d_6;
theta_i = interior angle at p_i;
tau_i   = theta_i - pi.
```

Negative elements are:

```text
nontriangle boundary edges;
degree-5 boundary vertices;
degree-6 boundary vertices.
```

Dependencies:

```text
E2 degree bound <= 6;
E6 minimum degree >= 3;
E8 boundary cycle.
```

Proof obligations:

1. Every boundary vertex degree is one of `3,4,5,6`.
2. The boundary vertices are partitioned by these degree classes.
3. The set of negative elements has cardinality `N`.

Lean transcription notes:

Use finite sets for boundary vertices and boundary edges.  Keep edge-negative
and vertex-negative elements in a disjoint sum type to avoid double counting.

### E11. Claim: Arcs and concavity

Statement:

An arc of size `k` is a maximal sequence of degree-4 boundary vertices

```text
p_{i+1}, ..., p_{i+k}
```

with triangle edges between consecutive vertices and one of Swanepoel's four
endpoint patterns:

```text
Left endpoint:
  L1. deg(p_i)=3, deg(p_{i-1})=4, and p_i p_{i-1}, p_i p_{i+1}
      are triangle edges.
  L2. deg(p_i)=deg(p_{i-1})=3, and p_i p_{i+1} is a triangle edge.

Right endpoint:
  R1. deg(p_{i+k+1})=3, deg(p_{i+k+2})=4, and
      p_{i+k}p_{i+k+1}, p_{i+k+1}p_{i+k+2} are triangle edges.
  R2. deg(p_{i+k+1})=deg(p_{i+k+2})=3, and
      p_{i+k}p_{i+k+1} is a triangle edge.
```

Define:

```text
A = number of arcs with k >= 2m - 3;
B = number of arcs with k >= 2m - 3 and sum tau over the arc >= pi/3.
```

Dependencies:

```text
E8 boundary cycle;
E9 triangle-edge classification;
E10 degree classes.
```

Proof obligations:

1. Maximality makes arcs disjoint as ranges of boundary vertices.
2. Every degree-4 run between suitable degree-3 endpoints is either an arc or
   is interrupted by a negative element.
3. If `p_j` is a degree-4 vertex in an arc, then `tau_j >= 0` by E3.4/E3.5.

Lean transcription notes:

Define arcs as data containing start index, size, endpoint-pattern witness,
maximality proof, and triangle-edge witnesses.

### E12. Claim: Boundary angle-count inequality

Statement:

```text
d_3 >= d_5 + 2*d_6 + b + B + 6.
```

Therefore:

```text
d_3 >= N + B + 6.
```

Dependencies:

```text
E3 polygon angle sum;
E3 face-angle lower bounds;
E10 boundary counts;
E11 concave arcs.
```

Proof:

1. Boundary angle sum:

   ```text
   sum_i theta_i = pi * (sum_{j=3}^6 d_j - 2).
   ```

2. Degree contribution:

   ```text
   each degree-j boundary vertex contributes at least pi*(j-1)/3.
   ```

3. Each nontriangle edge contributes an additional `pi/3` beyond the degree
   contribution.
4. Each concave long arc contributes an additional `pi/3` by definition.
5. Combine:

   ```text
   pi*(sum d_j - 2)
     >= sum_{j=3}^6 pi*(j-1)/3*d_j + pi/3*(b+B).
   ```

6. Multiply by `3/pi` and rearrange to get the stated inequality.

Lean transcription notes:

Do the final inequality over integers after proving all angle inequalities in
`Real`.  The positivity of `pi` is required when multiplying.

### E13. Claim: Lemma 4, subpolygon low-degree inequality

Statement:

Let `Q` be any simple closed polygon in `G`.  Let `G_Q` be the subgraph induced
by vertices on or inside `Q`.  If `D_i` is the number of boundary vertices of
`Q` with degree `i` in `G_Q`, then:

```text
2 * D_2 + D_3 >= 6.
```

Dependencies:

```text
E3 polygon angle sum;
E3 angle lower bounds;
E2 degree bound <= 6;
same counting argument as E12.
```

Proof:

1. Apply the E12 angle-counting method to `Q`.
2. The degree range on the boundary of `G_Q` starts at `2`, not `3`, because
   a subpolygon boundary vertex may lose outside neighbours.
3. Rearranging the resulting inequality gives:

   ```text
   2*D_2 + D_3 >= 6.
   ```

Lean transcription notes:

This is the central local contradiction lemma.  Later proofs should cite it
by constructing a polygon `Q` and proving that its induced boundary has too
few degree-2 and degree-3 vertices.

## 5. Long nonconcave arc

### E14. Claim: Lemma 6, forced negative element after a gap

Statement:

Let `p_{i(j)}` and `p_{i(j+1)}` be consecutive degree-3 boundary vertices.
Assume:

```text
no arc of size >= 2m - 3 lies between them;
no negative element lies between them except possibly p_{i(j)+1}
or the edge p_{i(j)}p_{i(j)+1}.
```

Then:

```text
p_{i(j+1)+1} is negative
or
p_{i(j+1)}p_{i(j+1)+1} is a nontriangle edge.
```

Dependencies:

```text
E5 small independent sets;
E11 arcs;
E13 subpolygon low-degree inequality.
```

Proof:

1. Assume the conclusion fails:

   ```text
   deg(p_{i(j+1)+1}) <= 4
   and p_{i(j+1)}p_{i(j+1)+1} is a triangle edge.
   ```

2. Since no long arc lies in the gap:

   ```text
   i(j+1) - i(j) - 2 < 2m - 3.
   ```

3. Define the every-other set:

   ```text
   S = { p_{i(j)+2h} | h = 0,...,ceil((i(j+1)-i(j))/2) }.
   ```

4. Its size `k` satisfies `k <= m`.
5. Count neighbours of `S`; using the endpoint hypothesis, this count is at
   most `3k - 1`.
6. Prove `S` is independent:
   1. If two selected vertices coincide, construct the boundary subpolygon
      between their occurrences and violate E13.
   2. If two selected vertices are adjacent, use the chord plus the boundary
      subpath to form a polygon whose induced boundary violates E13.
7. E5 says `S` has at least `3k` neighbours, contradicting Step 5.

Lean transcription notes:

The main work is the finite index arithmetic for `S` and the two E13
applications for equality/adjacency exclusions.

### E15. Claim: Lemma 7, induction over degree-3 vertices

Statement:

Let `N_j` and `A_j` count negative elements and long arcs between
`p_{i(1)}` and `p_{i(j+1)}`.  For each `j`:

```text
N_j + A_j >= j - 1.
```

If equality holds, then:

```text
p_{i(j+1)+1} is negative
or
p_{i(j+1)}p_{i(j+1)+1} is a nontriangle edge.
```

Dependencies:

```text
E14.
```

Proof:

1. Base case `j=1`:
   1. Use the initially chosen gap with no negative element and no long arc.
   2. Apply E14 if `A_1=0`.
2. Induction step from `j-1` to `j`:
   1. If `N_{j-1}+A_{j-1} > j-2`, monotonicity gives the inequality.
   2. If equality holds at `j-1`, E14 supplies a negative element immediately
      after `p_{i(j)}`, hence `N_j+A_j >= j-1`.
   3. If equality also holds at `j`, apply E14 to the gap from `p_{i(j)}` to
      `p_{i(j+1)}` to get the equality-case conclusion.

Lean transcription notes:

Represent "between" counts with cyclic intervals and prove monotonicity of
counts under interval extension.

### E16. Claim: Lemma 5, nonconcave long arc exists

Statement:

There exists an arc of size at least `2m - 3` whose turn sum is less than
`pi/3`.

Dependencies:

```text
E12 boundary angle-count inequality;
E14;
E15.
```

Proof:

1. Let `A` be the number of long arcs and `B` the number of concave long arcs.
2. E12 gives:

   ```text
   d_3 >= N + B + 6.
   ```

3. It suffices to prove:

   ```text
   N + A >= d_3.
   ```

4. If every gap between consecutive degree-3 boundary vertices contains a
   negative element or a long arc, Step 3 follows by charging each degree-3
   vertex to such an element.
5. Otherwise choose a gap with neither and label it the first gap.
6. Apply E15 with `j=d_3`:

   ```text
   N + A >= d_3 - 1.
   ```

7. Equality cannot hold, because the equality-case negative element after
   `p_{i(d_3+1)} = p_{i(1)}` would lie in the initially chosen empty gap.
8. Hence `N + A >= d_3`.
9. From Steps 2 and 8, `A > B`; therefore some long arc is not concave.

Lean transcription notes:

The charging argument in Step 4 and the cyclic equality case in Step 7 are
the two nontrivial combinatorial bookkeeping points.

## 6. Broken-lattice obstruction

### E17. Claim: Broken-lattice setup

Statement:

Choose a nonconcave arc from E16 and shorten it, if necessary, to exactly
`2m - 3` degree-4 vertices:

```text
p_1, ..., p_{2m-3}.
```

It has:

```text
deg(p_0) = 3;
p_0p_1, p_1p_2, ..., p_{2m-4}p_{2m-3} are triangle edges;
tau_1 + ... + tau_{2m-3} < pi/3.
```

For `i = 0,...,2m-4`, let `q_i` be the unique common neighbour of
`p_i,p_{i+1}`.

Dependencies:

```text
E9 unique q_i;
E11 arc definition;
E16 nonconcave long arc.
```

Proof obligations:

1. A nonconcave arc of size greater than `2m-3` contains an initial subarc of
   exactly `2m-3` with turn sum still less than `pi/3`, because each turn in
   the arc is nonnegative.
2. The endpoint pattern may be chosen so that `deg(p_0)=3` and the listed
   edges are triangle edges, as in Swanepoel's construction.

Lean transcription notes:

Store the broken lattice as a structure with fields for `p`, `q`, degree
witnesses, triangle-edge witnesses, and turn-sum witness.

### E18. Claim: Lemma 8, each `q_i` has two extra neighbours

Statement:

For every `i = 1,...,2m-5`, the vertex `q_i` has exactly two neighbours other
than:

```text
p_i, p_{i+1}, and possibly q_{i-1}, q_{i+1}.
```

Call them `r_i,s_i` in positive cyclic order around `q_i`:

```text
s_i, r_i, q_{i-1}, p_i, p_{i+1}, q_{i+1}.
```

Dependencies:

```text
E3 angle facts;
E5 small independent sets;
E13 subpolygon low-degree inequality;
E17 broken-lattice setup.
```

Proof:

1. At most two extra neighbours.
   1. Suppose `q_i` has three extra neighbours `r1,r2,r3`.
   2. Around `q_i`, use E3.2 to get three angle lower bounds of `pi/3`.
   3. Use E3.3 on adjacent quadrilateral configurations to get:

      ```text
      tau_i + tau_{i+1} >= pi/3.
      ```

   4. This contradicts the broken-lattice turn sum.
2. At least two extra neighbours.
   1. Suppose `q_i` has at most one extra neighbour.
   2. Define:

      ```text
      S = {q_i, p_{i+2}} union {p_{i-2h-1} | h=0,...,floor(i/2)}.
      ```

   3. `|S| = floor(i/2)+3 <= m`.
   4. Count neighbours; by the assumption, `S` has at most `3|S|-1`
      neighbours.
   5. Prove `S` is independent:
      1. Distinctness and independence among the boundary `p` vertices are as
         in E14.
      2. If `q_i` equals or is adjacent to one of those vertices, form the
         polygon specified in Swanepoel Lemma 8 and violate E13.
      3. Use uniqueness of common neighbours from E9 for the cases involving
         `p_{i+1}` and `p_{i+2}`.
   6. E5 contradicts the neighbour count.
3. Hence exactly two extra neighbours exist.
4. Name them `r_i,s_i` according to the positive cyclic order.

Lean transcription notes:

The cyclic-order conclusion needs an embedding rotation system around `q_i`.

### E19. Claim: Lemma 9, three consecutive equalities are late

Statement:

If:

```text
s_i = r_{i+1} for i = a,a+1,a+2
```

with `1 <= a <= 2m-8`, then:

```text
a >= 2m - 10.
```

Dependencies:

```text
E3 angle facts;
E4 local exclusions;
E5 small independent sets;
E13 subpolygon low-degree inequality;
E18 extra-neighbour structure.
```

Proof:

1. Angle bound at `s_{a+1}`.
   1. If `s_{a+1}` had more than two neighbours other than
      `s_a,s_{a+2},q_{a+1},q_{a+2}`, then the angle estimate used in E18 would
      give:

      ```text
      tau_{a+1}+tau_{a+2}+tau_{a+3} >= pi/3.
      ```

   2. This contradicts nonconcavity.
   3. Hence `s_{a+1}` has at most two such extra neighbours.
2. Define:

   ```text
   S = {p_{a+5}, q_{a+3}, p_{a+2}, s_{a+1}, q_a}
       union {p_{a-2h-1} | h=0,...,floor(a/2)}.
   ```

3. Then:

   ```text
   |S| = floor(a/2) + 6.
   ```

4. Neighbour count:

   ```text
   S has at most 3|S| - 1 neighbours.
   ```

5. Distinctness and independence:
   1. Boundary `p` vertices are handled by the E14 boundary-selected-vertices
      sublemma: a coincidence or chord between two selected boundary vertices
      forms a subpolygon whose induced boundary violates E13.
   2. If `q_a = q_{a+3}`, use the polygon
      `q_a p_{a+1} p_{a+2} p_{a+3}` and contradict E13.
   3. If `q_a` is adjacent to `q_{a+3}`, use the polygon
      `q_a p_{a+1} p_{a+2} p_{a+3} q_{a+3}` and split the possible neighbours
      of `q_a`:
      1. `q_{a+3}=q_{a-1}` gives only `p_{a+1},p_{a+3}` of degree `3` and
         only `q_{a+3}` of degree `2` on the induced boundary, violating E13.
      2. `q_{a+3}=r_a` gives only `p_{a+1},p_{a+3},q_a` of degree `3` and
         only `q_{a+3}` of degree `2`, violating E13.
      3. `q_{a+3}=q_{a+1}` contradicts unique common neighbour for
         `p_{a+2},p_{a+3}` from E9.
      4. `q_{a+3}=p_a` or `q_{a+3}=p_{a+1}` gives a boundary subpolygon with
         `2*D_2 + D_3 < 6`, violating E13.
   4. `s_{a+1}` is not adjacent to `q_a` or `q_{a+3}` by E4.2, because the
      relevant vertex pairs already have two common neighbours.
   5. If `s_{a+1}` equals or is adjacent to `p_{a+5}`, use the polygon
      `s_{a+1} q_{a+1} p_{a+2} p_{a+3} p_{a+4} p_{a+5}` and contradict E13.
   6. If `s_{a+1}` is adjacent to `p_{a+2}`, then uniqueness of common
      neighbours forces `s_{a+1}=p_{a+1}` or `s_{a+1}=p_{a+3}`, contrary to
      the definitions of `s_{a+1}` and `r_{a+2}`.
   7. If `s_{a+1}` equals or is adjacent to an earlier `p_{a-2h-1}`, use the
      polygon `s_{a+1} q_{a+1} p_{a+1} p_a p_{a-1} ... p_{a-2h-1}` and
      contradict E13.
6. Thus `S` is independent.
7. E5 forces `|S| > m`; otherwise `S` would have at least `3|S|` neighbours.
8. `floor(a/2)+6 > m` implies `a >= 2m - 10`.

Lean transcription notes:

This is a finite local-case proof.  Each subcase should become a separate
lemma returning either an E13 contradiction or an E4 contradiction.

### E20. Claim: Theorem 4, broken-lattice obstruction

Statement:

If `G` is a smallest counterexample to

```text
alpha(G) >= (m/(4m-1))*n
```

with `m >= 5`, then `G` contains broken-lattice data satisfying:

```text
BL1. p_0,...,p_{2m-3} lie consecutively on the boundary.
BL2. tau_1 + ... + tau_{2m-3} < pi/3.
BL3. deg(p_0)=3 and deg(p_i)=4 for i=1,...,2m-3.
BL4. q_i is the unique common neighbour of p_i,p_{i+1}
     for i=0,...,2m-4.
BL5. r_i,s_i exist for i=1,...,2m-5 as in E18.
BL6. If s_i = r_{i+1} for i=a,a+1,a+2, then a >= 2m-10.
```

Dependencies:

```text
E5-E19.
```

Proof:

1. Use E16 to choose a nonconcave long arc.
2. Use E17 to package the arc as broken-lattice data.
3. Use E18 to add `r_i,s_i`.
4. Use E19 to obtain BL6.

Lean transcription notes:

This should be a structure-valued theorem:

```text
exists BL : BrokenLattice G m, BL.turn_lt and BL.late_triples
```

## 7. Euclidean Lemma 10 and final contradiction

### E21. Claim: Lemma 10 reduction

Statement:

In the Euclidean broken-lattice data from E20:

```text
s_i = r_{i+1}
```

for all `i = 1,...,2m-6`, except possibly one index.

Dependencies:

```text
E3 Euclidean angle facts;
E17-E18 broken-lattice data.
```

Proof plan:

1. Prove implication F:

   ```text
   if s_i != r_{i+1}, then
   tau_i + 2*tau_{i+1} + tau_{i+2} >= pi/3.        (5)
   ```

2. Prove implication G:

   ```text
   if s_i != r_{i+1}, then
   tau_i + tau_{i+1} >= angle(q_{i+1}, p_{i+1}, r_{i+1}).  (6)
   ```

3. Suppose two failures occur at indices `i < j`.
4. If `i+2 <= j`, average the two inequalities (5).  Since all turns in the
   arc are nonnegative, the total turn is at least `pi/3`.
5. If `j=i+1`, combine (6) at `i` and the mirror of (6) at `i+1`.  Use:

   ```text
   triangle q_{i+1} r_{i+1} p_{i+1} is isosceles;
   triangle q_{i+1} p_{i+2} s_{i+1} is isosceles;
   triangle p_{i+1} p_{i+2} q_{i+1} is equilateral;
   angle sum of triangle q_{i+1}s_{i+1}r_{i+1};
   angle sum of quadrilateral p_{i+1}p_{i+2}s_{i+1}r_{i+1};
   angle(s_{i+1},q_{i+1},r_{i+1}) >= pi/3.
   ```

   This again forces total turn at least `pi/3`.
6. Both cases contradict BL2, so at most one failure exists.

Lean transcription notes:

E21 should depend on two analytic sublemmas E22 and E23 corresponding to (5)
and (6).

### E22. Claim: Lemma 10 inequality (5)

Statement:

If `s_i != r_{i+1}`, then:

```text
tau_i + 2*tau_{i+1} + tau_{i+2} >= pi/3.
```

Dependencies:

```text
E3 Euclidean angle facts;
E18 neighbour order around q_i;
Euclidean trigonometry for Figure 8.
```

Proof:

1. Define angles as in Swanepoel Figure 8:

   ```text
   alpha   = angle(q_{i+1}, p_{i+1}, q_i)
   alpha'  = angle(q_i, p_i, q_{i-1})
   alpha'' = angle(q_{i+2}, p_{i+2}, q_{i+1})
   beta, beta', gamma, delta, epsilon, epsilon'
   d1 = |s_i r_{i+1}|
   d2 = |q_i q_{i+1}|
   ```

2. Angle accounting gives:

   ```text
   tau_i + 2*tau_{i+1} + tau_{i+2}
     = alpha' + 2*alpha + alpha'' - 4*pi/3.
   ```

3. E3.3 on the two adjacent quadrilaterals gives:

   ```text
   alpha'  >= pi - beta'
   alpha'' >= pi - epsilon'.
   ```

4. E3.2 at `q_i` and `q_{i+1}` gives:

   ```text
   beta'    <= 4*pi/3 - beta
   epsilon' <= 4*pi/3 - epsilon.
   ```

5. The angle sum of pentagon
   `p_{i+1} q_{i+1} r_{i+1} s_i q_i` gives:

   ```text
   beta + epsilon = 3*pi - alpha - gamma - delta.
   ```

6. Combining Steps 2-5:

   ```text
   tau_i + 2*tau_{i+1} + tau_{i+2}
     >= alpha - gamma - delta + pi.
   ```

7. It remains to prove:

   ```text
   gamma + delta <= alpha + 2*pi/3.
   ```

8. Euclidean Figure 8 analytic obligation:
   1. Under constraints `q_i s_i = 1`, `s_i r_{i+1} >= 1`,
      `r_{i+1} q_{i+1} = 1`, and `q_i q_{i+1}=d2`,
      `gamma + delta` decreases as `d1=|s_i r_{i+1}|` increases.
   2. Under constraints `p_{i+1}q_i = p_{i+1}q_{i+1}=1`,
      `alpha` increases as `d2` increases.
   3. For fixed `gamma+delta`, `d2` is minimized when
      `triangle r_{i+1}s_iq_{i+1}` is equilateral, i.e. `delta=pi/3`.
   4. In that extremal case:

      ```text
      gamma + delta = alpha + 2*pi/3.
      ```

9. Steps 7-8 imply the desired inequality.

Lean transcription notes:

Do not formalize Step 8 synthetically unless a strong geometry library is
available.  Preferred Lean route: introduce coordinates for the Figure 8
configuration and prove Step 7 directly from trigonometric inequalities.

### E23. Claim: Lemma 10 inequality (6)

Statement:

If `s_i != r_{i+1}`, then:

```text
tau_i + tau_{i+1} >= angle(q_{i+1}, p_{i+1}, r_{i+1}).
```

Dependencies:

```text
E3 Euclidean angle facts;
law of cosines;
trigonometric monotonicity on [0,pi].
```

Proof:

1. Define Figure 9 angles:

   ```text
   alpha = angle(s_i, p_{i+1}, q_i)
   theta = angle(r_{i+1}, p_{i+1}, s_i)
   beta  = angle(q_{i+1}, p_{i+1}, r_{i+1})
   d1    = |p_{i+1} r_{i+1}|
   d2    = |s_i r_{i+1}|
   ```

2. Angle accounting gives:

   ```text
   tau_{i+1} = alpha + theta + beta - pi/3.
   ```

3. E3.3 and the isosceles/equilateral relations give:

   ```text
   tau_i >= pi/3 - 2*alpha.
   ```

4. General bounds:

   ```text
   0 <= alpha <= pi/3;
   1 <= d1 <= 2.
   ```

5. Cosine-rule estimate:

   ```text
   cos(theta)
     <= (d1^2 - 1 + 4*cos(alpha)^2) / (4*d1*cos(alpha)).
   ```

6. Case `alpha <= pi/6`.
   1. From Steps 2-3:

      ```text
      tau_i + tau_{i+1} >= beta + theta - alpha.
      ```

   2. It is enough to show `theta >= alpha`.
   3. Since cosine is decreasing on `[0,pi]`, it is enough to show
      `cos(theta) <= cos(alpha)`.
   4. By Step 5, this reduces to:

      ```text
      d1^2 - 1 <= 4*(d1 - 1)*cos(alpha)^2.
      ```

   5. Since `d1 >= 1`, it is enough to show:

      ```text
      d1 + 1 <= 4*cos(alpha)^2.
      ```

   6. This follows from `d1 <= 2` and `alpha <= pi/6`.
7. Case `alpha >= pi/6`.
   1. Use `tau_i >= 0` and Step 2:

      ```text
      tau_i + tau_{i+1} >= alpha + theta + beta - pi/3.
      ```

   2. It is enough to show:

      ```text
      alpha + theta >= pi/3.
      ```

   3. By monotonicity of cosine and Step 5, reduce to:

      ```text
      d1^2 - 1 + (2-d1)*(1 + cos(2*alpha))
        <= sqrt(3)*d1*sin(2*alpha).
      ```

   4. Use:

      ```text
      cos(2*alpha) <= 1/2;
      sqrt(3)/2 <= sin(2*alpha);
      1 <= d1 <= 2.
      ```

   5. The remaining inequality is algebraic.

Lean transcription notes:

This lemma is a good candidate for a standalone analytic file later.  The
configuration-specific geometric hypotheses should be converted into the
numeric bounds in Steps 4-5 before invoking trigonometry.

### E24. Claim: Final `m=8` contradiction

Statement:

The Euclidean theorem E follows from E20 and E21 with `m=8`.

Dependencies:

```text
E20 broken-lattice obstruction;
E21 Lemma 10;
integer arithmetic.
```

Proof:

1. Suppose a Euclidean counterexample to `alpha(G) >= 8n/31` exists.
2. Set:

   ```text
   m = 8;
   m/(4m-1) = 8/31;
   2m - 10 = 6;
   2m - 6 = 10.
   ```

3. Apply E20 to get broken-lattice data.
4. E21 says that among indices `1,...,10`, at most one fails
   `s_i = r_{i+1}`.
5. Therefore some triple of consecutive equalities starts at `a <= 4`:
   1. if the unique failure is in `{1,2,3}`, use a triple starting at
      `failure+1`;
   2. otherwise use the triple starting at `1`.
6. E20.BL6 says every triple starts at `a >= 6`.
7. Contradiction.
8. Hence no counterexample exists.
9. Translate graph independence back to `UDConfig.IsIndep` using E1.

Lean transcription notes:

The pigeonhole step can be a finite lemma over `Fin 10` or a direct case split
on the optional failure index.

## 8. General nonparalleloid theorem N

This theorem is separate from the Euclidean `8/31` theorem.  It uses the same
broken-lattice obstruction pattern, but its final contradiction comes from
proper Brass measure and compactness, not from Euclidean Lemma 10.

### N. Theorem: nonparalleloid contact-graph improvement

Assumptions:

N.A1. `C` is a convex disc.

N.A2. `C` is not a paralleloid.

Conclusion:

```text
exists c > 1/4, forall n and every packing of n translates of C,
alpha(contactGraph packing) >= c*n.
```

Proof dependencies:

```text
N0: normed-plane version of Swanepoel Theorem 4.
N1-N2: contact graph and normed-plane reduction.
N3: proper Brass measure.
N4-N7: Lemmas 11-14.
N8: Lemma 15.
N9: final contradiction with N0.
```

### N0. Claim: General broken-lattice obstruction

Statement:

Let `M(C)` be a nonrectilinear normed plane with a Brass measure.  Let
`m >= 5`.  If `G` is a smallest counterexample to:

```text
alpha(G) >= (m/(4m-1))*n,
```

then `G` contains broken-lattice data satisfying:

```text
N0.1. p_0,...,p_{2m-3} lie consecutively on the boundary.
N0.2. tau_1 + ... + tau_{2m-3} < pi/3.
N0.3. deg(p_0)=3 and deg(p_i)=4 for i=1,...,2m-3.
N0.4. q_i is the unique common neighbour of p_i,p_{i+1}
      for i=0,...,2m-4.
N0.5. r_i,s_i exist in the Lemma 8 range.
N0.6. If s_i = r_{i+1} for i=a,a+1,a+2, then a >= 2m-10.
```

Dependencies:

```text
Swanepoel Section 3:
normed-plane planarity and degree <= 6;
Brass-measure angle facts;
minimal-counterexample Lemmas 1-3;
boundary angle count;
subpolygon low-degree Lemma 4;
Lemmas 5-9.
```

Proof obligations:

1. Repeat E5-E7 with normed-plane minimum-distance graphs.
2. Repeat E8-E13 using Brass-measure angle facts instead of Euclidean angles.
3. Repeat E14-E16 to obtain a nonconcave arc.
4. Repeat E17-E19 to construct `q_i,r_i,s_i` and prove late triples.

Lean transcription notes:

This is the shared theorem used by the nonparalleloid path.  It may later be
formalized once in a normed-plane file.  The Euclidean theorem E can instead
use the Euclidean-specialized E20.

### N1. Claim: Difference-body contact-graph reduction

Statement:

The contact graph of a packing of translates of `C` is a minimum-distance
graph of the centers in the norm determined by a centrally symmetric copy of
`C-C`, up to global scaling.

Dependencies:

```text
convex disc translate definitions;
difference body boundary/interior/exterior characterization.
```

Proof:

1. For translates `C+x1`, `C+x2`, intersection behaviour depends on
   `x1-x2`.
2. Touching means `x1-x2` is on `bd(C-C)`.
3. Overlap means `x1-x2` is in `int(C-C)`.
4. Disjointness means `x1-x2` is outside `C-C`.
5. Therefore contact edges are exactly minimum-distance edges in the chosen
   norm scale.

Lean transcription notes:

Choose one scale and state all later norm distances consistently.

### N2. Claim: Paralleloid passes to the difference body

Statement:

`C` is a paralleloid iff `C-C` is a paralleloid.  Hence the nonparalleloid
hypothesis survives the reduction N1.

Dependencies:

```text
convex geometry of supporting lines and chords;
Swanepoel Section 2 observation.
```

Proof obligations:

1. Translate supporting chords of `C` into boundary segments of `C-C`.
2. Translate the strict length-sum condition in both directions.

Lean transcription notes:

This is not needed for the Euclidean theorem.  It is required only for N.

### N3. Claim: Proper Brass measure

Statement:

If the unit ball is not a paralleloid, the normed plane admits a proper Brass
measure.

Dependencies:

```text
Swanepoel Proposition 3 / Brass theorem.
```

Proof obligations:

1. Import or formalize Brass's theorem.
2. Expose the equality case: with a proper Brass measure, equality
   `angle = pi/3` in the isosceles lemma forces equilateral/collinear
   degeneracies used in N4.

Lean transcription notes:

This is a major external-theorem dependency for the nonparalleloid theorem.

### N4. Claim: Lemma 11, near-extreme angles force near-parallel directions

Statement:

For every `epsilon > 0`, there exists `delta > 0` such that in the Figure 10
local graph, if:

```text
angle(r,q,p)  > 2*pi/3 - delta;
angle(p+,q,s) > 2*pi/3 - delta;
```

then:

```text
|| (r-p)/||r-p|| - (s-p+)/||s-p+|| || < epsilon.
```

Dependencies:

```text
N3 proper Brass measure;
compactness of bounded configurations;
E3-style angle lower bounds in Brass measure.
```

Proof:

1. Assume false for some `epsilon`.
2. Choose a sequence with `delta=1/n` violating the conclusion.
3. Use bounded diameter of the Figure 10 configuration to extract a convergent
   subsequence.
4. In the limit, both relevant angles are at least `2*pi/3`.
5. The remaining angle lower bounds force equality throughout.
6. Properness from N3 forces the collinear/equilateral equality cases.
7. Conclude the two normalized directions are equal, contradicting the
   assumed separation by `epsilon`.

Lean transcription notes:

Requires topology on finite tuples of points and continuity of angle/direction
away from zero vectors.

### N5. Claim: Lemma 12, nonparalleloid boundary comparison

Statement:

In a nonparalleloid normed plane, let `u,v` be unit vectors with `uv=1`.

```text
1. If x is a unit vector strictly between u and v, then ux < 1.
2. If x is a unit vector strictly between v and v-u, then ux > 1.
```

Dependencies:

```text
Proposition 1: no long boundary segment iff not paralleloid;
convexity of the unit ball.
```

Proof obligations:

1. For (1), show `ux >= 1` would force a boundary segment between `u` and `v`
   of forbidden length.
2. For (2), show `ux <= 1` would similarly force a forbidden boundary segment
   in the adjacent sector.

Lean transcription notes:

The paper omits this proof.  Lean must supply it.

### N6. Claim: Lemma 13, six-sector localization

Statement:

Let `u,v` be unit vectors with `uv=1`.  Define six lattice directions
`x_0,...,x_5` from the equilateral triangle and set `y_i=x_{i-1}+x_i`.

Then:

```text
1. If ox >= 1, then x is not in int(conv{x_0,...,x_5}).
2. Every unit vector lies in one of the six triangles
   conv{x_{i-1}, x_i, y_i}.
3. If the unit ball is not a paralleloid, the cover sharpens to the boundary
   edges plus interiors of these six triangles.
```

Dependencies:

```text
convexity of the unit ball;
N5 for the nonparalleloid sharpening.
```

Proof obligations:

1. Establish the central hexagon exclusion from convexity and minimum norm.
2. Establish the unit-circle cover by cyclic order around the boundary.
3. Use N5 to rule out ambiguous sector interiors in the nonparalleloid case.

Lean transcription notes:

This is a convex-geometry localization lemma, independent of the Euclidean
`8/31` proof.

### N7. Claim: Lemma 14, failed equality gives uniform direction jump

Statement:

For a nonparalleloid unit ball, there exists `epsilon > 0` depending only on
the norm such that every Figure 12 local configuration satisfies:

```text
r+ and the line pr are on opposite sides of the comparison line p+r';
|| normalize(r-p) - normalize(r+-p+) || >= epsilon.
```

Dependencies:

```text
N5;
N6;
compactness of local configurations.
```

Proof:

1. Place `q` at the origin and use the triangular lattice generated by
   `p,p+`.
2. Use N6 to localize `q+`, `r`, `s`, and `r+`.
3. Split into the two cases for the sector containing `r`.
4. In each case, use N5 and N6 to eliminate all positions inconsistent with
   the side condition.
5. If no uniform `epsilon` existed, take a convergent sequence with direction
   separation tending to zero.
6. The limit has parallel comparison directions, contradicting the side
   condition already proved.

Lean transcription notes:

This is the largest nonparalleloid local case analysis.

### N8. Claim: Lemma 15, early triple for large `m`

Statement:

For sufficiently large `m`, depending only on the nonparalleloid norm, the
broken-lattice data contains:

```text
s_i = r_{i+1} for i=a,a+1,a+2
```

for some:

```text
1 <= a <= 2m - 11.
```

Dependencies:

```text
N4;
N7;
N0 broken-lattice turn bound.
```

Proof:

1. Choose `epsilon` from N7.
2. Choose `delta` from N4 applied to `epsilon/3`.
3. Choose:

   ```text
   m > 4 + 2/delta + 41/(delta*epsilon).
   ```

4. Since total turn is `< pi/3`, at most `pi/(3*delta)` indices have either
   local angle at most `2*pi/3 - delta`.
5. On a long remaining stretch, N4 gives:

   ```text
   ||u_{i+1}-u_i|| < epsilon/3
   ```

   whenever `s_i = r_{i+1}`.
6. N7 gives:

   ```text
   ||u_{i+1}-u_i|| >= epsilon
   ```

   whenever `s_i != r_{i+1}`.
7. If every triple in the range had a failure, then the subsequence `u_{3i}`
   would accumulate boundary length greater than `4` on one arc.
8. Therefore the full unit-ball boundary length would exceed `8`, impossible
   in a normed plane.
9. Hence some early triple of equalities exists.

Lean transcription notes:

Requires formal boundary length of a normed unit circle and the theorem that
its circumference is at most `8`.

### N9. Claim: Conclusion of nonparalleloid theorem

Statement:

Theorem N follows from Theorem 4 and N8.

Dependencies:

```text
N1-N8;
N0 general broken-lattice obstruction;
integer inequality m/(4m-1) > 1/4.
```

Proof:

1. Reduce contact graphs to minimum-distance graphs using N1-N2.
2. Choose `m` large enough for N8.
3. Suppose a smallest counterexample to

   ```text
   alpha(G) >= (m/(4m-1))*n
   ```

   exists.
4. N0 says every triple of equalities starts at:

   ```text
   a >= 2m - 10.
   ```

5. N8 gives a triple starting at:

   ```text
   a <= 2m - 11.
   ```

6. Contradiction.
7. Set `c = m/(4m-1)`.  Since `m>=1`, `c > 1/4`.

Lean transcription notes:

This proof should live in a separate nonparalleloid file or section.  It is
not a prerequisite for theorem E.

## 9. Exact blockers for Lean proof of theorem E

B1. Boundary-face infrastructure.

Need:

```text
finite straight-line planar embedding;
outer face as a simple cycle;
cyclic indexing of boundary vertices;
inside/on/outside relation for simple polygons;
induced subgraph on the inside of a polygon.
```

Blocks:

```text
E8, E13, E14, E18, E19.
```

B2. Euclidean angle API.

Need:

```text
oriented and interior angles;
polygon angle sums;
face angle lower bounds;
quadrilateral angle inequality E3.3;
law-of-cosines wrappers;
cosine monotonicity on [0,pi].
```

Blocks:

```text
E3, E12, E13, E18, E21, E22, E23.
```

B3. Local exclusion lemmas.

Need:

```text
convex four-cycle lemma;
K_{2,3} exclusion;
unique common neighbour for triangle boundary edges.
```

Blocks:

```text
E4, E9, E18, E19.
```

B4. Subpolygon low-degree lemma.

Need:

```text
formal E13 and a reusable tactic/lemma pattern:
construct polygon Q -> compute possible D_2,D_3 -> contradiction.
```

Blocks:

```text
E14, E18, E19.
```

B5. Euclidean Lemma 10 analytics.

Need:

```text
coordinate/trigonometric proof of E22;
cosine-rule proof of E23;
finite argument converting E22,E23 into "all but one failure".
```

Blocks:

```text
E21-E24.
```

B6. Minimal-counterexample arithmetic.

Need:

```text
finite graph independent-set deletion;
cleared-denominator arithmetic for m/(4m-1);
component/cut-vertex independence-number arguments.
```

Blocks:

```text
E5-E7.
```

## 10. Lean-ready content now present

R1. The Euclidean theorem target is precise and separated from the
nonparalleloid theorem target.

R2. The Euclidean proof is decomposed into future Lean obligations E1-E24.

R3. Every use of Swanepoel Section 5 is isolated in N0-N9 and is marked as not
needed for theorem E.

R4. The exact final blocker for `8/31` is not the nonparalleloid compactness
argument.  It is the chain:

```text
boundary-face infrastructure -> subpolygon low-degree lemma -> Lemmas 6/8/9
-> Euclidean Lemma 10 inequalities -> m=8 contradiction.
```

R5. No Lean file was added.  Therefore there is no new Lean compilation
obligation from this audit.
