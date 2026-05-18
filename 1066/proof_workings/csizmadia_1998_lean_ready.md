# Csizmadia 1998 Lean-ready proof working

Source document: `../Proof_Files/Cs98.pdf`

Paper: G. Csizmadia, "On the Independence Number of Minimum Distance
Graphs", Discrete & Computational Geometry 20 (1998), 179-187.

This file is a Lamport-style transcription plan.  It is not a finished
Lean proof.  Every numbered assertion below is intended to become either:

- a Lean definition,
- a Lean lemma with a proof,
- an imported geometric theorem, or
- an explicitly named unformalized dependency.

## 0. Audit Corrections

0.1. The target bound is `9 / 35`.

The PDF text extraction drops fraction bars in several places.  The theorem
and Lemma 1 must be read as the lower bound `9n / 35`, equivalently
`35 * alpha(G) >= 9 * n` in integer arithmetic.

0.2. Lemma 1 uses at most nine selected vertices.

The extracted text sometimes renders `<=` as `<`.  Lemma 3 explicitly selects
nine vertices, so the Lean lemma must use `1 <= k` and `k <= 9`, not `k < 9`.

0.3. The local ratio should be represented without division.

For a selected independent set `P`, let `k = |P|` and let `m` be the number
of outside vertices adjacent to at least one vertex of `P`.  The local
condition is:

```text
35 * k >= 9 * (k + m).
```

The stronger sufficient condition used throughout the paper is:

```text
m <= 3 * k - 1    and    k <= 9.
```

Indeed:

```text
k + m <= 4 * k - 1
9 * (k + m) <= 36 * k - 9
36 * k - 9 <= 35 * k    iff    k <= 9.
```

0.4. The boundary-turn accounting needs a strict version.

The block-count conclusion in the paper is:

```text
positiveBlocks > negativeBlocks + 4.
```

This conclusion follows from strict total remaining turn:

```text
sum_C a(p) > 240 degrees.
```

The PDF line is OCR-fragile, but the preceding construction removes one
endpoint whose turn is strictly less than `120 degrees`; the Lean statement
should therefore expose the strict `> 240 degrees` hypothesis.  If a later
formalization only proves `>= 240 degrees`, the block-count lemma must be
weakened and rechecked.

0.5. The case split should not be transcribed from OCR literally.

The extraction renders several `<=` symbols as `<`.  The proof needs the
following discrete version:

```text
Case A: exists h, 3 <= h, h <= 15, h < m, d(p_h) = 3.
Case B: otherwise, 16 <= m and d(p_i) = 4 for 3 <= i <= 14.
```

These are the obligations that make Lemma 3 applicable.  A Lean proof should
not use the strict OCR string `3 < h < 15` without rechecking coverage of
the complementary case.

## 1. Global Formal Setting

Definition 1.1. A minimum-distance configuration is a finite set `X` of
points in `R^2` such that distinct points of `X` have Euclidean distance at
least `1`.

Lean obligation `Cs98.Config`.

- Carrier: finite type or finite set of points.
- Separation: `x != y -> 1 <= dist x y`.
- No quotienting by coordinates; the proof only needs finite graph vertices
  equipped with an embedding into `R^2`.

Definition 1.2. The minimum-distance graph `G(X)` has vertex set `X` and
an edge between distinct vertices exactly when their Euclidean distance is
`1`.

Lean obligation `Cs98.MinimumDistanceGraph`.

- `Adj x y := x != y and dist x y = 1`.
- Prove symmetry and looplessness.
- Prove every independent graph set is a point set with mutual distance
  strictly greater than `1`, using separation.

Definition 1.3. For a graph `G` and a finite independent set `P`, define the
outside neighborhood:

```text
N(P) = {v | v notin P and exists p in P, Adj v p}.
```

Let:

```text
k(P) = |P|
m(P) = |N(P)|.
R(P) = P union N(P).
```

Lean obligation `Cs98.neighborSet`.

- `P` and `N(P)` are disjoint by definition.
- `|R(P)| = k(P) + m(P)`.
- If `Q` is contained in the induced graph on `V \ R(P)`, then no vertex of
  `Q` is adjacent to any vertex of `P`.

## 2. The Main Theorem

Theorem 2.1. For every finite minimum-distance configuration `X` with
`n = |X|`, the graph `G(X)` has an independent set `I` such that:

```text
35 * |I| >= 9 * n.
```

Lean obligation `Cs98.main_9_35`.

- The theorem should be stated over a finite graph induced by a finite point
  configuration.
- The final selected set must be independent in the original graph, not only
  in the final induced subgraphs.

## 3. Local Deletion Lemma

Lemma 3.1. Every nonempty minimum-distance graph `G` has an independent set
`P` such that:

```text
1 <= |P|
|P| <= 9
|N(P)| <= 3 * |P| - 1.
```

Lean obligation `Cs98.local_deletion`.

- This is the only genuinely geometric theorem needed for the `9 / 35`
  lower bound.
- Sections 5 through 12 below decompose the paper's proof of this lemma.

Lemma 3.2. Lemma 3.1 implies the local ratio:

```text
35 * |P| >= 9 * |R(P)|.
```

Proof.

3.2.1. By Definition 1.3, `|R(P)| = |P| + |N(P)|`.

3.2.2. By Lemma 3.1, `|N(P)| <= 3 * |P| - 1`.

3.2.3. Therefore `|R(P)| <= 4 * |P| - 1`.

3.2.4. Since `|P| <= 9`, arithmetic gives:

```text
9 * |R(P)| <= 9 * (4 * |P| - 1) <= 35 * |P|.
```

Lean status: fully formalizable by `omega` or linear natural-number
arithmetic after avoiding division.

Theorem 3.3. Lemma 3.1 implies Theorem 2.1.

Proof.

3.3.1. Induct on the finite vertex set `V`.

3.3.2. If `V` is empty, choose `I = empty`.

3.3.3. If `V` is nonempty, apply Lemma 3.1 to the induced graph on `V` and
obtain `P`.

3.3.4. Let `R = P union N(P)`.

3.3.5. Apply the induction hypothesis to the induced graph on `V \ R`; obtain
an independent set `I'` with:

```text
35 * |I'| >= 9 * |V \ R|.
```

3.3.6. Prove `P union I'` is independent in `G`.

Proof obligation.

- `P` is independent by Lemma 3.1.
- `I'` is independent in the induced subgraph, hence in `G`.
- No edge joins `P` to `I'`, because every vertex adjacent to `P` lies in
  `N(P)`, and `I'` is disjoint from `R`.

3.3.7. Add the inequalities:

```text
35 * |P|  >= 9 * |R|
35 * |I'| >= 9 * |V \ R|
```

3.3.8. Use disjointness:

```text
|P union I'| = |P| + |I'|
|V| = |R| + |V \ R|.
```

3.3.9. Conclude:

```text
35 * |P union I'| >= 9 * |V|.
```

Lean status: fully formalizable after Lemma 3.1 is available.

## 4. Immediate Local Configurations

Lemma 4.1. If `G` has a vertex `v` with degree at most `2`, then Lemma 3.1
holds.

Proof.

4.1.1. Let `P = {v}`.

4.1.2. Then `P` is independent.

4.1.3. `|P| = 1`.

4.1.4. `N(P)` is the set of neighbors of `v`, so `|N(P)| <= 2`.

4.1.5. Hence:

```text
|N(P)| <= 2 = 3 * 1 - 1.
```

Lean status: fully formalizable from finite graph degree definitions.

Lemma 4.2. If nonadjacent degree-3 vertices `u` and `v` share a neighbor,
then Lemma 3.1 holds.

Proof.

4.2.1. Let `P = {u, v}`.

4.2.2. `P` is independent because `u` and `v` are nonadjacent.

4.2.3. `|P| = 2`.

4.2.4. The outside neighbors of `P` are contained in the union of the
neighbors of `u` and `v`.

4.2.5. The shared neighbor is counted once, and `u`, `v` are not counted
because `N(P)` is outside `P`.

4.2.6. Hence `|N(P)| <= 3 + 3 - 1 = 5`.

4.2.7. Since `5 = 3 * 2 - 1`, Lemma 3.1 holds.

Lean status: fully formalizable as finite-set inclusion/cardinality.

Lemma 4.3. If a degree-3 vertex `u` and a nonadjacent degree-4 vertex `v`
share two neighbors, then Lemma 3.1 holds.

Proof.

4.3.1. Let `P = {u, v}`.

4.3.2. `P` is independent because `u` and `v` are nonadjacent.

4.3.3. `|P| = 2`.

4.3.4. The outside neighborhood has size at most:

```text
3 + 4 - 2 = 5.
```

4.3.5. Since `5 = 3 * 2 - 1`, Lemma 3.1 holds.

Lean status: fully formalizable.

Assumption 4.4. Hard case.

After Lemmas 4.1 through 4.3, the proof may assume:

```text
every vertex has degree at least 3,
no configuration from Lemma 4.2 occurs,
no configuration from Lemma 4.3 occurs,
and every later "etc." easy overlap configuration is absent.
```

Lean blocker.

The paper writes "etc." after the first easy configurations.  A complete
formal proof must replace this by a finite list of forbidden overlap
lemmas, or avoid relying on the omitted list.  Later independence and
neighbor-count arguments implicitly use these missing forbidden
configurations.

## 5. Boundary Cycle and Turns

Construction 5.1. Boundary walk.

5.1.1. Choose a vertex `r_1` with minimum `y`-coordinate.

5.1.2. Start with the downward ray from `r_1`.

5.1.3. Rotate counterclockwise about the current pivot until the ray or
segment first hits a unit-distance neighbor.

5.1.4. Continue until the walk first revisits a vertex.

5.1.5. Let `C'` be the resulting cycle and let `C` be the path obtained by
removing the repeated endpoint.

Lean obligation `Cs98.boundary_walk_exists`.

- Prove the "first hit" exists at every step under minimum degree at least
  `3`.
- Prove the first repeated vertex produces a simple boundary cycle after
  deleting the repeated endpoint.
- Prove the cycle is the outer boundary of the embedded unit-distance graph.

Lean status: unformalized geometric dependency.  This should probably be
imported from a planar straight-line embedding or convex-hull/outer-face
package rather than proved ad hoc.

Lemma 5.2. Boundary degree bound.

For every boundary vertex `p_i` in `C`:

```text
3 <= d(p_i)
d(p_i) <= 5.
```

Proof obligations.

5.2.1. The lower bound follows from the hard-case assumption.

5.2.2. The upper bound uses geometry of unit neighbors around a boundary
vertex: one exterior sector is empty, and unit neighbors in the remaining
angle must be separated by angles at least `60 degrees`.

Lean status: `5.2.2` is an unformalized geometric dependency.

Definition 5.3. Turn at a boundary vertex.

For consecutive boundary vertices `p_{i-1}, p_i, p_{i+1}`, define:

```text
a(p_i) = 180 degrees - angle(p_{i-1}, p_i, p_{i+1}),
```

where the angle is measured clockwise while facing the interior of the
cycle.

Lean obligation `Cs98.turn`.

- Use radians in Lean.
- Replace `180 degrees` by `Real.pi`.
- Replace `60 degrees` by `Real.pi / 3`.
- State every inequality in real arithmetic.

Lemma 5.4. Boundary-turn lower bound.

For the path `C` obtained from the boundary cycle:

```text
sum_{p in C} a(p) > 240 degrees.
```

Proof obligations.

5.4.1. The full closed boundary turn is `360 degrees`.

5.4.2. The deleted endpoint has turn strictly less than `120 degrees`.

5.4.3. Subtracting the deleted endpoint gives the strict `> 240 degrees`
bound.

Lean status: unformalized geometric/topological dependency.

## 6. Regular, Irregular, and Special Degree-3 Vertices

Definition 6.1. Regular degree-3 boundary vertex.

Let `p_i` be a boundary vertex with `d(p_i) = 3`.  Its boundary neighbors are
`p_{i-1}` and `p_{i+1}`.  Let `q_1` be the third neighbor, ordered clockwise.

`p_i` is regular iff:

```text
angle(p_{i-1}, p_i, q_1) = 60 degrees
angle(q_1, p_i, p_{i+1}) = 60 degrees.
```

Definition 6.2. Irregular degree-3 boundary vertex.

`p_i` is irregular iff it is degree `3` and not regular.

Lemma 6.3. Irregular vertices have a boundary neighbor with no common
neighbor.

If `p_i` is irregular, then at least one of `p_{i-1}` and `p_{i+1}` has no
common neighbor with `p_i`.

Lean status: unformalized geometric dependency.

Required proof content.

- If both boundary neighbors shared common neighbors with `p_i`, the unit
  triangles around `p_i` would force both adjacent angles to be `60 degrees`.
- This is exactly regularity, contradiction.

Definition 6.4. Special pair.

If `p_i` is irregular, `p_j` is one of its boundary neighbors, `p_i` and
`p_j` have no common neighbor, and `d(p_j) >= 4`, then `(p_i, p_j)` is a
special pair.

## 7. Lemma 2: Special Pairs Neutralize Positive Turn

Lemma 7.1. Let `p_i` be irregular.  Suppose `(p_i, p_{i+1})` is a special
pair and:

```text
angle(q_1, p_i, p_{i+1}) = alpha
alpha > 60 degrees.
```

Then:

```text
a(p_i) + a(p_{i+1}) < 0.
```

Proof.

7.1.1. Reduce to `d(p_{i+1}) = 4`.

Lean obligation.

- If `d(p_{i+1}) = 5`, the additional neighbor contributes another angle
  of at least `60 degrees`, making `a(p_{i+1})` no larger.

Status: unformalized geometric monotonicity dependency.

7.1.2. Let the four neighbors of `p_{i+1}` be:

```text
p_i, q_2, q_3, p_{i+2}
```

in clockwise order.

7.1.3. Since `p_i` and `p_{i+1}` have no common neighbor:

```text
angle(p_i, p_{i+1}, q_2) >= 180 degrees - alpha.
```

Status: unformalized figure/angle dependency.

7.1.4. Each angle between adjacent unit-neighbor rays at the same center is
at least `60 degrees`, because the corresponding neighbor points are at
mutual distance at least `1`.

Lean obligation `Cs98.unit_neighbor_angle_ge_sixty`.

7.1.5. Sum the angles:

```text
(180 - a(p_i)) + (180 - a(p_{i+1}))
  > 60 + alpha + (180 - alpha) + 60 + 60
  = 360.
```

7.1.6. Rearrange to obtain:

```text
a(p_i) + a(p_{i+1}) < 0.
```

Lean status: algebra is formalizable after 7.1.1 through 7.1.4 are
available.

Corollary 7.2. If `p_i` is irregular and:

```text
a(p_{i-1}) + a(p_i) + a(p_{i+1}) > 0,
```

then:

```text
d(p_{i-1}) = 3 or d(p_{i+1}) = 3.
```

If:

```text
a(p_{i-1}) + a(p_i) + a(p_{i+1}) > 60 degrees,
```

then:

```text
d(p_{i-1}) = 3 and d(p_{i+1}) = 3.
```

Proof obligations.

7.2.1. Use Lemma 6.3 to choose a boundary neighbor with no common neighbor.

7.2.2. If that neighbor has degree at least `4`, apply Lemma 7.1 to cancel
the positive turn at `p_i`.

7.2.3. Bound any remaining adjacent positive turn by `60 degrees`.

Lean status: depends on Lemma 7.1 and a missing local turn upper bound for
degree-3 vertices.

## 8. Block Decomposition

Standing assumption 8.1.

There are no boundary vertices `p_j` and `p_{j+2}` with:

```text
d(p_j) = 3
d(p_{j+2}) = 3.
```

Justification.

8.1.1. If such vertices existed, `p_j` and `p_{j+2}` would be nonadjacent
degree-3 vertices sharing `p_{j+1}` as a neighbor.

8.1.2. Lemma 4.2 would give Lemma 3.1.

Lean status: fully formalizable once boundary indexing is available.

Definition 8.2. Neutral blocks.

8.2.1. If a regular degree-3 boundary vertex `r_i` has a boundary neighbor
`s_i` of degree `5`, choose one such `s_i`; the string `{r_i, s_i}` is a
neutral block.

8.2.2. If an irregular degree-3 boundary vertex `r_i` belongs to a special
pair, choose a special-pair neighbor `s_i`; the string `{r_i, s_i}` is a
neutral block.

Lean obligation.

- Prove the selected neutral blocks are pairwise disjoint.
- The paper asserts this for regular blocks by `s_i != s_j unless r_i = r_j`;
  a formal proof must include the corresponding statement for special pairs.

Definition 8.3. Positive blocks.

8.3.1. A regular degree-3 boundary vertex with no degree-5 boundary neighbor
chosen in Definition 8.2 is a positive block.

8.3.2. A consecutive pair of irregular degree-3 boundary vertices is a
positive block.

Definition 8.4. Negative blocks.

8.4.1. A degree-5 boundary vertex not in a neutral block is a negative block.

8.4.2. A maximal string of consecutive degree-4 boundary vertices is a
negative block if:

```text
sum of turns over the string <= -60 degrees,
and neither endpoint belongs to a neutral block.
```

Lean obligation.

- Define "maximal string" on a cyclic order.
- Prove negative degree-4 strings are disjoint from neutral blocks except
  where excluded.
- Prove vertices not assigned to a block have total turn `<= 0` on each
  unblocked interval.

Lemma 8.5. Block turn bounds.

8.5.1. Every negative block contributes at most `-60 degrees`.

8.5.2. Every positive block contributes at most `60 degrees`.

8.5.3. Every neutral block contributes at most `0 degrees` after pairing
the positive degree-3 turn with the special or degree-5 neighbor.

8.5.4. Every unblocked interval contributes at most `0 degrees`.

Lean status:

- 8.5.1 is by definition for degree-4 strings and by a degree-5 turn bound
  for singleton degree-5 blocks.
- 8.5.2 for regular singleton blocks is geometric; for irregular pairs it
  uses Corollary 7.2.
- 8.5.3 uses Lemma 7.1 or the regular-degree-5 neutralization argument.
- 8.5.4 is asserted in the paper and must be formalized as part of the block
  construction.

Lemma 8.6. Positive blocks outnumber negative blocks.

Let `Pcnt` be the number of positive blocks and `Ncnt` the number of negative
blocks.  Then:

```text
Pcnt > Ncnt + 4.
```

Proof.

8.6.1. By Lemma 5.4, total turn over `C` is greater than `240 degrees`.

8.6.2. By Lemma 8.5, the total turn is at most:

```text
60 * Pcnt - 60 * Ncnt.
```

8.6.3. Therefore:

```text
60 * Pcnt - 60 * Ncnt > 240.
```

8.6.4. Divide by `60`:

```text
Pcnt - Ncnt > 4.
```

8.6.5. Since counts are natural numbers:

```text
Pcnt > Ncnt + 4.
```

Lean status: formalizable after block decomposition and turn bounds.

Lemma 8.7. Adjacent good blocks exist.

In the cyclic order of blocks, there is a positive block followed by a block
that is positive or neutral.

Proof obligation.

- Prove the combinatorial statement on a cyclic list of block labels.
- Negative blocks cannot follow every positive block because Lemma 8.6 gives
  too many positive blocks.

Lean status: fully formalizable as finite cyclic-list counting.

## 9. Degree Patterns from Adjacent Good Blocks

Lemma 9.1. Let `B_j` be a positive block followed by a positive or neutral
block `B_{j+1}` as in Lemma 8.7.  Label the boundary vertices between them
as:

```text
p_1, p_2, ..., p_m.
```

Then the degree pattern is one of:

```text
(A) 4, 3, 3;
(B) 4, 3, <=4, <=4, ..., <=4, <=5, 3;
(C) 3, 3, <=4, <=4, ..., <=4, <=5, 3.
```

In cases `(A)` and `(B)`, `p_2` is regular, so `p_1` and `p_3` share two
neighbors.

Lean obligations.

9.1.1. Enumerate the eight possible pairs `(B_j, B_{j+1})` from the paper.

9.1.2. For each pair, construct the indexing `p_1, ..., p_m`.

9.1.3. Prove the corresponding degree pattern.

9.1.4. Prove that regularity of `p_2` forces `p_1` and `p_3` to share two
neighbors.

Lean status: unformalized finite case analysis.  This is figure-free but
must be written out explicitly; the paper compresses it into prose.

## 10. Case A: A Nearby Degree-3 Vertex

Assumption 10.1.

There exists `h` such that:

```text
3 <= h
h <= 15
h < m
d(p_h) = 3.
```

Lemma 10.2. Under Assumption 10.1, Lemma 3.1 holds.

Construction.

10.2.1. If `h` is even, define:

```text
P = {p_h, p_{h-2}, ..., p_2}.
```

10.2.2. If `h` is odd, define:

```text
P = {p_h, p_{h-2}, ..., p_1}.
```

Proof obligations.

10.2.3. Cardinality:

```text
1 <= |P|
|P| <= 8
```

because `h <= 15`.

10.2.4. Independence:

- no two chosen vertices are consecutive on the boundary;
- no chord joins two chosen vertices.

Status: the no-chord part is not proved explicitly in the paper.  It must be
derived from the excluded easy configurations, boundary-planarity, and
minimum-distance geometry.

10.2.5. Neighbor count:

```text
|N(P)| <= 3 * |P| - 1.
```

Required bookkeeping.

- The selected vertices have degrees controlled by Lemma 9.1: the endpoint
  `p_h` has degree `3`, while the earlier selected vertices can have degree
  `3` or `4`.
- If the selected set reaches `p_1`, then the proof must use the initial
  pattern from Lemma 9.1.  In cases `(A)` and `(B)`, regularity of `p_2`
  gives two common neighbors for `p_1` and `p_3`; in case `(C)`, the first
  two boundary vertices have degree `3`.
- Consecutive selected vertices along the alternating sequence must provide
  enough shared boundary/common-neighbor savings to reduce the naive
  degree-at-most-4 count to `3 * |P| - 1`.
- Vertices between selected vertices must not create additional distinct
  outside neighbors beyond the counted boundary and common-neighbor overlaps.

Status: unformalized in the paper.  A Lean proof needs an explicit incidence
map or injection from `N(P)` into a counted multiset of size `3 * |P| - 1`.

## 11. Case B: Long Degree-4 Run

Assumption 11.1.

Case A fails.  Then the proof uses:

```text
16 <= m
d(p_i) = 4 for 3 <= i <= 14
sum_{i=3}^{14} a(p_i) > -60 degrees
p_1 and p_3 have at most six neighbors altogether.
```

Lean obligations.

11.1.1. Prove `16 <= m` and the degree-4 run from the negation of Case A
and Lemma 9.1.

11.1.2. Prove the turn sum from the absence of negative blocks between
`B_j` and `B_{j+1}`.

11.1.3. Prove the "at most six neighbors altogether" statement.

Status: 11.1.1 and 11.1.2 are block-combinatorial once Lemma 9.1 is
available.  11.1.3 relies on cases `(A)` and `(B)` where `p_1` and `p_3`
share two neighbors.  In case `(C)`, `p_1` has degree `3`, `p_3` has degree
at most `4`, and they share the boundary neighbor `p_2`, giving at most
`3 + 4 - 1 = 6` neighbors.

Lemma 11.2. Lemma 3 hypothesis.

If Assumption 11.1 holds, then the hypotheses of Lemma 12.1 below hold for
the sequence:

```text
p_1, p_2, ..., p_14.
```

Lean status: formalizable after Assumption 11.1 is proved.

## 12. Lemma 3 and Its Internal Claim

Lemma 12.1. Long degree-4 run gives a local deletion.

Suppose there are consecutive boundary vertices:

```text
p_1, p_2, ..., p_14
```

such that:

```text
d(p_2) = 3
d(p_i) = 4 for 3 <= i <= 14
sum_{i=3}^{14} a(p_i) > -60 degrees
p_1 and p_3 have at most six neighbors altogether.
```

Then there is an independent set `P` satisfying Lemma 3.1.

Lean status: this is the main unformalized local geometric lemma.

### 12A. Claim for Six Consecutive Vertices

Claim 12.2. Let:

```text
p_0, p_1, ..., p_6
```

be consecutive boundary vertices with:

```text
d(p_i) = 4 for 1 <= i <= 5
a(p_i) + a(p_{i+1}) > -60 degrees for 1 <= i <= 4.
```

Then the following hold.

Claim 12.2(i). For `k = 1, 2, 3, 4`, the vertices `p_k` and `p_{k+1}` have
a common neighbor `r_k`.

Proof obligations.

- Assume no common neighbor.
- Use the figure to name the other neighbors around `p_k` and `p_{k+1}`.
- Prove three lower angle bounds:

```text
angle(b, p_k, p_{k+1}) + angle(p_k, p_{k+1}, c) > 180 degrees
angle(p_{k-1}, p_k, b) > 120 degrees
angle(c, p_{k+1}, p_{k+2}) > 120 degrees.
```

- Convert these inequalities into:

```text
a(p_k) + a(p_{k+1}) < -60 degrees,
```

contradiction.

Status: unformalized figure/angle dependency.

Claim 12.2(ii). Each `r_k` has at most two neighbors different from:

```text
p_k, p_{k+1}, r_{k-1}, r_{k+1}.
```

Proof obligations.

- Suppose `r_k` has three such neighbors.
- Name them in cyclic order.
- Use angle lower bounds around `r_k`.
- Derive that the full angle around `r_k` is strictly greater than
  `360 degrees`, contradiction.

Status: unformalized figure/angle dependency.

Claim 12.2(iii). Suppose `r_2` and `r_3` each have exactly two such other
neighbors, and:

```text
sum_{i=2}^{4} a(p_i) > -30 degrees.
```

Then `r_2` and `r_3` have a common side-neighbor:

```text
s_2 = s'_2,
```

with `s_2 != p_3`.

Proof obligations.

- If `s_2 != s'_2`, define the angles `alpha, beta, gamma` as in Fig. 6.
- Prove:

```text
alpha + beta + gamma < 210 degrees.
30 degrees < beta / 2 < 45 degrees.
```

- Express:

```text
|r_2 r_3| = 2 * sin(beta / 2).
```

- Bound the distance `|s_2 s'_2|` by a trigonometric expression strictly
  less than `1`.
- Contradict the minimum-distance assumption.

Status: genuinely analytic geometry/trigonometry dependency.

Claim 12.2(iv). Under the hypotheses of Claim 12.2(iii), the common
side-neighbor `s_2` has at most two neighbors different from:

```text
s_1, r_2, r_3, s'_3.
```

Proof obligations.

- Suppose `s_2` has three additional neighbors.
- Use Fig. 7 to define angles `epsilon` and `epsilon'`.
- Prove:

```text
epsilon < alpha + beta - 60 degrees
epsilon' < gamma + beta - 60 degrees.
```

- Sum the angles around `s_2` and obtain a contradiction to `360 degrees`.

Status: unformalized figure/angle dependency.

### 12B. Proof of Lemma 12.1

12.3. By Claim 12.2(i), every pair:

```text
p_i, p_{i+1}    for 3 <= i <= 13
```

has a common neighbor `r_i`.

Lean obligations.

- First prove a degree-4 boundary vertex has nonpositive turn.
- From `sum_{i=3}^{14} a(p_i) > -60 degrees`, prove every adjacent pair in
  the run satisfies:

```text
a(p_i) + a(p_{i+1}) > -60 degrees    for 3 <= i <= 13.
```

  Otherwise, the remaining degree-4 turns are nonpositive and the total
  over `p_3, ..., p_14` would be at most `-60 degrees`.
- Apply Claim 12.2(i) to sliding windows of six consecutive vertices.

12.4. If there exists `j` with:

```text
4 <= j
j <= 12
r_j has only one neighbor outside {r_{j-1}, r_{j+1}, p_j, p_{j+1}},
```

then Lemma 3.1 holds.

Construction.

12.4.1. If `j` is odd, select:

```text
P = {p_{j+2}, r_j, p_{j-1}, p_{j-3}, ..., p_2}.
```

12.4.2. If `j` is even, select:

```text
P = {p_{j+2}, r_j, p_{j-1}, p_{j-3}, ..., p_1}.
```

Required proof obligations.

- `P` is independent.
- `|P| = floor(j / 2) + 2`.
- `|P| <= 8`, since `j <= 12`.
- `|N(P)| <= 3 * |P| - 1`.

Status: the paper states the neighbor count but does not give the incidence
proof.  Independence is also implicit from the figure and the excluded local
configurations.

12.5. Otherwise, every `r_j` with `4 <= j <= 12` has exactly two such other
neighbors.

Lean obligation.

- Combine Claim 12.2(ii) with the negation of 12.4.

12.6. From:

```text
sum_{i=3}^{14} a(p_i) > -60 degrees
```

deduce that one half-run has turn greater than `-30 degrees`.

One possible formal statement:

```text
sum_{i=4}^{8} a(p_i) > -30 degrees
or
sum_{i=9}^{13} a(p_i) > -30 degrees.
```

The paper proceeds, without loss of generality, with:

```text
sum_{i=9}^{13} a(p_i) > -30 degrees.
```

Lean obligation.

- State the exact two half-runs used.
- Prove the pigeonhole inequality.
- Prove the symmetry that allows the second half-run to be assumed without
  loss of generality, or handle both cases separately.

12.7. Apply Claim 12.2(iii) to obtain:

```text
s_9 = s'_9
s_10 = s'_10
s_11 = s'_11.
```

Lean obligation.

- Apply the claim to the appropriate overlapping windows.
- Match all indices to the notation in Fig. 8.

12.8. Apply Claim 12.2(iv) to prove that `s_10` has at most two neighbors
outside:

```text
{s_9, s_11, r_10, r_11}.
```

Lean obligation.

- Match `s_1, r_2, r_3, s'_3` from Claim 12.2(iv) to
  `s_9, r_10, r_11, s_11`.

12.9. Define the final nine-point set:

```text
P = {s_10, r_12, r_9, p_14, p_11, p_8, p_6, p_4, p_2}.
```

Required proof obligations.

12.9.1. `|P| = 9`.

12.9.2. `P` is independent.

Status: not proved in the paper text.  This is a major blocker.  A formal
proof must show all 36 unordered pairs in `P` are nonadjacent, using:

- boundary separation,
- locations of the `r_i` and `s_i`,
- absence of forbidden easy configurations,
- minimum-distance constraints from the figures.

12.9.3. `|N(P)| <= 26`.

Status: not proved in the paper text beyond the assertion.  A formal proof
must provide a counted cover of `N(P)` with 26 slots and prove every outside
neighbor lands in one of them.

12.9.4. Since:

```text
26 = 3 * 9 - 1,
```

Lemma 3.1 follows.

Lean status: arithmetic is formalizable; independence and neighbor-count
bookkeeping are unformalized.

## 13. Algorithmic Content

Proposition 13.1. If Lemma 3.1 is constructive, the proof yields an algorithm
selecting an independent set of size at least `9n / 35`.

Proof obligations.

13.1.1. Construct the minimum-distance graph in `O(n log n)` time.

13.1.2. Repeatedly find one of the local configurations from Lemma 3.1.

13.1.3. Delete the selected independent set and its outside neighborhood.

13.1.4. Stop when no vertices remain.

Lean status: not needed for the existential theorem.  A verified executable
version would require data structures for geometric nearest-neighbor search
and certified detection of the local configurations.

## 14. Dependency Graph for Lean Transcription

14.1. Fully formalizable without new geometry.

- Definition 1.3: outside neighborhoods.
- Lemma 3.2: arithmetic local ratio.
- Theorem 3.3: local deletion implies global bound.
- Lemmas 4.1 through 4.3: easy finite graph configurations.
- Lemma 8.6: block count from turn bounds.
- Lemma 8.7: cyclic block-count combinatorics.
- Cardinality parts of Lemmas 10.2, 12.4, and 12.9.

14.2. Formalizable after standard geometric libraries are available.

- Definition 5.3: oriented angle and turn.
- Lemma 7.1 algebra after angle inequalities are supplied.
- Claim 12.2 trigonometric contradiction after coordinates/angle lemmas are
  supplied.

14.3. Genuinely unformalized dependencies in the paper.

- Boundary walk construction and proof that it gives the relevant outer
  boundary cycle.
- Boundary degree bound `d(p_i) <= 5`.
- Strict turn lower bound `sum_C a(p) > 240 degrees`.
- Irregular vertex common-neighbor Lemma 6.3.
- Lemma 7.1 figure inequalities.
- Block decomposition disjointness and treatment of unblocked intervals.
- Eight-case derivation of degree patterns in Lemma 9.1.
- Case A independence and neighbor-count proof.
- Claim 12.2 all figure-based angle inequalities.
- Lemma 12.1 final independence proof for the nine-point set.
- Lemma 12.1 final neighbor-count cover of size `26`.

## 15. Exact Blockers to a Complete Proof of `9 / 35`

Blocker 15.1. The "etc." in the easy local observations must be eliminated.

Needed output: a finite list of forbidden configurations, each with a
proved local-deletion lemma, sufficient for every later independence and
neighbor-count argument.

Blocker 15.2. The boundary package is missing.

Needed output: an outer-boundary cycle theorem for finite unit-distance
graphs with minimum degree at least `3`, including boundary degree at most
`5` and strict turn sum greater than `240 degrees` for the path `C`.

Blocker 15.3. The block decomposition is not formal.

Needed output: a cyclic-list construction proving disjointness, turn bounds,
unblocked interval negativity, and the adjacent-good-block lemma.

Blocker 15.4. The eight adjacent-block cases are compressed.

Needed output: eight explicit case proofs producing patterns `(A)`, `(B)`,
or `(C)` and the `p_1`, `p_3` common-neighbor condition where required.

Blocker 15.5. Case A lacks the two key finite proofs.

Needed output:

- a proof that the alternating set `P` is independent;
- a proof that `N(P)` has at most `3 * |P| - 1` vertices.

Blocker 15.6. Lemma 3 depends on figure-based analytic geometry.

Needed output:

- formal angle inequalities for Figs. 4, 5, and 7;
- the trigonometric distance contradiction for Fig. 6;
- all index translations for sliding windows.

Blocker 15.7. The final nine-point set in Lemma 3 is asserted, not proved.

Needed output:

- pairwise nonadjacency for
  `{s_10, r_12, r_9, p_14, p_11, p_8, p_6, p_4, p_2}`;
- an explicit 26-slot cover of its outside neighborhood.

Once Blockers 15.1 through 15.7 are resolved, the remaining path from
Lemma 3.1 to the theorem is routine finite graph and arithmetic
formalization.
