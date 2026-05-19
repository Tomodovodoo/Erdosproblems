# Pach-Toth 1996 Lamport-style proof working

Source document: `../Proof_Files/PaTo96.ps`

Original paper: J. Pach and G. Toth, "On the independence number of coin
graphs", Geombinatorics 6 (1996), 30-33.

Current-status note, 2026-05-19: this is a source-paper roadmap, not the live
Lean handoff.  It should be read for paper structure and obligations; check
`theorem_dependency_map.md` for current Lean route status before starting work.

Status: proof skeleton only. The paper gives Figure 2 and a deformation
argument, not exact coordinates. A Lean proof of the 5/16 upper bound requires
the finite graph data and geometric realization obligations listed below.
Code blocks are statement shapes; the named predicates and structures are
local interfaces still to be implemented.

## 0. Lean-facing target

**Theorem PT96.Main.** For all sufficiently large `n`, there exists a planar
unit-distance configuration on `n` vertices with independence number at most
`ceil(5 * n / 16)`.

Lean-shaped statement:

```lean
theorem pach_toth_upper_bound_large_n
    (n : Nat) (hn : PT96.N0 <= n) :
    exists C : UDConfig n,
      forall S : Finset (Fin n),
        C.IsIndep S -> S.card <= Nat.ceilDiv (5 * n) 16
```

Dependency:

- `PT96.ExactBlocks`, the exact-multiple construction.
- `PT96.RemainderConstruction`, the construction for `n % 16` extra vertices.
- `PT96.RemainderArithmetic`, the residue arithmetic.

## 0A. Assumptions of this proof skeleton

**Assumption A.FG.** The finite graph data from Figure 2 has been transcribed
as `FG.1` through `FG.6`.

**Assumption A.GEO.** The geometric realization obligations `GEO.1` through
`GEO.4` have been proved from exact coordinates or exact parameterized
coordinates.

**Assumption A.CHAIN.** For every `k >= K0`, `A.GEO` produces a closed chain
whose block graph is exactly the graph specified by `A.FG`.

**Assumption A.REM.** The remainder components are placed far from the chain
and from each other except for their intended unit edges.

No theorem below is a complete Lean proof until these assumptions are replaced
by data and proofs.

## 1. Figure 2 finite graph data requirements

The following data must be transcribed from Figure 2 before the finite
independence proof is a Lean proof.

**Data FG.1, local vertices.**

```lean
inductive LocalVertex
  | r
  | tri (t : Fin 5) (c : Fin 3)
```

Required facts:

- `FG.partition`: the 16 local vertices are exactly `{r}` plus five disjoint
  shaded triples `tri t`.
- `FG.card`: the local vertex type has cardinality 16.

**Data FG.2, same-block adjacency.**

Required object:

```lean
sameBlockAdj : LocalVertex -> LocalVertex -> Prop
```

Required facts:

- `FG.same_irrefl`: `not (sameBlockAdj v v)`.
- `FG.same_symm`: `sameBlockAdj u v -> sameBlockAdj v u`.
- `FG.shaded_clique`: if `u` and `v` are distinct vertices in the same shaded
  triple `tri t`, then `sameBlockAdj u v`.
- `FG.r_blocks_nonfarthest`: for each shaded triple `tri t`, vertex `r` is
  adjacent to exactly the two vertices that are not the Figure 2 farthest
  vertex from `r`.
- `FG.same_complete`: every same-block unit edge intended by Figure 2 is in
  `sameBlockAdj`.

**Data FG.3, forced vertices.**

Required objects:

```lean
farthest : Fin 5 -> LocalVertex
p q : LocalVertex
```

Required facts:

- `FG.farthest_mem`: `farthest t` lies in shaded triple `tri t`.
- `FG.unique_not_adjacent_to_r`: within `tri t`, `farthest t` is the unique
  vertex not adjacent to `r`.
- `FG.p_is_farthest`: `p = farthest tp` for some `tp`.
- `FG.q_is_farthest`: `q = farthest tq` for some `tq`.
- `FG.p_ne_q`: `p != q`.

**Data FG.4, next-block adjacency.**

Required object:

```lean
nextBlockAdj :
  Orientation -> LocalVertex -> LocalVertex -> Prop
```

Here `Orientation` has the two Figure 2 transitions:

- `same`: `B_{i+1}` has the same orientation as `B_i`;
- `opposite`: `B_{i+1}` has the opposite orientation.

Required facts:

- `FG.next_complete`: every intended connector unit edge from `B_i` to
  `B_{i+1}` in Figure 2 is in `nextBlockAdj`.
- `FG.next_no_extra_for_proof`: the finite independence proof uses only
  `sameBlockAdj` and `nextBlockAdj`; no visual proximity is used as an edge.
- `FG.next_bound_after_pq`: if an independent subset of `B_{i+1}` avoids all
  vertices adjacent to `p_i` or `q_i`, then it has cardinality at most 4.

**Data FG.5, PostScript identifiers for the first block.**

The embedded `coin.ps` drawing supplies these drawing-coordinate identifiers
for the first block. These are labels for transcription, not certified metric
coordinates.

```text
r_1 = (7225, 10800)

T0 = {(8091, 9300),  (8091, 10300), (7225, 9800)}
T1 = {(8091, 11300), (8091, 12300), (7225, 11800)}
T2 = {(8760, 8557),  (9069, 9509),  (9738, 8766)}     p_1 = (9738, 8766)
T3 = {(9581, 13184), (9091, 12312), (8581, 13172)}
T4 = {(11170, 12502), (10179, 12382), (10574, 13301)} q_1 = (11170, 12502)
```

Obligation:

- `FG.transcription_check`: compare these identifiers with the rendered Figure
  2 and fix the local vertex ordering before writing Lean data.

**Data FG.6, edge classification table.**

Required object:

```lean
structure Figure2Edge where
  endpoint1 : Figure2VertexId
  endpoint2 : Figure2VertexId
  sourceTriangle : Option Figure2TriangleId
  class : EdgeClass

inductive EdgeClass
  | sameBlock (u v : LocalVertex)
  | nextSameOrientation (u v : LocalVertex)
  | nextOppositeOrientation (u v : LocalVertex)
  | drawingOnly
```

Required facts:

- `FG.edge_table_complete`: every side of every Figure 2 triangle primitive in
  `PaTo96.ps` has exactly one row in the table.
- `FG.edge_table_no_proof_gap`: every row used in `sameBlockAdj` or
  `nextBlockAdj` is classified as one of the three proof edge classes, not
  `drawingOnly`.
- `FG.edge_table_no_duplicates`: duplicate PostScript sides are identified as
  the same unordered edge.

Source primitives to classify:

```text
Shaded:
S0 = {(11170,12502), (10179,12382), (10574,13301)}
S1 = {(8760,8557),   (9069,9509),   (9738,8766)}
S2 = {(8091,11300),  (8091,12300),  (7225,11800)}
S3 = {(8091,9300),   (8091,10300),  (7225,9800)}
S4 = {(9581,13184),  (9091,12312),  (8581,13172)}
S5 = {(11655,8553),  (10871,7933),  (11800,7564)}
S6 = {(12685,7099),  (12645,8098),  (13530,7633)}
S7 = {(12691,12178), (12639,11179), (13530,11633)}
S8 = {(11084,9856),  (10454,10634), (11442,10790)}

Unshaded connector/auxiliary triangles:
U0  = {(7225,9800),   (7225,10800),  (8091,10300)}
U1  = {(8091,10300),  (8091,11300),  (7225,10800)}
U2  = {(7225,10800),  (7225,11800),  (8091,11300)}
U3  = {(8091,9300),   (8760,8557),   (9069,9509)}
U4  = {(9738,8766),   (10096,9700),  (10726,8922)}
U5  = {(10726,8922),  (10096,9700),  (11084,9856)}
U6  = {(10096,9700),  (11084,9856),  (10454,10634)}
U7  = {(11442,10790), (10454,10634), (10812,11568)}
U8  = {(11442,10790), (10812,11568), (11800,11724)}
U9  = {(10179,12382), (10574,13301), (9581,13184)}
U10 = {(9091,12312),  (8581,13172),  (8091,12300)}
U11 = {(10726,8922),  (10871,7933),  (11655,8553)}
U12 = {(11800,7564),  (12645,8098),  (12685,7099)}
U13 = {(11800,11724), (12639,11179), (12691,12178)}
U14 = {(13530,11633), (14396,11133), (13530,10633)}
U15 = {(13530,10633), (14396,11133), (14396,10133)}
U16 = {(13530,10633), (14396,10133), (13530,9633)}
U17 = {(13530,9633),  (14396,10133), (14396,9133)}
U18 = {(13530,9633),  (14396,9133),  (13530,8633)}
U19 = {(13530,8633),  (14396,9133),  (14396,8133)}
U20 = {(13530,8633),  (14396,8133),  (13530,7633)}
U21 = {(14396,8133),  (15065,7390),  (15374,8342)}
U22 = {(15065,7390),  (15374,8342),  (16043,7599)}
U23 = {(15396,11145), (14886,12005), (15886,12017)}
U24 = {(15886,12017), (16484,11215), (16879,12134)}
U25 = {(16484,11215), (16879,12134), (17475,11353)}
U26 = {(14396,11133), (15396,11145), (14886,12005)}
U27 = {(11800,11724), (10812,11568), (11170,12502)}
U28 = {(7225,8800),   (7225,9800),   (8091,9300)}
U29 = {(7225,11800),  (7225,12800),  (8091,12300)}
```

Obligations:

- `FG.edge_classification_complete`: classify every side of `S0` through `S8`
  and `U0` through `U29`.
- `FG.block_edge_projection`: derive `sameBlockAdj` from rows classified as
  `sameBlock`.
- `FG.next_edge_projection`: derive `nextBlockAdj` from rows classified as
  `nextSameOrientation` or `nextOppositeOrientation`.

## 2. Geometric realization obligations

The following obligations replace the paper's Figure 2/deformation sentence.

**Obligation GEO.1, exact local coordinates.**

Provide exact coordinates or exact parameterized coordinates:

```lean
localPoint : LocalVertex -> R2
```

Required facts:

- `GEO.local_sep`: distinct local vertices have distance at least `1`.
- `GEO.same_edges_unit`: if `sameBlockAdj u v`, then
  `dist (localPoint u) (localPoint v) = 1`.
- `GEO.same_no_unintended_close`: no distinct local pair has distance below
  `1`.

**Obligation GEO.2, transition maps.**

Provide the two transition placements:

```lean
placeNext :
  Orientation -> (LocalVertex -> R2) -> (LocalVertex -> R2)
```

Required facts:

- `GEO.next_edges_unit`: if `nextBlockAdj o u v`, then the placed copies of
  `u in B_i` and `v in B_{i+1}` have distance `1`.
- `GEO.next_sep`: every vertex of `B_i` and every vertex of `B_{i+1}` have
  distance at least `1`.
- `GEO.orientation_matches_figure`: the two maps are exactly the same/opposite
  Figure 2 transitions.

**Obligation GEO.3, closed chains.**

Provide a threshold and a closed-chain placement:

```lean
K0 : Nat
closedChain :
  (k : Nat) -> K0 <= k -> ChainPlacement k
```

Required facts:

- `GEO.chain_vertices`: the placement has exactly `16 * k` vertices, indexed
  by block and local vertex.
- `GEO.chain_edges_unit`: all same-block and next-block intended edges have
  distance exactly `1`.
- `GEO.chain_sep`: all distinct vertices in the whole chain have distance at
  least `1`.
- `GEO.chain_closed`: the last block connects to the first block with one of
  the two allowed orientations.
- `GEO.deformation_certified`: the non-rigid deformation used to close the
  chain preserves `GEO.chain_edges_unit` and `GEO.chain_sep`.

**Obligation GEO.4, remainder placement.**

For `r = n % 16`, place `r` extra vertices as disjoint unit triangles plus,
when needed, one extra unit edge or one isolated vertex.

Required facts:

- `GEO.remainder_sep`: all extra vertices are at mutual distance at least `1`.
- `GEO.remainder_edges_unit`: intended triangle/edge contacts have distance
  exactly `1`.
- `GEO.remainder_far_from_chain`: every extra vertex is at distance greater
  than `1` from every chain vertex.

## 3. Exact block theorem

**Theorem PT96.ExactBlocks.** For every `k >= K0`, there exists a closed chain
on `16 * k` vertices whose independent sets have cardinality at most `5 * k`.

Lean-shaped statement:

```lean
theorem pach_toth_chain_alpha_le
    (k : Nat) (hk : K0 <= k) :
    exists C : UDConfig (16 * k),
      forall S : Finset (Fin (16 * k)),
        C.IsIndep S -> S.card <= 5 * k
```

### Proof of PT96.ExactBlocks

Assumptions:

- `A.FG`.
- `A.GEO`.
- `A.CHAIN`.

<1>1. Instantiate the closed chain.

Claim:

```lean
exists C : UDConfig (16 * k), HasPT96ChainCombinatorics C k
```

Proof obligation:

- Apply `GEO.closedChain`, `GEO.chain_sep`, and `GEO.chain_edges_unit`.

Dependencies:

- `GEO.3`.

<1>2. Define the block counts.

Definition:

```lean
a i = (S.filter (fun v => blockIndex v = i)).card
```

Proof obligation:

- `PT96.block_sum`: `Finset.univ.sum a = S.card`.

Dependencies:

- `GEO.chain_vertices`.
- Finset partition by block index.

<1>3. Prove each block contributes at most 6.

Claim:

```lean
forall i, a i <= 6
```

Proof:

<2>1. The restriction of `S` to block `i` is independent for
`sameBlockAdj`.

Dependencies:

- `C.IsIndep S`.
- `GEO.chain_edges_unit`.
- `FG.same_complete`.

<2>2. Apply `PT96.BlockCardLeSix`.

Dependencies:

- `PT96.BlockCardLeSix`.

<2>QED. `a i <= 6`.

<1>4. Prove a full block forces the next block small.

Claim:

```lean
forall i, a i = 6 -> a (i + 1) <= 4
```

Proof:

<2>1. If `a i = 6`, equality holds in the five-triangle-plus-`r` bound.

Dependencies:

- `PT96.BlockCardLeSixEquality`.

<2>2. Equality forces `r_i in S` and one selected vertex in each shaded
triangle.

Dependencies:

- `FG.partition`.
- `FG.shaded_clique`.

<2>3. Since `r_i in S`, each selected triangle vertex is the unique vertex not
adjacent to `r_i`.

Dependencies:

- `FG.r_blocks_nonfarthest`.
- `FG.unique_not_adjacent_to_r`.
- Independence of `S`.

<2>4. Therefore `p_i in S` and `q_i in S`.

Dependencies:

- `FG.p_is_farthest`.
- `FG.q_is_farthest`.

<2>5. The restriction of `S` to block `i+1` avoids all vertices adjacent to
`p_i` or `q_i`.

Dependencies:

- `C.IsIndep S`.
- `GEO.next_edges_unit`.
- `FG.next_complete`.

<2>6. Apply `FG.next_bound_after_pq`.

Dependencies:

- `FG.next_bound_after_pq`.

<2>QED. `a (i + 1) <= 4`.

<1>5. Average the block counts.

Claim:

```lean
Finset.univ.sum a <= 5 * k
```

Proof obligation:

- Apply `PT96.CyclicAverageSixFour` to the results of `<1>3` and `<1>4`.

Dependencies:

- `PT96.CyclicAverageSixFour`.
- Closed cyclic block indexing from `GEO.chain_closed`.

<1>6. Conclude the independent set bound.

Proof:

<2>1. By `<1>2`, `S.card = Finset.univ.sum a`.

<2>2. By `<1>5`, `Finset.univ.sum a <= 5 * k`.

<2>QED. `S.card <= 5 * k`.

<1>QED. `PT96.ExactBlocks`.

## 4. Finite combinatorial lemmas

### Lemma PT96.BlockCardLeSix

Statement:

```lean
lemma BlockCardLeSix
    (A : Finset LocalVertex)
    (hA : IsIndependent sameBlockAdj A) :
    A.card <= 6
```

Proof:

Assumptions:

- `A.FG`.

<1>1. For each `t : Fin 5`, `A` contains at most one vertex of `tri t`.

Dependencies:

- `FG.shaded_clique`.
- `hA`.

<1>2. `A` contains at most one vertex outside the five shaded triples.

Dependencies:

- `FG.partition`, because the only outside vertex is `r`.

<1>3. Sum the five bounds plus the outside bound.

Dependencies:

- Finset disjoint-union cardinality.

<1>QED. `A.card <= 6`.

### Lemma PT96.BlockCardLeSixEquality

Statement:

```lean
lemma BlockCardLeSixEquality
    (A : Finset LocalVertex)
    (hA : IsIndependent sameBlockAdj A)
    (hcard : A.card = 6) :
    LocalVertex.r in A
      /\ forall t : Fin 5, exists! v, v in A /\ v in tri t
```

Proof:

Assumptions:

- `A.FG`.

<1>1. The proof of `BlockCardLeSix` bounds six disjoint parts by
`1 + 1 + 1 + 1 + 1 + 1`.

<1>2. If the total cardinality is 6, every part has cardinality exactly 1.

Dependencies:

- Natural-number equality in a sum of six terms each bounded by 1.
- `FG.partition`.

<1>QED. Equality structure.

### Lemma PT96.FullBlockForcesNextSmall

Statement:

```lean
lemma FullBlockForcesNextSmall
    (A B : Finset LocalVertex)
    (hA : IsIndependent sameBlockAdj A)
    (hB : IsIndependent sameBlockAdj B)
    (hcross : CrossIndependent nextBlockAdj A B)
    (hAcard : A.card = 6) :
    B.card <= 4
```

Proof:

Assumptions:

- `A.FG`.

<1>1. From `hAcard`, get `r in A` and one selected vertex in each shaded
triple.

Dependencies:

- `PT96.BlockCardLeSixEquality`.

<1>2. For each shaded triple, the selected vertex is `farthest t`.

Dependencies:

- `FG.unique_not_adjacent_to_r`.
- `hA`.

<1>3. Therefore `p in A` and `q in A`.

Dependencies:

- `FG.p_is_farthest`.
- `FG.q_is_farthest`.

<1>4. Since `A` and `B` are cross-independent, `B` avoids all neighbors of
`p` and `q` under `nextBlockAdj`.

Dependencies:

- `hcross`.

<1>5. Apply `FG.next_bound_after_pq`.

<1>QED. `B.card <= 4`.

### Lemma PT96.CyclicAverageSixFour

Statement:

```lean
lemma CyclicAverageSixFour
    {k : Nat} (hk : 0 < k) (a : Fin k -> Nat)
    (hle6 : forall i, a i <= 6)
    (hfull : forall i, a i = 6 -> a (i + 1) <= 4) :
    Finset.univ.sum a <= 5 * k
```

Proof:

<1>1. Define `full i := a i = 6`.

<1>2. If `full i`, then not `full (i + 1)`.

Dependencies:

- `hfull i`.
- `4 < 6`.

<1>3. Charge the surplus `1` of every full block to its successor.

Definition:

```lean
charge i = i + 1
```

<1>4. The charge map is injective on full blocks.

Dependencies:

- Addition by `1` is injective on `Fin k`.

<1>5. Every charged block has deficit at least `1`, because its value is at
most `4`.

Dependencies:

- `hfull`.

<1>6. Total surplus above `5` is at most total deficit below `5`.

Dependencies:

- `<1>4`.
- `<1>5`.
- Finite sum over `Fin k`.

<1>7. Rewrite this as `sum a <= 5 * k`.

<1>QED. Cyclic average.

## 5. Remainder theorem

**Theorem PT96.RemainderConstruction.** If `n = 16 * k + r` with `r < 16`,
and a closed chain exists for `k`, then there is an `n`-vertex configuration
whose independence number is at most
`5 * k + ceil(r / 3)`.

Proof:

Assumptions:

- `A.GEO`.
- `A.REM`.

<1>1. Build the `16 * k` chain using `PT96.ExactBlocks`.

<1>2. Build the `r`-vertex remainder:

- `r / 3` disjoint unit triangles;
- if `r % 3 = 1`, one isolated vertex;
- if `r % 3 = 2`, one unit edge.

<1>3. Place the remainder far from the chain.

Dependencies:

- `GEO.remainder_far_from_chain`.

<1>4. Any independent set splits into a chain part and a remainder part.

Dependencies:

- No unit edges between chain and remainder.

<1>5. The chain part has size at most `5 * k`.

Dependencies:

- `PT96.ExactBlocks`.

<1>6. The remainder part has size at most `ceil(r / 3)`.

Dependencies:

- Each unit triangle contributes at most 1.
- A unit edge contributes at most 1.
- An isolated vertex contributes at most 1.

<1>QED. Bound `5 * k + ceil(r / 3)`.

### Lemma PT96.RemainderArithmetic

Statement:

```lean
lemma RemainderArithmetic
    (n : Nat) :
    5 * (n / 16) + Nat.ceilDiv (n % 16) 3 <=
      Nat.ceilDiv (5 * n) 16
```

Proof:

<1>1. Write `n = 16 * q + r`, where `r = n % 16` and `r < 16`.

<1>2. Reduce the target to
`5 * q + ceil(r / 3) <= 5 * q + ceil(5 * r / 16)`.

<1>3. Cancel `5 * q`.

<1>4. Verify the 16 residue cases:

```text
r :  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
ceil(r/3):
     0  1  1  1  2  2  2  3  3  3  4  4  4  5  5  5
ceil(5r/16):
     0  1  1  1  2  2  2  3  3  3  4  4  4  5  5  5
```

<1>QED. Arithmetic bound.

## 6. Proof of PT96.Main

<1>1. Let `k = n / 16` and `r = n % 16`.

<1>2. Since `n >= N0`, prove `k >= K0`.

Dependency:

- Choose `N0 >= 16 * K0`.

<1>3. Apply `PT96.RemainderConstruction`.

<1>4. Apply `PT96.RemainderArithmetic`.

<1>QED. `PT96.Main`.

## 7. Exact blockers to complete the 5/16 proof

1. `FG.transcription_check`: the exact Figure 2 finite graph must be encoded,
   including all same-block edges, connector edges, and both relative
   orientations.
2. `FG.next_bound_after_pq`: the finite graph theorem "full block forces next
   block at most 4" must be proved by enumeration or a certificate.
3. `GEO.1`: exact local coordinates or exact parameterized local coordinates
   are missing from the paper.
4. `GEO.2`: the same/opposite transition maps must be encoded and proved to
   realize the connector graph.
5. `GEO.3`: the non-rigid deformation/closed-chain sentence in the paper must
   be replaced by a certified closed-chain construction and an explicit `K0`.
6. `GEO.4`: the far-apart placement of remainder components must be encoded
   for the local `UDConfig` API.
