# Pach-Toth Figure 2 PostScript audit

Worker: PT-PostScriptAudit

Scope: `Proof_Files/PaTo96.ps`, `proof_workings/pach_toth_1996_lean_ready.md`,
and the current `FiniteGraph`, `ExactLocalGeometry`, `CrossBlockGeometry`
model.

Current-status note, 2026-05-19: this source audit remains useful for Figure 2
orientation and non-rigidity facts, but it is not the live Lean handoff.  Check
`theorem_dependency_map.md` and `nonvacuous_completion_route.md` for the
current W34 threshold route before turning these findings into tasks.

## Source findings

The paper prose immediately before Figure 2 gives two construction facts.

1. Consecutive blocks are not just translated copies. The text says that
   a closed chain is built from congruent copies of `B_1` "in the way indicated
   in the figure", with the orientation of `B_{i+1}` either the same as or
   opposite to the orientation of `B_i`; see `Proof_Files/PaTo96.ps:1235-1246`.

2. The drawing is explicitly non-rigid. The next sentence says "this figure is
   not rigid" and that the picture can be slightly deformed while preserving
   (a) no two vertices closer than one and (b) every adjacent pair at exactly
   distance one; see `Proof_Files/PaTo96.ps:1247-1254`.

Relevant short PostScript text snippets:

```postscript
1235-1246: ... orientation of B_{i+1} is either the same as or opposite ...
```

```postscript
1247-1254: Notice that this figure is not rigid.
```

Figure 2 itself contains three labeled block regions and endpoint alternatives:

- Block outlines are the three spline regions at `Proof_Files/PaTo96.ps:1849-1871`,
  `1874-1895`, and `1897-1917`.
- Labels `B_1`, `B_2`, `B_3` are emitted at `1955-1972`.
- The first block has labels `p` and `q` at `1935-1939`.
- The next visible block has labels `q` and `p` in swapped vertical roles at
  `1941-1945`.
- The figure labels the chain-end alternatives as `q_k (or p_k)` and
  `p_k (or q_k)` using the text pieces at `1979-1999` and `2000-2017`.

These snippets support the Lean-ready note's same/opposite orientation split
and its explicit deformation obligation, not a rigid-translation-only model.

## Figure 2 primitive data

The shaded triangle primitives in Figure 2 occur at
`Proof_Files/PaTo96.ps:1380-1396`. The unshaded triangle primitives occur at
`1726-1739`, `1747-1759`, `1767-1798`, `1834-1848`.

The first-block points used in the current transcription are visible in those
primitives:

```text
r_1 = (7225,10800)
T0 = {(8091,9300), (8091,10300), (7225,9800)}
T1 = {(8091,11300), (8091,12300), (7225,11800)}
T2 = {(8760,8557), (9069,9509), (9738,8766)}
T3 = {(9581,13184), (9091,12312), (8581,13172)}
T4 = {(11170,12502), (10179,12382), (10574,13301)}
```

PostScript support:

- `T4`: `Proof_Files/PaTo96.ps:1380`
- `T2`: `Proof_Files/PaTo96.ps:1382`
- `T1`: `Proof_Files/PaTo96.ps:1384`
- `T0`: `Proof_Files/PaTo96.ps:1386`
- `T3`: `Proof_Files/PaTo96.ps:1388`
- `r_1`: ellipse at `Proof_Files/PaTo96.ps:1813-1818`
- `p_1`: label at `1937-1939`, near the `T2` vertex `(9738,8766)`
- `q_1`: label at `1934-1936`, near the `T4` vertex `(11170,12502)`

## Lean-ready note comparison

`proof_workings/pach_toth_1996_lean_ready.md` already records the correct
high-level requirements:

- It says the paper gives Figure 2 plus a deformation argument, not exact
  coordinates: lines `8-10`.
- It introduces `Orientation` with `same` and `opposite` transitions: lines
  `111-123`.
- It requires `placeNext` transition maps matching those orientations: lines
  `259-275`.
- It requires a closed-chain placement and a certified non-rigid deformation:
  lines `277-298`.
- Its remaining-obligation list still asks for both relative orientations and
  the closed-chain deformation certificate: lines `761-771`.

## Current Lean model comparison

`FiniteGraph.lean` matches the first-block combinatorial certificate shape:

- `LocalVertex` is `r` plus five triples: lines `15-20`.
- The shaded triples are cliques: lines `51-54`.
- The first-block non-shaded edges are listed as `connectorAdj`: lines `56-81`.
- The forced six-set is `{r, T0_0, T1_1, T2_2, T3_0, T4_0}`: lines `97-100`.
- The next-forbidden set is `{T1_1, T1_2, T0_0, T0_2}`: lines `175-178`.
- The finite "full block forces next block at most four" theorem is present:
  lines `273-319`.

`ExactLocalGeometry.lean` matches a local exact realization, not the
PostScript drawing:

- The file states that coordinates are not the rounded PostScript drawing
  coordinates: lines `10-13`.
- The local grid coordinates are exact on `(i * sqrt 3 / 2, j / 2)`: lines
  `31-45` and `71-88`.
- It proves same-block graph edges are unit-distance and local vertices are
  separated: lines `103-128`.

`CrossBlockGeometry.lean` currently models pure translations only:

- The file says it studies translations by a grid offset: lines `7-10`.
- It proves the four finite connector edges split into disjoint translation
  families: lines `12-23`, with concrete offsets at `71-81`.
- It proves no single pure translation realizes all four connector units:
  lines `195-216`.
- Its own future-interface comment says the global bridge should avoid a false
  one-translation closure and should instead use a `place` function with direct
  connector-distance hypotheses: lines `218-243`.

Therefore the current Lean model matches the local combinatorics and exact
first-block realization, and it correctly detects that a single pure
translation is insufficient. It does not yet encode the paper's same/opposite
orientation transitions or the non-rigid closed-chain deformation.

## Geometry data to add next

The next data should be added as explicit, source-backed geometry interfaces:

1. An orientation type with the two transitions from the paper:
   `same` and `opposite`, sourced by `Proof_Files/PaTo96.ps:1235-1246`.
2. A `nextBlockAdj : Orientation -> LocalVertex -> LocalVertex -> Prop` or an
   oriented refinement of `CrossBlock.NextConnector`, sourced by Figure 2
   primitives and the endpoint labels at `Proof_Files/PaTo96.ps:1934-2017`.
3. Exact or parameterized `placeNext` maps for the two orientations, with
   proofs of connector unit distances and cross-block separation. The
   Lean-ready statement shape is already at
   `proof_workings/pach_toth_1996_lean_ready.md:259-275`.
4. A closed-chain placement with an explicit deformation parameter or
   certified placement family, proving that all intended adjacencies remain
   unit and all distinct vertices remain at least one apart. This is required
   by the paper's non-rigid sentence at `Proof_Files/PaTo96.ps:1247-1254` and
   by the Lean-ready obligations at
   `proof_workings/pach_toth_1996_lean_ready.md:277-298`.

No source line supports replacing these obligations with a single rigid
translation of each next block.
