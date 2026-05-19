# Theorem Dependency Map

This file is the durable context map for the Erdos problem 1066 Lean project.
It explains the live theorem routes, current guardrails, and where a worker
should look before editing.  It is not a proof claim and not an execution
checklist.  Use `../TASK.md` for active tasks.

Status note, 2026-05-19:

- `ErdosProblems1066.lean` imports the retained Lean tree: `872 / 872`
  project files, with no missing, extra, or duplicate imports in the latest
  coverage check.
- The Lean forbidden-token/trust-source scan over `ErdosProblems1066/` and
  `ErdosProblems1066.lean` was clean.
- A fresh full root build and CI-style axiom audit for the current checkout are
  still tracked as pending in `../TASK.md`.

## Reading Order

For a new worker:

1. Read `../TASK.md` for the selected obligation and completion gate.
2. Read this file for the live dependency graph.
3. Read `current_spines.md` for the compact conditional proof spines.
4. Read `remaining_fields_matrix.md` for the exact source packages still open.
5. Read `nonvacuous_completion_route.md` for route guardrails.
6. Read the relevant source roadmap only after that:
   `swanepoel_2002_lean_ready.md`, `pach_toth_1996_lean_ready.md`, or
   `pach_toth_postscript_audit.md`.

Status words:

- `checked`: root-imported infrastructure, subject to the current full-build
  gate in `../TASK.md`.
- `conditional`: Lean closes a target from explicit source fields.
- `open`: the source field/package still needs an honest inhabitant.
- `blocked`: a tempting route has a checked obstruction or no-go theorem.
- `legacy`: historical wave/audit material, not the live route.

## Public Facade

`ErdosProblems1066/KnownBounds.lean` is the public theorem facade.  It should
expose only unconditional bounds.

Current public verified wrappers:

- `Verified.upper_bound_third`
- `Verified.lower_bound_quarter`
- `PollackPach.lower_bound_quarter`

Swanepoel `8 / 31` and Pach--Toth `5 / 16` target names exist internally as
propositions and conditional closures.  They are not public verified wrappers
until their source packages are inhabited, the root build passes, and the
axiom audit is clean.

## Swanepoel Dependency Graph

Public lower-bound wrapper:

```text
KnownBounds.Verified.lower_bound_eight_thirty_one
  <- Swanepoel.targetLowerBoundEightThirtyOne
  <- SwanepoelW32FinalAssembly.targetLowerBoundEightThirtyOne_of_w34ActualRoutePremises
  <- SwanepoelW32FinalAssembly.W34ActualRoutePremises
```

Current status: `conditional`.  The public `KnownBounds` wrapper remains
blocked until `W34ActualRoutePremises` is inhabited unconditionally and
imported.

Current live gate surfaces:

```text
SwanepoelW32FinalAssembly.W34ActualRoutePremises
M8ConstructionDataInhabitationW33.StrongestRouteSource
NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure
```

The shortest current source constructor is:

```text
SwanepoelW32FinalAssembly.
  w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
```

There is also an expanded long-arc/W16 sibling:

```text
SwanepoelW32FinalAssembly.
  w34ActualRoutePremises_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
```

### Swanepoel Open Source Obligations

These are the compact positive obligations behind the W34 route.  They are the
right task shapes; older W20-W31 gates are compatibility context unless a task
explicitly asks for them.

| Stage | Open input | Lean surface | Purpose |
|---|---|---|---|
| S2 | Exact actual topology | `SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget` or `FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget` | Build the honest selected outer-face/topology rows from a minimal failure. |
| S3 | Sector order | `OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem` | Give the selected topology a usable nondegenerate outer-face sector order. |
| S4 | Closure/missing-field package | `SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage` | Close the exact topology package used by the compact W34 constructor. |
| S4 alt | Long-arc/W16 route | long-arc source plus W16 finite p/q source feeding the expanded constructor | Alternative when working directly through arc budget and finite spine rows. |
| S4 | Generated order rows | `FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows` | Produce the finite-walk generated cyclic order consumed by the route certificate. |
| S4 | Route coverage/realization carrier | `K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem` | Provide the selected frame realization carrier and K23 coverage rows. |
| S4 | Bad adjacency rows | `K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem` | Rule the bad-adjacency/common-neighbor cases needed by the route. |
| S5 | Compact angle rows | `ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource` | Supply the compact label-certificate angle package. |

The S5 compact package is now the preferred final angle handoff.  Atomic
Figure 8/Figure 9 rows are still useful local proof tasks, but they are not
the top-level blockers when the compact S5 package is available.

S2 is reduced to one finite planar straight-line theorem.  The checked reducer
is:

```text
JordanTopologyExteriorEnclosure.
  finitePlanarStraightLineOuterComponentTheorem_of_exterior_cycle_frontier_not_mem
```

The remaining S2 source theorem must, for every `FinitePlanarOuterComponentInputs C`,
choose a real exterior `UnitDistanceCycleBoundary C` and an exterior set whose
frontier contains exactly the chosen cycle vertices on graph vertices, with all
non-cycle graph vertices outside the exterior.  The reducer then supplies the
boundary-following rotation system, face orbit, `FinitePlanarStraightLineOuterComponentTheorem`,
chosen Jordan rows, and finally the exact W32/W33 topology target.

The first drawing layer is checked in `Swanepoel/FinitePlaneDrawing.lean`.
It defines `embeddedEdgeSet`, `embeddedEdgePairs`, and `drawingComplement`,
proves closed segments are compact/closed, proves the embedded drawing is a
finite compact closed union of unit-edge segments, proves
`drawingComplement_open`, `drawingComplement_nonempty`, and
`frontier_drawingComplement_subset_embeddedEdgeSet`, and proves
`vertex_mem_embeddedEdgeSet_of_inputs`: every graph vertex is on the embedded
unit-edge drawing under `FinitePlanarOuterComponentInputs`.  It also constructs
a rightward x-axis ray outside the compact drawing and proves that ray is
preconnected and unbounded.

`Swanepoel/ExteriorComponentTopology.lean` adds the next checked reduction.
An `ExteriorComponentRows` exterior is an open subset of `drawingComplement C`,
so `graph_vertex_not_mem_exterior` proves all graph vertices are outside it.
`drawingComplementRows` supplies the whole open complement as the weakest
candidate.  Therefore `ExteriorFrontierCycleRows` only has to choose the
exterior unit-distance cycle and prove `frontier_iff_cycle_vertex`; the
off-cycle not-in-exterior row is automatic.  `ExteriorConnectedComponentRows`
packages connected components of the drawing complement and proves they are
open, connected, contained in the complement, and have frontier contained in
the embedded drawing.  `unboundedExteriorComponentRows` now constructs the
unbounded component using the x-axis ray outside the compact drawing; graph
vertices are proved outside it, and its frontier is carried by the embedded
drawing.  The helper `unboundedExteriorFrontierCycleRowsOfBoundary` reduces the
remaining proof to choosing the simple unit-distance outer cycle for that
component and proving `frontier_iff_cycle_vertex`.  `FaceBoundaryTopologySourceW32`
now consumes a family of those rows directly to produce
`MinimalFailureExactActualTopologyFieldsTarget`.

The sharpest checked S2 reducer is now
`ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_connected_two_regular_frontier_graph`.
It avoids adding another target: if the actual unbounded-frontier edge carrier
is presented as a finite connected two-regular graph `F`, with an injective
homomorphism `F -> GraphBridge.unitDistanceSimpleGraph C` whose vertex image is
exactly the graph vertices on
`frontier (unboundedExteriorComponentRows C inputs).exterior`, then Lean builds
the required `UnboundedExteriorFrontierCycleRows C inputs`.  The exact blocker
is therefore the finite plane-graph theorem constructing this boundary-edge
carrier and proving connectedness, degree two, and the frontier vertex iff.
Do not replace this by the induced graph on all frontier vertices: chords
between frontier vertices can make that induced graph have degree greater than
two, even when the exterior boundary itself is a simple cycle.

### Swanepoel Guardrails

- Do not add another numbered facade unless it directly removes one of the
  source obligations above.
- Do not mark a topology/angle task complete merely because a conditional
  wrapper exists.  The row must be inhabited from the minimal-failure data.
- Keep no-cut/minimality work tied to
  `NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure`.
- The source roadmap `swanepoel_2002_lean_ready.md` explains the paper
  chronology; this file names the current Lean handoff.

## Pach--Toth Dependency Graph

Public upper-construction wrapper:

```text
KnownBounds.Verified.upper_bound_five_sixteen
  <- PachToth.targetUpperConstructionFiveSixteenArbitrary
```

Current status: `conditional/open`.  The direct exact-base all-positive
flexible route is checked blocked.  The live positive route is the W34
threshold/eventual route:

```text
PachTothRemainingSourceLedgerW34.
  exactAndArbitraryTargets_of_largeClosedPlacementFieldsSix_and_below
    <- LargeClosedPlacementFieldsSix
    <- BelowThresholdMetricFieldsSix
    <- MinimalExactRemainderSplitSourceBlocker
```

Useful large-side handoff:

```text
AlternativeNonRigidClosedPlacementW34.
  largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix
```

### Pach--Toth Open Source Obligations

| Stage | Open input | Lean surface | Purpose |
|---|---|---|---|
| P1 | Non-rigid same/opposite transitions | `EventualRoleHingeClosure`, `RoleHingeCandidateSearchSurface` | Replace impossible translated connector equations with honest transition geometry. |
| P2 | Period/closure data | `PeriodSearchInterface`, `EventualPeriodSearchData` | Supply orientation words and closure equations for the generated chain. |
| P3 | Cross-block separation | `GeneratedSeparationFarApart`, `EventualCrossBlockMetricData` | Prove reduced non-connector square-distance lower bounds. |
| P4 | Large block closure | `EventualClosedPlacementSourceW34`, `AlternativeNonRigidClosedPlacementW34`, `PachTothRemainingSourceLedgerW34.LargeClosedPlacementFieldsSix` | Close exact placements from block length six onward. |
| P5 | Small block complements | `PachTothRemainingSourceLedgerW34.BelowThresholdMetricFieldsSix`, `SmallLengthExactTargetsConcreteW24.DeformedLengthOneExactBlocksTwoThroughFiveSource` | Provide genuine certificates for lengths below the large threshold. |
| P6 | Remainder split | `RemainderSplitSourceClosureW32`, `PachTothRemainingSourceLedgerW34.MinimalExactRemainderSplitSourceBlocker` | Route exact block targets to arbitrary `n`. |

### Pach--Toth Blocked Routes

Do not hand off the following as live construction targets:

```text
FiniteReducedMetricCandidateSearchW33.not_directFlexibleSourceShape
FlexibleCandidateMetricInhabitationW33.not_nonempty_directFlexibleSourcePayload
DeformedLengthOneSourceW34.not_nonempty_directFlexibleSourcePayload
```

These no-go theorems rule out the exact-base/direct-flexible all-positive
payload.  The remaining construction must be threshold/eventual, deformed, and
source-backed.

## File-Structure Policy

- Prefer proving a paper lemma or source package in its owning existing module.
- Create a new Lean file only for a real ownership, import-boundary,
  reusable-certificate, or compile-time advantage.
- Keep obstruction/no-go modules clearly documented as obstruction routes.
- Put disposable non-Markdown logs under `proof_logs/`, not `proof_workings/`.
- `proof_workings/` is for durable Markdown proof/context documents only.
