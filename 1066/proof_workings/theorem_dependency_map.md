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

S2 is reduced to the live actual-boundary theorem for the finite embedded
unit-edge drawing:

```text
FinitePlanarOuterComponentInputs C
  -> unboundedExteriorComponentRows C inputs
  -> ActualBoundaryCycleFrontierEquivalenceRows C inputs
     containing:
       B : UnitDistanceCycleBoundary C
       + graph vertex on frontier iff boundary-cycle vertex of B
       + every boundary-cycle edge has open segment on the unbounded exterior frontier
  -> unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
  -> UnboundedExteriorFrontierCycleRows C inputs
```

The drawing layer in `Swanepoel/FinitePlaneDrawing.lean` is checked.  It owns
closed/compact straight segments, the finite `embeddedEdgeSet`,
`drawingComplement`, graph-vertex membership in the drawing under
`FinitePlanarOuterComponentInputs`, and the fact that complement frontiers are
carried by unit-edge segments.  It also provides the uniqueness/isolation
lemmas `common_inOpenSegment_ordered_edges_eq`,
`common_inOpenSegment_closedSegment_ordered_edges_eq`, and
`exists_ball_inter_embeddedEdgeSet_subset_closedSegment_of_inOpenSegment`: an
interior point of a canonical edge has a ball in which every drawing point is
carried by that same edge segment.  It also provides
`exists_ball_inter_embeddedEdgeSet_subset_incident_closedSegment`, the local
vertex-star row saying that sufficiently near a graph vertex, every drawing
point is carried by an incident edge segment.

`Swanepoel/ExteriorComponentTopology.lean` owns the unbounded component and the
current S2 actual-boundary surface.  The concrete unbounded component is
`unboundedExteriorComponentRows C inputs`.  The shortest checked handoff now
erases `ActualBoundaryCycleFrontierEquivalenceRows C inputs` directly to
`UnboundedExteriorFrontierCycleRows C inputs` via
`unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`.

The carrier route remains checked and useful for building those rows, but it
is no longer the shortest final eraser.  The existing
`ExteriorComponentTopology.exteriorFrontierCarrierRows_of_inputs` consumes a
chosen boundary cycle and its geometric/frontier rows; it is a checked
consumer, not the input-only source.  The current boundary-edge carrier objects
are `unboundedFrontierVertexSet`, `unboundedFrontierEdgeSet`, and
`unboundedFrontierCarrierGraph`.

The checked reducers consume honest boundary-cycle/frontier rows and erase them
to either the direct actual-boundary package or the concrete carrier package.
They do not construct the exterior cycle or prove outerness.  Relevant checked
handoffs include:

```text
ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows
ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows
ExteriorComponentTopology.unboundedFrontierCarrierGraph_adj_iff
ExteriorComponentTopology.unboundedFrontierCarrierGraph_adj_canonicalAdj
ExteriorComponentTopology.unboundedFrontierCarrierGraph_openSegment_frontier_of_adj
ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_carrier
ExteriorComponentTopology.cyclicCoverageLocalSectorRows_of_boundaryVertexExteriorSectorRows
ExteriorComponentTopology.exteriorFrontierCarrierRows_nonempty_of_boundaryVertexExteriorSectorRows
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_faceDartOrbitExteriorCarrierRows
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_cyclicCoverageLocalSectorRows
```

Additional checked local handoffs for the face-orbit proof:

```text
FinitePlaneDrawing.isPreconnected_inOpenSegment
ExteriorComponentTopology.graph_vertex_mem_unboundedExterior_frontier_iff_mem_closure
ExteriorComponentTopology.exists_ball_forall_unboundedExterior_frontier_mem_incident_closedSegment_of_vertex
ExteriorComponentTopology.unboundedFrontierEdgeSet_or_symm_of_adj_openSegment_frontier
ExteriorComponentTopology.cutVertexPartition_of_unreachable_after_delete
ExteriorComponentTopology.repeatedExteriorBoundarySeparationRows_of_unreachable_after_delete
GeometricRotationSystem.geometricUnitDistanceRotationSystem_nextAround_getElem_succ
GeometricRotationSystem.geometricUnitDistanceRotationSystem_nextAround_getElem_last
```

The active final proof path is:

```text
actual exterior boundary cycle B
  + frontier iff B.vertex
  + boundary edge open-segment frontier
  -> ActualBoundaryCycleFrontierEquivalenceRows C inputs
  -> UnboundedExteriorFrontierCycleRows C inputs
  -> finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
  -> FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
```

The carrier/geometric support path is:

```text
GeometricBoundarySuccessorRows
  + graph vertex on frontier iff boundary-cycle vertex
  + boundary-edge open-segment frontier
  + BoundaryCycleIncidentFrontierEdgeCompleteness
  -> ExteriorComponentTopology.exteriorFrontierCarrierRows_of_inputs
     (checked consumer of the four rows)
  -> ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_carrier
```

The primitive exterior-sector branch is checked as well: a boundary cycle,
the frontier-vertex iff row, and pointwise
`BoundaryVertexExteriorSectorRowsAt` feed
`ExteriorComponentTopology.exteriorFrontierCarrierRows_nonempty_of_boundaryVertexExteriorSectorRows`.
Those sector rows also project to `GeometricBoundarySuccessorRows`, pointwise
local-sector rows, and `BoundaryCycleIncidentFrontierEdgeCompleteness`.

Under that route, the reducers already supply finiteness, connectedness,
two-regularity, graph injection, frontier-vertex coverage, and frontier-edge
honesty to the final carrier handoff.  Do not restate those reducer outputs as
independent S2 source targets.  The compact open proof obligations are now:

1. construct the actual exterior boundary cycle `B :
   JordanBoundaryConcrete.UnitDistanceCycleBoundary C`;
2. prove graph vertices on the unbounded exterior frontier iff they are
   boundary-cycle vertices of `B`;
3. prove every boundary-cycle edge of `B` has its open segment on the unbounded
   exterior frontier, using the checked boundary-edge open-segment frontier
   wrapper where applicable;
4. if using the carrier/geometric support path, prove
   `GeometricBoundarySuccessorRows` and
   `BoundaryCycleIncidentFrontierEdgeCompleteness`: every incident
   unbounded-frontier edge at a boundary-cycle vertex is one of the two cycle
   edges, using `inputs.noCutVertex` where needed to rule out repeated
   exterior-boundary vertices via the existing repeated-boundary separation and
   injectivity reducers.

Do not replace the actual boundary-edge carrier by the induced graph on all
frontier vertices: chords between frontier vertices can make that graph have
larger degree.  Do not use synthetic enclosure rows, convex-hull edges, an
arbitrary spanning cycle, identity angular-order rows, or any numbered
compatibility layer as the live method.  Do not add a new W-facade or duplicate
source package for S2; use the existing `ExteriorComponentTopology` carrier
surface.

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
