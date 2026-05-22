# Theorem Dependency Map

This file is the durable context map for the Erdos problem 1066 Lean project.
It explains the live theorem routes, current guardrails, and where a worker
should look before editing.  It is not a proof claim and not an execution
checklist.  Use `../TASK.md` for active tasks.

Status note, 2026-05-22:

- `ErdosProblems1066.lean` imports the retained Lean tree: `880 / 880`
  project files, with no missing, extra, or duplicate imports in the latest
  coverage check.
- The Lean forbidden-token/trust-source scan over `ErdosProblems1066/` and
  `ErdosProblems1066.lean` was clean.
- The pinned full root build was replayed after the current S2 q44/q46 cleanup
  with
  `elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066`, and it
  completed successfully.  `../TASK.md` records the live S2 source target and
  completion gate.
- q50/q51/q7/q42 support is checked support only.  q60's minimal-separation
  composer is also checked conditional support only: the q32 start-edge
  projection is superseded because the q32 package erases the selected seed
  local row behind `Classical.choice`.  The current live refinement is the q61
  seed-visible route, avoiding projection from the lossy q32 package.
- q62 compresses the seed-visible route further: cut-partition input rows,
  selected-head geometric rows, selected-head endpoint rows, selected-carrier
  successor rows, and deleted-tail separation for the concrete q62/q61
  selected raw orbit feed the actual-sector source.  The cyclic-successor
  nonreachability variant now composes directly to actual-sector rows;
  endpoint-closed separation remains an optional selected-orbit support leaf,
  not a revived endpoint branch.
- The live source target remains
  `faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs` followed by the
  actual exterior-sector eraser; no W32 composer, endpoint branch, induced
  frontier graph, convex-hull shortcut, or global no-between branch is live.

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

Provenance/source-family rule: for Swanepoel S2, use Csizmadia only for the
constructive rotating boundary-walk source model.  Swanepoel's paper invokes a
simple outer boundary polygon as a standard plane-graph fact; Csizmadia gives a
more explicit lowest-vertex rotating ray/segment walk that can guide the Lean
exterior face-orbit construction.  Do not import Csizmadia's later `9 / 35`
local-deletion, block-decomposition, Case A/B, or figure-geometry machinery
into S2.  Those remain separate Csizmadia formalization obligations.

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

S2 q41 is reduced to the live actual exterior face-orbit source for the finite
embedded unit-edge drawing.  The intended construction is the Csizmadia-style
rotating exterior angular walk, followed by no-cut tail injectivity, actual
`FaceDartOrbitExteriorCarrierRows C inputs`, and same-boundary angular rows:

```text
FinitePlanarOuterComponentInputs C
  -> unboundedExteriorComponentRows C inputs
  -> FaceDartOrbitExteriorCarrierRows C inputs
     + same-boundary BoundaryVertexAngularNoBetweenRows
  -> actualExteriorSectorInputSourceRows_of_inputs
  -> Exists B : UnitDistanceCycleBoundary C,
       graph vertex on frontier iff boundary-cycle vertex of B
       + Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

The q37 primitive-to-cut route and q38/q39/q40 endpoint-side routes are checked
support for this source, not live S2 targets.

Checked q41 support in `S2SeededRawOrbitSource.lean`:

```text
S2_q41_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_frontierVertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_cyclicSuccCutPartitions_faceSuccTurn
```

This removes finite no-open as a separate premise from the r18 actual-sector
source surface by deriving it from the same-`K` trace no-closed topology row.
It still leaves the real producer obligations live: frontier-vertex incident
selected edge rows, selected carrier/geometric rows, cyclic-successor cut rows,
and genuine same-boundary `faceSucc` turn/angular rows on the same selected raw
orbit.

Checked q44/q45 support in `S2SeededRawOrbitSource.lean`:

```text
S2_q44_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
S2_q44_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_frontierVertexIncident_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
S2_q45_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
```

These compose the q42 selected raw `faceSucc` source into the actual-sector
source shape and lower finite no-open/frontier-incident prerequisites through
trace-no-closed topology plus punctured/outside-accumulation support.  They are
not source producers for the geometric-selection, local angular/orientation, or
cyclic-successor cut rows.

Additional q45 source-support lowerings:

```text
S2_q45_rawFaceWalkThirdCarrierNeighborRepeatedTailCutPartitionSource_of_repeatedTailIndex_cyclicSuccCutPartitions
S2_q45_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource_of_repeatedTailIndex_cyclicSuccCutPartitions_noCut
S2_q45_kComponentTraceNoClosedSeparation_of_janiszewskiBoundaryBumping_20260522q45
frontierVertexIncidentSource_of_frontierPreconnected_boundaryBumpingObstruction_localIsolation
S2_q45_geometricSelectionInputSource_family_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
S2_q45_boundaryFreeLocalSectorGeometricAngularSource_family_of_unreachableAfterDelete_boundaryVertexExteriorSectorRows_selectedHeads
S2_q45_orientationRows_family_of_geometricSelection_selectedCarrierRows
S2_q45_localStrictOrder_family_of_geometricSelection_selectedCarrierRows
```

These reduce the current route leaves to sharper repeated-tail/cut,
Janiszewski topology, punctured frontier incidence, and selected-head local
geometric rows.  They keep the dependency direction acyclic: the final
`ActualExteriorSectorInputSourceRows` package is not used to prove the raw
exterior face-walk producer.

q46 outside/frontier support in `ExteriorComponentTopology.lean`:

```text
S2_q46_outsideAccumulationForcesActualFrontier_of_boundaryBumpingObstruction_20260522
S2_q46_outsideAccumulationSource_of_frontierVertexIncident_20260522
S2_q46_puncturedAccumulationSource_of_frontierPreconnected_boundaryBumpingObstruction_20260522
S2_q46_frontierVertexIncidentSource_of_frontierPreconnected_boundaryBumpingObstruction_localIsolation_20260522
S2_q46_outsideAccumulationSource_of_frontierPreconnected_boundaryBumpingObstruction_localIsolation_20260522
```

These connect singleton boundary-bumping obstruction, punctured accumulation,
frontier-incident selected edge rows, and outside-accumulation rows without
using all-adjacent endpoint/chord claims or the final actual-sector package.

The direct actual-boundary eraser remains checked support:

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
current S2 actual-boundary surface.  `Swanepoel/S2LocalTwoGermAssembly.lean`
and `Swanepoel/S2ExteriorBoundarySource.lean` own the current source-facing
local two-germ and boundary-sector assembly rows.  The concrete unbounded
component is `unboundedExteriorComponentRows C inputs`.  The shortest checked
handoff for the exact topology target now consumes a boundary cycle plus
pointwise `BoundaryVertexExteriorSectorRowsAt` via
`FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows`.
The actual-boundary eraser still converts
`ActualBoundaryCycleFrontierEquivalenceRows C inputs` to
`UnboundedExteriorFrontierCycleRows C inputs` via
`unboundedExteriorFrontierCycleRows_of_actualBoundaryCycleFrontierEquivalenceRows`.

2026-05-21 local-source update: the concrete local selected-carrier leaf now
has checked handoffs from the honest exterior face-dart carrier package:

```text
FaceDartOrbitExteriorCarrierRows C inputs
  -> S2CarrierLocalSource.ActualCarrierDegreeTwoSource inputs
  -> S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs
```

2026-05-21 j16 local-source refinement: the e32 fieldwise cut source is also
checked below actual exterior-sector input rows:

```text
exists B,
  graph vertex on unbounded exterior frontier iff B.vertex k
  + Nonempty (ActualExteriorSectorInputSourceRows inputs B)
  -> FaceDartOrbitExteriorCarrierRows C inputs
  -> S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs
```

The exact declarations are
`S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows`
and
`S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_family_20260521j16_of_actualExteriorSectorInputSourceRows`.
The same lowering is also available directly from primitive same-boundary
sector rows through
`S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows`
and
`S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_family_20260521j17_of_boundaryVertexExteriorSectorRows`.

2026-05-21 r9 S2 source boundary:

```text
FinitePlanarOuterComponentInputs C
  -> BoundaryFreeNoThirdGermSource inputs
  -> (unboundedFrontierCarrierGraph C inputs).Connected
  -> RawOrbitIteratedFaceSuccOpenSegmentFrontierNoOrbitSource inputs
     or RawOrbitIteratedFaceSuccLocalSectorTransitionNoOrbitSource inputs
  -> pairwise RawFaceSuccOrbitRepeatedTailExteriorCutRows on the selected orbit
  -> SelectedRawOrbitGeometricFaceSuccTurnRows on that same orbit
  -> S2RawGeometricFaceSuccOrbitSourcePackage C inputs
  -> FaceDartOrbitExteriorCarrierRows C inputs + same-boundary angular rows
  -> actualExteriorSectorInputSourceRows_of_inputs
```

New checked source-boundary declarations:

```text
RawOrbitIteratedFaceSuccOpenSegmentFrontierNoOrbitSource
rawOrbitIteratedFaceSuccOpenSegmentFrontierNoOrbitSource_of_localSectorTransition
rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_openSegmentFrontierNoOrbitSource
S2_r8h_rawGeometricFaceSuccOrbit_sourcePackage_family_of_boundaryFree_connected_selectedEdge_repeatedTailExteriorCutRows_faceSuccTurn
S2_r7j_component_topology_input_source_family_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j
S2_selected_carrier_neighbor_source_family_20260521_of_geometricSelectionInputSource
unboundedFrontierCarrierGraph_connected_family_of_componentTopologyInputSourceRows
boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointNoThird_20260521r61
selectedRawOrbitRepeatedTailExteriorCutRows_of_cyclicSuccCutPartitionSource_20260521current7
selectedRawOrbitGeometricFaceSuccTurnRows_of_faceSuccGeometricNonwrapRows
```

These declarations are source lowerings and erasers only.  The remaining S2
producer work is still the finite plane-graph construction of those source
leaves from `FinitePlanarOuterComponentInputs C`, especially the actual
exterior-oriented `faceSucc` local transition, repeated-tail cut partitions,
and raw same-boundary turn/orientation rows.

2026-05-21 r11 S2 source boundary update:

```text
topology points-between
  <- PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction

BoundaryFreeLocalSectorGeometricAngularSource
  <- S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
     + selected-head getElem geometric-order rows
     + IncidentGermEndpointSelectedEdgeNoThirdRows

SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
  <- SelectedRawOrbitRepeatedTailPrimitiveSourceRows

SelectedRawOrbitFaceSuccGeometricNonwrapRows
  <- SelectedRawOrbitGeometricFaceSuccTurnRows

carrier-cut fieldwise rows
  <- concrete third-neighbour repeated-tail cut partitions
```

Checked r11 declarations:

```text
S2TopologySource.S2_r11_topology_points_between_source_20260521r11
S2CarrierLocalSource.S2_r11_boundaryFreeLocalSectorGeometricAngularSource_family_of_finitePlaneLocalSeparationPrimitive_getElem_selectedEdgeNoThirdRows
S2SeededRawOrbitSource.selectedRawOrbitCyclicSuccDeletedTailCutPartitionSource_of_primitiveSourceRows_20260521pool7
S2SeededRawOrbitSource.S2_r11_faceSucc_nonwrap_source_family_20260521r11
S2CarrierCutSource.S2_r11_carrierCutFieldwiseFamily_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions
```

Q37 repeated-tail lowerings:

```text
S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows O i j
  + i != j
  + (O.dart i).tail = (O.dart j).tail
  -> RawFaceSuccOrbitRepeatedTailExteriorCutRows O i j

SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
  <- SelectedRawOrbitRepeatedTailBoundaryArcRows
  <- SelectedRawOrbitRepeatedTailPrimitiveSourceRows

SelectedSeededRawOrbitMinimalDeletedTailSeparation
  <- SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
  <- SelectedRawOrbitRepeatedTailPrimitiveSourceRows on the q30 selected seed

actualExteriorSectorInputSourceRows q30 family
  <- FiniteDrawingUnboundedComplementFrontierNoOpenSeparation
  + FrontierVertexIncidentUnboundedFrontierEdgeSource
  + UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
  + SelectedNeighborIncidentGermFrontierEdgeMembershipRows
  + RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource
  + SelectedRawOrbitRepeatedTailPrimitiveSourceRows
```

Checked q37 declarations:

```text
S2ExteriorBoundarySource.S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows.toRepeatedTailExteriorCutRows
S2SeededRawOrbitSource.S2_q37_cyclicSuccDeletedTailNonreachabilitySource_family_of_exteriorFaceOrbitSeedSource_boundaryArcRows
S2SeededRawOrbitSource.S2_q37_cyclicSuccDeletedTailNonreachabilitySource_family_of_exteriorFaceOrbitSeedSource_primitiveSourceRows
S2SeededRawOrbitSource.S2_q37_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_primitiveSourceRows
S2SeededRawOrbitSource.S2_q37_selectedSeededRawOrbitMinimalDeletedTailSeparation_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_primitiveSourceRows
```

These still do not construct the exterior boundary cycle.  They sharpen the
remaining producer obligations to: topology no-subcontinuum obstruction,
selected carrier `getElem`/endpoint no-third rows, actual `faceSucc`
open-segment preservation, repeated-tail cut partitions from the exterior
walk, and genuine selected geometric turn rows.

2026-05-21 r13 faceSucc-turn update:

```text
SelectedRawOrbitGeometricFaceSuccTurnRows on the selected seeded raw orbit
  <- RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource
     on the same selected exterior carrier heads
```

Checked declarations:

```text
S2SeededRawOrbitSource.selectedSeededRawOrbitGeometricFaceSuccTurnRows_of_selectedActualCarrierFaceSuccAngleRows_20260521r13
S2SeededRawOrbitSource.S2_r13_selectedRawOrbitGeometricFaceSuccTurnRows_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
S2SeededRawOrbitSource.S2_r13_selectedRawOrbitGeometricFaceSuccTurnRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
```

The r13 bridge is a source lowering, not a final-S2 assumption: it still
requires the actual selected-carrier `faceSucc` angle rows.  It uses the
geometric raw `faceSucc` orbit endpoint equality at the cyclic predecessor and
eta-expands the successor-tail geometric row through dependent selected-row
lets.  It does not revive global all-outgoing no-between or W32/final
actual-sector rows.

2026-05-21 r15 r30/r36 local update:

```text
S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
+ Nonempty UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
  <- BoundaryFreeLocalSectorGeometricAngularSource
```

Checked declarations:

```text
S2CarrierLocalSource.S2_r15_r30_finitePlaneLocalSeparationPrimitive_of_boundaryFreeLocalSectorGeometricAngularSource
S2CarrierLocalSource.S2_r15_r36_geometricSelectionInputSource_of_boundaryFreeLocalSectorGeometricAngularSource
S2CarrierLocalSource.S2_r15_r30_r36_local_sources_of_boundaryFreeLocalSectorGeometricAngularSource
S2CarrierLocalSource.S2_r15_r30_r36_local_sources_family_of_boundaryFreeLocalSectorGeometricAngularSource
```

This is the current strict local dependency boundary.  The remaining
input-only theorem below it is the boundary-free local geometric-angular
source at each actual unbounded-frontier vertex; the r15 declarations only
erase that source to the r30/r36 lane and do not introduce boundary cycles,
actual-sector rows, W32, induced frontier graphs, or global outgoing
no-between rows.

Topology refinement on the same pass:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
  -> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
  -> PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
  -> PlanarContinuumUnboundedComplementFrontierPreconnected
```

The checked declarations are
`ExteriorComponentTopology.planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_subcontinuumPointsBetween`,
`ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_crossingSubcontinuumPointsBetween`,
and
`ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierPreconnected_of_crossingSubcontinuumPointsBetween`.

The local remaining construction can therefore be pursued as the actual
exterior face-orbit carrier, with selected `unboundedFrontierEdgeSet` edge
rows, rather than as an induced frontier graph, all-adjacent endpoint row, or
outgoing-list no-between row.

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
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows
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

The checked final consumer path is:

```text
actualExteriorSectorInputSourceRows_of_inputs
  + S1 noCutRows
  -> FaceBoundaryTopologySourceW32.
       minimalFailureExactActualTopologyFieldsTarget_of_actualExteriorSectorInputSourceRows
```

S2 should be proved orbit-first internally and boundary-sector externally.  The
primary theorem to target is:

```text
S2ExteriorBoundarySource.faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
```

After that producer is proved from `FinitePlanarOuterComponentInputs C`, the
next theorem is
`S2ExteriorBoundarySource.actualExteriorSectorInputSourceRows_of_inputs`.
Do not add a new W32 composer while this producer/eraser pair remains open.

The checked final-cycle handoffs are reducer support only.  Do not make a new
S2 task that hands actual rows, sector rows, carrier rows, or selected
successor-edge rows to a later worker while only adding an eraser to
`UnboundedExteriorFrontierCycleRows`.  Missing exterior-boundary premises are
the next producer subtasks and must be proved from
`FinitePlanarOuterComponentInputs C`.

2026-05-21 p correction: the live S2 handoff is now the actual
exterior-sector producer recorded at the top of `../TASK.md`.  The topology
no-compact-connected-crossing source remains useful support, but the direct
W32 consumer below does not need another topology composer once the actual
producer is proved:

```text
forall C inputs,
    exists B,
      exact unbounded-frontier/cycle-vertex equivalence for B
      + Nonempty (ActualExteriorSectorInputSourceRows inputs B)
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_actualExteriorSectorInputSourceRows
```

Live local producer theorem:

```lean
theorem actualExteriorSectorInputSourceRows_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

First live intermediate producer theorem:

```lean
theorem faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
      forall k : Fin rows.orbit.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C rows.orbit.boundary k
```

This is the source-level exterior face-orbit theorem.  It should be proved
from the Csizmadia-style rotating seed/face-successor construction and then
erased to `actualExteriorSectorInputSourceRows_of_inputs`.

Checked support composers:

```text
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
S2CarrierLocalSource.finitePlanarStraightLineOuterComponentTheorem_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
S2CarrierLocalSource.unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_continuousKSide_carrierCutFieldwise_20260521j10
S2CarrierLocalSource.finitePlanarStraightLineOuterComponentTheorem_of_continuousKSide_carrierCutFieldwise_20260521j10
S2CarrierLocalSource.unboundedExteriorFrontierCycleRowsFamily_of_continuousKSide_carrierCutFieldwise_20260521j10
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_boundaryVertexExteriorSectorRows_20260521k2
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
S2CarrierLocalSource.finitePlanarStraightLineOuterComponentTheorem_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
S2CarrierLocalSource.unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows
S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_family_20260521j16_of_actualExteriorSectorInputSourceRows
S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows
S2CarrierCutSource.S2_agent_carrier_cut_fieldwise_source_family_20260521j17_of_boundaryVertexExteriorSectorRows
ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_crossingSubcontinuumPointsBetween
ExteriorComponentTopology.planarContinuumUnboundedComplementFrontierPreconnected_of_crossingSubcontinuumPointsBetween
```

The local side is the actual exterior unit-distance boundary cycle with
same-boundary exterior-sector rows:

```text
exists B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C,
  (forall v,
    (canonicalGraph C).point v ∈
      frontier (unboundedExteriorComponentRows C inputs).exterior <->
      Exists fun k : Fin B.length => B.vertex k = v) /\
  forall k : Fin B.length,
    BoundaryVertexExteriorSectorRowsAt inputs B k
```

The j16/j17, k2, k6m/k9, carrier-cut, and g1/g2/g3 raw-orbit routes are
support for proving or consuming this same producer.  They are not displayed
live routes unless the top `Current S2 Active Workboard` promotes them again.

Historical 2026-05-21 local-leaf support: the following W32 route avoids the
over-strong selected-head outgoing-list no-between leaf, but it is support for
older finite-drawing/carrier work rather than the live p producer route:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
  + forall C inputs a, UnboundedFrontierCarrierNeighborPairAt inputs a
  + S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_neighborPairRows_20260521
```

The same preferred handoff is checked with the local leaf written directly as
the sharper cut-partition source:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
  + forall C inputs, UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
  + S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_cutPartitionInputSource_20260521
```

The older route through
`UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows` or
`GraphVertexGeometricOutgoingListNoBetweenRows` remains compatibility support.
Do not treat it as the live source leaf unless it is explicitly reformulated
with a cyclic exterior-sector orientation that does not exclude legal interior
unit chords.  The local S2 source is the actual exterior-boundary carrier
degree-two statement: every unbounded-frontier vertex has exactly two actual
unbounded-frontier carrier neighbours.

2026-05-21 carrier nonemptiness/no-isolated support:

```text
FinitePlanarOuterComponentInputs C
  -> nontrivial_vertices_of_finitePlanarOuterComponentInputs
  -> exists_unitDistanceSimpleGraph_adjacent_of_finitePlanarOuterComponentInputs
  -> exists_canonicalGraph_adjacent_of_finitePlanarOuterComponentInputs

FinitePlanarOuterComponentInputs C
  -> unboundedExterior_frontier seed
  -> unboundedFrontierCarrier_nonempty
  -> unboundedFrontierCarrierGraph_connected_of_adjClosed_topologyRows_noAuxNonempty

FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs
  -> exists_unboundedFrontierCarrierGraph_adj_of_frontierVertexIncidentSource
  -> unboundedFrontierCarrierGraph_neighborFinset_nonempty_of_frontierVertexIncidentSource
  -> unboundedFrontierCarrierGraph_neighborFinset_card_pos_of_frontierVertexIncidentSource
```

These are support facts, not replacements for the live local leaf.  The live
leaf remains selected exterior-boundary incident edges plus the sharp
third-neighbour cut-partition source.

2026-05-21 punctured-frontier incident-edge support:

```text
IsPreconnected (frontier (unboundedExteriorComponentRows C inputs).exterior)
+ forall graph-frontier vertices v, another point of that same frontier
-> punctured_vertex_frontier_of_preconnected_frontier_nontrivialAt
-> frontierVertexIncidentSource_of_frontierPreconnected_nontrivialAt
<-> frontierVertexIncidentSource_iff_frontier_nontrivialAt_of_preconnected
<- frontier_nontrivialAt_of_two_frontier_points
-> frontierVertexIncidentSource_of_frontierPreconnected_two_frontier_points
<- exists_two_frontier_points_of_unboundedFrontierEdgeSet
<- exists_two_frontier_points_of_frontier_edgeInterior
<- exists_two_frontier_points_of_two_unboundedFrontierVertices
<- exists_unboundedFrontierVertexSet_or_two_frontier_points
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_frontierPreconnected_nontrivialAt
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_nontrivialAt
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_nontrivialAt
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_points
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_points
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_selectedEdge
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_selectedEdge
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontier_edgeInterior
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_frontier_edgeInterior
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_vertices
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_vertices
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_no_frontier_vertex
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_no_frontier_vertex
-> exists_two_frontier_points_or_no_unboundedFrontierVertexSet_of_card_ne_one
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexSet_card_ne_one
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexSet_card_ne_one
-> unboundedFrontierVertexSet_card_ne_one_of_frontierVertexIncidentSource
-> unboundedFrontierEdgeSet_empty_of_unboundedFrontierVertexSet_card_eq_one
-> no_frontier_edgeInterior_of_unboundedFrontierVertexSet_card_eq_one
-> unboundedExterior_frontier_eq_singleton_of_unboundedFrontierVertexSet_card_eq_one
-> unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontier_not_singleton
-> unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_frontier_not_singleton
-> inOpenSegment_mem_frontier_drawingComplement_of_edge_mem
-> inOpenSegment_mem_frontier_drawingComplement_of_adj
-> exists_drawingComplement_frontier_point_ne_graph_vertex
-> exists_drawingComplement_point_not_unboundedExterior_near_of_ambient_frontier_not_unboundedExterior_frontier
-> exists_ambient_frontier_nearby_complement_outside_unboundedExterior_of_frontier_singleton
-> exists_ambient_frontier_nearby_complement_outside_unboundedExterior_of_unboundedFrontierVertexSet_card_eq_one
-> S2CarrierLocalSource.unboundedFrontierVertexSet_card_ne_one_of_actualCarrierDegreeTwo
-> S2CarrierLocalSource.frontierVertexIncidentSource_of_actualCarrierDegreeTwo
-> S2CarrierLocalSource.unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
```

This support route converts actual frontier preconnectedness plus pointwise
nontriviality into the graph-vertex selected incident-edge source.  It leaves
the pointwise nontriviality proof as genuine local topology, now with a
checked reduction from two distinct actual unbounded-frontier points.  The
open-edge branch of the canonical frontier seed gives those two points via the
selected-edge endpoint row; the non-singleton graph-frontier carrier case is
also closed under finite-drawing no-closed-separation.  The remaining seed case
is exactly the singleton graph-frontier carrier case.  A selected incident
frontier edge at that singleton would contradict the singleton cardinality by
`unboundedFrontierVertexSet_card_ne_one_of_frontierVertexIncidentSource`, so
the unique graph-frontier vertex still needs a lower accumulation/topology
proof that supplies such an edge or proves the singleton carrier impossible.
The singleton case now also has checked empty selected-edge carrier and
no-open-edge-frontier rows, and the actual unbounded exterior frontier is
identified with that singleton point.  Thus any remaining singleton
contradiction must be a point-frontier/accumulation theorem at the unique graph
vertex; equivalently, finite-drawing no-closed-separation plus the lower
statement that the actual unbounded exterior frontier is not a single graph
point closes the component-topology source rows.  The ambient drawing frontier
midpoint row now gives a distinct drawing-complement frontier point, and the
metric separation adapter shows that in the singleton actual-frontier case
arbitrarily nearby drawing-complement points lie outside the selected
unbounded exterior component; the remaining topology/cut step is to convert
that other-component boundary bumping into the singleton contradiction.  The
local carrier side also has a checked bridge: actual carrier degree two rules
out singleton graph-frontier carriers, supplies selected incident-edge rows at
actual frontier graph vertices, and, with finite-drawing no-closed-separation,
feeds component-topology rows directly.  This
is not an all-adjacent
endpoint, induced frontier graph, or final boundary-cycle route.  The ambient
drawing-complement side now has a concrete midpoint theorem: every graph
vertex has a distinct nearby whole-complement frontier point along an incident
edge.  The still-missing bridge is to lift the relevant ambient frontier point
to the unbounded component frontier, or use its bounded-component side to
derive the promised local cut/separation contradiction.

Historical checked handoff:

```text
FinitePlanarOuterComponentInputs C
-> unboundedExteriorComponentRows C inputs
-> BoundaryFreeLocalSectorGeometricAngularInputRows inputs
-> BoundaryFreeNoThirdGermSource inputs
   + UnboundedExteriorFrontierComponentTopologySourceRows inputs
   + RawOrbitIteratedFaceSuccSuccessorLocalTwoGermRowsNoOrbitSource inputs
-> S2SeededRawOrbitSource.S2_agent_raw_orbit_final_no_orientation_assembly_20260520bt
-> UnboundedExteriorFrontierCycleRows C inputs
-> finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
```

2026-05-21 r18 update: `S2CarrierLocalSource.lean` checks
`S2_r18_boundaryFreeNoThirdGermSource_of_boundaryFreeLocalSectorGeometricAngularInputRows_20260521r18`
and
`S2_r18_frontierVertexIncidentSource_of_boundaryFreeLocalSectorGeometricAngularInputRows_20260521r18`.
The exact remaining local source for both
`BoundaryFreeNoThirdGermSource inputs` and
`FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs` on this lane is
`BoundaryFreeLocalSectorGeometricAngularInputRows inputs`.

Concrete live S2 subgoals after the 2026-05-22 q41 refresh:

| Task | Owner surface | Deliverable |
|---|---|---|
| S2-A topology support | `ExteriorComponentTopology`, `S2TopologySource`, `FinitePlaneDrawing` | Prove or strictly reduce `PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing` when working on topology-dependent support branches.  Do not route through final boundary-cycle rows or finite S2 conclusions. |
| S2-B exterior face-orbit producer | `S2ExteriorBoundarySource`, `S2SeededRawOrbitSource`, owner modules for local lemmas | Prove `faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs` from `FinitePlanarOuterComponentInputs C`: construct the actual exterior face orbit, prove carrier/frontier rows, and prove genuine same-boundary angular rows. |
| S2-C actual exterior-sector producer | `S2ExteriorBoundarySource`, `ExteriorComponentTopology` | Erase S2-B to `actualExteriorSectorInputSourceRows_of_inputs`, producing the actual boundary cycle `B`, frontier equivalence, and `Nonempty (ActualExteriorSectorInputSourceRows inputs B)`. |
| S2-D final composition | `FaceBoundaryTopologySourceW32`, `S2CarrierLocalSource` | Use existing checked consumers only after S2-C is proved.  Consumer-only reducers are support, not live source tasks. |

Topology e61 update: `S2TopologySource.lean` now checks
`planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_kComponentFrontierComponent`
and `S2_agent_subcontinuum_carrier_source_20260521e61`.  Thus the
subcontinuum-carrier source is reduced to the same-`K` frontier-component
source by packaging the connected component of `frontier U` through a chosen
trace point.  The remaining topology work is to source that standard
Janiszewski/frontier-component theorem or an equivalent lower planar theorem,
not to route through final boundary cycles.

Topology h13 update: `ExteriorComponentTopology.lean` now also checks
`planarContinuumUnboundedComplementFrontierConnected_of_subcontinuumBetween`.
Together with the earlier
`planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_connected`,
the connected-frontier and pairwise subcontinuum-between source surfaces are
equivalent for compact connected planar continua.  The nonempty frontier field
comes from `planarContinuumUnboundedComplement_frontier_nonempty`; this is an
actual Lean proof, not a new source assumption.  Future S2-A topology work
should target the closed-split/Janiszewski boundary-bumping theorem below this
equivalence, not shuttle between these two surfaces.

Topology j1 update: `ExteriorComponentTopology.lean` now checks
`planarContinuumUnboundedComplementFrontierPreconnected_of_closedSeparationForcesContinuumSeparation`.
`S2CarrierLocalSource.lean` and `FaceBoundaryTopologySourceW32.lean` also have
checked consumers from
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation`
plus actual selected-carrier degree two.  The live topology leaf is therefore
the closed-frontier continuum-separation theorem, not preconnectedness itself.

Topology j7 update: `ExteriorComponentTopology.lean` now checks
`planarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation_of_janiszewskiKComponentPointsBetween`.
On the current branch, the topology source is lowered to
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`;
the other live local source remains the actual selected-carrier e32 fieldwise
cut package.

Topology/local j11 handoff: `S2CarrierLocalSource.lean` and
`FaceBoundaryTopologySourceW32.lean` now compose the lower point-level topology
source
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween`
directly with the e32 fieldwise actual-carrier cut source:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
+ forall C inputs,
    S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget
```

The checked declaration names are
`unboundedExteriorFrontierCycleRowsFamily_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11`,
`finitePlanarStraightLineOuterComponentTheorem_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11`,
and
`minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11`.
This is a strict source lowering below the continuous-side alias; the two
open leaves remain the point-level planar topology theorem and the actual
selected-carrier e32 fieldwise theorem.

The older local two-germ/geometric `faceSucc` rows remain useful below the
orbit-first proof when they prove the actual carrier-neighbour family, but
they are not the top-level live leaves by themselves.

No-orientation raw-orbit core:

```text
BoundaryFreeConnectedRawOrbitSourceRows
  -> BoundaryFreeConnectedRawOrbitSourceRows.toUnboundedExteriorCycleRows
  -> unboundedExteriorFrontierCycleRows_family_of_connectedRawOrbitSourceRows_20260520bp

BoundaryFreeNoThirdGermSource.unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbit_noOrientation
  is the final-cycle eraser to keep when working below the package level.
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

Endpoint-closure correction: do not use
`AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs` or
`AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs` as an
unconditional source target over arbitrary adjacent exterior-frontier graph
vertices.  Boundary chords make that statement false.  The safe checked theorem
is
`ExteriorComponentTopology.closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource`,
which applies only after the edge has already been selected in
`unboundedFrontierEdgeSet C inputs`.  The live source work is the selected
exterior carrier/orbit that provides those selected edges.

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
source package for S2; use the existing `ExteriorComponentTopology`,
`S2LocalTwoGermAssembly`, and `S2ExteriorBoundarySource` surfaces.

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

## Swanepoel S2 q47 Actual-Sector Spine

Checked q47 local/raw producer handoff:

```text
S2_q47_localGeometricProducerRows
  -> S2_q47_localGeometricSourceRows_of_localGeometricProducerRows
  -> S2_q46_localGeometricSourceRows

S2_q47_selectedRawRows_of_traceNoClosed_outsideAccumulation_localGeometricProducer
  names the exact q42 selected raw exterior orbit from:
    trace no-closed topology
    + outside-accumulation source
    + q47 local-geometric producer rows

S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
  on that selected raw orbit
  -> selectedRawOrbitRepeatedTailActualExteriorArcRows_of_pairwiseMinimalDeletedTailSeparation_20260522q47
  -> selectedRawOrbitCyclicSuccDeletedTailCutPartitionSource_of_actualExteriorArcRows_20260522q46
  -> S2_q47_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_traceNoClosed_outsideAccumulation_localGeometricProducer_pairwiseMinimalDeletedTailSeparation
  -> S2_q45_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
  -> S2_q47_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_localGeometricProducer_pairwiseMinimalDeletedTailSeparation
```

This is still source-facing: the live mathematical producer remains the
finite-plane exterior face-walk theorem supplying the topology trace,
outside-accumulation/frontier, local-geometric producer, and pairwise
minimal-deleted-tail separation rows from
`FinitePlanarOuterComponentInputs C`.

Checked q48 lower-source assembler:

```text
S2_q47_traceNoClosed_outsideAccumulation_sources_of_nontrivialRelativeClopen_boundaryBumpingObstruction_20260522q47
  supplies trace no-closed + outside accumulation from the nontrivial
  relative-clopen Janiszewski route and singleton boundary-bumping obstruction.

S2_q48_localGeometricProducerRows_family_of_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles
  supplies the q47 local producer from selected-edge local isolation, same-head
  geometric rows, endpoint local-radius cover rows, and selected actual-carrier
  faceSucc angle rows.

S2_q47_pairwiseMinimalDeletedTailSeparation_family_of_finiteNoOpen_vertexIncident_geometricSelection_orientation_localStrict_localAngular_cutPartitions
  supplies the q38 pairwise separation package from cut partitions on the exact
  q47 selected raw orbit.

Together these feed
S2_q48_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_janiszewskiBoundaryBumping_frontierPreconnected_boundaryBumpingObstruction_selectedLocalIsolation_geometric_endpointLocalRadius_selectedActualCarrierFaceSuccAngles_pairwiseMinimalDeletedTailSeparation
```

The local producer has additional checked lowerings:

```text
selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_actualCarrierDegreeTwo
selectedUnboundedFrontierEdgeLocalIsolationSourceRows_of_unreachableAfterDeleteInputSource

S2_q48_localGeometricProducerRows_family_of_actualCarrierDegreeTwo_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
S2_q48_localGeometricProducerRows_family_of_unreachableAfterDelete_geometricRows_endpointRadius_selectedActualCarrierFaceSuccAngles
```

Thus the live local residual is no longer the selected local-isolation wrapper
itself; it is the genuine geometric/endpoint/face-successor source rows for
the selected heads, plus an input-level proof of actual carrier degree two or
the existing unreachable-after-delete source.

Checked q50/q51/q7/q42 refresh:

```text
q42 raw faceSucc/orientation/topology/local-carrier lowerings
q7 selected-carrier/angular wrappers
q50 endpoint-radius, topology-composer, actual-arc, and punctured-accumulation support
q51 topology punctured-compression, selected-endpoint, and route-compression support
```

These are checked composers or lowerings around the already selected raw orbit.
They do not close the exterior face-orbit source and should not be promoted to
new live routes.  The remaining source leaves are:

q61/q62 checked refresh: the live conditional actual-sector surface is now the
seed-visible q61 route plus q62 compression.  The checked q62 composer
`S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_minimalDeletedTailSeparation`
exposes component topology, actual carrier neighbour cut rows, selected-head
geometric rows, selected-head endpoint rows, selected-carrier successor rows,
and minimal deleted-tail separation on the concrete q62 selected raw orbit.
The cyclic-successor versions
`S2_q62_actualExteriorSectorInputSourceRows_family_of_q61SelectedRawOrbit_cyclicSuccDeletedTailNonreachability`
and
`S2_q62_actualExteriorSectorInputSourceRows_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_cyclicSuccDeletedTailNonreachability`
show cyclic-successor nonreachability can feed actual-sector rows directly
through the q62 minimal-separation lowerer.  The selected-orbit endpoint
support route is
`S2_q62_cyclicSuccDeletedTailNonreachability_family_of_componentTopology_cutPartitionInputSource_geometricRows_selectedHeadAt_selectedCarrierRows_finiteNoClosed_endpointClosedSeparation`.
The q64 primitive bundle
`S2_q64ActualExteriorWalkPrimitiveSourceRows` packages the same-orbit local
source surface before actual-sector erasure.  The q66 pointwise bridge
`S2_q60_geometricRows_of_cutPartitionInputSource_angularNoBetweenRows`
lowers the q60/q62 selected-head geometric row to honest angular no-between
rows for the exact heads selected by the actual carrier cut source.

```text
FinitePlanarOuterComponentInputs C
  -> actual exterior face-orbit / exterior-sector source:
       faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
       actualExteriorSectorInputSourceRows_of_inputs
```

More explicitly, the live leaves are the genuine exterior face walk and
selected carrier/frontier rows, same-boundary angular or face-successor turn
rows, repeated-tail/cut rows on that same walk, and the Janiszewski/frontier
topology source needed to feed the existing trace/outside-accumulation
support.  Checked q50/q51 endpoint-radius and selected-endpoint reducers stay
support-only unless they are restricted to actual selected exterior-sector
germs.

## File-Structure Policy

- Prefer proving a paper lemma or source package in its owning existing module.
- Create a new Lean file only for a real ownership, import-boundary,
  reusable-certificate, or compile-time advantage.
- Keep obstruction/no-go modules clearly documented as obstruction routes.
- Put disposable non-Markdown logs under `proof_logs/`, not `proof_workings/`.
- `proof_workings/` is for durable Markdown proof/context documents only.
