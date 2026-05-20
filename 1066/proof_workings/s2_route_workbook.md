# S2 Route Workbook

This file records the live Swanepoel S2 proof route, failed or demoted routes,
and the immediate research/proof tactics for the next worker.  It is not a
build log and not a wave ledger.  `../TASK.md` remains the active workboard;
this file is the durable route notebook that explains how to avoid repeating
empty reducer work.

Provenance note: use only the Csizmadia boundary-walk construction idea for
S2.  Swanepoel invokes the simple boundary polygon as a standard planar-graph
fact; Csizmadia explicitly describes the constructive angular walk from a
lowest exterior seed.  That rotating ray/segment walk is useful for the S2
exterior face orbit.  The later Csizmadia `9 / 35` local deletion, block
decomposition, Case A/B, and figure-geometry machinery is not an S2 dependency
and should not be imported into the Swanepoel route.

## Update Protocol

- Update this file whenever an S2 route is proved, demoted, or shown circular.
- Record tried routes by theorem shape and reason, not by worker narrative.
- Keep immediate tasks source-level.  A task that needs a missing row must prove
  that row first or become that missing-row task.
- Do not write disposable command output here.  Disposable logs belong in
  `../proof_logs/`.

## Recent Checked Reductions

2026-05-20 compact live decomposition after subagent sweep:

The W32-facing S2 route is now decomposed into one topology leaf and one
local/geometric leaf:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

and

```text
forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs
+ selected-head GraphVertexGeometricOutgoingListNoBetweenRows
-> forall C inputs, UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
```

Together with the checked S1 no-cut family, these are exactly the inputs to
`minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520`.

2026-05-21 final S2 composition audit:

No unconditional S2 W32 theorem was added.  The no-cut input is available as

```lean
NoCutMinimalityClosureW34.noCutVertexFamily_of_refuting_bothPlusSidesCutForced
```

and has the exact `noCutRows` shape consumed by the W32 route.  The shortest
checked W32 consumer remains

```lean
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
```

with these remaining source inputs:

```lean
ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
forall {m : Nat} (C : UDConfig m)
  (inputs : JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs C),
    S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
```

Current topology reducers still require a planar source, for example
`S2_codex_current_20260520_finite_no_closed_separation_source` needs
`PlanarContinuumUnboundedComplementFrontierConnected`, and
`S2_codex_cont_20260520_finite_no_closed_separation_source` needs
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance`.
Current geometric erasers still require rows, for example
`selectedNeighborCutPartitionGeometricOrderInputSource_family_of_geometricNeighborSelectionRows`
needs the geometric-neighbour source family above, and
`S2_codex_cont_20260520_selected_neighbor_input_source_family` needs actual
selected incident-edge rows plus genuine outgoing-list no-between rows.

2026-05-20 relative-clopen hard source reduction:

New declaration:

```lean
planarJaniszewskiBoundaryBumpingRelativeClopenKSide_of_crossingSubcontinuumForcesBounded
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
```

This strictly reduces the component-witness Janiszewski relative-clopen leaf to
the lower compact-plane crossing-boundedness source already used by the
frontier/no-subcontinuum route.  It introduces no new source predicate,
arbitrary trace, carrier cycle, induced frontier graph, or synthetic enclosure.

2026-05-20 component-avoidance plus selected-input W32 consumer:

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedNeighborInput_20260520
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
+ forall C inputs, SelectedNeighborCutPartitionGeometricOrderInputSource inputs
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is the shortest checked W32 consumer currently in the tree.  It keeps
`noCutRows` explicit to avoid importing downstream W34 closure back into W32.

2026-05-20 selected-edge/geometric-order W32 consumers:

New declarations:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedIncidentEdgeRows_geometricOrderRows_20260520
minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_actualCarrierDegreeTwo_geometricOutgoingListNoBetweenRows_20260520
```

Route impact:

```text
component avoidance
+ actual selected unboundedFrontierEdgeSet incident rows
+ genuine selected-head geometric order rows
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget

component avoidance
+ actual unboundedFrontierCarrierGraph degree two
+ genuine selected-head GraphVertexGeometricOutgoingListNoBetweenRows
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

These are W32 consumers only.  They do not source component avoidance, actual
carrier degree two, selected-head geometric order, or no-cut rows.

2026-05-20 raw-orbit selected-order W32 consumer:

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedIncidentEdgeRows_rawOrbitHeadMatch_rawOrientation_20260520
```

Route impact:

```text
component avoidance
+ actual selected unboundedFrontierEdgeSet incident rows
+ selected raw-tail coverage
+ SelectedRawOrbitHeadMatchSource
+ SelectedRawOrbitOrientationRows
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This names the raw-orbit route at the W32 boundary.  The hard source leaves
remain explicit; the consumer only composes the checked reducers.

2026-05-20 selected raw-tail coverage source:

New declarations:

```lean
S2_current_selectedRawTailCoverageSourceRows_of_rawOrbitCoverage_boundaryFreeSource_20260520b
S2_current_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520b
S2_current_selectedRawTailCoverageSourceRows_family_of_connectedRawOrbitSourceRows_20260520b
S2_current_selectedRawTailCoverageSourceRows_nonempty_family_of_connectedRawOrbitSourceRows_20260520b
```

Route impact:

```text
RawOrbitCoverageSourceRows for the selected geometric raw face orbit
+ BoundaryFreeNoThirdGermSource
-> SelectedRawTailCoverageSourceRows

BoundaryFreeConnectedRawOrbitSourceRows
-> RawOrbitCoverageSourceRows via the existing connected/local-sector reducer
-> SelectedRawTailCoverageSourceRows
```

The tail-coverage field is read back through the checked edge-coverage/local
two-germ endpoint reducer over the actual `unboundedFrontierEdgeSet` carrier.
No synthetic frontier, arbitrary orbit/cycle, or induced frontier-graph
shortcut is introduced.

2026-05-20 no-subcontinuum selected-input W32 consumer:

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_selectedNeighborInput_20260520
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
+ forall C inputs, SelectedNeighborCutPartitionGeometricOrderInputSource inputs
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is a consumer for the no-subcontinuum topology leaf.  It does not source
the planar Janiszewski theorem itself.

2026-05-20 crossing-subcontinuum selected-input W32 consumer:

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuum_selectedNeighborInput_20260520
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
+ forall C inputs, SelectedNeighborCutPartitionGeometricOrderInputSource inputs
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is only a W32 consumer.  It routes through the checked
`S2_current_no_subcontinuum_source_20260520b` reducer and keeps the topology
crossing-subcontinuum theorem, selected-neighbour input source, and no-cut rows
as explicit source leaves.

2026-05-20 raw-orbit angular source from genuine faceSucc/list order:
Claim `S2-codex-cont-20260520-raw-orbit-angular-source` is checked in
`S2SeededRawOrbitSource.lean`, with a supporting generic helper in
`GeometricRotationSystem.lean`.

New declarations:

```lean
geometricUnitDistanceRotationSystem_faceSucc_eq_of_geometricAngularNeighborSelectionRow
selectedRawOrbitGeometricAngularNeighborSelectionRows_of_orientationRows
S2_codex_cont_20260520_raw_orbit_angular_source
```

Route impact:

```text
selected raw graphDartArg orientation
+ actual geometric faceSucc consecutive row
-> nonwrap branch in genuine geometricOutgoingDartList
-> GraphVertexGeometricAngularNeighborSelectionRow source
```

The selected raw-orbit angular source is now exposed through real sorted-list
nonwrap rows produced from `faceSucc`; no identity angular order, synthetic
cycle, or arbitrary carrier order is introduced.

2026-05-20 raw-orbit selected-order source:
Claim `S2-current-raw-orbit-selected-order-source-20260520a` is checked in
`S2SeededRawOrbitSource.lean`.

New declarations:

```lean
unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_selectedRawOrbitHeadMatch_rawOrientation
unboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows_of_selectedCutRows_rawOrbitHeadMatch_rawOrientation
unboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows_of_selectedRawOrbitHeadMatch_rawOrientation
selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedCutRows_rawOrbitHeadMatch_rawOrientation
S2_current_raw_orbit_selected_order_source_20260520a
S2_current_raw_orbit_selected_order_source_family_20260520a
```

Route impact:

```text
actual selected cut rows carrying unboundedFrontierEdgeSet incidences
+ SelectedRawOrbitHeadMatchSource for those selected heads
+ SelectedRawOrbitOrientationRows on the same raw orbit
-> S2_codex_cont_20260520_raw_orbit_angular_source
-> selected geometric-order/index rows for the same selected heads
-> SelectedNeighborCutPartitionGeometricOrderInputSource
```

The selected cut rows are reused verbatim, so the two frontier-edge incidences
do not drift between source families.  The geometric order comes from the
selected raw orbit's genuine `faceSucc`/`geometricOutgoingDartList` nonwrap row;
no identity angular order, synthetic row, induced frontier graph, or arbitrary
cycle is introduced.  The only remaining bridge is the honest
`SelectedRawOrbitHeadMatchSource` aligning the selected carrier heads with the
raw orbit predecessor/successor tails.

2026-05-20 selected raw head-match reduction:
Claim `S2-current-selected-raw-head-match-source-20260520b` is checked in
`S2SeededRawOrbitSource.lean`.

New declarations:

```lean
SelectedRawOrbitLeftPredHeadMatchSource
selectedRawOrbitHeadMatchSource_of_leftPredHeadMatchSource_20260520b
S2_current_selected_raw_left_pred_head_match_source_20260520b
S2_current_selected_raw_head_match_source_20260520b
S2_current_raw_orbit_selected_order_source_20260520b
S2_current_raw_orbit_selected_order_source_family_20260520b
```

Route impact:

```text
actual selected incident-edge rows
+ selected raw-tail coverage
+ one-sided left = raw predecessor alignment
-> selected cut-partition/no-cut eraser on the same selected incidences
-> SelectedRawOrbitHeadMatchSource
-> S2_current_raw_orbit_selected_order_source_20260520a
```

This strictly reduces the head-match leaf: once a selected carrier vertex is
identified as a raw tail and the selected left head is the raw predecessor tail,
the stored actual selected cut-partition row forces the selected right head to
be the raw successor tail.  The proof uses the concrete
`unboundedFrontierEdgeSet` incidences already carried by the selected rows and
the raw predecessor/successor nonbacktracking row; it does not introduce an
identity angular order, synthetic selected row, or arbitrary carrier cycle.

2026-05-21 current final W32 composer:
Claim `S2-agent-current-final-composer-20260520c` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_selectedIncidentEdgeRows_connectedRawOrbit_leftPred_geometricSuccessorNonwrap_20260520b
```

Route impact:

```text
component avoidance
+ actual selected unboundedFrontierEdgeSet incident rows
+ BoundaryFreeConnectedRawOrbitSourceRows
+ one-sided selected-left = raw predecessor head-match rows
+ selected raw geometric successor nonwrap rows
+ noCutRows
-> SelectedRawTailCoverageSourceRows via
   S2_current_selectedRawTailCoverageSourceRows_family_of_connectedRawOrbitSourceRows_20260520b
-> SelectedRawOrbitOrientationRows via
   S2_current_raw_orbit_orientation_source_family_20260520b
-> SelectedNeighborCutPartitionGeometricOrderInputSource via
   S2_current_raw_orbit_selected_order_source_family_20260520b
-> MinimalFailureExactActualTopologyFieldsTarget
```

The consumer adds no facade and does not source any positive rows internally
except through the checked 20260520b reducers.  The exact remaining leaves are:
component avoidance, selected incident-edge rows, boundary-free connected
raw-orbit rows, left-predecessor head-match rows on the selected raw-tail
package, selected raw geometric successor nonwrap rows, and S1 no-cut rows.
Focused W32 owner build passed on 2026-05-21.

2026-05-20 local selected source continuation:
Claim `S2-codex-cont-20260520-local-selected-source` is checked in
`S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
S2_codex_cont_20260520_local_selected_source
S2_codex_cont_20260520_local_sector_rows_of_selected_input_source
S2_codex_cont_20260520_local_selected_source_family
```

Route impact:

```text
SelectedNeighborCutPartitionGeometricOrderInputSource
-> selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
-> UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows

same selected rows
+ projected genuine selected-head index rows
+ local-radius incident-germ membership from finite drawing inputs
-> LocalSelectedNeighborSourceRows
-> local-sector rows and local two-germ rows
```

This keeps the selected heads tied to actual `unboundedFrontierEdgeSet`
incidences.  No all-adjacent endpoint incidence/closure, induced frontier
graph, arbitrary cycle, convex hull, identity angular order, or synthetic
enclosure is introduced.

2026-05-20 aligned hard-case K-split continuation:
Claim `S2-codex-cont-20260520-aligned-k-source` is checked in
`ExteriorComponentTopology.lean`.

New declarations:

```lean
S2_codex_cont_20260520_aligned_k_source
S2_codex_cont_20260520_finite_no_closed_separation_source
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
-> PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

The component-avoidance adapter produces the closed disjoint `K`-cover aligned
with the two nonempty frontier pieces.  No final boundary-cycle/carrier rows,
induced frontier graphs, arbitrary cycles, convex-hull shortcut, identity
angular-order shortcut, or synthetic enclosure predicate enters this route.

2026-05-20 boundary-free global no-third source projection:

New declarations:

```lean
S2_codex_main_20260520_boundaryfree_no_third_source_of_geometricSelection_incidentGermFrontierEdge
S2_codex_main_20260520_boundaryfree_no_third_source_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge
S2_codex_main_20260520_boundaryfree_no_third_source_family_of_selectedNeighborGeometricOrder_incidentGermFrontierEdge
```

Route impact:

```text
Selected actual geometric carrier neighbours
+ selected incident-germ membership in unboundedFrontierEdgeSet
-> BoundaryFreeInputSourceReduction
-> BoundaryFreeNoThirdGermSource
```

This is the global closed-germ source only after the germ's incident graph edge
is proved to be an actual selected unbounded-frontier edge.  It does not use
all-adjacent frontier endpoint classification, chord exclusion, induced
frontier graphs, arbitrary cycles, or identity angular order.

2026-05-20 successor-tail geometric source:
Claim `S2-codex-main-20260520-successor-tail-geometric-source` is checked in
`S2SeededRawOrbitSource.lean`.

Theorem-shape decomposition:

```text
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricTripleIndexNoOrbitSource
  for selectedNeighborGeometricCarrierLeft/Right
-> RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricOutgoingListNoBetweenRowsNoOrbitSource
  via genuine geometricOutgoingDartList entries i, i+1, i+2
-> RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
  for the selected-neighbour route
```

Checked theorem:

```lean
S2_codex_main_20260520_successor_tail_geometric_source_of_tripleIndex
```

The live leaf is the triple-index sorted-list row, not an identity angular
order, induced frontier graph, arbitrary cycle, or synthetic enclosure.

2026-05-20 selected edge-chain source:
Claim `S2-codex-main-20260520-edge-chain-source` is checked in
`ExteriorComponentTopology.lean`.

Theorem-shape decomposition:

```text
PlanarContinuumUnboundedComplementFrontierConnected
+ forall frontier vertices, UnboundedFrontierCarrierLocalSectorRowsAt
-> componentTopologySourceRows_of_planarContinuumConnected_localSectorRows
-> unboundedFrontierCarrierGraph_connected_of_componentTopologySourceRows
-> unboundedFrontierEdgeCarrierSegmentChainConnected_of_unboundedFrontierCarrierGraph_connected
-> UnboundedFrontierEdgeCarrierSegmentChainConnected
```

The bundled checked output is:

```lean
S2_dyn_20260520_frontier_edge_chain_from_fixed_side :
  PlanarContinuumUnboundedComplementFrontierConnected ->
  (forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a) ->
    UnboundedFrontierEdgeCarrierSegmentChainConnected inputs ∧
      UnboundedExteriorFrontierComponentTopologySourceRows inputs
```

The route stays on selected `unboundedFrontierEdgeSet` edges: local-sector rows
provide the actual frontier-edge cover, component topology connects the
concrete frontier carrier graph, and graph walks lift to overlapping selected
closed edge segments.

2026-05-20 successor-tail neighbour-row residual:
Claim `S2-codex-current-20260520-raw-face-succ-orbit-existence-source` is
checked in `S2SeededRawOrbitSource.lean`.

New declarations:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricNeighborRowsNoOrbitSource
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_of_successorTailGeometricNeighborRows
S2_codex_current_20260520_raw_face_succ_orbit_existence_source
boundaryFreeConnectedRawOrbitSourceRows_family_of_geometricSelection_incidentGermFrontierEdge_successorTailNeighborRows_20260520
S2_codex_current_20260520_raw_orbit_source_closure_of_selectedNeighborGeometricOrder_successorTailNeighborRows
```

Route impact:

```text
two real successor-tail neighbour rows in geometricOutgoingDartList
-> shared-middle index-chain equality
-> successor-tail geometric rows
-> raw faceSucc orbit closure path
```

The explicit index-chain equality is no longer a source field.  The remaining
source is the pair of genuine sorted-list neighbour rows for each selected
successor tail.

2026-05-20 W32 geometric-angular handoff:
`FaceBoundaryTopologySourceW32.lean` has the checked consumer

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_geometricAngularSelection_20260520
minimalFailureExactActualTopologyFieldsTarget_of_alignedKSplit_selectedCutPartition_geometricAngularSelection_20260520
```

Current local W32 face after the selected-head angular-order reducer:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
+ pointwise Nonempty GraphVertexGeometricAngularNeighborSelectionRow
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The second theorem inlines the current topology residual:

```text
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit
+ selected cut/geometric-angular rows
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

2026-05-20 aligned K-split topology reducer:
Claim `S2-codex-current-20260520-closed-separation-forces-continuum-source`
is checked in `ExteriorComponentTopology.lean`.

New declarations:

```lean
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit
planarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation_of_nontrivialAlignedKSplit
S2_codex_current_20260520_closed_separation_forces_continuum_source
```

Route impact:

```text
Nontrivial closed separation of the unbounded component frontier
-> aligned disjoint closed K-side cover containing the two frontier pieces
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
-> PlanarContinuumUnboundedComplementFrontierConnected
```

The remaining topology source is the aligned hard case over the original
compact connected continuum `K`; it does not use boundary-cycle or selected
carrier rows.

2026-05-20 Janiszewski closed-split claim:
Claim `S2-codex-main-20260520-janiszewski-closed-split-source` is checked in
`ExteriorComponentTopology.lean`.

New declarations:

```lean
S2_codex_main_20260520_janiszewski_closed_split_source
S2_codex_main_20260520_planar_connected_frontier_of_janiszewski_closed_split_source
```

Theorem-shape decomposition:

```text
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
-> PlanarContinuumUnboundedComplementFrontierConnected
```

This is a strict source reduction to the non-circular aligned hard-case
planar theorem.  It does not use final boundary-cycle/carrier rows, induced
frontier graphs, arbitrary cycles, synthetic enclosures, or the demoted
relative-clopen/no-subcontinuum loop.

2026-05-20 finite no-closed-separation source:
Claim `S2-codex-main-20260520-finite-no-closed-separation-source` is checked
in `ExteriorComponentTopology.lean`.

Theorem-shape decomposition:

```text
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit
-> PlanarContinuumUnboundedComplementFrontierConnected
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

Checked theorem:

```lean
S2_codex_main_20260520_finite_no_closed_separation_source
```

This keeps the finite-drawing leaf reduced to the non-circular Janiszewski
hard case while using only compactness and connectedness of `embeddedEdgeSet C`
for the specialization.

2026-05-20 exterior edge-coverage/local-sector reducer:
Claim `S2-codex-current-20260520-boundary-edge-coverage-local-sector-source`
is checked in `S2ExteriorBoundarySource.lean`.

New declarations:

```lean
S2_codex_current_20260520_rawOrbit_edgeCoverage_of_localSectorRows_carrierConnected
S2_codex_current_20260520_selected_edge_chain_connectivity_leaf_of_localSectorRows_carrierConnected
S2_componentTopologySourceRows_of_rawFaceSuccOrbit_dartFrontier_localSectorRows_carrierConnected
```

Route impact:

```text
RawFaceSuccOrbit O
+ raw dart open-segment frontier for O
+ pointwise UnboundedFrontierCarrierLocalSectorRowsAt
+ connectedness of the actual unboundedFrontierCarrierGraph
-> selected unboundedFrontierEdgeSet coverage
-> selected edge-chain connectivity / component topology source rows
```

This removes standalone selected `edge_coverage` as a source field while
preserving actual `unboundedFrontierEdgeSet` edge honesty.

2026-05-20 boundary-free local/no-third-germ and selected-head angular final reducers:

New declarations:

```lean
S2_codex_current_20260520_boundaryfree_local_no_third_germ_source
S2_codex_current_20260520_boundaryfree_local_no_third_germ_source_family
graphVertexGeometricOutgoingListNoBetweenRows_of_graphVertexAngularNoBetweenRows
graphVertexAngularNoBetweenRows_iff_geometricOutgoingListNoBetweenRows
graphVertexAngularNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
graphVertexGeometricOutgoingListNoBetweenRows_iff_nonempty_geometricAngularNeighborSelectionRow
S2_codex_current_20260520_selected_head_angular_order_final_source
```

Route impact:

```text
LocalSelectedIncidentEdgePairSourceRows
-> boundary-free local/no-third-germ source

Nonempty (GraphVertexGeometricAngularNeighborSelectionRow C center left right)
-> GraphVertexAngularNoBetweenRows C center left right
-> GraphVertexGeometricOutgoingListNoBetweenRows C center left right
```

The remaining geometric source is now the genuine nonwrap adjacent-row source
inside the actual sorted `geometricOutgoingDartList`, not an identity-order or
cycle shortcut.

2026-05-20 connected raw-orbit face-dart carrier reduction:
Claim `S2-codex-main-20260520-raw-face-orbit-source` is checked in
`S2SeededRawOrbitSource.lean`.

New declarations:

```lean
S2_codex_main_20260520_face_dart_orbit_carrier_source_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation
S2_codex_main_20260520_face_dart_orbit_carrier_source_of_connectedRawOrbitSourceRows_selectedCutPartitions_geometricSuccessorNonwrap
S2_codex_main_20260520_face_dart_orbit_carrier_source_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_geometricSuccessorNonwrap
```

These strictly reduce the raw inputs consumed by
`S2_codex_current_20260520_face_dart_orbit_carrier_source_of_rawOrbit_localSectorRows`.
The selected raw orbit, local-sector rows, carrier connectedness, and raw dart
open-segment frontier row are extracted from
`BoundaryFreeConnectedRawOrbitSourceRows`; the compact exposed residual is now
cut partitions for repeated tails on that same selected raw orbit plus genuine
nonwrap rows in the actual sorted outgoing geometric lists.  No arbitrary
cycle, induced frontier graph, convex hull, synthetic enclosure, or identity
angular-order row is used.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" -e "\bconstant\b" -e "\bunsafe\b" -e "\bopaque\b" -e "#check" -e "#print" -e "#eval" -e "implemented_by" -e "native_decide" -e "trustCompiler" -e "ofReduceBool" ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

The targeted check and module build passed with existing lint warnings only;
the focused forbidden-token scan returned no matches.

2026-05-20 current pruning pass, actual carrier degree-two and same-boundary angular rows:

Two completed worker reductions were pruned and folded back into the live S2
route.

New declarations:

```lean
S2_codex_current_20260520_actual_carrier_degree_two_final_source
S2_codex_current_20260520_actual_carrier_degree_two_source_of_final_source
boundaryVertexAngularNoBetweenRows_iff_boundaryVertexGeometricRotationOrderRow
S2_codex_current_20260520_same_boundary_angular_geometric_order_source_iff
S2_codex_current_20260520_same_boundary_angular_no_between_source
```

Route impact:

```text
Boundary-free two-selected-edge/no-third-germ family
-> actual carrier degree two
-> LocalSelectedIncidentEdgePairSourceRows

BoundaryVertexGeometricRotationOrderRow
<-> BoundaryVertexAngularNoBetweenRows
```

The first branch keeps actual `unboundedFrontierEdgeSet` honesty and does not
use the induced frontier graph.  The second branch ties same-boundary angular
no-between rows to genuine `geometricOutgoingDartList` / `graphDartArg`
rotation-order rows.  Residuals remain source-level: the boundary-free
no-third-germ family and topology-owned local exterior sector rows.

2026-05-20 planar connected frontier strict source reducer:
Claim `S2-codex-main-20260520-planar-connected-frontier-theorem` is checked in
`ExteriorComponentTopology.lean`.

New declarations:

```lean
planarContinuumUnboundedComplementFrontierConnected_of_closedSeparationForcesContinuumSeparation
S2_codex_main_20260520_planar_connected_frontier_theorem
```

Route:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
-> PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
-> PlanarContinuumUnboundedComplementFrontierConnected
```

This is the sharpest checked non-circular reducer found for the connected
frontier theorem in the current local/mathlib surface.  The remaining source is
the genuine Janiszewski-style planar theorem that any closed split of the
unbounded component frontier forces a closed split of the original compact
continuum `K`; connectedness of `K` then rules out the split.  The route does
not use final boundary-cycle/carrier rows, selected carrier data, or the
demoted crossing/no-subcontinuum/relative-clopen cycle.

2026-05-20 selected-head outgoing-list pointwise source:
Claim `S2-codex-main-20260520-selected-head-outgoing-list-source` is reduced
in `S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
unboundedFrontierCarrierSelectedNeighborGraphVertexGeometricOutgoingListNoBetweenRows_of_geometricOrderRows
S2_codex_main_20260520_selected_head_outgoing_list_source
S2_codex_main_20260520_selected_head_outgoing_list_source_of_selectedNeighborGeometricOrderSourceRows
```

These prove the reusable pointwise
`GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows` for
the actual selected carrier heads from the existing genuine selected
geometric-order rows.  The proof projects each selected
`GraphVertexGeometricAngularNeighborSelectionRow` through the real sorted
`geometricOutgoingDartList` no-between eraser; it does not use identity
angular order, an arbitrary carrier cycle, induced frontier graph, or
endpoint-only shortcut.  Residual: this reduces the pointwise
outgoing-list/no-between source to the already live selected geometric-order
row; it does not by itself prove the independent successor-tail strict-order
source still needed by the raw `faceSucc` lane.

Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`
passed.  Final owner-file verification also passed for
`GeometricRotationSystem.lean` and `S2SeededRawOrbitSource.lean`; the latter
needed a stale call-shape cleanup removing a duplicated explicit `inputs`
argument at
`S2_codex_main_20260520_face_dart_orbit_carrier_source_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation`.
The focused forbidden-token scan over the three owner Lean files returned no
matches, and
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource`
passed with pre-existing style warnings only.

2026-05-20 planar subcontinuum-between connected source:
Claim `S2-codex-main-20260520-planar-subcontinuum-connected-source` is checked
in `ExteriorComponentTopology.lean`.

New declaration:

```lean
S2_codex_main_20260520_planar_subcontinuum_connected_source
```

Route:

```text
PlanarContinuumUnboundedComplementFrontierConnected
-> PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
```

The proof uses the existing local theorem
`planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_connected`:
for two points of the selected unbounded component frontier, take the whole
frontier as the compact connected subcontinuum.  Frontier compactness is
supplied by `planarContinuumUnboundedComplement_frontier_compact`; connectedness
is exactly the non-circular compact-connected planar theorem
`PlanarContinuumUnboundedComplementFrontierConnected`.  This does not use final
boundary-cycle/carrier rows or the demoted crossing/no-subcontinuum/
relative-clopen loop.

2026-05-20 raw-orbit and selected-input decomposition refresh:

The current decomposition has two independent source branches plus S1 no-cut:

```text
Topology:
  PlanarContinuumUnboundedComplementFrontierConnected
  -> PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
  -> FiniteDrawingUnboundedComplementFrontierPreconnected
  -> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation

Local/geometric:
  actual carrier degree two
  + selected-head GraphVertexGeometricOutgoingListNoBetweenRows
  -> SelectedNeighborCutPartitionGeometricOrderInputSource

Boundary/orbit:
  raw exterior face-successor orbit
  + local-sector rows
  + carrier connectedness
  + raw dart open-segment frontier
  + repeated-tail separation
  + raw orientation
  -> FaceDartOrbitExteriorCarrierRows
```

New checked local reductions:

```lean
S2_codex_current_20260520_boundary_incident_completeness_source
S2_codex_current_20260520_actualBoundary_geometricOrder_incident_source_of_rawOrbit_localSectorRows
S2_codex_current_20260520_face_dart_orbit_carrier_source_of_rawOrbit_localSectorRows
S2_codex_current_20260520_successor_tail_triple_index_source
S2_codex_current_20260520_selected_input_from_degree_order
minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_selectedNeighborInput_20260520
```

These do not close S2 by themselves.  They remove bookkeeping below the
boundary/orbit and selected-input branches: incident completeness is now a
local-sector consequence on the same boundary, the face-dart carrier package
can be read from raw-orbit rows, and the compact selected-neighbour input can
be read from actual carrier two-regularity plus genuine selected-head
outgoing-list no-between rows.

2026-05-20 connected-frontier W32 handoff:
`FaceBoundaryTopologySourceW32.lean` has the checked consumer

```lean
minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_selectedNeighborInput_20260520
```

Current sharp S2 handoff:

```text
PlanarContinuumUnboundedComplementFrontierConnected
+ SelectedNeighborCutPartitionGeometricOrderInputSource
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This composes through the checked
`S2_codex_current_20260520_subcontinuum_between_source` reducer and keeps the
local residual bundled around the same selected heads.

2026-05-20 true-residual W32 handoff:
`FaceBoundaryTopologySourceW32.lean` now has the checked consumer

```lean
minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_selectedNeighborInput_20260520
```

Current compact S2 handoff:

```text
PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
+ SelectedNeighborCutPartitionGeometricOrderInputSource
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This keeps the topology residual non-circular and the local residual bundled
around the same selected heads.  It composes through the finite
frontier-preconnected source and the finite no-closed-separation selected-input
consumer.

2026-05-20 crossing-subcontinuum bounded source:
Claim `S2-codex-current-20260520-crossing-subcontinuum-bounded-source` is
checked in `ExteriorComponentTopology.lean`.

New declarations:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_frontierSubcontinuum
S2_codex_current_20260520_crossing_subcontinuum_bounded_source
```

Route:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

The reducer assumes the selected complement component is unbounded only for
contradiction, asks the new source for a compact connected subset of the same
frontier meeting both closed sides, and then splits that witness by the given
closed cover of the frontier.  This avoids the circular relative-clopen
K-side/no-subcontinuum/no-closed-separation/connected-frontier lane; the older
reducers through that lane remain compatibility plumbing only.

Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
and focused forbidden-token scan passed.

2026-05-20 crossing-bounded selected-neighbour W32 handoff:
`FaceBoundaryTopologySourceW32.lean` now has:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_selectedNeighborInput_20260520
```

This composes the current topology leaf and compact local leaf:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
+ forall C inputs, SelectedNeighborCutPartitionGeometricOrderInputSource inputs
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The topology side goes through
`S2_codex_current_20260520_nontrivial_relative_clopen_side_leaf`, then the
finite-drawing nontrivial-relative-clopen and no-closed-separation reducers.
The local side goes through the checked finite selected-neighbour input W32
consumer.

2026-05-20 finite selected-neighbour input W32 handoff:
`FaceBoundaryTopologySourceW32.lean` now has the checked consumer

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedNeighborInput_20260520
```

This is the compact current S2 handoff:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ SelectedNeighborCutPartitionGeometricOrderInputSource
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The local source is bundled: each pointwise row carries the two actual
selected frontier incidences, the third-neighbour cut residual, and the
genuine adjacent sorted-list indices for those same selected heads.  The
wrapper erases that bundle to selected cut rows and pointwise angular
no-between rows through already checked `S2LocalTwoGermAssembly` projections.

2026-05-20 actual carrier degree-two source wrapper:
Claim `S2-codex-current-20260520-actual-carrier-degree-two-source` is checked
in `S2LocalTwoGermAssembly.lean`.

New declaration:

```lean
S2_codex_current_20260520_actual_carrier_degree_two_source
```

It feeds the honest actual-carrier two-regularity row

```lean
forall a,
  ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2
```

directly into `LocalSelectedIncidentEdgePairSourceRows inputs` via
`localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two`.
This is not a source closure of two-regularity; the live source remains the
actual degree-two theorem for the selected `unboundedFrontierEdgeSet` carrier.

2026-05-20 finite frontier preconnected acyclic source:
Claim `S2-codex-current-20260520-finite-frontier-preconnected-acyclic-source`
is checked in `ExteriorComponentTopology.lean`.

New declaration:

```lean
S2_codex_current_20260520_finite_frontier_preconnected_acyclic_source
```

It reduces the finite embedded-drawing frontier-preconnectedness residual to
the pairwise planar-continuum subcontinuum-between source:

```lean
PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
-> FiniteDrawingUnboundedComplementFrontierPreconnected
```

This is the non-circular route for the current finite topology leaf.  It uses
only the existing pairwise-connected-subset criterion for preconnectedness and
the finite drawing facts that `embeddedEdgeSet C` is compact and connected.

Demotion: do not count the crossing/relative-clopen loop as source progress:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

Those adapters are useful compatibility plumbing, but as a chain they are
circular and should not be cited as the proof route for either
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation` or
`FiniteDrawingUnboundedComplementFrontierPreconnected`.

2026-05-20 selected strict-order current eraser:
Claim `S2-codex-current-20260520-selected-strict-order-source-leaf` is
checked in `S2SeededRawOrbitSource.lean`.

New declarations:

```lean
rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_successorTailOutgoingListNoBetweenRows
rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_geometricSelectionInputSource_successorTailOutgoingListNoBetweenRows_20260520
rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_selectedNeighborGeometricOrder_successorTailOutgoingListNoBetweenRows_20260520
S2_codex_current_20260520_selected_strict_order_source_leaf
```

The row is an honest sorted-list eraser: selected successor-tail
outgoing-list no-between rows project to the strict `faceSucc` angular-order
inequalities.  Because the previous checked outgoing-list row also reduces to
strict order, this pair is an equivalence of local angular packages, not a
closure of the actual angular source.  The next source task remains to inhabit
the genuine selected sorted-list / geometric-order index rows for the selected
carrier heads.

2026-05-20 selected-head angular source current leaf:
Claim `S2-codex-current-20260520-selected-head-angular-source-leaf` is
checked in `S2LocalTwoGermAssembly.lean` and `GeometricRotationSystem.lean`.

Key declarations:

```lean
unboundedFrontierCarrierSelectedNeighborGraphVertexAngularNoBetweenRows_of_geometricOrderRows
S2_worker_20260520_selected_head_angular_no_between_of_indexRows
```

For any selected cut-partition source, the primitive genuine sorted-list
residual

```lean
UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows selectedRows
```

now supplies the pointwise selected-head angular source required by the W32
selected-cut/angular route:

```lean
forall a,
  GeometricRotationSystem.GraphVertexAngularNoBetweenRows
    C a.1 (selectedRows.selectedNeighborRows a).left
      (selectedRows.selectedNeighborRows a).right
```

The reduction packages each index row as a
`GraphVertexGeometricAngularNeighborSelectionRow` over the real sorted
`GeometricRotationSystem.geometricOutgoingDartList`, then erases it to
`GraphVertexAngularNoBetweenRows`.  It does not use identity angular order,
induced frontier graphs, arbitrary cycles, all-adjacent endpoint shortcuts, or
synthetic enclosure rows.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.GeometricRotationSystem
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
```

2026-05-20 selected angular/index current leaf:
Claim `S2-codex-current-20260520-selected-angular-index-source` is checked in
`S2LocalTwoGermAssembly.lean`.

New declaration:

```lean
S2_codex_current_20260520_selected_angular_index_source
```

It proves the selected-edge-route index family

```lean
forall C inputs,
  UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
    (selected rows derived from selectedEdgeRows C inputs)
```

from the matching route-selected
`GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows` rows.
The selected heads remain those produced by the live
`LocalSelectedIncidentEdgePairSourceRows` route; the order input is the genuine
sorted `GeometricRotationSystem.geometricOutgoingDartList` no-between row,
erased through the checked graph-vertex geometric-order/index reducers.  No
identity angular order, final boundary-cycle shortcut, induced frontier graph,
arbitrary cycle, all-adjacent endpoint shortcut, or synthetic enclosure is used.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.GeometricRotationSystem
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" -e "\bconstant\b" -e "\bunsafe\b" -e "\bopaque\b" -e "#check" -e "#print" -e "#eval" -e "implemented_by" -e "native_decide" -e "trustCompiler" -e "ofReduceBool" ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean
```

The module builds completed with pre-existing style warnings only, and the
focused forbidden-token scan returned no matches.

2026-05-20 finite selected-cut/angular W32 handoff:
Claim `S2-codex-current-20260520-w32-selected-cut-angular-integration` is
checked in `FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedCutPartition_angularNoBetween_20260520
```

This is the current compact W32 handoff:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
+ matching selected-head GraphVertexAngularNoBetweenRows
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

It uses the checked compact eraser
`S2_codex_current_20260520_compact_geometric_neighbor_source_leaf` and does
not add a facade layer.

2026-05-20 selected cut-partition current leaf:
Claim `S2-codex-current-20260520-selected-cut-partition-source-leaf` is checked
in `S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
S2_codex_current_20260520_selected_cut_partition_source_leaf
S2_codex_current_20260520_selected_cut_partition_source_leaf_family
```

The selected cut-partition source now reduces to the honest selected-edge
local source:

```text
LocalSelectedIncidentEdgePairSourceRows inputs
-> UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs
```

The route goes through the existing selected-incident-edge and cut-partition
erasers; it does not use induced frontier graphs, arbitrary cycles, or
all-adjacent endpoint shortcuts.

2026-05-20 nontrivial relative-clopen side current leaf:
Claim `S2-codex-current-20260520-nontrivial-relative-clopen-side-leaf` is
checked in `ExteriorComponentTopology.lean`.

New declarations:

```lean
planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_crossingBounded
S2_codex_current_20260520_nontrivial_relative_clopen_side_leaf
```

The nontrivial x-indexed relative-clopen side source now reduces to the
crossing-subcontinuum boundedness source:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
```

This uses the compact-Hausdorff separator locally plus the unbounded-component
hypothesis, and does not assume the forbidden Janiszewski relative-clopen
theorem or a no-subcontinuum source row.

2026-05-20 selected successor-tail outgoing-list current leaf:
Claim `S2-codex-current-20260520-selected-successor-tail-outgoing-list-leaf`
is checked in `S2SeededRawOrbitSource.lean`.

New declarations:

```lean
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricOutgoingListNoBetweenRowsNoOrbitSource_of_noBetweenRows
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricOutgoingListNoBetweenRowsNoOrbitSource_of_carrierNoBetweenRows_strictOrder
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricOutgoingListNoBetweenRowsNoOrbitSource_of_geometricSelectionInputSource_strictOrder
S2_codex_current_20260520_selected_successor_tail_outgoing_list_leaf
```

The successor-tail outgoing-list source for the selected geometric carrier
heads is strictly reduced to the selected successor-head strict angular-order
row:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
```

The carrier sector comes from the bundled selected-neighbour geometric order
row and is split around the selected `faceSucc` head; each split angular
no-between row is then reified through the genuine sorted
`geometricOutgoingDartList`.  No identity cyclic-order row, arbitrary carrier
cycle, induced frontier graph, endpoint-only shortcut, or all-adjacent shortcut
is used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.GeometricRotationSystem
```

2026-05-20 selected-edge chain connectivity current leaf:
Claim `S2-codex-current-20260520-selected-edge-chain-connectivity-leaf` is
checked in `S2ExteriorBoundarySource.lean`.

New declarations:

```lean
unboundedFrontierSelectedEdgeEndpointRelated_symm
unboundedFrontierSelectedEdgeEndpointRelated_of_eq_or_symm
unboundedFrontierSelectedEdgeEndpointRelated_rawOrbit_selected_of_eq_or_symm
rawFaceSuccOrbitSelectedFrontierEdge_endpointRelated_succ
unboundedFrontierSelectedEdgeEndpointChainConnected_of_rawFaceSuccOrbit_edges
S2_codex_current_20260520_selected_edge_endpoint_chain_connectivity_leaf
S2_codex_current_20260520_selected_edge_chain_connectivity_leaf
```

The selected endpoint-chain row and the closed-segment carrier-chain row now
reduce to the same raw face-successor edge-coverage source:

```lean
forall e : {e : PlanarInterface.Edge n //
    e ∈ unboundedFrontierEdgeSet C inputs},
  Exists fun k : Fin O.period =>
    e.1 =
        ((O.dart k).tail,
          (O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail) ∨
      e.1 =
        ((O.dart (PlanarInterface.cyclicSucc O.period_pos k)).tail,
          (O.dart k).tail)
```

The raw consecutive edges are first proved to be actual
`unboundedFrontierEdgeSet` edges from the raw dart-edge frontier row.  The
endpoint-chain proof walks through the selected raw orbit edges by shared raw
successor tails and attaches arbitrary selected frontier edges using the
coverage row.  No induced frontier graph, arbitrary cycle, convex hull,
identity angular-order row, all-adjacent endpoint shortcut, or final S2 cycle
row is used.

2026-05-20 Janiszewski relative-clopen K-side current leaf:
Claim `S2-codex-current-20260520-relative-clopen-k-side-leaf` is checked in
`ExteriorComponentTopology.lean`.

New declaration:

```lean
S2_codex_current_20260520_relative_clopen_k_side_leaf
```

It reduces the component-witness Janiszewski/boundary-bumping relative-clopen
`K`-side residual to the x-indexed planar-continuum nontrivial relative-clopen
forcing row:

```lean
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
```

The proof only opens the witness
`U = connectedComponentIn Kᶜ x` and calls
`janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide`; it does not use
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction`.

2026-05-20 finite no-closed final leaf:
Claim `S2-codex-current-20260520-finite-no-closed-final-leaf` is checked in
`ExteriorComponentTopology.lean`.

New declaration:

```lean
S2_codex_current_20260520_finite_no_closed_final_leaf
```

The current finite no-closed-separation premise is strictly reduced to the
finite-drawing frontier-preconnectedness row:

```lean
FiniteDrawingUnboundedComplementFrontierPreconnected
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

This uses only the existing drawing-level closed-piece criterion
`finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected`.
It does not introduce arbitrary trace Janiszewski assumptions, induced
frontier graphs, synthetic enclosures, or boundary-cycle facade rows.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 Janiszewski component-avoidance current leaf:
Claim `S2-codex-current-20260520-janiszewski-component-avoidance-leaf` is
checked in `ExteriorComponentTopology.lean`.

New declarations:

```lean
planarJaniszewskiBoundaryBumpingComponentAvoidance_of_crossingSubcontinuumForcesBounded
S2_codex_current_20260520_janiszewski_component_avoidance_leaf
```

The component-avoidance source is strictly reduced to the existing
x-indexed crossing-subcontinuum boundedness source:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

The checked proof takes the image in the plane of the relative component in
`K` of a `B` point.  If that component contained an `A` point, this image is a
compact connected subset of `K` meeting both closed frontier sides, so the
boundedness source contradicts the unboundedness of the selected complement
component.  No new source predicate, W facade, final-cycle row, induced
frontier graph, or synthetic enclosure row is introduced.

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 seed-visible raw orbit actual-boundary handoff:
`S2SeededRawOrbitSource.lean` now has:

```lean
SelectedSeededRawFaceSuccOrbitSourceRows.toActualBoundaryCycleFrontierEquivalenceRows_of_cutRows
```

It sends the selected seed/raw face-successor orbit package directly to the
actual boundary-cycle/frontier-equivalence rows consumed by the current
face-dart carrier route.  The residual is exactly the repeated-tail cut row
for the same selected raw orbit:

```lean
forall {i j : Fin rows.O.period},
  i ≠ j ->
  (rows.O.dart i).tail = (rows.O.dart j).tail ->
    RawFaceSuccOrbitRepeatedTailExteriorCutRows
      (inputs := inputs) rows.O i j
```

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 selected-head geometric order reduced to raw orbit sources:
`S2SeededRawOrbitSource.lean` now has:

```lean
S2_codex_current_20260520_selected_head_geometric_order_source
S2_codex_current_20260520_selected_head_geometric_outgoing_list_no_between_source
S2_codex_current_20260520_selected_head_nonwrap_leaf
```

The selected-head geometric-order/no-between branch is reduced to the exact
selected raw-orbit source premises:

```lean
S2_codex_current_20260520_selectedEdgePairRoute_rawOrbitHeadMatchSource
SelectedRawOrbitGeometricSuccessorNonwrapRows
```

These are tied to the actual selected carrier heads and use the real sorted
`geometricOutgoingDartList`.

The later `S2_codex_current_20260520_selected_head_nonwrap_leaf` packages the
same handoff in the still smaller source form:

```lean
SelectedRawOrbitHeadMatchSource selectedRows rawRows
SelectedRawOrbitOrientationRows rawRows
```

It derives nonwrap rows internally through
`selectedRawOrbitGeometricSuccessorNonwrapRows_of_orientationRows`.

2026-05-20 planar connected frontier reduced to no-closed separation:
`ExteriorComponentTopology.lean` now has:

```lean
S2_codex_current_20260520_planar_connected_frontier_source
```

It reduces:

```text
PlanarContinuumUnboundedComplementFrontierConnected
-> PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
```

The topology chain for the current finite route is therefore:

```text
PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
-> PlanarContinuumUnboundedComplementFrontierConnected
-> FiniteDrawingUnboundedComplementFrontierPreconnected
-> MinimalFailureExactActualTopologyFieldsTarget
```

2026-05-20 actual-boundary face-dart carrier reducer:
`ExteriorComponentTopology.lean` now has the stricter face-dart carrier source
reducers:

```lean
faceDartOrbitExteriorCarrierRows_of_actualBoundaryCycleFrontierEquivalenceRows_faceSuccRows_complete
S2_codex_current_20260520_actual_boundary_cycle_source
faceDartOrbitExteriorCarrierRows_of_rawFaceSuccOrbitBoundaryRows_complete
```

They reduce `FaceDartOrbitExteriorCarrierRows C inputs` to actual
boundary/frontier rows, matching face-successor rows, and
`BoundaryCycleIncidentFrontierEdgeCompleteness` for the same boundary.  The
raw-orbit specialization supplies the matching
`UnitDistanceCycleFaceSuccRows` from the raw orbit, so its residual is the
actual boundary/frontier row plus same-boundary incident-edge completeness.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean
```

2026-05-20 selected raw-tail face-dart carrier reducer:
`S2SeededRawOrbitSource.lean` now projects the selected raw-tail package
directly to the honest carrier target:

```lean
SelectedRawTailCoverageSourceRows.rawBoundary
SelectedRawTailCoverageSourceRows.rawBoundary_period_eq
SelectedRawTailCoverageSourceRows.rawBoundary_tail_eq
SelectedRawTailCoverageSourceRows.toFaceDartOrbitExteriorCarrierRows_complete
SelectedRawTailCoverageSourceRows.toFaceDartOrbitExteriorCarrierRows_of_deletedTailWitnesses_complete
SelectedRawTailCoverageSourceRows.toFaceDartOrbitExteriorCarrierRows_of_cutPartitions_complete
```

This reduces `FaceDartOrbitExteriorCarrierRows C inputs` from the actual
selected raw face-successor orbit rows.  The extracted boundary is produced by
raw-tail injectivity from repeated-tail/no-cut rows; frontier vertex coverage
and consecutive edge-frontier rows come from `SelectedRawTailCoverageSourceRows`;
the remaining carrier-local residual is exactly
`BoundaryCycleIncidentFrontierEdgeCompleteness` for that same extracted raw
boundary.  No final cycle rows, induced frontier graph shortcut, arbitrary
cycle, or synthetic enclosure is used.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 finite preconnected face-dart W32 consumer:
`FaceBoundaryTopologySourceW32.lean` now has the direct current-surface W32
consumer:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingPreconnected_faceDartOrbitCarrier_geometricOutgoingListNoBetween_20260520
```

It consumes:

```text
FiniteDrawingUnboundedComplementFrontierPreconnected
+ forall C inputs, FaceDartOrbitExteriorCarrierRows C inputs
+ selected-head geometric outgoing-list no-between rows for
  `S2_codex_current_20260520_selected_carrier_source (faceRows C inputs)`
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The topology handoff is the checked eraser
`finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_frontierPreconnected`.
Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-20 finite frontier preconnected source:
Claim `S2-codex-current-20260520-finite-frontier-preconnected-source` is checked
in `ExteriorComponentTopology.lean`.

New declaration:

```lean
S2_codex_current_20260520_finite_frontier_preconnected_source
```

The finite embedded-drawing leaf
`FiniteDrawingUnboundedComplementFrontierPreconnected` is reduced to the
standard selected compact-connected planar theorem:

```lean
PlanarContinuumUnboundedComplementFrontierConnected
```

The checked adapter uses the actual finite drawing facts already proved for
`embeddedEdgeSet C`: `embeddedEdgeSet_compact C` and
`embeddedEdgeSet_connected_of_inputs inputs`, via
`finiteDrawingUnboundedComplementFrontierPreconnected_of_connected`.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 finite no-closed-separation source:
Claim `S2-codex-current-20260520-planar-no-closed-separation-leaf` now has an
exact finite W32-facing reducer in `ExteriorComponentTopology.lean`.

New declarations:

```lean
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_connected
S2_codex_current_20260520_finite_no_closed_separation_source
```

The finite selected-edge W32 topology premise now reduces directly as:

```text
PlanarContinuumUnboundedComplementFrontierConnected
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

This is stricter than routing through aligned-K or boundary-cycle surfaces, and
uses only `embeddedEdgeSet_compact C`, `embeddedEdgeSet_connected_of_inputs`,
and the checked closed-piece criterion.  Remaining mathematical source:

```lean
PlanarContinuumUnboundedComplementFrontierConnected
```

2026-05-20 finite nontrivial relative-clopen side reduced to finite frontier
preconnectedness:
Claim `S2-codex-current-20260520-boundary-bumping-relative-clopen` is checked
in `ExteriorComponentTopology.lean`.

New declarations:

```lean
finiteDrawingUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_frontierPreconnected
finiteDrawingUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_finiteDrawing_noClosedSeparation
S2_codex_current_20260520_boundary_bumping_relative_clopen
```

The route is:

```text
FiniteDrawingUnboundedComplementFrontierPreconnected
-> FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
```

The proof is by contradiction from the displayed nonempty closed split of the
same finite-drawing frontier; no `K`-side selection is needed in the finite
case once preconnectedness is available.  The exact remaining theorem on this
reduced finite lane is:

```lean
FiniteDrawingUnboundedComplementFrontierPreconnected
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 finite face-dart-carrier W32 consumer:
`FaceBoundaryTopologySourceW32.lean` now specializes the finite selected-edge
consumer to the honest exterior face-dart carrier package:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_faceDartOrbitCarrier_geometricOutgoingListNoBetween_20260520
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_faceDartOrbitCarrier_angularNoBetween_20260520
```

These consume either selected-head outgoing-list no-between rows or selected-head
angular no-between rows for the selected carrier heads:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs, FaceDartOrbitExteriorCarrierRows C inputs
+ matching selected-head geometric outgoing-list no-between rows, or
  selected-head angular no-between rows, for
  `S2_codex_current_20260520_selected_carrier_source (faceRows C inputs)`
+ S1 no-cut rows
-> MinimalFailureExactActualTopologyFieldsTarget
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

2026-05-20 aligned K-split focus source:
Claim `S2-codex-this-thread-20260520-aligned-ksplit-source` is reduced in
`ExteriorComponentTopology.lean` to the actual finite embedded-drawing
nontrivial relative-clopen side theorem:

```lean
finiteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded_of_finiteDrawing_nontrivialRelativeClopenKSide
S2_codex_this_thread_20260520_aligned_ksplit_source
```

The checked handoff is:

```text
FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
-> FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit
-> FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded
```

This keeps the source on the actual embedded edge set and does not use the
demoted arbitrary trace Janiszewski assumptions.  The smallest exact theorem
remaining on this lane is therefore:

```lean
FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 finite no-closed separation relative-clopen reduction:
`ExteriorComponentTopology.lean` now has the finite drawing no-closed
separation route reduced further to the finite drawing nontrivial
relative-clopen split source:

```lean
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_finiteDrawing_nontrivialRelativeClopenKSide
actualFrontierNoClosedSeparation_of_alignedKSplitSource
actualFrontierNoClosedSeparation_of_finiteDrawing_alignedKSplit
actualFrontierNoClosedSeparation_of_finiteDrawing_nontrivialRelativeClopenKSide
```

Remaining topology leaf:

```lean
FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
```

This is the honest finite-drawing task: from a nonempty closed split of the
unbounded-component frontier, produce the corresponding nontrivial relative
clopen side in the finite embedded drawing.  Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 selected carrier source reduction:
`S2ExteriorBoundarySource.lean` now reduces the local selected carrier source
to the honest face-dart exterior carrier package:

```lean
localSelectedIncidentEdgePairSourceRows_of_faceDartOrbitExteriorCarrierRows
S2_codex_current_20260520_selected_carrier_source
```

The selected incident-edge rows are therefore sourced from:

```text
FaceDartOrbitExteriorCarrierRows C inputs
-> LocalSelectedIncidentEdgePairSourceRows inputs
```

This keeps the selected heads tied to actual `unboundedFrontierEdgeSet`
incidences.  The sharper actual-boundary helper reduces the same source to
`BoundaryCycleIncidentFrontierEdgeCompleteness inputs actualRows.boundary`.
Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean
```

2026-05-20 finite selected-edge W32 consumer:
`FaceBoundaryTopologySourceW32.lean` now has the direct finite-drawing
selected-edge/outgoing-list consumer:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_selectedEdgePair_geometricOutgoingListNoBetween_20260520
```

It consumes:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs
+ matching selected-head geometric outgoing-list no-between rows
+ S1 no-cut rows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This keeps the topology branch on the actual finite embedded unit-edge drawing
and keeps the local branch on selected `unboundedFrontierEdgeSet` carrier
edges.  Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-20 finite no-closed-separation boundedness reducer:
Claim `S2-codex-20260520-finite-no-closed-source-live` strictly reduced the
finite drawing topology leaf to a drawing-level boundedness contradiction
source, without using arbitrary trace assumptions or final boundary-cycle
shortcuts.

New declarations:

```lean
FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_closedSeparationForcesBounded
finiteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded_of_alignedKSplit
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_alignedKSplit
```

The immediate reducer is:

```text
FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesBounded
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

For the current checked finite drawing route, the boundedness source itself is
fed by `FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit`:
in the bounded case it is immediate; in the unbounded case the aligned
`embeddedEdgeSet C = K1 ∪ K2` split contradicts connectedness of the actual
embedded unit-edge drawing.  The remaining mathematical leaf for closing the
finite no-closed-separation source through this route is therefore the actual
finite drawing aligned K-split source, equivalently a direct proof of the new
boundedness-contradiction source.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 outgoing-list no-between reducer:
Claim `S2-codex-20260520-carrier-neighbor-outgoing-source-live` is checked in
`ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.

New declarations:

```lean
unboundedFrontierCarrierGeometricNeighborOutgoingListNoBetweenSourceRows_of_neighborPair_geometricAngularSelectionRows
unboundedFrontierCarrierGeometricNeighborOutgoingListNoBetweenSourceRows_of_geometricNeighborSelectionSourceRows
unboundedFrontierCarrierGeometricNeighborOutgoingListNoBetweenSourceRows_of_geometricSelectionInputSource
unboundedFrontierCarrierGeometricNeighborOutgoingListNoBetweenSourceRows_family_of_geometricNeighborSelectionSourceRows
```

This reduces the outgoing-list no-between source to pointwise genuine
`GraphVertexGeometricAngularNeighborSelectionRow` data for the two selected
carrier heads.  It keeps the route on sorted outgoing-dart geometry and does
not use identity cyclic-order rows.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean
```

2026-05-20 carrier degree-two reducer:
Claim `S2-codex-20260520-carrier-degree-two-live` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.

New declarations:

```lean
unboundedFrontierCarrierGraph_neighborFinset_card_two_of_unreachableAfterDeleteInputSource
unboundedFrontierCarrierGraph_neighborFinset_card_two_of_deletedNeighborLocalSeparationInputSource
```

These give the exact neighbour-finset cardinality form needed by the selected
edge-pair erasers.  The remaining carrier source is now an actual
deleted-neighbour separation package:

```text
UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource
```

or the stricter local Boolean source:

```text
UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
```

2026-05-20 finite no-closed-separation S2 route:
Claim `S2-codex-main-20260520-finite-no-closed-separation-route` is checked.
The narrow finite topology source now feeds the current compact
geometric-neighbour S2 route without detouring through the global Janiszewski
no-subcontinuum `Prop`.

New declarations:

```lean
actualFrontierPreconnected_of_finiteDrawing_noClosedSeparation
unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_localSectorRows
unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_geometricSelectionInputSource
unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricSelectionInputSource_20260520
unboundedExteriorFrontierCycleRowsFamily_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
```

The topology handoff deliberately factors through:

```lean
finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteDrawing_noClosedSeparation
actualFrontierPreconnected_of_finiteDrawing_frontierPreconnected
```

The W32 consumer now takes:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs, UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-20 current short S2 lane:
The live route is the W32 consumer

```lean
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_geometricNeighborSelectionRows_20260520
```

with source leaves:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
+ forall C inputs, UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
+ S1 noCutRows
```

The geometric-neighbour package has a checked pointwise eraser:

```lean
S2_dyn_20260520_geometric_neighbor_rows_current_source_family
```

so the local/geometric residual is exactly:

```text
forall a, UnboundedFrontierCarrierNeighborPairAt inputs a
+ forall a, GraphVertexAngularNoBetweenRows C a.1 (left a) (right a)
```

The successor-tail raw-orbit task is now pruned as a fallback-only lane.  The
next work should source the three displayed leaves; do not revive the
all-adjacent endpoint, induced-frontier-graph, arbitrary-cycle, identity-order,
synthetic-enclosure, or extra-facade routes.

2026-05-20 selected-edge-pair neighbour eraser:
`S2LocalTwoGermAssembly.lean` now has a direct selected-edge eraser:

```lean
unboundedFrontierCarrierNeighborPairRows_of_selectedIncidentEdgePairRows
S2_codex_main_20260520_selected_edge_pair_neighbor_eraser
```

It consumes `LocalSelectedIncidentEdgePairSourceRows inputs` and produces
`forall a, UnboundedFrontierCarrierNeighborPairAt inputs a` using only actual
`unboundedFrontierEdgeSet` incidences plus
`unboundedFrontierCarrierGraph_adj_iff`.  This bypasses the longer
local-radius/cut-partition route when the downstream target only needs
carrier neighbour-pair rows.  The remaining source is still to construct the
selected edge-pair rows honestly; this eraser does not assert any
all-adjacent-frontier-endpoint or induced-graph statement.

2026-05-20 component-avoidance proof-now:
Claim `S2-codex-20260520-component-avoidance-proof-now` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.  The
Janiszewski component-avoidance leaf now has a direct strict reducer from the
no-subcontinuum obstruction:

```lean
planarJaniszewskiBoundaryBumpingComponentAvoidance_of_noSubcontinuumObstruction
S2_codex_20260520_component_avoidance_proof_now
planarJaniszewskiBoundaryBumpingComponentAvoidance_iff_noSubcontinuumObstruction
```

The proof does not pass through the relative-clopen separator.  If the
relative component in `K` of a `B`-point contains an `A`-point, the image of
that component is itself the compact connected subcontinuum of `K` meeting
both closed frontier sides, contradicting the no-subcontinuum obstruction.
The current component-avoidance source is therefore demoted to the exact
remaining Janiszewski no-subcontinuum obstruction.

Verification:
`lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.

2026-05-20 crossing-topology source:
Claim `S2-codex-main-20260520-crossing-topology-source` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.  The x-indexed
crossing-subcontinuum boundedness source now has a direct reducer from the
actual Janiszewski component-avoidance surface:

```lean
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_janiszewskiComponentAvoidance
S2_codex_main_20260520_crossing_topology_source
```

The route is:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

Verification:
`lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`.

2026-05-20 shortest connected raw-orbit handoff:
The live W32 route has been shortened to the no-orientation connected
raw-orbit handoff:

```lean
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows
```

Its S2 source leaf is:

```lean
forall {n : Nat} (C : UDConfig n)
  (inputs : FinitePlanarOuterComponentInputs C),
    Nonempty (BoundaryFreeConnectedRawOrbitSourceRows inputs)
```

and the package fields are exactly:

```text
BoundaryFreeNoThirdGermSource inputs
+ (unboundedFrontierCarrierGraph C inputs).Connected
+ RawOrbitDartEdgeFrontierSource inputs
```

The repeated-tail/orientation routes remain checked fallback routes, but they
are no longer the shortest displayed S2 handoff.  Do not use all-adjacent
endpoint closure, induced frontier graphs, arbitrary carrier cycles, convex
hulls, identity angular-order rows, synthetic enclosure rows, or a new W
facade.

2026-05-20 strict-order connected raw-orbit reducer:
`S2SeededRawOrbitSource.lean` now has the selected-neighbour strict-order
source reducers:

```lean
boundaryFreeConnectedRawOrbitSourceRows_of_boundaryFreeInput_preconnected_selectedNeighborGeometricOrder_strictOrder_20260520
boundaryFreeConnectedRawOrbitSourceRows_family_of_boundaryFreeInput_preconnected_selectedNeighborGeometricOrder_strictOrder_20260520
boundaryFreeConnectedRawOrbitSourceRows_family_of_boundaryFreeInput_preconnected_selectedNeighborInput_strictOrder_20260520
```

These reduce the connected raw-orbit package to boundary-free input rows,
planar frontier preconnectedness, selected-neighbour geometric-order input
rows, and the selected `faceSucc` strict angular-order source.  Verification:
`lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.

2026-05-20 repeated-tail selected raw-orbit source:
Claim `S2-codex-main-20260520-repeated-tail-source` is checked in
`ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.  The internally
selected raw orbit now has named reducers:

```lean
selectedRawOrbitRepeatedTailCutPartitions_of_connectedRawOrbitSourceRows_repeatedTailWitnessSource_20260520
selectedRawOrbitRepeatedTailWitnessSource_of_connectedRawOrbitSourceRows_boundaryArcSource_20260520
selectedRawOrbitRepeatedTailCutPartitions_of_connectedRawOrbitSourceRows_boundaryArcSource_20260520
```

These compose the existing `S2RepeatedTailExteriorCutWitnessSource` erasers and
two-open-arc exterior source into the selected raw-orbit cut-partition row.  No
induced frontier graph, arbitrary carrier cycle, synthetic enclosure, or
endpoint shortcut is introduced.  Verification:
`lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.

2026-05-20 topology source close:
Claim `S2-codex-main-20260520-topology-source-close` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.  The
connected-frontier theorem now has direct reducers from the two honest
Janiszewski source surfaces:

```lean
planarContinuumUnboundedComplementFrontierConnected_of_janiszewskiRelativeClopenKSide
planarContinuumUnboundedComplementFrontierConnected_of_janiszewskiComponentAvoidance
```

The first routes relative-clopen through no-closed-separation; the second
routes component avoidance through the checked compact-Hausdorff
relative-clopen separator.  No new source package, W-layer, endpoint closure,
induced frontier graph, arbitrary cycle, convex-hull shortcut, or synthetic
enclosure row is introduced.  Verification:
`lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.

2026-05-20 connected-frontier source leaf:
Claim `S2-codex-main-20260520-connected-frontier-source-leaf` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.  The new theorem

```lean
S2_codex_main_20260520_connected_frontier_source_leaf
```

reduces `PlanarContinuumUnboundedComplementFrontierConnected` to
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance`
and packages the downstream composition to
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation` via the existing
finite-drawing connected-frontier adapter.  Verification:
`lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.

2026-05-20 geometric-selection input source:
Claim `S2-codex-20260520-geometric-selection-input-source` is checked in
`ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`.  The bundled source

```lean
UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs
```

now has named strict reductions from the two live actual-carrier surfaces:

```lean
S2_codex_20260520_geometric_selection_input_source_of_neighborRows_geometricOrderRows
S2_codex_20260520_geometric_selection_input_source_family_of_neighborRows_geometricOrderRows
S2_codex_20260520_geometric_selection_input_source_of_localSectorRows_geometricOrderRows
S2_codex_20260520_geometric_selection_input_source_family_of_localSectorRows_geometricOrderRows
```

The neighbour-row route consumes actual `UnboundedFrontierCarrierNeighborPairAt`
rows plus genuine non-wrap consecutive rows in
`GeometricRotationSystem.geometricOutgoingDartList`.  The local-sector route
first erases actual `UnboundedFrontierCarrierLocalSectorRowsAt` rows to the
same neighbour heads, so the selected edges remain actual
`unboundedFrontierEdgeSet` incidences.  No identity angular order, induced
frontier graph, arbitrary carrier cycle, synthetic enclosure, convex hull, or
all-adjacent endpoint shortcut is used.

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean
```

2026-05-20 local-sector source claim:
Claim `S2-codex-20260520-local-sector-source` is checked in
`ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean`.  The pointwise
source
`forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a` is strictly
reduced through actual unbounded-frontier carrier source rows:

```lean
S2_codex_20260520_local_sector_source_of_localTwoGermRows
S2_codex_20260520_local_sector_source_family_of_localTwoGermRows
S2_codex_20260520_local_sector_source_of_neighborPairRows
S2_codex_20260520_local_sector_source_family_of_neighborPairRows
S2_codex_20260520_local_sector_source_of_cutPartitionRows
S2_codex_20260520_local_sector_source_family_of_cutPartitionRows
S2_codex_20260520_local_sector_source_of_cutPartitionInputSource
S2_codex_20260520_local_sector_source
```

The family theorem reduces every `FinitePlanarOuterComponentInputs C` instance
to the same-input sharp
`UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`; the
object-level variants also expose the actual neighbor-pair and local two-germ
surfaces.  No final boundary-cycle rows, induced frontier graph shortcuts,
arbitrary cycles, identity angular-order rows, or all-adjacent endpoint closure
are used.

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean
lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 Janiszewski relative-clopen source:
Claim `S2-codex-20260520-janiszewski-relative-clopen-source` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` as
`S2_codex_20260520_janiszewski_relative_clopen_source`.  It strictly reduces
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide`
to the existing component-avoidance source
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance`
via `S2_dyn_20260520_component_avoidance_relative_clopen` and
`planarJaniszewskiBoundaryBumpingRelativeClopenKSide_of_componentAvoidance`.
This keeps the S2 topology route on the Janiszewski/component-avoidance
surface and adds no facade, final-boundary source package, induced frontier
graph, arbitrary cycle, or trace-connected compatibility assumption.

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 Janiszewski no-subcontinuum source:
Claim `S2-codex-20260520-janiszewski-nosubcontinuum-source` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.  The global
component-indexed no-subcontinuum leaf is now recorded as exactly equivalent
to the relative-clopen separator theorem:

```lean
planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_iff_relativeClopenKSide
```

For the actual finite-drawing setting, the candidate subcontinuum is no longer
the remaining source: a nonempty closed split is already impossible from the
finite/planar no-closed-separation rows:

```lean
finiteDrawingUnboundedComplementFrontierNoSubcontinuumObstruction_of_finiteDrawing_noClosedSeparation
finiteDrawingUnboundedComplementFrontierNoSubcontinuumObstruction_of_noClosedSeparation
```

Exact remaining theorem for the global source leaf:
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide`.
Exact remaining theorem for the actual finite drawing specialization:
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation` (or the stronger
existing planar source
`PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`).

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
lake env lean ErdosProblems1066/Swanepoel/FinitePlaneDrawing.lean
```

2026-05-20 current no-subcontinuum source 20260520b:
Claim `S2-current-no-subcontinuum-source-20260520b` is strictly reduced in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.

New checked bridge:

```lean
planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_crossingSubcontinuumForcesBounded
S2_current_no_subcontinuum_source_20260520b
```

Route:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
```

This uses the component witness `U = connectedComponentIn K.compl x`: any
candidate compact connected `T <= K` meeting both closed frontier sides would
force the same component `U` to be bounded, contradicting the unboundedness
hypothesis.  The exact remaining theorem shape is therefore the frontier
witness source
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum`.
No extra topology surface is introduced beyond that witness source and the
already checked boundedness bridge.

2026-05-20 selected-edge source leaf:
Claim `S2-codex-20260520-selected-edge-source` is checked in
`ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`.  The pure
`LocalSelectedIncidentEdgePairSourceRows inputs` leaf now has named strict
reducers from the honest actual unbounded-frontier carrier/local rows:

```lean
S2_codex_20260520_selected_edge_source_of_neighborPairRows
S2_codex_20260520_selected_edge_source
S2_codex_20260520_selected_edge_source_family_of_neighborPairRows
S2_codex_20260520_selected_edge_source_family_of_localSectorRows
S2_codex_20260520_selected_edge_source_of_cutPartitionRows
S2_codex_20260520_selected_edge_source_family_of_cutPartitionRows
```

The local-sector route erases through
`unboundedFrontierCarrierNeighborPairRows_of_localSectorRows`; the
cut-partition route erases through
`S2_agent_ct_local_sector_from_cutPartitionRows_20260520`.  In each case the
selected heads remain the two actual `unboundedFrontierEdgeSet` carrier
neighbours, and incident completeness comes from the actual carrier
neighbour-pair/local-sector/cut-partition rows.  No all-adjacent endpoint
closure, arbitrary adjacent frontier endpoint selection, induced frontier
graph, final boundary cycle, or identity angular-order row is used.

Verification:

```powershell
lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
```

2026-05-20 no-closed-separation source reduction:
`S2_codex_20260520_no_closed_separation_source` in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` reduces
`PlanarContinuumUnboundedComplementFrontierNoClosedSeparation` to the existing
Janiszewski/boundary-bumping relative-clopen separator theorem
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide`.
The checked chain runs through the existing nontrivial relative-clopen and
aligned K-split reducers; it introduces no W facade, final boundary cycle,
induced frontier graph, arbitrary cycle, convex-hull shortcut, synthetic
enclosure, or all-adjacent endpoint closure.

2026-05-20 direct no-closed-separation selected-edge route:
`minimalFailureExactActualTopologyFieldsTarget_of_planarNoClosedSeparation_selectedEdgePair_geometricOutgoingListNoBetween_20260520`
in `ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean` composes
the latest topology and local-sector reductions into the W32 S2 target.  It
consumes:

```lean
PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs
forall C inputs,
  S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
    (selectedEdgeRows C inputs)
S1 noCutRows
```

The cycle-row construction is through
`unboundedExteriorFrontierCycleRows_of_planarContinuumNoClosedSeparation_localSectorRows`,
with local-sector rows supplied by
`localSectorRows_of_selectedEdgePairRoute_geometricOutgoingListNoBetween_localIncident_20260520`.
This route still requires the three displayed source leaves; it does not use
all-adjacent endpoint closure, an induced frontier graph, an arbitrary cycle,
convex hull vertices, identity angular order, synthetic enclosure rows, or a
new facade.

2026-05-20 active route refresh after dynamic pruning:
The live S2 route is now the selected-edge/index handoff with three source
leaves, not an endpoint or final-cycle route:

```lean
PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction
forall C inputs, forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a
forall C inputs,
  S2_dyn_20260520_selected_head_angular_no_between_source_for_localSelectedNoThirdGermRoute
    (S2_dyn_20260520_local_selected_no_third_source (localSectorRows C inputs))
S1 noCutRows
```

These leaves feed the checked reducers:

```lean
S2_dyn_20260520_janiszewski_relative_clopen_source
S2_dyn_20260520_local_selected_no_third_source
S2_dyn_20260520_selected_head_geometric_order_source
minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_localSelectedNoThird_graphVertexGeometricOrder_20260520
```

The selected local-sector leaf has support from
`localSectorRowsFamily_of_geometricSelection_localIncident_20260520`.
The selected geometric/order leaf has support from
`geometricOutgoingDartList_no_between_of_graphVertexGeometricAngularNeighborSelectionRow`
and the selected-head route erasers.  Current active workers should source or
strictly reduce these leaves, not introduce another W-layer or any route that
uses all-adjacent endpoint closure, induced frontier graphs, arbitrary cycles,
identity angular-order rows, synthetic enclosures, or `KnownBounds` exposure.

2026-05-20 finite-drawing actual frontier source package:
`S2_agent_20260520_finite_drawing_frontier_source` in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` is checked.  It
specializes a finite-drawing no-closed-separation source for actual unbounded
complement components to the selected
`unboundedExteriorComponentRows C inputs`, producing:

```lean
UnboundedExteriorActualFrontierNoClosedSeparationSource C inputs
UnboundedExteriorActualFrontierPreconnectedSource C inputs
UnboundedExteriorActualFrontierClosedSeparationForcesAlignedKSplit C inputs
```

The carrier remains the actual `embeddedEdgeSet C`; no final boundary cycle,
induced frontier graph, arbitrary carrier/cycle, convex hull, endpoint
shortcut, identity angular order, synthetic enclosure, or new W facade is used.
The supporting checked adapters are
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation`,
`finiteDrawingUnboundedComplementFrontierAlignedKSplit_of_finiteDrawing_noClosedSeparation`,
`actualFrontierNoClosedSeparation_of_finiteDrawing_noClosedSeparation`, and
`actualFrontierAlignedKSplit_of_finiteDrawing_noClosedSeparation`.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
and
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`
passed.

2026-05-20 final route composer:
`unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520`
in `ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean` is now the
shortest checked endpoint-free cycle-row handoff for the selected-edge/index
route.  It erases selected incident-edge pair rows to selected cut-partition
rows in the S2 source owner, keeps the genuine selected index rows tied to
those exact selected heads, and avoids endpoint-only shortcuts, arbitrary
cycles, induced frontier graphs, synthetic enclosures, and `KnownBounds`.

`minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520`
in `ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean` now
consumes that cycle-row composer directly through
`minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows`.
W32 no longer repeats the selected-row reconstruction.

The remaining source leaves are exactly:

```lean
relative_side :
  PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide

selectedEdgeRows :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      LocalSelectedIncidentEdgePairSourceRows inputs

indexRows :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) (selectedEdgeRows C inputs)
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows selectedRows
```

Verification: direct targeted Lean checks passed for
`S2SeededRawOrbitSource.lean`, `FaceBoundaryTopologySourceW32.lean`, and
`S2ExteriorBoundarySource.lean`.  The attempted Lake target build is blocked
before this route by the current upstream
`ExteriorComponentTopology.lean` unknown identifier
`planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noSubcontinuumObstruction`.

2026-05-20 current three-leaf W32 handoff:
`minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_localSelectedNoThird_graphVertexGeometricOrder_20260520`
in `ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean` is now the
sharp checked W32 surface.  It consumes:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
forall C inputs, UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs
forall C inputs,
  S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute
    (S2_dyn_20260520_selected_edge_pair_source (localSource C inputs))
S1 noCutRows
```

It composes the checked reducers:

```lean
S2_dyn_20260520_relative_clopen_topology_source
S2_dyn_20260520_selected_edge_pair_source_family
S2_dyn_20260520_selected_index_geometric_source
minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
```

This is the route to extend next.  Remaining source work is exactly the
Janiszewski relative-clopen theorem, the local selected/no-third germ source,
and the genuine geometric-order rows for the selected heads produced from that
local source.

2026-05-20 sharp live route after blocker-map pass:
The currently sharpest endpoint-free W32 handoff is now the selected-edge/index
split over the relative-clopen topology source:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_selectedEdgePair_indexRows_20260520
```

It consumes:

```lean
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide
forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs
forall C inputs, selected-edge-route genuine outgoing-list index rows
S1 noCutRows
```

The subcontinuum-boundedness handoff is still checked and useful, but is now
one source path into the relative-clopen theorem, not the sharpest local
surface:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumForcesBounded_selectedEdgePair_indexRows_20260520
```

This route does not require `BoundaryFrontierEndpointIncidentOnlyPredSucc`,
`AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource`, a completed
boundary cycle, an induced frontier graph, or identity angular order.  The
local source `LocalSelectedIncidentEdgePairSourceRows` can be obtained from
two-neighbour rows of the actual selected carrier:

```lean
S2_dyn_20260520_local_selected_edge_pair_source_family_of_neighborPairRows
```

and the index rows can be produced from genuine selected geometric-order rows
for the exact selected heads:

```lean
S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute_geometricOrderRows
```

The actual boundary-sector/raw-orbit route is still useful support, and the
new reducers
`minimalFailureExactActualTopologyFieldsTarget_of_preconnected_actualBoundarySector_selectedOrder_safeLocalThirdGerm_20260520`,
`actualBoundaryCycleFrontierEquivalenceRows_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_20260520`,
and `S2_dyn_20260520_carrier_connected_real_source` remain available.  But
unless the sector rows are sourced without endpoint-branch assumptions, do not
prefer that route over the selected-edge/index split.

2026-05-20 endpoint-free actual boundary-sector route update:
The latest checked reducers moved the live S2 local branch away from endpoint
closure/chord statements and toward actual selected carrier edges.

`S2_dyn_20260520_actual_boundary_rows_source` in
`ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean` constructs
`ActualBoundaryCycleFrontierEquivalenceRows C inputs` from local sector rows,
connectedness of `unboundedFrontierCarrierGraph C inputs`, a selected
geometric raw face-successor orbit, raw dart-edge frontier propagation, and
repeated-tail separation.

`S2_dyn_20260520_boundary_geometric_to_selected_geometric_source_rows` in
`ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean` turns same-boundary
actual sector rows plus genuine geometric rotation-order rows into the
selected-neighbour geometric-order source rows consumed by the safe selected
route.

`S2_dyn_20260520_local_exterior_sector_source` and
`S2_dyn_20260520_local_exterior_sector_source_of_incidentCompleteness` in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` are available
only as explicit selected-edge/local-sector reducers.  Do not use them to
prove any unconditional all-adjacent frontier-endpoint theorem; the endpoint
branch remains explicit and is not the preferred selected-neighbour route.

Current active source obligations are therefore:

```text
raw face-successor exterior orbit package
carrier connectedness for the actual unbounded-frontier carrier
same-boundary actual sector rows / genuine geometric rotation order
standard frontier-preconnected or Janiszewski topology source
```

Avoid going backwards to induced frontier graphs, arbitrary cycles, convex hull
cycles, identity angular order, final-cycle assumptions, synthetic enclosures,
or endpoint-chord closure.

2026-05-20 current reduced W32 handoff:
`minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_localSelectedNoThird_geometricOrderRows_20260520`
in `ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean` is the
current checked W32 surface.  It consumes:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
forall C inputs, UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs
forall C inputs, selected geometric-order rows for the selected edge-pair route
S1 noCutRows
```

The topology leaf is further reduced by
`S2_dyn_20260520_component_avoidance_relative_clopen` to
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance`.
The local leaf is reduced by `S2_dyn_20260520_selected_no_third_germ_source`
to same-boundary actual frontier-vertex equivalence, actual boundary
`unboundedFrontierEdgeSet` edge membership, boundary angular no-between rows,
and local exterior point-sector rows.  The geometric leaf is reduced by
`S2_dyn_20260520_geometric_order_source_rows` to pointwise genuine
`GraphVertexGeometricAngularNeighborSelectionRow` rows for the same selected
heads.  These are the live leaves; avoid going backwards through boundedness,
final-cycle rows as assumptions, induced frontier graphs, arbitrary cycles,
all-adjacent endpoint shortcuts, or identity angular order.

2026-05-20 planar preconnected source reduction:
`S2_agent_20260520_planar_preconnected_source_of_connected` and
`S2_agent_20260520_finite_frontier_preconnected_source_of_connected` in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` record the
claim-level strict reduction from the planar and finite-drawing
frontier-preconnectedness surfaces to the standard compact-connected planar
complement theorem `PlanarContinuumUnboundedComplementFrontierConnected`.
The finite drawing contributes only `embeddedEdgeSet_compact` and
`embeddedEdgeSet_connected_of_inputs` through the existing checked reducers.
No completed boundary cycle, induced frontier graph, all-adjacent
endpoint/no-chord row, convex hull shortcut, identity angular order, or
synthetic enclosure row is used.  Verification:
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`
passed.

2026-05-20 selected-neighbour carrier/geometric input eraser:
`selectedNeighborCutPartitionGeometricOrderSource_of_geometricSelectionInputSource`
and
`selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource`
in `ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean` now compose the
actual selected carrier-neighbour/geometric-selection rows directly into the
dependent selected-neighbour source and the geometric-order source rows.  The
compact `..._of_geometricNeighborSelectionRows` and family variants do the same
for the bundled carrier row.  This keeps the selected `unboundedFrontierEdgeSet`
heads, cut data, and genuine sorted `geometricOutgoingDartList` consecutive
indices tied to the same pointwise carrier row; no identity angular order,
all-adjacent endpoint shortcut, induced frontier graph, or final boundary
cycle row is used.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean`
passed.

2026-05-20 selected raw-orbit actual-boundary composer:
`unboundedExteriorFrontierCycleRows_of_selectedRawTailCoverage_cutPartitions_20260520`
and
`unboundedExteriorFrontierCycleRows_of_connectedRawOrbitSourceRows_selectedCutPartitions_20260520`
in `ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean` compose the
checked selected raw-tail package, boundary-free local source carried inside
that package, repeated-tail cut partitions, and
`ActualBoundaryCycleFrontierEquivalenceRows` eraser directly to
`UnboundedExteriorFrontierCycleRows C inputs`.  This removes the extra
raw-orientation/actual-sector residual from this final-cycle support route.
Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`
passed, with only the pre-existing unnecessary-`simpa` style warning at line
7833.

2026-05-20 current W32 leaf composer:
`minimalFailureExactActualTopologyFieldsTarget_of_crossingRelativeClopen_localSector_geometricOutgoingListNoBetween_20260520`
is the shortest checked non-circular W32 handoff for the present three live
S2 leaves after the Nash/Dirac/Kierkegaard reductions.  It consumes exactly:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumRelativeClopenKSide
forall C inputs a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a
forall C inputs,
  S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute
    (S2_dyn_20260520_unreachable_neighbor_source_worker (localSectorRows C inputs))
S1 noCutRows
```

The proof composes through the existing checked reducers
`S2_dyn_20260520_crossing_bounded_source_worker`,
`S2_dyn_20260520_unreachable_neighbor_source_worker`, and
`S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_unreachableAfterDeleteRoute_of_geometric_outgoing_list_no_between_source`,
then reuses
`minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_unreachable_noIntervening_20260520`.
No facade, `KnownBounds` exposure, final-cycle row, induced-frontier graph,
endpoint-only shortcut, or new source leaf is involved.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\FaceBoundaryTopologySourceW32.lean`
passed.

2026-05-20 sharp current W32 composer:
`minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumForcesBounded_selectedEdgePair_indexRows_20260520`
is the newest checked W32 handoff.  It consumes exactly:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded
forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs
forall C inputs,
  UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
    (selected rows derived from those selected-edge rows)
S1 noCutRows
```

This is now the source-facing split to attack.  The three live proof leaves
are therefore:
S2-B: Janiszewski/boundary-bumping subcontinuum-forces-bounded;
S2-A: local selected incident exterior-edge pair rows; and
S2-C: genuine sorted outgoing-list consecutive index rows for those selected
heads.

2026-05-20 S2-B source tightening:
`S2_dyn_20260520_janiszewski_boundedness_source` reduces
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`
to
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction`.
This is the new S2-B leaf.  It is still an honest Janiszewski/boundary-bumping
topology source and does not use compatibility trace, final cycle rows,
induced frontier graphs, arbitrary carriers, or synthetic enclosure rows.

2026-05-20 sharp-leaf audit:
The sharp W32 split is non-circular.  S2-B is independent planar topology.
S2-A names selected incident exterior edges and can be sourced from actual
carrier degree two or actual carrier neighbour-pair rows.  S2-C depends on
S2-A only to identify the same heads and should be sourced from route-specific
`GeometricRotationSystem.GraphVertexAngularNoBetweenRows` or the equivalent
no-intervening outgoing-dart row, then erased by
`S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute`.

2026-05-20 S2-A and S2-C source tightening:
`S2_dyn_20260520_local_selected_edge_pair_source_family_of_neighborPairRows`
reduces the S2-A selected-edge pair family to actual carrier neighbour-pair
rows.  Equivalent stronger routes are the geometric-selection input/source
families, but the least direct row target is still carrier degree two or
`forall a, UnboundedFrontierCarrierNeighborPairAt inputs a`.

`S2_dyn_20260520_selected_edge_index_source_family_of_geometric_outgoing_list_no_between`
reduces the S2-C selected-edge index family to the route-specific genuine
`geometricOutgoingDartList` no-between source for the exact selected heads.
This is now the angular source leaf; do not replace it with identity angular
order or an endpoint-only/no-chord argument.

2026-05-20 local-sector input source tightening:
`S2_dyn_20260520_local_sector_input_source_worker` in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean` proves the honest
pointwise local-sector family from the input-level local selected-edge/no-third
row.  At every actual unbounded-frontier carrier vertex the residual now names
two genuine incident `unboundedFrontierEdgeSet` heads and a positive local
radius on which nearby exterior-frontier points in incident W3 germs cannot
use a third head.  The proof shrinks by the standard vertex-star radius and
then erases through the local two-germ carrier constructor; it does not use the
deleted-neighbour/unreachable route, final boundary cycles, induced frontier
graphs, all-adjacent endpoint assumptions, identity angular order, or convex
hull shortcuts.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean`
passed.

2026-05-20 sharpened S2-A boundary-free source:
`boundaryFreeLocalNoThirdGermSourceRows_of_selectedIncidentEdgePairRows` and
`S2_dyn_20260520_boundaryFreeLocalNoThirdGermSource_of_selectedIncidentEdgePairRows`
in `ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean` reduce
`BoundaryFreeLocalNoThirdGermSourceRows inputs` to the selected incident
exterior-edge pair row
`S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs`.
The proof uses
`S2LocalTwoGermAssembly.localIncidentGermFrontierEdgeMembershipRows_of_inputs`
to obtain the positive local radius and promote any nearby noncenter incident
W3 frontier germ to an actual selected `unboundedFrontierEdgeSet` incidence;
the selected pair row then rules out third heads.  The scout-confirmed chain is
now:

```lean
LocalSelectedIncidentEdgePairSourceRows inputs
  -> BoundaryFreeLocalNoThirdGermSourceRows inputs
  -> BoundaryFreeLocalNoThirdGermSourceRows.toLocalTwoGermRows
  -> localSectorRows_of_localTwoGermRows
  -> forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a
```

This avoids unreachable-after-delete, deleted-neighbour separation, final
boundary-cycle rows, induced frontier graphs, all-adjacent endpoint assumptions,
identity angular order, and convex hull shortcuts.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean`
passed.

2026-05-20 deleted-neighbour source tightening:
`S2_dyn_20260520_unreachable_neighbor_source_worker` reduces
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs`
to the pointwise local-sector source
`forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a`.  The proof
uses the two selected `unboundedFrontierEdgeSet` heads in each local-sector row
and the row's `only` field to rule out every third carrier neighbour.  This
closes the old S2-A deleted-neighbour worker as a strict reduction; the honest
remaining input on that branch is now the actual local-sector row, not an
induced-frontier graph, endpoint-only chord shortcut, or final-cycle row.

2026-05-20 crossing-subcontinuum boundedness tightening:
`S2_dyn_20260520_crossing_bounded_source_worker` reduces
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded`
to
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumRelativeClopenKSide`.
The latter is the crossing-specific relative-clopen side source obtained from
the whole-frontier relative-clopen source.  This keeps the planar-continuum
residual honest and localized: the live S2-B branch now asks for the relative
clopen side in the actual crossing split, not a synthetic trace or final-cycle
substitute.

2026-05-20 selected no-intervening tightening:
`S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_unreachableAfterDeleteRoute_of_geometric_outgoing_list_no_between_source`
pins the no-intervening outgoing-dart row to the live
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource` route
and reduces it to a genuine geometric outgoing-list no-between source.  The
reducer uses sorted outgoing-list membership via
`GeometricRotationSystem.mem_geometricOutgoingDartList`; it does not use
identity angular order, induced frontier graphs, or all-adjacent endpoint
claims.

2026-05-20 source-leaf audit:
S2-A local-sector rows should be sourced through
`BoundaryFreeLocalNoThirdGermSourceRows inputs`, then
`BoundaryFreeLocalNoThirdGermSourceRows.toLocalTwoGermRows`, then
`localSectorRows_of_localTwoGermRows`.  Do not reverse the checked direction
`local-sector -> unreachable-after-delete`; that is circular as a source.

S2-B topology is narrowed to
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`.
The checked chain from that theorem to the current crossing-relative-clopen
leaf is:
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`
to `S2_codex_20260520_relative_clopen_side_source_final` to
`planarContinuumUnboundedComplementFrontierCrossingRelativeClopenKSide_of_relativeClopenKSide`.

S2-C's smallest missing eraser is purely list-theoretic:
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows selectedRows`
should imply
`S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute selectedEdgeRows`.
Use the sorted outgoing list pairwise order and consecutive-index no-between
lemmas, not identity angular order.

2026-05-20 selected successor / raw `faceSucc` leaf:
`rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_selectedNeighborGeometricOrder_sortedBetween_20260520`
connects
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows` to
`RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs`, using the checked
safe local-third-germ source and leaving only the selected
`RawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource` row for
the same selected carrier heads.  The input-source wrapper
`rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_selectedNeighborInput_sortedBetween_20260520`
does the same after reconstructing selected geometric-order rows from
`SelectedNeighborCutPartitionGeometricOrderInputSource`.  This is not a final
boundary-row, endpoint/no-chord, identity-order, arbitrary-cycle, or synthetic
enclosure route.

2026-05-20 sorted-between source reduction:
`rawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource_of_selectedNeighborCutPartition_indexRows_strictOrder_20260520`
and
`rawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource_of_selectedNeighborGeometricOrder_strictOrder_20260520`
strictly reduce the selected raw `faceSucc` sorted-between source.  Existing
selected cut/geometric-order index rows first give the selected-head
`GraphVertexAngularNoBetweenRows`; the real geometric `faceSucc`
successor-tail reducers then recover the three sorted outgoing-list positions
once the remaining primitive strict angular position of the selected
`faceSucc` head between those same selected heads is supplied.  The remaining
primitive is `RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource`
for those selected heads, not identity order, a completed boundary cycle,
convex hull data, or a synthetic enclosure.

2026-05-20 selected faceSucc source reduction:
`rawOrbitIteratedFaceSuccHeadLocalAngularCarrierNoBetweenRowsNoOrbitSource_of_geometricSelectionInputSource`,
`rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_of_geometricSelectionInputSource_strictOrder`,
and
`rawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource_of_geometricSelectionInputSource_strictOrder`
prove the selected successor-tail sorted outgoing-list no-between row from the
bundled selected geometric-neighbour input rows plus the strict selected
`faceSucc` head angular-order row for the same bundled heads.  The propagation
reducers
`rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_geometricSelectionInputSource_strictOrder_20260520`,
`rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_selectedNeighborGeometricOrder_strictOrder_20260520`,
and
`rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_selectedNeighborInput_strictOrder_20260520`
then close the selected raw `faceSucc` frontier-edge propagation row using the
safe selected local third-germ source.  This keeps the exact selected heads
from the genuine geometric outgoing-list package and uses no final boundary
cycle, endpoint-only/no-chord row, identity angular order, induced frontier
graph, arbitrary carrier/cycle, or synthetic enclosure.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean`
passed,
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource`
passed, and the touched Lean-file forbidden-token scan was clean.

2026-05-20 selected strict-order source reduction:
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource` is now
strictly reduced to the genuine successor-tail geometric rows by
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_successorTailGeometricRows`
and to the one-index triple row by
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_successorTailTripleIndex`.
For the exact selected heads produced by the geometric-neighbour source, the
checked wrappers are
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_geometricSelectionInputSource_successorTailRows_20260520`,
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_geometricSelectionInputSource_tripleIndex_20260520`,
and
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_selectedNeighborGeometricOrder_successorTailRows_20260520`.
The direct angular no-between forms are also checked:
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_successorTailNoBetweenRows`,
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_geometricSelectionInputSource_successorTailNoBetweenRows_20260520`,
and
`rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_selectedNeighborGeometricOrder_successorTailNoBetweenRows_20260520`.
This exposes the non-circular source row as the real successor-tail
geometric/triple-index fact for the same selected heads; it does not use
endpoint-only/no-chord rows, identity angular order, an induced frontier graph,
an arbitrary carrier/cycle, a final boundary cycle, or a synthetic enclosure.
Verification: direct
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean`
passed before a later concurrent raw-orbit/orientation edit in the same file.
Latest final sweep is now blocked outside this selected strict/angular-order
lane by `ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean:9090`; the
module build reaches the same blocker after dependencies replay.

2026-05-20 selected point-sector source reduction:
`S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_localSectorRows_geometricOrderRows`
and its family form prove the selected cut/geometric input source from actual
carrier local-sector rows plus genuine geometric-order rows for the same two
selected `unboundedFrontierEdgeSet` heads.  The bundled selected-order forms
`S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrderRows`
and
`S2_agent_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_safeLocalThirdGerm`
record the safe route: `SelectedNeighborThirdGermLocalExteriorPointSectorRows`
can still supply local-sector rows, but the selected input source no longer
needs the false arbitrary-radius `SelectedNeighborLocalExteriorPointSectorRows`
premise.  The owner build
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly`
passed.

2026-05-20 finite-plane topology no-closed-separation leaf:
`planarContinuumUnboundedComplementFrontierNoClosedSeparation_of_connected`
and
`S2_agent_20260520_planar_no_closed_separation_source` reduce the planar
no-closed-separation source to the standard theorem
`PlanarContinuumUnboundedComplementFrontierConnected`.  The finite drawing
handoff
`finiteDrawingUnboundedComplementFrontierAlignedKSplit_of_connected` and
`S2_agent_20260520_finite_aligned_K_split_source_of_connected` specialize
that theorem to the aligned-K split source for `embeddedEdgeSet C`, using only
the existing compactness, connectedness, and frontier-subset facts for the
finite drawing.  This keeps trace-connected compatibility sources off the live
path.  Remaining mathematical source on this branch:
`PlanarContinuumUnboundedComplementFrontierConnected`.

2026-05-20 planar continuum API discovery:
Search of local source and mathlib found no theorem named or shaped as a
Janiszewski/unicoherence/plane-continuum result proving connectedness of the
frontier of an unbounded complement component.  The checked owner-file route is
therefore not missing glue: the mathematical residual is one of the existing
source surfaces below
`PlanarContinuumUnboundedComplementFrontierConnected`.

Useful local/mathed APIs:
`frontier_connectedComponentIn_subset_frontier`,
`planarContinuumUnboundedComplement_frontier_compact`,
`planarContinuumUnboundedComplement_frontier_nonempty`,
`noClosedSeparation_of_isPreconnected`,
`isPreconnected_of_noClosedSeparation`,
`isConnected_of_noClosedSeparation`,
`planarContinuumUnboundedComplementFrontierNoClosedSeparation_of_connected`,
`planarContinuumUnboundedComplementFrontierConnected_of_noClosedSeparation`,
`planarContinuumUnboundedComplementFrontierPreconnected_of_subcontinuumBetween`,
`planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_connected`,
`connectedComponentIn_subset`, `isPreconnected_connectedComponentIn`,
`isConnected_connectedComponentIn_iff`, `connectedComponentIn_eq`,
`connectedComponent_eq_iInter_isClopen`, `isClosed_frontier`,
`frontier_compl`, `frontier_subset_closure`, `IsClosed.frontier_subset`,
`OnePoint.isOpenEmbedding_coe`, `OnePoint.isClosed_image_coe`,
`OnePoint.isDenseEmbedding_coe`, and `OnePoint.instConnectedSpace`.

Recommended next theorem shape:
prove `PlanarContinuumUnboundedComplementFrontierNoClosedSeparation` directly
by a Janiszewski/boundary-bumping closed-split contradiction, or prove
`PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween` if a
continuum-between construction is easier.  Both close the connected frontier
surface through existing checked reducers; no W-facade or source package is
needed.

## Current Claims

- `S2-main-20260520-selected-source-composition`: compose the checked
  selected-neighbour, selected-successor, boundary-free, and finite-topology
  reducers into the shortest owner-file route while the leaf rows below are
  proved.  This claim may add only route-shortening helper theorems in
  `S2SeededRawOrbitSource.lean`, `S2BoundaryFreeRawSource.lean`, or
  `FaceBoundaryTopologySourceW32.lean`.  Current checked shortcut:
  `finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedCutPartitions_20260520`
  drops the raw-orientation residual from the final-cycle support route by
  using the actual-boundary eraser directly.
- `S2-agent-20260520-selected-point-sector-source`: completed by the checked
  selected local-sector/geometric-order reducers above.  The old
  arbitrary-radius point-sector premise is not a live source leaf.
- `S2-agent-20260520-sorted-between-source`: prove or strictly reduce
  `RawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource` for the
  same selected carrier heads used by the selected-successor route.
- `S2-agent-20260520-planar-no-closed-separation-source`: completed/strictly
  reduced.  The finite drawing no-closed-separation / aligned-K split source
  now reduces to `PlanarContinuumUnboundedComplementFrontierConnected`, without
  reverting to compatibility-only trace sources.
- `S2-agent-20260520-planar-continuum-api-discovery`: completed/API mapped.
  No direct mathlib theorem was found for
  `PlanarContinuumUnboundedComplementFrontierConnected`.  The Lean-feasible
  closure is through the existing no-closed-separation or subcontinuum-between
  source surfaces listed above.
- `S2-agent-20260520-planar-preconnected-source`: completed/strictly reduced.
  The planar preconnectedness source and finite-drawing
  frontier-preconnectedness source now reduce to the standard connected-frontier
  theorem `PlanarContinuumUnboundedComplementFrontierConnected`.
- `S2-agent-20260520-selected-edge-pair-source`: prove or strictly reduce the
  selected incident-edge pair / neighbour-pair cut source from actual
  `unboundedFrontierEdgeSet` carrier data, not from arbitrary adjacent
  frontier endpoints.
- `S2-agent-20260520-no-intervening-outgoing-source`: prove or strictly reduce
  the selected no-intervening outgoing-dart row for the exact selected heads
  used by the selected edge-pair route.

## Live Objective

The source-facing external S2 theorem is:

```lean
S2ExteriorBoundarySource.boundaryVertexExteriorSectorRows_of_inputs
```

It is still fine for internal checked reducers to pass through

```lean
ExteriorComponentTopology.UnboundedExteriorFrontierCycleRows C inputs
```

but that family is not the workboard's source target by itself.  The source
theorem must expose the actual boundary cycle and local exterior-sector rows,
not merely erase them.

The source construction must prove from

```lean
inputs : JordanTopologyFactsConcrete.MinimalFailureTopology
  .FinitePlanarOuterComponentInputs C
```

that there is an actual unbounded exterior boundary cycle

```lean
B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C
```

such that:

- graph vertices on `frontier (unboundedExteriorComponentRows C inputs).exterior`
  are exactly the vertices of `B`;
- consecutive boundary edges of `B` are actual unbounded exterior frontier
  edges, not chords through frontier vertices;
- each boundary vertex carries the real geometric exterior-sector row consumed
  by `BoundaryVertexExteriorSectorRowsAt inputs B k`.

The intended proof is orbit-first internally and boundary-sector externally:

```text
FinitePlanarOuterComponentInputs C
  -> unboundedExteriorComponentRows C inputs
  -> Csizmadia-style lowest/exterior seed dart
  -> rotating geometric angular face-successor walk
  -> local two-germ/no-third source
  -> exterior frontier component/carrier connectedness source
  -> selected geometric faceSucc frontier-propagation source
  -> selected raw exterior face-successor orbit
  -> repeated-tail cut rows and no-cut injectivity
  -> UnitDistanceCycleBoundary B
  -> frontier iff B.vertices
  -> UnboundedExteriorFrontierCycleRows C inputs
  -> forall k, BoundaryVertexExteriorSectorRowsAt inputs B k
  -> W32 exact topology target
```

2026-05-20 route minimization checkpoint: the shortest checked support route
to `UnboundedExteriorFrontierCycleRows` is now the local-incident
selected-neighbour route.  Its two live source leaves are:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide

forall {m : Nat} (C : UDConfig m)
  (inputs : FinitePlanarOuterComponentInputs C),
    BoundaryFreeLocalSectorGeometricAngularSource inputs
```

The checked chain is:

```text
BoundaryFreeLocalSectorGeometricAngularSource
  -> selectedNeighborCutPartitionGeometricOrderInputSource_of_boundaryFree_geometricAngularSource
  -> unboundedExteriorFrontierCycleRows_of_finiteDrawingNontrivialRelativeClopen_boundaryFreeGeometricAngular_localIncident_20260520
  -> minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_boundaryFreeGeometricAngular_safeLocalIncident_20260520
```

2026-05-20 selected-source tightening: the input-facing selected cut/geometric
source now has the strict reducer
`S2_codex_20260520_selectedNeighborCutPartitionGeometricOrderInputSource_of_selectedNeighborGeometricOrder_localPointSector`.
It replaces the stale endpoint-only/no-chord premise with actual selected
`unboundedFrontierEdgeSet` geometric-order rows plus the honest local
point-sector theorem for those same selected heads.  Carrier connectedness also
has
`unboundedFrontierCarrierGraph_connected_of_planarContinuum_geometricSelection_localIncident`,
which fills the local-third-germ row from local selected incident-germ
membership instead of carrying it as a separate source premise.

The Janiszewski branch is reduced to the genuine planar topology theorem: a
closed split of the frontier of an unbounded complement component must yield a
relative-clopen side in the compact drawing.  The active proof decomposition is
the compact-Hausdorff clopen separator plus the planar no-subcontinuum
obstruction for such frontier splits.

Current checked erasers include the CT composer
`finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260520`
and the CO composer
`finitePlanarStraightLineOuterComponentTheorem_of_rawFaceSuccOrbitSourceRows_localTwoGerm_incident_selectedSuccessorEdge_20260520co`.
Both are consumers only and no longer the shortest route: the live work is
proving the two source leaves above honestly from
`FinitePlanarOuterComponentInputs C`.

### Csizmadia Boundary-Walk Source Model

Use Csizmadia only for the constructive outer-boundary recipe:

```text
lowest exterior seed vertex
  -> downward ray first-hit neighbour
  -> rotate the current segment around its head to the next angular neighbour
  -> first repeated vertex closes a raw exterior boundary walk
```

For Lean this should become either a compact source row

```lean
ExteriorAngularWalkRows C inputs
```

or current-equivalent raw orbit rows.  The useful source theorem shapes are:

```lean
theorem exists_exterior_seed_dart_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    Nonempty (ExteriorSeedDart C inputs)

theorem rotating_successor_walk_traces_unbounded_frontier
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C)
    (seed : ExteriorSeedDart C inputs) :
    Nonempty (ExteriorAngularWalkRows C inputs)
```

Then prove no-cut tail injectivity and package the simple
`UnitDistanceCycleBoundary B` plus `BoundaryVertexExteriorSectorRowsAt`.

Do not route the rest of Csizmadia into S2: local deletion, reducible
configuration lists, regular/irregular degree-3 machinery, block
decomposition, adjacent-block case analysis, Case A/B selected sets,
Figure 4-7 analytic inequalities, and the final `9 / 35` neighbour-counting
argument belong to a separate Csizmadia formalization.

2026-05-20 composer checkpoint: the direct CO cycle-row declaration
`unboundedExteriorFrontierCycleRows_of_rawFaceSuccOrbitSourceRows_localTwoGerm_incident_selectedSuccessorEdge_20260520co`
feeds the finite theorem above and the W32 consumer
`minimalFailureExactActualTopologyFieldsTarget_of_rawFaceSuccOrbitSourceRows_localTwoGerm_incident_selectedSuccessorEdge_20260520co`.
This is the shortest checked route currently exposed.  It does not license an
all-adjacent endpoint shortcut; the incident-edge premise must remain the
selected unbounded-frontier edge source, or be replaced by its exact next
source theorem.

2026-05-20 checkpoint: the pointwise local two-germ target has been strictly
reduced to the selected geometric-angular source by

```lean
localTwoGermRows_of_boundaryFree_geometricAngularSource
S2_agent_cp_local_two_germ_input_source_20260520
S2_agent_cp_local_two_germ_inputRows_source_20260520
```

This closes the S2-A erasure layer only.  The live source theorem is now the
input-level construction of the selected geometric-angular rows themselves:
two actual `unboundedFrontierEdgeSet` germs at each unbounded-frontier vertex,
their genuine sorted angular no-between relation, and the local third-germ
exclusion.  Do not replace that with the old global
`BoundaryFreeNoThirdGermSource` or any all-adjacent endpoint row.

2026-05-20 selected-neighbour safety checkpoint: the aligned K-split cycle-row
route now has a direct local-incident composer

```lean
unboundedExteriorFrontierCycleRows_of_finiteDrawingAlignedK_selectedNeighborGeometricOrder_localIncident_20260520
```

and a finite nontrivial-relative-clopen companion.  These use
`UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows` plus the
local-radius theorem

```lean
S2_codex_20260520_selected_incident_germ_membership_local_radius
```

to build local sector rows, then route through the selected edge-chain
consumer.  This is the safe route: it never asserts that arbitrary adjacent
frontier endpoints are selected exterior edges.

The next source theorem is the dependent selected-neighbour source:

```lean
SelectedNeighborCutPartitionGeometricOrderSource inputs
```

which packages the selected carrier-neighbour cut-partition rows together with
the sorted outgoing-dart order rows for exactly the same selected heads.
Construct this from `FinitePlanarOuterComponentInputs C`; do not split the
selected-head choice and geometric-order proof into unrelated source families.

## Non-Negotiable Rule

No deferred-premise S2 work.  Do not add or claim a theorem that merely erases
already-missing exterior-boundary data into `UnboundedExteriorFrontierCycleRows`.
Examples of missing data that must not be deferred:

- `ActualBoundaryCycleFrontierEquivalenceRows`
- `BoundaryVertexExteriorSectorRowsAt`
- `ExteriorFrontierCarrierRows`
- actual/sector/carrier rows under another local name
- a selected successor edge row

When a proof needs one of these, the same claim must prove it from
`FinitePlanarOuterComponentInputs C`, or the claim must be rewritten as that
source-row task.

## Current Source Tasks

### S2-A. Local Two-Germ / No-Third Source

Owner files:

- `ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean`
- `ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`
- `ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
- `ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean`

Preferred deliverable:

```lean
localSectorRows_of_inputs :
  forall a : {v : Fin n // v in unboundedFrontierVertexSet C inputs},
    UnboundedFrontierCarrierLocalSectorRowsAt inputs a
```

Demotion note: do not try to prove the old global
`BoundaryFreeNoThirdGermSource inputs` directly from
`FinitePlanarOuterComponentInputs C` as the live source.  Its closed-segment
germ surface is too strong for boundary-chord configurations unless a selected
edge/local radius row has already been supplied.  The honest input task is the
local selected-edge/two-germ row above; legacy `BoundaryFreeNoThirdGermSource`
reducers are useful only after such local rows make the selected carrier edges
explicit.

2026-05-20 endpoint-only honesty update:
`S2_dyn_20260520_local_angular_source_of_selectedNeighbor_pointThirdGerm`
replaces the selected-neighbour local-angular composer that routed through
`endpoint_only`.  The honest residual is now the point-third-germ local
angular source aligned to the same selected carrier neighbours.  The old
endpoint-only premise cannot be closed from
`FinitePlanarOuterComponentInputs C` by the current carrier-neighbour rows:
those rows classify incident edges already in `unboundedFrontierEdgeSet`, while
`endpoint_only` would classify every graph-adjacent frontier endpoint.  Such
an adjacent endpoint may be a frontier chord unless an additional selected
edge/local-neighbour theorem proves the actual incident frontier-edge
membership.

Deleted-neighbour branch status:

```lean
BoundaryFreeLocalNoThirdGermSourceRows.toLocalTwoGermRows
BoundaryFreeLocalNoThirdGermSourceRows.toLocalSectorRows
BoundaryFreeLocalNoThirdGermSourceRows.toComponentTopologyRowsFromEdgeChain
BoundaryFreeLocalNoThirdGermSourceRows.toComponentTopologyInputRowsFromEdgeChain
S2_codex_20260520_unreachableAfterDeleteInputSource_of_boundaryfree_local_germ_source
```

These make the deleted-neighbour and component-topology branches downstream
consequences of the local-radius selected-edge source.  Do not keep a separate
deleted-neighbour premise alive unless the route has first failed to construct
the pointwise `UnboundedFrontierCarrierLocalSectorRowsAt` family.

How to work:

- Start from local vertex-star isolation in `FinitePlaneDrawing.lean`.
- Use the genuine angular order from `GeometricRotationSystem.lean`.
- Show the exterior component occupies one angular gap at a frontier vertex.
- Show the two incident frontier germs bounding that gap are the only selected
  exterior frontier germs at that vertex.
- Do not use a completed boundary cycle or `BoundaryVertexExteriorSectorRowsAt`
  as an input.

Useful searches:

```powershell
rg -n "vertex.*star|local.*sector|LocalSector|NoThird|neighbor_iff|AngularNoBetween" ErdosProblems1066/Swanepoel
rg -n "UnboundedFrontierCarrierLocalSectorRowsAt|BoundaryFreeNoThirdGermSource" ErdosProblems1066/Swanepoel
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2BoundaryFreeRawSource
```

### S2-B. Exterior Component / Carrier Connectedness Source

Owner files:

- `ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
- `ErdosProblems1066/Swanepoel/FinitePlaneDrawing.lean`

Preferred deliverable:

```lean
unboundedExteriorFrontierComponentTopologySourceRows_of_inputs :
  UnboundedExteriorFrontierComponentTopologySourceRows inputs
```

Smaller deliverable:

```lean
unboundedFrontierCarrierGraph_connected_of_inputs :
  (unboundedFrontierCarrierGraph C inputs).Connected
```

How to work:

- Use only `unboundedExteriorComponentRows C inputs` as the exterior component.
- Use the actual unbounded frontier-edge carrier, not the induced graph on all
  frontier vertices.
- Source connectedness from the unbounded component and finite straight-line
  drawing topology.
- Track circularity: a proof of carrier connectedness cannot use a component
  topology row that was itself built from carrier connectedness.
- Endpoint correction: do not prove endpoint closure or incident-edge selection
  for arbitrary adjacent graph vertices whose endpoints both lie on the
  exterior frontier.  Boundary chords can satisfy those endpoint hypotheses
  without being exterior boundary edges.  Endpoint closure is valid only for
  edges already selected in `unboundedFrontierEdgeSet C inputs`.

Checked endpoint support:

```lean
ExteriorComponentTopology
  .closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource
```

This theorem is the safe endpoint lemma.  It consumes
`AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs`, i.e.
actual selected-edge membership in `unboundedFrontierEdgeSet` in one
orientation.  It does not prove, and must not be cited as proving, that every
unit chord between two exterior-frontier vertices is an exterior boundary edge.

2026-05-20 local-source correction:
`SelectedNeighborLocalExteriorPointSectorRows` is too strong as a bare source
target: strict angular-between excludes points on the two selected boundary
germs themselves.  The checked safe replacement is the local-radius third-germ
row

```lean
SelectedNeighborThirdGermLocalExteriorPointSectorRows
S2_codex_20260520_selected_third_germ_local_sector
```

This row only addresses non-selected incident germs inside a vertex-isolating
radius.  It is sourced by
`SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows` and the selected
carrier-neighbour pair row, avoiding the false all-adjacent endpoint/no-chord
shortcut.

Checked frontier-preconnected strict reduction:

```lean
PlanarContinuumUnboundedComplementFrontierPreconnected
PlanarContinuumUnboundedComplementFrontierConnected
PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
planarContinuumUnboundedComplement_frontier_compact
planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_connected
planarContinuumUnboundedComplementFrontierPreconnected_of_subcontinuumBetween
finiteDrawingUnboundedComplementFrontierPreconnected_of_subcontinuumBetween
finiteDrawingUnboundedComplementFrontierPreconnected_of_planarContinuum
S2_dyn_20260520_frontier_preconnected_source_of_planarContinuum
S2_dyn_20260520_planar_continuum_frontier_preconnected_source
S2_dyn_20260520_planar_frontier_subcontinuum_between
S2_dyn_20260520_noOpenSeparation_source_of_planarContinuumPreconnected
S2_dyn_20260520_noOpenSeparation_source_of_subcontinuumBetween
planarContinuumUnboundedComplementFrontierClosedSeparationForcesBounded_of_alignedKSplit
planarContinuumUnboundedComplementFrontierNoClosedSeparation_of_alignedKSplit
planarContinuumUnboundedComplementFrontierConnected_of_alignedKSplit
planarContinuumUnboundedComplementFrontierPreconnected_of_alignedKSplit
finiteDrawingUnboundedComplementFrontierPreconnected_of_alignedKSplit
finiteDrawingUnboundedComplementFrontierNoOpenSeparation_of_alignedKSplit
S2_agent_20260520_cp_aligned_K_split_frontier_preconnected
S2_agent_20260520_cp_aligned_K_split_component_frontier_source
```

Claim `S2-dyn-20260520-planar-continuum-frontier-preconnected-source` is
complete as a strict reduction.  The finite-drawing residual now factors
through the standard planar-continuum subcontinuum-between statement: for
compact connected `K : Set PlanarInterface.Point`, any two points on the
frontier of the unbounded component of `Kᶜ` lie in a compact connected subset
of that same frontier.  The checked reducer uses Mathlib's
`isPreconnected_of_forall_pair` to recover
`PlanarContinuumUnboundedComplementFrontierPreconnected`, and the finite
drawing still contributes only `embeddedEdgeSet_compact` and
`embeddedEdgeSet_connected_of_inputs`; no final S2 cycle rows, exterior
boundary-cycle assumptions, induced frontier graph, arbitrary carrier/cycle,
or synthetic enclosure row is used.  Remaining mathematical source:
prove `PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween`, or
continue reducing that theorem inside the planar continuum/topology lane.

Claim `S2-dyn-20260520-planar-frontier-subcontinuum-between` is now strictly
reduced one step further.  The exact standard continuum theorem left is
`PlanarContinuumUnboundedComplementFrontierConnected`: the frontier of the
unbounded complement component of a compact connected planar set is connected.
Lean checks the remaining compactness part separately via
`planarContinuumUnboundedComplement_frontier_compact`, using only
`frontier_connectedComponentIn_subset_frontier`, `frontier_compl`, and
`IsCompact.of_isClosed_subset`.  The reducer
`planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_connected`
takes the whole frontier as the compact connected subcontinuum between the two
given frontier points.

Claim `S2-codex-current-20260520-subcontinuum-between-source` is recorded as
the direct theorem-level version of the same reduction:

```lean
S2_codex_current_20260520_subcontinuum_between_source :
  PlanarContinuumUnboundedComplementFrontierConnected ->
  PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
```

The residual is therefore exactly
`PlanarContinuumUnboundedComplementFrontierConnected`.  The proof uses
`planarContinuumUnboundedComplement_frontier_compact` and takes the whole
frontier as the compact connected subset joining the two requested frontier
points.

Ohm boundedness lane, 2026-05-20: after Nash's no-closed-separation pivot, do
not add further reducers into
`PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`.  The bounded
route is now exactly
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesBounded`.
The checked handoff is:

```lean
planarContinuumUnboundedComplementFrontierClosedSeparationForcesBounded_of_closedSeparationForcesContinuumSeparation
S2_dyn_20260520_closed_separation_forces_bounded
```

It reduces boundedness to Nash's K-split residual by case-splitting on whether
the selected component is bounded.  In the unbounded branch, the K-split source
produces a nonempty disjoint closed cover of `K`, contradicting
`hconnected.isPreconnected`.

Verification for this reduction:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
```

Subcontinuum boundedness lane, 2026-05-20: the checked reducer
`planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_relativeClopenKSide`
and claim wrapper
`S2_codex_20260520_subcontinuum_boundedness_of_relativeClopenKSide` reduce
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`
to the existing one-sided source
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide`.
In the unbounded branch, the relative-clopen side separates the compact
connected candidate `T` into the two nonempty closed pieces `T ∩ K1` and
`T ∩ (K \ K1)`, contradicting `T`'s preconnectedness.  No final
boundary-cycle rows, induced frontier graph, arbitrary carrier/cycle,
endpoint/no-chord row, convex hull shortcut, identity angular order, synthetic
enclosure row, or new trust assumption is used.  Verification:
`lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`
passed with pre-existing warnings only.

Boyle boundary-trace refresh, 2026-05-20: the same boundedness/relative-clopen
lane is now reduced below the closed frontier split data.  New checked source:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected
planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_frontierTraceConnected
S2_agent_20260520_planar_continuum_boundary_boundedness
S2_agent_20260520_planar_continuum_boundary_relativeClopenKSide
```

The remaining standard topology statement says that if `U` is an unbounded
component of `Kᶜ`, then every subcontinuum `T ⊆ K` has connected nonempty trace
`T ∩ frontier U`.  The checked adapter uses the original closed frontier
pieces only after this trace statement: a split `frontier U = A ∪ B` meeting
both sides in `T` restricts to a closed disjoint cover of
`T ∩ frontier U`, contradicting connectedness.  This is a strict reduction of
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`
and directly feeds the relative-clopen K-side source.

Touched Lean-file forbidden-token scan returned `clean`.

Claim `S2-agent-20260520-cp-component-frontier-source` is strictly reduced on
the aligned K-split lane.  The sharper residual
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit`
now feeds boundedness, no-closed-separation, connectedness, preconnectedness,
finite-drawing no-open-separation, actual S2 frontier preconnectedness, carrier
connectedness, selected edge-chain connectedness, and
`UnboundedExteriorFrontierComponentTopologySourceRows` directly.  The
component package still needs the existing fixed-side local-sector source for
the selected `unboundedFrontierEdgeSet` cover; no final cycle rows, induced
frontier graph, arbitrary cycle, convex hull, or synthetic enclosure are used.

Useful searches:

```powershell
rg -n "UnboundedExteriorFrontierComponentTopologySourceRows|unboundedFrontierCarrierGraph_connected|IsPreconnected|frontier_preconnected" ErdosProblems1066/Swanepoel
rg -n "unboundedExteriorComponentRows|unboundedFrontierEdgeSet|unboundedFrontierCarrierGraph" ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FinitePlaneDrawing
```

### S2-C. Selected Geometric FaceSucc Frontier Propagation

Owner files:

- `ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`
- `ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean`
- `ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`

Preferred deliverable:

```lean
rawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource_of_inputs :
  RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs
```

Smaller deliverable:

```lean
rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_inputs :
  RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs
```

Current reducer, 2026-05-20:

```lean
S2_dyn_20260520_successor_frontier_point_source :
  BoundaryFreeLocalSectorGeometricAngularSource inputs ->
  RawOrbitIteratedGeometricFaceSuccPropagationNoOrbitSource
    inputs localAngularSource ->
  RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs
```

This is a strict local-angular/frontier-propagation reduction.  The selected
geometric propagation row is exactly the head-between residual already used by
`S2_C_co_selected_successor_edge_source_20260520co` to close the stronger
selected successor frontier-edge no-orbit source; the local-angular package
also supplies the local-sector rows used by the midpoint eraser.  Remaining
honest residuals are:

- `BoundaryFreeLocalSectorGeometricAngularSource inputs`
- `RawOrbitIteratedGeometricFaceSuccPropagationNoOrbitSource inputs
  localAngularSource`

Update, 2026-05-20, claim
`S2-dyn-20260520-geometric-faceSucc-propagation-source`:
`S2SeededRawOrbitSource.lean` now strictly reduces this propagation source to
the two local pointwise graph-dart inequalities
`RawOrbitIteratedGeometricFaceSuccPropagationLeftNoOrbitSource inputs
localAngularSource` and
`RawOrbitIteratedGeometricFaceSuccPropagationRightNoOrbitSource inputs
localAngularSource`, via
`S2_dyn_20260520_geometric_faceSucc_propagation_source` and the family wrapper.
These rows are exactly the left/right angular bounds for the selected
geometric `faceSucc` head at the successor tail.  Verification passed:
`elan run leanprover/lean4:v4.28.0 lake env lean
ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean` and `elan run
leanprover/lean4:v4.28.0 lake build
ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource`.

Verification note:
`elan run leanprover/lean4:v4.28.0 lake build
ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource` passed.

How to work:

- Start from an exterior-side point on the current selected frontier edge.
- Move through a small neighbourhood of the head vertex.
- Use S2-A local two-germ/no-third data and the geometric `faceSucc`.
- Produce an interior frontier point, or the whole frontier-edge row, on the
  selected successor edge.
- Do not revive the orientation-free `FaceSuccFrontierEdgeSource` as the live
  target.

Useful searches:

```powershell
rg -n "RawOrbitIteratedFaceSucc.*Source|faceSucc|InteriorFrontierPoint|FrontierEdgeNoOrbit" ErdosProblems1066/Swanepoel
rg -n "geometricUnitDistanceRotationSystem|faceSucc|nextAround|prevAround" ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean ErdosProblems1066/Swanepoel/JordanTopologyFactsConcrete.lean
```

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.GeometricRotationSystem
```

### S2-D. Final Composition

Owner files:

- `ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean`
- `ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean`

Deliverable:

```lean
S2ExteriorBoundarySource.boundaryVertexExteriorSectorRows_of_inputs
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows
```

Route-composer audit, 2026-05-20:

The shortest non-circular source-facing route currently present is:

```lean
S2ExteriorBoundarySource
  .S2_unboundedExteriorFrontierCycleRows_family_of_actualExteriorSectorInputSourceRows
ExteriorComponentTopology
  .finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
```

The exact source theorem to prove is:

```lean
forall {n : Nat} (C : UDConfig n)
  (inputs : FinitePlanarOuterComponentInputs C),
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

This packages the actual boundary cycle, exact graph-vertex frontier
equivalence, consecutive selected frontier-edge rows, angular/no-between rows,
and local selected-edge/two-germ rows on the same `B`.

Older checked composition route:

```lean
S2SeededRawOrbitSource
  .unboundedExteriorFrontierCycleRows_of_connectedIteratedFaceSuccEdgeSource
ExteriorComponentTopology
  .finitePlanarStraightLineOuterComponentTheorem_of_unboundedExteriorFrontierCycleRows
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows
```

This route is only a composition surface.  It cannot yet be closed from bare
`FinitePlanarOuterComponentInputs C`, because the following exact input-level
theorem names are still missing:

```lean
localSectorRows_of_inputs :
  forall a : {v : Fin n // v in unboundedFrontierVertexSet C inputs},
    UnboundedFrontierCarrierLocalSectorRowsAt inputs a

unboundedFrontierCarrierGraph_connected_of_inputs :
  (unboundedFrontierCarrierGraph C inputs).Connected

rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_inputs :
  RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs
```

The last theorem feeds the checked adapter
`rawOrbitIteratedFaceSuccFrontierEdgeSource_of_noOrbitSource`, which supplies
the orbit-indexed edge source required by
`unboundedExteriorFrontierCycleRows_of_connectedIteratedFaceSuccEdgeSource`.
No composition lemma was added because these premises are not genuinely
available from inputs.

Local-sector honesty repair, 2026-05-20:

```lean
BoundaryFreeLocalNoThirdGermSourceRows.toComponentTopologyRowsFromEdgeChain
RawOrbitCoverageSourceRows.toComponentTopologyRowsFromLocalSectorRows
rawOrbitCoverageSourceRows_of_tailCoverage_localSectorRows
rawOrbitCoverageSourceRows_of_connectedCarrier_localSectorRows
unboundedExteriorCycleRows_of_edgeChain_localSectorRows
unboundedExteriorCycleRows_of_edgeChain_localNoThirdGermSource
unboundedExteriorCycleRows_of_rawCoverage_localSectorRows
finitePlanarStraightLineOuterComponentTheorem_of_edgeChain_localSectorRows
finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_localSectorRows
```

These are now the preferred checked reducers for the local branch.  They route
raw coverage, edge-chain connectivity, component-topology rows, and final cycle
rows through `UnboundedFrontierCarrierLocalSectorRowsAt`; the old
`BoundaryFreeNoThirdGermSource` and endpoint-incident wrappers remain
compatibility consumers only.

How to work:

- Compose only with source rows already proved from
  `FinitePlanarOuterComponentInputs C`.
- A missing S2-A, S2-B, or S2-C row is handled immediately by proving that row
  inside the same claim or by switching the claim to that source task.
- Keep the final file thin: it should assemble the source theorem, not introduce
  another facade or wave layer.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

## Tried Routes And Current Status

### Checked: Local CO Reducers

These declarations are checked support reducers, not final S2 source
theorems.  They are safe to use only when their premises have already been
proved from `FinitePlanarOuterComponentInputs C` in S2-A/B/C.

```lean
ExteriorComponentTopology
  .S2_agent_co_frontier_vertex_incident_source_20260520co

ExteriorComponentTopology
  .S2_agent_co_open_segment_closure_source_20260520co

S2LocalTwoGermAssembly
  .S2_agent_co_local_two_germ_source_20260520co

S2LocalTwoGermAssembly
  .S2_agent_ct_local_sector_from_cutPartitionRows_20260520

S2LocalTwoGermAssembly
  .S2_agent_ct_local_sector_input_source_family_of_cutPartitionRows_20260520

S2SeededRawOrbitSource
  .finitePlanarStraightLineOuterComponentTheorem_of_rawCoverage_localTwoGerm_incident_selectedSuccessorEdge_20260520co

FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_rawCoverage_localTwoGerm_incident_selectedSuccessorEdge
```

Status: useful only as downstream composition.  Do not claim work that merely
adds another reducer of this kind; the remaining source tasks are S2-A,
S2-B, and S2-C below.

### Current Residual Split

- Worker-map refresh, 2026-05-20:
  The live route is unchanged, but the active work has been pruned to source
  obligations rather than pool/wave tasks.  Closed or stale lanes:
  completed Godel two-arc cutpartition reducer, superseded Gibbs
  selector-avoidance reducer, and stale Galileo verification-only pass.
  After the latest reductions, active proof lanes now target exactly:
  `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation`
  (the bounded route is now reduced to it);
  the pointwise selected-edge/local-radius source feeding
  `S2_dyn_20260520_local_sector_source_at_frontier_vertex`;
  `RawOrbitIteratedGeometricFaceSuccPropagationNoOrbitSource inputs
  localAngularSource`;
  `RawOrbitIteratedFaceSuccHeadAvoidsLocalAngularCarrierLeftSelectorNoOrbitSource`
  and
  `RawOrbitIteratedFaceSuccHeadAvoidsLocalAngularCarrierRightSelectorNoOrbitSource`;
  and `S2RepeatedBoundaryArcRealWitnessPrimitiveRows`.  This does not license
  any all-adjacent endpoint-incident theorem, induced frontier graph,
  arbitrary carrier/cycle, or final boundary-cycle premise as an input.

  Claim `S2-dyn-20260520-selector-avoidance-halves-source` is claimed by
  Codex GPT-5 on 2026-05-20.  The intended reduction is the local angular
  third-germ/faceSucc-head-between lane: each selector half should reduce to
  a one-sided strict angular-order inequality at the selected successor tail,
  not to a selected-edge equality or carrier membership shortcut.

  Completion note, 2026-05-20: `S2SeededRawOrbitSource.lean` now contains the
  one-sided sources
  `RawOrbitIteratedFaceSuccHeadAfterLocalAngularCarrierLeftSelectorNoOrbitSource`
  and
  `RawOrbitIteratedFaceSuccHeadBeforeLocalAngularCarrierRightSelectorNoOrbitSource`.
  The checked theorem `S2_dyn_20260520_selector_avoidance_halves_source`
  reduces the left/right local-angular selector avoidance halves to those two
  strict graph-dart argument inequalities.  The residual is exactly those
  pointwise strict angular-order rows at the selected `faceSucc` successor
  tail.  Verification passed:
  `lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource`.

  Completion note, 2026-05-20, claim
  `S2-dyn-20260520-strict-angular-order-source-rows`:
  `S2SeededRawOrbitSource.lean` now packages the shared strict-order leaf as
  `RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource`, feeding
  the two selector residuals and Halley's propagation-left/right residuals
  through `S2_dyn_20260520_strict_angular_order_source_rows`.  The sharper
  residual is the sorted-list index source
  `RawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource`, which
  stays at the selected geometric `faceSucc` successor tail and derives the
  strict `graphDartArg` inequalities by the genuine geometric outgoing-dart
  list order using
  `GeometricRotationSystem.graphDartArg_lt_of_dartFromGeometricList_index_lt`
  and
  `rawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource_of_sortedBetween`.
  Verification passed:
  `elan run leanprover/lean4:v4.28.0 lake env lean
  ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean`.  The touched file
  scan found no axioms, constants, sorries, admits, unsafe, opaque, or debug
  commands.

  Completion note, 2026-05-20, claim
  `S2-dyn-20260520-sorted-between-source`:
  `RawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource` is now
  strictly reduced by `S2_dyn_20260520_sorted_between_source` to
  `RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource`.
  The residual is exact: at each selected Nat-indexed raw iterate and selected
  `faceSucc` successor tail, prove two real
  `GraphVertexGeometricAngularNeighborSelectionRow`s in the sorted outgoing
  geometric dart list, one from the left local-angular carrier to the selected
  `faceSucc` head and one from that head to the right local-angular carrier,
  with the first row's successor index equal to the second row's index.  This
  is the missing sorted-dart lemma/source row; it uses no selected-edge
  equality shortcut, endpoint-only/no-chord assumption, final cycle rows,
  actual-boundary rows, induced frontier graph, arbitrary carrier/cycle,
  synthetic enclosure, or identity angular order.

  Build checkpoint: the combined pinned S2 owner build
  `lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
  ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource
  ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
  ErdosProblems1066.Swanepoel.ExteriorComponentTopology`
  passed on 2026-05-20 after the seeded `htail` repair.

  Selector-aware route cleanup: the checked composer
  `unboundedExteriorFrontierCycleRows_of_geometricSelection_endpointOnly_successorPoint_selectorAvoidance_20260520`
  now exposes the left/right selector-avoidance halves directly instead of the
  older raw `notLocalCarrier` premise.  This is only a route cleanup; the live
  mathematical leaves remain the selected-neighbour source, endpoint-only row,
  successor geometric propagation, selector-avoidance halves, local-radius
  selected-edge row, crosscut K-split theorem, and repeated-tail primitive
  two-open-arc rows.

- Residual board refresh, 2026-05-20:
  `TASK.md` is the active workboard; this note records the exact live residual
  names after pruning completed/superseded dynamic claims.  The live residuals
  are:
  `UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs`;
  `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a`;
  `PlanarContinuumUnboundedComplementFrontierConnected`;
  `RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs`;
  `RawOrbitIteratedFaceSuccHeadAvoidsLocalAngularCarrierSelectorsNoOrbitSource
  inputs localAngularSource`; and the repeated selected raw-tail callback
  `forall {i j}, i != j -> (rows.O.dart i).tail = (rows.O.dart j).tail ->
    Nonempty (CutVertexInterface.CutVertexPartition C)`.  Nash owns the
  continuum-frontier connected residual; Dewey owns the selector-avoidance
  residual.  Older broad active claims remain historical only if this list gives
  their sharper completed/superseding residual.
- Claim `S2-dyn-20260520-two-arc-separation-source` strictly reduced the
  selected repeated raw-tail source in
  `S2ExteriorBoundarySource.lean`.  The actual source
  `S2RepeatedBoundaryArcSeparationSource`, which feeds
  `S2_repeated_tail_two_arc_cutpartition_20260520` and the cut-partition
  callback, is now obtained from the smaller primitive row
  `S2RepeatedBoundaryArcRealWitnessPrimitiveRows` by
  `S2RepeatedBoundaryArcRealWitnessPrimitiveRows.toRepeatedBoundaryArcSeparationSource`
  and the input-shaped
  `S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_20260520`.
  Exact remaining source: for each hypothetical repeated selected raw-tail pair,
  prove non-cut witnesses on the two cyclic open raw arc images, raw-tail
  coverage away from the deleted tail, off-cut image disjointness, and
  anticompleteness across the two image sides.  This reduction does not use a
  final boundary cycle, actual-boundary equivalence row, induced frontier graph,
  arbitrary carrier/cycle, synthetic enclosure, or endpoint shortcut.  The
  touched Lean-file forbidden-token scan was clean, and the targeted owner
  build for `ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource` passed.

- Claim `S2-dyn-20260520-repeated-tail-primitive-rows-source` is now strictly
  reduced in `S2ExteriorBoundarySource.lean`.  Added
  `S2RepeatedBoundaryArcRealWitnessPrimitiveRows.ofRepeatedTailActualExteriorArcRows`
  and the input-shaped
  `S2_repeatedBoundaryPrimitiveRows_of_repeatedTailActualExteriorArcRows_20260520`,
  which erase selected raw pair-level
  `RawFaceSuccOrbitRepeatedTailActualExteriorArcRows` to the exact primitive
  row: non-cut witnesses on the two cyclic open raw arc images, raw-tail
  coverage away from the deleted tail, off-cut image disjointness, and
  anticompleteness across the two image sides.  Also added
  `S2_repeatedBoundaryArcSeparationSource_of_repeatedTailActualExteriorArcRows_20260520`
  to feed the existing `primitiveTwoOpenArcRows` reducer directly.  Verification:
  `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2ExteriorBoundarySource.lean`
  passed; no `sorry`/`admit`/`axiom` scan hits in the touched file.

- Claim `S2-dyn-20260520-repeated-tail-actual-exterior-arc-rows` is now
  strictly reduced in `S2ExteriorBoundarySource.lean`.  Added
  `S2RepeatedBoundaryArcRealWitnessPrimitiveRows.toRepeatedTailActualExteriorArcRows`
  to construct `RawFaceSuccOrbitRepeatedTailActualExteriorArcRows` from the
  primitive actual two-open-arc source after deleting the repeated tail, and
  added the input-shaped
  `S2_repeatedTailActualExteriorArcRows_of_primitiveTwoOpenArcRows_20260520`.
  The handoff
  `S2_repeatedBoundaryArcSeparationSource_of_primitiveTwoOpenArcRows_via_actualExteriorArcRows_20260520`
  explicitly feeds
  `S2_repeatedBoundaryArcSeparationSource_of_repeatedTailActualExteriorArcRows_20260520`.
  Remaining source: for each hypothetical repeated selected raw-tail pair,
  prove the primitive two-arc row: non-cut witnesses on both cyclic open raw
  arc images, raw-tail coverage away from the deleted tail, off-cut image
  disjointness, and anticompleteness across the two image sides.  This uses no
  final boundary cycle, actual-boundary equivalence row, induced frontier
  graph, arbitrary carrier/cycle, synthetic enclosure, or endpoint shortcut.
  Verification: `lake env lean ErdosProblems1066\Swanepoel\S2ExteriorBoundarySource.lean`
  passed; no `sorry`/`admit`/`axiom` scan hits in the touched Lean file.

- Claim `S2-codex-20260520-primitive-source-rows-projection` strictly reduced
  `S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows` to the existing
  concrete raw-index repeated-tail witness/source rows.  Added
  `S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows.ofRealWitnessSourceRows`,
  `.ofSourceWitnessRows`, and the two input-shaped reducers
  `S2_repeatedBoundaryPrimitiveSourceRows_of_realWitnessSourceRows_20260520`
  and
  `S2_repeatedBoundaryPrimitiveSourceRows_of_sourceWitnessRows_20260520`.
  The projection preserves the selected open-arc indices and non-cut
  coverage, and derives the primitive image disjointness/anticompleteness
  fields from raw-index same-tail-only-cut and anticompleteness rows.  This
  stays source-level: no final boundary cycle, actual-boundary equivalence
  row, induced frontier graph, arbitrary carrier/cycle, synthetic enclosure,
  or endpoint shortcut.  Verification:
  `elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource`
  passed.

- Claim `S2-codex-20260520-real-witness-primitive-source-direct` strictly
  reduced the live real-witness row
  `S2RepeatedBoundaryArcRealWitnessSourceRows` to the concrete primitive
  raw-index source rows.  Added
  `S2RepeatedBoundaryArcRealWitnessPrimitiveSourceRows.toRealWitnessSourceRows`
  and the input-shaped
  `S2_repeatedBoundaryRealWitnessSourceRows_of_primitiveSourceRows_20260520`.
  This preserves the chosen left/right cyclic open-arc indices and non-cut
  raw-tail coverage, deriving only same-tail-only-cut from off-cut image
  disjointness and index anticompleteness from graph anticompleteness across
  the two raw-tail image sides.  Direct owner-file check
  `elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean`
  passed; the requested Lake target is currently blocked upstream by
  pre-existing `S2LocalTwoGermAssembly.lean` errors at lines 3607 and 3612.

- Claim `S2-dyn-20260520-crosscut-K-split-source` strictly reduced the exact
  live continuum topology source
  `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation`.
  The new residual is the aligned Janiszewski/boundary-bumping source
  `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit`:
  for any compact planar `K`, exterior point `x`, unbounded component, and
  closed disjoint frontier split `frontier (connectedComponentIn Kᶜ x) = A ∪ B`,
  construct closed disjoint `K₁/K₂` with `K = K₁ ∪ K₂`, `A ⊆ K₁`, and
  `B ⊆ K₂`.  The checked adapter
  `planarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation_of_alignedKSplit`
  supplies the nonempty `K`-side fields from `A.Nonempty` and `B.Nonempty`,
  and `S2_dyn_20260520_crosscut_K_split_source` exposes the claim-level
  reducer.  No reducer was added into
  `PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`, and the
  route uses no final S2 cycle rows, exterior carrier rows, induced frontier
  graph, arbitrary carrier/cycle, convex hull, or synthetic enclosure.  The
  owner-file Lean check for `ExteriorComponentTopology.lean` passed on
  2026-05-20.

- Claim `S2-dyn-20260520-aligned-K-split-source` strictly reduced the exact
  aligned K-split residual
  `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit`.
  Reduced first to the one-sided source
  `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide`:
  for a compact planar `K`, exterior point `x`, unbounded complement component,
  and closed disjoint frontier split
  `frontier (connectedComponentIn Kᶜ x) = A ∪ B`, choose one closed side
  `K₁ ⊆ K` such that `K \ K₁` is closed, `A ⊆ K₁`, and
  `Disjoint K₁ B`.  The checked adapter
  `planarContinuumUnboundedComplementFrontierAlignedKSplit_of_relativeClopenKSide`
  sets `K₂ = K \ K₁`, uses
  `planarContinuumUnboundedComplement_frontier_subset` to place `B` in `K`,
  and constructs the required closed disjoint cover `K = K₁ ∪ K₂` with
  `A ⊆ K₁` and `B ⊆ K₂`.  The claim wrapper now consumes the sharper
  nontrivial source
  `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide`,
  whose extra hypotheses are `A.Nonempty` and `B.Nonempty`; the degenerate
  empty-side cases are handled by the checked adapter
  `planarContinuumUnboundedComplementFrontierRelativeClopenKSide_of_nontrivialRelativeClopenKSide`.
  Claim wrapper: `S2_dyn_20260520_aligned_K_split_source`.  No reducer was
  added into
  `PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`, and the
  route uses no final S2 cycle rows, carrier rows, induced frontier graph,
  arbitrary carrier/cycle, convex hull, or synthetic enclosure.  The owner-file
  Lean check and targeted Lake owner build for `ExteriorComponentTopology.lean`
  passed on 2026-05-20 with only existing lint/style warnings.

- Claim `S2-agent-20260520-current-alignedK-input` tightened the same lane at
  the finite-drawing level.  Added
  `FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit`
  for the actual `embeddedEdgeSet C` and drawing-complement component
  frontiers, plus
  `finiteDrawingUnboundedComplementFrontierPreconnected_of_alignedKSplit`.
  This proves finite drawing frontier preconnectedness by applying the aligned
  split to a hypothetical nonempty closed frontier separation and contradicting
  `embeddedEdgeSet_connected_of_inputs`.  The actual S2-B consumers now have
  finite-drawing source reducers:
  `actualFrontierPreconnected_of_finiteDrawing_alignedKSplit`,
  `componentTopologySourceRows_of_finiteDrawingAlignedKSplit_localSectorRows`,
  `unboundedFrontierCarrierGraph_connected_of_finiteDrawingAlignedKSplit_localSectorRows`,
  `edgeChain_of_finiteDrawingAlignedKSplit_localSectorRows_fixedSide`, and
  `S2_agent_20260520_current_alignedK_input_component_frontier_source`.
  This is not a final-cycle/carrier-row route: it stays on the actual
  `embeddedEdgeSet C` topology plus fixed-side local-sector rows.

- Import/order audit `S2-dyn-20260520-import-order-and-owner-build-audit`
  passed on 2026-05-20.  No declaration-order or import repair was needed in
  `S2ExteriorBoundarySource.lean`, `S2BoundaryFreeRawSource.lean`, or
  `S2SeededRawOrbitSource.lean`; all three owner modules build.  This older
  audit is superseded for the local branch by the local-sector honesty repair
  above.  Its then-smallest residual names were:
  `BoundaryFreeNeighborPairEndpointOnlySourceRows inputs`,
  `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs`,
  `FiniteDrawingUnboundedComplementFrontierPreconnected`,
  `SelectedRawTailCoverageSourceRows inputs`, and the selected-orbit repeated
  witness callback
  `forall {i j}, i != j -> (rows.O.dart i).tail = (rows.O.dart j).tail ->
    S2RepeatedTailExteriorCutWitnessSource (inputs := inputs) rows.O i j`.
- S2-A must prove local two-germ/no-third data from the unbounded exterior
  component and genuine geometric angular order.  The local-sector half now
  has a strictly smaller checked source:
  `S2_agent_ct_local_sector_from_cutPartitionRows_20260520` gets
  `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a` from only the
  pointwise cut-partition neighbour rows, so the adjacent-endpoint
  incident-edge and angular-row premises are no longer needed for that
  local-sector target.  The remaining source on this cut is exactly
  `forall a, UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a`.
  The cut-partition residual now has the checked CU reduction
  `S2_agent_cu_neighbor_cutpartition_source_of_unreachableAfterDelete_20260520`
  and its family form
  `S2_agent_cu_neighbor_cutpartition_source_family_of_unreachableAfterDelete_20260520`,
  reducing it to
  `UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs`.
  Claim `S2-dyn-20260520-local-radius-selected-edge-source` is checked in
  `S2LocalTwoGermAssembly.lean`: the structured source
  `LocalRadiusSelectedEdgeSourceRows inputs` forgets through
  `LocalRadiusSelectedEdgeSourceRows.toExistsSource` to the pointwise
  existential source consumed by
  `S2_dyn_20260520_local_sector_source_at_frontier_vertex`, and
  `S2_dyn_20260520_local_radius_selected_edge_source` returns the local-sector
  family.  This does not use a completed boundary cycle,
  `BoundaryVertexExteriorSectorRowsAt`, an induced frontier graph, arbitrary
  carrier/cycle data, synthetic enclosure data, identity angular order, or a
  universal adjacent-endpoint source.
  The live S2-A source is therefore the local selected-edge row itself:
  choose the two selected incident unbounded-frontier edges at each frontier
  vertex, prove they are distinct, and prove the positive-radius local
  no-third-germ row.  Older
  `BoundaryFreeNeighborPairEndpointOnlySourceRows` wrappers are demoted to
  compatibility consumers because their endpoint branch is still a no-chord
  statement about arbitrary adjacent frontier endpoints.  The open-edge branch
  remains handled by the existing interior-frontier carrier-membership theorem,
  not a universal adjacent-endpoint incident shortcut.

- Claim `S2-dyn-20260520-inhabit-local-radius-selected-edge-rows` is now
  strictly reduced in `S2LocalTwoGermAssembly.lean`.  Added
  `localRadiusSelectedEdgeSourceRows_of_neighborPairRows`, with claim wrapper
  `S2_dyn_20260520_inhabit_local_radius_selected_edge_rows`, proving
  `LocalRadiusSelectedEdgeSourceRows inputs` from the concrete carrier
  neighbour-pair family
  `forall a, UnboundedFrontierCarrierNeighborPairAt inputs a`.  At each
  frontier vertex the selected heads are exactly the two actual carrier
  neighbours, so their incident edges are obtained from
  `unboundedFrontierCarrierGraph_adj_iff`.  The local radius is the finite
  graph-vertex isolation radius from `FinitePlaneDrawing`, excluding closed
  third endpoint germs; relative-interior third germs are promoted to actual
  `unboundedFrontierEdgeSet` edges by the checked
  `InteriorFrontierEdgeCarrierMembershipSource` and then contradicted by
  `neighbor_iff`.  No final boundary cycle, `BoundaryVertexExteriorSectorRowsAt`,
  induced frontier graph, arbitrary carrier/cycle, synthetic enclosure,
  identity angular order, or universal adjacent endpoint source is used.
  Verification: direct `lake env lean`, targeted Lake build for
  `ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly`, and touched-file
  forbidden-token scan passed.
- Claim `S2-dyn-20260520-geometric-neighbor-selection-source` is now strictly
  reduced in `S2LocalTwoGermAssembly.lean`.  The new source rows
  `UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows` package the
  current real carrier-neighbour pair family together with the honest extra
  geometric fact: those same two selected heads are a non-wrap consecutive pair
  in the genuine sorted outgoing-dart list.  Its eraser
  `S2_dyn_20260520_geometric_neighbor_selection_source` produces
  `UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs`
  without final boundary-cycle rows, actual-boundary equivalence rows, induced
  frontier graph, arbitrary carrier/cycle, synthetic enclosure, identity
  angular order, or all-adjacent endpoint closure/incident shortcuts.  The
  endpoint-only/no-chord row is not bundled here; it remains a separate sharper
  residual for consumers that need the closed endpoint-germ branch.
- S2-B now has `embeddedEdgeSet_connected_of_inputs` checked in
  `FinitePlaneDrawing.lean`.  The broad open-separation wrapper has been
  reduced to the sharper finite-drawing theorem
  `FiniteDrawingUnboundedComplementFrontierPreconnected`: direct
  preconnectedness of the frontier of each unbounded complement component of
  this compact connected finite drawing.  It feeds
  `S2_agent_cu_finite_drawing_frontier_topology_20260520cu` and then the
  existing `UnboundedExteriorFrontierNoOpenSeparationSource` row.
  The narrower actual-component route is now also checked:
  `S2_pool_cx_frontier_topology_source_from_edgeChain_localSectorRows_20260520`
  proves `UnboundedExteriorFrontierNoOpenSeparationSource C inputs` directly
  for the actual `unboundedExteriorComponentRows C inputs` from the exact
  residuals `UnboundedFrontierEdgeCarrierSegmentChainConnected inputs` and
  `forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a`.  This
  bypasses the broad
  `FiniteDrawingUnboundedComplementFrontierPreconnected` premise on the
  no-open-separation path.
  API scout `S2-agent-cw-planar-frontier-preconnected-api-scout` found no
  mathlib theorem closing this planar-continuum step.  Mathlib supplies the
  component/open-set mechanics (`connectedComponentIn`, `mem_connectedComponentIn`,
  `connectedComponentIn_subset`, `isPreconnected_connectedComponentIn`,
  `IsOpen.connectedComponentIn`, `frontier_subset_closure`, `IsOpen.frontier_eq`,
  `IsOpen.inter_frontier_eq`, and `isPreconnected_iff_subset_of_disjoint`), but
  not the theorem that an unbounded complementary domain of a compact connected
  planar set has connected frontier.  The subcontinuum-between residual has
  been reduced to that exact connected-frontier theorem: compactness of the
  frontier is checked from component-frontier inclusion and compactness of
  `K`, and the whole frontier is used as the compact connected subset between
  the two given points.
  Continuation API scout
  `S2-dyn-20260520-continuum-frontier-connected-api-scout` checked the current
  mathlib/project surface for the sharpened Nash residual and again found no
  existing theorem closing
  `PlanarContinuumUnboundedComplementFrontierConnected`, nor a shorter named
  standard lemma about connected frontiers of unbounded complementary
  components of compact connected plane continua.  Searches around
  `frontier`, `IsConnected`, `IsPreconnected`, `connectedComponentIn`,
  `Bornology.IsBounded`, `continuum`, `EuclideanSpace`, `Fin 2`, and `Jordan`
  only exposed generic component/frontier mechanics or unrelated convex,
  complex, order, spectrum, and ball-frontier facts.  The shortest checked
  project reducer remains the current connected-frontier theorem surface:
  connectedness of
  `frontier (connectedComponentIn Kᶜ x)` implies the subcontinuum-between,
  preconnectedness, no-open-separation, and finite-drawing residuals through
  the existing reducers.  No Lean code was changed.
- The old endpoint source target
  `AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs` is not
  a valid unconditional target from `FinitePlanarOuterComponentInputs C`,
  because adjacent exterior-frontier endpoints may be joined by an interior
  chord.  The checked endpoint branch is selected-edge only:
  `closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource`.
  The live residual is not endpoint closure; it is constructing the actual
  selected exterior carrier/orbit that supplies `unboundedFrontierEdgeSet`
  membership for boundary edges.
- S2-C must prove selected geometric `faceSucc` frontier propagation and raw
  orbit coverage from actual exterior raw face orbit data.  The exact
  input-facing raw source now has a checked residual:
  `exists_rawFaceSuccOrbit_sourceRows_of_dartFrontier_tailCoverage_20260520cu`
  produces
  `Exists R start O, Nonempty (RawFaceSuccOrbitSourceRows (inputs := inputs) O)`
  from the selected raw dart-frontier row, cyclic carrier coverage, local
  sectors, positive raw-tail coverage of every unbounded-frontier carrier
  vertex, and repeated-tail separation.  The period lower bound is derived
  internally.  The consecutive-edge variant is
  `exists_rawFaceSuccOrbit_sourceRows_of_edgeFrontier_tailCoverage_20260520cu`.
  New CX cut:
  `exists_rawFaceSuccOrbit_sourceRows_of_selectedRawTailCoverage_20260520cx`
  turns a concrete `SelectedRawTailCoverageSourceRows inputs` package plus
  repeated-tail exterior separation on that same selected orbit into the exact
  existential raw-source target.  The connected-source version
  `exists_rawFaceSuccOrbit_sourceRows_of_connectedRawOrbitSourceRows_selectedRepeatedTail_20260520cx`
  derives the selected raw-tail package from `BoundaryFreeConnectedRawOrbitSourceRows`
  first, so dart frontier, consecutive-edge frontier, tail coverage of every
  concrete unbounded-frontier carrier vertex, period `>= 3`, and cyclic carrier
  coverage are no longer independent premises on that route.  The exact
  remaining premise on this CX cut is repeated-tail exterior separation for the
  selected orbit produced by
  `S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw`.
- DYN seed-parametric cut:
  `exists_selectedRawFaceSuccOrbit_sourceRows_of_seed_edgeFrontier_tailCoverage_localTwoGerm_directCyclic_20260520dyn`
  and
  `exists_selectedRawFaceSuccOrbit_sourceRows_of_seed_dartFrontier_tailCoverage_localTwoGerm_directCyclic_20260520dyn`
  keep the supplied `UnboundedExteriorFrontierSeed inputs`, selected local
  edge rows, start dart, and geometric raw `faceSucc` orbit visible while
  filling `RawFaceSuccOrbitSourceRows`.  The only exposed fields are local
  two-germ rows, selected raw frontier propagation, raw-tail coverage of every
  unbounded-frontier carrier vertex, and repeated-tail separation.  The
  consecutive-edge frontier, period `>= 3`, frontier-iff-tail, and cyclic
  carrier coverage fields are derived internally from the same selected raw
  orbit.  The erased projection
  `exists_rawFaceSuccOrbit_sourceRows_of_seed_dartFrontier_tailCoverage_localTwoGerm_directCyclic_20260520dyn`
  is available for downstream consumers that do not need the selected seed
  witnesses.
- S2-D may compose only after those source rows are proved from inputs.

### Demoted: Reducer-Only Carrier Routes

Theorems that consume `ExteriorFrontierCarrierRows`,
`ActualBoundaryCycleFrontierEquivalenceRows`, or pointwise
`BoundaryVertexExteriorSectorRowsAt` are useful checked consumers.  They are not
live source progress because their hypotheses already contain the missing
exterior boundary content.

Status: keep as downstream support, but do not claim new work in this shape.

### Demoted: Induced Frontier Graph

The graph induced on all graph vertices lying on the exterior frontier is not a
valid boundary cycle source.  Boundary chords can create degree greater than
two.  The live carrier must use actual exterior frontier edges, including
open-segment frontier membership.

Status: forbidden for S2 source construction.

### Demoted: All-Adjacent Frontier Endpoint Closure

The following source shape is too strong from bare
`FinitePlanarOuterComponentInputs C`:

```lean
AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs
```

The same warning applies to an unconditional

```lean
AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs
```

Both quantify over arbitrary adjacent graph vertices whose embedded points are
on the exterior frontier.  A boundary chord can satisfy those endpoint
hypotheses while its open segment lies inside the drawing, not on the unbounded
exterior boundary.  The two-triangle triangular-lattice strip is the model
obstruction: an interior diagonal connects two exterior frontier vertices but is
not part of the outer boundary.

Correct use:

```lean
e in unboundedFrontierEdgeSet C inputs
  -> endpoint closure for the closed segment of e
```

The checked project theorem currently available is:

```lean
closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource
```

The direct selected-carrier API is also checked:

```lean
SelectedUnboundedFrontierEdgeEndpointClosureSource
selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition
```

Status: selected-edge endpoint closure is checked support; the unfinished task
is to produce the selected exterior carrier/orbit from inputs.

### Demoted: Convex Hull Or Girth Cycle

Convex hull edges need not be unit-distance graph edges.  A canonical or girth
unit cycle need not be the unbounded exterior boundary.

Status: forbidden unless the exact selected cycle is proved to be the
unbounded exterior boundary, which returns to the live S2 source theorem.

### Demoted: Whole Drawing Complement

The drawing complement may have bounded components.  S2 is about the unbounded
component:

```lean
unboundedExteriorComponentRows C inputs
```

Status: use only the unbounded exterior component as exterior.

### Demoted: Orientation-Free FaceSucc Source

The live raw orbit is the selected exterior-oriented geometric face-successor
orbit.  Orientation-free routes are too strong or force dead residuals.

Status: keep old theorems as helper erasers only when their premises are
input-proved through the selected exterior route.

## Research Checklist For Any S2 Worker

Before editing:

```powershell
rg -n "boundaryVertexExteriorSectorRows_of_inputs|BoundaryFreeNoThirdGermSource|UnboundedExteriorFrontierComponentTopologySourceRows|RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource" ErdosProblems1066/Swanepoel TASK.md proof_workings
rg -n "sorry|admit|axiom|constant|unsafe|opaque|implemented_by|native_decide|trustCompiler|ofReduceBool" ErdosProblems1066/Swanepoel --glob "*.lean"
```

When searching Mathlib or project APIs:

- Search for exact local theorem names first.
- Then search by structure field names.
- Then search by concepts: `frontier`, `connectedComponentIn`,
  `IsPreconnected`, `SimpleGraph.Connected`, `Walk`, `IsCycle`, angular order,
  open segment, closed segment, and finite union compactness.
- Prefer project-local APIs over importing broad new topology unless the
  existing owner file already uses that namespace.

Before marking progress:

- The owned declaration must build in its owner module.
- The proof must not introduce a new source package whose fields are the same
  missing S2 theorem under different names.
- The route must not rely on a final boundary cycle unless the same proof has
  constructed it from `FinitePlanarOuterComponentInputs C`.
- Update `../TASK.md` only when a source row is actually proved, sharply
  reduced to a strictly smaller source row, or a route is ruled circular.

### 2026-05-20 raw face-orbit seed-visible reduction

Claim `S2-agent-20260520-raw-face-orbit-source` is completed as a strict
seed-visible reducer in `S2SeededRawOrbitSource.lean`.

New checked declarations:

```lean
SelectedSeededRawFaceSuccOrbitSourceRows
SelectedSeededRawFaceSuccOrbitSourceRows.toSelectedRawTailCoverageSourceRows
SelectedSeededRawFaceSuccOrbitSourceRows.frontier_iff_tail
SelectedSeededRawFaceSuccOrbitSourceRows.toRawFaceSuccOrbitSourceRows_of_cutPartitions
SelectedSeededRawFaceSuccOrbitSourceRows.existsRawFaceSuccOrbitSourceRows_of_cutPartitions
SelectedSeededRawOrbitRepeatedTailCutPartitions
S2_agent_20260520_selectedSeededRawFaceSuccOrbitSourceRows_of_connectedRawOrbitSourceRows
exists_rawFaceSuccOrbit_sourceRows_of_connectedRawOrbitSourceRows_seededCutPartitions_20260520
```

The constructor chooses a genuine `UnboundedExteriorFrontierSeed`, turns it
through
`exists_geometricRawFaceSuccOrbitSeed_of_unboundedExteriorFrontierSeed_localSectorRows`
into an exterior-oriented start dart, and keeps the seed edge/local rows in
the package.  From the selected geometric raw `faceSucc` orbit it derives:

- dart-edge and consecutive-tail frontier rows,
- actual `unboundedFrontierEdgeSet` membership for every raw consecutive edge,
  up to symmetry,
- raw predecessor/successor nonbacktracking from local-sector rows,
- frontier-tail coverage of every concrete unbounded-frontier carrier vertex,
- period `>= 3` and cyclic carrier coverage.

The only exposed residual for `RawFaceSuccOrbitSourceRows` is now
`SelectedSeededRawOrbitRepeatedTailCutPartitions`, i.e. repeated-tail cut rows
on the same selected seed orbit.  The route does not use final boundary
cycles, induced frontier graphs, convex hull shortcuts, identity angular
order, all-adjacent endpoint/no-chord rows, or synthetic enclosures.

Verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
```

with the pre-existing seeded-file `simpa` style warning.

## Claim Template

Use this format in `../TASK.md` for new S2 work:

```text
- Claim: `S2-...`.
  Owner: ...
  Role: source theorem prover / route verifier.
  Scope: owner file(s).
  Status: active.
  Source task: S2-A / S2-B / S2-C / S2-D.
  Deliverable: exact theorem name.
  Immediate premise policy: any missing premise is proved in this claim or the
    claim is rewritten as that premise.
  Verification gate: targeted owner build command and touched-file forbidden
    token scan.
```

## 2026-05-20 Safe Local-Radius Consumer Refresh

The current preferred W32 route is now the local-radius aligned-K route, not
the older arbitrary-radius `SelectedNeighborLocalExteriorPointSectorRows`
route.

Checked W32 consumers:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborOrder_safeLocalThirdGerm_20260520

minimalFailureExactActualTopologyFieldsTarget_of_janiszewski_selectedNeighborSplit_safeLocalThirdGerm_20260520
```

These consume:

```lean
unboundedExteriorFrontierCycleRows_of_finiteDrawingNontrivialRelativeClopen_selectedNeighborOrder_safeLocalThirdGerm_20260520
```

through the safe local-radius source:

```lean
SelectedNeighborThirdGermLocalExteriorPointSectorRows
S2_codex_20260520_selected_third_germ_local_sector
```

Live source focus:

```lean
SelectedNeighborCutPartitionGeometricOrderSource
```

Equivalently, prove its two halves:

```lean
UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows
UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
```

Do not re-route through `SelectedNeighborLocalExteriorPointSectorRows`,
`BoundaryFreeLocalSectorGeometricAngularSource` as a source-level theorem,
`AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource`,
`AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource`, endpoint-only
successor wrappers, final boundary-cycle rows, actual-boundary equivalence
rows, induced frontier graphs, arbitrary carrier/cycle assumptions, synthetic
enclosure, or identity angular order.

## 2026-05-20 Integration Gate Refresh

Checked after pruning the stale Hubble worker:

```text
lake build ErdosProblems1066.Swanepoel.GeometricRotationSystem
lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

All three pass on the pinned Lean 4.28 toolchain.  The touched S2 owner files
also pass the forbidden-token scan for `axiom`, `sorry`, `admit`, `unsafe`,
`opaque`, `#check`, `#print`, and `#eval`.

The live proof obligation is unchanged:

```lean
SelectedNeighborCutPartitionGeometricOrderSource inputs
```

The current decomposition is:

```lean
UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource C inputs
```

for the selected cut-partition half, plus genuine

```lean
GeometricRotationSystem.GraphVertexAngularNoBetweenRows
```

or equivalent sorted index rows for the same selected heads.  These must still
come from `FinitePlanarOuterComponentInputs C`, not from a completed boundary
cycle or a synthetic carrier.

Scout results after the reducer:

- Deleted-neighbour source route:
  `BoundaryFreeLocalNoThirdGermSourceRows inputs` erases to local-sector rows,
  which erase to
  `UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource C inputs`.
  The missing theorem should live in `S2BoundaryFreeRawSource.lean` and prove
  the local no-third-germ rows directly from `FinitePlanarOuterComponentInputs C`
  or expose the exact smaller finite-drawing/local-topology lemma.
  Existing reducer note: `BoundaryFreeLocalNoThirdGermSourceRows.ofNeighborPairRows`
  already proves the local no-third-germ rows from
  `forall a, UnboundedFrontierCarrierNeighborPairAt inputs a`, so do not
  duplicate that reducer.  If the direct source is too hard, the sharper
  remaining source is the actual selected neighbor-pair row family from
  `FinitePlanarOuterComponentInputs C`.
  Newer reducer note: `boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource`
  now reduces the same local source to
  `UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`.
  In `ExteriorComponentTopology.lean`,
  `unboundedFrontierCarrierNeighborPairCutPartitionInputSource_of_localTwoGermRows`
  reduces that source further to
  `forall a, UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a`.  Thus the
  current sharpest local S2-A leaf is the actual local two-germ theorem at every
  unbounded-frontier vertex, from `FinitePlanarOuterComponentInputs C`.
  Checked reducer, 2026-05-20:
  `S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows`
  now sends that same local two-germ family directly to
  `UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs` via
  the local-sector/cut-partition erasers; targeted
  `lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`
  passed.
  Checked reducer, 2026-05-20:
  `S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource`
  proves the pointwise local two-germ family from
  `UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`.  It
  first erases the sharp cut-partition input source to actual carrier-neighbour
  rows, then uses the existing local-star/unbounded-frontier-edge argument in
  `localTwoGermRows_of_neighborPairRows`; targeted
  `lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`
  passed.  The remaining unproved input-level source is now exactly
  `UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`.
- Selected angular-order route:
  selected cut-partition rows do not imply angular consecutivity by themselves.
  The same selected heads still need a real non-wrap
  `GeometricRotationSystem.GraphVertexAngularNoBetweenRows` row or equivalent
  `UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows`, obtained
  from the sorted `geometricOutgoingDartList`, not identity angular order.
  Checked reducer, 2026-05-20:
  `unboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows_of_graphVertexAngularNoBetweenRows`
  and
  `S2_worker_20260520_selected_geometric_index_source_of_graphVertexAngularNoBetweenRows`
  prove the primitive index residual from honest selected-head
  `GraphVertexAngularNoBetweenRows`, using the actual
  `unboundedFrontierEdgeSet` incidences to supply unit-distance adjacency and
  the existing sorted-list no-between/index theorem in
  `GeometricRotationSystem`.  The remaining source is exactly those
  pointwise selected-head angular no-between rows from
  `FinitePlanarOuterComponentInputs C`.
  Checked reducer, 2026-05-20:
  `unboundedFrontierCarrierSelectedNeighborGraphVertexAngularNoBetweenRows_of_geometricOrderRows`
  and
  `S2_worker_20260520_selected_head_angular_no_between_of_indexRows`
  prove the selected-head
  `forall a, GeometricRotationSystem.GraphVertexAngularNoBetweenRows C a.1
  (selectedRows.selectedNeighborRows a).left
  (selectedRows.selectedNeighborRows a).right` source from the same selected
  cut-partition rows plus the primitive genuine sorted-list index residual.
  This is the reverse checked handoff: actual `unboundedFrontierEdgeSet`
  incidences stay in the cut-partition source, while angular consecutivity is
  supplied only by the real `geometricOutgoingDartList` index rows.
  Checked reducer, 2026-05-20:
  `GeometricRotationSystem.geometricOutgoingDartList_no_between_of_graphVertexGeometricAngularNeighborSelectionRow`
  turns a pointwise
  `GraphVertexGeometricAngularNeighborSelectionRow` into the exact outgoing
  list no-between row over `geometricOutgoingDartList`.  The route-facing
  reducers
  `S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute_of_graph_vertex_geometric_order_rows`,
  `S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_unreachableAfterDeleteRoute_of_graph_vertex_geometric_order_rows`,
  and
  `S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_family_for_unreachableAfterDeleteRoute_of_graph_vertex_geometric_order_rows`
  lift that pointwise row to the current W32 selected-head outgoing-list
  source.  The remaining S2-C leaf is therefore the genuine pointwise
  geometric-neighbour selection row for the selected heads; the outgoing-list
  no-between erasure is checked.

## 2026-05-20 Local And Raw Residual Refresh

The checked local bridge now includes:

```lean
S2_dyn_20260520_boundaryfree_localTwoGerm_bridge
```

in `ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean`.  It composes:

```lean
unboundedFrontierCarrierNeighborPairCutPartitionInputSource_of_localTwoGermRows
boundaryFreeLocalNoThirdGermSourceRows_of_neighborPairCutPartitionInputSource
```

so `BoundaryFreeLocalNoThirdGermSourceRows inputs` follows from the pointwise
actual local two-germ family.  This is a strict reducer only; the S2-A input
leaf remains the actual local two-germ source at every unbounded-frontier
vertex.

Aquinas' read-only audit sharpened that leaf to the source consumed by:

```lean
localTwoGermRows_of_boundaryFree_twoSelectedEdges_noThirdGerm_source
```

Equivalently, for each
`a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}`, prove two
distinct selected incident `unboundedFrontierEdgeSet` heads and the local
no-third-germ row for nearby exterior-frontier points in incident
`vertexIncidentGermW3` sectors.  The stronger structured surface already in
`S2LocalTwoGermAssembly.lean` is:

```lean
LocalRadiusSelectedEdgeSourceRows inputs
```

which erases to local-sector rows via
`S2_dyn_20260520_local_radius_selected_edge_source`.

### 2026-05-20 Local Incident Germ Membership Reduction

The local-star/frontier part of the S2-A leaf is now separated in
`ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean`:

```lean
unboundedFrontierEdgeSet_or_symm_of_local_incident_frontier_germ
localIncidentGermFrontierEdgeMembershipRows_of_inputs
```

These prove from bare `FinitePlanarOuterComponentInputs C` that, after
shrinking to the graph-vertex isolation radius at an unbounded-frontier vertex,
any noncenter exterior-frontier point in an incident `vertexIncidentGermW3`
promotes that incident edge to `unboundedFrontierEdgeSet` in one orientation.
The existing selected-neighbour/local-radius rows now reuse this fact.

Remaining blocker for
`boundaryFree_twoSelectedEdges_noThirdGerm_source_of_inputs`: choose the two
actual selected incident `unboundedFrontierEdgeSet` heads from bare inputs and
prove they exhaust the concrete carrier neighbours.  The all-radius no-third
source is still stronger than the current local drawing API; the checked bare
input result is local-radius only.

Kant's S2-C audit sharpened the raw `faceSucc` residual to:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricTripleIndexNoOrbitSource
```

This is the sorted-list triple-index row: at each selected successor tail, the
selected left head, selected `faceSucc` head, and selected right head must be
entries `i`, `i+1`, and `i+2` of the genuine
`geometricOutgoingDartList`.  It feeds the checked chain:

```lean
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_of_tripleIndex
S2_dyn_20260520_successor_tail_geometric_rows
rawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource_of_successorTailGeometricRows
S2_dyn_20260520_sorted_between_source
rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_selectedNeighbor_pointThirdGerm_sortedBetween_20260520
unboundedExteriorFrontierCycleRows_of_finiteDrawingAlignedK_selectedNeighbor_pointThirdGerm_sortedBetween_20260520
```

Boole's local-star scout confirms the shortest checked S2-A route through
existing APIs:

```lean
forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
  UnboundedFrontierCarrierNeighborPairAt inputs a
```

This feeds either:

```lean
S2_agent_local_two_germ_neighbor_only_20260520ax
S2_dyn_20260520_inhabit_local_radius_selected_edge_rows
```

The local topology ingredients already available for that route are:

```lean
exists_ball_forall_unboundedExterior_frontier_mem_incident_inOpenSegment_of_vertex_ne
interiorFrontierEdgeCarrierMembershipSource_of_frontier_edge_point
exists_ball_forall_graph_vertex_eq_of_mem_ball
exists_ball_forall_unboundedExterior_frontier_mem_vertexIncidentGermW3
unboundedFrontierCarrierLocalTwoGermRowsAt_of_no_third_germ
```

So the real remaining S2-A proof work is choosing the two actual selected
unbounded-frontier carrier neighbours at each frontier vertex and proving that
every other carrier neighbour is excluded by the local frontier/star topology.

Ramanujan added the checked reverse reducer:

```lean
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricTripleIndexNoOrbitSource_of_successorTailGeometricRows
S2_dyn_20260520_successor_tail_triple_index_source
```

Thus the one-index triple wrapper is no longer the live S2-C leaf.  The live
raw `faceSucc` source is again the genuine successor-tail geometric row:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
```

Concretely, at each selected successor tail, produce the two
`GraphVertexGeometricAngularNeighborSelectionRow`s with the selected
`faceSucc` head as their shared middle dart, plus the index-chain equality.

Noether added the next strict reducer:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricNoBetweenRowsNoOrbitSource
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_of_noBetweenRows
S2_dyn_20260520_successor_tail_geometric_row_source
```

and the sorted-list uniqueness helper:

```lean
graphVertexGeometricAngularNeighborSelectionRow_index_succ_eq_of_shared_middle
```

So the live S2-C residual is now the exact no-between source.  At each selected
successor tail, prove:

```lean
GraphVertexAngularNoBetweenRows C succ.tail (left a) succ.head
GraphVertexAngularNoBetweenRows C succ.tail succ.head (right a)
```

together with the three incident `GraphBridge.UnitDistanceAdj` facts.  This is
stronger than the existing strict inequalities: it must also rule out any
intermediate outgoing dart in the genuine sorted list.

Feynman closed this no-between residual one level further by adding:

```lean
graphVertexAngularNoBetweenRows_left_subinterval
graphVertexAngularNoBetweenRows_right_subinterval
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricNoBetweenRowsNoOrbitSource_of_localAngularStrictOrder
S2_dyn_20260520_successor_tail_noBetween_source
```

This reduces the selected successor-tail no-between rows to the honest pair:

```lean
BoundaryFreeLocalSectorGeometricAngularSource inputs
RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource inputs
```

Avicenna's read-only route check found no direct non-circular existing theorem
that supplies the no-between rows outright.  The current live S2-C leaf is
therefore the strict successor-tail order row for the selected `faceSucc` head,
which should be obtained from the genuine sorted `geometricOutgoingDartList`
or an already checked selected-neighbour geometric-order/index source, not
from endpoint closure, final-cycle rows, arbitrary carrier rows, synthetic
enclosures, or identity angular order.

Huygens added the checked composer:

```lean
S2_dyn_20260520_strict_to_successorTail_geometric_composer
```

It proves:

```lean
BoundaryFreeLocalSectorGeometricAngularSource inputs
+ RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource inputs
    (localAngularCarrierLeft localAngularSource)
    (localAngularCarrierRight localAngularSource)
-> RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource inputs
    (localAngularCarrierLeft localAngularSource)
    (localAngularCarrierRight localAngularSource)
```

by composing `S2_dyn_20260520_successor_tail_noBetween_source` with
`S2_dyn_20260520_successor_tail_geometric_row_source`.  The owner-file check
`lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean`
passes with the existing seeded-file style warning.

Kierkegaard confirmed the strict-order residual also follows from the existing
successor-tail geometric rows by the already checked path:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
-> RawOrbitIteratedFaceSuccHeadLocalAngularSortedBetweenNoOrbitSource
-> RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
```

The selected-neighbour index rows and raw-orbit nonwrap rows remain pairwise;
they do not by themselves construct the three-term row
`left, succ.head, right`.

Curie and Boyle both point the shortest W32-facing route back to the local
selected-neighbour leaf, not the raw `faceSucc` branch.  The current best
source target is:

```lean
selectedNeighborCutPartitionGeometricOrderInputSource_of_inputs
```

equivalently:

```lean
forall a, Nonempty
  (SelectedNeighborCutPartitionGeometricOrderInputRowsAt inputs a)
```

This packages the two actual selected `unboundedFrontierEdgeSet` carrier
neighbours plus their genuine adjacent positions in the sorted outgoing-dart
list.  The live W32 chain is:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide
+ UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
+ selected-head GraphVertexAngularNoBetweenRows
+ no-cut rows
-> minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_neighborPairCutPartition_angularNoBetween_20260520
```

The active shared-workboard owners are now Dirac for the relative-clopen
topology leaf, Confucius for the neighbour-pair cut-partition leaf, and Hegel
for the matching selected-head angular leaf.

Support scouts sharpened those three leaves:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
```

is the non-circular topology leaf.  It feeds the existing Janiszewski reducer
chain to:

```lean
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesRelativeClopenKSide
```

For the carrier-neighbour lane, the smallest honest pointwise theorem is:

```lean
theorem unboundedFrontierCarrierNeighborPairCutPartitionRowsAt_of_inputs
    {C : _root_.UDConfig n}
    (inputs : FinitePlanarOuterComponentInputs C)
    (a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs}) :
    UnboundedFrontierCarrierNeighborPairCutPartitionRowsAt inputs a
```

It must choose two genuine incident `unboundedFrontierEdgeSet` heads and prove
any third concrete carrier neighbour yields
`Nonempty (CutVertexInterface.CutVertexPartition C)`.  Routing through
`localTwoGermRows` to prove this source would be circular, because the repo
already has the reverse reducer from the cut-partition source to local
two-germ rows.

For the angular lane, the larger bundled
`SelectedNeighborCutPartitionGeometricOrderInputRowsAt` is still more than the
W32 consumer needs, but selected cut rows alone do not determine angular
consecutivity.  The corrected target is the matching selected-cut-row
no-between family with a separate genuine sorted outgoing-list index premise:

```lean
theorem S2_dyn_20260520_selected_head_angular_rows_of_neighborPairCutPartitionInputSource_indexRows
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (cutSource :
      UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)
    (indexRows :
      let selectedRows :
          UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
        S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
          (C := C) (inputs := inputs)
          (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
            (C := C) (inputs := inputs) cutSource)
      UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
        selectedRows) :
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
      GeometricRotationSystem.GraphVertexAngularNoBetweenRows
        C a.1
        (selectedRows.selectedNeighborRows a).left
        (selectedRows.selectedNeighborRows a).right
```

This is exactly the angular premise consumed by
`unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_neighborPairCutPartition_angularNoBetween_20260520`.

2026-05-20 local-radius pruning: the local selected-edge branch has been
strictly reduced past metric radii.  The checked chain is:

```lean
LocalSelectedIncidentEdgePairSourceRows
  -> localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
  -> S2_agent_20260520_local_radius_source
  -> S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
```

The live S2-A residual is now pointwise selected carrier incidence only:
choose the two incident `unboundedFrontierEdgeSet` heads at each
`a : {v // v ∈ unboundedFrontierVertexSet C inputs}` and prove every selected
incident head is one of them.  The finite drawing vertex-isolation radius and
nearby-germ promotion to `unboundedFrontierEdgeSet` are no longer source
leaves.

2026-05-20 angular/index pruning: the selected-neighbour geometric-order
branch has also been reduced to the pointwise combined input row:

```lean
SelectedNeighborCutPartitionGeometricOrderInputSource
  -> selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
  -> S2_agent_20260520_indexrows_family_from_selected_neighbor_inputSource
```

This preserves the dependency that the cut rows and angular rows name the same
selected heads.  The live S2-C residual is now to construct the pointwise
`SelectedNeighborCutPartitionGeometricOrderInputRowsAt` rows themselves:
selected incident frontier edges, third-neighbour cut partitions, and adjacent
positions in the genuine sorted outgoing-dart list.
Newton confirmed the no-index version is underpowered: the cut source names
two carrier heads and third-neighbour cut partitions, but it contains no
genuine sorted outgoing-dart/angular order.  Hegel added the checked `_indexRows`
version above in `S2SeededRawOrbitSource.lean`.

Dirac and Confucius added strict reductions on the other two live leaves:

```lean
S2_codex_20260520_relative_clopen_side_source_final
S2_codex_20260520_neighbor_pair_cutpartition_final
```

Dirac reduces the relative-clopen K-side source to the sharper
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`.
Confucius reduces the neighbour-pair cut-partition source to actual carrier
neighbour rows plus `LocalRadiusSelectedEdgeSourceRows`.  The remaining active
source leaves are therefore:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded
actual carrier-neighbour / local-radius selected-edge source
selected-neighbour geometric-order index rows for the same selected heads
```

Hilbert added the checked projection from the pointwise combined
selected-neighbour geometric-order source:

```lean
selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
S2_agent_20260520_indexrows_from_selected_neighbor_inputSource
S2_agent_20260520_indexrows_family_from_selected_neighbor_inputSource
```

This means the selected-neighbour/cut/geometric input source now splits into
the selected cut rows and the genuine sorted-list index rows needed by the
angular branch.  It does not prove that input source from bare topology; it
only makes the projection explicit and checked.

Codex-main added W32 consumers for the newest source surface:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborCutPartitionIndex_localIncident_20260520
minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborInput_localIncident_20260520
minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedEdgePair_indexRows_20260520
```

These compose Boyle's frontier-trace compatibility premise with the selected
cut/index route, with Hilbert's pointwise selected-neighbour input projection,
or directly with the selected incident-edge pair source plus genuine selected
index rows.  After the valid-source audit below, these are not live topology
source routes.  The latest `FaceBoundaryTopologySourceW32.lean` owner check
passes.

Descartes reduced the demoted trace compatibility premise one step further:

```lean
S2_dyn_20260520_frontier_trace_connected_worker
```

so the frontier-trace connectedness compatibility premise follows from:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceSubcontinuumBetween
```

Laplace reduced the local selected-edge leaf:

```lean
S2_dyn_20260520_selected_edge_pair_degree_worker
```

so `LocalSelectedIncidentEdgePairSourceRows inputs` now follows from simple
degree two of the actual `unboundedFrontierCarrierGraph`.

Erdos added the checked reduction of the selected incident-edge pair source to
actual carrier degree two:

```lean
localSelectedIncidentEdgePairSourceRows_of_unboundedFrontierCarrierGraph_degree_two
S2_agent_20260520_selected_edge_pair_source_of_carrierGraph_degree_two
S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows
```

Thus the local branch no longer needs a radius source or an independent
selected-edge pair source.  It needs the honest degree-two/two-neighbour theorem
for the selected unbounded-frontier carrier, together with the genuine
geometric-order index row for those same two neighbours.

Helmholtz rechecked the selected-index branch after the local selected-edge
pair route landed.  The next useful theorem is not another local-angular
facade, but the family-level selected-index theorem for the exact selected rows
derived from `LocalSelectedIncidentEdgePairSourceRows`:

```lean
theorem S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
    {C : _root_.UDConfig n}
    {inputs : FinitePlanarOuterComponentInputs C}
    (selectedEdgeRows : LocalSelectedIncidentEdgePairSourceRows inputs) :
    let cutSource :
        UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs :=
      S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
        (C := C) (inputs := inputs) selectedEdgeRows
    let selectedRows :
        UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs :=
      S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
        (C := C) (inputs := inputs)
        (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
          (C := C) (inputs := inputs) cutSource)
    UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows
      selectedRows
```

This theorem must prove adjacent sorted outgoing-dart indices for the same two
selected heads.  It must not recompute heads, use identity order, or replace
the selected carrier with an induced frontier graph.

Hilbert rechecked the generic geometric helper needed for this branch.  No new
helper is needed: `GeometricRotationSystem.lean` already has

```lean
exists_graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
graphVertexGeometricAngularNeighborSelectionRow_of_graphVertexAngularNoBetweenRows
```

These convert actual unit-distance adjacency plus
`GraphVertexAngularNoBetweenRows` into adjacent entries in the genuine
`geometricOutgoingDartList`.  Therefore the selected-index route should focus
on proving the angular no-between row for the selected carrier heads, not on
adding another sorted-list helper.

Carver implemented that exact strict reduction:

```lean
S2_dyn_20260520_selected_head_angular_no_between_source_for_selectedEdgePairRoute
S2_dyn_20260520_selected_index_rows_of_selectedEdgePairRoute
```

The selected-index row for the local selected-edge pair route now follows from
route-specific `GraphVertexAngularNoBetweenRows` for the same selected heads.
This is the correct residual: selected exterior-edge membership by itself does
not rule out an intervening non-frontier unit dart in the full sorted outgoing
list.

Popper redirected the live topology branch away from arbitrary frontier traces.
The whole-frontier relative-clopen source is now reduced by:

```lean
PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction
planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noSubcontinuumObstruction
planarContinuumUnboundedComplementFrontierRelativeClopenKSide_of_noSubcontinuumObstruction
S2_dyn_20260520_whole_frontier_relative_clopen_source
```

So the live S2-B residual is now a no-subcontinuum obstruction for a compact
connected subset of `K` crossing two nonempty closed sides of the actual
unbounded complement-component frontier.  Euler independently confirmed this
is the correct nontrivial source, with the nontrivial relative-clopen theorem
feeding both the relative-clopen and aligned K-split consumers.  The
compatibility-only trace-subcontinuum route remains off the live path.

Epicurus reduced the no-subcontinuum obstruction one step further:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_crossingSubcontinuumForcesBounded
S2_dyn_20260520_whole_frontier_no_subcontinuum_worker
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_janiszewskiBoundaryBumping
```

Thus the S2-B live topology leaf is a boundedness theorem for a compact
connected subcontinuum crossing the two nonempty closed sides of the actual
unbounded complement-component frontier.

Ptolemy rechecked S2-A.  The smallest non-circular local residual is:

```lean
UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
```

It feeds
`unboundedFrontierCarrierNeighborPairRows_of_unreachableAfterDeleteInputSource`
and then `S2_agent_20260520_selected_edge_pair_source_of_neighborPairRows` to
obtain `LocalSelectedIncidentEdgePairSourceRows inputs`.  The degree-two
variant is available through
`unboundedFrontierCarrierGraph_degree_two_of_unreachableAfterDeleteInputSource`
and `S2_dyn_20260520_selected_edge_pair_degree_worker`.

Codex-main added the executable W32 handoff for the current three live S2
leaves:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_unreachable_noIntervening_20260520
```

It consumes:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
forall C inputs, UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
forall C inputs, S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_for_selectedEdgePairRoute ...
S1 noCutRows
```

and routes them through the checked relative-clopen / selected-edge /
selected-index W32 consumers.  This is now the live S2 integration surface.

Codex reduced the selected no-intervening outgoing-dart source to the existing
genuine selected-index row for the same selected-edge-pair route:

```lean
S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_angular_no_between_source_for_selectedEdgePairRoute
S2_dyn_20260520_selected_head_no_intervening_outgoing_dart_source_of_selected_index_rows_for_selectedEdgePairRoute
```

The first theorem erases route-specific `GraphVertexAngularNoBetweenRows` to
the outgoing-dart source by reading each outgoing dart's unit-distance
adjacency.  The second theorem composes that eraser with the already checked
selected-index row builder, so the live no-intervening source now strictly
reduces to the real non-wrap consecutive index row in
`GeometricRotationSystem.geometricOutgoingDartList` for the exact selected
heads from `LocalSelectedIncidentEdgePairSourceRows`.  Targeted build:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
```

passed on 2026-05-20.

Newton reduced the S2-B frontier-trace compatibility surface.  The connected-trace
premise

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected
```

now has checked lower source surfaces:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceSubcontinuumBetween
planarJaniszewskiBoundaryBumpingTraceConnected_of_traceNoClosedSeparation
planarJaniszewskiBoundaryBumpingTraceConnected_of_traceSubcontinuumBetween
S2_agent_20260520_relativeClopenKSide_of_traceNoClosedSeparation
S2_agent_20260520_relativeClopenKSide_of_traceSubcontinuumBetween
```

The compatibility route is:

```text
pairwise compact connected subtrace
  -> no closed separation of T ∩ frontier U
  -> connected trace
  -> subcontinuum-boundedness
  -> relative-clopen K-side
```

This is no longer a live S2-B source theorem: arbitrary compact connected
subcontinua `T ⊆ K` need not have connected or nonseparating
`T ∩ frontier U`.  The owner build for the conditional adapters
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`
passed.

Plato rechecked the current consumer chain after the post-pool integration.
The then-shortest checked W32 compatibility route was:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected
selectedInput : forall C inputs,
  SelectedNeighborCutPartitionGeometricOrderInputSource inputs
S1 noCutRows
  -> minimalFailureExactActualTopologyFieldsTarget_of_frontierTraceConnected_selectedNeighborInput_localIncident_20260520
```

Internally this routes through:

```lean
S2_agent_20260520_planar_continuum_boundary_relativeClopenKSide
selectedNeighborCutPartitionSourceRows_of_geometricOrderInputSource
S2_agent_20260520_indexrows_family_from_selected_neighbor_inputSource
unboundedExteriorFrontierCycleRows_of_relativeClopenKSide_selectedNeighborCutPartitionIndex_localIncident_20260520
```

After the valid-source audit below, the trace residual in this compatibility
route is not a live topology source.  No live route requires the false
all-adjacent endpoint theorem, an induced frontier graph, a synthetic
enclosure, or identity angular order.

Jason completed the boundary-free angular input-source cut for the selected
head route.  The checked declarations are:

```lean
S2_agent_20260520_boundaryFreeAngularSource_of_selectedNeighborGeometricOrder_localPointSector
S2_agent_20260520_boundaryFreeAngularSource_family_of_selectedNeighborGeometricOrder_localPointSector
S2_agent_20260520_localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localPointSector
S2_agent_20260520_localSelectedNeighborRows_family_of_selectedNeighborGeometricOrder_localPointSector
```

This decomposes
`BoundaryFreeLocalSectorGeometricAngularSource inputs` into:

```text
UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows inputs
SelectedNeighborLocalExteriorPointSectorRows selectedRows.toGeometricSelectionInputSource
```

The first input carries the two actual selected `unboundedFrontierEdgeSet`
neighbour heads, their cut-partition/no-cut carrier-neighbour eraser, and the
genuine non-wrap consecutive positions in the sorted outgoing-dart list.  The
second input is the remaining local exterior point-sector theorem for those
same heads.  The owner check
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly`
passed.

Lagrange closed the selected-neighbour input-from-carrier reduction.  The
strict selected-neighbour source now has a direct actual-carrier handoff:

```lean
UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs
  -> SelectedNeighborCutPartitionGeometricOrderInputSource inputs

UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
  -> SelectedNeighborCutPartitionGeometricOrderInputSource inputs
```

The declarations are:

```lean
selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricSelectionInputSource
selectedNeighborCutPartitionGeometricOrderInputSource_of_geometricNeighborSelectionRows
selectedNeighborCutPartitionGeometricOrderInputSource_family_of_geometricSelectionInputSource
selectedNeighborCutPartitionGeometricOrderInputSource_family_of_geometricNeighborSelectionRows
```

Each pointwise output row keeps the same two selected carrier heads, reads the
selected `unboundedFrontierEdgeSet` incidences from the carrier row, discharges
third-carrier-neighbour cut partitions by the carrier `only` field, and reuses
the genuine consecutive index row in the sorted outgoing-dart list.  Targeted
build:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
```

passed on 2026-05-20.

Codex-continuation added the family-level selected incident-edge route.  The
new checked family reducer is:

```lean
S2_codex_cont_20260520_selected_neighbor_input_source_family
```

It composes `LocalSelectedIncidentEdgePairSourceRows` with pointwise genuine
`GraphVertexGeometricOutgoingListNoBetweenRows` for the selected cut rows into
`SelectedNeighborCutPartitionGeometricOrderInputSource inputs`.  The matching
raw-orbit-facing composer is:

```lean
boundaryFreeConnectedRawOrbitSourceRows_family_of_componentTopology_selectedIncidentEdges_geometricOutgoingListNoBetween_sortedBetween_20260520cont
```

That theorem threads the same selected input family through the existing
selected sorted-between successor-edge reducer, keeping the selected
frontier-edge incidences and sorted geometric order tied to the same heads.

Galileo closed the actual-carrier neighbour-selection claim as a checked
strict reducer.  The exact handoff is now:

```lean
UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs
+ UnboundedFrontierCarrierSelectedNeighborGeometricOrderIndexRows selectedRows
-> UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs
```

The declarations are:

```lean
S2_agent_20260520_actual_carrier_neighbor_selection_of_cutPartition_indexRows
S2_agent_20260520_actual_carrier_neighbor_selection_family_of_cutPartition_indexRows
```

The cut-partition rows carry the actual selected `unboundedFrontierEdgeSet`
incidences, while the index rows are the genuine sorted
`geometricOutgoingDartList` positions for the same selected heads.  Targeted
build:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
```

passed on 2026-05-20.

Selected-edge endpoint closure correction, checked 2026-05-20:

```lean
SelectedUnboundedFrontierEdgeEndpointClosureSource C inputs
selectedUnboundedFrontierEdgeEndpointClosureSource_of_definition :
  SelectedUnboundedFrontierEdgeEndpointClosureSource C inputs

selectedUnboundedFrontierEdgeEndpointClosureSource_of_selectedIncidentEdge :
  SelectedUnboundedFrontierEdgeEndpointClosureSource C inputs ->
  ((i, j) ∈ unboundedFrontierEdgeSet C inputs ∨
    (j, i) ∈ unboundedFrontierEdgeSet C inputs) ->
  (Exists fun r : Real =>
    0 < r /\
      forall z : PlanarInterface.Point,
        z ∈ Metric.ball ((canonicalGraph C).point i) r ->
        z ∈ closedSegment ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) ->
        z ∈ closure (unboundedExteriorComponentRows C inputs).exterior) /\
  (Exists fun r : Real =>
    0 < r /\
      forall z : PlanarInterface.Point,
        z ∈ Metric.ball ((canonicalGraph C).point j) r ->
        z ∈ closedSegment ((canonicalGraph C).point i)
          ((canonicalGraph C).point j) ->
        z ∈ closure (unboundedExteriorComponentRows C inputs).exterior)

closedSegmentEndpointClosureSource_of_selectedEndpointClosure_incidentEdge :
  SelectedUnboundedFrontierEdgeEndpointClosureSource C inputs ->
  AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs ->
  AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs
```

Scan shape:

```text
S2LocalTwoGermAssembly.lean:
  no direct reference to AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource
  local third-germ consumers:
    AdjacentFrontierEndpointsIncidentUnboundedFrontierEdgeSource C inputs
    selected incident unboundedFrontierEdgeSet hypotheses
```

Actual raw exterior orbit/carrier source reduction, checked 2026-05-20:

```lean
SelectedRawTailCoverageSourceRows.frontier_iff_tail :
  SelectedRawTailCoverageSourceRows inputs ->
  forall v : Fin n,
    (canonicalGraph C).point v ∈
        frontier (unboundedExteriorComponentRows C inputs).exterior ↔
      Exists fun k : Fin rows.O.period => (rows.O.dart k).tail = v

SelectedRawTailCoverageSourceRows.toActualBoundaryCycleFrontierEquivalenceRows :
  (rows : SelectedRawTailCoverageSourceRows inputs) ->
  (forall {i j : Fin rows.O.period},
    i ≠ j ->
    (rows.O.dart i).tail = (rows.O.dart j).tail ->
      RepeatedExteriorBoundarySeparationRows C
        (fun k : Fin rows.O.period => (rows.O.dart k).tail) i j) ->
  ActualBoundaryCycleFrontierEquivalenceRows C inputs

SelectedRawTailCoverageSourceRows.toExteriorFrontierCarrierRows_nonempty :
  (rows : SelectedRawTailCoverageSourceRows inputs) ->
  (forall {i j : Fin rows.O.period},
    i ≠ j ->
    (rows.O.dart i).tail = (rows.O.dart j).tail ->
      RepeatedExteriorBoundarySeparationRows C
        (fun k : Fin rows.O.period => (rows.O.dart k).tail) i j) ->
  Nonempty (ExteriorFrontierCarrierRows C inputs)

actualBoundaryCycleFrontierEquivalenceRows_of_selectedRawTailCoverage_cutPartitions_20260520 :
  (rows : SelectedRawTailCoverageSourceRows inputs) ->
  SelectedRawOrbitRepeatedTailCutPartitions rows ->
  ActualBoundaryCycleFrontierEquivalenceRows C inputs

exteriorFrontierCarrierRows_nonempty_of_selectedRawTailCoverage_cutPartitions_20260520 :
  (rows : SelectedRawTailCoverageSourceRows inputs) ->
  SelectedRawOrbitRepeatedTailCutPartitions rows ->
  Nonempty (ExteriorFrontierCarrierRows C inputs)

actualBoundaryCycleFrontierEquivalenceRows_of_connectedRawOrbitSourceRows_selectedCutPartitions_20260520 :
  BoundaryFreeConnectedRawOrbitSourceRows inputs ->
  (let selectedRows :=
    S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
      (C := C) (inputs := inputs) rows
   in SelectedRawOrbitRepeatedTailCutPartitions selectedRows) ->
  ActualBoundaryCycleFrontierEquivalenceRows C inputs

exteriorFrontierCarrierRows_nonempty_of_connectedRawOrbitSourceRows_selectedCutPartitions_20260520 :
  BoundaryFreeConnectedRawOrbitSourceRows inputs ->
  (let selectedRows :=
    S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
      (C := C) (inputs := inputs) rows
   in SelectedRawOrbitRepeatedTailCutPartitions selectedRows) ->
  Nonempty (ExteriorFrontierCarrierRows C inputs)
```

2026-05-20 frontier topology valid-source audit:

Demoted compatibility-only trace surfaces:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceConnected
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceSubcontinuumBetween
```

Do not use as live source:

```lean
forall T, IsCompact T -> IsConnected T -> T ⊆ K ->
  (T ∩ frontier U).Nonempty -> IsConnected (T ∩ frontier U)
```

Valid live source shape:

```lean
FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit
+ (forall a : {v : Fin n // v ∈ unboundedFrontierVertexSet C inputs},
    UnboundedFrontierCarrierLocalSectorRowsAt inputs a)
-> S2_agent_20260520_frontier_topology_valid_source
-> UnboundedExteriorActualFrontierPreconnectedSource C inputs
 ∧ UnboundedExteriorFrontierComponentTopologySourceRows inputs
```

Existing whole-frontier alternatives:

```lean
PlanarContinuumUnboundedComplementFrontierConnected
-> S2_dyn_20260520_planar_continuum_frontier_connected
-> UnboundedExteriorActualFrontierPreconnectedSource C inputs

PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
-> S2_dyn_20260520_planar_continuum_frontier_no_closed_separation
-> UnboundedExteriorActualFrontierPreconnectedSource C inputs

FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit
-> actualFrontierPreconnected_of_finiteDrawing_alignedKSplit
-> componentTopologySourceRows_of_finiteDrawingAlignedKSplit_localSectorRows
```

2026-05-20 aligned-K leaf check:

`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit`
does not include `IsConnected K`, so the existing connected-frontier /
no-closed-separation continuum facts do not close that exact planar `Prop`.
At the finite drawing level, `FinitePlanarOuterComponentInputs C` supplies
`embeddedEdgeSet_connected_of_inputs inputs`, and compactness plus
`finiteDrawingUnboundedComplement_frontier_subset_embeddedEdgeSet` handles the
degenerate empty-side split.  Added the checked reducer
`finiteDrawingUnboundedComplementFrontierAlignedKSplit_of_noClosedSeparation`:

```lean
PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
-> FiniteDrawingUnboundedComplementFrontierClosedSeparationForcesAlignedKSplit
```

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
```

2026-05-20 preconnected frontier adapter check:

The live connected/no-closed/aligned-K continuum lane now has a checked
preconnectedness adapter.  New declarations in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`:

```lean
planarContinuumUnboundedComplementFrontierNoClosedSeparation_of_preconnected
planarContinuumUnboundedComplementFrontierConnected_of_preconnected
finiteDrawingUnboundedComplementFrontierAlignedKSplit_of_preconnected
S2_agent_20260520_finite_aligned_K_split_source_of_preconnected
```

This strictly reduces the connected-frontier theorem surface to the
preconnectedness form plus the already checked generic nonempty frontier lemma,
and lets the finite aligned-K split consume
`PlanarContinuumUnboundedComplementFrontierPreconnected` directly.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
```

2026-05-20 selected edge-pair actual-carrier adapter:

The selected local carrier source has a checked direct projection from the
actual carrier/geometric-selection rows:

```lean
localSelectedIncidentEdgePairSourceRows_of_geometricSelectionInputSource
S2_agent_20260520_selected_edge_pair_source_of_geometricSelectionInputSource
S2_agent_20260520_selected_edge_pair_source_of_geometricNeighborSelectionRows
S2_agent_selected_cutpartition_source_of_geometricSelectionInputSource_20260520
```

The first three produce `LocalSelectedIncidentEdgePairSourceRows` from rows
whose pointwise data already contains the two genuine
`unboundedFrontierEdgeSet` incidences and carrier-neighbour completeness.  The
last one projects the same actual carrier source through the existing
local-radius/local-sector eraser to the selected neighbour-pair cut rows.  No
all-adjacent endpoint source, induced frontier graph, synthetic enclosure, or
identity angular order is used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
```

2026-05-20 component-avoidance source:

The Janiszewski component-avoidance source now has a checked strict reducer
from the standard relative-clopen K-side theorem:

```lean
planarJaniszewskiBoundaryBumpingComponentAvoidance_of_relativeClopenKSide
S2_dyn_20260520_component_avoidance_source
```

Given the relative-clopen side `K₁`, the proof views `K₁` as a clopen subset of
the subtype `K`.  A `B` point lies in the clopen complement, so its relative
connected component is contained in that complement; hence it cannot contain an
`A` point, since `A ⊆ K₁`.  This uses only component avoidance/relative
component topology and the Janiszewski relative-clopen K-side source; it does
not use the no-subcontinuum/boundedness reverse chain, final cycles, induced
frontier graph, endpoint shortcuts, or identity angular order.

 Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
```

2026-05-20 component-avoidance finite no-closed handoff:

Claim `S2-codex-cont-20260520-component-avoidance-source` is strictly reduced
in `ExteriorComponentTopology.lean`.

New declarations:

```lean
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiComponentAvoidance
S2_codex_cont_20260520_component_avoidance_source
```

The existing continuation handoff
`S2_codex_cont_20260520_finite_no_closed_separation_source` now factors
through `S2_codex_cont_20260520_component_avoidance_source`.  The new direct
proof specializes component avoidance to the actual finite drawing
`embeddedEdgeSet C`, obtains the hard-case closed aligned `K`-split, and
contradicts connectedness of `embeddedEdgeSet C` for each attempted nonempty
closed split of the selected unbounded frontier.  This lands on
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation` without adding a
W-numbered facade, arbitrary-trace route, synthetic enclosure, or route
ledger.

2026-05-20 local selected incident source family:

Claim `S2-codex-current-20260520-local-selected-incident-source` is completed
as a checked strict reduction.  New declarations:

```lean
S2_codex_current_20260520_local_selected_incident_source_of_carrierGraph_degree_two
S2_codex_current_20260520_local_selected_incident_source_of_neighborPairRows
S2_codex_current_20260520_local_selected_incident_source_of_localSectorRows
ExteriorComponentTopology.S2_codex_current_20260520_local_selected_incident_source
```

The requested family
`forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs` now has
checked reducers from four honest carrier surfaces: actual degree two of
`unboundedFrontierCarrierGraph`, actual carrier neighbour-pair rows, actual
local-sector rows, and `FaceDartOrbitExteriorCarrierRows C inputs`.  The
face-dart family wrapper reuses
`S2_codex_current_20260520_selected_carrier_source`, so the selected heads and
incidences still come from actual `unboundedFrontierEdgeSet` carrier/orbit
data.  The route does not use induced frontier graphs, arbitrary cycles,
all-adjacent endpoint shortcuts, or synthetic enclosures.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" -e "\bconstant\b" -e "\bunsafe\b" -e "\bopaque\b" -e "#check" -e "#print" -e "#eval" -e "implemented_by" -e "native_decide" -e "trustCompiler" -e "ofReduceBool" ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean
```

2026-05-20 local-sector / incident-germ current leaf:

Worker C added the checked current-claim wrapper in
`ErdosProblems1066/Swanepoel/S2BoundaryFreeRawSource.lean`:

```lean
S2_codex_current_20260520_local_sector_residual_of_geometricSelection
S2_codex_current_20260520_incident_germ_residual_reduced_to_local_radius
S2_codex_current_20260520_local_sector_incident_germ_leaf
S2_codex_current_20260520_local_sector_incident_germ_leaf_family
```

This strictly reduces the two residuals exposed by
`S2_codex_current_20260520_boundaryfree_input_reduction_leaf` to the corrected
local package `BoundaryFreeLocalInputSourceReduction`: selected local-sector
rows come from the actual selected carrier/geometric-selection source, while
incident-germ `unboundedFrontierEdgeSet` membership is the local-radius row
proved from finite drawing isolation.  The stronger global
`BoundaryFreeInputSourceReduction` still requires a separate honest global
closed-germ endpoint source; it is not derived here from an all-adjacent
frontier endpoint/no-chord assertion.

Targeted verification passed:

```powershell
lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean
lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean
```

2026-05-20 geometric-angular connected raw-orbit W32 consumer:

Supporting route note: the repeated-tail/orientation branch was sharpened from
abstract selected cut partitions plus raw orientation rows to the selected
repeated-tail witness plus geometric-angular neighbour-selection surface:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricAngularNeighborSelection_20260520
```

This composes:

```lean
finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricAngularNeighborSelection_20260520
```

through the existing W32 finite-planar handoff.  This is checked support for
the raw-orbit program, but it is not the shortest live S2 handoff.

The shortest live handoff remains:

```text
Nonempty (BoundaryFreeConnectedRawOrbitSourceRows inputs)
+ S1 noCutRows
-> minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows
```

The expanded S2 leaves inside `BoundaryFreeConnectedRawOrbitSourceRows` are:

```text
BoundaryFreeNoThirdGermSource inputs
(unboundedFrontierCarrierGraph C inputs).Connected
RawOrbitDartEdgeFrontierSource inputs
```

The endpoint-only boundary-free reducer landed, but it is not yet a live
source leaf without audit: an unconditional adjacent-frontier-endpoint
no-chord row can be false in the presence of boundary chords.  Current work
therefore treats it as a reducer to be repaired or sharpened to selected
`unboundedFrontierEdgeSet`/open-segment-frontier hypotheses before use.

Targeted verification passed for the new W32 consumer:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\FaceBoundaryTopologySourceW32.lean
```

2026-05-20 component-topology family source:

The component-topology field of the compact connected raw-orbit package now has
a checked family-level reducer:

```lean
S2_dyn_20260520_component_topology_family_source
```

It exports both

```lean
forall C inputs, UnboundedExteriorFrontierComponentTopologySourceRows inputs
forall C inputs, (unboundedFrontierCarrierGraph C inputs).Connected
```

from Janiszewski relative-clopen/boundary-bumping rows plus pointwise local
sector rows.  The cover remains by actual selected
`unboundedFrontierEdgeSet C inputs` edges on the actual
`unboundedExteriorComponentRows C inputs` frontier.

Targeted verification reported by the worker:

```powershell
lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-20 local selected no-third source:

The local-selected source row now has a checked local-sector and compact
geometric-neighbour reduction:

```lean
S2_dyn_20260520_local_selected_source
S2_dyn_20260520_local_selected_source_family_of_geometricSelectionInputSource
S2_dyn_20260520_local_selected_source_family_of_geometricNeighborSelectionRows
```

This is intentionally endpoint-free: it builds
`UnboundedFrontierCarrierLocalSelectedNoThirdGermSource C inputs` from actual
selected carrier neighbour/geometric data and local radius rows, not from an
endpoint-only no-chord premise.

2026-05-20 endpoint-only audit repair:

The endpoint-only/no-chord residual was confirmed too strong as a theorem from
`FinitePlanarOuterComponentInputs` because boundary chords may join two
frontier vertices without being exterior boundary edges.  The repaired local
boundary-free route introduces selected-edge-only source rows:

```lean
BoundaryFreeSelectedEdgeOnlyForLocalSectorRows
boundaryFreeLocalNoThirdGermSourceRows_of_localSectorRows_selectedEdges
BoundaryFreeLocalInputSourceReduction
boundaryFreeInputSourceReduction_of_localSelectedNeighborRows_endpointFrontier_20260520
```

Endpoint-only wrappers are now compatibility surfaces only and must not be used
as live finite-input source leaves.  Live work should use selected
`unboundedFrontierEdgeSet` membership or open-segment-frontier hypotheses.

2026-05-20 repeated-tail actual exterior-arc fallback:

The repeated-tail primitive residual on the fallback selected raw-tail route
now reduces to actual exterior-arc rows:

```lean
SelectedRawOrbitRepeatedTailActualExteriorArcRows
selectedRawOrbitRepeatedTailPrimitiveSourceRows_of_actualExteriorArcRows_20260520
selectedRawOrbitRepeatedTailCutPartitions_of_actualExteriorArcRows_20260520
```

This is not the compact shortest S2 handoff, but it keeps the
repeated-tail/orientation branch tied to genuine exterior arcs rather than
primitive black-box row data.

2026-05-20 selected-edge boundary successor source:

The raw dart-frontier branch gained a selected-edge-gated source for boundary
successors:

```lean
SelectedEdgeBoundarySuccessorSource
RawOrbitSelectedEdgeBoundarySuccSource
```

The actual-boundary/sector raw dart-frontier path now consumes actual
`unboundedFrontierEdgeSet` edge data and forward boundary-successor orientation,
not all-adjacent endpoint incidence.

2026-05-20 boundary-free input from geometric selection plus incident germs:

The missing compact-route composer identified by the scout is checked:

```lean
boundaryFreeInputSourceReduction_of_geometricSelection_incidentGermFrontierEdge_20260520
boundaryFreeInputSourceReductionFamily_of_geometricSelection_incidentGermFrontierEdge_20260520
boundaryFreeInputSourceReduction_of_geometricNeighborSelection_incidentGermFrontierEdge_20260520
boundaryFreeInputSourceReductionFamily_of_geometricNeighborSelection_incidentGermFrontierEdge_20260520
```

This produces `BoundaryFreeInputSourceReduction` from actual selected
geometric-neighbour rows plus the genuine incident-germ frontier-edge
membership row.  No endpoint-only/no-chord or all-adjacent endpoint premise is
introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean
```

2026-05-20 geometric-angular rows from successor nonwrap:

The selected raw-orbit geometric-angular residual now has a strict reduction
back to genuine successor nonwrap rows:

```lean
selectedRawOrbitGeometricAngularNeighborSelectionRows_of_geometricSuccessorNonwrapRows
selectedRawOrbitGeometricAngularNeighborSelectionRows_iff_geometricSuccessorNonwrapRows
```

The new geometric helper uses adjacent nonwrap entries in the real
`geometricOutgoingDartList`, not identity angular order.

2026-05-20 compact connected raw-orbit composer:

The compact S2 handoff now has a checked selected-edge-safe family composer:

```lean
boundaryFreeConnectedRawOrbitSourceRows_family_of_geometricSelection_incidentGermFrontierEdge_strictOrder_20260520
```

Inputs:

```text
geometricSelection
incidentGermFrontierEdgeRows
PlanarContinuumUnboundedComplementFrontierPreconnected
RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
```

Output:

```lean
forall C inputs, Nonempty (BoundaryFreeConnectedRawOrbitSourceRows inputs)
```

The boundary-free field goes through
`boundaryFreeInputSourceReductionFamily_of_geometricSelection_incidentGermFrontierEdge_20260520`;
the raw-orbit field goes through the existing selected-neighbour strict-order
route.  No endpoint-only/no-chord or all-adjacent endpoint premise is used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
```

2026-05-20 topology leaf reduced to no-closed-separation:

Claim `S2-agent-20260520-topology-leaf-source` added a checked finite-drawing
reducer from the nontrivial relative-clopen topology leaf to the existing
primitive no-closed-separation theorem, plus a direct cycle-row wrapper from
that primitive topology source and the existing local-sector family.

New declarations:

```lean
finiteDrawingUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noClosedSeparation
S2_agent_20260520_topology_leaf_source_of_noClosedSeparation
unboundedExteriorFrontierCycleRows_of_planarContinuumNoClosedSeparation_localSectorRows
```

The finite-drawing reducer uses connectedness of the actual
`embeddedEdgeSet C` from `FinitePlanarOuterComponentInputs`: a nonempty closed
split of the selected unbounded complement frontier contradicts
`PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`, so the old
generic whole-frontier no-subcontinuum and trace-compatibility detours are no
longer needed on this finite-drawing route.  The cycle-row wrapper then routes
through `S2_dyn_20260520_planar_continuum_frontier_no_closed_separation` and
`unboundedExteriorFrontierCycleRows_of_frontierPreconnected_localSectorRows`.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
```

2026-05-21 selected incident-edge family actual-sector reduction:

Checked theorem-shape additions:

```lean
S2_codex_cont_20260520_selected_incident_edge_family_source_of_boundaryVertexExteriorSectorRows :
  (forall C inputs, Exists B,
    frontier_iff_cycle_vertex C inputs B /\
    forall k, BoundaryVertexExteriorSectorRowsAt inputs B k)
  -> forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs

S2_codex_cont_20260520_selected_incident_edge_family_source_of_actualExteriorSectorInputSourceRows :
  (forall C inputs, Exists B,
    frontier_iff_cycle_vertex C inputs B /\
    Nonempty (ActualExteriorSectorInputSourceRows inputs B))
  -> forall C inputs, LocalSelectedIncidentEdgePairSourceRows inputs

S2_codex_cont_20260520_geometric_neighbor_family_source_of_boundaryVertexExteriorSectorRows_graphVertexGeometricOutgoingListNoBetweenRows :
  boundary-sector selected-incident source
  -> route-specific GraphVertexGeometricOutgoingListNoBetweenRows
  -> forall C inputs, UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs

S2_codex_cont_20260520_geometric_neighbor_family_source_of_actualExteriorSectorInputSourceRows_graphVertexGeometricOutgoingListNoBetweenRows :
  actual-exterior-sector selected-incident source
  -> route-specific GraphVertexGeometricOutgoingListNoBetweenRows
  -> forall C inputs, UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
```

Remaining local/geometric source shape:

```text
forall C inputs, Exists B,
  frontier_iff_cycle_vertex C inputs B /\
  Nonempty (ActualExteriorSectorInputSourceRows inputs B)

+ for the selected heads computed from that source by the current
  selected-edge-pair route:
  forall a, GraphVertexGeometricOutgoingListNoBetweenRows C a left right
```

2026-05-20 crossing-subcontinuum point-source reduction:

Claim `S2-agent-crossing-subcontinuum-source-20260520c` is checked in
`ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean`.

New declarations:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum_of_pointsBetween
S2_agent_crossing_subcontinuum_source_20260520c
```

The target
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum`
now strictly reduces to the point-level source
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween`.
The checked reducer chooses one point from `T ∩ A` and one point from `T ∩ B`,
uses the displayed frontier cover to place both points on
`frontier (connectedComponentIn Kᶜ x)`, and asks only for a compact connected
frontier subset joining those two actual frontier points.  The closed-side,
disjointness, and cover bookkeeping is discharged by the reducer.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-21 current carrier degree-two local source:

Claim `S2-current-carrier-degree-two-source-20260520b` has a checked strict
reduction in `Swanepoel/S2BoundaryFreeRawSource.lean`.

New declarations:

```lean
BoundaryFreeLocalNoThirdGermSourceRows.toNeighborFinsetCardTwo
S2_current_carrier_degree_two_source_20260520b
S2_current_carrier_degree_two_source_family_20260520b
```

The actual `unboundedFrontierCarrierGraph` degree-two row is now sourced from
the honest local exterior-star/no-third-germ package
`BoundaryFreeLocalNoThirdGermSourceRows inputs`.  The proof erases those local
rows to concrete neighbour-pair rows and then uses the existing actual-carrier
degree-two reducer.  It does not use an induced frontier graph, arbitrary
cycle, all-adjacent endpoint closure, identity angular order, or synthetic
rows.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean
```

2026-05-20 carrier degree / cut-partition local source:

Claim `S2-codex-cont-20260520-carrier-degree-cutpartition-source` is closed
as a checked local-source handoff in
`Swanepoel/S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
S2_codex_cont_20260520_carrier_degree_cutpartition_source
S2_codex_cont_20260520_carrier_degree_unreachableAfterDelete_source
S2_codex_cont_20260520_carrier_degree_two_of_local_radius_source
```

The source is the honest pointwise `LocalRadiusSelectedEdgeSourceRows`: two
actual incident `unboundedFrontierEdgeSet` heads at each frontier vertex plus
the local selected exterior-star/no-third-germ radius.  It erases through the
existing local-sector row, then feeds both the sharp cut-partition input
source and the ambient deleted-neighbour source.  The degree-two theorem then
uses the existing `inputs.noCutVertex` eraser through the deleted-neighbour to
cut-partition chain.  No induced frontier graph, arbitrary cycle,
all-adjacent endpoint incidence, synthetic enclosure, or identity angular
order is used.

2026-05-20 current component-avoidance finite no-closed reduction:

Claim `S2-current-component-avoidance-source-20260520a` added the direct
finite-drawing no-closed-separation reducer

```lean
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
```

The proof avoids the relative-clopen loop and does not introduce a new facade:
for a nonempty closed split of the selected unbounded frontier in the actual
finite drawing, both sides lie in `embeddedEdgeSet C`; taking
`T = embeddedEdgeSet C` gives a compact connected subset of the original
compactum meeting both sides, contradicting the component-witness
Janiszewski no-subcontinuum obstruction.

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

Together with the checked equivalence
`planarJaniszewskiBoundaryBumpingComponentAvoidance_iff_noSubcontinuumObstruction`,
the component-avoidance leaf for the live finite no-closed-separation route is
now reduced to the exact remaining theorem shape
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction`
itself, equivalently the original component-avoidance statement.  No arbitrary
trace route, synthetic enclosure row, or relative-clopen detour is used.

2026-05-20 selected-neighbour input-source reduction:

Claim `S2-current-selected-neighbor-input-source-20260520a` is strictly
reduced in `Swanepoel/S2LocalTwoGermAssembly.lean`.

New checked reducers:

```lean
S2_current_selected_neighbor_input_source_20260520a_family_of_selectedIncidentEdgeRows_geometricOrderRows
S2_current_selected_neighbor_input_source_20260520a_family_of_actualCarrierDegreeTwo_geometricOutgoingListNoBetweenRows
```

The first reducer closes the selected-neighbour input family from actual
selected incident `unboundedFrontierEdgeSet` rows plus the genuine selected
head geometric-neighbour row in the sorted outgoing-dart list.  The second is
the actual-carrier degree-two specialization: degree two produces the selected
incident edge rows, and the only remaining order source is the matching
`GraphVertexGeometricOutgoingListNoBetweenRows` family for those same heads.

Exact remaining source row after this cut:

```lean
forall C inputs,
  let selectedEdgeRows :=
    S2_codex_current_20260520_actual_carrier_degree_two_source C inputs
      (hdegree C inputs)
  let cutSource :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      selectedEdgeRows
  let selectedRows :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        cutSource)
  forall a,
    GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
      C a.1 (selectedRows.selectedNeighborRows a).left
        (selectedRows.selectedNeighborRows a).right
```

The reduction uses no induced frontier graph, all-adjacent endpoint claim,
identity angular-order shortcut, or synthetic enclosure row.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
rg -n -e sorry -e admit -e axiom -e unsafe ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
```

The focused scan returned no matches in the Lean owner file.

2026-05-20 selected cut-partition source:

Claim `S2-codex-main-20260520-selected-cutpartition-source` is checked in
`Swanepoel/S2LocalTwoGermAssembly.lean`.

The route decomposition is:

```lean
boundary-free two-selected-edge/no-third-germ rows
-> S2_codex_current_20260520_actual_carrier_degree_two_final_source
-> S2_codex_current_20260520_actual_carrier_degree_two_source_of_final_source
-> S2_codex_current_20260520_selected_cut_partition_source_leaf
-> UnboundedFrontierCarrierSelectedNeighborCutPartitionSourceRows inputs
```

New declarations:

```lean
S2_codex_main_20260520_selected_cutpartition_source_of_boundaryFree_twoSelectedEdges_noThirdGerm
S2_codex_main_20260520_selected_cutpartition_source_family_of_boundaryFree_twoSelectedEdges_noThirdGerm
```

The selected heads stay backed by actual `unboundedFrontierEdgeSet` incidences;
the no-third local germ row is erased through the actual carrier degree-two
route before filling the selected cut-partition source.  No induced frontier
graph, all-adjacent endpoint shortcut, arbitrary cycle, identity angular-order
shortcut, synthetic enclosure, or W facade is introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean
```

2026-05-20 selected-head geometric angular source:

Claim `S2-codex-main-20260520-selected-geometric-angular-source` is checked in
`Swanepoel/S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
unboundedFrontierCarrierSelectedNeighborGeometricOrderRows_of_graphVertexGeometricOutgoingListNoBetweenRows
S2_codex_main_20260520_selected_geometric_angular_source
S2_codex_main_20260520_selected_geometric_order_rows_of_outgoing_list_no_between
```

The selected-head geometric source is now decomposed as:

```text
selected cut-partition rows
+ actual selected unboundedFrontierEdgeSet incidences
+ GraphVertexGeometricOutgoingListNoBetweenRows on geometricOutgoingDartList
-> pointwise Nonempty GraphVertexGeometricAngularNeighborSelectionRow
-> UnboundedFrontierCarrierSelectedNeighborGeometricOrderRows
```

This keeps the order source on the real sorted `geometricOutgoingDartList` and
uses the selected frontier-edge incidences only to discharge the unit-distance
membership hypotheses.  It does not use identity angular order, an induced
frontier graph, an arbitrary cycle, all-adjacent endpoint/chord shortcuts, or
synthetic enclosure rows.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/GeometricRotationSystem.lean
```

2026-05-21 selected incident-edge no-between reduction:

New theorem shapes:

```lean
GeometricRotationSystem.graphVertexGeometricOutgoingListNoBetweenRows_family_of_graphVertexAngularNoBetweenRows
S2LocalTwoGermAssembly.graphVertexAngularNoBetweenRows_of_boundaryFreeGraphVertexAngularNoBetweenRows
S2LocalTwoGermAssembly.graphVertexGeometricOutgoingListNoBetweenRows_of_boundaryFreeGraphVertexAngularNoBetweenRows
S2LocalTwoGermAssembly.S2_codex_cont_20260520_selected_head_graphVertexGeometricOutgoingListNoBetweenRows_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
S2LocalTwoGermAssembly.S2_codex_cont_20260520_selected_head_geometricOutgoingListNoBetween_source_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
S2LocalTwoGermAssembly.S2_codex_cont_20260520_selected_head_geometricOutgoingListNoBetween_source_family_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
S2LocalTwoGermAssembly.S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_boundaryFreeAngularRows
```

Route shape:

```text
LocalSelectedIncidentEdgePairSourceRows inputs
+ matching BoundaryFreeGraphVertexAngularNoBetweenRows
  C a.1 (selectedRows.selectedNeighborRows a).left
      (selectedRows.selectedNeighborRows a).right
-> GraphVertexGeometricOutgoingListNoBetweenRows
   C a.1 (selectedRows.selectedNeighborRows a).left
       (selectedRows.selectedNeighborRows a).right
-> S2_dyn_20260520_selected_head_geometric_outgoing_list_no_between_source_for_selectedEdgePairRoute
-> S2_codex_cont_20260520_geometric_neighbor_family_source_of_selectedIncidentEdgeRows_geometricOutgoingListNoBetween
-> UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
```

Exact remaining source: for the selected heads computed from the selected
incident-edge route, prove the displayed
`BoundaryFreeGraphVertexAngularNoBetweenRows`.  This is the real local angular
no-between source; selected incident-edge/no-third-germ rows alone only rule
out nearby frontier germs and do not exclude an arbitrary outgoing unit-distance
dart in `GeometricRotationSystem.geometricOutgoingDartList`.

2026-05-20 compact connected raw-orbit source leaf:

Linnaeus added the component-topology/boundary-free raw-orbit reducers in
`S2SeededRawOrbitSource.lean`:

```lean
boundaryFreeConnectedRawOrbitSourceRows_of_componentTopology_boundaryFreeInput_selectedSuccessorEdge_20260520
boundaryFreeConnectedRawOrbitSourceRows_of_componentTopology_boundaryFreeInput_selectedNeighborGeometricOrder_successorTailRows_20260520
boundaryFreeConnectedRawOrbitSourceRows_family_of_componentTopology_boundaryFreeInput_selectedNeighborGeometricOrder_successorTailRows_20260520
```

The compact raw-orbit package now reduces to component topology,
`BoundaryFreeInputSourceReduction`, and selected-neighbour successor-tail
`faceSucc` rows.  The selected successor edge is derived internally.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
```

2026-05-20 crossing-subcontinuum boundedness current leaf:

Claim `S2-codex-current-20260520-crossing-subcontinuum-bounded-leaf` is checked
in `ExteriorComponentTopology.lean` as:

```lean
S2_codex_current_20260520_crossing_subcontinuum_bounded_leaf
```

It strictly reduces
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded`
to the component-witness Janiszewski no-subcontinuum obstruction:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

The reducer reuses
`planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_janiszewskiNoSubcontinuumObstruction`.
No W-facing facade, synthetic row, carrier cycle, induced frontier graph,
convex-hull shortcut, or arbitrary boundary-cycle input is introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" -e "\bunsafe\b" -e "\bopaque\b" -e "#check" -e "#print" -e "#eval" ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

The focused module build produced only existing lint warnings, and the
forbidden-token scan returned no matches in the Lean source file.

2026-05-20 Janiszewski no-subcontinuum current leaf:

Claim `S2-codex-current-20260520-janiszewski-no-subcontinuum-leaf` is checked
in `ExteriorComponentTopology.lean` as:

```lean
S2_codex_current_20260520_janiszewski_no_subcontinuum_leaf
```

It strictly reduces
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction`
to the existing boundary-bumping relative-clopen K-side theorem:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
```

The reducer reuses
`planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_relativeClopenKSide`.
The proof core is the checked compact-connected subcontinuum split by the
relative-clopen side `K1` and `K \ K1`; no new topology source predicate is
introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" -e "\bunsafe\b" -e "\bopaque\b" -e "#check" -e "#print" -e "#eval" ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

The focused module build produced only existing lint warnings, and the
forbidden-token scan returned no matches in the Lean source file.

2026-05-20 seed-visible repeated-tail reducer:

Franklin added the checked seed-visible repeated-tail lane in
`S2SeededRawOrbitSource.lean`:

```lean
SelectedSeededRawOrbitRepeatedTailWitnessSource
SelectedSeededRawFaceSuccOrbitSourceRows.repeatedTailExteriorCutRows_of_deletedTailWitnesses
SelectedSeededRawFaceSuccOrbitSourceRows.toActualBoundaryCycleFrontierEquivalenceRows_of_deletedTailWitnesses
SelectedSeededRawFaceSuccOrbitSourceRows.faceSuccRows_of_deletedTailWitnesses
SelectedSeededRawFaceSuccOrbitSourceRows.toFaceDartOrbitExteriorCarrierRows_of_deletedTailWitnesses_complete
SelectedSeededRawFaceSuccOrbitSourceRows.toRawFaceSuccOrbitSourceRows_of_deletedTailWitnesses
SelectedSeededRawFaceSuccOrbitSourceRows.existsRawFaceSuccOrbitSourceRows_of_deletedTailWitnesses
S2_codex_current_20260520_face_dart_carrier_input_leaf_of_deletedTailWitnesses
```

This keeps the seed edge and oriented seed dart visible and reduces the
face-dart carrier input leaf to deleted-tail witnesses for repeated selected
raw tails.  It does not use induced frontier graphs, arbitrary carrier cycles,
or synthetic enclosure rows.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
```

2026-05-20 boundary-free source leaf:

Hooke added the checked selected-carrier local source reduction in
`S2BoundaryFreeRawSource.lean`:

```lean
boundaryFreeNoThirdGermSource_of_localSectorRows_incidentGermFrontierEdge
S2_codex_current_20260520_boundaryfree_source_leaf
S2_codex_current_20260520_boundaryfree_source_leaf_family
```

The boundary-free source now reduces to selected carrier local-sector rows
plus the honest incident-germ `unboundedFrontierEdgeSet` membership row.  No
all-adjacent frontier incidence or endpoint closure shortcut is used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean
```

2026-05-20 selected raw-orbit orientation source leaf:

Leibniz added:

```lean
S2_codex_current_20260520_selected_orientation_source_leaf
```

in `S2SeededRawOrbitSource.lean`.  It reduces both
`SelectedRawOrbitOrientationRows` and
`SelectedRawOrbitGeometricAngularNeighborSelectionRows` to the genuine
nonwrap `SelectedRawOrbitGeometricSuccessorNonwrapRows` source over
`geometricOutgoingDartList`.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\GeometricRotationSystem.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
```

2026-05-20 current raw-orbit orientation faceSucc/list-order source:

Claim `S2-current-raw-orbit-orientation-source-20260520b` is closed as a
checked strict reducer in `S2SeededRawOrbitSource.lean`, with the generic
face-successor/list-order bridge in `GeometricRotationSystem.lean`.

New declarations:

```lean
graphDartArg_lt_of_dartFromGeometricList_getElem_succ
geometricUnitDistanceRotationSystem_faceSucc_eq_and_graphDartArg_lt_of_reverse_getElem_succ_at
selectedRawOrbitOrientationRows_of_geometricSuccessorNonwrapRows_faceSuccListOrder
S2_current_raw_orbit_orientation_source_20260520b
S2_current_raw_orbit_orientation_source_family_20260520b
```

Route impact:

```text
SelectedRawOrbitGeometricSuccessorNonwrapRows
-> SelectedRawOrbitOrientationRows
```

The proof verifies the predecessor/current raw step through the concrete
`geometricUnitDistanceRotationSystem` face-successor list helper and reads the
strict predecessor/successor angular inequality from adjacent entries of the
real `geometricOutgoingDartList`.  It does not use identity angular order,
synthetic rows, final boundary-sector rows, or axioms.

2026-05-20 Janiszewski component-avoidance leaf:

Halley added:

```lean
planarJaniszewskiBoundaryBumpingComponentAvoidance_of_crossingSubcontinuumForcesBounded
S2_codex_current_20260520_janiszewski_component_avoidance_leaf
```

in `ExteriorComponentTopology.lean`.  The topology residual is now the
strictly smaller boundedness source
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded`.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
```

2026-05-20 trace no-closed-separation audit:

`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierTraceNoClosedSeparation`
is not a valid live topology source for arbitrary compact connected
`T ⊆ K`.  The same obstruction as for the trace-connected form applies:
a compact connected subcontinuum of a disk, e.g. a chord, can meet the
unbounded-component frontier in two separated endpoint traces.  The Lean file
therefore keeps this declaration only as a compatibility surface.

Checked conditional reducers in `ExteriorComponentTopology.lean`:

```lean
planarJaniszewskiBoundaryBumpingTraceNoClosedSeparation_of_traceSubcontinuumBetween
planarJaniszewskiBoundaryBumpingTraceConnected_of_traceNoClosedSeparation
planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_frontierTraceNoClosedSeparation
S2_agent_20260520_boundedness_of_traceNoClosedSeparation
S2_agent_20260520_relativeClopenKSide_of_traceNoClosedSeparation
```

These are adapters only; they do not make the arbitrary-`T` trace statement a
source theorem.  The finite-drawing-only replacement route is:

```lean
finiteDrawingUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noClosedSeparation
S2_agent_20260520_topology_leaf_source_of_noClosedSeparation
actualFrontierNoClosedSeparation_of_finiteDrawing_noClosedSeparation
actualFrontierPreconnected_of_finiteDrawing_noClosedSeparation
unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_localSectorRows
```

The exact live topology leaf on this route is
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation` when working
purely at drawing level, or its reusable planar-continuum source
`PlanarContinuumUnboundedComplementFrontierNoClosedSeparation`.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" -e "\bconstant\b" -e "\bunsafe\b" -e "\bopaque\b" -e "#check" -e "#print" -e "#eval" -e "implemented_by" -e "native_decide" -e "trustCompiler" -e "ofReduceBool" ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

The Lean check and targeted module build produced only existing lint warnings;
the focused source-file forbidden-token scan returned no matches.

2026-05-20 current dynamic source reductions:

Topology: Boole the 3rd added

```lean
S2_dyn_20260520_frontier_preconnected_current_source_of_janiszewskiBoundaryBumping
```

in `ExteriorComponentTopology.lean`, reducing the actual-component
preconnected source to

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
```

through the existing actual unbounded exterior adapter
`actualFrontierPreconnected_of_janiszewskiBoundaryBumping`.  The next topology
target is that relative-clopen Janiszewski leaf.

Local/geometric: Lagrange the 3rd added

```lean
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiNoSubcontinuum_geometricNeighborSelectionRows_20260520
```

in `FaceBoundaryTopologySourceW32.lean`, reducing the W32 local/geometric
input from

```lean
UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs
```

to the compact source

```lean
UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
```

via the existing eraser
`UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows.toGeometricSelectionInputSource`.
The next local/geometric target is that compact neighbour-selection row,
ideally reduced to actual carrier neighbour-pair rows plus genuine
`GraphVertexAngularNoBetweenRows` for the same two selected heads.

2026-05-20 local-radius incident-germ cleanup:

Worker Aristotle the 3rd completed the local-radius-safe replacement for the
old global incident-germ surface.  New checked declarations include:

```lean
S2_dyn_20260520_incident_germ_global_source_reduced_to_local_radius

localSelectedNeighborRows_of_selectedNeighborGeometricOrder_localIncidentGermMembership

boundaryFreeLocalInputSourceReduction_of_selectedNeighborGeometricOrder_localIncident_20260520

boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520

boundaryFreeLocalInputSourceReduction_of_geometricNeighborSelection_localIncident_20260520
```

This keeps the global
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` row as compatibility
surface only.  Live local consumers should use the local-radius row
`SelectedNeighborIncidentGermLocalFrontierEdgeMembershipRows` and the new
`BoundaryFreeLocalInputSourceReduction` wrappers.

2026-05-20 current dynamic-worker refresh:

After pruning the stale Planck handle attempt, the current checked S2 surface
is still valid under the pinned toolchain.  Codex-current ran:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly ErdosProblems1066.Swanepoel.S2BoundaryFreeRawSource ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

and the active-owner forbidden-token scan over the S2 source files returned
clean.

The live worker split is:

```text
S2-dyn-20260520-incident-germ-global-source:
  try to close or bypass the selected-edge-gated global incident-germ row.

S2-dyn-20260520-frontier-preconnected-current-source:
  try to close or reduce PlanarContinuumUnboundedComplementFrontierPreconnected.

S2-dyn-20260520-raw-successor-strict-order-source:
  try to close or reduce the strict selected raw faceSucc/geometric-successor
  order source.

S2-dyn-20260520-compact-route-audit-current:
  read-only audit of the shortest non-circular route and stale claims.
```

Important integration note: the file already contains a safer W32 lane
through

```lean
minimalFailureExactActualTopologyFieldsTarget_of_preconnected_geometricSelectionInputSource_20260520
minimalFailureExactActualTopologyFieldsTarget_of_planarNoClosedSeparation_geometricSelectionInputSource_20260520
```

which avoids using the too-strong endpoint-only/no-chord route and does not
need the global incident-germ row directly.  The compact connected raw-orbit
composer remains checked support, but the route auditor should prefer the
shortest non-circular source split that uses only local-radius selected
carrier/geometric-selection rows.

2026-05-20 strict-order leaf reduction:

Worker Lovelace the 3rd completed the strict raw-order task in
`S2SeededRawOrbitSource.lean`.  New checked reducers:

```lean
boundaryFreeConnectedRawOrbitSourceRows_family_of_boundaryFreeInput_preconnected_selectedNeighborGeometricOrder_successorTailRows_20260520

boundaryFreeConnectedRawOrbitSourceRows_family_of_geometricSelection_incidentGermFrontierEdge_successorTailRows_20260520
```

The compact connected raw-orbit route can now take the smaller source:

```lean
RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource
```

for the same selected geometric heads, instead of the broader strict-order
source.  A new dynamic worker is assigned to prove or strictly reduce this
successor-tail geometric row from genuine sorted outgoing-list nonwrap data.

2026-05-20 actual-boundary package W32 consumer:

Codex-main added the package-form W32 consumer

```lean
minimalFailureExactActualTopologyFieldsTarget_of_connectedFrontier_actualBoundaryPackage_20260520
```

in `ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean`.
The live S2 residual surface is now:

```text
PlanarContinuumUnboundedComplementFrontierConnected
+ ActualBoundaryFaceSuccLocalSectorRows
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is only a dependency compression: the package is still honest because it
contains the actual boundary rows, genuine geometric `faceSucc` rows, boundary
orientation in `graphDartArg`, and pointwise local-sector rows for actual
`unboundedFrontierVertexSet` vertices.  It does not use all-adjacent endpoint
closure/incidence, induced frontier graphs, arbitrary carrier cycles, convex
hull vertices, identity angular-order rows, or synthetic enclosure shims.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\FaceBoundaryTopologySourceW32.lean
```

2026-05-20 connected raw-orbit compression:

The package route has been compressed again through checked reducers in
`S2SeededRawOrbitSource.lean` and `GeometricRotationSystem.lean`.

Current live W32 handoff:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260520
```

Current residual surface:

```text
BoundaryFreeConnectedRawOrbitSourceRows
+ SelectedRawOrbitRepeatedTailCutPartitions for the selected raw orbit
+ SelectedRawOrbitOrientationRows for that same selected raw orbit
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

Checked reductions feeding this surface:

```lean
S2_agent_cw_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520cw
selectedRawOrbitRepeatedTailWitnessSource_of_cutPartitions_20260520
selectedRawTailCoverage_repeatedTailExteriorCutWitnessSource_of_cutPartitions_20260520
selectedRawOrbitGeometricSuccessorNonwrapRows_of_orientationRows
selectedRawOrbitGeometricSuccessorNonwrapRows_iff_orientationRows
```

The route remains selected-edge/raw-orbit based.  It does not use
all-adjacent frontier endpoint incidence, induced frontier graphs, arbitrary
cycles, convex hull vertices, identity angular-order rows, or synthetic
enclosure predicates.

Verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

2026-05-20 unconditional-cycle-composer route cut:

Claim `S2-agent-20260520-unconditional-cycle-composer` added a checked direct
boundary-sector composer on the connected raw-orbit lane:

```lean
unboundedExteriorFrontierCycleRows_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation_20260520 :
  BoundaryFreeConnectedRawOrbitSourceRows inputs ->
  (let selectedRows := ... in
    forall {i j : Fin selectedRows.O.period},
      i ≠ j ->
      (selectedRows.O.dart i).tail = (selectedRows.O.dart j).tail ->
        RepeatedExteriorBoundarySeparationRows C
          (fun k => (selectedRows.O.dart k).tail) i j) ->
  (let selectedRows := ... in SelectedRawOrbitOrientationRows selectedRows) ->
  UnboundedExteriorFrontierCycleRows C inputs
```

and the family/W32 consumers:

```lean
finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation_20260520

minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation_20260520
```

The same claim then added the sharper deleted-tail/geometric-successor cut of
this route:

```lean
unboundedExteriorFrontierCycleRows_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_rawOrientation_20260520

finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_rawOrientation_20260520

minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_rawOrientation_20260520

unboundedExteriorFrontierCycleRows_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricSuccessorNonwrap_20260520

finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricSuccessorNonwrap_20260520

minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnesses_geometricSuccessorNonwrap_20260520
```

This composes through
`S2_agent_20260520_boundarySectorRows_of_rawOrbit_localSectorRows`, so the
displayed route no longer needs the intermediate
`ActualExteriorSectorInputSourceRows` package.  The strongest remaining source
signature for this lane is now exactly:

1. `forall C inputs, BoundaryFreeConnectedRawOrbitSourceRows inputs`;
2. for the internally selected raw orbit from (1), pointwise
   `S2RepeatedTailExteriorCutWitnessSource` for every repeated-tail pair;
3. for that same internally selected raw orbit,
   `SelectedRawOrbitGeometricSuccessorNonwrapRows`.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\FaceBoundaryTopologySourceW32.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

2026-05-20 local-sector source family:

The pointwise local-sector branch now has a checked source-family eraser from
the selected exterior-frontier neighbour/geometric-selection rows:

```lean
localSectorRows_of_geometricSelection_localIncident
localSectorRowsFamily_of_geometricSelection_localIncident_20260520
```

This composes the existing selected-neighbour local point-sector proof
`S2_codex_20260520_selected_third_germ_local_sector` with
`localSectorRows_of_selectedNeighborThirdGermLocalExteriorPointSectorRows`.
The local-sector rows therefore come from actual selected
`unboundedFrontierEdgeSet` carrier heads plus genuine geometric neighbour
selection.  This route does not use all-adjacent endpoint closure, an induced
frontier graph, final boundary-cycle rows, or identity angular order.

2026-05-20 local-sector close:

Claim `S2-codex-main-20260520-local-sector-close` is checked in
`Swanepoel/S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
localSectorRows_of_geometricSelection_localIncident
S2_codex_main_20260520_local_sector_close
localSectorRowsFamily_of_geometricSelection_localIncident_20260520
S2_codex_main_20260520_local_sector_close_of_faceSucc_sectorRows
```

The pointwise source leaf
`forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a` now projects
directly from the actual selected carrier-neighbour/geometric-selection input
source.  The same-boundary face-successor/sector-row wrapper feeds that source
from actual boundary-sector rows and genuine geometric rotation order.  No
all-adjacent endpoint closure or induced frontier graph shortcut is used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean
lake env lean ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
```

2026-05-20 Janiszewski relative-clopen finite-drawing specialization:

Claim `S2-agent-20260520-janiszewski-relative-clopen-source` is completed as a
checked strict reducer in `ExteriorComponentTopology.lean`.

New declarations:

```lean
actualFrontierPreconnected_of_janiszewskiBoundaryBumping
unboundedExterior_frontier_noOpenSeparation_of_janiszewskiBoundaryBumping
actualFrontierAlignedKSplit_of_janiszewskiBoundaryBumping
S2_agent_20260520_janiszewski_relative_clopen_source
```

The route now specializes the standard Janiszewski relative-clopen theorem to
the actual finite drawing `embeddedEdgeSet C` and the selected
`unboundedExteriorComponentRows C inputs`: it yields both actual frontier
preconnectedness and the aligned K-split source consumed by the local carrier
rows.  It does not introduce a boundary cycle, induced frontier graph,
arbitrary cycle, synthetic enclosure predicate, convex-hull shortcut, or
identity angular-order shortcut.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\ExteriorComponentTopology.lean
```
