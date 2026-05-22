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

## 2026-05-22 Active S2 Source Route

Current baseline: `S2SeededRawOrbitSource` builds, q37 primitive-to-cut
lowering is checked, and q38/q39/q40 declarations are route infrastructure
rather than live work claims.  q40 endpoint closed-side support remains
audit-sensitive: it is useful only when it feeds the selected raw-orbit source
without using actual-sector rows, finished boundary-cycle rows, or W32 rows as
premises.

The support route currently checked is:

```text
q30 selected seed raw face-successor orbit
+ selected-carrier successor rows
+ finite no-closed/no-open topology rows
+ SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointClosedSeparationSource
-> SelectedRawOrbitCyclicSuccDeletedTailReachableFrontierClosedSeparationSource
-> SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
-> SelectedSeededRawOrbitMinimalDeletedTailSeparation
-> actualExteriorSectorInputSourceRows
```

Useful q39 declarations:

```lean
S2_q39_selectedRawOrbitReachableFrontierClosedSeparationSource_of_endpointClosedSeparation
S2_q39_selectedSeededRawOrbitMinimalDeletedTailSeparation_of_finiteDrawingNoClosed_endpointClosedSeparation
S2_q39ReachableClosedSeparationTopologyPremises
S2_q39_reachableClosedSeparationTopologyPremises_of_traceNoClosedSeparation_outsideAccumulation_20260522
S2_q39_actualExteriorSectorInputSourceRows_family_of_finiteTopologyPackage_geometricSelection_incidentGerm_selectedCarrierRows_reachableClosedSeparation
S2_q39_actualExteriorSectorInputSourceRows_family_of_traceNoClosed_outsideAccumulation_geometricSelection_incidentGerm_selectedCarrierRows_reachableClosedSeparation
```

q40 endpoint closed-side rows are support, not the live source.  The exact
checked endpoint bridge factors through
`SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointFrontierComponentSeparationSource`,
but that component-separation branch is over-strong as a source route; the file
already contains a diagnostic theorem showing it is false if the whole frontier
is preconnected.  Do not make endpoint frontier-component separation the live
proof target.

The live q41 source target is the actual exterior face-orbit theorem:

```lean
forall {n : Nat} (C : _root_.UDConfig n)
  (inputs : FinitePlanarOuterComponentInputs C),
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

Preferred decomposition:

1. construct the q30 selected seed raw geometric face-successor orbit;
2. prove its edge open segments are on the unbounded exterior frontier and its
   tails cover exactly the frontier graph vertices;
3. prove any repeated raw tail gives deleted-tail nonreachability, equivalently
   a cut partition, using the no-cut input;
4. erase the selected raw-tail package to `FaceDartOrbitExteriorCarrierRows`;
5. supply same-boundary angular rows from the genuine geometric successor
   orientation, not global all-outgoing no-between rows;
6. erase the resulting `FaceDartOrbitExteriorCarrierRows` and angular rows to
   `actualExteriorSectorInputSourceRows_of_inputs`.

q41 support now checked: `S2CarrierCutSource.lean` proves the actual
exterior-arc repeated-tail rows imply the q24 cyclic-successor deleted-tail
nonreachability and cut-partition sources:

```lean
S2_q41_rawFaceWalkCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailActualExteriorArcRows
S2_q41_rawFaceWalkCyclicSuccDeletedTailCutPartitionSource_of_repeatedTailActualExteriorArcRows
```

These are support rows for step 3 above.  They do not prove the input-facing
exterior face walk by themselves.

q42 split claims currently pursue the four remaining source directions:
selected raw orbit production in `S2SeededRawOrbitSource.lean`, genuine
geometric orientation in `GeometricRotationSystem.lean` /
`S2ExteriorBoundarySource.lean`, the finite-drawing topology crossing source in
`S2TopologySource.lean`, and local unbounded-frontier carrier rows in
`S2LocalTwoGermAssembly.lean` / `S2CarrierLocalSource.lean`.

q42 topology support now reduces the topology leaf to

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected
```

through:

```lean
S2_q42_noCompactConnectedKCrossing_source_of_kComponentTracePreconnected_20260522q42
S2_q42_finiteDrawing_noClosedSeparation_source_of_kComponentTracePreconnected_20260522q42
S2_q42_finiteDrawing_frontierPreconnected_source_of_kComponentTracePreconnected_20260522q42
S2_q42_finiteDrawing_preconnected_noClosed_source_of_kComponentTracePreconnected_20260522q42
```

q43 topology support further lowers that trace-preconnected leaf to the same
`K` Janiszewski point-between theorem:

```lean
S2_q43_kComponentTracePreconnected_of_kComponentPointsBetween_20260522q43
```

The remaining topology-side source is therefore
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`
unless the route bypasses this branch through a direct exterior face-orbit
producer.

q42 geometric support now gives the exact raw orientation row from genuine
geometric face-successor equalities and strict selected turns:

```lean
S2_q42_geometric_orientation_worker_rawOrientation_of_faceSuccRows_strictSelectedTurns
S2_q42_geometric_orientation_worker_rawOrientation_of_rawFaceSuccOrbit_strictSelectedTurns
```

q42 selected raw-orbit support lowers the raw exterior `faceSucc` source to the
current non-circular leaves:

```lean
S2_q42_rawFaceSuccOrbitSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_orientation_localStrict_localAngular_cyclicSuccCutPartitions
```

Residual leaves for that route are finite no-open separation, frontier vertex
incident selected edge, actual geometric neighbour selection, local
orientation/strict-turn/angular rows, and cyclic-successor cut partitions for
the same selected raw orbit.

q42 local carrier support now lowers actual carrier degree two to the selected
unbounded-frontier edge local-isolation row:

```lean
actualCarrierDegreeTwo_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
S2_q42_local_frontier_carrier_worker_of_selectedEdgeLocalIsolation
S2_q42_local_frontier_carrier_worker_family_of_selectedEdgeLocalIsolation
nonempty_selectedUnboundedFrontierEdgeLocalIsolationSourceRows_iff_actualCarrierDegreeTwo
```

This is not an input-facing proof by itself.  It identifies the local geometric
source still needed from `FinitePlanarOuterComponentInputs C`: select the two
actual exterior-frontier edge germs at each frontier vertex and prove the
no-third-germ/local-isolation radius for selected `unboundedFrontierEdgeSet`
edges.

q43 local-isolation support shows that the local radius/no-third-germ part is
already downstream of selected incident-edge pairs:

```lean
S2_q43_local_isolation_source_worker_of_selectedIncidentEdgePairRows
localRadiusSelectedEdgeSourceRows_of_selectedIncidentEdgePairRows
```

Thus the local source residual is sharpened to actual carrier degree two:

```lean
localSelectedIncidentEdgePairSourceRows_of_inputs
```

or equivalently:

```lean
unboundedFrontierCarrierGraph_neighborFinset_card_two_of_inputs
```

for the actual `unboundedFrontierCarrierGraph C inputs`.  Proving this is the
no-cut/two-connected exterior-boundary step; it must not be replaced by the
induced frontier graph or an arbitrary two-regular spanning cycle.

## 2026-05-22 q39/q38/q37 Checked Support

These are support declarations for the route above, not live tasks or open
agent claims.  Keep q39 endpoint-closed support audit-sensitive until the
current audit settles.

Useful checked q38 declarations:

```lean
S2_q38_selectedSeededRawOrbitMinimalDeletedTailSeparation_of_finiteDrawingNoClosed_reachableClosedSeparation
S2_q38_actualExteriorSectorInputSourceRows_family_of_finiteDrawingNoClosed_exteriorFaceOrbitSeedSource_reachableClosedSeparation_selectedCarrierRows
S2_q38_actualExteriorSectorInputSourceRows_family_of_finiteNoClosedNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_reachableClosedSeparation
S2_q38_rawFaceWalkPairwiseMinimalDeletedTailSeparationSource
S2_q38_repeatedTailExteriorCutRows_of_pairwiseMinimalDeletedTailSeparationSource
S2_q38_deletedNeighborLocalSeparationInputSource_family_of_selectedIncidentEdgePairRows
S2_q38_finiteDrawing_topology_accumulation_sources_of_traceNoClosedSeparation_outsideAccumulation_20260522
```

Useful checked q37 declarations/state:

- Targeted `S2SeededRawOrbitSource.lean` builds after the q37 work.
- The q31/q30 `selectedCarrierRows` wrappers are checked.
- The q37 repeated-tail wrappers strictly lower
  `SelectedSeededRawOrbitMinimalDeletedTailSeparation`, equivalently pairwise
  `RawFaceSuccOrbitRepeatedTailExteriorCutRows`, to
  `SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource` on the same
  selected seed raw orbit.
- The checked q37 primitive/boundary-arc adapters lower
  `SelectedRawOrbitRepeatedTailPrimitiveSourceRows` for the selected raw-tail
  package to the same cyclic-successor nonreachability source, then through
  the q37 actual-sector eraser.
- The selected-carrier angular leaf is discharged by q7/q24 wrappers once
  `selectedCarrierRows` are available.

## 2026-05-22 q32 Route Reductions

Checked topology reduction:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing
-> FiniteDrawingUnboundedComplementFrontierPreconnected
```

via
`finiteDrawingUnboundedComplementFrontierPreconnected_of_finiteClosedSeparationForcesBounded_20260522`
and
`S2_r14_finiteDrawing_frontierPreconnected_of_noCompactConnectedKCrossing_20260522`
in `S2TopologySource.lean`.

Checked exposed-raw-orbit reduction:

```text
componentTopology
+ geometricSelection
+ strictSuccessorOrder
+ minimal deleted-tail separation on the exposed q31 raw orbit
+ successor nonwrap rows on the same orbit
-> actualExteriorSectorInputSourceRows
```

via
`S2_q32_actualExteriorSectorInputSourceRows_family_of_componentTopology_geometricSelection_strictSuccessor_minimalSeparation_nonwrap`.
The local incident-germ leaf is filled by the finite drawing local-isolation
row; no actual-sector rows are used as a premise.

Checked q32 compatibility/source-lowering adapters:

```lean
S2_q32_successorNonwrapRows_and_orientation_family_of_componentTopology_geometricSelection_strictSuccessor_faceSuccTurn
S2_q32_minimalDeletedTailSeparation_family_of_componentTopology_geometricSelection_strictSuccessor_primitiveSourceRows
```

The first turns genuine face-successor turn rows on the exact q32 exposed raw
orbit into successor-nonwrap plus raw orientation.  The second is currently an
identity-style lowering surface for the same minimal-deleted-tail callback, not
a new source theorem.

The seed-visible q31 erasers also now replace explicit raw orientation by
selected actual-carrier face-successor angle rows:

```text
q30 seed-visible raw orbit
+ repeated-tail cut/cut-partition/boundary-arc rows
+ selected actual-carrier faceSucc angle rows
-> actualExteriorSectorInputSourceRows
```

Remaining source-level proof work is the construction of selected geometric
carrier / strict successor data, q31 minimal deleted-tail separation on the
exposed raw orbit, and successor nonwrap / selected actual-carrier angle rows
for that same orbit.  Do not replace these with all-adjacent endpoint rows,
induced frontier graphs, arbitrary cycles, or W-facing composers.

## 2026-05-22 q34 Source Sharpening

Checked topology lowering in `S2TopologySource.lean`:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingWitnessNoClosedSeparation
planarContinuumUnboundedComplementFrontierNoCompactConnectedKCrossing_of_crossingWitnessNoClosedSeparation_20260522q34
S2_q34_noCompactConnectedKCrossing_source_of_crossingWitnessNoClosedSeparation_20260522q34
S2_q34_finiteDrawing_noClosedSeparation_source_of_crossingWitnessNoClosedSeparation_20260522q34
```

This sharpens the topology residual to the local compact-connected crossing
witness used by the no-compact-connected-`K`-crossing target, rather than a
global connectedness-of-`K` premise.

Carrier-cut route map, read-only: the first non-circular source theorem is

```lean
S2_q34_rawOrbit_thirdNeighborMinimalDeletedTailSeparationSource_of_inputs
```

with target shape: construct the same selected raw face-successor orbit,
its edge-frontier and frontier-tail coverage rows, raw predecessor/successor
nondegeneracy, and
`S2_r12_rawFaceWalkThirdCarrierNeighborMinimalDeletedTailSeparationSource`.
Existing r12/r11 reducers then feed
`S2_agent_carrier_cut_source_worker_20260521e32_fieldwise inputs`.

Do not use the boundary-sector or actual-sector erasers as source routes for
this carrier-cut leaf; those are downstream consumers.

## 2026-05-22 q39 Reachable Closed-Separation Source

Checked in `S2SeededRawOrbitSource.lean`:

```lean
S2_q39_selectedRawOrbitReachableFrontierClosedSeparationSource_of_endpointClosedSeparation
S2_q39_selectedSeededRawOrbitMinimalDeletedTailSeparation_of_finiteDrawingNoClosed_endpointClosedSeparation
```

This lowers the q38 reachable-frontier closed-separation leaf to endpoint
closed-separation on the same selected raw orbit.  It is checked support, not
the current live source target while the q41 actual exterior face-orbit route
is active.

Checked topology handshake in `S2TopologySource.lean`:

```lean
S2_q39ReachableClosedSeparationTopologyPremises
S2_q39_reachableClosedSeparationTopologyPremises_of_q38_finiteDrawing_topology_accumulation_package_20260522
S2_q39_reachableClosedSeparationTopologyPremises_of_traceNoClosedSeparation_outsideAccumulation_20260522
```

These expose exactly the finite `noClosed`, finite `noOpen`, and
frontier-incident topology rows needed by the reachable route, without a W32
composer.

The endpoint bridge factors through:

```lean
SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointFrontierComponentSeparationSource
  source.1.toSelectedRawTailCoverageSourceRows
```

which lowers through
`selectedRawOrbitCyclicSuccDeletedTailReachableEndpointClosedSeparationSource_of_endpointFrontierComponentSeparation_20260521r8g`
and then q39's endpoint-closed-separation bridge.  This branch is retained as
support/audit trail only; endpoint frontier-component separation is too strong
to be the live proof target.

The endpoint closed-side row can still be used as a support shape:

```lean
SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointClosedSeparationSource rows
```

for the exact selected raw tail-coverage rows.  Do not open it as the live
source target; use it only if it feeds the actual exterior face-orbit source
without assuming `ActualExteriorSectorInputSourceRows`, boundary-sector rows,
final boundary cycles, or W32 consumers.

Cut-partition shortcut: a cut partition for the same repeated-tail/deleted-tail
configuration still erases to nonreachability via
`selectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource_of_cyclicSuccCutPartitionSource_20260521current6`.

## 2026-05-21 Historical Producer Route

The historical producer route was deliberately short:

```text
FinitePlanarOuterComponentInputs C
-> faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
-> actualExteriorSectorInputSourceRows_of_inputs
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_actualExteriorSectorInputSourceRows
```

The actual-sector theorem is checked as an erasure.  The real source theorem
is still the face-dart/angular producer:

```lean
theorem faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
      forall k : Fin rows.orbit.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C rows.orbit.boundary k
```

Immediate proof slices for that producer:

1. Choose the Csizmadia-style lowest/exterior seed dart and build the genuine
   geometric face-successor orbit.
2. Prove the selected orbit edges lie in `unboundedFrontierEdgeSet C inputs`.
3. Prove graph vertices on the exterior frontier are exactly selected orbit
   tails.
4. Prove repeated selected tails give deleted-tail cut partitions, then use
   the no-cut input to get a simple face-dart boundary.
5. Prove same-boundary `BoundaryVertexAngularNoBetweenRows` for the selected
   exterior sector.  This is not global outgoing-list no-between.
6. Erase the resulting `FaceDartOrbitExteriorCarrierRows` and angular rows to
   `actualExteriorSectorInputSourceRows_of_inputs`.

Topology support such as
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`
may help a sublemma, but it is not the primary S2 producer and should not
replace the exterior face-orbit construction.

## 2026-05-22 q31 Live Source Leaves After q30

Checked in `S2SeededRawOrbitSource.lean`:

```lean
S2_q31_boundaryFreeLocalRawOrbitSourceRows_of_componentTopology_geometricSelection_localIncident_strictSuccessor
S2_q31_rawGeometricOrbitPackage_of_componentTopology_geometricSelection_localIncident_strictSuccessor
S2_q31_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentTopology_geometricSelection_localIncident_strictSuccessor_rawLeaves
S2_q31_actualExteriorSectorInputSourceRows_family_of_componentTopology_geometricSelection_localIncident_strictSuccessor_rawLeaves
S2_q31_actualExteriorSectorInputSourceRows_family_of_componentTopology_geometricSelection_localIncident_strictSuccessor_minimalSeparation_nonwrap
S2_q31_actualExteriorSectorInputSourceRows_of_exteriorFaceOrbitSeedSource_cutRows_rawOrientation
S2_q31_actualExteriorSectorInputSourceRows_of_exteriorFaceOrbitSeedSource_cutRows_selectedActualCarrierAngles
S2_q31_actualExteriorSectorInputSourceRows_of_exteriorFaceOrbitSeedSource_cutPartitions_rawOrientation
S2_q31_actualExteriorSectorInputSourceRows_of_exteriorFaceOrbitSeedSource_minimalDeletedTailSeparation_selectedActualCarrierAngles
S2_q31_actualExteriorSectorInputSourceRows_of_exteriorFaceOrbitSeedSource_exteriorFrontierArcSeparation_selectedActualCarrierAngles
S2_q31_actualExteriorSectorInputSourceRows_family_of_exteriorFaceOrbitSeedSource_minimalDeletedTailSeparation_selectedActualCarrierAngles
S2_q31_actualExteriorSectorInputSourceRows_family_of_exteriorFaceOrbitSeedSource_exteriorFrontierArcSeparation_selectedActualCarrierAngles
```

The q31 local raw-orbit source lowering is completed/checked, and the q31 raw
geometric orbit package is checked.  The local q31 package exposes
`localSectorRows`, carrier connectedness, the concrete geometric raw orbit, its
dart-frontier row, and raw coverage.  The checked raw-leaf wrapper routes that
package through the existing r19 face-dart/angular producer once repeated-tail
separation and raw orientation are supplied on the same exposed orbit.  The
sharper q31 wrapper lowers those rows to the finite-graph deleted-tail minimal
separation callback and genuine nonwrap successor rows in
`geometricOutgoingDartList`, respectively.

The q30 source-facing erasers also start from the exposed q30 selected raw
exterior face-successor orbit and erase to the concrete actual exterior-sector
source:

```text
q30 seeded raw exterior face orbit
+ repeated-tail cut rows for that same orbit
+ raw orientation rows
-> Exists B, frontier iff B.vertex
      /\ Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

The selected actual-carrier face-successor angle version lowers the angle row
to the raw orientation row on the same seeded raw orbit.  This does not use
actual-sector rows, a finished boundary cycle, endpoint-local radius, induced
frontier graphs, arbitrary carrier cycles, convex hull data, or identity
angular order.

The q31 actual-sector producer is checked down to one hard source:
`SelectedSeededRawOrbitMinimalDeletedTailSeparation`, equivalently pairwise
`RawFaceSuccOrbitRepeatedTailExteriorCutRows`, for repeated tails on the same
selected seed raw orbit.  The non-circular arc route is minimal-deleted-tail ->
`RawFaceSuccOrbitExteriorFrontierArcSeparationSourceRows` through r55; the k6f
theorem goes the reverse direction and is not a source.  The selected-carrier
angular leaf is handled by q7/q24 wrappers once `selectedCarrierRows` are
available.

Checked in `S2BoundaryFreeRawSource.lean`:

```lean
RawOrbitCoverageSourceRows.frontierVertexTailCoverageFromLocalSource
RawOrbitCoverageSourceRows.frontierIffTailFromLocalSource
```

These erase raw coverage plus `BoundaryFreeLocalNoThirdGermSourceRows` to the
frontier-tail coverage / frontier-iff-tail rows for the same raw orbit.  They
use only selected incident edges from the local row and do not promote it to
the global no-third-germ classifier.

The q30 seed/raw geometric orbit package is no longer an open q31 leaf.  Global
outgoing-list no-between rows remain support only unless the selected interval
is the actual exterior sector.

Demoted/support-only routes: all-adjacent endpoint closure, endpoint selected
head classification for arbitrary adjacent frontier endpoints, induced
frontier graph degree, and arbitrary spanning cycles.

## 2026-05-22 q30 Selected Face-Successor Angle Source

Checked in `S2CarrierLocalSource.lean`:

```lean
S2_q30_selectedActualCarrierFaceSuccAngleRows_family_of_carrierCutFieldwise_selectedAngular_orientation_localStrictOrder
```

This names the local angular source used by the raw exterior face-orbit route:
e32 carrier-cut fieldwise rows plus r36 selected angular rows, selected
orientation rows, and local strict-order rows give the selected actual-carrier
`faceSucc` angle family.  It avoids endpoint-local-radius rows, actual-sector
rows, W32 consumers, induced frontier graphs, arbitrary cycles, and identity
angular order.

Owner-file gate:

```text
lake env lean -DmaxErrors=30 ErdosProblems1066/Swanepoel/S2CarrierLocalSource.lean
```

## 2026-05-22 q12 Repeated-Tail Cut Lowering

Checked in `S2SeededRawOrbitSource.lean`: for the endpoint-local r17 selected
raw orbit, `SelectedRawOrbitRepeatedTailPrimitiveSourceRows` is strictly below
four source surfaces:

- ordinary `SelectedRawOrbitRepeatedTailCutPartitions`;
- canonical `SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource`;
- canonical `SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource`;
- pairwise `SelectedRawOrbitRepeatedTailActualExteriorArcRows`.

The theorem names are:
`S2_agent_q12_primitiveSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_repeatedTailCutPartitions`,
`S2_agent_q12_primitiveSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_cyclicSuccCutPartitions`,
`S2_agent_q12_primitiveSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_cyclicSuccDeletedTailNonreachability`,
and
`S2_agent_q12_primitiveSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_actualExteriorArcRows`.
The cut/cyclic-successor variants use only the existing selected raw-orbit
no-cut erasers; the actual-arc variant directly projects primitive witnesses
from the actual arc rows.

## 2026-05-22 q13 Raw-Orbit Source Focus

The sharpest checked eraser after q13 is now:

```lean
S2ExteriorBoundarySource.
  S2_q13_boundary_sector_erasure_source_of_rawFaceSuccOrbitSourceRows
```

It lowers a family of concrete raw geometric `faceSucc` orbits with
`RawFaceSuccOrbitSourceRows` plus a raw predecessor-before-successor orientation
row directly to the actual exterior-sector source family.  This avoids another
boundary-sector facade and does not assume final actual-sector rows.

Useful source-facing q13 support:

```lean
ExteriorComponentTopology.S2_q13_exterior_orbit_carrier_source
GeometricRotationSystem.boundaryVertexAngularNoBetweenRows_of_actual_faceSuccRows_strictTurnRows
S2SeededRawOrbitSource.
  S2_agent_q13_cyclicSuccDeletedTailNonreachabilitySource_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_boundaryArcRows
S2SeededRawOrbitSource.
  S2_agent_q13_cyclicSuccDeletedTailCutPartitionSource_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_boundaryArcRows
S2LocalTwoGermAssembly.IncidentGermSelectedEndpointLocalRadiusSourceRows
```

The current first genuine leaves remain source-level:

```text
component topology / no-open separation for the actual unbounded component;
frontier-vertex incident edge source;
selected-carrier local neighbour rows;
actual selected `faceSucc` successor/angle rows;
repeated-tail boundary-arc or deleted-tail nonreachability rows for the same
selected raw orbit;
raw orientation rows for the selected exterior sector.
```

Do not turn the q13 eraser into another W32 composer.  The live proof work is
to inhabit `RawFaceSuccOrbitSourceRows` and its raw orientation row from
`FinitePlanarOuterComponentInputs C`, or to strictly lower one of the listed
source leaves.

## 2026-05-22 q14/q15 Selected Raw-Orbit Source Boundary

The current checked q14 spine is:

```text
FiniteDrawingUnboundedComplementFrontierNoOpenSeparation
+ FrontierVertexIncidentUnboundedFrontierEdgeSource
+ UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
+ selected endpoint/head incident-germ rows or selected endpoint-radius rows
+ selected-carrier successor-tail rows
+ SelectedRawOrbitRepeatedTailBoundaryArcRows
-> RawFaceSuccOrbitSourceRows + raw orientation
-> actual exterior-sector source family
```

Checked q14 declarations include:

```lean
S2SeededRawOrbitSource.
  S2_q14_rawFaceSuccOrbitSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_boundaryArcRows
S2SeededRawOrbitSource.
  S2_q14_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_boundaryArcRows
S2SeededRawOrbitSource.
  S2_q14_rawFaceSuccOrbitSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_boundaryArcRows
S2SeededRawOrbitSource.
  S2_q14_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_boundaryArcRows
S2SeededRawOrbitSource.
  S2_q14_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_selectedHeadAt_selectedCarrierRows_boundaryArcRows
```

The last declaration is the current endpoint-facing form: it exposes the
selected-head endpoint classifier instead of treating endpoint-radius covers as
primitive.  This remains a strict source lowering, not a completed S2 proof.

Live q15 implementation leaves:

1. Prove or lower `FiniteDrawingUnboundedComplementFrontierNoOpenSeparation`.
2. Prove or lower `FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs`.
3. Prove or lower
   `UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs`.
4. Prove or lower the selected-head endpoint classifier for actual selected
   frontier germs.
5. Prove or lower selected-carrier successor-tail / actual `faceSucc` rows.
6. Prove or lower `SelectedRawOrbitRepeatedTailBoundaryArcRows` on the same
   selected raw orbit.

Do not use `FaceDartOrbitExteriorCarrierRows` or
`ActualExteriorSectorInputSourceRows` as sources for these leaves unless the
theorem is explicitly a reverse support lemma and not part of the live input
route.

## 2026-05-22 q28 Selected Endpoint Composer Demotion

Tried route: add a source-facing q28 wrapper around
`S2CarrierLocalSource.S2_q27_actualExteriorSectorInputSourceRows_family_of_componentTopology_carrierCutFieldwise_selectedAngular_endpointLocalRadius_orientation_localStrict_cyclicSuccDeletedTailNonreachability`
that replaces its broad `endpointLocalRadiusCovers` premise with only the
selected endpoint local source rows
`IncidentGermSelectedEndpointLocalRadiusSourceRows`.

Result: do not add this theorem.  The q27 composer first rebuilds
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` for the geometric
selection.  The checked selected-endpoint bridge
`S2SeededRawOrbitSource.S2_agent_q13_selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_selectedEndpointLocalRadiusSourceRows_selectedHeadAt`
does consume selected endpoint local source rows, but it also requires

```lean
forall a, IncidentGermEndpointSelectedHeadAt selectedRows a
```

That row classifies an arbitrary closed incident frontier germ endpoint as one
of the two selected heads.  It is therefore stronger than the requested
selected endpoint source rows and is exactly the endpoint classification
shortcut this branch was meant to avoid.  Without that classifier, the selected
endpoint rows only prove frontier-edge/source facts for the two chosen heads;
they do not turn an arbitrary adjacent closed-germ endpoint `x` into one of
those heads, so they cannot supply the incident-germ membership row consumed by
the q27 actual-sector route.

## 2026-05-22 q16 No-Compact Topology Source

Checked in `S2TopologySource.lean`:

```lean
S2_q16_noCompactConnectedKCrossing_source_of_kComponentPointsBetween_20260522
S2_q16_noCompactConnectedKCrossing_source_of_nontrivialAlignedKSplit_20260522
S2_q16_noCompactConnectedKCrossing_source_of_nontrivialRelativeClopenKSide_20260522
S2_q16_noCompactConnectedKCrossing_source_of_janiszewskiBoundaryBumping_20260522
```

This records the q16 no-compact-connected-`K`-crossing source as strictly below
the hard-case aligned closed `K`-split primitive
`PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit`,
via the existing same-`K` point-between reducer
`S2_r18_kcomponent_points_between_source_20260521r18`.  The intermediate
same-`K` point-between primitive still feeds the q15 finite no-closed/no-open
component topology package with local-sector rows, while the q16 no-compact
support branch no longer needs a separate facade or any final boundary-cycle,
actual-sector, W32, induced-frontier graph, arbitrary-cycle, or carrier source
row.

The sharper checked q16 support source is now below the hard-case aligned split:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
-> PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing
```

This is genuinely upstream of the aligned split route and uses only the
Janiszewski/boundary-bumping relative-clopen separator plus the compact
connected no-crossing eraser.

## 2026-05-22 q17 Aligned-Split Topology Source

Checked in `S2TopologySource.lean`:

```lean
S2_q17_topology_alignedKSplit_source_of_pairFrontierComponent_20260522
```

This strictly lowers
`PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesAlignedKSplit`
to the U-indexed primitive
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent`.
The route is:

```text
U-indexed pair-frontier component
-> crossing-subcontinuum point-between
-> continuous Boolean K-side
-> hard-case aligned closed K split
```

It deliberately avoids the same-`K` point-between source, the no-compact
crossing alias, relative-clopen as a consumed source, finite boundary-cycle
rows, carrier rows, actual-sector rows, and W32 consumers.

## 2026-05-22 q23 Source Composer

Checked in `S2SeededRawOrbitSource.lean`:

```lean
S2_q23_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_cyclicSuccCutPartitions
```

This is a source-facing actual-sector package, not a W32 facade.  It combines
the same-`K` Janiszewski point-between topology route with the selected
geometric-carrier local-sector route, then consumes the exact selected
raw-orbit cyclic-successor deleted-tail cut-partition source.  The current
remaining leaves are:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
FrontierVertexIncidentUnboundedFrontierEdgeSource
UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
SelectedNeighborIncidentGermFrontierEdgeMembershipRows
selected carrier faceSucc successor rows
selected raw-orbit cyclic-successor deleted-tail cut partitions
```

Future work should prove these rows from `FinitePlanarOuterComponentInputs C`;
adding more actual-sector or W32 consumer wrappers is not progress.

Claim `S2-q23-actual-source-composer` then threads the newest q22
face-successor reductions through the same q23 source surface.  Checked in
`S2SeededRawOrbitSource.lean`:

```lean
S2_q23_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn
S2_q23_unboundedExteriorFrontierCycleRows_family_of_kComponentPointsBetween_vertexIncident_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn
```

This strictly replaces the selected-carrier/cyclic-cut residual by the q22
actual selected `faceSucc` angle, cyclic-successor deleted-tail
nonreachability, and selected raw `faceSucc` turn rows on the internally
selected raw orbit.  The remaining S2Seeded leaves are:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
FrontierVertexIncidentUnboundedFrontierEdgeSource
UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
SelectedNeighborIncidentGermFrontierEdgeMembershipRows
selected actual-carrier faceSucc angle rows
selected raw-orbit cyclic-successor deleted-tail nonreachability
selected raw-orbit geometric faceSucc turn rows
```

The W32-side source is the still shorter topology-collapsed q23 family already
present in `FaceBoundaryTopologySourceW32.lean`, now carried through the direct
cycle and W32 handoffs:

```lean
unboundedExteriorFrontierCycleRows_family_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
minimalFailureExactActualTopologyFieldsTarget_of_boundaryBumping_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_cyclicSuccDeletedTailNonreachability_rawFaceSuccTurn_20260522q23
```

The remaining W32 leaves are exactly boundary-bumping, geometric selection,
selected incident-germ frontier membership, selected actual-carrier `faceSucc`
angle rows, cyclic-successor deleted-tail nonreachability, selected raw
`faceSucc` turn rows, and the usual minimal-failure no-cut family.

## 2026-05-22 q24 Carrier-Local Lowering

Checked in `S2CarrierLocalSource.lean`:

```lean
S2_q24_actualExteriorSectorInputSourceRows_family_of_kComponentPointsBetween_vertexIncident_carrierCutFieldwise_selectedAngular_incidentGerm_selectedCarrierRows_cyclicSuccCutPartitions
```

This is a source-facing lowering of the q23 actual-sector package.  It removes
the standalone geometric-selection leaf by rebuilding it pointwise from the
e32 fieldwise carrier-cut source plus the same-head r36 selected angular row:

```text
carrierCutFieldwise
+ selectedAngularNoBetweenRows over the associated r30 primitive
-> UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
```

The remaining q24 leaves are therefore:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
FrontierVertexIncidentUnboundedFrontierEdgeSource
S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
SelectedNeighborIncidentGermFrontierEdgeMembershipRows for the rebuilt selection
selected carrier faceSucc successor rows for the rebuilt selection
selected raw-orbit cyclic-successor deleted-tail cut partitions
```

The incident-germ endpoint branch has an existing q23 reducer from e32/r36 plus
endpoint-local-radius covers, but that branch is support only.  It is not a
live source leaf for the final input route unless it is first replaced by rows
restricted to actual selected unbounded-frontier germs.  Do not revive
all-adjacent endpoint closure or list endpoint-local-radius/all-adjacent
endpoint routes as live sources.

## 2026-05-22 q27 Actual-Source Collapse Status

Checked support in `S2CarrierLocalSource.lean`:

```lean
S2_q27_actualExteriorSectorInputSourceRows_family_of_componentTopology_carrierCutFieldwise_selectedAngular_endpointLocalRadius_orientation_localStrict_cyclicSuccDeletedTailNonreachability
```

This q27 composer erases the q25 face-dart/angular producer to
`ActualExteriorSectorInputSourceRows`.  It composes the checked component
topology package, e32 fieldwise carrier-cut rows, r36 selected angular rows,
selected actual-carrier orientation/local strict-order rows, and the q27
deleted-tail nonreachability reducer.  It is source-facing support only: it
does not add a W32 facade, final boundary-cycle premise, actual-sector premise,
induced frontier graph, arbitrary cycle, or all-adjacent endpoint route.

Checked repeated-tail support in `S2SeededRawOrbitSource.lean`:

```lean
S2_q27_selectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource_of_repeatedTailCutPartitions_noCut
S2_q27_cyclicSuccDeletedTailNonreachabilitySource_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_repeatedTailExteriorCutRows
S2_q27_cyclicSuccDeletedTailNonreachabilitySource_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles_repeatedTailExteriorCutRows
```

These reducers make deleted-tail nonreachability support below repeated-tail
cut/no-cut data, and below pointwise repeated-tail exterior cut rows for the
current selected r35 raw orbit.  Therefore deleted-tail nonreachability is no
longer the honest live leaf; the live leaf is the upstream repeated-tail
exterior cut source.

Current honest live leaves after the q27/q28/q29 route checks:

```text
topology trace/no-open support, with the stronger trace premise still upstream;
q26 local selected-germ isolation / no-third-germ support;
e32 carrier-cut fieldwise rows and r36 selected angular rows;
selected actual-carrier orientation plus local strict-order rows;
repeated-tail exterior cut rows on the current selected raw orbit.
```

Endpoint-local-radius, endpoint-selected-head, and any all-adjacent endpoint or
endpoint-all-adjacent/chord route are support-only unless they are restricted to
the two actual selected unbounded-frontier germs.  The q29 radius-containment
check showed the concrete `S2_r38` radius is the graph-vertex isolation radius
and excludes adjacent selected endpoints, so endpoint-radius containment is not
a live q27 input source.

Root build gate: no root build was run for this documentation refresh.  The
next integration gate is still targeted owner-file checks for any future Lean
edits, followed only after an unconditional source theorem by the pinned root
build and forbidden-token scan.

## 2026-05-22 q22 Source Composer

Checked in `FaceBoundaryTopologySourceW32.lean`:

```lean
actualExteriorSectorInputSourceRows_family_of_q21_remaining_leaves_20260522
```

This is the `S2-q22-source-composer` claim.  It is only a composer/eraser:
the q21 face-dart/angular producer
`S2_q21_faceDartOrbitExteriorCarrierRows_and_angularRows_family_of_componentInput_geometricSelection_incidentGerm_strictSuccessor_cyclicSuccCutPartitions_orientation`
is fed directly to
`actualExteriorSectorInputSourceRows_of_faceDartOrbitExteriorCarrierRows_family`.
No W32 target theorem, duplicate source package, actual-sector premise, final
boundary-cycle facade, induced frontier graph, arbitrary cycle, endpoint
all-adjacency shortcut, or identity angular order is introduced.

Exact remaining source leaves:

```lean
componentTopology :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs

geometricSelection :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      S2LocalTwoGermAssembly.UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
        C inputs

incidentGermFrontierEdgeRows :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      S2LocalTwoGermAssembly.SelectedNeighborIncidentGermFrontierEdgeMembershipRows
        (C := C) (inputs := inputs) (geometricSelection C inputs)

strictSuccessorOrder :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      let selectedRows :
          S2LocalTwoGermAssembly.UnboundedFrontierCarrierSelectedNeighborGeometricOrderSourceRows
            inputs :=
        S2LocalTwoGermAssembly.selectedNeighborGeometricOrderSourceRows_of_geometricSelectionInputSource
          (C := C) (inputs := inputs) (geometricSelection C inputs)
      RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource
        inputs
        (selectedNeighborGeometricCarrierLeft
          (C := C) (inputs := inputs) selectedRows.toGeometricSelectionInputSource)
        (selectedNeighborGeometricCarrierRight
          (C := C) (inputs := inputs) selectedRows.toGeometricSelectionInputSource)

cyclicSuccCutPartitions :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
        (S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
          (C := C) (inputs := inputs)
          (componentTopology C inputs) (geometricSelection C inputs)
          (incidentGermFrontierEdgeRows C inputs)
          (strictSuccessorOrder C inputs))

rawOrientationRows :
  forall {m : Nat} (C : _root_.UDConfig m)
    (inputs : FinitePlanarOuterComponentInputs C),
      SelectedRawOrbitOrientationRows
        (S2_r35_selectedRawTailCoverageSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor
          (C := C) (inputs := inputs)
          (componentTopology C inputs) (geometricSelection C inputs)
          (incidentGermFrontierEdgeRows C inputs)
          (strictSuccessorOrder C inputs))
```

## Historical 2026-05-21 k20 Connected Raw-Orbit Route

Historical support only.  The current live route is the 2026-05-21 live
producer route above, whose live producer is still
`faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs`.

Checked W32 route:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing
+ forall C inputs, BoundaryFreeConnectedRawOrbitSourceRows inputs
+ selected primitive repeated-tail rows on the internally selected raw orbit
+ selected raw predecessor/successor orientation rows on that same orbit
+ S1 noCutRows
-> W32
```

The W32 consumer is:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_noCompactConnectedKCrossing_connectedRawOrbit_primitiveRepeatedTail_orientation_20260521k20
```

The selected repeated-tail leaf is lowered by:

```lean
ExteriorComponentTopology
  .S2_agent_repeated_tail_actual_arc_source_family_20260521k19
```

The selected raw angular leaf is lowered by:

```lean
ExteriorComponentTopology
  .S2_agent_selected_raw_geometric_angular_source_family_20260521k19
```

Immediate source tasks on this route:

1. Prove the no-compact connected crossing topology source, or lower it to a
   concrete planar-continuum separation theorem.
2. Construct `BoundaryFreeConnectedRawOrbitSourceRows` from the exterior
   boundary face-successor orbit.
3. Prove selected primitive repeated-tail rows on that orbit by the no-cut
   repeated-vertex separation theorem.
4. Prove selected raw predecessor/successor orientation rows from the genuine
   geometric face-successor order.

## Historical 2026-05-22 Source-Leaf Decomposition

Historical support only.  The live route is the compact 2026-05-21 producer
route above.  The decomposition below records useful source surfaces, but it is
not the current workboard.

The route recorded here was:

```text
FinitePlanarOuterComponentInputs C
-> faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
-> actualExteriorSectorInputSourceRows_of_inputs
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_actualExteriorSectorInputSourceRows
```

The actual-sector theorem is checked as an erasure.  The real source theorem
is the face-dart/angular producer:

```lean
theorem faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
      forall k : Fin rows.orbit.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C rows.orbit.boundary k
```

Recorded source leaves:

1. Component topology:
   `S2_dynamic_component_topology_input_source_family_of_crossingSubcontinuumForcesBounded_outsideAccumulation_20260522`
   lowers `UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs` to
   `PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded`
   plus pointwise
   `UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier C inputs`.
   The lower global topology variant is
   `S2_dynamic_component_topology_input_source_family_of_nontrivialRelativeClopen_outsideAccumulation_20260522`.

2. Local-sector/geometric-selection:
   `S2_r30_deletedNeighborLocalSeparationInputSource_family_of_localSectorRows_geometricRows_endpointLocalRadiusCovers`
   and
   `S2_dynamic_selected_carrier_neighbor_geometricSelectionInputSource_family_20260522_of_deletedNeighborLocalSeparation_geometricSelectionRows`
   keep the selected-carrier lane at local-sector rows, same-head
   `GraphVertexGeometricAngularNeighborSelectionRow`s, and endpoint-radius
   coverage for the same selected heads.

3. Selected incident-germ endpoint radius:
   `selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_endpointLocalRadiusCovers_20260522`
   turns the exact selected-pair
   `IncidentGermEndpointLocalRadiusCoversRows` into
   `SelectedNeighborIncidentGermFrontierEdgeMembershipRows (geometricSelection C inputs)`.

4. Repeated-tail nonreachability:
   `S2_subagent_repeated_tail_nonreachability_family_20260521_current6_of_connectedRawOrbitSourceRows_cyclicSuccCutPartitions`
   erases `SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource` to
   `SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource` for the
   selected raw orbit.  The source content is still the finite deleted-tail
   cut/nonreachability argument.

5. `faceSucc` / turn-to-angular:
   `S2_r12_rawOrbit_package_family_of_componentInput_geometricSelection_incidentGerm_successorTailRows_cyclicSuccCutPartitions_faceSuccTurn_20260522r12`
   feeds the raw package from `SelectedRawOrbitGeometricFaceSuccTurnRows`.
   The direct face-dart/angular producer
   `S2_subagent_raw_package_integration_20260522_current6_faceDartOrbitExteriorCarrierRows_and_angularRows_of_successorTailRows_cyclicSuccCutPartitions_geometricAngularSelection`
   still needs `SelectedRawOrbitGeometricAngularNeighborSelectionRows` for the
   final same-boundary angular rows.  The rotation helper
   `rawFaceSuccOrbit_actualFaceSucc_headAngle_lt_of_geometricSuccessorNonwrapRows_20260522`
   is support for angle inequalities, not an input-only angular closure.

Guardrails: do not revive W32 composers, final actual-sector rows, arbitrary
cycles, induced frontier graphs, all-adjacent endpoint closure, or global
outgoing-list no-between as live sources.  A missing row becomes the next
source theorem from `FinitePlanarOuterComponentInputs C`.

## Historical 2026-05-21 p Route

This section is historical after the compact 2026-05-21 live producer route
above.  It is
kept for dependency archaeology only; do not read the older k6m/k9, g1/g2/g3,
U-pair, finite no-closed-separation, actual-carrier-degree-two,
local-selected-incident, continuous-side, relative-clopen, same-`K`, or
geometric no-between notes as current work assignments.

The current checked W32 consumer is:

```text
forall C inputs,
    exists B,
      frontier exterior iff B.vertices
      /\ Nonempty (ActualExteriorSectorInputSourceRows inputs B)
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_actualExteriorSectorInputSourceRows
```

The actual exterior-sector wrapper is checked as an erasure from the
face-dart/angular producer family.  It is not a standalone input-source theorem.
The remaining local source theorem is the face-dart/angular producer from
`FinitePlanarOuterComponentInputs C`.

```lean
theorem actualExteriorSectorInputSourceRows_of_inputs
    (faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs : ...)
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
      (forall v : Fin n,
        (canonicalGraph C).point v ∈
            frontier (unboundedExteriorComponentRows C inputs).exterior ↔
          Exists fun k : Fin B.length => B.vertex k = v) ∧
      Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

The first real intermediate producer is active and not proved:

```lean
theorem faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs : FinitePlanarOuterComponentInputs C) :
    PSigma fun rows : FaceDartOrbitExteriorCarrierRows C inputs =>
      forall k : Fin rows.orbit.boundary.length,
        GeometricRotationSystem.BoundaryVertexAngularNoBetweenRows
          C rows.orbit.boundary k
```

Proving this makes `actualExteriorSectorInputSourceRows_of_inputs` a short
erasure through the checked `FaceDartOrbitExteriorCarrierRows` and
`ActualExteriorSectorInputSourceRows` consumers.  That erasure is support; the
producer above is the real finite plane-graph theorem.

The producer proof should be orbit-first internally and boundary-sector
externally:

```text
FinitePlanarOuterComponentInputs C
-> choose Csizmadia-style lowest/exterior seed dart
-> build the selected geometric raw face-successor orbit
-> prove selected raw-orbit edges lie in unboundedFrontierEdgeSet C inputs
-> prove exterior-frontier graph vertices are exactly selected raw-orbit tails
-> prove repeated raw tails give cut partitions and use noCut for injectivity
-> package FaceDartOrbitExteriorCarrierRows and same-boundary angular rows
-> erase to UnitDistanceCycleBoundary B with frontier equivalence and sector rows
-> produce Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

Historical 2026-05-21 source leaves:

1. Prove `faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs` from
   `FinitePlanarOuterComponentInputs C`.
2. Prove `actualExteriorSectorInputSourceRows_of_inputs` from
   `FinitePlanarOuterComponentInputs C`.
3. Keep
   `PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`
   as topology support, not as a replacement for the actual exterior-boundary
   producer.

Do not revive all-adjacent endpoint rows, induced frontier graphs, arbitrary
cycles, convex-hull shortcuts, identity angular order, synthetic enclosures, or
global outgoing-list no-between obligations as the live source.  Do not add
another W32-facing composer while either live source leaf is open.

2026-05-21 r13 face-successor turn source: checked in
`ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.  The source-facing
selected seeded raw-orbit turn bridge is now:

```lean
selectedSeededRawOrbitGeometricFaceSuccTurnRows_of_selectedActualCarrierFaceSuccAngleRows_20260521r13
S2_r13_selectedRawOrbitGeometricFaceSuccTurnRows_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
S2_r13_selectedRawOrbitGeometricFaceSuccTurnRows_family_of_componentInput_geometricSelection_incidentGerm_selectedActualCarrierFaceSuccAngles
```

These reduce `SelectedRawOrbitGeometricFaceSuccTurnRows` for the selected
exterior seeded raw orbit to the actual selected-carrier `faceSucc` angle
source.  The proof uses the geometric raw `faceSucc` orbit endpoint
identification at the cyclic predecessor and eta-expands the successor-tail
row through
`rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource_eta`
when passing through dependent selected-row lets.  This is not a global
all-outgoing no-between route and does not use W32/final actual-sector rows.

2026-05-21 r14 selected actual-carrier faceSucc angle source: checked in
`ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.  The sharp
selected-carrier angle row is now lowered to concrete non-wrap geometric
`faceSucc` rows on the same selected carrier heads:

```lean
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccOrientationRowsNoOrbitSource_of_faceSuccRows_20260521r14
rawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedActualCarrierFaceSuccAngleRowsNoOrbitSource_of_orientationRows_successorTailRows_20260521r14
S2_r14_selected_actual_carrier_faceSucc_angle_source_of_faceSuccRows
S2_r14_selected_actual_carrier_faceSucc_angle_source_of_geometricSelection_faceSuccRows
```

This is a strict source reduction, not a new consumer.  The orientation
equalities are projected from the actual `faceSucc` row, and the strict angular
inequalities are rebuilt from the successor-tail geometric rows through the
existing local strict-order reducer.  The remaining source below this branch is
the concrete selected geometric `faceSucc` row itself, not global all-outgoing
no-between, W32, or final actual-sector data.

2026-05-22 q12 faceSucc strict-order source: checked in
`ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean`.

```lean
S2_agent_q6_selected_actual_carrier_faceSucc_angle_source_of_geometricSelection_orientationRows_localStrictOrder_20260522q6
S2_agent_q7_selected_actual_carrier_orientation_source_of_geometricSelection_selectedCarrierRows_20260522q7
S2_agent_q7_localStrictOrder_source_of_geometricSelection_selectedCarrierRows_20260522q7
S2_agent_q7_selected_actual_carrier_faceSucc_angle_source_of_geometricSelection_selectedCarrierRows_20260522q7
S2_agent_q7_selected_actual_carrier_faceSucc_angle_source_family_of_geometricSelection_selectedCarrierRows_20260522q7
```

The q10 selected raw-orbit angle rows now route through the selected-carrier
successor rows: the orientation equalities are projections of the same
selected carrier rows, while `RawOrbitIteratedFaceSuccHeadLocalAngularStrictOrderNoOrbitSource`
is obtained from those successor-tail geometric rows via the existing
sorted/nonwrap strict-order reducer.  The route stays inside the selected
exterior carrier sector and does not use a global all-outgoing no-between
shortcut, W32/final actual-sector rows, induced graphs, convex hulls, or
synthetic rows.  The build repair in the same pass eta-expanded the
endpoint-local r17 repeated-tail family adapters to apply their dependent
callbacks to explicit `i`/`j`, keeping the touched seeded raw-orbit module
buildable.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
```

2026-05-21 r15 r30/r36 local source: checked in
`ErdosProblems1066/Swanepoel/S2CarrierLocalSource.lean`.  The local carrier
lane now has the explicit strict source boundary:

```lean
S2_r15_r30_finitePlaneLocalSeparationPrimitive_of_boundaryFreeLocalSectorGeometricAngularSource
S2_r15_r36_geometricSelectionInputSource_of_boundaryFreeLocalSectorGeometricAngularSource
S2_r15_r30_r36_local_sources_of_boundaryFreeLocalSectorGeometricAngularSource
S2_r15_r30_r36_local_sources_family_of_boundaryFreeLocalSectorGeometricAngularSource
```

Thus the r30 finite-plane deleted-neighbour primitive and the r36 selected
geometric carrier source are both reduced to the same
`BoundaryFreeLocalSectorGeometricAngularSource`.  This keeps the selected
heads on actual `unboundedFrontierEdgeSet` incidences and does not introduce a
final boundary cycle, actual-sector rows, W32, an induced frontier graph, or a
global outgoing no-between premise.  The remaining local producer from bare
`FinitePlanarOuterComponentInputs C` is the boundary-free local
geometric-angular source itself.

2026-05-21 r15 boundary-free local geometric-angular lowering:
`S2_r15_boundaryFreeLocalSectorGeometricAngularSource_of_finitePlaneLocalSeparationPrimitive_geometricOrderRows_endpointLocalRadiusCoversRows`
and its family form are checked in `S2CarrierLocalSource.lean`.  They compose
the r30 finite-plane local carrier primitive, the r36 selected geometric-order
row, and the r15 endpoint local-radius promotion to rebuild
`BoundaryFreeLocalSectorGeometricAngularSource`.  The residual is now the
explicit `IncidentGermEndpointLocalRadiusCoversRows` for the same selected
pair, rather than the older global selected-edge no-third endpoint row; the
route still avoids global all-outgoing no-between, induced frontier graph,
arbitrary cycle, actual-sector, and W32 premises.

2026-05-21 r15 selected incident-germ frontier membership source:
`S2_r15_selectedNeighborIncidentGermFrontierEdgeMembershipRows_of_geometricSelection_endpointLocalRadiusCoversRows`
and its family form are checked in `S2CarrierLocalSource.lean`.  The proof
builds the selected edge-pair rows from the geometric selection, derives the
selected head-local incident rows, promotes them through the explicit
same-selected-pair `IncidentGermEndpointLocalRadiusCoversRows`, and then uses
the existing selected-head-to-frontier-edge source.  This supplies the exact
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows (geometricSelection C inputs)`
family consumed by the r15 source spine without final boundary rows,
actual-sector rows, W32, induced frontier graph, arbitrary cycle, or an
all-adjacent endpoint shortcut.

The direct selected raw-source adapter in `S2SeededRawOrbitSource.lean` was
also kept in selected-carrier shape by erasing
`RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailSelectedCarrierRowsNoOrbitSource`
directly to the concrete `faceSucc` row source.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2CarrierLocalSource
```

2026-05-21 current5 decomposition: the current direct face-dart/angular route
uses the checked current4 loop-breaker

```lean
S2_subagent_successor_no_between_loop_break_family_20260521_current4_faceDartOrbitExteriorCarrierRows_and_angularRows_of_successorTailRows_exteriorArc_geometricAngularSelection
```

so the live local source no longer needs the over-strong
`RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricOutgoingListNoBetweenRowsNoOrbitSource`.
The route now asks for the selected carrier heads' direct
`RawOrbitIteratedFaceSuccHeadLocalAngularSuccessorTailGeometricRowsNoOrbitSource`,
the actual selected raw exterior-arc/nonreachability source, the concrete
carrier degree/local selected no-third source, and the topology
frontier-subcontinuum support source.  These are source leaves only; none may
be replaced by an assumed actual-sector row, W32 consumer, arbitrary cycle,
induced frontier graph, or global outgoing-list interval.

2026-05-21 live-status refresh: r6q/r6r confirm that no checked route currently
goes from bare `FinitePlanarOuterComponentInputs C` directly to S2 closure.
The live route is:
`actualExteriorSectorInputSourceRows_of_inputs` <-
`faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs` <-
raw exterior face-orbit sources.  r6n supplies the checked local wrapper from
geometric selection + local incident-germ + successor-tail rows to
`RawOrbitDartEdgeFrontierSource inputs`, giving the raw orbit dart/edge frontier
side of the route.  r6o identifies the repeated-tail/no-cut side as pointwise
`RawFaceSuccOrbitRepeatedTailExteriorCutRows`, equivalently
`SelectedRawOrbitMinimalDeletedTailSeparation`.  r8c sharpens this branch:
`SelectedRawOrbitMinimalDeletedTailSeparation` is now reduced to
`SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource`, i.e. deleted-tail
nonreachability between the two canonical cyclic-successor tails.  The checked
bridge
`S2_r8c_selectedRawOrbitRepeatedTailPrimitiveSourceRows_of_connectedRawOrbitSourceRows_cyclicSuccDeletedTailNonreachability`
turns this source into the primitive repeated-tail row consumed by the r8b raw
package assembler.  r8d was an intermediate eraser through Boolean side
labelling; after r8e it is no longer the live residual.  The live repeated-tail
residual was briefly sharpened to the topology-facing source
`SelectedRawOrbitCyclicSuccDeletedTailReachableClosedSeparationCompactCarrierSource`:
from any deleted-tail reachable path, construct the actual closed frontier
sides and the compact connected subset of `embeddedEdgeSet C` carried by the
walk that meets both sides.  r8f completes the walk-carrier half through
`FinitePlaneDrawing.walkEmbeddedCarrier`, so this is no longer the live
residual.  r8g then tried to lower endpoint closed-side construction to
whole-frontier component separation:

```lean
SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointFrontierComponentSeparationSource
```

This is now demoted.  The r8h diagnostic

```lean
selectedRawOrbit_endpointFrontierComponentSeparation_false_of_frontierPreconnected_20260521r8h
```

shows that this whole-frontier component-separation source is incompatible
with the intended preconnectedness of the actual unbounded exterior frontier.
It is therefore a conditional no-go route, not a live source target.  Do not
try to prove r8g from topology rows.

The live repeated-tail residual is again the direct finite plane-graph source:
prove
`SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource`, equivalently
`SelectedRawOrbitMinimalDeletedTailSeparation`, by the no-cut/Jordan
separation argument after deleting the repeated raw tail.  The correct
separation is a graph deletion/cut-partition or punctured-frontier obstruction,
not a closed disjoint decomposition or connected-component split of the whole
frontier.  The demoted endpoint closed-side source
`SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointClosedSeparationSource`:
construct the closed frontier sides containing the two cyclic successor
endpoint vertices should not be revived as live.  r8d also adds the local selected-head support theorem from
`ActualCarrierDegreeTwoSource` to
`IncidentGermSelectedHeadLocalRows`, keeping selected-head work tied to actual
carrier degree rather than global outgoing no-between rows.  New W32 composers
remain pruned work unless they disappear behind this producer route.

r8h also adds the finite-boundary-arc route to the canonical successor
deleted-tail source:

```lean
selectedRawOrbitCyclicSuccDeletedTailBoolSideSeparationSource_of_boundaryArcRows_20260521r8h

selectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource_of_boundaryArcRows_20260521r8h
```

Thus the current repeated-tail producer can be stated either as
`SelectedRawOrbitRepeatedTailBoundaryArcRows` or as the smaller pairwise
`RawFaceSuccOrbitRepeatedTailExteriorCutRows`.  The mathematical content is
the same standard finite plane-graph step: if the selected exterior face walk
repeats a vertex, the two open arcs cut by that repeated vertex determine two
nonempty graph sides with no edge between them after deleting the repeated
tail.  This must be proved from the actual selected raw exterior walk and
noncrossing geometry, not from a whole-frontier component split.

r9 wires this smaller repeated-tail residual directly into the raw geometric
orbit package boundary:

```lean
S2_r8h_rawGeometricFaceSuccOrbit_sourcePackage_of_boundaryFree_connected_selectedEdge_repeatedTailExteriorCutRows_orientation

S2_r8h_rawGeometricFaceSuccOrbit_sourcePackage_of_boundaryFree_connected_selectedEdge_repeatedTailExteriorCutRows_faceSuccTurn
```

These are not S2 closers.  They mean that, on the positive selected-edge route,
the raw package no longer needs the cyclic-successor nonreachability or
primitive repeated-tail rows as external premises.  It can consume the actual
pairwise `RawFaceSuccOrbitRepeatedTailExteriorCutRows` source directly, then
erase through the existing exterior-cut-to-primitive bridge internally.  The
live repeated-tail source remains the finite plane-graph cut construction
itself.

r9 also adds the orbit-free whole-open-segment face-successor source:

```lean
RawOrbitIteratedFaceSuccOpenSegmentFrontierNoOrbitSource

rawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource_of_openSegmentFrontierNoOrbitSource

rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_openSegmentFrontierNoOrbitSource

rawOrbitIteratedFaceSuccOpenSegmentFrontierNoOrbitSource_of_localSectorTransition
```

So the successor-edge leaf can now be worked at the sharper level:
prove the selected Nat-indexed geometric `faceSucc` transition preserves the
whole successor open segment on the exterior frontier.  The checked reducer
fills this from `RawOrbitIteratedFaceSuccLocalSectorTransitionNoOrbitSource`;
the remaining real geometric content is to prove that strict local-sector
transition source from the actual exterior-oriented face-successor construction,
without smuggling in a completed boundary cycle.

r9 topology and local-neighbour source lowerings:

```lean
S2_r7j_component_topology_input_source_of_finiteDrawingNoClosedSeparation_puncturedAccumulation_20260521r7j

unboundedFrontierCarrierGeometricNeighborSelectionSourceRows_of_geometricSelectionInputSource
```

The component-topology input source now reduces to finite-drawing
no-closed-separation plus punctured accumulation at frontier graph vertices.
The selected-neighbour source now projects cleanly from actual carrier-neighbour
geometric selection rows to the compact geometric-neighbour source, without
introducing a separate global outgoing-list no-between leaf.

The pruned current raw-package source boundary is therefore:

```text
BoundaryFreeNoThirdGermSource inputs
+ (unboundedFrontierCarrierGraph C inputs).Connected
+ RawOrbitIteratedFaceSuccOpenSegmentFrontierNoOrbitSource inputs
  (or its local-transition source)
+ pairwise RawFaceSuccOrbitRepeatedTailExteriorCutRows on the selected orbit
+ selected raw orientation, preferably via SelectedRawOrbitGeometricFaceSuccTurnRows
-> S2RawGeometricFaceSuccOrbitSourcePackage C inputs
-> faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs
-> actualExteriorSectorInputSourceRows_of_inputs
```

The true remaining input-level leaves are the first proofs of those source
rows from `FinitePlanarOuterComponentInputs C`: selected `faceSucc`
frontier preservation, actual carrier/local two-germ connectedness,
repeated-tail exterior cuts, and raw same-boundary orientation.  The checked
package/composer names above should be treated as erasers, not as proof that
the exterior boundary cycle has been constructed.

r10 source lowerings sharpen three of those leaves:

```lean
unboundedFrontierCarrierGraph_connected_of_componentTopologyInputSourceRows

boundaryFreeNoThirdGermSource_of_neighborPairRows_endpointNoThird_20260521r61

selectedRawOrbitRepeatedTailExteriorCutRows_of_cyclicSuccCutPartitionSource_20260521current7

selectedRawOrbitGeometricFaceSuccTurnRows_of_faceSuccGeometricNonwrapRows
```

Consequences:

```text
carrier connectedness
  <- UnboundedExteriorFrontierComponentTopologyInputSourceRows

BoundaryFreeNoThirdGermSource
  <- actual carrier-neighbour pair rows
     + IncidentGermEndpointSelectedEdgeNoThirdRows for the selected heads

RawFaceSuccOrbitRepeatedTailExteriorCutRows
  <- SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource

SelectedRawOrbitGeometricFaceSuccTurnRows
  <- SelectedRawOrbitFaceSuccGeometricNonwrapRows
```

The currently sharp residuals are therefore:

1. finite-drawing/component topology input rows, now down to finite
   no-closed-separation plus punctured accumulation;
2. actual carrier-neighbour pairs plus endpoint selected-edge no-third rows;
3. strict selected `faceSucc` local-sector transition / whole-open-segment
   preservation;
4. cyclic-successor cut partitions for repeated raw tails;
5. concrete face-successor nonwrap rows on the selected raw orbit.

r11 source lowerings update that residual list:

```lean
S2_r11_topology_points_between_source_20260521r11

S2_r11_boundaryFreeLocalSectorGeometricAngularSource_family_of_finitePlaneLocalSeparationPrimitive_getElem_selectedEdgeNoThirdRows

selectedRawOrbitCyclicSuccDeletedTailCutPartitionSource_of_primitiveSourceRows_20260521pool7

S2_r11_faceSucc_nonwrap_source_family_20260521r11

S2_r11_carrierCutFieldwiseFamily_of_rawOrbit_thirdNeighborRepeatedTailCutPartitions
```

r15 adds the direct no-cut/repeated exterior face-walk adapter for the exact
cyclic-successor cut-partition family consumed by the current source spine:

```lean
selectedRawOrbitCyclicSuccDeletedTailCutPartitionSource_of_repeatedTailExteriorCutRows_noCut_20260521r15

S2_r15_cyclicSuccDeletedTailCutPartitionSource_family_of_componentInput_geometricSelection_incidentGerm_successorTailRows_repeatedTailExteriorCutRows_20260521r15
```

So the r15 cyclic-successor deleted-tail source can now be supplied from
pointwise `RawFaceSuccOrbitRepeatedTailExteriorCutRows` on the same selected
raw orbit.  The proof erases those exterior face-walk cut rows to ordinary
repeated-tail cut partitions and applies `inputs.noCutVertex`, without using
final boundary cycles, actual-sector rows, induced frontier graphs, arbitrary
cycles, or W32.

Consequences:

```text
topology points-between
  <- PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction

BoundaryFreeLocalSectorGeometricAngularSource
  <- S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
     + selected-head getElem geometric-order rows
     + IncidentGermEndpointSelectedEdgeNoThirdRows

SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
  <- SelectedRawOrbitRepeatedTailPrimitiveSourceRows
     (through finite boundary-arc Boolean side separation)

SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
  <- pointwise RawFaceSuccOrbitRepeatedTailExteriorCutRows
     + inputs.noCutVertex

SelectedRawOrbitFaceSuccGeometricNonwrapRows
  <- SelectedRawOrbitGeometricFaceSuccTurnRows

carrier-cut fieldwise rows
  <- concrete third-neighbour repeated-tail cut partitions
```

The current source boundary is now sharper: the difficult content is the
first construction of the actual selected exterior face walk, not another
adapter.  The live proof-producing leaves are the topology no-subcontinuum
obstruction, selected local `getElem`/endpoint no-third rows for the carrier
pair, strict selected `faceSucc` open-segment preservation, concrete
repeated-tail cut partitions from the exterior walk, and genuine selected
turn/nonwrap rows from the geometric rotation system.

r8e adds a topology-facing version of the same deleted-tail leaf:

```lean
SelectedRawOrbitCyclicSuccDeletedTailReachableClosedSeparationCompactCarrierSource
```

This source asks the reachability witness itself to produce closed frontier
sides and a compact connected subset of `embeddedEdgeSet C` meeting both
sides.  The checked reducer

```lean
selectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource_of_noCompactConnectedKCrossing_reachableClosedSeparationCompactCarrier_20260521r8e
```

then applies
`PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing`
directly.  The residual is now the honest geometric construction of the
closed sides and walk carrier from a deleted-tail reachable path, not another
no-closed-separation or Boolean-side eraser.

r8f proves the walk-carrier half of this residual from endpoint-side closed
separation data:

```lean
SelectedRawOrbitCyclicSuccDeletedTailReachableEndpointClosedSeparationSource
```

The checked reducer

```lean
selectedRawOrbitCyclicSuccDeletedTailReachableClosedSeparationCompactCarrierSource_of_endpointClosedSeparation_20260521r8f
```

uses the finite `walkEmbeddedCarrier` construction to supply the compact
connected embedded carrier.  The remaining proof content is therefore exactly
the direct nonreachability/cut-partition construction for the two canonical
cyclic successor vertices of a repeated raw tail.  The endpoint closed-side and
whole-frontier component-separation subroutes are archived as over-strong.

The broad r7i/r8a source-decomposition claims are historical route
archaeology after the r8b/r8c/r8e/r8f/r8g/r8h refinements.  They should not be
read as live residual surfaces or ownership claims.

## 2026-05-21 r5d/r5f Route Refinements

Checked owner-file support added while preserving the live producer target.

Raw/carrier head alignment:

```lean
selectedRawOrbitPointwiseHeadMatch_of_headMatch_tailInjective_20260521r5d
```

This decomposes the selected raw/carrier alignment into:

```text
SelectedRawOrbitHeadMatchSource selectedRows rawRows
+ raw tail injectivity
-> pointwise predecessor/successor selected-head equalities at each raw index
```

The theorem does not use `SelectedRawOrbitGeometricSuccessorNonwrapRows` or
`SelectedRawOrbitGeometricAngularNeighborSelectionRows`; those remain genuine
geometric source rows, not head-match bookkeeping.

Topology support:

```lean
S2_r5f_local_topology_no_closed_source_20260521r5f
```

This records the checked topology-only chain:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationNoCompactConnectedKCrossing
-> PlanarContinuumUnboundedComplementFrontierPreconnected
-> PlanarContinuumUnboundedComplementFrontierNoClosedSeparation
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

Neither theorem closes the live exterior-boundary producer.  The source target
is still `faceDartOrbitExteriorCarrierRows_and_angularRows_of_inputs`, and then
`actualExteriorSectorInputSourceRows_of_inputs`.

## 2026-05-21 k6 Repeated-Tail Witness Source

Claim `S2-k6-repeated-tail-witness-source` is checked in
`S2SeededRawOrbitSource.lean`.

New selected-row reducers:

```lean
selectedRawOrbitRepeatedTailWitnessSource_of_repeatedTailExteriorCutRows_20260521k6
selectedRawOrbitRepeatedTailWitnessSource_of_actualExteriorArcRows_20260521k6
selectedRawOrbitRepeatedTailWitnessSource_of_boundaryArcRows_20260521k6
selectedRawOrbitRepeatedTailWitnessSource_of_exteriorFrontierArcSeparationRows_20260521k6
```

The core handoff uses the existing k6 two-way maps through
`SelectedRawOrbitMinimalDeletedTailSeparation`: pointwise
`RawFaceSuccOrbitRepeatedTailExteriorCutRows` first gives the minimal
deleted-tail separation package, then the minimal package gives
`SelectedRawOrbitRepeatedTailWitnessSource`.  The stricter geometric residual
is now the actual exterior arc/separation row for the same selected raw
face-walk tail.  No arbitrary cycle, induced frontier graph, all-adjacent
endpoint shortcut, or proof placeholder is introduced.

## 2026-05-21 Two-Leaf S2 Route

Active local-source claim:

```lean
forall a, UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a
```

The current owner is Codex main under TASK claim
`S2-codex-main-boundaryfree-local-input-source-20260521h1`.  The checked h1
eraser lowers `BoundaryFreeLocalInputSourceReduction inputs` to these
pointwise local two-germ rows.  The checked h2 eraser also fills the same
corrected local input package directly from
`UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`.  The
checked h4 eraser fills it directly from pointwise actual carrier-neighbour
rows.  The checked h5 equivalence records that the corrected local input
package is `Nonempty` exactly when the pointwise actual carrier-neighbour row
family is `Nonempty`; `S2CarrierLocalSource` also records the same corrected
local input package as equivalent to actual degree two of the selected
unbounded-frontier carrier graph.  The checked h8 equivalence records the
local two-germ family itself as `Nonempty` exactly when that same actual
carrier degree-two source holds, and adds the reverse family handoff from
actual degree two to pointwise `UnboundedFrontierCarrierLocalTwoGermRowsAt`.
The h12 raw-orbit handoff records that
`SelectedSeededRawFaceSuccOrbitSourceRows inputs`, together with either
repeated-tail cut partitions or primitive deleted-tail witnesses for that same
selected orbit, feeds `ActualCarrierDegreeTwoSource inputs` directly via the
orbit's `RawFaceSuccOrbitSourceRows.localSectorRows` field.
The same handoff is now available for generic selected raw-tail coverage rows
and for internally selected connected raw-orbit rows, with either selected
cut-partition rows or primitive deleted-tail witnesses; all of these go through
raw `faceSucc` source rows and avoid the former raw-orientation/nonwrap detour.
The direct W32 raw-orbit consumer remains checked: connected raw-orbit source
rows plus selected repeated-tail cut partitions, or the lower deleted-tail
witness row, already produce the finite planar theorem and the W32 target.
The h12 follow-up lowers that same W32 route one step further:
connected raw-orbit source rows plus primitive deleted-tail exterior-cut
witnesses for repeated tails of the internally selected orbit now produce the
finite planar theorem and W32 target by first erasing those witnesses to the
checked selected cut-partition route.
The compact successor-point branch is now explicit at all three levels:
boundary-free local input plus Janiszewski point-between topology plus the
selected successor interior-frontier point row produces
`UnboundedExteriorFrontierCycleRows`, then
`FinitePlanarStraightLineOuterComponentTheorem`, then the W32 target.
The same compact branch is also available one step lower: the successor point
row is derived from
`RawOrbitIteratedFaceSuccBoundaryFreeLocalTwoGermTransitionNoOrbitSource`
for the `BoundaryFreeNoThirdGermSource` inside the boundary-free input
package.
The
proof route must stay selected-edge and local-radius based: no all-adjacent
endpoint rows, induced frontier graph, arbitrary cycle, or outgoing-list
shortcut.

2026-05-21 k4 selected raw-orbit lowering:

```lean
S2SeededRawOrbitSource
  .rawOrbitDartEdgeFrontierSource_of_boundaryFree_selectedFaceSuccEdge_20260521k4
S2SeededRawOrbitSource
  .rawFaceSuccOrbit_edge_mem_unboundedFrontierEdgeSet_of_boundaryFree_selectedFaceSuccEdge_20260521k4
S2SeededRawOrbitSource
  .boundaryFreeConnectedRawOrbitSourceRows_of_componentTopology_boundaryFree_selectedFaceSuccEdge_20260521k4
S2SeededRawOrbitSource
  .selectedSeededRawFaceSuccOrbitSourceRows_of_componentTopology_boundaryFree_selectedFaceSuccEdge_20260521k4
S2SeededRawOrbitSource
  .selectedSeededRawFaceSuccOrbitSourceRows_family_of_componentTopology_boundaryFree_selectedFaceSuccEdge_20260521k4
S2SeededRawOrbitSource
  .selectedSeededRawFaceSuccOrbitSourceRows_of_componentTopology_boundaryFree_localAngularHeadBetween_20260521k4
ExteriorComponentTopology
  .unboundedFrontierCarrierGraph_connected_of_rawFaceSuccOrbit_tail_coverage_localSectorRows_20260521k4
```

This puts `SelectedSeededRawFaceSuccOrbitSourceRows` below the actual
component-topology row, `BoundaryFreeNoThirdGermSource`, and selected
orbit-free `RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource`; the second
wrapper lowers that selected edge row to
`RawOrbitIteratedFaceSuccHeadBetweenLocalAngularNoOrbitSource` for a supplied
boundary-free local angular source.  The seed dart is chosen through the
existing `UnboundedExteriorFrontierSeed` constructor, and the raw dart
open-segment frontier row is built from selected
`unboundedFrontierEdgeSet` propagation plus local sector midpoint rows.  The
exact remaining raw-orbit blocker on this lane is therefore the selected
local-angular head-between source at the geometric `faceSucc` successor tail,
plus the separate repeated-tail cut rows for converting the seed-visible orbit
to final raw source rows.

The carrier-connectedness part of this k4 lane is now checked directly from
raw `faceSucc` tail coverage plus pointwise local-sector rows.  It stays on
the actual `unboundedFrontierCarrierGraph C inputs`: cyclic coverage is built
internally from consecutive raw tail open-segment frontier rows, whose carrier
adjacencies are selected by `unboundedFrontierEdgeSet`, and then projected to
graph connectedness.  Verification:
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`
passed.  The exact remaining blocker for this connectedness cut is proving the
raw-tail coverage row for the actual exterior `faceSucc` orbit from the input
geometry.

2026-05-21 k4 no-cut degree-two update: the finite-plane no-cut-to-degree
source is now named directly in `S2CarrierLocalSource.lean`:

```lean
S2_dynamic_no_cut_degree_two_k4_of_cutPartitionInputSource
S2_dynamic_no_cut_degree_two_k4_of_unreachableAfterDeleteInputSource
S2_dynamic_no_cut_selectedIncidentRows_k4_of_unreachableAfterDeleteInputSource
S2_dynamic_no_cut_degree_two_family_k4_iff_unreachableAfterDeleteInputSource
```

This is a strict local lowering, not a new source theorem.  The no-cut field
inside `FinitePlanarOuterComponentInputs` is consumed by the existing
cut-partition/unreachable-after-delete erasers: a third actual carrier
neighbour would supply a concrete `CutVertexInterface.CutVertexPartition`,
contradicting no-cut, so the two selected `unboundedFrontierEdgeSet` heads are
exactly the carrier neighbours.  The exact remaining blocker is now the lower
ambient deleted-graph source: for every actual exterior-frontier carrier
vertex, construct two selected incident frontier edges and prove any proposed
third carrier neighbour is unreachable from one selected side after deleting
the carrier vertex.

The current shortest checked route to S2 after the 2026-05-21 k2 handoff is:

```text
PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
+ forall C inputs,
    exists B,
      graph vertices on frontier exterior iff vertices of B
      + forall k, BoundaryVertexExteriorSectorRowsAt inputs B k
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget
```

2026-05-21 k1/k2 update: the topology side now composes at the generic
pairwise subcontinuum-between theorem, and the W32 route also accepts the
primitive same-boundary exterior-sector package directly:

```lean
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_carrierCutFieldwise_20260521k1
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumBetween_boundaryVertexExteriorSectorRows_20260521k2
```

The remaining source leaves on this displayed route are the standard
pairwise frontier subcontinuum theorem for unbounded complement components
and the actual construction of the exterior unit-distance boundary cycle with
same-boundary exterior-sector rows.

2026-05-21 k4 finite-drawing local-isolation update: the finite drawing and
actual exterior-component layers now expose consumer-shaped local carrier
facts for the exterior frontier carrier/orbit construction:

```lean
FinitePlaneDrawing
  .exists_ball_inter_embeddedEdgeSet_eq_inter_closedSegment_of_adj_inOpenSegment
FinitePlaneDrawing
  .exists_ball_inter_frontier_drawingComplement_subset_closedSegment_of_inOpenSegment
FinitePlaneDrawing
  .exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_closedSegment_of_inOpenSegment
FinitePlaneDrawing
  .exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_closedSegment_of_adj_inOpenSegment
FinitePlaneDrawing
  .exists_ball_inter_frontier_connectedComponentIn_drawingComplement_subset_incident_closedSegment
ExteriorComponentTopology
  .exists_ball_inter_unboundedExterior_frontier_subset_closedSegment_of_unboundedFrontierEdgeSet_inOpenSegment
ExteriorComponentTopology
  .exists_ball_inter_unboundedExterior_frontier_subset_inOpenSegment_of_unboundedFrontierEdgeSet_inOpenSegment
ExteriorComponentTopology
  .exists_ball_forall_unboundedExterior_frontier_mem_closedSegment_of_unboundedFrontierEdgeSet_inOpenSegment
ExteriorComponentTopology
  .exists_ball_forall_unboundedExterior_frontier_mem_inOpenSegment_of_unboundedFrontierEdgeSet_inOpenSegment
```

These are not new source assumptions.  They package existing straight-line
local isolation and the selected `unboundedFrontierEdgeSet` definition so
local carrier/orbit proofs can directly use: near an interior selected
frontier edge, the actual unbounded exterior frontier remains on that edge;
near a vertex, the selected component frontier is carried by incident closed
segments.

2026-05-21 k4 topology lowering: the pairwise subcontinuum-between topology
leaf now has a direct checked reduction from the boundedness-contradiction
closed-split source:

```lean
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_closedSeparationForcesBounded
```

The proof takes the whole selected frontier as the compact connected witness
after `PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesBounded`
rules out any nonempty disjoint closed cover of that frontier by contradicting
the supplied unboundedness.  The exact remaining topology source on this
branch is therefore
`PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesBounded`.
Verification:
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology`.

2026-05-21 k4 local-sector update: the pointwise local-sector/two-germ source
now has a checked fieldwise local finite-plane source in
`S2LocalTwoGermAssembly`:

```lean
S2LocalTwoGermAssembly
  .SelectedUnboundedFrontierEdgeLocalIsolationRowsAt
S2LocalTwoGermAssembly
  .SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
S2LocalTwoGermAssembly
  .SelectedUnboundedFrontierEdgeLocalIsolationRowsAt.toLocalTwoGermRowsAt
S2LocalTwoGermAssembly
  .localTwoGermRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
S2LocalTwoGermAssembly
  .localSectorRows_of_selectedUnboundedFrontierEdgeLocalIsolationSourceRows
```

This is not a new final facade.  The residual row names exactly the missing
local finite-drawing statement: for each actual unbounded-frontier carrier
vertex, choose two genuine selected `unboundedFrontierEdgeSet` incident heads
and a local radius, then prove every sufficiently nearby noncenter point of
the actual unbounded exterior frontier that is witnessed in an incident W3
germ has one of those two heads.  The eraser shrinks by the existing vertex-star
isolation radius and obtains the local two-germ row, then reuses the checked
two-germ-to-sector reducer.  Verification:
`elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean`
and
`elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly`
passed.

2026-05-21 j15 update: the U-indexed Janiszewski subcontinuum-forces-bounded
topology source now composes directly with the e32 actual selected-carrier cut
fieldwise source:

```lean
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumForcesBounded_carrierCutFieldwise_20260521j15
```

This keeps the W32 handoff below the U-pair frontier-component alias.  The two
remaining source leaves on this displayed route are now the Janiszewski
subcontinuum-boundedness theorem and the e32 actual carrier cut fieldwise
theorem.

2026-05-21 j16 update: the e32 actual-carrier cut fieldwise theorem now has a
checked strict source reduction from the actual exterior-sector input package:

```lean
S2CarrierCutSource
  .S2_agent_carrier_cut_fieldwise_source_20260521j16_of_actualExteriorSectorInputSourceRows
S2CarrierCutSource
  .S2_agent_carrier_cut_fieldwise_source_family_20260521j16_of_actualExteriorSectorInputSourceRows
S2CarrierCutSource
  .S2_agent_carrier_cut_fieldwise_source_20260521j17_of_boundaryVertexExteriorSectorRows
S2CarrierCutSource
  .S2_agent_carrier_cut_fieldwise_source_family_20260521j17_of_boundaryVertexExteriorSectorRows
```

The local residual below e32 is therefore an actual boundary cycle `B` with
exact unbounded-frontier vertex coverage and
`Nonempty (ActualExteriorSectorInputSourceRows inputs B)`, or equivalently
the primitive same-boundary `BoundaryVertexExteriorSectorRowsAt` family with
the same exact frontier-vertex equivalence.  This keeps the source
selected-edge/sector based and does not use induced frontier graphs,
all-adjacent endpoint rows, arbitrary cycles, convex hull shortcuts, synthetic
enclosures, identity angular order, or outgoing-list no-between.

The point-level crossing-subcontinuum source also now feeds the pairwise
subcontinuum-between and preconnected-frontier theorem surfaces directly:

```lean
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_crossingSubcontinuumPointsBetween
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierPreconnected_of_crossingSubcontinuumPointsBetween
```

The current j15 topology leaf is also lowered directly from the U-indexed
point-between boundary-bumping theorem:

```lean
ExteriorComponentTopology
  .planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_subcontinuumPointsBetween
```

2026-05-21 j14 update: the U-indexed pair frontier-component topology source
now composes directly with the e32 actual selected-carrier cut fieldwise source:

```lean
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_uPairFrontierComponent_carrierCutFieldwise_20260521j14
```

This keeps the W32 handoff below the point-between topology alias.  The two
remaining source leaves on this displayed route are now the U-indexed
Janiszewski pair frontier-component theorem and the e32 actual carrier cut
fieldwise theorem.

2026-05-21 j11 update: the point-level crossing-subcontinuum topology source
now composes directly with the e32 actual selected-carrier cut fieldwise source:

```lean
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuumPointsBetween_carrierCutFieldwise_20260521j11
```

This keeps the current W32 handoff below the continuous-side alias.  The two
remaining source leaves on this displayed route are the point-level planar
topology theorem and the e32 actual carrier cut fieldwise theorem.

2026-05-21 j10 update: the continuous-side topology source now composes
directly with the e32 actual selected-carrier cut fieldwise source:

```lean
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_continuousKSide_carrierCutFieldwise_20260521j10
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_continuousKSide_carrierCutFieldwise_20260521j10
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_continuousKSide_carrierCutFieldwise_20260521j10
```

This is a checked composer only.  It should not replace the lower non-circular
topology source when proving topology; it keeps the W32 route executable from
the current continuous-side source plus the actual carrier cut fieldwise source.

2026-05-21 j1 update: the topology source in the previous route was strictly
lowered by a direct checked handoff:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
-> PlanarContinuumUnboundedComplementFrontierPreconnected
```

with the corresponding selected-carrier finite-theorem and W32 consumers:

```lean
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierPreconnected_of_closedSeparationForcesContinuumSeparation
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_closedSeparationForcesContinuumSeparation_actualCarrierDegreeTwo_20260521j1
```

The two live source leaves are therefore the closed-frontier
continuum-separation theorem and the e32 fieldwise carrier cut source for the
selected unbounded-frontier carrier graph.

2026-05-21 j7 topology lowering: the closed-frontier continuum-separation
source now has a direct checked route from the same-`K` boundary-bumping point
source:

```lean
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation_of_janiszewskiKComponentPointsBetween
```

This makes
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`
the smallest named topology source on the current checked branch.

2026-05-21 j8 local-carrier lowering: the local e32/actual-degree branch now
accepts the honest exterior face-dart carrier package directly:

```lean
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_faceDartOrbitExteriorCarrierRows
S2CarrierCutSource
  .S2_agent_carrier_cut_fieldwise_source_20260521j8_of_faceDartOrbitExteriorCarrierRows
```

Thus the current local construction source can be stated as
`FaceDartOrbitExteriorCarrierRows C inputs`: an actual exterior face-orbit
carrier whose edges are selected `unboundedFrontierEdgeSet` incidences.  This
is not an induced frontier graph, an all-adjacent endpoint row, or an
outgoing-list/no-between row.

2026-05-21 j9 handoff: the same-`K` topology leaf is now composed directly
with the e32 fieldwise actual-carrier cut source, with cycle-row, finite
outer-component, and W32 handoffs:

```lean
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiKComponentPointsBetween_carrierCutFieldwise_20260521j9
```

The i1/j1 actual-carrier-degree route remains checked as a compatibility
route:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
+ forall C inputs, S2CarrierLocalSource.ActualCarrierDegreeTwoSource inputs
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget
```

The h3/h6 route remains checked as a compatibility route:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ forall C inputs a, UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget
```

Checked cycle and W32 composers:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_closedSeparationForcesContinuumSeparation_carrierCutFieldwise_20260521i5
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_carrierCutFieldwise_20260521i5
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
S2CarrierLocalSource
  .finitePlanarStraightLineOuterComponentTheorem_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_planarContinuumPreconnected_actualCarrierDegreeTwo_20260521i1
ExteriorComponentTopology
  .unboundedExteriorFrontierCycleRows_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
ExteriorComponentTopology
  .unboundedExteriorFrontierCycleRowsFamily_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
ExteriorComponentTopology
  .finitePlanarStraightLineOuterComponentTheorem_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_planarContinuumPreconnected_localTwoGermRows_20260521i1
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_frontierSubcontinuum_boundarySectorSource_20260521
ExteriorComponentTopology
  .S2_agent_topology_frontier_subcontinuum_source_20260521g1
S2CarrierLocalSource
  .actualCarrierDegreeTwo_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_cutPartitions
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_selectedSeededRawFaceSuccOrbitSourceRows_deletedTailWitnesses
S2CarrierLocalSource
  .actualCarrierDegreeTwo_family_of_selectedSeededRawFaceSuccOrbitSourceRows_cutPartitions
S2CarrierLocalSource
  .actualCarrierDegreeTwo_family_of_selectedSeededRawFaceSuccOrbitSourceRows_deletedTailWitnesses
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_cutPartitions
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_selectedRawTailCoverageSourceRows_repeatedTailWitnessSource
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions
S2CarrierLocalSource
  .actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedRepeatedTailWitnessSource
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_selectedCutPartitions_20260521
S2SeededRawOrbitSource
  .finitePlanarStraightLineOuterComponentTheorem_of_connectedRawOrbitSourceRows_deletedTailWitnesses_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows_deletedTailWitnesses_20260521
S2SeededRawOrbitSource
  .unboundedExteriorFrontierCycleRows_family_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_successorPoint_20260521
S2SeededRawOrbitSource
  .finitePlanarStraightLineOuterComponentTheorem_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_successorPoint_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_successorPoint_20260521
S2SeededRawOrbitSource
  .unboundedExteriorFrontierCycleRows_family_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_localTransition_20260521
S2SeededRawOrbitSource
  .finitePlanarStraightLineOuterComponentTheorem_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_localTransition_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_localTransition_20260521
S2SeededRawOrbitSource
  .carrierCutpartitionInputSource_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
S2SeededRawOrbitSource
  .carrierCutpartitionInputSource_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
ExteriorComponentTopology
  .S2_agent_topology_boundedness_source_20260521f8
S2CarrierCutSource
  .S2_agent_carrier_cutpartition_source_family_20260521f9_of_boundarySectorSource
S2TopologySource
  .S2_agent_U_pair_source_from_K_component_20260521e69
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_kComponentFrontierComponent_selectedIncidentEdgePairRows_20260521
S2CarrierLocalSource
  .S2_agent_local_selected_source_from_carrier_degree_20260521e70
S2TopologySource
  .S2_main_U_frontier_component_pair_source_20260521e68
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_pairFrontierComponent_selectedIncidentEdgePairRows_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumPointsBetween_selectedIncidentEdgePairRows_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_subcontinuumCarrier_selectedIncidentEdgePairRows_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiSubcontinuumPointsBetween_actualCarrierDegreeTwo_20260521
FaceBoundaryTopologySourceW32
  .unboundedExteriorFrontierCycleRows_of_pointsBetween_actualCarrierDegreeTwo_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_pointsBetween_actualCarrierDegreeTwo_20260521
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h1
ExteriorComponentTopology
  .boundaryFreeLocalInputSourceReduction_of_localTwoGermRows_20260521h1
ExteriorComponentTopology
  .boundaryFreeLocalInputSourceReduction_of_neighborPairCutPartitionInputSource_20260521h2
ExteriorComponentTopology
  .boundaryFreeLocalInputSourceReduction_of_neighborPairRows_20260521h4
ExteriorComponentTopology
  .nonempty_boundaryFreeLocalInputSourceReduction_iff_neighborPairRows_20260521h5
S2CarrierLocalSource
  .actualCarrierDegreeTwo_iff_boundaryFreeLocalInputSourceReduction_20260521h5
S2CarrierLocalSource
  .localTwoGermRows_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .localTwoGermRows_family_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .nonempty_localTwoGermRows_iff_actualCarrierDegreeTwo
S2CarrierLocalSource
  .localTwoGermRows_family_iff_actualCarrierDegreeTwo
```

2026-05-21 h3 live-cycle handoff:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ forall C inputs a, UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a
-> UnboundedExteriorFrontierCycleRows C inputs
-> FinitePlanarStraightLineOuterComponentTheorem
```

The h3 task is only the explicit cycle-row/outer-component handoff for the
already displayed live leaves.  It does not add a new source package, W facade,
or alternate local statement.

Checked declarations:

```lean
ExteriorComponentTopology
  .unboundedExteriorFrontierCycleRows_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
ExteriorComponentTopology
  .unboundedExteriorFrontierCycleRowsFamily_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
ExteriorComponentTopology
  .finitePlanarStraightLineOuterComponentTheorem_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h3
```

Targeted build passed:

```text
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2BoundaryFreeRawSource
```

2026-05-21 h6 W32 finite-theorem handoff:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ forall C inputs a, UnboundedFrontierCarrierLocalTwoGermRowsAt inputs a
-> FinitePlanarStraightLineOuterComponentTheorem
-> MinimalFailureExactActualTopologyFieldsTarget
```

Checked declaration:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiSubcontinuumPointsBetween_localTwoGermRows_20260521h6
```

Targeted build passed:

```text
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

2026-05-21 h7 f9 boundary-sector cycle handoff:

```text
S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9 inputs
-> Nonempty (UnboundedExteriorFrontierCycleRows C inputs)
```

The f9 source is a Prop existential over the actual boundary cycle, exact
frontier-vertex equivalence, and primitive sector rows.  Because it is a Prop
source, the direct target is `Nonempty`; the actual source proof still has to
construct the boundary-sector package from `FinitePlanarOuterComponentInputs`.

Checked declarations:

```lean
S2CarrierCutSource
  .nonempty_unboundedExteriorFrontierCycleRows_of_boundarySectorSource_20260521h7
S2CarrierCutSource
  .nonempty_unboundedExteriorFrontierCycleRows_family_of_boundarySectorSource_20260521h7
```

Targeted build passed:

```text
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2CarrierCutSource
```

2026-05-21 e68 update: the topology leaf is now lowered to the pure U-indexed
frontier-component pair source:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent
S2_main_U_frontier_component_pair_source_20260521e68
```

This source says that for the displayed compact connected `T <= K`, the two
selected points of `frontier U` already lie in the same connected component of
`frontier U`.  The checked reducer only packages that component as the compact
connected witness required by the earlier point-between leaf.

2026-05-21 f7 update: the U-indexed pair frontier-component source now has a
checked strict reducer that avoids the same-`K`, continuous-side,
relative-clopen, final S2, and finite frontier-cycle routes:

```lean
planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_noSubcontinuumObstruction
S2_agent_U_pair_frontier_component_source_20260521f7
```

The claim wrapper reduces
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPairFrontierComponent`
to the boundedness/crosscut source
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded`
through the existing direct no-subcontinuum obstruction.  The proof obtains a
compact connected frontier witness from the obstruction and translates it to
subtype connected-component membership in `frontier U`.

2026-05-21 f8 update: the boundedness/crosscut source now has a checked
strict reducer that avoids the same-`K`, continuous-side, relative-clopen,
final S2, finite frontier-cycle, and f7 no-subcontinuum-consumer routes:

```lean
planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_of_frontierSubcontinuum
S2_agent_topology_boundedness_source_20260521f8
```

The residual source is the direct U-indexed frontier-subcontinuum witness:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
```

The proof assumes the selected component is unbounded, uses the witness source
to produce a compact connected subset of `frontier U` meeting both closed
sides, and contradicts connectedness by the displayed closed frontier cover.

2026-05-21 e69 update: the pair source is now strictly reduced to the existing
same-`K` frontier-component theorem:

```lean
planarJaniszewskiBoundaryBumpingSubcontinuumPairFrontierComponent_of_kComponentFrontierComponent
S2_agent_U_pair_source_from_K_component_20260521e69
```

This uses connectedness of `T` only to put `z` in `connectedComponentIn K y`,
then translates `connectedComponentIn (frontier U) y` to subtype connected
component membership.

The topology leaf is consumed by:

```text
points-between
-> S2_agent_continuous_side_source_worker_20260521e42
-> S2_agent_topology_source_worker_20260521e40
-> S2_dyn_20260520_aligned_K_split_source
-> unboundedExteriorFrontierCycleRows_of_planarContinuumAlignedKSplit_localSectorRows
```

2026-05-21 refinement: the point-between topology leaf now has a strict
frontier-component reducer in `S2TopologySource.lean`:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumFrontierComponent
S2_agent_points_between_source_scout_20260521e45
S2_agent_frontier_component_source_20260521e48_adapter
```

The adapter reduces the crossing-subcontinuum frontier-component source to the
already isolated Janiszewski same-`K` frontier-component theorem:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
```

2026-05-21 e54 update: the point-between topology leaf also has a direct
non-circular planar-theorem reducer in `S2TopologySource.lean`:

```lean
S2_agent_point_between_honest_source_prover_20260521e54
```

It consumes exactly

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
```

This U-indexed source says that for an unbounded complement component `U` and a
compact connected `T <= K`, two points of `T` on `frontier U` are joined by a
compact connected subset of `frontier U`.  The reducer only specializes `U` to
`connectedComponentIn Kᶜ x`; it does not route through continuous-side,
relative-clopen, same-`K` frontier component, no-subcontinuum,
component-avoidance, crossing-boundedness, finite no-closed-separation, or
final boundary-cycle rows.

2026-05-21 e61 update: the carrier source below that U-indexed point theorem
now has a checked strict reducer in `S2TopologySource.lean`:

```lean
planarJaniszewskiBoundaryBumpingSubcontinuumCarrier_of_kComponentFrontierComponent
S2_agent_subcontinuum_carrier_source_20260521e61
```

It lowers
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumCarrier`
to the same-`K` frontier-component theorem by choosing one point in
`T ∩ frontier U`, using connectedness of `T` to put every trace point in
`connectedComponentIn K y`, and packaging the connected component of
`frontier U` through `y` as the compact connected carrier.  This remains a
topology source reducer, not a boundary-cycle or finite-drawing route.

The same-`K` frontier-component theorem is already strictly reduced in
`ExteriorComponentTopology.lean` by:

```lean
planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_relativeClopenKSide
S2_agent_frontier_component_source_worker_20260521e31
```

The standard Janiszewski/boundary-bumping relative-clopen theorem is itself
now reduced by `S2_agent_relative_clopen_source_prover_20260521e49` to the
lower continuous-side source:

```lean
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide
```

The W32-facing route also has a checked direct composer:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiKComponentFrontierComponent_actualCarrierDegreeTwo_20260521
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiRelativeClopen_actualCarrierDegreeTwo_20260521
```

The second composer is the current shortest W32 handoff from the standard
Janiszewski relative-clopen topology source plus the local actual-carrier
degree-two family and S1 no-cut rows.

The local leaf is consumed by:

```text
ActualCarrierDegreeTwoSource inputs
-> S2CarrierLocalSource.localSectorRows_of_actualCarrierDegreeTwo
-> unboundedExteriorFrontierCycleRows_of_planarContinuumAlignedKSplit_localSectorRows
```

The local actual-degree leaf now has family erasers in
`S2CarrierLocalSource.lean` from the following lower source families:

```lean
actualCarrierDegreeTwo_family_of_boundaryFreeLocalNoThirdGermSourceRows
actualCarrierDegreeTwo_family_of_cutPartitionInputSource
actualCarrierDegreeTwo_family_of_deletedNeighborLocalSeparationInputSource
actualCarrierDegreeTwo_family_of_deletedNeighborLocalSeparationExactFieldSource
actualCarrierDegreeTwo_family_of_localSelectedNoThirdGermSource
```

2026-05-21 f1/e72 update: the live actual-degree leaf is now pinned exactly to
the e32 fieldwise carrier-cut package:

```lean
actualCarrierDegreeTwo_family_iff_localSelectedIncidentEdgePairSourceRows
actualCarrierDegreeTwo_iff_carrierCutFieldwise
actualCarrierDegreeTwo_family_of_carrierCutFieldwise
actualCarrierDegreeTwo_family_iff_carrierCutFieldwise
S2_codex_local_carrier_source_20260521f1
```

The concrete carrier now also has the checked graph-side consequence

```lean
S2CarrierLocalSource
  .three_le_unboundedFrontierVertexSet_card_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .three_le_unboundedFrontierCarrier_fintype_card_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .selectedFrontierEdgeCover_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .selectedFrontierEdgeCover_family_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .unboundedFrontierCarrierGraph_connected_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
S2CarrierLocalSource
  .unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
S2CarrierLocalSource
  .neighborPairRows_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .neighborPairRows_family_of_actualCarrierDegreeTwo
S2CarrierLocalSource
  .actualCarrierDegreeTwo_iff_neighborPairRows
S2CarrierLocalSource
  .actualCarrierDegreeTwo_family_iff_neighborPairRows
```

so any branch that has sourced actual degree two may use at least three actual
unbounded-frontier graph vertices, the selected exterior-frontier edge cover,
the finite-no-closed-separation connected/cycle support route, and the
pointwise concrete carrier neighbour-pair rows without re-opening
singleton/two-vertex carrier cases or re-proving fixed-side edge coverage.

The remaining local theorem is therefore precisely:

```lean
forall C inputs,
  S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise
    inputs
```

This is the actual exterior-carrier source: two selected
`unboundedFrontierEdgeSet` heads at each actual carrier vertex and a concrete
cut partition for every third actual carrier neighbour.

2026-05-21 f9 update: the exact cut-partition family now has a checked
source reduction in `S2CarrierCutSource.lean`:

```lean
S2_agent_carrier_cutpartition_boundarySectorSource_20260521f9
S2_agent_carrier_cutpartition_source_20260521f9_of_boundarySectorSource
S2_agent_carrier_cutpartition_fieldwise_20260521f9_of_boundarySectorSource
S2_agent_carrier_cutpartition_source_family_20260521f9_of_boundarySectorSource
S2_agent_carrier_cutpartition_fieldwise_family_20260521f9_of_boundarySectorSource
```

It lowers
`forall C inputs, Nonempty (UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs)`
to one concrete same-boundary exterior-sector source: a boundary object with
exact frontier-vertex equivalence plus primitive
`BoundaryVertexExteriorSectorRowsAt` rows for that same object.  The selected
heads are actual predecessor/successor `unboundedFrontierEdgeSet` incidences,
and incident completeness makes the third-neighbour cut branch unreachable.

2026-05-21 g2 update: the f9 same-boundary exterior-sector source is now
strictly reduced in `S2SeededRawOrbitSource.lean` to the connected raw-orbit
route:

```lean
boundaryVertexExteriorSectorRows_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
boundaryVertexExteriorSectorRows_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
carrierCutpartitionBoundarySectorSource_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
carrierCutpartitionBoundarySectorSource_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
```

The remaining local/raw leaves are therefore the connected raw exterior-orbit
rows, selected repeated-tail cut partitions, and selected raw orientation for
the same selected orbit.  This keeps all carrier edges as actual
`unboundedFrontierEdgeSet` edges and still avoids induced frontier graphs,
arbitrary cycles, all-adjacent endpoint rows, identity angular order, and
selected-head all-outgoing no-between.

2026-05-21 g1 update: the f8 frontier-subcontinuum source is now strictly
reduced in `ExteriorComponentTopology.lean` to the U-indexed point-between
source:

```lean
planarJaniszewskiBoundaryBumpingCrossingSubcontinuumYieldsFrontierSubcontinuum_of_subcontinuumPointsBetween
S2_agent_topology_frontier_subcontinuum_source_20260521g1
```

The remaining topology leaf is therefore:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
```

2026-05-21 h13 update: the connected compactum topology surfaces are now
checked-equivalent in `ExteriorComponentTopology.lean`:

```lean
planarContinuumUnboundedComplementFrontierConnected_of_subcontinuumBetween
planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_connected
```

The new direction uses the existing nonempty-frontier row for unbounded
complement components plus the earlier subcontinuum-between-to-preconnected
reducer.  Do not spend new topology work cycling between
`PlanarContinuumUnboundedComplementFrontierConnected` and
`PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween`; the remaining
planar source is below that equivalence, such as the closed-split/Janiszewski
boundary-bumping content.

2026-05-21 g3 update: the same connected raw-orbit, selected repeated-tail,
and selected raw-orientation leaves now feed the sharp local input source and
actual-carrier degree-two source as well:

```lean
carrierCutpartitionInputSource_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
carrierCutpartitionInputSource_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
actualCarrierDegreeTwo_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
actualCarrierDegreeTwo_family_of_connectedRawOrbitSourceRows_selectedCutPartitions_rawOrientation_20260521j
```

Thus the local/raw S2 source should be worked directly at the three remaining
rows:

```text
BoundaryFreeConnectedRawOrbitSourceRows inputs
+ selected repeated-tail cut partitions for its selected raw orbit
+ SelectedRawOrbitOrientationRows for that same selected raw orbit
```

2026-05-21 e64 read-only route check: the smallest non-circular topology
target among the currently named topology leaves remains:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
```

Mathlib supplies the generic component/clopen tools used by the checked
reducers, but not the Janiszewski/boundary-bumping theorem itself.

2026-05-21 f2 update: the exact same-`K` frontier-component source now has a
direct checked reducer from the continuous Boolean side source in
`ExteriorComponentTopology.lean`:

```lean
planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_continuousKSide
S2_agent_topology_k_component_source_20260521f2
```

This composes the existing continuous-side-to-relative-clopen bridge with the
frontier-component reducer.  It is a support reducer only: it does not use
final S2 rows, finite frontier-cycle rows, finite no-closed-separation, or a
new facade, and it should not be looped back through point-between aliases.

Topology e51 reduction:

```lean
planarContinuumUnboundedComplementFrontierContinuousKSide_of_pointsBetween_closedSplit
S2_agent_continuous_side_source_prover_20260521e51
```

So the preferred topology leaf has been lowered again to the point-between
source:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
```

This is the same source consumed by the direct W32 point-between composer.  Do
not loop this back through the continuous-side or relative-clopen aliases.

Route audit e56: after e51, any displayed live route whose topology source is
`PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide`
is an alias route, not a source route.  The non-circular W32 split is:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
+ forall C inputs, S2CarrierLocalSource.ActualCarrierDegreeTwoSource inputs
+ S1 noCutRows
-> W32
```

The local source can be lowered further through e52/e53 to:

```lean
forall {m : Nat} (C : UDConfig m)
  (inputs : FinitePlanarOuterComponentInputs C),
    UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource inputs
```

2026-05-21 e55 update: exact deleted-neighbour local separation is equivalent
to actual carrier two-regularity in `S2CarrierLocalSource.lean`:

```lean
deletedNeighborLocalSeparationExactFieldSource_of_actualCarrierDegreeTwo
S2_agent_deleted_neighbor_exact_source_prover_20260521e55
nonempty_deletedNeighborLocalSeparationExactFieldSource_iff_actualCarrierDegreeTwo
```

2026-05-21 local two-germ update: pointwise local two-germ rows now erase
directly to the same actual-carrier degree source in `S2CarrierLocalSource.lean`:

```lean
actualCarrierDegreeTwo_of_localTwoGermRows
actualCarrierDegreeTwo_family_of_localTwoGermRows
```

So the local leaf should be worked in its smallest current form:

```lean
forall {m : Nat} (C : UDConfig m)
  (inputs : FinitePlanarOuterComponentInputs C),
  letI := unboundedFrontierCarrierGraph_decidableAdj C inputs
  forall a : {v : Fin m // v ∈ unboundedFrontierVertexSet C inputs},
    ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2
```

Active claims e57/e58/e59 split the next work into the U-indexed
Janiszewski point-between theorem, the actual carrier degree-two theorem, and
the raw-orbit route into that local theorem.  These are source tasks; they
should not add W-numbered facades or route back through downstream aliases.

`S2BoundaryFreeRawSource.lean` also has e50 reductions:

```lean
BoundaryFreeLocalNoThirdGermSourceRows.toLocalSelectedNoThirdGermSource
boundaryFreeLocalNoThirdGermSourceRows_family_of_neighborPairCutPartitionInputSource
unboundedFrontierCarrierLocalSelectedNoThirdGermSource_family_of_neighborPairCutPartitionInputSource
```

The current local source work should target one of these lower source families
from `FinitePlanarOuterComponentInputs`, especially the actual
cut-partition input source; do not replace it with all-outgoing angular
no-between or induced-frontier graph rows.

Local e52/e53 reductions:

```lean
S2_agent_cutpartition_input_source_prover_20260521e52_of_deletedNeighborLocalSeparationExactFieldSource
S2_agent_cutpartition_input_source_prover_family_20260521e52_of_deletedNeighborLocalSeparationExactFieldSource
S2CarrierLocalSource.S2_agent_actual_carrier_degree_source_prover_20260521e53
```

The cut-partition family is now lowered to
`UnboundedFrontierCarrierDeletedNeighborLocalSeparationExactFieldSource`; the
actual-carrier degree family is lowered to the fieldwise cut-partition source.
The remaining local proof should build the exact deleted-neighbour local
separation or fieldwise cut-partition source from the finite planar inputs.

The finite-drawing no-closed-separation and neighbour-pair/cut-partition
routes remain checked support routes.  They should not be used as the live
source if doing so loops back through the point-between leaf, same-`K` aliases,
component-avoidance, no-subcontinuum, crossing-boundedness, final
boundary-cycle rows, induced frontier graphs, or all-adjacent endpoint rows.

## 2026-05-21 Local-Leaf Correction

Current preferred W32 route after the latest local-leaf correction:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs a, UnboundedFrontierCarrierNeighborPairAt inputs a
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_neighborPairRows_20260521
```

This is now the main S2 route. It avoids the over-strong selected-head
outgoing-list/no-between leaf and does not make the broader open-`K` cover
source the first topology target.

The same route is also checked with the local leaf written in the sharper
cut-partition source form:

```lean
FaceBoundaryTopologySourceW32.
  minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_cutPartitionInputSource_20260521
```

Owner-file gate passed for this direct composer:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

The compressed e15/e16 route remains a checked support route:

```text
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation
+ forall C inputs, UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_openKCoverSeparation_cutPartitionInputSource_20260521
```

The e15 topology reducer turns open-cover separation of `K` into the aligned
closed `K` split.  The e16 local reducer pins the carrier-neighbour row to the
cut-partition source using actual `unboundedFrontierEdgeSet` incidences and
the concrete `unboundedFrontierCarrierGraph`.

The support W32 composer above is checked: it first erases open-cover separation to
the aligned closed `K` split, erases the cut-partition source to actual
carrier-neighbour rows, and then applies the checked neighbor-pair W32 route.
The open-cover topology leaf now has a checked source reducer:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
-> PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation
```

via
`planarContinuumUnboundedComplementFrontierNontrivialOpenKCoverSeparation_of_nontrivialRelativeClopenKSide`.
It uses normal separation of the closed relative `K`-side and its closed
relative complement.
The same open-cover leaf is now reduced further:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
-> PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation
```

via `S2_agent_open_k_cover_source_worker_20260521e18`, and W32 has the checked
composer
`minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_cutPartitionInputSource_20260521`.
The local cut-partition input source has an exact fieldwise constructor:

```text
forall a, choose two incident unboundedFrontierEdgeSet heads at a
+ for every third carrier neighbour, CutVertexPartition C
-> UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

via `S2_agent_cutpartition_input_source_worker_20260521e19` and its exact-iff
family theorem.  This is now the precise local source theorem to prove from
finite plane graph topology/no-cut, not another wrapper target.

2026-05-21 e32 update: `ErdosProblems1066/Swanepoel/S2CarrierCutSource.lean`
records this fieldwise source as
`S2_agent_carrier_cut_source_worker_20260521e32_fieldwise`, proves its exact
iff against `UnboundedFrontierCarrierNeighborPairCutPartitionInputSource` using
the e19 exact iff, and strictly reduces it from
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource` via
the checked deleted-graph cut-partition eraser.  The same selected heads also
feed `S2_agent_selected_incident_edge_source_worker_20260521e25_of_selectedEdges_thirdCuts`.
So the remaining lower local source is deleted-graph nonreachability, or the
already named local separation source below it.

2026-05-21 e20/e21 reductions:

```text
PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
-> PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation
```

via `S2_live_component_avoidance_source_worker_20260521` and
`S2_agent_open_k_cover_source_worker_20260521e18`.

```text
forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a
-> UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

via `S2_agent_cutpartition_input_source_worker_20260521e21_of_localSectorRows`.
Equivalent checked erasers also accept local two-germ rows or the local
selected-edge/no-third-germ source.  The live source targets are therefore the
continuous side-map theorem and the pointwise local-sector/local-two-germ
source from `FinitePlanarOuterComponentInputs C`.

These two active leaves now have a direct checked W32 composer:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_continuousKSide_localSectorRows_20260521
```

e22/e23 reduce those leaves further:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide
```

via `S2_agent_continuous_side_source_worker_20260521e22`.

```text
LocalSelectedIncidentEdgePairSourceRows inputs
-> forall a, UnboundedFrontierCarrierLocalSectorRowsAt inputs a
```

via
`S2_agent_local_sector_source_worker_20260521e23_of_selectedIncidentEdgePairRows`.
So the current short source leaves are crossing-subcontinuum boundedness and
actual selected incident-edge pair rows for the unbounded frontier carrier.

e24 reduces the topology leaf one step further:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

via `S2_agent_crossing_bounded_source_worker_20260521e24`.  The direct checked
W32 composer for the current support route is now:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiCrossingSubcontinuum_selectedIncidentEdgeRows_20260521
```

Thus the compressed support route has exactly two source leaves:

```text
1. PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum

2. forall C inputs,
     LocalSelectedIncidentEdgePairSourceRows inputs
```

Explorer e26 identified an even more concrete non-circular topology source
already wired by existing reducers:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

through
`planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_janiszewskiKComponentPointsBetween`.
This route is preferred over the broader frontier-subcontinuum-yields source
when assigning the topology proof.

e29 strictly reduced that same-`K` point-between source to the direct
frontier-component theorem:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
```

The checked reducer is
`planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_frontierComponent`,
with claim wrapper
`S2_agent_kcomponent_points_between_worker_20260521e29`.  It takes the
connected component of `y` inside `frontier U`, uses compactness of that
frontier for unbounded complement components of compact planar sets, and
packages the component image as the compact connected witness containing
`y` and `z`.  The remaining source is exactly to prove
`z in connectedComponentIn (frontier U) y` from
`z in connectedComponentIn K y`; no crossing-boundedness, component-avoidance
loop, or reverse relative-clopen alias is used.

e31 strictly reduces that direct frontier-component source to the
Janiszewski closed-frontier relative-clopen K-side theorem:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
```

The checked reducer is
`planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_relativeClopenKSide`,
with claim wrapper
`S2_agent_frontier_component_source_worker_20260521e31`.  If `z` is not in the
connected component of `y` inside `frontier U`, the proof uses compact-Hausdorff
quasicomponent separation to split `frontier U` by clopen frontier pieces; the
relative-clopen K-side for that split separates `y` and `z` in `K`,
contradicting `z in connectedComponentIn K y`.  This is a direct frontier
separation reduction and does not pass through crossing-boundedness,
component-avoidance, or a reverse relative-clopen alias.

e25 reduces the local selected-incident leaf:

```text
degree-two of the actual unboundedFrontierCarrierGraph
-> LocalSelectedIncidentEdgePairSourceRows inputs
```

via
`S2_agent_selected_incident_edge_source_worker_20260521e25_of_carrier_degree_two`.
It also provides the more explicit selected-head/cut-partition source:

```text
selected actual unbounded-frontier heads at each frontier vertex
+ third-neighbour cut partitions
-> LocalSelectedIncidentEdgePairSourceRows inputs
```

via
`S2_agent_selected_incident_edge_source_worker_20260521e25_of_selectedEdges_thirdCuts`.
So the local source leaf is now the actual carrier degree-two theorem, or the
equivalent selected-head plus third-neighbour cut-partition theorem.

Explorer e27 confirmed the shortest non-circular local source is the actual
carrier cut/deletion package:

```text
UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
-> LocalSelectedIncidentEdgePairSourceRows inputs
```

through
`S2_agent_third_neighbor_cut_source_20260521f_selectedIncidentEdgePairRows` or
the e25 fieldwise selected-edge reducer.  If the proof naturally produces
deleted-graph nonreachability instead, use
`UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource` and
then `S2_dyn_20260520_selected_edge_pair_rows_of_unreachableAfterDeleteInputSource`.
Do not use the reverse adapter from selected incident rows back to cut rows.

e29 reduces the topology point-between source to the direct
frontier-component theorem:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
```

via `S2_agent_kcomponent_points_between_worker_20260521e29`.

e30 confirmed the local leaf should be the fieldwise actual-carrier cut source
packaged by `S2_agent_cutpartition_input_source_worker_20260521e19`.
The sharpest current checked W32 composer is:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_frontierComponent_cutPartitionInputSource_20260521
```

Its two source leaves, apart from S1 no-cut rows, are:

```text
1. PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent

2. forall C inputs,
     UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

e31 reduces the first leaf to the Janiszewski relative-clopen K-side source:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
```

via `S2_agent_frontier_component_source_worker_20260521e31`.  The corresponding
W32 composer is:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_cutPartitionInputSource_20260521
```

The current two source leaves, apart from S1 no-cut rows, are now:

```text
1. PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide

2. forall C inputs,
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

e32 records this local source in `S2CarrierCutSource.lean`.  It provides the
fieldwise residual, the exact iff with the e19 input source, and the forward
deleted-neighbour route:

```text
UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
-> UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

via `S2_agent_carrier_cut_source_worker_20260521e32_of_unreachableAfterDelete`.
W32 now also has:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_relativeClopenKSide_unreachableAfterDeleteInputSource_20260521
```

e34 found no bare-input theorem already present for the carrier cut source.
The non-circular forward local sources available in the code are local-sector
rows, local-two-germ rows, pointwise cut-partition rows, or deleted-neighbour
unreachable-after-delete rows.

e36 reduces the topology leaf to the direct Janiszewski no-subcontinuum
obstruction:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
```

via `S2_agent_relative_clopen_source_worker_20260521e36`.  W32 now has:

```lean
FaceBoundaryTopologySourceW32
  .minimalFailureExactActualTopologyFieldsTarget_of_noSubcontinuum_unreachableAfterDeleteInputSource_20260521
```

Its two source leaves, apart from S1 no-cut rows, are:

```text
1. PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction

2. forall C inputs,
     UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
```

e35 reduces the local deleted-neighbour source to actual carrier degree two:

```text
forall C inputs a,
  ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2
-> forall C inputs,
     UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
```

via
`S2_agent_local_two_germ_source_worker_20260521e35_unreachableAfterDelete_of_carrier_degree_two`.
It keeps the selected heads in `unboundedFrontierEdgeSet`; this is still a
source reduction, not a proof of degree two from bare inputs.

e38 confirms the shortest no-subcontinuum topology route is:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesNontrivialRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
```

via `janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide`,
`planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_relativeClopenKSide`,
and the composed wrapper `S2_agent_no_subcontinuum_route_scout_20260521d3`.
So the topology source below the current W32 composer is the nontrivial
relative-clopen side theorem, unless a worker proves the no-subcontinuum
obstruction directly.

The preferred W32-facing S2 route is now:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
+ forall C inputs,
     carrier degree two for the actual unboundedFrontierCarrierGraph
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiKComponentPointsBetween_carrierDegreeTwo_20260521
```

Equivalently, the local degree-two leaf can be replaced by:

```text
forall C inputs,
  UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

or the displayed fieldwise form from
`S2_agent_cutpartition_input_source_worker_20260521e19_exact_iff`.

The older finite-drawing route remains useful:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs a, UnboundedFrontierCarrierNeighborPairAt inputs a
+ S1 noCutRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_neighborPairRows_20260521
```

This supersedes both the route that made
`UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs` or
selected-head `GraphVertexGeometricOutgoingListNoBetweenRows` the live local
source leaf and the route that made the broader open-`K` cover theorem the
first topology target.  Those rows remain compatibility/support surfaces only.
Do not assign them as the main S2 source unless the proof explicitly uses a
cyclic exterior-sector orientation and does not exclude legal interior unit
chords.
Later dated workbook sections are an archive of tried routes and checked
reducers.  If a later section says "live", "current", "shortest", or "active"
while pointing at selected-head outgoing-list/no-between, geometric-neighbour
rows, raw-orbit composers, or W32 erasers as the source task, read it as
historical support only unless this correction explicitly names it.

For the preferred finite-drawing route, the two live source leaves are:

```text
1. FiniteDrawingUnboundedComplementFrontierNoClosedSeparation

2. forall C inputs,
     forall a : {v // v in unboundedFrontierVertexSet C inputs},
       UnboundedFrontierCarrierNeighborPairAt inputs a
```

2026-05-21 graph-frontier non-singleton reducer:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ (unboundedFrontierVertexSet C inputs).card != 1
-> UnboundedExteriorFrontierComponentTopologySourceRows inputs
```

Checked declarations:

```lean
exists_two_frontier_points_or_no_unboundedFrontierVertexSet_of_card_ne_one

unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexSet_card_ne_one

unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_frontierVertexSet_card_ne_one

unboundedFrontierVertexSet_card_ne_one_of_frontierVertexIncidentSource

unboundedFrontierEdgeSet_empty_of_unboundedFrontierVertexSet_card_eq_one

no_frontier_edgeInterior_of_unboundedFrontierVertexSet_card_eq_one

unboundedExterior_frontier_eq_singleton_of_unboundedFrontierVertexSet_card_eq_one

unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontier_not_singleton

unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_frontier_not_singleton

inOpenSegment_mem_frontier_drawingComplement_of_edge_mem

inOpenSegment_mem_frontier_drawingComplement_of_adj

exists_drawingComplement_frontier_point_ne_graph_vertex

exists_drawingComplement_point_not_unboundedExterior_near_of_ambient_frontier_not_unboundedExterior_frontier

exists_ambient_frontier_nearby_complement_outside_unboundedExterior_of_frontier_singleton

exists_ambient_frontier_nearby_complement_outside_unboundedExterior_of_unboundedFrontierVertexSet_card_eq_one

three_le_vertices_of_finitePlanarOuterComponentInputs

cutVertexPartition_of_unique_unitDistance_neighbor

two_le_unitDistanceSimpleGraph_neighborSet_ncard_of_finitePlanarOuterComponentInputs

S2CarrierLocalSource.unboundedFrontierVertexSet_card_ne_one_of_actualCarrierDegreeTwo

S2CarrierLocalSource.frontierVertexIncidentSource_of_actualCarrierDegreeTwo

S2CarrierLocalSource.unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_actualCarrierDegreeTwo
```

This closes the no-graph-frontier and at-least-two-graph-frontier-vertices
branches under finite drawing no-closed-separation.  The remaining seed-side
local topology is precisely the singleton graph-frontier carrier case: prove
that this singleton case is impossible, or prove directly that the singleton
vertex has an actual incident selected `unboundedFrontierEdgeSet` edge.  The
new incident-source contradiction shows the latter immediately rules out the
singleton graph-frontier cardinality, so the real residual is the lower
accumulation/topology argument that produces the incident selected edge or a
direct singleton contradiction.  The singleton case also has an empty selected
`unboundedFrontierEdgeSet` and no open-edge frontier point, so the residual is
purely concentrated at the unique graph-frontier point; in fact the whole
actual unbounded exterior frontier is equal to that singleton.  Consequently,
finite drawing no-closed-separation plus the lower pure-topology statement
"the actual unbounded exterior frontier is not a single graph point" now
closes the component-topology source rows directly.  Separately, every graph
vertex now has a distinct nearby ambient drawing-complement frontier point
obtained as the midpoint of an incident canonical edge.  If the actual
unbounded exterior frontier is a singleton graph point, that distinct ambient
frontier point has arbitrarily nearby drawing-complement points outside the
selected unbounded exterior component.  The remaining step is to turn this
other-component boundary-bumping information into the needed singleton
contradiction or cut-partition source.

Actual carrier degree two also supplies selected incident-edge rows and rules
out the singleton graph-frontier carrier: degree two gives a concrete carrier
neighbour at every actual frontier vertex, and a singleton carrier would force
that neighbour to be the same vertex, contradicting looplessness.  Consequently
finite-drawing no-closed-separation plus the live `ActualCarrierDegreeTwoSource`
can already feed component-topology rows.  This does not source degree two; it
records that the degree-two proof closes the singleton branch automatically.

For the checked compressed support route, the corresponding stronger leaves
are:

```text
1. PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation

2. forall C inputs,
     UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

2026-05-21 update: the compressed topology leaf
`PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesOpenKCoverSeparation`
now has a checked reducer from the concrete Boolean side-map source:

```lean
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierOpenKCoverSeparation_of_continuousKSide
ExteriorComponentTopology
  .planarContinuumUnboundedComplementFrontierNontrivialOpenKCoverSeparation_of_nontrivialRelativeClopenKSide
```

So the non-circular topology work can target
`PlanarContinuumUnboundedComplementFrontierNontrivialClosedSeparationForcesContinuousKSide`
directly, or use the existing nontrivial relative-clopen side route directly,
provided neither route loops back through aligned splits or the open-cover
theorem it is meant to source.

The topology leaf stays separate.  The current named residual is the
Janiszewski/boundary-bumping obstruction

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
```

feeding the checked reducer

```text
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_janiszewskiNoSubcontinuumObstruction
```

to `FiniteDrawingUnboundedComplementFrontierNoClosedSeparation`.  Same-`K`,
relative-clopen, and bounded/subcontinuum branches are support routes only
unless a worker is explicitly proving this obstruction through them.  Do not
replace this leaf by final boundary-cycle assumptions.

### 2026-05-21c Dynamic Dispatch

The current active source work is split by proof obligation, not by a fixed
pool or wave:

```text
Topology:
  PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded
  -> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation

Local carrier:
  UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
  -> forall a, UnboundedFrontierCarrierNeighborPairAt inputs a

Boundary-free raw source:
  BoundaryFreeSelectedEdgeInputSourceRows inputs

Repeated-tail raw orbit:
  S2RepeatedTailExteriorCutWitnessSource for selected raw-orbit repeated tails

Orientation:
  find a selected exterior-sector source for SelectedRawOrbitOrientationRows
  without making all-outgoing-dart no-between the live source.
```

The `RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs` lane and the
short-spine composer lane are already claimed in `TASK.md`; do not duplicate
them unless those claims are cleared or marked stale.

Einstein's 2026-05-21c1 boundedness worker closed the boundedness/no-subcontinuum
equivalence:

```lean
S2_agent_janiszewski_boundedness_worker_20260521c1
planarJaniszewskiBoundaryBumpingSubcontinuumForcesBounded_iff_noSubcontinuumObstruction_20260521c1
```

The active topology residual below the boundedness surface is now:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
```

Darwin's 2026-05-21c6 worker reduced that no-subcontinuum obstruction to the
same-`K` point-between source:

```lean
planarJaniszewskiBoundaryBumpingNoSubcontinuumObstruction_of_kComponentPointsBetween_20260521c6
S2_agent_janiszewski_no_subcontinuum_worker_20260521c6
```

The active topology residual is now:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
```

This same-`K` point-between residual is already downstream of the checked
relative-clopen theorem:

```lean
planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_relativeClopenKSide
S2_agent_kcomponent_points_between_source_20260520f
S2_agent_topology_kcomponent_source_worker_20260520k
```

So the next topology worker should target
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide`
or a genuinely lower compact-Hausdorff separator source, not re-prove a
K-component/component-avoidance cycle.

Codex-current 2026-05-21 follow-up: the generic compact-subspace Boolean split
helper now checks after replacing the invalid `IsClosed.preimage hside ...`
projection with `isClosed_singleton.preimage hside` for both Boolean fibres.
This was an API repair only; it does not change the topology source leaf.

Local topology scan after the e2 spawn was rejected: the relative-clopen side,
component-avoidance, no-subcontinuum, and same-`K` point-between surfaces are
already an equivalence cluster via checked compact-Hausdorff reducers.  A
future topology worker should target a lower planar-continuum theorem such as:

```text
PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
```

or

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
```

Those are below the Janiszewski naming layer and avoid cycling among
relative-clopen/no-subcontinuum/component-avoidance/K-component aliases.

Banach's 2026-05-21c2 cut-partition worker added two checked local reducers:

```lean
S2_agent_cutpartition_input_worker_20260521c2_of_selectedIncidentEdgePairRows
S2_agent_cutpartition_input_worker_20260521c2_of_carrier_degree_two
```

The local cut-partition residual is therefore no harder than selected
incident-edge pair rows, and from bare `FinitePlanarOuterComponentInputs C` it
is exactly the concrete carrier degree-two theorem

```text
forall a, ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2
```

Carver's 2026-05-21d1 degree-two worker proved the reverse strict reduction:
carrier degree two is filled from the same sharp cut-partition source.

```lean
S2_agent_carrier_degree_two_source_worker_20260521d1_neighborPairRows
S2_agent_carrier_degree_two_source_worker_20260521d1_neighborFinset_card_two
S2_agent_carrier_degree_two_source_worker_family_20260521d1
```

So the local source is now pinned on one theorem surface, not another eraser:

```text
UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
```

It must be proved by constructing two actual selected `unboundedFrontierEdgeSet`
carrier edges at each exterior-frontier vertex and proving any third carrier
neighbour gives an honest cut partition.

Codex-current added a raw-orbit source reducer for this local source:

```lean
S2_codex_20260521e_rawOrbit_cutpartitionSource_of_connectedRawOrbitSourceRows_selectedRepeatedTailRows_rawOrientation
S2_codex_20260521e_rawOrbit_cutpartitionSource_family
S2_codex_20260521e_rawOrbit_cutpartitionSource_of_connectedRawOrbitSourceRows_selectedPrimitiveRows_rawOrientation
S2_codex_20260521e_rawOrbit_cutpartitionSource_family_of_connectedRawOrbitSourceRows_selectedPrimitiveRows_rawOrientation
S2_codex_20260521e_rawOrbit_cutpartitionSource_of_connectedRawOrbitSourceRows_selectedActualArcRows_rawOrientation
S2_codex_20260521e_rawOrbit_cutpartitionSource_family_of_connectedRawOrbitSourceRows_selectedActualArcRows_rawOrientation
S2_codex_20260521e_rawOrbit_neighborRows_of_connectedRawOrbitSourceRows_selectedPrimitiveRows_rawOrientation
S2_codex_20260521e_rawOrbit_neighborRows_family_of_connectedRawOrbitSourceRows_selectedPrimitiveRows_rawOrientation
```

Thus `UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs`
can now be sourced from:

```text
BoundaryFreeConnectedRawOrbitSourceRows inputs
+ SelectedRawOrbitRepeatedTailSeparationRows for the internally selected orbit
  or the smaller SelectedRawOrbitRepeatedTailPrimitiveSourceRows residual
  or selected actual repeated exterior-arc rows
+ SelectedRawOrbitOrientationRows for the same selected orbit
```

This is still source-level work: it does not use a final boundary cycle or an
induced frontier graph.  The remaining raw-orbit obligations are the actual
connected raw-orbit rows, primitive repeated-tail arc data, and the
non-overstrong selected orientation rows.  The primitive-row neighbor-row
family is the closest current local-source surface to the preferred W32 route.
Prefer that surface when assigning new repeated-tail work; the separation-row
surface remains a checked compatibility input.

Noether's 2026-05-21c4 repeated-tail worker reduced
`S2RepeatedTailExteriorCutWitnessSource` to selected raw-orbit repeated-tail
primitive/two-open-arc data, actual exterior-arc rows, or cut-partition rows:

```lean
S2_agent_repeated_tail_witness_worker_of_boundaryArcSource_20260521c4
S2_agent_repeated_tail_witness_worker_of_primitiveSourceRows_20260521c4
S2_agent_repeated_tail_witness_worker_of_actualExteriorArcRows_20260521c4
S2_agent_repeated_tail_witness_worker_of_cutPartitions_20260521c4
```

2026-05-21 k4 update: the repeated-tail source is also exposed directly at
the raw-orbit minimal finite-separation row:

```lean
S2_dynamic_repeated_tail_cut_k4_of_minimalDeletedTailSeparation
S2_dynamic_repeated_tail_separation_k4_of_minimalDeletedTailSeparation
S2_dynamic_repeated_tail_nonrepeat_k4_of_minimalDeletedTailSeparation
S2_dynamic_repeated_tail_injective_k4_of_minimalDeletedTailSeparation
```

The residual for a hypothetical repeated selected raw tail is now exactly one
raw-tail witness on each cyclic open side, both off the deleted tail, plus
nonreachability between those witnesses in the unit-distance graph induced
after deleting the repeated tail.  The no-cut field then gives nonrepeat and
tail injectivity.  No final boundary cycle rows, actual-boundary equivalence
rows, induced frontier graph, arbitrary cycle, all-adjacent endpoint row, or
identity angular order is used.

Dalton's orientation scout found that `SelectedRawOrbitOrientationRows` itself
is not the overstrong all-neighbour statement.  The live source should identify
the selected raw `faceSucc` branch as the exterior sector and then produce
orientation rows; generic no-between rows stay compatibility-only unless first
tied to that selected exterior sector.

Volta's 2026-05-21c3 boundary-free reducer exposed the residual
`BoundaryFreeIncidentGermEndpointSelectedFrontierEdgeRows inputs`.  Do not make
that row a live unconditional source: it still has the same chord obstruction
as the all-adjacent frontier-endpoint row.  It is valid only after additional
selected carrier/orbit data has already identified the incident edge as an
actual `unboundedFrontierEdgeSet` edge.  Otherwise, route through actual
carrier degree two or selected raw-orbit boundary-edge sources.

The local leaf should be attacked as the actual exterior-boundary carrier
degree-two theorem, not as all-outgoing-dart angular consecutivity:

```lean
theorem unboundedFrontierCarrierNeighborPairRows_of_inputs
    {n : Nat} (C : _root_.UDConfig n)
    (inputs :
      JordanTopologyFactsConcrete.MinimalFailureTopology
        .FinitePlanarOuterComponentInputs C) :
    forall a : {v : Fin n //
        v in ExteriorComponentTopology.unboundedFrontierVertexSet C inputs},
      ExteriorComponentTopology.UnboundedFrontierCarrierNeighborPairAt
        inputs a := by
  -- Prove from the actual unbounded-frontier carrier.
  -- A third exterior-boundary carrier neighbour at `a` should yield
  -- unreachable-after-delete / cut-partition rows, contradicting
  -- `inputs.noCutVertex`.
  ...
```

If using an intermediate source row, make it the missing local theorem itself,
for example:

```text
UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
```

with a proof that a third exterior-boundary carrier neighbour at a frontier
vertex forces a cut partition after deleting that vertex.  This is the local
finite plane-graph content behind "the exterior face boundary of a
2-connected plane graph is a cycle."

Do not add consumer-only work that merely transports actual rows, sector rows,
carrier rows, or selected successor-edge rows to
`UnboundedExteriorFrontierCycleRows`.  A missing row becomes the next producer
subtask and must be proved from `FinitePlanarOuterComponentInputs C`.

## Recent Checked Reductions

2026-05-20 q-dispatch returned source tightening:

Topology:

```lean
S2_agent_crossing_point_between_worker_20260520q1
```

The crossing-subcontinuum point-between source is reduced to the U-indexed
Janiszewski/boundary-bumping subcontinuum point source:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
```

This remains the live non-circular topology leaf.  Do not route it through
`KComponentPointsBetween`, component avoidance, finite-cycle rows, or
boundary-cycle rows.

Local deletion:

```lean
S2_agent_deleted_neighbor_local_separation_worker_20260520q2_rows_of_unreachableAfterDeleteRows
S2_agent_deleted_neighbor_local_separation_worker_20260520q2_of_unreachableAfterDelete
S2_agent_deleted_neighbor_local_separation_family_worker_20260520q2_of_unreachableAfterDelete
```

The explicit deleted-neighbour local-separation source is reduced to:

```lean
UnboundedFrontierCarrierNeighborPairUnreachableAfterDeleteInputSource C inputs
```

Local raw orbit:

```lean
S2_agent_connected_raw_orbit_source_worker_20260520q3
S2_agent_selected_repeated_tail_boundary_arc_worker_20260520q4
S2_agent_selected_raw_orientation_worker_20260520q5
```

Current local raw-orbit leaves:

```text
BoundaryFreeInputSourceReduction inputs
UnboundedExteriorFrontierComponentTopologySourceRows inputs
RawOrbitIteratedFaceSuccInteriorFrontierPointNoOrbitSource inputs
RawFaceSuccOrbitRepeatedTailExteriorCutRows for repeated tails of the selected raw orbit
```

The q5 orientation route reduces to
`SelectedRawOrbitAngularNoBetweenRows selectedRows`.  Treat that as
compatibility support only unless it is proved as a selected exterior-sector
orientation theorem that does not exclude legal interior chords.

2026-05-20 p-dispatch returned source tightening:

Local exact incident package:

```lean
S2_agent_actual_boundary_incident_source_of_rawOrbit_localSectorRows_20260520p1
S2_agent_actual_boundary_incident_source_worker_20260520p2
S2_agent_raw_orbit_actualRows_source_worker_20260520p3
```

The local exact package

```lean
Exists fun actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
  BoundaryCycleIncidentFrontierEdgeCompleteness inputs actualRows.boundary
```

is now reduced to:

```text
BoundaryFreeConnectedRawOrbitSourceRows inputs
+ selected raw-orbit repeated-tail boundary-arc rows
+ selected raw-orbit orientation rows
```

The direct p1 eraser constructs `actualRows` with
`S2_dyn_20260520_actual_boundary_rows_source` and pairs it with
`S2_agent_local_sector_incident_bridge`, so incident completeness is tied to
the same concrete boundary.  No selected-head outgoing-list no-between,
all-adjacent endpoint closure, induced frontier graph, arbitrary carrier
cycle, or final `UnboundedExteriorFrontierCycleRows` is used.

Local no-cut source:

```lean
S2_agent_third_neighbor_cut_source_worker_20260520p4_at
S2_agent_third_neighbor_cut_source_worker_20260520p4_neighborRows_of_cutPartitionRows
S2_agent_third_neighbor_unreachable_source_worker_20260520p4_at
S2_agent_third_neighbor_unreachable_source_worker_20260520p4_neighborRows
S2_agent_third_neighbor_cut_source_worker_20260520p4_neighborRows_of_localSeparation
```

The remaining no-cut/local leaf is:

```lean
UnboundedFrontierCarrierDeletedNeighborLocalSeparationInputSource C inputs
```

equivalently the unreachable-after-delete source: for each actual exterior
carrier vertex, choose two real selected frontier-edge heads and prove any
third carrier neighbour is unreachable from the chosen side in the unit-distance
graph after deleting the vertex.

Topology source:

```lean
S2_agent_no_subcontinuum_obstruction_worker_20260520p6
```

is a checked compatibility reducer from relative-clopen K-side to
no-subcontinuum obstruction.  The live non-circular topology source is instead:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
```

with checked downstream route:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
-> planarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum_of_pointsBetween
-> planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_frontierSubcontinuum
-> planarContinuumUnboundedComplementFrontierNoSubcontinuumObstruction_of_crossingSubcontinuumForcesBounded
```

Do not source this through `KComponentPointsBetween`, component avoidance,
finite cycle rows, boundary-cycle rows, or boundedness already derived from the
K-component route.

2026-05-20 o-dispatch returned source tightening:

Local source tightening:

```lean
boundaryVertexFrontierIncidentSectorSource_of_actualBoundaryRows_incidentComplete
S2_agent_boundary_incident_sector_source_worker_20260520o2_of_actualBoundaryRows_incidentComplete
S2_agent_boundary_incident_sector_source_worker_20260520o2
```

The live local leaf is now:

```lean
Exists fun actualRows : ActualBoundaryCycleFrontierEquivalenceRows C inputs =>
  BoundaryCycleIncidentFrontierEdgeCompleteness inputs actualRows.boundary
```

This packages the boundary as `actualRows.boundary` and uses
`boundaryVertexFrontierIncidentSectorRows_of_actualBoundaryRows_incidentComplete`
to source the incident-sector rows.  It does not use selected-head outgoing-list
no-between rows, all-adjacent endpoint rows, induced frontier graphs, or an
arbitrary carrier cycle.

Topology source tightening:

```lean
S2_agent_relative_clopen_k_side_worker_20260520o4
```

The live topology leaf is now:

```lean
PlanarContinuumUnboundedComplementFrontierClosedSeparationNoSubcontinuumObstruction
```

The checked route is:

```text
NoSubcontinuumObstruction
-> planarContinuumUnboundedComplementFrontierNontrivialRelativeClopenKSide_of_noSubcontinuumObstruction
-> janiszewskiBoundaryBumping_of_nontrivialRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_relativeClopenKSide
-> finite no-closed-separation reducers
```

Do not prove the topology leaf by passing through
`KComponentPointsBetween`, component avoidance, crossing-boundedness derived
from it, or boundary-cycle rows; those are downstream of this source.

2026-05-21 n-route selected source reducers:

Checked declarations:

```lean
S2_agent_selected_incident_edge_pair_source_scout_20260520n5
S2_agent_selected_incident_edge_pair_source_family_scout_20260520n5
S2_agent_local_selected_pair_to_neighborRows_worker_20260520n3
S2_agent_local_selected_pair_to_neighborRows_family_worker_20260520n3
finiteDrawingUnboundedComplementFrontierNoClosedSeparation_of_kComponentPointsBetween_via_nonCircularTopologyReducers
S2_agent_kcomponent_to_finite_no_closed_worker_20260520n4
```

Current live source leaves after these reducers:

```text
Local source:
  Exists B,
    frontier_iff_cycle_vertex B
    /\ forall k, BoundaryVertexFrontierIncidentSectorRowsAt inputs B k

Topology source:
  PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
```

The local source flows through incident-sector rows to
`LocalSelectedIncidentEdgePairSourceRows`, then through the deleted-neighbor
route to pointwise `UnboundedFrontierCarrierNeighborPairAt`.  The topology
source flows through points-between and crossing-bounded reducers to finite
no-closed-separation.  Neither route uses selected-head outgoing-list
no-between, all-adjacent endpoint closure, induced frontier graphs, or a final
boundary-cycle assumption.

2026-05-21 raw-orbit source-family closure m2:

Claim `S2-agent-raw-orbit-source-family-closure-worker-20260520m2` is checked
in `S2SeededRawOrbitSource.lean`.

New declarations:

```lean
S2_agent_raw_orbit_source_family_of_connectedRawOrbitSourceRows_selectedBoundaryArcRows_rawOrientation_20260520m2
S2_agent_raw_orbit_source_family_closure_worker_20260520m2
```

Route impact:

```text
BoundaryFreeConnectedRawOrbitSourceRows
+ SelectedRawOrbitRepeatedTailBoundaryArcRows for the selected raw orbit
+ SelectedRawOrbitOrientationRows for the selected raw orbit
-> exact PSigma source family consumed by
   S2_agent_raw_orbit_actual_boundary_source_worker_20260520k

BoundaryFreeNoThirdGermSource
+ UnboundedExteriorFrontierComponentTopologySourceRows
+ RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource
-> BoundaryFreeConnectedRawOrbitSourceRows
-> same exact PSigma source family
```

The produced package contains pointwise local-sector rows, connectedness of
`unboundedFrontierCarrierGraph C inputs`, the selected geometric raw
face-successor orbit, dart-edge open-segment frontier rows, repeated-tail
separation rows erased from finite boundary-arc rows, and raw
predecessor/successor orientation.  It introduces no final exterior cycle,
induced frontier graph, identity angular order, synthetic enclosure, arbitrary
cycle, or W-numbered facade.

Remaining leaves after this closure are exactly the component/local selected
source leaves:

```text
forall C inputs, BoundaryFreeNoThirdGermSource inputs
forall C inputs, UnboundedExteriorFrontierComponentTopologySourceRows inputs
forall C inputs, RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs
forall C inputs, SelectedRawOrbitRepeatedTailBoundaryArcRows selectedRows
forall C inputs, SelectedRawOrbitOrientationRows selectedRows
```

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-21 crossing bounded proof worker m1:

Claim `S2-agent-crossing-bounded-proof-worker-20260520m1` is checked in
`ExteriorComponentTopology.lean`.

New declarations:

```lean
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_pointsBetween
S2_agent_crossing_bounded_proof_worker_20260520m1
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

This is the non-Janiszewski route for the crossing-boundedness leaf.  It does
not pass through
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide`,
`PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween`,
component-avoidance, or final boundary-cycle rows.  The first remaining leaf is
exactly
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumPointsBetween`.

2026-05-21 l-dispatch returned leaves:

Checked selected-edge/local reducers:

```lean
boundary_frontier_closedSegment_selectedEdgeSource_of_endpoint_incident_and_relative_closure
S2_agent_boundary_free_no_third_selected_edge_worker_20260520l4
S2_agent_boundary_free_no_third_selected_edge_worker_nonempty_20260520l4
S2_agent_boundary_free_no_third_selected_edge_worker_family_20260520l4
actualBoundaryFaceSuccLocalSectorRows_of_connectedRawOrbitSourceRows_selectedBoundaryArcRows_rawOrientation_20260520
actualBoundaryFaceSuccLocalSectorRows_family_of_connectedRawOrbitSourceRows_selectedBoundaryArcRows_rawOrientation_20260520
```

Route impact:

```text
endpoint-selected edge membership
+ boundary open-segment relative closure
-> BoundaryFrontierClosedSegmentSelectedEdgeSource

BoundaryFrontierClosedSegmentSelectedEdgeSource
+ bad selected incident-edge repeated exterior-boundary arc rows
-> BoundaryFreeNoThirdGermSource

SelectedRawOrbitRepeatedTailBoundaryArcRows
-> selected repeated-tail actual exterior arcs
-> actual boundary/local-sector raw-orbit route
```

The remaining selected raw repeated-tail leaf is
`SelectedRawOrbitRepeatedTailBoundaryArcRows` for the selected raw orbit.  The
remaining boundary-free no-third leaf is a bad selected incident-edge arc row
family producing `RepeatedExteriorBoundaryArcSeparationRows` for selected
incident edges that are neither the boundary predecessor nor successor.

Read-only scouts also fixed the first non-circular leaves:

```lean
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
forall a : {v : Fin n // v in unboundedFrontierVertexSet C inputs},
  UnboundedFrontierCarrierLocalSectorRowsAt inputs a
```

The first topology leaf feeds
`planarJaniszewskiBoundaryBumpingRelativeClopenKSide_of_crossingSubcontinuumForcesBounded`.
Do not use circular reducers that derive it from K-component or relative-clopen
K-side data.  The local-sector family is also the first source leaf for
`BoundaryCycleIncidentFrontierEdgeCompleteness` through
`S2_agent_local_sector_incident_bridge`.

2026-05-21 raw-orbit actual-boundary geometric-order source reduction:

Claim `S2-agent-raw-orbit-actual-boundary-source-worker-20260520k` is checked
in `S2ExteriorBoundarySource.lean`.

New declarations:

```lean
S2_agent_raw_orbit_actual_boundary_source_worker_20260520k
```

Route impact:

```text
forall C inputs,
  local-sector rows for the unbounded-frontier carrier
  + connectedness of unboundedFrontierCarrierGraph
  + a geometric RawFaceSuccOrbit with dart-edge frontier rows
  + repeated-tail exterior boundary separation rows
  + raw predecessor-before-successor orientation
-> Exists actualRows,
     BoundaryVertexGeometricRotationOrderRow rows for actualRows.boundary
     /\ BoundaryCycleIncidentFrontierEdgeCompleteness inputs actualRows.boundary
```

This is a family-level wrapper around the existing checked pointwise
constructor
`S2_codex_current_20260520_actualBoundary_geometricOrder_incident_source_of_rawOrbit_localSectorRows`.
It keeps the same raw face-successor/local-sector route: repeated-tail
separation makes the raw boundary simple, the raw orientation is transported
to genuine geometric boundary-order rows, and incident completeness is supplied
by the same local-sector bridge.  It does not assume final
`UnboundedExteriorFrontierCycleRows`, use an induced frontier graph, arbitrary
carrier cycle, identity angular order, endpoint-chord shortcut, or synthetic
enclosure.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean
```

2026-05-21 topology K-component source worker k:

Claim `S2-agent-topology-kcomponent-source-worker-20260520k` is implemented in
`ExteriorComponentTopology.lean`.

New declaration:

```lean
S2_agent_topology_kcomponent_source_worker_20260520k
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
```

The first arrow is the direct compact-frontier component proof
`planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_relativeClopenKSide`:
take the connected component of one frontier point inside the compact
frontier, and if the other point is outside it, use compact-Hausdorff clopen
separation of the frontier plus the relative-clopen `K`-side to contradict
same-component membership in `K`.  This reduction does not use the cyclic
component-avoidance route, no-subcontinuum cycle, arbitrary trace connectivity,
or final boundary-cycle rows.

Focused gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-21 topology subcontinuum-points worker a1:

Claim `S2-agent-topology-subcontinuum-points-worker-20260521a1` is checked in
`ExteriorComponentTopology.lean`.

New declarations:

```lean
planarJaniszewskiBoundaryBumpingSubcontinuumPointsBetween_of_subcontinuumForcesBounded
S2_agent_topology_subcontinuum_points_worker_20260521a1
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumForcesBounded
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierNoSubcontinuumObstruction
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
```

The remaining Janiszewski point-between leaf is now the same-lane
boundedness/crosscut theorem: a closed split of `frontier U` crossed by the
displayed compact connected `T` must force `U` bounded.  This reducer does not
use same-`K` component point rows, component avoidance, boundary-cycle rows,
synthetic enclosure assumptions, or a facade.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-21 selected repeated-tail actual exterior-arc wrapper:

Claim `S2-agent-selected-repeated-actual-arc-wrapper-20260520k` is checked in
`S2SeededRawOrbitSource.lean`.

New declaration:

```lean
selectedRawOrbitRepeatedTailActualExteriorArcRows_of_boundaryArcRows_20260520
```

Route impact:

```text
SelectedRawOrbitRepeatedTailBoundaryArcRows rows
-> SelectedRawOrbitRepeatedTailActualExteriorArcRows rows
```

The wrapper is the selected-row-facing form of the existing pair-level eraser
`RawFaceSuccOrbitRepeatedTailActualExteriorArcRows.ofRepeatedExteriorBoundaryArcSeparationRows`.
It keeps the residual on the same selected raw orbit and introduces no new
facade, carrier cycle, final boundary cycle, or no-cut shortcut.

2026-05-22 q9 selected raw-orbit boundary-arc reduction:

Claim `S2-agent-q9-raw-orbit-boundary-arc` is checked in
`S2SeededRawOrbitSource.lean`.

New declaration:

```lean
S2_agent_q9_cyclicSuccDeletedTailNonreachabilitySource_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_boundaryArcRows
```

Route impact:

```text
SelectedRawOrbitRepeatedTailBoundaryArcRows for the r17 selected raw orbit
-> SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
-> SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
```

This is the nonreachability-shaped repeated-tail leaf used by q9-style
actual-sector spines.  The proof stays on the selected r17 raw orbit and
composes the checked q8 boundary-arc-to-cut-partition reducer with the finite
graph cut-partition-to-nonreachability eraser; it does not introduce a final
boundary cycle, induced frontier graph, arbitrary carrier cycle, endpoint
shortcut, or synthetic enclosure.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=120 ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-22 q10 r17 boundary-arc source reduction:

Claim `S2-agent-q10-boundary-arc-source` is checked in
`S2SeededRawOrbitSource.lean`.

New declarations:

```lean
S2_agent_q10_boundaryArcRows_family_of_componentInput_geometricSelection_incidentGerm_selectedCarrierRows_primitiveSourceRows
S2_agent_q10_boundaryArcRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_primitiveSourceRows
S2_agent_q10_cyclicSuccDeletedTailNonreachabilitySource_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_primitiveSourceRows
```

Route impact:

```text
primitive repeated-tail raw-index rows for the selected component/r17 raw orbit
-> SelectedRawOrbitRepeatedTailBoundaryArcRows for that same selected raw orbit
-> q9 SelectedRawOrbitCyclicSuccDeletedTailNonreachabilitySource
```

This is a strict reduction of the r17 boundary-arc leaf.  It keeps the
repeated-tail work on the selected raw `faceSucc` orbit produced from
finite no-open/component topology and selected carrier propagation, then uses
the existing primitive-to-boundary-arc eraser and q9 nonreachability eraser.
It does not introduce an actual-sector row, W32 route, final boundary cycle,
induced frontier graph, arbitrary cycle, or endpoint shortcut.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-22 q10 selected-carrier propagation:

Claim `S2-agent-q10-selected-carrier-propagation` is checked in
`S2SeededRawOrbitSource.lean`.

New declaration:

```lean
S2_agent_q10_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_endpointLocalRadius_selectedCarrierRows_boundaryArcRows
```

Route impact:

```text
finite no-open + frontier-vertex incident
+ geometric selected carrier rows
+ local endpoint-radius selected incident-germ covers
+ selected carrier successor rows
+ boundary-arc rows on the endpoint-local-radius r17 selected raw orbit
-> actual exterior-sector source family
```

This lowers the q8 selected-carrier actual-sector spine from the older global
`SelectedNeighborIncidentGermFrontierEdgeMembershipRows` leaf to the local
endpoint-radius row for the same selected carrier heads.  The primitive
repeated-tail boundary-arc reducers were also eta-expanded at the repeated-tail
indices so they remain pinned to the exact selected raw orbit under dependent
`let` binders.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-22 q12 endpoint-local-radius selected-edge lowering:

Claim `S2-agent-q12-endpoint-local-radius` is checked in
`S2SeededRawOrbitSource.lean`.

New declaration:

```lean
S2_agent_q12_SelectedNeighborEndpointLocalRadiusCoversRows_of_selectedHeadAt_endpointRadiusContains
S2_agent_q12_SelectedNeighborEndpointLocalRadiusCoversRows_family_of_selectedHeadAt_endpointRadiusContains
```

Route impact:

```text
geometric selected carrier neighbours
+ same-selected-pair IncidentGermEndpointSelectedHeadAt
+ same-selected-pair IncidentGermSelectedEndpointLocalRadiusContainsAt
-> S2_r17_SelectedNeighborEndpointLocalRadiusCoversRows
```

The selected endpoint frontier-edge premise is discharged internally from the
`LocalSelectedIncidentEdgePairSourceRows` projected out of the same geometric
selection, using only its selected `left_edge` and `right_edge`
`unboundedFrontierEdgeSet` incidences.  The theorem does not use an
all-adjacent endpoint row, final unbounded exterior frontier cycle rows,
actual exterior-sector rows, W32 target, induced frontier graph, convex hull,
identity angular rows, or synthetic enclosure.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-22 q11 r30 local-separation lowering:

Claim `S2-agent-q11-r30-local-separation` is checked in
`S2CarrierLocalSource.lean`.

New declarations:

```lean
S2_agent_q11_r30_finitePlaneLocalSeparationPrimitive_of_selectedEdgeLocalIsolation
S2_agent_q11_r30_finitePlaneLocalSeparationPrimitive_family_of_selectedEdgeLocalIsolation
S2_agent_q11_r30_finitePlaneLocalSeparationPrimitive_of_boundaryFreeLocalNoThirdGermSourceRows
S2_agent_q11_r30_finitePlaneLocalSeparationPrimitive_family_of_boundaryFreeLocalNoThirdGermSourceRows
```

Route impact:

```text
SelectedUnboundedFrontierEdgeLocalIsolationSourceRows
  = BoundaryFreeLocalNoThirdGermSourceRows
-> local-sector rows on the actual unbounded-frontier carrier
-> S2_r30_deleted_neighbor_finitePlaneLocalSeparationPrimitive
```

This is the local r30 source in the smallest currently checked selected-edge
form: two actual selected `unboundedFrontierEdgeSet` heads at each frontier
carrier vertex plus the local no-third exterior-frontier germ row.  It avoids
the stronger global outgoing-list no-between route, all-adjacent endpoint
claims, induced frontier graphs, arbitrary cycles, and W32/final-boundary
facades.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2CarrierLocalSource.lean
```

2026-05-22 q11 r36 selected-geometry lowering:

Claim `S2-agent-q11-r36-selected-geometry` is checked in
`S2CarrierLocalSource.lean`, with the generic owner-surface mirror in
`S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
S2_r36_selectedAngularNoBetweenRows_of_finitePlaneLocalSeparationPrimitive
S2_r36_selectedGeometricOrderRows_of_finitePlaneLocalSeparationPrimitive_angularNoBetweenRows
S2_r36_selectedGeometricOrderRows_family_of_finitePlaneLocalSeparationPrimitive_angularNoBetweenRows
```

Route impact:

```text
selected r30/r5r carrier heads
+ pointwise GraphVertexAngularNoBetweenRows at exactly those heads
-> Nonempty GraphVertexGeometricAngularNeighborSelectionRow for those heads
-> S2_r36_selectedGeometricOrderRows_of_finitePlaneLocalSeparationPrimitive
```

The selected geometry leaf is now the local angular no-between row for the
actual selected exterior carrier heads.  The proof gets unit-adjacency from
the stored selected `unboundedFrontierEdgeSet` incidences and uses the
geometric rotation-system adjacent-list extraction theorem.  It does not use
an all-adjacent endpoint claim, induced frontier graph, final boundary cycle,
identity angular order, or global all-outgoing no-between shortcut.

Focused owner-file gates passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2LocalTwoGermAssembly.lean
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=120 ErdosProblems1066/Swanepoel/S2CarrierLocalSource.lean
```

2026-05-21 actual-boundary package i2 reduction:

Claim `S2-agent-actual-boundary-package-source-20260520i2` is checked in
`S2ExteriorBoundarySource.lean`.

New declarations:

```lean
S2_agent_actual_boundary_package_source_20260520i2_of_actualBoundary_geometricOrder_incident
S2_agent_actual_boundary_package_source_20260520i2_of_rawOrbit_localSectorRows
S2_agent_actual_boundary_package_source_20260520i2
```

Route impact:

```text
Exists actualRows,
  geometric BoundaryVertexGeometricRotationOrderRow rows for actualRows.boundary
  /\ BoundaryCycleIncidentFrontierEdgeCompleteness inputs actualRows.boundary
-> Exists actualRows,
     BoundaryVertexAngularNoBetweenRows rows for actualRows.boundary
     /\ BoundaryCycleIncidentFrontierEdgeCompleteness inputs actualRows.boundary
```

The pointwise raw route composes this adapter with
`S2_codex_current_20260520_actualBoundary_geometricOrder_incident_source_of_rawOrbit_localSectorRows`,
so the package is strictly reduced through the existing raw face-successor
construction: local sector rows, connectedness of the actual
unbounded-frontier carrier, the selected geometric raw orbit, dart-edge
frontier propagation, repeated-tail separation, and raw predecessor/successor
orientation.  It does not assume `UnboundedExteriorFrontierCycleRows`, use an
induced frontier graph, arbitrary cycle, identity angular order,
endpoint-chord shortcut, or synthetic enclosure.

Focused owner-file gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean
```

2026-05-21 Janiszewski K-component point source verification:

Claim `S2-agent-janiszewski-kcomponent-source-20260520i` verified the checked
source reduction in `ExteriorComponentTopology.lean`.

Relevant declarations:

```lean
planarJaniszewskiBoundaryBumpingKComponentPointsBetween_of_relativeClopenKSide
S2_agent_kcomponent_points_between_source_20260520f
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
```

The proof is not a facade: it takes the connected component of a frontier point
inside the compact frontier as the witness.  If the second frontier point is
outside that component, compact-Hausdorff clopen separation of the frontier
produces a nontrivial closed split; the Janiszewski relative-clopen `K`-side
then gives a relatively clopen split of `K`, contradicting that the two points
are in the same `connectedComponentIn K`.  No arbitrary trace connectivity,
synthetic enclosure predicate, induced frontier graph, or boundary-cycle row is
used.

Focused gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-21 historical h-route W32 support composer:

Claim `S2-agent-current-shortest-route-composer-20260520h` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_componentAvoidance_actualCarrierDegreeTwo_geometricAngularNeighborSelectionRows_20260520h
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ actual carrier degree two for unboundedFrontierCarrierGraph
+ selected-head GraphVertexGeometricAngularNeighborSelectionRow rows after
   the actual-carrier degree-two selected-head construction
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is the shortest checked W32 composer after the current g4 local/geometric
reducers: it enters the existing finite no-closed-separation plus compact
geometric-neighbour W32 consumer directly.  The topology branch uses the
checked direct component-avoidance finite no-closed-separation reducer; the
local branch uses the checked g4 actual-carrier geometric-neighbour family
reducer.  No facade layer, W-label wrapper, raw-orbit shortcut, induced
frontier graph, arbitrary cycle, synthetic enclosure row, axiom, sorry, admit,
unsafe, opaque, or debug command was introduced.

The former support leaves are:

```lean
ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierComponentAvoidance
forall {m : Nat} (C : UDConfig m)
  (inputs : FinitePlanarOuterComponentInputs C),
  letI : DecidableRel (unboundedFrontierCarrierGraph C inputs).Adj :=
    unboundedFrontierCarrierGraph_decidableAdj C inputs
  forall a : {v : Fin m //
      Set.Mem (unboundedFrontierVertexSet C inputs) v},
    ((unboundedFrontierCarrierGraph C inputs).neighborFinset a).card = 2
forall {m : Nat} (C : UDConfig m)
  (inputs : FinitePlanarOuterComponentInputs C),
  let selectedEdgeRows :=
    S2_codex_current_20260520_actual_carrier_degree_two_source
      (hdegree C inputs)
  let cutSource :=
    S2_agent_20260520_neighbor_pair_cutpartition_source_of_selectedIncidentEdgePairRows
      (C := C) (inputs := inputs) selectedEdgeRows
  let selectedRows :=
    S2_worker_20260520_selected_cutpartition_source_of_localTwoGermRows
      (C := C) (inputs := inputs)
      (S2_worker_20260520_local_two_germ_source_of_neighborPairCutPartitionInputSource
        (C := C) (inputs := inputs) cutSource)
  forall a : {v : Fin m //
      Set.Mem (unboundedFrontierVertexSet C inputs) v},
    Nonempty
      (GeometricRotationSystem.GraphVertexGeometricAngularNeighborSelectionRow
        C a.1 (selectedRows.selectedNeighborRows a).left
          (selectedRows.selectedNeighborRows a).right)
forall {n : Nat} (C : UDConfig n),
  MinimalGraphFacts.IsMinimalClearedFailure C -> CutVertexInterface.NoCutVertex C
```

Focused W32 gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-21 historical f-route support W32 composer:

Claim `S2-agent-current-source-gap-composer-20260520f` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_crossingBounded_boundaryVertexExteriorSectorRows_selectedHeadNoBetween_20260520f
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierClosedSeparationRelativeClopenKSide
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ boundary-sector source:
   Exists B, frontier iff B.vertex /\ forall k, BoundaryVertexExteriorSectorRowsAt inputs B k
+ selected-head GraphVertexGeometricOutgoingListNoBetweenRows after
   S2_agent_selected_incident_close_route_20260520f_of_boundaryVertexExteriorSectorRows
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is the former checked W32 support handoff after the e/f reducers currently in
scope.  It uses the compact finite no-closed-separation/geometric-neighbour
route, the checked 20260520f boundary-sector -> selected-incident reducer, and
the existing selected-head outgoing-list no-between eraser.  The checked
`S2_agent_kcomponent_points_between_source_20260520f` remains useful for the
point-between topology lane, but it is not on this shortest chain because the
same crossing-bounded/relative-clopen topology source feeds finite
no-closed-separation directly.  No facade layer, W-label, raw-orbit shortcut,
induced frontier graph, arbitrary cycle, synthetic enclosure row, axiom,
sorry, or debug command was introduced.

The former support leaves are:

```lean
ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded
forall C inputs,
  Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
    (forall v,
      Set.Mem
        (frontier (unboundedExteriorComponentRows C inputs).exterior)
        ((canonicalGraph C).point v) <->
      Exists fun k : Fin B.length => B.vertex k = v) /\
    forall k : Fin B.length,
      ExteriorComponentTopology.BoundaryVertexExteriorSectorRowsAt inputs B k
forall C inputs,
  GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
    for the selected heads produced from
    S2_agent_selected_incident_close_route_20260520f_of_boundaryVertexExteriorSectorRows
forall {n : Nat} (C : UDConfig n),
  MinimalGraphFacts.IsMinimalClearedFailure C -> CutVertexInterface.NoCutVertex C
```

Focused W32 gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-21 historical Nash geometric-neighbour handoff:

Claim `S2-agent-current-shortest-chain-20260520g2` returned the current
shortest non-circular S2 route:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs, UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
-> UnboundedExteriorFrontierCycleRows
-> W32
```

This supersedes the active g2/g3 route-mapping claims for Nash, Anscombe, and
Ampere.  The connected raw-orbit, repeated-tail, actual-boundary, and
crossing-subcontinuum lanes remain checked fallbacks only.

2026-05-21 no-cut handoff route:

Claim `S2-agent-no-cut-handoff-route-20260520g` is completed with no Lean
source edit.  The shortest existing exact supplier of the no-cut family is:

```lean
CutVertexSlackFromDeletion.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced
```

It checks at the exact W32 row shape:

```lean
forall {n : Nat} (C : UDConfig n),
  MinimalGraphFacts.IsMinimalClearedFailure C ->
    CutVertexInterface.NoCutVertex C
```

The later no-cut names
`NoCutBlockerEliminationW24.noCutVertexFamily_of_refuting_bothPlusSidesCutForced`,
`NoCutPointwiseBridgeW32.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced`,
and
`NoCutMinimalityClosureW34.noCutVertexFamily_of_refuting_bothPlusSidesCutForced`
also check at this shape, but are wrappers/re-exports for this handoff.

Checked W32 handoff:

```lean
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_geometricNeighborSelectionRows_20260520
  frontier_noClosedSeparation
  geometricRows
  CutVertexSlackFromDeletion.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced
```

No W32 wrapper was added: the current finite no-closed-separation plus compact
geometric-neighbour consumer already accepts the no-cut theorem directly.  The
exact remaining leaves for this shortest W32 route are therefore:

```lean
ExteriorComponentTopology.FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
forall C inputs,
  S2LocalTwoGermAssembly.UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows inputs
CutVertexSlackFromDeletion.minimalFailureNoCutVertexFamily_of_refuting_bothPlusSidesCutForced
```

2026-05-21 historical e-route support W32 composer:

Claim `S2-agent-current-e-composer-20260520e` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_closedSeparationContinuum_actualBoundaryRows_geometricBoundaryRows_incidentComplete_selectedHeadNoBetween_20260520e
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
-> finite drawing no-closed-separation
+ actual boundary-cycle/frontier rows
+ GeometricBoundarySuccessorRows for that boundary
+ BoundaryVertexGeometricRotationOrderRow for that boundary
+ BoundaryCycleIncidentFrontierEdgeCompleteness for that boundary
+ selected-head GraphVertexGeometricOutgoingListNoBetweenRows after the
   checked actual-sector -> selected-incident-edge reducer
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is the former checked W32 support handoff currently in the file: it uses the
finite no-closed-separation / compact geometric-neighbour route rather than
the longer connected raw-orbit d-lane.  The actual-sector and selected-edge
steps are real checked reducers from the S2 owner files; no W-facing facade,
raw-orbit shortcut, induced frontier graph, arbitrary cycle, synthetic
enclosure row, axiom, sorry, or debug command was introduced.  The exact
remaining leaves are:

```lean
ExteriorComponentTopology.PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
forall C inputs,
  ExteriorComponentTopology.ActualBoundaryCycleFrontierEquivalenceRows C inputs
forall C inputs,
  GeometricRotationSystem.GeometricBoundarySuccessorRows C
    (actualRows C inputs).boundary
forall C inputs,
  forall k : Fin (actualRows C inputs).boundary.length,
    GeometricRotationSystem.BoundaryVertexGeometricRotationOrderRow C
      (actualRows C inputs).boundary k
forall C inputs,
  ExteriorComponentTopology.BoundaryCycleIncidentFrontierEdgeCompleteness inputs
    (actualRows C inputs).boundary
forall C inputs,
  GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows
    for the selected heads produced from the checked actual-sector source
forall {n : Nat} (C : UDConfig n),
  MinimalGraphFacts.IsMinimalClearedFailure C -> CutVertexInterface.NoCutVertex C
```

Focused W32 gate passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-21 same-boundary actual exterior-sector source:

Claim `S2-codex-main-20260520-actual-sector-source` is checked in
`S2ExteriorBoundarySource.lean`.

New declarations:

```lean
S2_codex_main_20260520_actual_sector_source_of_boundaryVertexExteriorSectorRows
S2_codex_main_20260520_actual_sector_source_of_actualBoundaryRows_faceSuccIncidentComplete
```

Route impact:

```text
Exists B,
  frontier_iff_cycle_vertex B
  /\ (forall k, BoundaryVertexExteriorSectorRowsAt inputs B k)
-> Exists B,
     frontier_iff_cycle_vertex B
     /\ Nonempty (ActualExteriorSectorInputSourceRows inputs B)
```

The second declaration composes the existing S2 boundary-sector constructor
from actual boundary rows, genuine geometric face-successor/orientation rows,
and same-boundary incident frontier-edge completeness with the
`ExteriorComponentTopology` eraser.  The exact residual is now the primitive
same-boundary boundary-sector row family, or equivalently actual boundary-cycle
frontier-equivalence plus face-successor/orientation and incident-completeness
rows for that same boundary.  No induced frontier graph, arbitrary cycle,
synthetic enclosure predicate, W-facing facade, axiom, sorry, or debug command
was introduced.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource
```

2026-05-21 selected raw-tail coverage/repeated-tail reduction:

Claim `S2-codex-main-20260520-raw-tail-coverage-repeat-source` is checked in
`S2SeededRawOrbitSource.lean`.

New declarations:

```lean
unboundedExteriorFrontierCycleRows_of_boundaryFreeInput_preconnected_selectedNeighborGeometricOrder_successorTailRows_selectedCutPartitions_20260520
finitePlanarStraightLineOuterComponentTheorem_of_boundaryFreeInput_preconnected_selectedNeighborGeometricOrder_successorTailRows_selectedCutPartitions_20260520
```

Route impact:

```text
BoundaryFreeInputSourceReduction inputs
+ PlanarContinuumUnboundedComplementFrontierPreconnected
+ selectedNeighborGeometricOrder successor-tail rows
+ selected cut partitions for the internally built raw orbit
-> UnboundedExteriorFrontierCycleRows C inputs
-> FinitePlanarStraightLineOuterComponentTheorem
```

This strictly reduces the two residuals exposed by
`finitePlanarStraightLineOuterComponentTheorem_of_selectedNeighborGeometricOrder_rawFaceSuccOrbit_tailCoverage_20260520`:
`frontier_vertex_tail_coverage` is now closed through the checked
`BoundaryFreeConnectedRawOrbitSourceRows` to
`SelectedRawTailCoverageSourceRows` ladder, and `repeated_tail_rows` is reduced
to `SelectedRawOrbitRepeatedTailCutPartitions` for that same selected raw
orbit.  The selected successor data still travels through actual
`unboundedFrontierEdgeSet` membership in `selectedRows`; no facade, induced
frontier graph, arbitrary carrier cycle, or synthetic enclosure row was added.
Targeted builds of `S2SeededRawOrbitSource.lean` and
`S2BoundaryFreeRawSource.lean` passed on 2026-05-21.

2026-05-21 selected-head boundary-free angular source:

Claim `S2-codex-main-20260520-selected-head-boundaryfree-source` is checked in
`S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
boundaryFreeGraphVertexAngularNoBetweenRows_of_graphVertexGeometricOutgoingListNoBetweenRows
S2_codex_main_20260520_selected_head_boundaryFreeAngularRows_of_selectedIncidentEdgeRows_geometricOrderRows
S2_codex_main_20260520_selected_head_boundaryFreeAngularRows_of_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
S2_codex_main_20260520_selected_head_boundaryFreeAngularRows_family_of_selectedIncidentEdgeRows_geometricOrderRows
S2_codex_main_20260520_selected_head_boundaryFreeAngularRows_family_of_selectedIncidentEdgeRows_graphVertexGeometricOutgoingListNoBetweenRows
```

Route impact:

```text
LocalSelectedIncidentEdgePairSourceRows inputs
+ pointwise real geometricOutgoingDartList nonwrap selected-head rows
  or reusable GraphVertexGeometricOutgoingListNoBetweenRows
-> matching BoundaryFreeGraphVertexAngularNoBetweenRows for the selected heads
```

The selected heads are exactly those reconstructed from
`LocalSelectedIncidentEdgePairSourceRows` through the existing
cut-partition/local-two-germ route.  The support reducer exposes either
`S2_dyn_20260520_graph_vertex_geometric_order_row_source_for_selectedEdgePairRoute`
or the equivalent pointwise
`GeometricRotationSystem.GraphVertexGeometricOutgoingListNoBetweenRows` family
for those same heads.  Both residuals are stated over the real sorted
`GeometricRotationSystem.geometricOutgoingDartList`; no identity angular order,
all-adjacent endpoint source, induced frontier graph, arbitrary cycle, or
synthetic enclosure was introduced.  Targeted owner-file checks passed on
2026-05-21:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\GeometricRotationSystem.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean
```

2026-05-21 subcontinuum-between closed-split reduction:

Claim `S2-codex-main-20260520-subcontinuum-between-source` is checked in
`ExteriorComponentTopology.lean`.

New declarations:

```lean
planarContinuumUnboundedComplementFrontierSubcontinuumBetween_of_closedSeparationForcesContinuumSeparation
S2_codex_main_20260520_subcontinuum_between_source
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierClosedSeparationForcesContinuumSeparation
-> PlanarContinuumUnboundedComplementFrontierConnected
-> PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
```

This strictly reduces the live subcontinuum-between topology leaf below the
connected-frontier theorem to the existing Janiszewski-style closed-frontier
continuum-separation residual.  It adds no facade/source package and does not
use final boundary-cycle rows, induced frontier graphs, arbitrary cycles, or
synthetic enclosures.  Targeted `ExteriorComponentTopology.lean` check passed
on 2026-05-21 with only pre-existing linter warnings.

2026-05-21 selected incident-edge source preserving heads:

Claim `S2-agent-selected-incident-edge-source-20260520c` is checked in
`S2LocalTwoGermAssembly.lean`.

New declarations:

```lean
localSelectedIncidentEdgePairSourceRows_of_neighborPairRows_preserving_heads
localSelectedIncidentEdgePairSourceRows_of_localSectorRows_preserving_heads
S2_agent_selected_incident_edge_source_20260520c_of_neighborPairRows
S2_agent_selected_incident_edge_source_20260520c_of_localSectorRows
S2_agent_selected_incident_edge_source_20260520c_family_of_neighborPairRows
S2_agent_selected_incident_edge_source_20260520c_family_of_localSectorRows
```

Route impact:

```text
actual UnboundedFrontierCarrierNeighborPairAt rows
  or actual UnboundedFrontierCarrierLocalSectorRowsAt rows
-> LocalSelectedIncidentEdgePairSourceRows inputs
```

The reducers preserve the exact selected heads named by the source rows.  The
neighbor-pair form reads selected `unboundedFrontierEdgeSet` incidences through
`unboundedFrontierCarrierGraph_adj_iff` and uses the supplied `neighbor_iff`
for incident completeness.  The local-sector form copies the stored
`left_edge`/`right_edge` incidences and uses the local-sector `only` row after
reinterpreting any selected incident frontier edge as an edge of the actual
carrier graph.  No all-adjacent endpoint source, induced frontier graph,
arbitrary cycle, synthetic enclosure, identity angular order, axiom, sorry, or
debug command was introduced.  Targeted owner-file build and forbidden-token
scan passed on 2026-05-21.

2026-05-21 boundary-free connected raw-orbit local/component reduction:

New declarations:

```lean
S2ExteriorBoundarySource.componentTopologySourceRows_of_faceDartOrbitExteriorCarrierRows
S2ExteriorBoundarySource.componentTopologySourceRows_family_of_faceDartOrbitExteriorCarrierRows
S2BoundaryFreeRawSource.boundaryFreeLocalComponentRows_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
S2BoundaryFreeRawSource.boundaryFreeCarrierConnected_source_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
S2BoundaryFreeRawSource.boundaryFreeLocalComponentRows_family_of_faceDartOrbitExteriorCarrierRows_incidentGermFrontierEdge_20260520c
```

Route impact:

```text
FaceDartOrbitExteriorCarrierRows C inputs
+ selected incident-germ frontier-edge membership
-> BoundaryFreeNoThirdGermSource inputs
 + UnboundedExteriorFrontierComponentTopologySourceRows inputs
-> BoundaryFreeNoThirdGermSource inputs
 + (unboundedFrontierCarrierGraph C inputs).Connected
```

This is the checked write-scope handoff for
`S2-agent-boundaryfree-connected-raw-orbit-source-20260520c`: the two
local/connected fields needed by downstream
`BoundaryFreeConnectedRawOrbitSourceRows` constructors now come from the same
honest exterior face-dart carrier rows, preserving actual
`unboundedFrontierEdgeSet` incidences.  The remaining exact leaf outside this
scope is the seeded raw-orbit `RawOrbitDartEdgeFrontierSource`/selected
successor propagation row; no adjacent-endpoint chord, induced frontier graph,
arbitrary cycle, or synthetic enclosure was introduced.

2026-05-21 k6 selected-incident input lowering:

`ErdosProblems1066/Swanepoel/S2CarrierCutSource.lean` now records the claim
`S2-k6-selected-incident-edge-pair-from-inputs` as a strict reduction:

```lean
S2_k6_selected_incident_edge_pair_from_inputs_of_carrierCutFieldwise
S2_k6_selected_incident_edge_pair_from_inputs_family_of_carrierCutFieldwise
S2_k6_selected_incident_edge_pair_from_inputs_nonempty_iff_carrierCutFieldwise
```

The exact residual is the e32 actual-carrier cut field: at each actual
unbounded-frontier carrier vertex, choose two concrete incident
`unboundedFrontierEdgeSet` heads and provide a cut partition for every third
actual `unboundedFrontierCarrierGraph` neighbour.  This composes the existing
e32 selected-row eraser and does not introduce induced frontier graphs,
all-adjacent endpoint closure, arbitrary cycles, convex hulls, identity
angular order, or all-outgoing no-between rows.

2026-05-20 historical compact decomposition after subagent sweep:

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
the former route superseded by local-leaf correction through `UnboundedExteriorFrontierCycleRows`, then
the W32 handoff.

2026-05-21 checked raw-orbit support composer, not live route (20260520d):

Claim `S2-agent-current-route-composer-20260520d` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_boundaryBumpingPointsBetween_selectedIncidentEdgeRows_connectedRawOrbit_leftPred_geometricSuccessorNonwrap_20260520d
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
-> S2_agent_topology_points_between_source_20260520d
-> S2_agent_crossing_subcontinuum_source_20260520c
-> PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
+ actual selected unboundedFrontierEdgeSet incident rows
+ BoundaryFreeConnectedRawOrbitSourceRows
+ one-sided selected-left = raw predecessor head-match rows
+ selected raw geometric successor nonwrap rows
+ noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is a W32 consumer only, but it is a real checked reduction rather than a
facade label: it lowers the topology leaf to the U-indexed point-between
boundary-bumping source and then reuses the checked crossing-subcontinuum,
connected raw-tail, left-pred/full-head-match, and successor-nonwrap/orientation
reducers.  The exact remaining leaves are:

```lean
ExteriorComponentTopology.PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
forall C inputs, S2LocalTwoGermAssembly.LocalSelectedIncidentEdgePairSourceRows inputs
forall C inputs, ExteriorComponentTopology.BoundaryFreeConnectedRawOrbitSourceRows inputs
forall C inputs, ExteriorComponentTopology.S2_current_selected_raw_left_pred_head_match_source_20260520b
  (selectedEdgeRows C inputs)
  (ExteriorComponentTopology.S2_current_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520b
    (connectedRawRows C inputs))
forall C inputs, ExteriorComponentTopology.SelectedRawOrbitGeometricSuccessorNonwrapRows
  (ExteriorComponentTopology.S2_current_selectedRawTailCoverageSourceRows_of_connectedRawOrbitSourceRows_20260520b
    (connectedRawRows C inputs))
forall {n : Nat} (C : UDConfig n),
  MinimalGraphFacts.IsMinimalClearedFailure C -> CutVertexInterface.NoCutVertex C
```

No unconditional S2 W32 theorem was added.  The no-cut input is still available as

```lean
NoCutMinimalityClosureW34.noCutVertexFamily_of_refuting_bothPlusSidesCutForced
```

and has the exact `noCutRows` shape consumed by the W32 route.  Focused W32
owner build passed on 2026-05-21.

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

2026-05-21 final crossing-subcontinuum W32 composer:
Claim `S2-agent-final-topology-handoff-from-crossing-20260520c` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuum_selectedIncidentEdgeRows_connectedRawOrbit_leftPred_geometricSuccessorNonwrap_20260520b
```

Route impact:

```text
PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum
+ actual selected unboundedFrontierEdgeSet incident rows
+ BoundaryFreeConnectedRawOrbitSourceRows
+ one-sided selected-left = raw predecessor head-match rows
+ selected raw geometric successor nonwrap rows
+ noCutRows
-> no-subcontinuum / finite no-closed-separation topology via
   minimalFailureExactActualTopologyFieldsTarget_of_crossingSubcontinuum_selectedNeighborInput_20260520
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
the crossing-subcontinuum frontier-subcontinuum theorem, selected incident-edge
rows, boundary-free connected raw-orbit rows, left-predecessor head-match rows
on the selected raw-tail package, selected raw geometric successor nonwrap
rows, and S1 no-cut rows.  Focused W32 owner build passed on 2026-05-21.

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

2026-05-20 crossing frontier-subcontinuum connected repair:

New declarations:

```lean
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum_of_subcontinuumBetween_connected
S2_codex_cont_20260520_crossing_frontier_subcontinuum_source
planarContinuumUnboundedComplementFrontierCrossingSubcontinuumForcesBounded_of_subcontinuumBetween_connected
```

Route:

```text
PlanarContinuumUnboundedComplementFrontierSubcontinuumBetween
+ IsConnected K
-> crossing frontier-subcontinuum witness for the displayed split
-> crossing-subcontinuum boundedness for the displayed split
```

The strict connected-compactum repair keeps the remaining topology theorem on
the non-circular `SubcontinuumBetween` branch. The full global source
`PlanarContinuumUnboundedComplementFrontierCrossingSubcontinuumYieldsFrontierSubcontinuum`
is still not inhabited here because that `Prop` has no `IsConnected K`
hypothesis; in the finite S2 compactum, connectedness is supplied by the
existing `embeddedEdgeSet_connected_of_inputs` row.

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

2026-05-20 historical short S2 support lane:
The former support route used the W32 consumer

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

2026-05-20 historical connected raw-orbit support handoff:
The former W32 support route was shortened to the no-orientation connected
raw-orbit handoff:

```lean
FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_connectedRawOrbitSourceRows
```

Its former S2 source leaf was:

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

2026-05-20 historical W32 support composer:
`minimalFailureExactActualTopologyFieldsTarget_of_crossingRelativeClopen_localSector_geometricOutgoingListNoBetween_20260520`
is the historical checked non-circular W32 support handoff for the former support
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

2026-05-20 historical sharp W32 support composer:
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

This is now the source-facing split to attack.  The former proof leaves
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

## Historical Claims Superseded By 2026-05-21 p

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

## Historical Live Objective Superseded By 2026-05-21 p

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

2026-05-21 local-leaf audit correction: the shortest checked support route to
`UnboundedExteriorFrontierCycleRows` should use finite no-closed-separation
plus actual carrier-neighbour pairs, not the selected-head nonwrap
outgoing-list no-between package:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs a, UnboundedFrontierCarrierNeighborPairAt inputs a
-> localSectorRows_of_unboundedFrontierCarrierGraph_neighborPairRows_source
-> unboundedExteriorFrontierCycleRows_of_finiteDrawingNoClosedSeparation_localSectorRows
-> FaceBoundaryTopologySourceW32.
     minimalFailureExactActualTopologyFieldsTarget_of_finiteDrawingNoClosedSeparation_neighborPairRows_20260521
```

The older route through
`BoundaryFreeLocalSectorGeometricAngularSource`,
`UnboundedFrontierCarrierGeometricNeighborSelectionSourceRows`, or selected-head
`GraphVertexGeometricOutgoingListNoBetweenRows` is compatibility-only.  It is
not the live source leaf because ordinary outgoing unit-distance chords may
exist between exterior carrier directions; S2 only needs the two actual
unbounded-frontier carrier germs.

The topology branch remains a separate genuine planar-continuum theorem: a
closed split of the frontier of an unbounded complement component must yield a
forbidden separation in the compact finite drawing.  Current Janiszewski and
component-avoidance reductions are support for
`FiniteDrawingUnboundedComplementFrontierNoClosedSeparation`, not substitutes
for the exterior boundary cycle.

Current checked erasers such as the CT/CO raw-orbit composers remain consumers
or compatibility support only.  The live work is proving the two source leaves
in the 2026-05-21 correction honestly from
`FinitePlanarOuterComponentInputs C`, with the local leaf focused on actual
carrier-neighbour rows and the no-cut/cut-partition argument for excluding a
third exterior-boundary carrier neighbour.

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

## Historical Source Tasks Superseded By 2026-05-21 p

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
  names after pruning completed/superseded dynamic claims.  The former residual-board snapshot
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

In the old raw-orbit support lane, the relevant orbit is the selected exterior-oriented geometric face-successor
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
  Status: historical/support-only.
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
  lift that pointwise row to the former W32 selected-head outgoing-list support
  source.  The former S2-C leaf was therefore the genuine pointwise
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

Thus the one-index triple wrapper is no longer a former S2-C support leaf.  In the old support lane, the
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

So the former S2-C residual is now the exact no-between source.  At each selected
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
that supplies the no-between rows outright.  The former S2-C support leaf is
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
list.  The historical W32 chain is:

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
selected heads.  The former S2-C residual is now to construct the pointwise
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

Codex-main added the executable W32 handoff for the former support S2
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
the raw-orbit program, but it is not the checked raw-orbit support S2 handoff.

The checked raw-orbit support handoff remains:

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

2026-05-21 k6 actual-boundary sector input source:

Claim `S2-k6-actual-boundary-sector-input-source` is checked in the
import-safe seeded raw-orbit owner file.

New declarations:

```lean
S2_k6_actual_boundary_sector_input_source_of_connectedRawOrbitSourceRows_minimalDeletedTailSeparation_rawOrientation
S2_k6_actual_boundary_sector_input_source_family_of_connectedRawOrbitSourceRows_minimalDeletedTailSeparation_rawOrientation
S2_k6b_boundary_cycle_source_from_raw_orbit
S2_k6b_boundary_cycle_source_from_raw_orbit_family
```

The k6 theorem produces exactly:

```lean
Exists fun B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C =>
  (forall v, (canonicalGraph C).point v ∈
      frontier (unboundedExteriorComponentRows C inputs).exterior ↔
    Exists fun k : Fin B.length => B.vertex k = v) ∧
  forall k : Fin B.length,
    BoundaryVertexExteriorSectorRowsAt inputs B k
```

from connected raw-orbit rows, selected minimal deleted-tail separation on the
internally selected raw orbit, and selected raw orientation for that same
orbit.  The proof strictly lowers minimal deleted-tail separation through the
existing selected k5 repeated-tail cut-partition eraser, then reuses the
checked actual-boundary/local-sector/orientation boundary-sector reducer.  No
induced frontier graph, arbitrary carrier cycle, convex hull, identity
angular-order shortcut, or all-adjacent endpoint row is introduced.

Import-safety correction: the attempted connected-raw-orbit `k6b` wrappers
were removed from `S2ExteriorBoundarySource.lean` because that file must not
import or mention seeded raw-orbit types.  The same names now live in
`S2SeededRawOrbitSource.lean`, where `BoundaryFreeConnectedRawOrbitSourceRows`
and the selected raw-tail rows are defined.

One adjacent Prop/Type packaging issue in the existing k6 witness-map reducer
was tightened by changing the map package to `PSigma`, preserving `.1`/`.2`
projection use while avoiding a `Prop`-valued component in `Prod`.

Verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2ExteriorBoundarySource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2ExteriorBoundarySource
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
```

2026-05-21 k6 boundary-free local input source:

Claim `S2-k6-boundary-free-local-input-source` is strictly lowered in
`Swanepoel/S2BoundaryFreeRawSource.lean`.

New direct local no-third-germ reducers:

```lean
boundaryFreeLocalNoThirdGermSourceRows_of_selectedNeighborGeometricOrder_localIncident_20260521k6
boundaryFreeLocalNoThirdGermSourceRowsFamily_of_selectedNeighborGeometricOrder_localIncident_20260521k6
boundaryFreeLocalNoThirdGermSourceRows_of_geometricSelection_localIncident_20260521k6
boundaryFreeLocalNoThirdGermSourceRowsFamily_of_geometricSelection_localIncident_20260521k6
```

The existing local input reducers
`boundaryFreeLocalInputSourceReduction_of_selectedNeighborGeometricOrder_localIncident_20260520`
and
`boundaryFreeLocalInputSourceReduction_of_geometricSelection_localIncident_20260520`
now build their `localNoThirdGermSource` directly from the actual selected
carrier rows and the finite-drawing local incident-germ isolation row.  The
selected heads and `left_edge`/`right_edge` fields are the selected
`unboundedFrontierEdgeSet` incidences; the no-third field is the local-radius
row from
`selectedNeighborGeometricOrderLocalNoThirdGermRows_of_localIncidentGermMembership`.

This removes the local-input branch's detour through local-sector rows and
does not use all-adjacent endpoint closure, induced frontier graphs, global
closed-germ membership, boundary cycles, or arbitrary cycle data.

Verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2BoundaryFreeRawSource.lean
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2LocalTwoGermAssembly.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2BoundaryFreeRawSource
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2LocalTwoGermAssembly
```

2026-05-21 k5 deleted-neighbor unreachable lowering:

`S2CarrierLocalSource.lean` now exposes the deleted-neighbor source through
the actual selected frontier carrier data and the k4 no-cut consumers:

```lean
S2_k5_deleted_neighbor_unreachable_of_carrierCutFieldwise
S2_k5_deleted_neighbor_unreachable_family_of_carrierCutFieldwise
S2_k5_deleted_neighbor_unreachable_of_selectedIncidentEdgePairRows
S2_k5_deleted_neighbor_unreachable_family_of_selectedIncidentEdgePairRows
S2_k5_deleted_neighbor_unreachable_nonempty_iff_carrierCutFieldwise
S2_k5_deleted_neighbor_unreachable_nonempty_iff_selectedIncidentEdgePairRows
```

The fieldwise route packages the e32 actual selected-carrier cut source, uses
`S2_dynamic_no_cut_degree_two_k4_of_cutPartitionInputSource`, and then reuses
the checked actual-degree-to-deleted-neighbor eraser.  The selected-row route
first lowers pure `LocalSelectedIncidentEdgePairSourceRows` to the same e32
fieldwise source.  No `ExteriorComponentTopology.lean` edit was needed.

Verification:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2CarrierLocalSource.lean
```

The direct pinned Lean check passed.  The targeted Lake module build was also
run; after one timeout it failed while rebuilding the pre-existing dirty
dependency `S2LocalTwoGermAssembly.lean` at line 15320, where `cases` tries to
eliminate an `Exists` into `SelectedUnboundedFrontierEdgeLocalIsolationRowsAt`.
The new `S2CarrierLocalSource.lean` declarations are past the direct check.
Focused scans on the touched Lean file and new diff found no proof placeholders,
unsafe/debug constructs, or banned shortcut route names in the new code.

Exact residual blocker: prove the actual selected-carrier data, equivalently
`S2CarrierCutSource.S2_agent_carrier_cut_source_worker_20260521e32_fieldwise`
or its pure selected-row form
`LocalSelectedIncidentEdgePairSourceRows inputs`, for each
`FinitePlanarOuterComponentInputs C`.

2026-05-21 U-indexed point-between to connected raw-orbit source:

Claim `S2-codex-main-topology-to-connected-raw-source-20260521` is checked in
`ExteriorComponentTopology.lean` and `S2SeededRawOrbitSource.lean`.

New declarations:

```lean
planarContinuumUnboundedComplementFrontierPreconnected_of_janiszewskiSubcontinuumPointsBetween
boundaryFreeConnectedRawOrbitSourceRows_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_selectedSuccessorEdge_20260521
boundaryFreeConnectedRawOrbitSourceRows_family_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_selectedSuccessorEdge_20260521
```

The compact connected raw-orbit package can now be assembled directly from:

```text
BoundaryFreeInputSourceReduction inputs
+ PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs
-> BoundaryFreeConnectedRawOrbitSourceRows inputs
```

This demotes older preconnected/component-topology variants to support
surfaces for this branch.  The live proof work remains the actual input-level
source rows: boundary-free local reduction and selected raw `faceSucc`
frontier-edge source, with no all-adjacent endpoint closure, induced frontier
graph, arbitrary carrier cycle, or all-outgoing-dart no-between shortcut.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.ExteriorComponentTopology
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
```

2026-05-21 W32 short handoff from connected raw-orbit source leaves:

Claim `S2-codex-main-w32-connected-raw-short-handoff-20260521` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_boundaryFreeInput_janiszewskiSubcontinuumPointsBetween_selectedSuccessorEdge_20260521
```

Current short S2 route:

```text
forall C inputs, BoundaryFreeInputSourceReduction inputs
+ PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ forall C inputs, RawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource inputs
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The repeated-tail cut/orientation path remains useful support for actual
boundary-cycle reconstruction, but it is not needed by this checked W32
branch once `BoundaryFreeConnectedRawOrbitSourceRows` is inhabited directly.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

2026-05-21 corrected local-input W32 handoff:

Claim `S2-codex-main-w32-local-input-short-handoff-20260521` is checked in
`FaceBoundaryTopologySourceW32.lean`.

New declarations:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiSubcontinuumPointsBetween_boundaryFreeLocalInput_20260521
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiSubcontinuumPointsBetween_localNoThirdGermSource_20260521
minimalFailureExactActualTopologyFieldsTarget_of_janiszewskiSubcontinuumPointsBetween_cutPartitionInputSource_20260521
```

Preferred short S2 route:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ forall C inputs, BoundaryFreeLocalInputSourceReduction inputs
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The same handoff is now checked with the local source written as the sharp
actual-carrier cut-partition package:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierSubcontinuumPointsBetween
+ forall C inputs,
    UnboundedFrontierCarrierNeighborPairCutPartitionInputSource C inputs
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

This is now preferred over the connected raw-orbit handoff when the goal is
only W32/S2 closure, because it uses the corrected local-radius input package
and does not require the global closed-germ `BoundaryFreeNoThirdGermSource`.
The connected raw-orbit/repeated-tail/orientation route remains support for
actual boundary-cycle reconstruction, not the shortest W32 leaf.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.FaceBoundaryTopologySourceW32
```

2026-05-21 carrier nonemptiness / no-isolated tightening:

The current finite S2 route no longer needs callers to manufacture carrier
nonemptiness from a selected frontier-edge cover.  `ExteriorComponentTopology`
now has the intrinsic carrier nonemptiness row

```lean
unboundedFrontierCarrier_nonempty
```

from the actual unbounded exterior frontier seed.  It also records graph-side
no-isolated ambient input facts from connectedness plus the supplied unit cycle:

```lean
nontrivial_vertices_of_finitePlanarOuterComponentInputs
exists_unitDistanceSimpleGraph_adjacent_of_finitePlanarOuterComponentInputs
exists_canonicalGraph_adjacent_of_finitePlanarOuterComponentInputs
```

and the selected-carrier no-isolated consequences of the genuine endpoint
incident-edge source:

```lean
exists_unboundedFrontierCarrierGraph_adj_of_frontierVertexIncidentSource
unboundedFrontierCarrierGraph_neighborFinset_nonempty_of_frontierVertexIncidentSource
unboundedFrontierCarrierGraph_neighborFinset_card_pos_of_frontierVertexIncidentSource
```

The connectedness reducer

```lean
unboundedFrontierCarrierGraph_connected_of_adjClosed_topologyRows_noAuxNonempty
```

now discharges the nonempty vertex-type side condition internally.  The live
local source is still the sharp actual-carrier cut-partition input; these
helpers only remove auxiliary nonemptiness clutter and expose the real
remaining local fact: selected exterior-frontier incident edges, then exactly
two actual carrier neighbours.

2026-05-21 punctured-frontier incident-edge reduction:

```text
IsPreconnected (frontier (unboundedExteriorComponentRows C inputs).exterior)
+ pointwise nontriviality of that same frontier at every graph-frontier vertex
-> punctured accumulation at graph-frontier vertices
-> FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs
-> UnboundedExteriorFrontierComponentTopologyInputSourceRows inputs
```

Checked declarations:

```lean
punctured_points_of_preconnected_nontrivial
punctured_vertex_frontier_of_preconnected_frontier_nontrivialAt
frontierVertexIncidentSource_of_frontierPreconnected_nontrivialAt
frontier_nontrivialAt_of_frontierVertexIncidentSource
frontierVertexIncidentSource_iff_frontier_nontrivialAt_of_preconnected
frontier_nontrivialAt_of_two_frontier_points
frontierVertexIncidentSource_of_frontierPreconnected_two_frontier_points
exists_two_frontier_points_of_unboundedFrontierEdgeSet
exists_two_frontier_points_of_frontier_edgeInterior
exists_two_frontier_points_of_two_unboundedFrontierVertices
exists_unboundedFrontierVertexSet_or_two_frontier_points
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_frontierPreconnected_nontrivialAt
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingPreconnected_nontrivialAt
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_nontrivialAt
unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_nontrivialAt
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_points
unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_points
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_selectedEdge
unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_selectedEdge
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_frontier_edgeInterior
unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_frontier_edgeInterior
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_vertices
unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_two_frontier_vertices
unboundedExteriorFrontierComponentTopologyInputSourceRows_of_finiteDrawingNoClosedSeparation_no_frontier_vertex
unboundedExteriorFrontierComponentTopologySourceRows_of_finiteDrawingNoClosedSeparation_no_frontier_vertex
```

This is a source reducer only.  It does not prove pointwise nontriviality from
`FinitePlanarOuterComponentInputs C`, and it must not be read as an
all-adjacent endpoint or induced-carrier statement.  The remaining local work
is still to identify actual selected exterior-boundary incident edges.  One
now-sharpened branch is: prove finite no-closed-separation/preconnectedness
and either a selected unbounded-frontier edge, an open-edge frontier seed, two
distinct graph-frontier vertices, or two distinct points on the actual
unbounded exterior frontier.  The open-edge branch of the canonical frontier
seed already supplies the two-point row; two distinct graph-frontier vertices
also supply it by `canonical_point_injective`.  The remaining difficult seed
case is a singleton graph-frontier vertex.  It cannot coexist with
`FrontierVertexIncidentUnboundedFrontierEdgeSource`, by
`unboundedFrontierVertexSet_card_ne_one_of_frontierVertexIncidentSource`, so
the singleton residual is exactly the missing lower local topology that must
produce an incident selected edge or otherwise contradict singleton frontier
support.  The alternate branch remains the raw-orbit or cut-partition route.

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
The former local/geometric target is that compact neighbour-selection row,
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

Checked raw-orbit support handoff:

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
2026-05-21 S2 k6 selected successor faceSucc edge source:

Claim `S2-k6-selected-successor-faceSucc-edge-source` is checked in
`Swanepoel/S2SeededRawOrbitSource.lean`.

New declarations:

```lean
rawOrbitIteratedFaceSuccFrontierEdgeNoOrbitSource_of_selectedNeighborGeometricOrder_successorTailRows_20260520
S2_k6_selected_successor_faceSucc_edge_source
S2_k6_selected_successor_faceSucc_edge_source_family
```

The selected raw `faceSucc` frontier-edge source is now exposed directly as a
strict reducer from local selected-neighbour geometric-order rows plus the
genuine successor-tail geometric rows for the exact selected carrier heads.
The route uses the existing safe selected third-germ/local-sector handoff and
the selected successor-tail geometric row; it does not introduce global
outgoing-list no-between, endpoint/no-chord closure, induced frontier graphs,
identity angular order, final boundary-cycle rows, or synthetic enclosure rows.

I also pinned the selected repeated-tail witness wrapper
`selectedRawOrbitRepeatedTailWitnessSource_of_repeatedTailExteriorCutRows_20260521k6`
by eta-expanding the implicit repeated-tail indices at the final witness map.
This is proof-shape stabilization only; it does not change the source surface.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2SeededRawOrbitSource.lean
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066.Swanepoel.S2SeededRawOrbitSource
rg -n -e "\bsorry\b" -e "\badmit\b" -e "\baxiom\b" ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-21 r18 topology K-component point-between source:

Claim `S2-r18-topology-kcomponent-points-between-source` is checked in
`Swanepoel/S2TopologySource.lean`.

New declaration:

```lean
S2_r18_topology_kcomponent_points_between_source_of_frontierComponent_20260521r18
```

Route impact:

```text
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentPointsBetween
```

The lowerer uses the existing compact frontier-component packaging: a direct
frontier-component theorem supplies membership of the second frontier point in
the connected component of the first inside `frontier U`; the image of that
component is the compact connected witness required by the point-between
source.  This stays wholly in the topology layer and does not use boundary
cycles, actual-sector rows, carrier rows, W32, induced frontier graphs,
arbitrary cycles, synthetic enclosure predicates, or convex-hull data.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2TopologySource.lean
```

2026-05-21 r18 boundary-free incident source:

Claim `S2-r18-frontier-incident-from-boundary-free` is checked in
`Swanepoel/S2CarrierLocalSource.lean`.

New declarations:

```lean
boundaryFreeNoThirdGermSource_of_boundaryFreeLocalSectorGeometricAngularSource
S2_r18_boundaryFreeNoThirdGermSource_of_boundaryFreeLocalSectorGeometricAngularInputRows_20260521r18
S2_r18_boundaryFreeNoThirdGermSource_family_of_boundaryFreeLocalSectorGeometricAngularInputRows_20260521r18
S2_r18_frontierVertexIncidentSource_of_boundaryFreeLocalSectorGeometricAngularInputRows_20260521r18
S2_r18_frontierVertexIncidentSource_family_of_boundaryFreeLocalSectorGeometricAngularInputRows_20260521r18
```

Route impact:

```text
BoundaryFreeLocalSectorGeometricAngularInputRows inputs
-> BoundaryFreeNoThirdGermSource inputs
-> FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs
```

The proof uses the geometric-angular selector's genuine consecutive
`geometricOutgoingDartList` no-between row to contradict the third-germ
angular-between row.  It does not use actual-sector rows, W32, final boundary
cycles, induced frontier graphs, arbitrary cycles, all-adjacent endpoint rows,
or global outgoing-list shortcuts.  The exact remaining local source for both
targets on this lane is therefore
`BoundaryFreeLocalSectorGeometricAngularInputRows inputs`.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066\Swanepoel\S2CarrierLocalSource.lean
```

2026-05-21 r19 repeated-tail exterior-cut source:

Claim `S2-r19-repeated-tail-exterior-cut-source` is checked in
`Swanepoel/S2SeededRawOrbitSource.lean`.

New declarations:

```lean
S2_r19_selectedRawOrbitRepeatedTailExteriorCutRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor_cyclicSuccCutPartitions
S2_r19_selectedRawOrbitRepeatedTailPrimitiveSourceRows_of_componentInput_geometricSelection_incidentGerm_strictSuccessor_cyclicSuccCutPartitions
```

Route impact:

```text
SelectedRawOrbitCyclicSuccDeletedTailCutPartitionSource
  (for the r35/r18 selected raw orbit)
-> RawFaceSuccOrbitRepeatedTailExteriorCutRows
  (pointwise on that same orbit)
-> SelectedRawOrbitRepeatedTailPrimitiveSourceRows
```

This is the preferred repeated-tail boundary for the current r18/r35
actual-sector spine.  It bypasses the demoted endpoint-frontier
component-separation route and stays at source level: no actual-sector rows,
W32, final cycle, induced graph, arbitrary cycle, or all-adjacent endpoint
shortcut are used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-22 q9 topology frontier-component trace reduction:

Claim `S2-agent-q9-topology-frontier-component` is checked in
`Swanepoel/S2TopologySource.lean`.

New declarations:

```lean
PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentTracePreconnected
planarJaniszewskiBoundaryBumpingKComponentFrontierComponent_of_kComponentTracePreconnected
S2_agent_q9_topology_frontier_component_of_kComponentTracePreconnected_20260522
```

Route impact:

```text
forall K U y,
  IsCompact K
  -> U = connectedComponentIn Kᶜ x for some x ∈ Kᶜ
  -> ¬ Bornology.IsBounded U
  -> y ∈ frontier U
  -> IsPreconnected (frontier U ∩ connectedComponentIn K y)
-> PlanarJaniszewskiBoundaryBumpingUnboundedComponentFrontierKComponentFrontierComponent
```

The proof uses the existing compact complement-component frontier-subset lemma
to put the base frontier point back in `K`, then applies Mathlib's
`IsPreconnected.subset_connectedComponentIn` to the trace
`frontier U ∩ connectedComponentIn K y`.  This is a strict source reduction:
the remaining topology obligation is now one trace-preconnectedness theorem,
not the pointwise `z` component bookkeeping.  It does not use W32, final
boundary-cycle rows, carrier rows, actual-sector rows, induced frontier graphs,
arbitrary cycles, synthetic enclosure predicates, or convex-hull data.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2TopologySource.lean
```

2026-05-22 q11 repeated-tail primitive lowering:

Claim `S2-agent-q11-repeated-tail-primitive` is checked in
`Swanepoel/S2SeededRawOrbitSource.lean`.

New declarations:

```lean
S2_agent_q11_primitiveSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_repeatedTailExteriorCutRows
S2_agent_q11_primitiveSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_actualExteriorArcRows
S2_agent_q11_actualExteriorSectorInputSourceRows_family_of_finiteNoOpen_vertexIncident_geometricSelection_incidentGerm_selectedCarrierRows_repeatedTailExteriorCutRows
```

Route impact:

```text
FiniteDrawingUnboundedComplementFrontierNoOpenSeparation
+ FrontierVertexIncidentUnboundedFrontierEdgeSource
+ UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource
+ selected incident-germ frontier-edge rows
+ selected raw faceSucc carrier propagation rows
+ concrete repeated-tail exterior cut rows on the r17 selected raw orbit
-> SelectedRawOrbitRepeatedTailPrimitiveSourceRows on that same r17 orbit
-> q10 actual exterior-sector source
```

The same primitive raw-index residual is also strictly lowered from pairwise
`SelectedRawOrbitRepeatedTailActualExteriorArcRows` on the r17 selected raw
orbit.  The cut-row route uses the existing selected raw-orbit no-cut eraser;
the actual exterior-arc route uses the arc rows' concrete open-side witnesses,
coverage, disjointness, and anticompleteness directly.  No W32 facade, final
boundary cycle, actual-sector premise, induced frontier graph, arbitrary
cycle, all-adjacent endpoint statement, identity angular order, or convex-hull
shortcut is introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2SeededRawOrbitSource.lean
```

2026-05-22 q12 frontier accumulation lowering:

Claim `S2-agent-q12-frontier-accumulation` is checked in
`Swanepoel/S2TopologySource.lean`.

New declarations:

```lean
S2_agent_q12_outsideAccumulationSource_of_puncturedAccumulation_20260522
S2_agent_q12_outsideAccumulationSource_family_of_puncturedAccumulation_20260522
S2_agent_q12_singletonBoundaryBumpingObstruction_of_puncturedAccumulation_20260522
S2_agent_q12_singletonBoundaryBumpingObstruction_family_of_puncturedAccumulation_20260522
S2_agent_q12_topology_sources_of_kComponentPointsBetween_puncturedAccumulation_20260522
S2_agent_q12_topology_sources_of_globalKComponentPointsBetween_puncturedAccumulation_20260522
```

Route impact:

```text
UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs
-> FrontierVertexIncidentOpenSegmentClosureSource C inputs
-> FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs
-> UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier C inputs
-> UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs

FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween
+ forall C inputs,
    UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
   + FiniteDrawingUnboundedComplementFrontierNoOpenSeparation
   + forall C inputs,
       UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs
```

The q12 singleton branch no longer has `FrontierVertexIncidentUnboundedFrontierEdgeSource`
or the pointwise outside-accumulation source as its visible residual.  The
remaining local source is the pointwise punctured accumulation row on the
actual unbounded exterior frontier at graph vertices; the checked composition
uses only the existing incident open-segment closure and selected-edge
promotion reducers.  No final boundary cycle, W32 target, actual exterior
sector source, induced frontier graph, arbitrary cycle, convex hull, identity
angular rows, or synthetic enclosure is used.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2TopologySource.lean
```

2026-05-22 q11 topology trace/accumulation lowering:

Claim `S2-agent-q11-topology-trace-accumulation` is checked in
`Swanepoel/S2TopologySource.lean`.

New declarations:

```lean
FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween
finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_kComponentPointsBetween
finiteDrawingUnboundedComplementFrontierKComponentPointsBetween_of_globalKComponentPointsBetween
S2_agent_q11_finiteDrawing_kTracePreconnected_of_kComponentPointsBetween_20260522
S2_agent_q11_finiteDrawing_kTracePreconnected_of_globalKComponentPointsBetween_20260522
S2_agent_q11_outsideAccumulationSource_family_of_frontierVertexIncident_20260522
S2_agent_q11_topology_sources_of_kComponentPointsBetween_frontierVertexIncident_20260522
S2_agent_q11_topology_sources_of_globalKComponentPointsBetween_frontierVertexIncident_20260522
```

Route impact:

```text
FiniteDrawingUnboundedComplementFrontierKComponentPointsBetween
-> FiniteDrawingUnboundedComplementFrontierKTracePreconnected
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
   + FiniteDrawingUnboundedComplementFrontierNoOpenSeparation

forall C inputs, FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs
-> forall C inputs,
     UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier C inputs
-> forall C inputs,
     UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs
```

The finite trace leaf is now below a finite same-component point-between row
for the embedded drawing.  The singleton outside-accumulation branch is below
selected frontier-vertex incident edges, so q10 topology handoffs no longer
need an independent outside-accumulation source when incidence has already
been selected.  No W-facing wrapper, boundary-cycle row, carrier-cycle row,
actual-sector package, synthetic enclosure, induced frontier graph, or
all-adjacent endpoint shortcut is introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2TopologySource.lean
```

2026-05-22 q10 actual-sector integration:

Claim `S2-agent-q10-actual-sector-integration` is checked in
`Swanepoel/FaceBoundaryTopologySourceW32.lean`.

New declaration:

```lean
minimalFailureExactActualTopologyFieldsTarget_of_noClosedSeparation_singletonBoundaryBumping_geometricSelection_incidentGerm_selectedCarrierRows_boundaryArcRows_20260522q10
```

Route impact:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ forall C inputs,
    UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs
+ forall C inputs,
    UnboundedFrontierCarrierNeighborPairGeometricSelectionInputSource C inputs
+ selected incident-germ frontier-edge rows for that geometric selection
+ selected raw faceSucc carrier propagation rows
+ selected repeated-tail boundary-arc rows for the resulting r17 raw orbit
+ S1 noCutRows
-> MinimalFailureExactActualTopologyFieldsTarget
```

The theorem uses the q9 seed-and-incident frontier handoff to derive the
frontier-vertex incident source and the r14 no-closed-to-no-open conversion
before applying the q8 actual-sector eraser and the existing W32
actual-sector consumer.  The exact remaining source binders are the six
inputs displayed above before `noCutRows`; no W-numbered facade, duplicate
source package, synthetic enclosure predicate, induced frontier graph,
arbitrary cycle, all-adjacent endpoint statement, identity angular-order
shortcut, or convex-hull shortcut is introduced.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/FaceBoundaryTopologySourceW32.lean
```

2026-05-22 q9 seed-and-incident frontier reduction:

Claim `S2-agent-q9-seed-and-incident-frontier` is checked in
`Swanepoel/ExteriorComponentTopology.lean`.

New declarations:

```lean
S2_q9_selectedSeed_and_frontierVertexIncidentSource_of_finiteDrawingNoClosedSeparation_boundaryBumpingObstruction_20260522q9
S2_q9_selectedSeed_and_frontierVertexIncidentSource_family_of_finiteDrawingNoClosedSeparation_boundaryBumpingObstruction_20260522q9
```

Route impact:

```text
FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
+ UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs
-> UnboundedExteriorFrontierVertexPuncturedAccumulationSource C inputs
-> selected exterior seed + selected local unbounded-frontier edge
-> FrontierVertexIncidentUnboundedFrontierEdgeSource C inputs
```

This keeps the exterior seed and endpoint selected-edge source on one common
pre-boundary-cycle spine.  The theorem does not use actual-sector rows, W32,
an induced frontier graph, an arbitrary cycle, all-adjacent endpoint closure,
identity angular order, or convex-hull data.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/ExteriorComponentTopology.lean
```

2026-05-22 q10 finite trace topology source:

Claim `S2-agent-q10-topology-source` is checked in
`Swanepoel/S2TopologySource.lean`.

New declarations:

```lean
FiniteDrawingUnboundedComplementFrontierKTracePreconnected
finiteDrawingUnboundedComplementFrontierPreconnected_of_kTracePreconnected
finiteDrawingUnboundedComplementFrontierKTracePreconnected_of_globalTracePreconnected
S2_agent_q10_finiteDrawing_noClosed_noOpen_of_kTracePreconnected_20260522
S2_agent_q10_finiteDrawing_noClosed_noOpen_of_globalTracePreconnected_20260522
S2_agent_q10_topology_sources_of_kTracePreconnected_outsideAccumulation_20260522
S2_agent_q10_topology_sources_of_globalTracePreconnected_outsideAccumulation_20260522
```

Route impact:

```text
FiniteDrawingUnboundedComplementFrontierKTracePreconnected
-> FiniteDrawingUnboundedComplementFrontierPreconnected
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
   + FiniteDrawingUnboundedComplementFrontierNoOpenSeparation

FiniteDrawingUnboundedComplementFrontierKTracePreconnected
+ forall C inputs,
    UnboundedExteriorSingletonFrontierOutsideAccumulationForcesActualFrontier C inputs
-> FiniteDrawingUnboundedComplementFrontierNoClosedSeparation
   + FiniteDrawingUnboundedComplementFrontierNoOpenSeparation
   + forall C inputs,
       UnboundedExteriorSingletonFrontierBoundaryBumpingObstruction C inputs
```

The finite trace proof is the component/frontier lemma missing below the q9
global trace source: connectedness of `embeddedEdgeSet C` puts any two
frontier points in the same relative component of the drawing, and the trace
row gives a preconnected witness inside the selected frontier.  The paired
bundle keeps the singleton case at the pointwise outside-accumulation source
surface.  It does not use W32, final boundary-cycle rows, actual-sector rows,
carrier rows, induced frontier graphs, arbitrary cycles, all-adjacent endpoint
rows, identity angular order, synthetic enclosures, or convex-hull data.

Targeted verification passed:

```powershell
elan run leanprover/lean4:v4.28.0 lake env lean -DmaxErrors=80 ErdosProblems1066/Swanepoel/S2TopologySource.lean
```
