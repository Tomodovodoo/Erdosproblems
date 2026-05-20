# Remaining Explicit Fields Matrix

This is a compact handoff map for the remaining explicit data.  "Consumer"
means the first Lean surface that projects the field onward; downstream
modules are listed only when they explain why the field exists.

Status note, 2026-05-19: this matrix has been updated to the W32/W34 route
surfaces.  Older `MinimalFailureM8PaperFacts` and W20-W31 ledgers are useful
history, but the rows below are the current source-package blockers.

## Swanepoel W34 Route Premises

Live endpoint:

```text
SwanepoelW32FinalAssembly.W34ActualRoutePremises
```

Main source surfaces:

```text
M8ConstructionDataInhabitationW33.StrongestRouteSource
NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure
```

| Field/package | Remaining explicit data | Consumer | Downstream use |
|---|---|---|---|
| `MinimalFailureExactActualTopologyFieldsTarget` | Honest selected topology/outer-face data from a minimal cleared failure | `SelectedTopologyRowsInhabitationW33`, `FaceBoundaryTopologySourceW32` | Builds the selected topology rows for W34 route premises. |
| `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem` | Sector order for the selected nondegenerate outer face | `OuterBoundaryAngleSourceW34` | Lets angle/label rows use a concrete cyclic boundary order. |
| `ExactActualTopologyClosureMissingFieldPackage` | Closure fields not already present in exact topology rows | `SelectedTopologyRowsInhabitationW33` | Feeds the compact W34 constructor. |
| Long-arc plus W16 finite p/q source | Nonconcave long-arc budget and finite spine data | expanded `SwanepoelW32FinalAssembly` constructor | Alternative direct route to W34 premises. |
| `SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows` | Finite-walk generated cyclic-order rows | `FrameCyclicOrderAssemblyW32` | Supplies generated-order input to the route certificate. |
| `SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem` | Realization carrier, selected boundary gap, and degree 3/4 route rows | `K23RouteCoverageSourceW34` | Supplies K23 route coverage for selected frame cases. |
| `SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem` | Bad adjacency/common-neighbor exclusions | `K23RouteCoverageSourceW34` | Removes the selected bad-adjacency branch. |
| `S5AngleRowsForFinitePQSpineGeneratedOrderSource` | Compact label-certificate angle rows for the finite p/q spine and generated order | `ExactFigureWitnessSourceW34` | Supplies the final S5 angle package to W34 route premises. |

S2 exact-topology source note: the current live same-boundary theorem should
construct an actual unbounded frontier carrier/cycle `B` from
`FinitePlanarOuterComponentInputs`, prove graph vertices on the exterior
frontier iff they are vertices of `B`, prove consecutive boundary edge
membership in `unboundedFrontierEdgeSet`, prove the angular/no-between rows,
and prove `BoundaryFrontierIncidentEdgeExteriorAngularSector`.  The compact
handoff is then
`S2_agent_cm_actual_sector_source_20260520cm` ->
`BoundaryVertexExteriorSectorRowsAt` ->
`FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows`,
with the existing `UnboundedExteriorFrontierCycleRows`/W32 erasers downstream.
Do not add new bookkeeping layers or W facades for this route.  Do not count a
new theorem that merely hands actual rows, sector rows, carrier rows, or
selected successor-edge rows to a later worker while erasing them to
`UnboundedExteriorFrontierCycleRows`.  Such premises must be proved in the same
claim, or the claim must be rewritten as the missing-premise source task.  The
live S2 work is proving, from `FinitePlanarOuterComponentInputs C`, the local
two-germ/no-third source, the unbounded exterior frontier component/carrier
connectedness source, and the selected geometric `faceSucc`
frontier-propagation source.

Endpoint closure note: the all-adjacent frontier-endpoint source
`AdjacentFrontierEndpointsClosedSegmentEndpointClosureSource C inputs` is not a
valid unconditional target from `FinitePlanarOuterComponentInputs C`; boundary
chords can join exterior-frontier vertices without lying on the exterior
boundary.  Endpoint closure is only a checked selected-edge support theorem via
`closedSegmentEndpointClosureSource_of_incidentUnboundedFrontierEdgeSource`,
after membership in `unboundedFrontierEdgeSet C inputs` has been produced.

Completion gate:

```text
SwanepoelW32FinalAssembly.
  w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
```

or, for the expanded long-arc route:

```text
SwanepoelW32FinalAssembly.
  w34ActualRoutePremises_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
```

## Pach--Toth W34 Threshold Route

Live endpoint:

```text
PachTothRemainingSourceLedgerW34.
  exactAndArbitraryTargets_of_largeClosedPlacementFieldsSix_and_below
```

| Field/package | Remaining explicit data | Consumer | Downstream use |
|---|---|---|---|
| `LargeClosedPlacementFieldsSix` | Honest closed placements for all block lengths from six onward | `PachTothRemainingSourceLedgerW34`, `AlternativeNonRigidClosedPlacementW34` | Proves large exact block targets. |
| `BelowThresholdMetricFieldsSix` | Exact metric certificates for lengths below six | `PachTothRemainingSourceLedgerW34` | Closes the small complement to the threshold route. |
| `DeformedLengthOneExactBlocksTwoThroughFiveSource` | Genuine deformed length-one sources for block counts two through five | `SmallLengthExactTargetsConcreteW24` | Feeds `BelowThresholdMetricFieldsSix`. |
| `MinimalExactRemainderSplitSourceBlocker` | Remaining exact-to-arbitrary split input | `PachTothRemainingSourceLedgerW34`, `RemainderSplitSourceClosureW32` | Routes exact block targets to arbitrary `n`. |
| Eventual role-hinge transition data | Non-rigid same/opposite connector geometry | `EventualRoleHingeClosure`, `RoleHingeCandidateSearchSurface` | Supplies the large closed-placement source. |
| Eventual period data | Orientation words and closure equations | `PeriodSearchInterface`, `EventualPeriodSearchData` | Gives generated-chain closure. |
| Eventual cross-block metric data | Reduced non-connector square-distance lower bounds | `GeneratedSeparationFarApart`, `EventualCrossBlockMetricData` | Gives global separation for the large route. |

Useful closure:

```text
AlternativeNonRigidClosedPlacementW34.
  largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix
```

## Blocked Pach--Toth Fields

The exact-base direct-flexible all-positive lane is not merely unfinished; it
is checked refuted by:

```text
FiniteReducedMetricCandidateSearchW33.not_directFlexibleSourceShape
FlexibleCandidateMetricInhabitationW33.not_nonempty_directFlexibleSourcePayload
DeformedLengthOneSourceW34.not_nonempty_directFlexibleSourcePayload
```

Do not add tasks asking workers to inhabit this payload.  Use the threshold
route above.

## Documentation Rule

If a future file introduces a new final-looking package, it should either:

- directly consume one row in this matrix,
- replace this matrix with a smaller live matrix, or
- be documented as legacy/obstruction-only.

Otherwise it is probably another planning layer rather than progress.
