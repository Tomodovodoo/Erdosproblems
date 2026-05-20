# Current Conditional Spines

This note records the live conditional proof spines for Swanepoel and
Pach--Toth as of 2026-05-19.  It is a context handoff, not a claim that either
record theorem has been completed unconditionally.

The public target names below are internal propositions.  The conditional
wrappers in the final modules are deliberately not exposed through
`KnownBounds.lean`.

## Swanepoel Spine

Target proposition:

```text
ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne
```

Live conditional endpoint:

```text
SwanepoelW32FinalAssembly.W34ActualRoutePremises
```

Checked closure:

```text
W34ActualRoutePremises
  -> SwanepoelW32FinalAssembly.targetLowerBoundEightThirtyOne_of_w34ActualRoutePremises
  -> Swanepoel.targetLowerBoundEightThirtyOne
```

Current strongest source interfaces:

```text
M8ConstructionDataInhabitationW33.StrongestRouteSource
NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure
```

Compact constructor to target first:

```text
SwanepoelW32FinalAssembly.
  w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows
```

Expanded sibling when the long-arc/W16 data is being built directly:

```text
SwanepoelW32FinalAssembly.
  w34ActualRoutePremises_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows
```

Open positive inputs:

1. Exact selected topology rows:
   `SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget`
   or
   `FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget`.
   Current S2 source task: construct an input-only actual exterior boundary
   cycle `B`, prove graph vertices on the unbounded exterior frontier iff they
   are vertices of `B`, and provide `forall k,
   BoundaryVertexExteriorSectorRowsAt inputs B k`; this feeds
   `FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_boundaryVertexExteriorSectorRows`.
   Prove this orbit-first internally: choose an exterior-oriented geometric raw
   face-successor orbit, prove frontier-tail coverage and repeated-tail cut
   rows, then turn no-cut tail injectivity into the boundary cycle and sector
   rows.
2. Nondegenerate outer-face sector order:
   `OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`.
3. Exact topology closure/missing-field package:
   `SelectedTopologyRowsInhabitationW33.ExactActualTopologyClosureMissingFieldPackage`.
4. Finite-walk generated order rows:
   `FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows`.
5. Selected frame realization carrier and K23 route coverage:
   `K23RouteCoverageSourceW34.SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem`.
6. Bad-adjacency/common-neighbor rows:
   `K23RouteCoverageSourceW34.SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem`.
7. Compact S5 angle rows:
   `ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource`.

What this means operationally: new Swanepoel work should inhabit one of these
source rows from minimal-failure data.  Adding another gate, route alias, or
theorem-shaped wrapper is not progress unless it removes one of these open
inputs.

## Pach--Toth Spine

Target propositions:

```text
ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen
ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary
```

Live conditional route:

```text
PachTothRemainingSourceLedgerW34.
  exactAndArbitraryTargets_of_largeClosedPlacementFieldsSix_and_below
```

Large-side handoff:

```text
AlternativeNonRigidClosedPlacementW34.
  largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix
```

Open positive inputs:

1. `PachTothRemainingSourceLedgerW34.LargeClosedPlacementFieldsSix`:
   closed placements from block length six onward.
2. `PachTothRemainingSourceLedgerW34.BelowThresholdMetricFieldsSix`:
   exact small-length metric certificates below the threshold.
3. `SmallLengthExactTargetsConcreteW24.DeformedLengthOneExactBlocksTwoThroughFiveSource`:
   the small deformed length-one source used by the below-threshold package.
4. `PachTothRemainingSourceLedgerW34.MinimalExactRemainderSplitSourceBlocker`:
   the remaining exact-to-arbitrary split input.

Supporting route modules:

- `EventualRoleHingeClosure` and `RoleHingeCandidateSearchSurface` for honest
  non-rigid transition geometry.
- `PeriodSearchInterface` and `EventualPeriodSearchData` for generated chain
  closure.
- `GeneratedSeparationFarApart` and `EventualCrossBlockMetricData` for global
  separation.
- `EventualClosedPlacementSourceW34` and
  `AlternativeNonRigidClosedPlacementW34` for the large threshold route.
- `RemainderSplitSourceClosureW32` for arbitrary-size closure.

Blocked exact-base/direct-flexible lane:

```text
FiniteReducedMetricCandidateSearchW33.not_directFlexibleSourceShape
FlexibleCandidateMetricInhabitationW33.not_nonempty_directFlexibleSourcePayload
DeformedLengthOneSourceW34.not_nonempty_directFlexibleSourcePayload
```

What this means operationally: Pach--Toth work should not try to revive a
translated or exact-base all-positive direct-flexible payload.  The live work
is threshold/eventual and non-rigid: prove the large route, fill small
certificates, and close the remainder split.

## Trust Status

Both spines are conditional Lean closures around explicit source packages.
They intentionally keep the remaining geometric, finite-search, and
quantitative certificate obligations visible.  They do not assert final
unconditional completion of Swanepoel's `8 / 31` bound or Pach--Toth's
`5 / 16` construction.
