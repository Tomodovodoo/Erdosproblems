# Remaining explicit fields matrix

This is a compact handoff map for the remaining explicit data, not a proof
claim.  "Consumer" means the first Lean facade that projects the field onward;
downstream modules are listed only when they are the reason that field exists.

## Swanepoel `MinimalFailureM8PaperFacts`

Source structure:
`ErdosProblems1066/Swanepoel/MinimalFailureComponentPackage.lean`.

| Field | Meaning | Immediate Lean consumers | Downstream use |
|---|---|---|---|
| `cutVertex.positiveCard` | Nonempty minimal failure | `MinimalFailureCutVertexFacts.connectedDegreeRange`, `MinimalFailureCutVertexFacts.connectedNoCutDegreeRange` in `Swanepoel.MinimalFailureComponentPackage` | `Swanepoel.CutVertexFinal`, then boundary-label context |
| `cutVertex.remainingSlack` | Remaining no-cut/cut-vertex slack | `MinimalFailureCutVertexFacts.connectedNoCutDegreeRange`, `preconnectedNoCut` | `Swanepoel.CutVertexFinal`, `Swanepoel.M8BoundaryLabelsConcrete` |
| `planarBoundary` | Full planar-boundary package for the canonical graph | `concreteFaceCountingData`, `faceCountingTheorems`, `boundaryLabels`, `toM8SeparatedConstructionComponentPackage` | `Swanepoel.PlanarBoundaryFinal`, `Swanepoel.PlanarBoundaryClosure`, `Swanepoel.M8BoundaryLabelsConcrete` |
| `spine` | Boundary spine in the no-cut/minimal-failure context | `boundaryLabels`, `localLabels`, `toM8ConstructionData` | `Swanepoel.M8BoundaryLabelsConcrete`, `Swanepoel.BoundaryLabelExtractionTasks` |
| `lemma8` | Lemma 8 boundary-label combinatorics for `spine` | `boundaryLabels`, `localLabels`, `toM8ConstructionData` | `Swanepoel.Lemma8CombinatoricsConcrete`, `Swanepoel.M8BoundaryLabelsConcrete` |
| `arc` | Nonconcave arc turn data | `turnBounds`, `toM8SeparatedConstructionComponentPackage` | `Swanepoel.M8TurnBoundsConcrete`, `Swanepoel.M8TurnBoundsFromArc`, `Swanepoel.M8PipelineClosure` |
| `noEarlyTriples` | Lemma 9/no-early-triples input for derived labels | `lateTriples`, `toM8SeparatedConstructionComponentPackage` | `Swanepoel.M8LateTriplesConcrete`, `Swanepoel.M8LateTriplesFromNoEarly`, `Swanepoel.M8PipelineClosure` |
| `windowContainment` | Figure 8/Figure 9 containment witnesses for labels and turns | `windowGeometry`, `toM8SeparatedConstructionComponentPackage` | `Swanepoel.M8WindowGeometryConcrete`, `Swanepoel.M8WindowGeometryFromContainment`, `Swanepoel.Lemma10WindowGeometry` |
| `MinimalFailureM8PaperFactsFamily.facts` | Uniform supplier for every minimal cleared failure | `toSeparatedConstructionComponents`, `no_minimalClearedFailure`, `targetLowerBoundEightThirtyOne` | `Swanepoel.M8SeparatedConstructionConcrete`, `Swanepoel.MinimalFailureClosure`, final Swanepoel target |

## Pach--Toth non-rigid role-hinge/cross-block route

Preferred non-vacuous route modules:
`PachToth.NonRigidClosedPlacementInterface`,
`PachToth.RoleHingeTransitionSearch`,
`PachToth.ConcretePeriodSearchFamily`, and
`PachToth.CrossBlockLowerBoundsInterface`.

| Field package | Remaining explicit fields | Immediate Lean consumers | Downstream use |
|---|---|---|---|
| `ExplicitCyclicPointEdgeData k hk` | `point`, `separated`, `same_block_edges_unit`, `cross_connector_edges_unit` | `toExplicitClosedPlacementCertificate`, `toClosedPlacement` in `PachToth.NonRigidClosedPlacementInterface` | `PachToth.ClosedPlacementInterface`, `PachToth.DeformedPlacement`, exact and arbitrary targets via remainder bridge |
| `ExplicitCyclicOrbitEdgeData k hk` | `point`, `step`, `successor_eq`, `connector_unit_edges`, `separated`, `same_block_edges_unit` | `toSuccessorCompatibleCyclicPointOrbit`, `toExplicitTransitionClosedPlacementCertificate`, `toClosedPlacement` | `PachToth.ClosedChainExistence`, `PachToth.ClosedPlacementAlgebra`, `PachToth.DeformedPlacement` |
| `SameOppositeCyclicOrbitData O k hk` | `point`, `orientation`, `successor_eq`, `separated`, `same_block_edges_unit` | `toExplicitTransitionClosedPlacementCertificate`, `toClosedPlacement` | `PachToth.ClosedChainConstruction`, `PachToth.ClosedPlacementAlgebra`, non-rigid target wrappers |
| `RoleHingeTransitionFacts` | `placeNext`, `roleAngle`, `realizes_role`, `preserves_same_block_distances` | `toRoleHingeTransition`, `connector_unit_edges`, `toTransitionMetricObligations` in `PachToth.RoleHingeTransitionSearch` | `PachToth.HingedTransitionInterface`, `PachToth.BaseTransitionRealization`, `PachToth.GeneratedMetricClosure` |
| `SameOppositeRoleHingeTransitionFacts` | `same`, `opposite` role-hinged transition facts | `toRoleHingeTransitions`, `toMetricObligations`, `toFigure2TransitionObligations` | `PachToth.GeneratedMetricClosure`, `PachToth.GeneratedSeparationInterface` |
| `GeneratedClosureSearchData k hk` | `transitions`, `orientation`, `closure`, `separated` | `toRoleHingedGeneratedClosureData`, `toGeneratedReducedMetricHypotheses` | `PachToth.GeneratedMetricClosure`, `PachToth.ClosedPlacementInterface` |
| `GeneratedClosureSearchFamily` | uniform `transitions`, `orientation`, `closure`, `separated` for every positive `k` | `toRoleHingedGeneratedClosureFamily`, `closedPlacementFamily`, `targetUpperConstructionFiveSixteen` | Exact-multiple Pach--Toth target through `PachToth.GeneratedMetricClosure` |
| `PeriodSearchData` | `transitions`, finite orientation `word k hk`, indexed algebraic `equation k hk i` | `indexedCertificate`, `closure`, `periodEquation`, `toRoleHingedPeriodSearchFamily` in `PachToth.ConcretePeriodSearchFamily` | `PachToth.PeriodSearchInterface`, `PachToth.PeriodCertificateExamples`, `PachToth.CrossBlockLowerBoundsInterface` |
| `ConcreteCrossBlockFamily` | `periodSearch`, `lower`, `lower_ge_one`, `lower_bound` | `toCrossBlockLowerBounds`, `separated`, `toRoleHingedGeneratedClosureFamily` | `PachToth.GeneratedSeparationFarApart`, `PachToth.ExactFamilyClosure`, exact and arbitrary targets |
| `IndexedCrossBlockLowerTable F k hk` | finite-index `lower`, `lower_ge_one`, `lower_bound` over `Fin k x Fin 16` | `toLocalLower`, `toLocalLower_ge_one`, `toLocalLower_bound`, `generatedGlobalSeparation` | `PachToth.CrossBlockLowerBoundsInterface`, then generated separation |
| `IndexedCrossBlockLowerTableFamily F` | `table k hk` for every positive `k` | `CrossBlockLowerBounds.ofIndexedTables` | `PachToth.CrossBlockLowerBoundsInterface.CrossBlockLowerBounds` |
| `CrossBlockLowerBounds F` | local-vertex `lower`, pointwise `lower_ge_one`, metric `lower_bound` | `toLowerBoundsAtLeastOne`, `toDistanceLowerBounds`, `separated`, `toExactFamilyClosure` | `PachToth.GeneratedSeparationFarApart`, `PachToth.ExactFamilyClosure`, `PachToth.CrossBlockLowerBoundsInterface.targetUpperConstructionFiveSixteen*` |

Guardrail: the audited `PachToth.FinalConditional.EquationPeriodSearchCrossBlockFamily`
is the translated-equation closure route.  The non-vacuous route above should
feed role-hinged/deformed transition data into period certificates and
cross-block lower tables, not instantiate the contradictory translated
connector-equation package.
