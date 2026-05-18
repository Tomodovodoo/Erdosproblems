# Global Task Tracker

This is the living completion plan for the Lean formalization of Erdos problem
1066.  Keep it as an executable checklist: every open item names the current
state, the exact Lean target, and the next action needed to mark it off.

Ground rule: mark a task `DONE` only after the relevant Lean declarations are
imported by `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, compile
with the pinned toolchain, and pass the forbidden-token scan.  Conditional
bridges are progress, but they are not final theorem completion until their
hypotheses are discharged.

Every unchecked task below is meant to be a subagent-sized work unit.  A task
should name:

- Paper step: the source-paper claim it implements, such as Swanepoel `E14`
  or Pach--Toth `GEO.3`.
- Lean route: the existing files/declarations that consume the result.
- Deliverable: the exact theorem, structure field, or package to construct.
- Completion gate: the imported Lean declaration builds with the pinned
  toolchain and the forbidden-token scan is clean.

If a task cannot be completed by one focused proof agent, split it before
starting.  Do not mark an interface or conditional facade as done for the
paper theorem until its concrete input fields have been supplied.

Target skeletons below are proof-agent contracts, not source code to paste
unchanged into the Lean tree.  They may use `:= by sorry` to mark the intended
statement while the task is open.  A task is complete only when the real Lean
declaration has replaced that placeholder, is imported by
`E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, builds with the pinned
toolchain, and the Lean-source forbidden-token scan is still clean.

Verification command:

```powershell
Set-Location 'E:/Personal/Erdosproblems/1066'
elan run leanprover/lean4:v4.28.0 lake build
```

PowerShell-safe source scan:

```powershell
Set-Location 'E:/Personal/Erdosproblems/1066'
rg -n -i -e '\baxiom\b' -e '\bconstant\b' -e '\bsorry\b' -e '\badmit\b' `
  -e 'unsafe' -e 'opaque' -e 'implemented_by' -e '#check' -e '#print' `
  -e '#eval' ./ErdosProblems1066 ./ErdosProblems1066.lean --glob '*.lean'
if ($LASTEXITCODE -eq 1) { 'clean' } elseif ($LASTEXITCODE -ne 0) { exit $LASTEXITCODE }
```

Last verification recorded in this file:

```text
elan run leanprover/lean4:v4.28.0 lake build
Build completed successfully (8240 jobs).

Lean source forbidden-token scan over ErdosProblems1066/ and
ErdosProblems1066.lean: clean.

Root import coverage: 213 imported modules for 213 Lean files under
ErdosProblems1066/.

CI-style axiom audit: passed for 374 declarations; every checked declaration
reports only Lean/mathlib base axioms `propext`, `Classical.choice`, and
`Quot.sound`.

Encoding scan for common mojibake markers in Lean files: clean.
```

## Current Certified State

- [x] The imported project builds through the pinned Lean toolchain.
  - Root import file: `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`.
  - Current root imports include every Lean source module under
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/`.
  - Recent non-rigid Pach--Toth route modules imported:
    `PachToth.NonRigidClosedPlacementInterface`,
    `PachToth.RoleHingeTransitionSearch`,
    `PachToth.RoleHingeConnectorAlgebra`,
    `PachToth.RoleHingeAngleCertificates`,
    `PachToth.RoleHingeSameBlockAlgebra`,
    `PachToth.RoleHingeFiniteFamilyBridge`,
    `PachToth.RoleHingeConcreteSearch`,
    `PachToth.RoleHingeInterfaceRefinement`,
    `PachToth.IndexedCrossBlockTableConcrete`,
    `PachToth.CrossBlockDistanceSqReduction`,
    `PachToth.CrossBlockSqTableSearch`,
    `PachToth.CrossBlockUpperTriangleConcrete`,
    `PachToth.CrossBlockPolynomialNormalization`,
    `PachToth.NonRigidConnectorSeparationFacts`,
    `PachToth.ClosedPlacementNonRigidComponents`,
    `PachToth.ClosedPlacementComponentsAssembly`,
    `PachToth.SplitArbitraryNNonRigidBridge`,
    `PachToth.PeriodWordCertificates`,
    `PachToth.PeriodEquationConcreteSearch`,
    `PachToth.ConcretePeriodCandidateSearch`,
    `PachToth.EventualRoleHingeClosure`, and
    `PachToth.ExactFiveSixteenRouteMatrix`.
  - Recent Swanepoel M8 assembly modules imported:
    `Swanepoel.M8ConstructionDataBridge`,
    `Swanepoel.MinimalFailureComponentPackage`,
    `Swanepoel.MinimalFailureFactsFamilyConcrete`,
    `Swanepoel.M8PaperFactsAssemblyRefined`,
    `Swanepoel.MinimalFailurePaperFactMatrix`,
    `Swanepoel.M8TurnWindowNoEarlyFinal`,
    `Swanepoel.BoundaryFaceCountingToM8`,
    `Swanepoel.BoundaryLabelExtractionTasks`,
    `Swanepoel.BoundarySpineConcrete`,
    `Swanepoel.BoundaryLabelCertificateAssembly`,
    `Swanepoel.CutVertexSlackFromDeletion`,
    `Swanepoel.CutVertexPayForCutArithmetic`,
    `Swanepoel.CutVertexSideCardFromMinimality`,
    `Swanepoel.JordanBoundaryExtraction`,
    `Swanepoel.JordanBoundaryConcrete`,
    `Swanepoel.JordanTopologyFactsConcrete`,
    `Swanepoel.Lemma8CombinatoricsConcrete`,
    `Swanepoel.Lemma8NeighborExtractionConcrete`,
    `Swanepoel.Lemma8ExistenceConcrete`,
    `Swanepoel.Lemma8CyclicOrderConcrete`,
    `Swanepoel.Lemma8DegreeSixConcrete`,
    `Swanepoel.Lemma8ForbiddenDistinctConcrete`,
    `Swanepoel.BoundarySpineFiniteCertificate`,
    `Swanepoel.NonconcaveArcConcrete`,
    `Swanepoel.NonconcaveArcAngleFacts`,
    `Swanepoel.NonconcaveArcBudgetFromBoundary`,
    `Swanepoel.NoEarlyTripleFromLemma9`,
    `Swanepoel.NoEarlyTripleObstructionConcrete`,
    `Swanepoel.Figure8ContainmentConcrete`,
    `Swanepoel.Figure8EuclideanFactsConcrete`,
    `Swanepoel.Figure8ContainmentAngleBudget`,
    `Swanepoel.Figure9ContainmentConcrete`,
    `Swanepoel.Figure9EuclideanFactsConcrete`,
    `Swanepoel.Figure9ContainmentAngleBudget`, and
    `Swanepoel.PlanarBoundaryFaceDataRefinement`.
  - Current root target build succeeds and root import coverage is complete:
    213 imported package modules for 213 Lean files under
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/`.

- [x] Third parallel proof wave is integrated.
  - Pach--Toth workers P1--P10 own:
    `RoleHingeConcreteSearch.lean`, `ConcretePeriodSearchFamily.lean`,
    `CrossBlockSqTableSearch.lean`, `FiniteCertificateObligationSummary.lean`,
    `ExactFiveSixteenRouteMatrix.lean`, `GeneratedSeparationFarApart.lean`,
    `SplitRealizationFinal.lean`, `NonRigidClosedPlacementInterface.lean`,
    `ClosedPlacementComponentsAssembly.lean`, and
    `SmallCaseCertificates.lean`.
  - Swanepoel workers S1--S10 own:
    `CutVertexSideCardFromMinimality.lean`, `JordanTopologyFactsConcrete.lean`,
    `PlanarBoundaryFaceDataRefinement.lean`,
    `BoundaryLabelCertificateAssembly.lean`, `Lemma8ExistenceConcrete.lean`,
    `Lemma8NeighborExtractionConcrete.lean`, `Lemma8CombinatoricsConcrete.lean`,
    `NoEarlyTripleObstructionConcrete.lean`,
    `NonconcaveArcBudgetFromBoundary.lean`,
    `M8WindowGeometryFromContainment.lean`,
    `M8MinimalFailureEliminatorInterface.lean`, and
    `M8PipelineClosure.lean`.
  - Completion gate passed: all 20 workers were closed only after completion,
    every changed file received a targeted pinned Lean check and source scan,
    and the root build, source scan, coverage scan, encoding scan, and
    CI-style axiom audit passed.

- [ ] Fourth parallel proof wave is active.
  - Pach--Toth workers P11--P20 own:
    `RoleHingeInterfaceRefinement.lean`, `GeneratedMetricClosure.lean`,
    `FiniteSearchCertificate.lean`, `CrossBlockPolynomialNormalization.lean`,
    `ConcretePeriodCandidateSearch.lean`, `FinalConditional.lean`,
    `EventualRoleHingeClosure.lean`, `NonRigidConnectorSeparationFacts.lean`,
    `GeneratedPeriodClosure.lean`, and `ExactFiveSixteenRouteMatrix.lean`.
  - Swanepoel workers S11--S20 own:
    `CutVertexSlackFromDeletion.lean`, `JordanBoundaryConcrete.lean`,
    `BoundaryWalkConstruction.lean`, `SubpolygonAssembly.lean`,
    `OuterBoundaryAngleClosure.lean`, `NonconcaveArcConcrete.lean`,
    `Figure8EuclideanFactsConcrete.lean`,
    `Figure9EuclideanFactsConcrete.lean`, `M8TurnWindowNoEarlyFinal.lean`,
    and `MinimalFailurePaperFactMatrix.lean`.
  - Completion gate: close only completed workers, run targeted pinned checks
    and scans for their files, then rerun root build, source scan, coverage,
    encoding, and CI-style axiom audit before marking the wave integrated.

- [x] Import and scan the current-wave interface modules.
  - Current-wave modules now covered by the root import:
    `PachToth.ConnectorEquationClosure`,
    `PachToth.ExactFamilyClosure`,
    `PachToth.GeneratedSeparationFarApart`,
    `PachToth.OrientationWord`,
    `Swanepoel.SubpolygonAssembly`,
    `Swanepoel.BoundaryWalkConstruction`,
    `PachToth.EquationTransitionClosure`,
    `PachToth.CrossBlockLowerBoundsInterface`,
    `PachToth.PeriodCertificateExamples`,
    `PachToth.FinalConditional`,
    `Swanepoel.CutVertexFromConnectedness`,
    `Swanepoel.M8LabelsFromBoundaryInterface`,
    `Swanepoel.M8LateTriplesFromNoEarly`,
    `Swanepoel.M8MinimalFailureEliminatorInterface`,
    `Swanepoel.M8TurnBoundsFromArc`,
    `Swanepoel.M8WindowGeometryFromContainment`,
    `Swanepoel.PlanarBoundaryClosure`,
    `PachToth.RoleHingeConnectorAlgebra`,
    `PachToth.RoleHingeAngleCertificates`,
    `PachToth.RoleHingeSameBlockAlgebra`,
    `PachToth.RoleHingeFiniteFamilyBridge`,
    `PachToth.RoleHingeConcreteSearch`,
    `PachToth.RoleHingeInterfaceRefinement`,
    `PachToth.CrossBlockSqTableSearch`,
    `PachToth.CrossBlockUpperTriangleConcrete`,
    `PachToth.CrossBlockPolynomialNormalization`,
    `PachToth.NonRigidConnectorSeparationFacts`,
    `PachToth.PeriodEquationConcreteSearch`,
    `PachToth.ConcretePeriodCandidateSearch`,
    `PachToth.EventualRoleHingeClosure`,
    `PachToth.SplitArbitraryNNonRigidBridge`,
    `PachToth.ClosedPlacementComponentsAssembly`,
    `PachToth.ExactFiveSixteenRouteMatrix`,
    `PachToth.FiniteCertificateObligationSummary`,
    `Swanepoel.BoundarySpineConcrete`,
    `Swanepoel.BoundarySpineFiniteCertificate`,
    `Swanepoel.BoundaryLabelCertificateAssembly`,
    `Swanepoel.JordanBoundaryConcrete`,
    `Swanepoel.JordanTopologyFactsConcrete`,
    `Swanepoel.NonconcaveArcConcrete`,
    `Swanepoel.NonconcaveArcAngleFacts`,
    `Swanepoel.NonconcaveArcBudgetFromBoundary`,
    `Swanepoel.NoEarlyTripleFromLemma9`,
    `Swanepoel.NoEarlyTripleObstructionConcrete`,
    `Swanepoel.MinimalFailureFactsFamilyConcrete`,
    `Swanepoel.M8PaperFactsAssemblyRefined`,
    `Swanepoel.MinimalFailurePaperFactMatrix`,
    `Swanepoel.CutVertexPayForCutArithmetic`,
    `Swanepoel.CutVertexSideCardFromMinimality`,
    `Swanepoel.Lemma8NeighborExtractionConcrete`,
    `Swanepoel.Lemma8ExistenceConcrete`,
    `Swanepoel.Lemma8CyclicOrderConcrete`,
    `Swanepoel.Lemma8DegreeSixConcrete`,
    `Swanepoel.Lemma8ForbiddenDistinctConcrete`,
    `Swanepoel.Figure8ContainmentConcrete`,
    `Swanepoel.Figure8EuclideanFactsConcrete`,
    `Swanepoel.Figure8ContainmentAngleBudget`,
    `Swanepoel.Figure9ContainmentConcrete`,
    `Swanepoel.Figure9EuclideanFactsConcrete`, and
    `Swanepoel.FinalConditional`.
  - Current scan status: the full-tree forbidden-token scan is clean.

- [x] Record the Pach--Toth translated-equation obstruction.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/TranslatedEquationObstruction.lean`.
  - Current state: the four-equation translated connector route is formally
    uninhabited.  Treat equation-carried final facades as audit/obstruction
    material, not as the live constructive proof path.
  - Live Pach--Toth path: non-rigid/role-hinged transition data, explicit
    period words/equations, and indexed cross-block lower tables.

- [x] `TurnBoundsInterface.lean` is imported and build-checked.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/TurnBoundsInterface.lean`.
  - Current state: imported by the root file, included in the successful
    pinned build, and scan-clean.

- [x] `LocalDeletionConstructors.lean` is integrated and build-checked.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/LocalDeletionConstructors.lean`.
  - Current state: imported by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`; standalone
    `lake env lean` check passes; pinned `lake build` builds it.
  - New helper:
    `localClosedNeighborhoodDeletionEliminator_of_exists_localClosedNeighborhoodDeletion`
    turns tupled `deleted`/`reinsertion` data plus the five local facts into
    the structure-valued eliminator.
  - New direct local-deletion facts:
    `MinimalFailureLocalExclusions.LocalClosedNeighborhoodDeletion.induced_card_lt_original`,
    `hasCleared_of_minimalFailure`, and `false_of_minimalFailure`.
    These get the strict smaller induced configuration directly from local
    deletion data before attaching the smaller independent set.
  - Current downstream status: S2 now has the singleton-safe deletion
    certificate route and the deficient-neighborhood contradiction in
    `Swanepoel/DeficientNeighborhood.lean`.  This file remains conditional
    plumbing; the actual local inequality is certified separately.

- [x] Public facade currently exposes only completed legacy bounds.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/KnownBounds.lean`.
  - Current public theorems: `Verified.upper_bound_third`,
    `Verified.lower_bound_quarter`, and `PollackPach.lower_bound_quarter`.
  - Do not expose Swanepoel `8 / 31` or Pach-Toth `5 / 16` until the final
    checklists below are complete.

- [ ] Keep file hygiene clear.
  - Ignored stale generated output:
    `E:/Personal/Erdosproblems/1066/Aristotle/ARISTOTLE_SUMMARY.md`.
  - Ignored build cache: `E:/Personal/Erdosproblems/1066/.lake/`.
  - These do not affect Lean builds.  Do not use them as evidence of current
    proof state.
  - Next action: do not create audit/output files while proving tasks.  If file
    hygiene is cleaned later, remove stale ignored/generated files separately
    from proof edits.

## Swanepoel 8 / 31 Overview

Final target:

```lean
-- E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Bridge.lean
def targetLowerBoundEightThirtyOne : Prop :=
  forall (n : Nat) (C : UDConfig n),
    exists s : Finset (Fin n), C.IsIndep s /\ 31 * s.card >= 8 * n
```

Current checked reduction:

```lean
-- E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/TargetReduction.lean
theorem targetLowerBoundEightThirtyOne_of_pipelineCleared :
  (forall (n : Nat) (C : UDConfig n),
    CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C) ->
  targetLowerBoundEightThirtyOne
```

Current real status: the algebraic and conditional spine is good, but the
paper bridge is still missing.  Swanepoel is not one small theorem away unless
that theorem is treated as a large mega-construction containing E5 through E23.

Paper-to-Lean route:

| Paper step | Strategy in the paper | Lean route / current consumer |
|---|---|---|
| `E5` | Lemma 1, in the M8-needed form: every nonempty independent `S` with `S.card <= 8` has at least `3 * S.card` outside neighbours | S2, `SmallIndependentNeighborhood`, `MinimalFailureLocalExclusions`, `DeficientNeighborhood` |
| `E6` | Lemma 2: minimum degree at least `3` | S3, `MinimumDegree.unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure` |
| `E7` | Lemma 3: connected and no cut vertex | S3, `MinimalConnectednessClosure`, then `CutVertexFinal.RemainingNoCutSlackFact` |
| `E8-E10` | outer boundary and boundary bookkeeping | S4, `JordanTopologyFactsConcrete.TopologyFacts`, `JordanBoundaryConcrete.MissingTopologyFacts`, `PlanarBoundaryClosure.PlanarBoundaryData` |
| `E11` | source-faithful boundary arc bookkeeping that feeds the boundary labels | S4, boundary cycle/classification data, `BoundaryFaceCountingToM8`, `BoundaryLabelExtractionTasks` |
| `E12-E13` | boundary and subpolygon angle/count inequalities | S5, `BoundaryAngleRealization.OuterBoundaryAngleRealization.angleLowerBound`, `SubpolygonAssembly.SubpolygonCycleCountAngleData.lowDegreeInequality`, `SubpolygonAssembly.e13LowDegreeInequality_of_explicitCycleCountAngleData` |
| `E14-E16` | Lemmas 6, 7, 5: long nonconcave arc | S6, current Lean has reducers/adapters; the remaining proof must construct `NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts` |
| `E17` | `m = 8` thirteen-turn specialization of the long-arc data | S6, `NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts` to `M8TurnBoundsFromArc.NonconcaveArcTurnData` |
| `E18-E19` | Lemma 8 labels and Lemma 9 late triples | S6/S8, `M8FinitePQSpineCertificate`, `M8Lemma8MissingExistenceConditions`, `M8Lemma9FiveStartLateFacts` |
| `E21-E23` | Euclidean Lemma 10 and Figure 8/Figure 9 inequalities | S7, `AngleContainmentBridges`, `M8WindowContainment` |
| `E24` | `m = 8` contradiction and lower-bound target | S8, `MinimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne` |

Current source-refined paper package:

```lean
M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily
```

This is the cleanest paper-facing checklist.  The smallest Lean-efficient
conditional gate below it is:

```lean
M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator
```

The source-refined package closes the target through:

```text
MinimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne
-> MinimalFailureM8RemainingPaperFactsFamily.targetLowerBoundEightThirtyOne
-> MinimalFailureM8PaperFactsFamily.targetLowerBoundEightThirtyOne
-> Swanepoel.targetLowerBoundEightThirtyOne
```

The Lean-efficient separated-construction gate closes through:

```text
M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator
-> M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator
-> MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
-> Swanepoel.targetLowerBoundEightThirtyOne
```

The remaining fields to construct for each minimal cleared failure are exactly
`positiveCard`, `remainingNoCutSlack`, `planarBoundary`, `spineCertificate`,
`lemma8Existence`, `arcAngleFacts`, `lemma9FiveStartLateFacts`, and
`angleContainment`.

### Swanepoel Already Checked

- [x] `UDConfig` to Mathlib `SimpleGraph` bridge.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/GraphBridge.lean`.
  - Current declarations include `unitDistanceSimpleGraph`,
    `unitDistanceSimpleGraph_adj`, `unitDistanceSimpleGraph_adj_iff_ne_and_dist`,
    and `isIndep_iff_simpleGraph_isIndepSet`.

- [x] Induced subconfiguration machinery.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/InducedSubconfiguration.lean`.
  - Current declarations include `Induced`, `preservesDistancesOn`,
    `image_indep_iff`, and `ofFinset`.

- [x] Degree upper bound `<= 6`.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/DegreeBound.lean`.
  - Checked declaration: `UDConfig.unitDistanceNeighborSet_card_le_six`.

- [x] Noncrossing unit edges.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoncrossingUnitEdges.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/FaceReduction.lean`.
  - Checked declaration: `FaceReduction.unitDistanceEdges_pairwiseNoncrossing`.

- [x] Conditional deletion/reinsertion arithmetic.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalCounterexample.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CounterexamplePipeline.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/DegreePipeline.lean`.

- [x] Common-neighbor and labelled `K_{2,3}` cap for unit-distance configs.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CommonNeighborGeometry.lean`.
  - Current state: this cap no longer needs a separate `K23DegreeReducible`
    assumption.

- [x] Boundary-count and subpolygon-count algebra from explicit angle bounds.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryCounting.lean`.
  - Current declarations:
    `BoundaryCounts.boundary_angle_count_inequality` and
    `SubpolygonDegreeCounts.subpolygon_low_degree_inequality`.

- [x] Lemma 10 finite contradiction from supplied E22/E23.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10Bridge.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10AnalyticBridge.lean`.
  - Use `honestContradiction_of_E22_E23` for the final honest package.
    The lower-level `contradiction_of_E22_E23` also exists, but it needs an
    explicit raw `htriple`.

- [x] Euclidean angle and Lemma 10 window arithmetic interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/TriangleAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/AngleGeometry.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/AngleArithmetic.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10EuclideanBridge.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10Pipeline.lean`.
  - Current state: imported, build-checked, and scan-clean.  These files route
    explicit squared-distance/unit-angle facts and weighted turn-window
    inequalities into the existing Lemma 10 E22/E23 contradiction machinery.
  - Conditional status: the paper-specific Figure 8/Figure 9 distance data and
    turn-window containment still have to be extracted from the boundary
    construction.

- [x] Minimal-failure closure, conditional on no minimal failure.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureClosure.lean`.
  - Current declarations include `hasCleared_of_no_minimalClearedFailure` and
    `targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure`.

### Swanepoel Completion Checklist

#### S1. Integrate the local deletion constructor layer

- [x] Fix and import `LocalDeletionConstructors.lean`.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/LocalDeletionConstructors.lean`.
  - Why: it is useful conditional plumbing above
    `MinimalFailureLocalExclusions`.
  - Current state: root import coverage includes it and pinned build succeeds.
  - Next task: use this layer only after S2 supplies the actual eliminator
    hypothesis from honest local deletion data.

- [x] Add direct-card-bound local deletion interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/LocalDeletionWithCardBound.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/LocalDeletionEliminatorWithCardBound.lean`.
  - Current state: imported, build-checked, and scan-clean.  The checked layer
    packages `LocalDeletionData`, routes it to a local deletion certificate,
    and provides conditional eliminators such as
    `targetLowerBoundEightThirtyOne_of_directCardBoundCertificateEliminator`.
  - Conditional status: these are not final Swanepoel completion theorems; the
    direct-card-bound deletion data still has to be supplied in honest cases.

#### S2. Prove Lemma 1 / small independent neighborhoods

- [x] Add canonical multi-center closed neighborhoods.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SmallIndependentNeighborhood.lean`.
  - Checked declarations:

```lean
noncomputable def closedNeighborhoodOf
    {n : Nat} (C : UDConfig n) (S : Finset (Fin n)) : Finset (Fin n)

noncomputable def outsideNeighborhoodOf
    {n : Nat} (C : UDConfig n) (S : Finset (Fin n)) : Finset (Fin n)

lemma isClosedNeighborhood_closedNeighborhoodOf :
    IsClosedNeighborhood C S (closedNeighborhoodOf C S)
```

  - Current state: definitions are by finite filters over `Finset.univ`;
    membership lemmas, `isClosedNeighborhood_closedNeighborhoodOf`,
    `disjoint_outsideNeighborhoodOf`, `closedNeighborhoodOf_eq_union`,
    `closedNeighborhoodOf_card_eq_add_outsideNeighborhoodOf_card`, and the
    deletion-cardinality bridges are imported, build-checked, and audited.

- [x] Add a general local deletion certificate that works for singleton
  reinsertion.
  - Best home:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureLocalExclusions.lean`.
  - Why: the older `DegreeLocalDeletionCertificate` is degree-specific and
    assumes `2 <= reinsertion.card`; paper Lemma 1 needs singleton cases.
  - Checked shape:

```lean
structure LocalDeletionCertificate
    {n nSmall : Nat} (C : UDConfig n) (Csmall : UDConfig nSmall) where
  kept : Fin nSmall -> Fin n
  deleted : Finset (Fin n)
  reinsertion : Finset (Fin n)
  keptInjective : Function.Injective kept
  keptDeletedDisjoint :
    Disjoint ((Finset.univ.image kept) : Finset (Fin n)) deleted
  cover : ((Finset.univ.image kept) : Finset (Fin n)) ∪ deleted = Finset.univ
  closedNeighborhood : IsClosedNeighborhood C reinsertion deleted
  deletedCard : (deleted.card : Int) <= 4 * (reinsertion.card : Int) - 1
  reinsertionNonempty : reinsertion.Nonempty
  reinsertionCardUpper : reinsertion.card <= 8
  reinsertionIndep : C.IsIndep reinsertion
  preservesDistances :
    forall small : Finset (Fin nSmall),
      PreservesDistancesOn Csmall C kept small
```

  - Current checked declarations include
    `LocalDeletionCertificate.data`,
    `LocalDeletionCertificate.hypotheses`,
    `LocalDeletionCertificate.hasCleared_of_minimalFailure`,
    `LocalDeletionCertificate.false_of_minimalFailure`, and
    `LocalDeletionCertificate.not_nonempty_localDeletionCertificate_of_minimalFailure`.
  - Current downstream status: canonical data is now packaged by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/DeficientNeighborhood.lean`.
    The general certificate layer is no longer an S2 blocker.

- [x] Prove the deficient-neighborhood contradiction.
  - Checked declarations:

```lean
theorem canonicalDeletion_satisfies_directLocalDeletionInputs

theorem exists_localDeletionCertificate_of_deficientNeighborhood

theorem outsideNeighborhood_card_ge_three_mul_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    {S : Finset (Fin n)}
    (hSnonempty : S.Nonempty)
    (hSindep : C.IsIndep S)
    (hScard : S.card <= 8) :
    3 * S.card <= (outsideNeighborhoodOf C S).card
```

  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/DeficientNeighborhood.lean`.
  - Current state: imported, build-checked, and audited.  The proof deletes
    `closedNeighborhoodOf C S`, packages the kept side via
    `InducedSubconfiguration.ofFinset`, converts a deficient outside
    neighborhood into a `LocalDeletionCertificate`, and contradicts minimality.

#### S3. Derive graph structure from minimal failure

- [x] Prove minimum degree `>= 3`.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SingletonNeighborhood.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimumDegree.lean`.
  - Checked declarations:

```lean
theorem closedNeighborhoodOf_singleton_eq_closedUnitNeighborhood

theorem outsideNeighborhoodOf_singleton_eq_unitDistanceNeighborSet

theorem unitDistanceNeighborSet_card_ge_three_of_minimalClearedFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (v : Fin n) :
    3 <= (DegreePipeline.unitDistanceNeighborSet C v).card
```

  - Current state: imported, build-checked, and audited.  The proof
    specializes the deficient-neighborhood theorem to `S = {v}` and identifies
    the outside neighborhood with `DegreePipeline.unitDistanceNeighborSet`.

- [x] Package the minimal-failure degree range.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureDegreeRange.lean`.
  - Current state: imported, build-checked, and audited.  The theorem
    `unitDistanceNeighborSet_card_between_three_and_six_of_minimalClearedFailure`
    combines the minimum-degree lower bound with
    `DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six`.

- [x] Add structural anticomplete-partition glue.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/ConnectednessSeparator.lean`.
  - Current state: imported, build-checked, and audited.  The structure
    `FinAnticompletePartition` packages a two-side anticomplete partition, and
    `FinAnticompletePartition.hasCleared_of_induced_hasCleared` glues cleared
    independent sets from the induced sides.  The theorem
    `FinAnticompletePartition.contradiction_of_minimalClearedFailure` closes
    the contradiction for any supplied anticomplete partition of a minimal
    cleared failure.  This is honest connectedness plumbing, not yet a theorem
    extracting such a partition from graph disconnectedness.

- [x] Extract disconnectedness separators and close connectedness.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/ConnectednessExtraction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalConnectedness.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/ConnectednessExtractionClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalConnectednessClosure.lean`.
  - Current state: imported, build-checked, and scan-clean.  The extraction
    route converts failure of preconnectedness into a finite anticomplete
    partition, then uses the checked separator contradiction to prove
    `MinimalConnectednessClosure.unitDistanceSimpleGraph_connected_of_minimalClearedFailure`.

- [x] Add cut-vertex interfaces and conditional closure plumbing.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexClosure.lean`.
  - Current state: imported, build-checked, and scan-clean.  The checked layer
    defines `CutVertexPartition`, `NoCutVertex`, `CutVertexSlackGluingData`,
    and the conditional closure theorem
    `CutVertexClosure.noCutVertexCertificate_of_minimalFailure_allCutVertexSlack`.
  - This is not an unconditional no-cut-vertex theorem: it still requires the
    uniform cut-vertex slack package.

- [ ] Construct the remaining cut-vertex slack from minimality.
  - Paper step: Swanepoel `E7`, Lemma 3 two-connectedness/no-cut-vertex
    reduction.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexFromConnectedness.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexFinal.lean`,
    consumed downstream by
    `M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.remainingNoCutSlack`.
  - Correct target shape: `CutVertexFinal.RemainingNoCutSlackFact C` is a
    data-valued alias for `CutVertexClosure.AllCutVertexSlackGluingData C`,
    so the main target should be a `def`, not a `Prop` theorem.

```lean
noncomputable def remainingNoCutSlackFact_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexFinal.RemainingNoCutSlackFact C := by
  sorry
```

  - Exact hard leaf: prove the side-cardinality/slack statement below, then
    route it through the checked deletion reducers.

```lean
theorem cutVertexDeletionSideCardExactFact_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexSlackFromDeletion.CutVertexDeletionSideCardExactFact hmin := by
  sorry

theorem cutVertexDeletionSlackFact_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexSlackFromDeletion.CutVertexDeletionSlackFact C := by
  exact
    CutVertexSlackFromDeletion.deletionSlackFact_of_minimalFailure_sideCardExactFact
      hmin
      (cutVertexDeletionSideCardExactFact_of_minimalFailure hmin)
```

  - How: prove the uniform side-cardinality fact by deleting the two
    cut-vertex sides, gluing the cleared independent sets obtained from the
    induced side configurations, and paying the shared cut vertex with the
    existing `CutVertexPayForCutArithmetic` lemmas.  Be careful with the
    existing `CutVertexSideCardFromMinimality` facts: they also show that an
    actual cut partition plus the universal side-cardinality fact contradicts
    minimality, so the proof must derive no-cut by contradiction rather than
    asserting the side-cardinality fact under an already-supplied cut
    partition without closing the contradiction.
  - Completion gate: use this theorem to fill the `remainingNoCutSlack` field
    in the refined M8 paper-facts package for every minimal cleared failure.

- [x] Add connectedness-plus-conditional cut-vertex closure adapter.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexFromConnectedness.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    axiom audit.  It combines checked connectedness extraction, the
    conditional all-cut-vertex slack package, and the minimal-failure degree
    range into `ConnectedNoCutVertexCertificate`.
  - Conditional status: this still does not prove the all-cut-vertex slack
    package from minimality; that is the remaining no-cut payload.

- [x] Add cut-vertex pay-for-cut arithmetic reducer.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexPayForCutArithmetic.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    current root build surface.
  - Conditional status: it is arithmetic/reduction plumbing for the remaining
    cut-vertex slack route; the geometric slack facts still need proof.

#### S4. Build honest outer-boundary and subpolygon data

- [x] Add a lightweight boundary-walk bridge to Mathlib polygons.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryWalkBridge.lean`.
  - Current state: imported, build-checked, and audited.  It exposes
    `BoundaryCycle.toPolygon`, cyclic edge helpers, unit edge-length
    projections, and simple-polygon noncrossing projections.  It deliberately
    does not claim faces, interiors, or Jordan-curve construction.

- [x] Add boundary-walk construction bookkeeping.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryWalkConstruction.lean`.
  - Current state: imported, build-checked, and scan-clean.  It turns supplied
    finite boundary-cycle edge and degree classifications into
    `BoundaryClassification` bookkeeping and projections back to
    `OuterBoundaryCore`.
  - Conditional status: the geometric/Jordan-style boundary cycle and the
    classification evidence are still supplied inputs.

- [x] Add an honest outer-boundary core interface.
  - Existing weak interface:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/FaceReduction.lean`.
  - Existing package interfaces:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/OuterBoundaryInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/OuterBoundaryReduction.lean`.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/OuterBoundaryCore.lean`.
  - Checked structure:

```lean
structure OuterBoundaryCore
    (G : FaceReduction.CanonicalStraightLineUnitDistanceGraph n) where
  faceBoundary : FaceReduction.UnitDistanceFaceBoundaryHypotheses G
  outerFace : faceBoundary.Face
  outerFace_isOuter : faceBoundary.IsOuterFace outerFace
  outerEnclosure :
    OuterBoundaryInterface.OuterBoundaryEnclosure G faceBoundary outerFace
```

  - Current state: imported, build-checked, and scan-clean.  The file exposes
    projections to `OuterBoundaryPackage`,
    `OuterBoundaryReduction.OuterBoundaryConstruction`, and the canonical
    boundary-count hypotheses once explicit count and angle data are supplied.
  - Conditional status: this is an interface/forgetful packaging layer, not a
    construction of an outer face from a minimal cleared failure.

- [ ] Construct the honest topology/outer-boundary package from a minimal
  cleared failure.
  - Paper step: Swanepoel `E8`, boundary polygon exists.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanBoundaryExtraction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanBoundaryConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanTopologyFactsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/OuterBoundaryCore.lean`.
  - Deliverable: for each minimal cleared failure, construct
    `JordanTopologyFactsConcrete.TopologyFacts C` or, if a smaller first step
    is needed, `JordanBoundaryConcrete.MissingTopologyFacts C`.  Project to
    `OuterBoundaryCore` only through `.toCore`; the final consumer wants
    `PlanarBoundaryClosure.PlanarBoundaryData (CanonicalGraph C)`.
  - Target skeleton:

```lean
noncomputable def topologyFacts_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    JordanTopologyFactsConcrete.TopologyFacts C := by
  sorry

noncomputable def outerBoundaryCore_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    OuterBoundaryCore (JordanTopologyFactsConcrete.canonicalGraph C) :=
  (topologyFacts_of_minimalFailure hmin).toCore
```

  - How: start from S3 connected/no-cut data plus
    `FaceReduction.unitDistanceEdges_pairwiseNoncrossing`; use Mathlib
    `SimpleGraph.Walk`, `Walk.IsCycle`, `Polygon`, `Wbtw`, and `Sbtw` only for
    graph/cycle/polygon primitives.  The actual outer-face/Jordan extraction is
    project-local.
  - Completion gate: the constructed core is usable by
    `PlanarBoundaryClosure.PlanarBoundaryData.core`.

- [x] Add boundary classification and bookkeeping interfaces.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryClassification.lean`.
  - Current state: imported, build-checked, and scan-clean.  It defines
    `BoundaryEdgeClass`, `BoundaryDegreeClass`, `BoundaryBookkeeping`,
    `BoundaryCountsRealization`, and projection lemmas into
    `BoundaryCounting.BoundaryCounts`.
  - Conditional status: it computes counts from supplied classification data;
    it does not yet extract those classifications from an actual boundary.

- [ ] Extract actual boundary classifications and counts.
  - Needed data:
    boundary cycle vertices, ambient degrees `3..6`, triangle/nontriangle
    edge classification, unique common-neighbor witnesses on triangle edges,
    long arcs, concave long arcs, and computed `BoundaryCounts`.
  - Paper step: Swanepoel `E9-E10`, boundary edge classification and turn/count
    bookkeeping.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryClassification.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryWalkConstruction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryFaceCountingToM8.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/PlanarBoundaryFaceDataRefinement.lean`.
  - Deliverable: concrete boundary `BoundaryCountsRealization` and the
    boundary-face data needed by `PlanarBoundaryClosure.PlanarBoundaryData`.
  - How: define all counts from the actual boundary cycle, prove the
    classification is exhaustive and nonoverlapping, and project the computed
    counts to the fields consumed by `BoundaryCounting`.
  - Completion gate: `PlanarBoundaryClosure.PlanarBoundaryData.faceCountingTheorems`
    can be obtained from the constructed boundary data.

- [ ] Extract the source-faithful boundary arc bookkeeping used by the M8
  labels.
  - Paper step: Swanepoel `E11`, boundary arcs and label bookkeeping between
    the outer-boundary construction and the later `p_i/q_i` spine.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryFaceCountingToM8.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryLabelExtractionTasks.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundarySpineConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundarySpineFiniteCertificate.lean`.
  - Deliverable: checked boundary-cycle arc data with the exact finite labels
    needed to produce `BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
    planarBoundary`.
  - How: after the S4 topology/count data exists, define the cyclic boundary
    index order, identify the paper's arc endpoints and long-arc markers, and
    prove the projections used by the M8 label extraction modules.
  - Completion gate: the S6 Lemma 8 task can construct its finite spine from
    the honest `PlanarBoundaryClosure.PlanarBoundaryData`, not from abstract
    supplied labels.

- [x] Add outer-boundary assembly adapter.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/OuterBoundaryAssembly.lean`.
  - Current state: imported, build-checked, and scan-clean.  It combines an
    `OuterBoundaryCore`, bookkeeping-realized boundary counts, and a matching
    boundary-angle package into `FaceCountingBridge` count hypotheses.
  - Conditional status: it assembles supplied core/bookkeeping/angle data; it
    does not construct the outer boundary, classifications, or angle package.

- [x] Add concrete subpolygon count and angle-realization interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonCore.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAngleRealization.lean`.
  - Current state: imported, build-checked, and scan-clean.  `SubpolygonCore`
    computes boundary degree counts from a supplied induced vertex set and
    routes `DegreeCountData` to the checked low-degree inequalities.
    `SubpolygonAngleRealization` turns supplied geometric angle comparisons
    into `SubpolygonDegreeCounts.AngleLowerBound`.
  - Conditional status: these files do not construct the geometric subpolygon
    or the angle-sum comparisons.

- [x] Add subpolygon assembly interface.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAssembly.lean`.
  - Current state: imported by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, build-checked,
    and scan-clean.
  - Current purpose: assemble a supplied subpolygon boundary, induced count
    realization, and explicit angle comparisons into the checked E13
    subpolygon counting interfaces.
  - Conditional status: it still requires the supplied subpolygon boundary,
    count realization, and angle comparisons.

- [ ] Construct honest geometric subpolygon packages.
  - Needed data:
    subpolygon boundary cycle, inside/on vertex set, induced subconfiguration,
    induced boundary degrees, computed `SubpolygonDegreeCounts`.
  - Paper step: Swanepoel `E13`, Lemma 4 subpolygon low-degree inequality.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonCore.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAngleRealization.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAssembly.lean`.
  - Deliverable: a reusable honest subpolygon package whose computed
    `SubpolygonDegreeCounts` feeds
    `SubpolygonAssembly.SubpolygonCycleCountAngleData.lowDegreeInequality` and
    `SubpolygonAssembly.e13LowDegreeInequality_of_explicitCycleCountAngleData`.
  - How: define the inside/on vertex set, build the induced configuration,
    compute boundary degrees from the induced graph, and prove the degree range
    hypotheses needed by the existing low-degree inequality.
  - Completion gate: the subpolygon package can be supplied to
    `PlanarBoundaryClosure.PlanarBoundaryData` and to the Lemma 6/8
    contradiction subagents.

- [x] Add conditional planar-boundary closure adapter.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/PlanarBoundaryClosure.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    axiom audit.  It combines supplied `OuterBoundaryCore`, boundary
    bookkeeping/angle data, and subpolygon cycle/count/angle data into the
    `FaceCountingBridge` inputs.
  - Conditional status: it still requires the explicit planar/Jordan-style
    outer-boundary core and honest subpolygon data.

#### S5. Discharge boundary and subpolygon angle lower bounds

- [x] Add angle-lower-bound interface packages.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryAngleInterface.lean`.
  - Current state: imported, build-checked, and scan-clean.  It defines
    `BoundaryAngleLowerBoundPackage` and
    `SubpolygonAngleLowerBoundPackage`, routing supplied geometric angle-sum
    comparisons into the checked boundary and subpolygon counting inequalities.
  - Conditional status: the geometric angle sums and their comparison
    inequalities are still hypotheses.

- [x] Add concrete boundary-angle realization interface.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryAngleRealization.lean`.
  - Current state: imported by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, build-checked,
    and scan-clean.
  - Current purpose: records explicit per-class outer-boundary angle masses
    and routes them to `BoundaryAngleLowerBoundPackage`.
  - Conditional status: it still consumes supplied geometric angle-mass data;
    it does not derive those masses from an actual outer boundary.

- [ ] Prove outer boundary angle lower bound.
  - Paper step: Swanepoel `E12`, boundary angle-count inequality.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryAngleRealization.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/OuterBoundaryAngleClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryCounting.lean`.
  - Current consumer declarations:

```lean
BoundaryAngleRealization.OuterBoundaryAngleRealization.angleLowerBound
OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.angleLowerBound
OuterBoundaryAngleClosure.boundaryAngleCountInequality_of_outerBoundaryCore_angleRealization
```

  - Deliverable: construct the explicit `BoundaryAngleRealization` or
    `BoundaryBookkeepingAngleBounds` for the honest outer boundary.
  - Target skeleton:

```lean
noncomputable def outerBoundaryAngleRealization_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BoundaryAngleRealization.OuterBoundaryAngleRealization := by
  sorry

theorem outerBoundaryAngleLowerBound_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    BoundaryCounting.BoundaryCounts.AngleLowerBound
      (outerBoundaryAngleRealization_of_minimalFailure hmin).counts :=
  (outerBoundaryAngleRealization_of_minimalFailure hmin).angleLowerBound
```

  - How: use the polygon interior-angle sum plus local triangle/quadrilateral
    angle facts to prove the geometric angle-mass inequalities consumed by
    `BoundaryCounts.boundary_angle_count_inequality`.
  - Completion gate: the resulting angle package combines with S4 boundary
    counts inside `PlanarBoundaryClosure.PlanarBoundaryData`.

- [ ] Prove subpolygon angle lower bound.
  - Paper step: Swanepoel `E13`, subpolygon angle-count inequality.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAngleRealization.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAssembly.lean`.
  - Current consumer declarations:

```lean
SubpolygonAssembly.SubpolygonCycleCountAngleData.angleLowerBound
SubpolygonAssembly.SubpolygonCycleCountAngleData.lowDegreeInequality
SubpolygonAssembly.e13LowDegreeInequality_of_explicitCycleCountAngleData
```

  - Deliverable: construct the explicit subpolygon angle realization for each
    subpolygon produced by S4 and needed by Lemma 6/Lemma 8.
  - Target skeleton:

```lean
noncomputable def subpolygonCycleCountAngleData_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : SubpolygonCore.SubpolygonPackage
      (JordanTopologyFactsConcrete.canonicalGraph C)) :
    SubpolygonAssembly.SubpolygonCycleCountAngleData
      (JordanTopologyFactsConcrete.canonicalGraph C) := by
  sorry

theorem subpolygonLowDegreeInequality_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (P : SubpolygonCore.SubpolygonPackage
      (JordanTopologyFactsConcrete.canonicalGraph C)) :
    6 <=
      2 * (subpolygonCycleCountAngleData_of_minimalFailure hmin P).counts.D2 +
        (subpolygonCycleCountAngleData_of_minimalFailure hmin P).counts.D3 :=
  (subpolygonCycleCountAngleData_of_minimalFailure hmin P).lowDegreeInequality
```

  - How: mirror the outer-boundary angle proof for induced subpolygons and
    feed `SubpolygonDegreeCounts.subpolygon_low_degree_inequality`.
  - Completion gate: the subpolygon angle package can be used directly by the
    S6 long-arc and Lemma 8 subpolygon-contradiction tasks.

#### S6. Formalize Swanepoel Lemmas 6, 7, 5, 8, and 9

- [ ] Prove Lemma 6 / forced negative after a gap.
  - Paper step: Swanepoel `E14`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcBudgetFromBoundary.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAssembly.lean`.
  - Deliverable: a reusable theorem turning the paper gap condition on a
    boundary arc into the negative/concavity conclusion consumed by the
    nonconcave-arc package.  The existing Lean files are reducers; this task
    must introduce the exact project-local gap predicate and prove the paper
    implication before it is used to build the final arc-angle data.
  - How: express the gap condition in terms of the current boundary-spine and
    turn data, construct the subpolygon contradiction, and feed the checked
    S5 subpolygon low-degree inequality.
  - Completion gate: the theorem is callable while constructing
    `NonconcaveArcGeometricAngleFacts`.

- [ ] Prove Lemma 7 / degree-three gap induction.
  - Paper step: Swanepoel `E15`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`.
  - Deliverable: an induction theorem over the degree-three/gap pattern that
    supplies the arc monotonicity/forced-turn facts required by
    `NonconcaveArcGeometricAngleFacts`.  This should consume the Lemma 6
    theorem above, not bypass it with a new abstract field.
  - How: iterate the Lemma 6 theorem over the boundary index interval, keeping
    all finite-index arithmetic in `Nat`/`Fin` rather than informal cyclic
    notation.
  - Completion gate: the induction theorem is used in the construction of
    `arcAngleFacts`.

- [ ] Prove Lemma 5 / existence of a nonconcave long arc.
  - Paper step: Swanepoel `E16`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsFromArc.lean`.
  - Deliverable: construct the existing geometric-angle package from the S4/S5
    boundary and subpolygon facts plus Lemmas 6 and 7.

```lean
noncomputable def nonconcaveArcGeometricAngleFacts_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (planarBoundary :
      PlanarBoundaryClosure.PlanarBoundaryData
        (BoundaryFaceCountingToM8.CanonicalUDGraph C)) :
    NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts := by
  sorry
```

  - How: package the selected long arc, the turn function, turn
    nonnegativity, and the `totalTurn < Real.pi / 3` budget from Lemmas 6 and
    7.
  - Completion gate: the refined M8 package field `arcAngleFacts` is filled.

- [ ] Specialize the long-arc data to the `m = 8` thirteen-turn package.
  - Paper step: Swanepoel `E17`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsFromArc.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsConcrete.lean`.
  - Target skeleton:

```lean
noncomputable def m8ThirteenTurnData_of_nonconcaveArc
    (A : NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  A.toNonconcaveArcTurnData
```

  - How: prove that the paper's selected `m = 8` arc is exactly the current
    `turnIndexSet = {1, ..., 13}` and that all off-arc turns are normalized to
    zero by the checked adapter.
  - Completion gate: S7 can use
    `A.toNonconcaveArcTurnData.toM8TurnBounds.turn` as the turn function in
    the angle-containment field.

- [ ] Prove Lemma 8 / construction of the `r_i, s_i` witnesses.
  - Paper step: Swanepoel `E18`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundarySpineFiniteCertificate.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryLabelCertificateAssembly.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8NeighborExtractionConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8ExistenceConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8CyclicOrderConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8DegreeSixConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8ForbiddenDistinctConcrete.lean`.
  - Deliverables:

```lean
noncomputable def m8FinitePQSpineCertificate_of_planarBoundary
    {n : Nat} {C : UDConfig n}
    (planarBoundary :
      PlanarBoundaryClosure.PlanarBoundaryData
        (BoundaryFaceCountingToM8.CanonicalUDGraph C)) :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      planarBoundary := by
  sorry

noncomputable def m8Lemma8MissingExistenceConditions_of_spine
    {n : Nat} {C : UDConfig n}
    {H : M8LabelsFromBoundaryInterface.M8BoundaryCutDegreeContext C}
    (S : M8LabelsFromBoundaryInterface.M8BoundarySpine H) :
    Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions S := by
  sorry
```

  - How: first extract the finite `p/q` spine from the boundary labels, then
    prove the missing existence/cyclic-order/degree-six/forbidden-distinct
    fields using local boundary classification and S4/S5 subpolygon
    contradictions.
  - Completion gate: the refined M8 package fields `spineCertificate` and
    `lemma8Existence` are filled.

- [ ] Prove Lemma 9 / late triples.
  - Paper step: Swanepoel `E19`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoEarlyTripleFromLemma9.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoEarlyTripleObstructionConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8LateTriplesFromNoEarly.lean`.
  - Deliverable:

```lean
noncomputable def m8Lemma9FiveStartLateFacts_of_paperLemma9
    {V : Type u} {G : LocalConfigurations.LocalGraph V}
    (P : LocalConfigurations.BrokenLatticePredicates G 8) :
    NoEarlyTripleFromLemma9.M8Lemma9FiveStartLateFacts P := by
  sorry
```

  - How: show any equality triple in the honest `m = 8` label package starts
    at index at least `6`, then route it through the checked no-early-triples
    adapter.
  - Completion gate: the refined M8 package field `lemma9FiveStartLateFacts`
    is filled.

#### S7. Close E22/E23 through angle-to-turn containment

- [x] Add containment-to-angle-to-turn bridge interfaces.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/AngleContainmentInterface.lean`.
  - Checked declarations:

```lean
structure Figure8SeparatedContainmentInterface
structure Figure9AdjacentLeftContainmentInterface
structure AngleContainmentBridges

theorem Figure8SeparatedContainmentInterface.separatedWindowLowerE22
theorem Figure9AdjacentLeftContainmentInterface.adjacentWindowLowerE23
theorem AngleContainmentBridges.E22_E23
```

  - Current state: once extracted Figure 8/Figure 9 data and the respective
    angle-containment inequalities are supplied, the file packages them into the
    existing `Lemma10AngleToTurn` E22/E23 bridge.

- [x] Add window-level geometry wrappers for E22/E23.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10WindowGeometry.lean`.
  - Current state: imported, build-checked, and scan-clean.  The file routes
    explicit unit-distance data plus containment in the separated/adjacent
    turn windows to the existing E22/E23 lower-bound interfaces, including
    honest `m = 8` wrappers.
  - Conditional status: it still requires the actual Figure 8/Figure 9
    distance data and window-containment proofs.

- [ ] Extract Figure 8 distance data from failed separated labels.
  - Paper step: Swanepoel `E22`, Lemma 10 inequality (5), Figure 8.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8ContainmentConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8EuclideanFactsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8ContainmentAngleBudget.lean`,
    with older analytic data in
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/AngleBridgeFacts.lean`.
  - Local deliverable:

```lean
Figure8ContainmentConcrete.Figure8SeparatedWindowContainment
```

  - How: map the broken-lattice witnesses into the current Figure 8 contained
    witness structure, prove the unit-distance/squared-distance facts, and
    route them through the existing Euclidean facts module.
  - Completion gate: the Figure 8 half of `AngleContainmentBridges` can be
    constructed for the honest M8 labels.

- [ ] Prove Figure 8 central-angle containment.
  - Paper step: Swanepoel `E22`, angle-to-turn containment.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10AngleToTurn.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8ContainmentAngleBudget.lean`.
  - Deliverable field:
    `Figure8SeparatedAngleToTurnBridge.central_angle_le_separatedTurn`.
  - How: prove the oriented angle lies inside the separated turn window.  The
    local `pi / 3` angle lower bound is already checked.
  - Completion gate: this field is combined with the Figure 8 witness package
    into the Figure 8 part of `AngleContainmentBridges`.

- [ ] Extract Figure 9 distance data from failed adjacent labels.
  - Paper step: Swanepoel `E23`, Lemma 10 inequality (6), Figure 9.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9ContainmentConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9EuclideanFactsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9ContainmentAngleBudget.lean`.
  - Local deliverable:

```lean
Figure9ContainmentConcrete.Figure9AdjacentLeftContainedWitnesses
```

  - How: map adjacent failed labels into the current Figure 9 contained
    witness structure and prove the required unit-distance/squared-distance
    facts.
  - Completion gate: the Figure 9 half of `AngleContainmentBridges` can be
    constructed for the honest M8 labels.

- [ ] Prove Figure 9 left-angle containment.
  - Paper step: Swanepoel `E23`, angle-to-turn containment.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10AngleToTurn.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9ContainmentAngleBudget.lean`.
  - Deliverable field:
    `Figure9AdjacentLeftAngleToTurnBridge.left_angle_le_adjacentTurn`.
  - How: prove the oriented Figure 9 angle lies inside the adjacent three-turn
    window, then package the field with the distance data from the previous
    item.
  - Completion gate: this field is combined with the Figure 9 witness package
    into the Figure 9 part of `AngleContainmentBridges`.

- [ ] Build the honest E22/E23 hypotheses.
  - Existing final bridge:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10AngleToTurn.lean`.
  - Window-geometry bridge:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10WindowGeometry.lean`.
  - Target route:

```lean
figure8SeparatedWindowLowerE22_of_angleToTurnBridge
figure9AdjacentWindowLowerE23_of_leftAngleToTurnBridge
E22_E23_of_angleToTurnBridges

Lemma10WindowGeometry.honestE22_E23_of_leftWindowGeometry
```

  - Deliverable:

```lean
noncomputable def angleContainment_of_m8LabelsAndArc
    {n : Nat} {C : UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (A : NonconcaveArcAngleFacts.NonconcaveArcGeometricAngleFacts) :
    AngleContainmentInterface.AngleContainmentBridges
      (Lemma10Bridge.M8BrokenLatticeGood localLabels.predicates.data)
      A.toNonconcaveArcTurnData.toM8TurnBounds.turn := by
  sorry
```

  - How: construct `Figure8SeparatedAngleToTurnBridge` and
    `Figure9AdjacentLeftAngleToTurnBridge`, or use the newer containment
    wrappers directly from extracted distance data and window-containment
    lemmas.
  - Completion gate: the refined M8 package field `angleContainment` is filled.

- [x] Add containment-to-M8 window geometry adapter.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8WindowGeometryFromContainment.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8ContainmentConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8EuclideanFactsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure8ContainmentAngleBudget.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9EuclideanFactsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9ContainmentAngleBudget.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Figure9ContainmentConcrete.lean`.
  - Current state: imported, build-checked, scan-clean, and compatible with
    the current CI-style axiom audit.  It repackages supplied Figure 8/Figure 9 containment
    interfaces, concrete contained-witness data, and angle-budget wrappers
    into the window-geometry fields consumed by `M8ConstructionInterface`;
    the Figure 9 module now builds after the witness-alias type mismatch was
    corrected.
  - Conditional status: the concrete containment interfaces and extracted
    distance data still need to be proved from the boundary/broken-lattice
    geometry.

#### S8. Build the final minimal-failure contradiction

- [x] Add broken-lattice contradiction and minimal-failure closure interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BrokenLatticeInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BrokenLatticeMinimalFailure.lean`.
  - Current state: imported, build-checked, and scan-clean.
    `BrokenLatticeInterface` routes a supplied honest `m = 8` local-predicate,
    turn, E22/E23, and late-triples package to contradiction.
    `BrokenLatticeMinimalFailure` names the remaining construction data and
    proves `no_minimalClearedFailure_of_m8ConstructionEliminator` from an
    eliminator supplying that data for every minimal cleared failure.
  - Conditional status: the eliminator is not constructed yet.

- [x] Add turn-bound, late-triples, and M8 pipeline closure
  interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/TurnBoundsInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/LateTriplesInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8PipelineClosure.lean`.
  - Current state: imported by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, build-checked,
    and scan-clean.
  - Current purpose: package honest turn bounds, finite late-triples inputs,
    and separated M8 construction fields into the existing broken-lattice
    contradiction route.
  - Conditional status: the honest inputs still need to be constructed from
    the minimal-failure geometry.

- [x] Add boundary-to-M8, nonconcave-arc, no-early-triple, and final
  conditional M8 adapters.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8LabelsFromBoundaryInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsFromArc.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcBudgetFromBoundary.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8LateTriplesFromNoEarly.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoEarlyTripleFromLemma9.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoEarlyTripleObstructionConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8MinimalFailureEliminatorInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/FinalConditional.lean`.
  - Current state: imported, build-checked, scan-clean, and compatible with
    the current CI-style axiom audit.  These files package the structural boundary/no-cut/degree
    context, explicit Lemma 8 labels, concrete nonconcave-arc angle
    inequalities, boundary-attached turn-budget reducers, Lemma 9-shaped
    no-early triple exclusions, obstruction bookkeeping, and final separated
    M8 eliminator into the current conditional Swanepoel target route.
  - Conditional status: the paper Lemma 8 combinatorics, nonconcave arc,
    no-early-triple proof, containment data, and separated M8 construction
    fields still must be constructed from an actual minimal cleared failure.

- [x] Add concrete M8 assembly and reducer modules.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8ConstructionDataBridge.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureComponentPackage.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureFactsFamilyConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnWindowNoEarlyFinal.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryFaceCountingToM8.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryLabelExtractionTasks.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundarySpineConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundarySpineFiniteCertificate.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryLabelCertificateAssembly.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexSlackFromDeletion.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexSideCardFromMinimality.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanBoundaryExtraction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanBoundaryConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanTopologyFactsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/PlanarBoundaryFaceDataRefinement.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8CombinatoricsConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8NeighborExtractionConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8ExistenceConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8CyclicOrderConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8DegreeSixConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8ForbiddenDistinctConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8PaperFactsAssemblyRefined.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailurePaperFactMatrix.lean`.
  - Current state: imported, build-checked, scan-clean, and compatible with
    the current CI-style axiom audit.
  - Current purpose: the remaining Swanepoel construction has been narrowed to
    the explicit `MinimalFailureM8PaperFacts` fields: positive cardinality,
    cut-vertex slack, planar boundary/Jordan data, the M8 boundary spine,
    Lemma 8 extra-neighbor combinatorics, nonconcave-arc turn data, no-early
    triples, and Figure 8/Figure 9 containment.
  - Conditional status: these fields are still paper facts to prove, not
    completed Lean constructions.

- [ ] Prove the minimal-failure `m = 8` construction eliminator.
  - Paper step: Swanepoel `E24`, final `m = 8` contradiction.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8PaperFactsAssemblyRefined.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureFactsFamilyConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureComponentPackage.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8PipelineClosure.lean`.
  - Source-refined paper deliverables:

```lean
noncomputable def minimalFailureM8RefinedPaperFacts
    {n : Nat} (C : UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts C hmin := by
  sorry

noncomputable def minimalFailureM8RefinedPaperFactsFamily :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily where
  facts := fun C hmin => minimalFailureM8RefinedPaperFacts C hmin

theorem targetLowerBoundEightThirtyOne_verified :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  minimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne
```

  - Lean-efficient separated-construction gate:

```lean
noncomputable def minimalFailureM8SeparatedConstructionEliminator :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator := by
  intro n C hmin
  sorry
```

  - Exact gate definition already checked in Lean:

```lean
def M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty (M8PipelineClosure.M8SeparatedConstructionFields C hmin)
```

  - How: assemble the S3 cut-slack field, S4/S5 planar-boundary field, S6
    spine/Lemma 8/arc/Lemma 9 fields, and S7 containment field into
    `MinimalFailureM8RefinedPaperFacts`.  Then use
    `MinimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne`.
  - Completion gate: the refined family proves
    `Swanepoel.targetLowerBoundEightThirtyOne` without extra hypotheses.

- [ ] Prove no minimal cleared failure.
  - Best home: new `MinimalFailureContradiction.lean` or
    `NoMinimalFailure.lean`.
  - Target theorem:

```lean
theorem no_minimalClearedFailure
    {n : Nat} (C : UDConfig n) :
    Not (MinimalGraphFacts.IsMinimalClearedFailure C)
```

  - Next action: construct the S8 eliminator and call
    `BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator`.

- [ ] Prove the verified target wrapper.
  - Target theorem:

```lean
theorem targetLowerBoundEightThirtyOne_verified :
    targetLowerBoundEightThirtyOne
```

  - Next action: apply
    `MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure`.

- [ ] Add the public theorem.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/KnownBounds.lean`.
  - Target theorem:

```lean
theorem lower_bound_eight_thirty_one
    (n : Nat) (C : UDConfig n) :
    exists s : Finset (Fin n), C.IsIndep s /\ 31 * s.card >= 8 * n
```

## Pach-Toth 5 / 16 Overview

Current exact-block target:

```lean
-- E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Bridge.lean
def targetUpperConstructionFiveSixteen : Prop :=
  forall (k : Nat), 0 < k ->
    exists C : UDConfig (16 * k),
      forall s, C.IsIndep s -> s.card <= 5 * k
```

Current arbitrary-`n` target:

```lean
-- E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ArbitraryN.lean
def targetUpperConstructionFiveSixteenArbitrary : Prop := ...
```

Important source-faithfulness correction: the Pach-Toth paper route is
eventual, for sufficiently large `n` / sufficiently large block count `k`.
The current all-positive-`k` Lean target is a stronger optional theorem unless
finite small-case certificates are supplied.

Paper-to-Lean route:

| Paper step | Strategy in the paper | Lean route / current consumer |
|---|---|---|
| `FG.1-FG.4` | proof-used finite block graph, independence count, and edge roles | P2, `FiniteGraph`, `CrossBlock`, `Figure2EdgeTable` |
| `FG.5-FG.6` | source-faithful complete Figure 2 table from the PostScript primitives | P2 optional attribution layer, full `S0-S8` / `U0-U29` table and projection lemmas |
| `GEO.1` | exact one-block geometry | already routed by `ExactLocalGeometry`, `AffineLocalGeometry`, `BaseTransitionRealization.exactBase` |
| `GEO.2` | same/opposite non-rigid transition maps, including connector unit edges | P3, `RoleHingeInterfaceRefinement.SameOppositeRoleHingeOrbitTransitionFacts`; concrete connector edges are P3, global `next_sep` is P4 |
| `GEO.3` | source-faithful closed chains/period closure for sufficiently large block count | P4/P5, orientation words, `AlgebraicVertexPeriodEquation` fields, and eventual/threshold route |
| `GEO.3` stronger Lean route | compact all-positive-`k` closed chains and square-distance tables | P4, `FiniteCertificateObligationSummary.Obligations` |
| `GEO.3` separation | global distance `>= 1` for cross-block pairs | P4, all-pairs `CrossBlockSqTableSearch` route or reduced non-connector `NonRigidConnectorSeparationFacts` route |
| `GEO.4` | remainder placement | P5, `RemainderPlacement`, `SplitArbitraryNNonRigidBridge`, `SmallCaseCertificates` |
| `PT96.Main` | sufficiently large construction, optionally all `n` with finite cases | P5-P6, `targetUpperConstructionFiveSixteenEventually` and `targetUpperConstructionFiveSixteenArbitrary` |

Compact stronger all-positive-`k` non-rigid package:

```lean
FiniteCertificateObligationSummary.Obligations
```

It is the compact non-rigid route.  Its fields are `transitions`, `word`,
`equation`, `sqValue`, `sqValue_eq_polynomial_lt`, and `sqValue_ge_one_lt`.
Once supplied, it closes the exact and arbitrary target facades through
`FiniteCertificateObligationSummary.Obligations.targetUpperConstructionFiveSixteen`
and
`FiniteCertificateObligationSummary.Obligations.targetUpperConstructionFiveSixteenArbitrary`.
The only top-level theorem currently exposed in that module is the arbitrary
wrapper
`FiniteCertificateObligationSummary.targetUpperConstructionFiveSixteenArbitrary`.
The source-faithful thresholded/eventual analogue of this obligation package is
still a target task, not an existing imported structure.
Do not use the translated four-equation facade as the live route; that route is
kept only as an audited obstruction surface.

### Pach-Toth Already Checked

- [x] Finite one-block graph and counting.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FiniteGraph.lean`.
  - Current declarations include `alpha_le_six`,
    `unique_size_six_independent`, and `next_block_after_forbidden_le_four`.

- [x] Chain counting.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlock.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Chain.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/IndexedChain.lean`.

- [x] Exact local one-block geometry.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ExactLocalGeometry.lean`.
  - Note: do not use rounded PostScript drawing coordinates as metric
    coordinates.

- [x] Affine/local-coordinate and connector-equation support.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/AffineLocalGeometry.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ConnectorEquationFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedChainConstruction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/DeformedOrientationBridge.lean`.
  - Current state: imported, build-checked, and scan-clean.  These files
    provide coordinate/connector algebra and adapters from supplied oriented
    closed-chain placements to explicit closed-placement and indexed-chain
    certificates.
  - Conditional status: they do not supply the non-rigid transition geometry,
    period closure, or global separation by themselves.

- [x] Rigid translation routes are formally dead.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockGeometry.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/OrientedCrossBlockGeometry.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RealTranslationObstruction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/TranslatedEquationObstruction.lean`.
  - Current state: the stronger four-equation translated connector route is
    also formally uninhabited.  Do not use
    `FinalConditional.EquationPeriodSearchCrossBlockFamily` as the live proof
    route; keep it only as an audited conditional surface over inconsistent
    equation-transition data.

- [x] Remainder construction and far-apart translated placement.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RemainderConstruction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RemainderPlacement.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SplitSoundness.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SplitCertificateBridge.lean`.

- [x] Conditional closed-placement interfaces and reductions.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Arithmetic.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/DeformedPlacement.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedPlacementInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedChainExistence.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedChainReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CyclicIndex.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChain.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChainReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChainEventualReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/EventualReduction.lean`.
  - New checked arithmetic:
    `Arithmetic.cyclicSucc_iterate_val` and
    `Arithmetic.cyclicSucc_iterate_card`.
  - New checked orbit bridge:
    `ClosedChainExistence.SuccessorCompatibleCyclicPointOrbit.exists_closedPlacement_of_successorCompatibleCyclicPointOrbit`
    and
    `ClosedChainExistence.IsometricSuccessorCompatibleCyclicPointOrbit.exists_closedPlacement_of_isometricSuccessorCompatibleCyclicPointOrbit`.
  - Current meaning: a successor-compatible cyclic orbit now packages into the
    downstream closed-placement interface.  Generated closed-chain data now
    routes through exact-block, exact-target, and eventual arbitrary-`n`
    Pach-Toth reductions once its period, global separation, and same-block
    isometry obligations are supplied.  The theorem
    `GeneratedClosedChain.generatedPoint_same_block_isometry` reduces the
    same-block isometry obligation to base-block isometry plus local
    transition distance preservation.  Period and global separation remain open
    geometry.
  - Current eventual route:
    `GeneratedClosedChainEventualReduction.targetUpperConstructionFiveSixteenArbitrary_of_eventual_generated_chains_base_transitions`
    carries the same reduced same-block hypothesis style through the
    eventual-plus-small-cases arbitrary-`n` target.

### Pach-Toth Completion Checklist

#### P1. Add source-faithful eventual target

- [x] Add an internal eventual target.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ArbitraryN.lean`.
  - Checked declarations:

```lean
def targetUpperConstructionFiveSixteenEventually : Prop :=
  exists N0 : Nat, forall n : Nat,
    N0 <= n -> targetUpperConstructionFiveSixteenAt n

def targetUpperConstructionFiveSixteenSmallUpTo (N0 : Nat) : Prop :=
  forall n : Nat, n < N0 -> targetUpperConstructionFiveSixteenAt n

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventually_and_small
    (N0 : Nat)
    (Hlarge : forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n)
    (Hsmall : targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary
```

  - Current state: pure routing theorem is imported, build-checked, and in the
    axiom audit.  `PachToth/EventualReduction.lean` also routes eventual
    explicit closed-placement certificates plus finite small-case checks to the
    arbitrary-`n` target.  These theorems do not construct the large or small
    cases.

#### P2. Decide proof-sufficient versus source-faithful Figure 2 transcription

- [x] For the proof-sufficient Lean construction, the finite counting and
  proof-used edge roles are stated in terms of the current relations.
  - Paper step: Pach--Toth `FG.1-FG.4`, proof-used Figure 2 relation
    extraction.
  - Same-block relation:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FiniteGraph.lean`.
  - Cross-block relation:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlock.lean`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Figure2EdgeTable.lean`,
    consumed by `RoleHingeTransitionSearch` and the finite counting modules.
  - Deliverable: theorem/docstring wording for any internal or public wrapper
    says "proof-used Figure 2 edge roles" unless the full transcription task
    below is completed.
  - Checked gate:

```lean
theorem proofUsedFigure2EdgeRoles_project_to_current_relations :
    (forall u v role,
      Figure2EdgeTable.localEdgeRole u v = some role ->
        FiniteGraph.adj u v = true) /\
    (forall u v role,
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        CrossBlock.NextConnector u v) :=
  And.intro
    Figure2EdgeTable.localEdgeRole_adj
    Figure2EdgeTable.nextConnectorRole_nextConnector
```

  - Completion gate: this proof-sufficient gate is already imported; any
    wrapper wording must continue to say "proof-used Figure 2 edge roles"
    unless the full transcription task below is completed.

- [ ] Audit wording so no internal or public theorem claims a complete Figure
  2 transcription before `FG.5-FG.6` is closed.
  - Paper step: Pach--Toth attribution hygiene.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Figure2EdgeTable.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/KnownBounds.lean`,
    any eventual Pach--Toth wrapper module.
  - Completion gate: all names/docstrings/public wrappers distinguish the
    proof-used finite model from a complete source transcription.

- [x] Add the proof-used Figure 2 edge-role table.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Figure2EdgeTable.lean`.
  - Current state: imported, build-checked, and scan-clean.  It records the
    local edge roles, connector-source names, farthest representatives, and
    directed successor-connector roles used by the finite and chain counting
    proofs, with projection lemmas to `FiniteGraph.adj` and
    `CrossBlock.NextConnector`.
  - Conditional status: this is the proof-used finite subset; do not describe
    it as a complete Figure 2 transcription.

- [ ] Complete the source-faithful Figure 2 transcription if needed for the
  public attribution.
  - Paper step: Pach--Toth `FG.5-FG.6`, full Figure 2 edge table from the
    PostScript primitives.
  - Needed data:
    primitive side table, same-block edge projection to `FiniteGraph.adj`,
    orientation-indexed next-block relation or projection to
    `CrossBlock.NextConnector`, `p/q` roles, farthest-vertex roles, and
    no-duplicate/no-gap theorems.
  - Lean route:
    extend `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Figure2EdgeTable.lean`
    or add a dedicated imported module if the table becomes too large.
  - Deliverable: complete finite table plus projection lemmas to
    `FiniteGraph.adj` and `CrossBlock.NextConnector`.
  - Target skeleton after introducing the primitive source types:

```lean
structure SourceFaithfulFigure2TableCertificate where
  sourceLocalEdge :
    FiniteGraph.LocalVertex -> FiniteGraph.LocalVertex -> Bool
  sourceNextConnector :
    FiniteGraph.LocalVertex -> FiniteGraph.LocalVertex -> Bool
  localProjects :
    forall u v, sourceLocalEdge u v = true ->
      FiniteGraph.adj u v = true
  localComplete :
    forall u v, FiniteGraph.adj u v = true ->
      sourceLocalEdge u v = true
  nextProjects :
    forall u v, sourceNextConnector u v = true ->
      CrossBlock.NextConnector u v
  nextComplete :
    forall u v, CrossBlock.NextConnector u v ->
      sourceNextConnector u v = true
```

  - Completion gate: every side of the listed `S0-S8` and `U0-U29`
    primitives is classified exactly once and proof-used rows project to the
    existing finite relations.

#### P3. Construct the non-rigid transition geometry

- [x] Add unit-vector and hinge algebra interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/UnitVectorGeometry.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/HingeAlgebra.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/HingedTransitionInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/BaseTransitionRealization.lean`.
  - Current state: imported, build-checked, and scan-clean.  The checked layer
    defines `unitVec`, `hingePoint`, squared-distance hinge lemmas,
    same/opposite transition metric interfaces, `RoleHingeTransition`, and
    the exact base-block isometry for `ExactLocalGeometry.localPoint`.
  - Conditional status: concrete same/opposite role-hinge transitions and
    their distance-preservation fields are still supplied data.

- [ ] Build concrete refined same/opposite role-hinge transition data.
  - Live target shape:

```lean
noncomputable def concreteSameOppositeRoleHingeOrbitTransitionFacts :
    RoleHingeInterfaceRefinement.SameOppositeRoleHingeOrbitTransitionFacts := by
  sorry

noncomputable def concreteSameOppositeTransitionObligations_refined :
    Figure2Certificate.SameOppositeTransitionObligations :=
  concreteSameOppositeRoleHingeOrbitTransitionFacts.toFigure2TransitionObligations
```

  - Next action: choose the role angles and transition maps, prove the
    connector unit-edge fields through `RoleHingeConnectorAlgebra`, and route
    the refined facts to `Figure2Certificate.SameOppositeTransitionObligations`.
    Do not target the old
    `BaseTransitionRealization.BaseSameOppositeTransitionRealization` as the
    live path; the current fixed-angle strong interface is obstructed by
    `RoleHingeInterfaceRefinement.no_concreteSameOppositeRemainingEquations_for_strong_interface`.

- [x] Add non-rigid/role-hinged transition and closed-placement wrappers.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeTransitionSearch.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeConnectorAlgebra.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeAngleCertificates.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeSameBlockAlgebra.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeFiniteFamilyBridge.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeConcreteSearch.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeInterfaceRefinement.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/NonRigidClosedPlacementInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedPlacementNonRigidComponents.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedPlacementComponentsAssembly.lean`.
  - Current state: imported, build-checked, scan-clean, and compatible with
    the current CI-style axiom audit.
  - Current purpose: these modules route explicit non-rigid point/orbit
    fields and role-hinged transition facts to closed placements, exact-block
    targets, and exact-family targets; the newest algebra layers expose
    connector-port unit facts, exact-local same-block square-distance
    obligations, role-hinge interface refinements, component assembly, and a
    concrete role-angle search facade without using the contradictory
    translated four-equation data.
  - Conditional status: concrete role-angle maps, same-block preservation,
    successor connector unit edges, and global separation are still fields to
    prove.

- [ ] Prove exact-local same-block square-distance preservation for the
  concrete transitions.
  - Target theorems:

```lean
theorem concreteSamePlaceNext_preservesExactLocalSqDistances :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      RoleHingeConcreteSearch.samePlaceNext := by
  sorry

theorem concreteOppositePlaceNext_preservesExactLocalSqDistances :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      RoleHingeConcreteSearch.oppositePlaceNext := by
  sorry
```

  - Next action: case-split over `FiniteGraph.adj` / local vertex pairs and
    discharge each squared-distance identity with exact trig/vector algebra.
    These theorems feed
    `RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances`
    and then the orbit-level exact-local metric route.

- [x] Prove the generic connector-port unit-edge reducer.
  - Checked route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeConnectorAlgebra.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeInterfaceRefinement.lean`.
  - Current state: the generic role-hinge connector algebra is imported,
    build-checked, and scan-clean.

- [ ] Instantiate concrete connector-port unit edges.
  - Target theorem shape:

```lean
theorem concreteSameOppositeTransitionObligations_connector_edges :
    (forall source u v,
      CrossBlock.NextConnector u v ->
        _root_.eucDist (source u)
          (concreteSameOppositeTransitionObligations_refined.samePlaceNext
            source v) = 1) /\
    (forall source u v,
      CrossBlock.NextConnector u v ->
        _root_.eucDist (source u)
          (concreteSameOppositeTransitionObligations_refined.oppositePlaceNext
            source v) = 1) := by
  constructor
  case left =>
    intro source u v hconn
    exact
      concreteSameOppositeTransitionObligations_refined.same_connector_unit_edges
        source u v hconn
  case right =>
    intro source u v hconn
    exact
      concreteSameOppositeTransitionObligations_refined.opposite_connector_unit_edges
        source u v hconn
```

  - Next action: fill `concreteSameOppositeRoleHingeOrbitTransitionFacts`; the
    projection theorem above is then immediate.

- [ ] Build same/opposite transition maps, or bypass them with direct
  certificates.
  - Existing conditional interface:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Figure2Certificate.lean`.
  - Target declaration if using the interface:

```lean
def concreteSameOppositeTransitionObligations_refined :
  Figure2Certificate.SameOppositeTransitionObligations
```

  - Current state: the refined role-hinge route avoids the obstructed
    arbitrary-source preservation field.  The old
    `ConcreteSameOppositeRemainingEquations` /
    `BaseSameOppositeTransitionRealization` path is retained only as an
    obstruction audit surface.
  - Next action: instantiate the refined transition obligations, prove exact
    same-block square-distance preservation on generated orbits, then pass the
    resulting `SameOppositeTransitionObligations` to the P4 period/separation
    tasks.  Global separation and period closure remain separate obligations.

#### P4. Construct closed placements

- [x] Add generated closed-chain packaging and reduction plumbing.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChain.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChainReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedSeparationInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedPeriodClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedPlacementClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ConcretePeriodSearchFamily.lean`.
  - Checked declarations:

```lean
theorem GeneratedClosedChain.exists_closedPlacement_of_generated_closed_chain
theorem GeneratedClosedChain.generatedBlock_eq_closedPlacementAlgebra_iterated_from_zero

theorem GeneratedClosedChainReduction.targetUpperConstructionFiveSixteenAt_exactBlock_of_generated_closed_chain
theorem GeneratedClosedChainReduction.targetUpperConstructionFiveSixteen_of_generated_closed_chains
```

  - Current state: imported, build-checked, and scan-clean.  Generated
    same/opposite orbit data routes into the existing closed-placement and
    exact-block target interfaces.  `PeriodInterface` names the generated
    period/closure equations; `GeneratedPeriodClosure` and
    `ClosedPlacementClosure` route supplied period/closure equations plus
    generated metric hypotheses to exact-block and family target statements.
  - Conditional status: the period/closure equations, global separation, and
    concrete same/opposite metric realization remain open geometry/data.

- [x] Add generated metric and period-search interfaces.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedMetricClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodSearchInterface.lean`.
  - Current state: imported by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, build-checked,
    and scan-clean.
  - Current purpose: `GeneratedMetricClosure` packages exact-base
    role-hinged generated chains from supplied global separation and closure
    data; `PeriodSearchInterface` names finite orientation-word period
    certificates for later verified algebraic/search outputs.
  - Conditional status: the actual period certificates, global separation, and
    concrete metric data remain open.

- [x] Add finite period-word and indexed cross-block table reducers.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodWordCertificates.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/IndexedCrossBlockTableConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockDistanceSqReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/NonRigidConnectorSeparationFacts.lean`.
  - Current state: imported, build-checked, scan-clean, and compatible with
    the current CI-style axiom audit.
  - Current purpose: period words/equations and finite indexed cross-block
    inequalities now have direct table-style Lean surfaces, including a
    squared-distance reducer for generated cross-block lower bounds, plus
    connector-pair separation so finite tables only have to cover remaining
    non-connector cross-block pairs.
  - Conditional status: the actual finite period equations and the lower-bound
    inequalities for every distinct block pair remain to be proved.

- [x] Add orientation-word, connector-equation, far-apart, and
  exact-family closure modules.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/OrientationWord.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ConnectorEquationClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedSeparationFarApart.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ExactFamilyClosure.lean`.
  - Current state: imported by
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, build-checked,
    and scan-clean.
  - Current purpose: finite orientation-word algebra, connector-equation
    transition packaging, generated far-apart separation wrappers, and final
    exact-family target routing.
  - Conditional status: these are routing/packaging layers; they do not supply
    the actual large closed-chain family by themselves.

- [x] Add equation-transition, cross-block lower-bound, period-example, and
  final conditional Pach-Toth facade modules.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/EquationTransitionClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockLowerBoundsInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockSqTableSearch.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockUpperTriangleConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockPolynomialNormalization.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodCertificateExamples.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodEquationConcreteSearch.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ConcretePeriodCandidateSearch.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/EventualRoleHingeClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ExactFiveSixteenRouteMatrix.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FiniteCertificateObligationSummary.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FinalConditional.lean`.
  - Current state: imported, build-checked, scan-clean, and compatible with
    the current CI-style axiom audit.  The files route explicit connector equations, same-block
    distance preservation, finite period-search certificates/candidates,
    normalized cross-block square-distance tables, obligation summaries, and
    quantitative lower-bound tables into the strongest current conditional
    Pach-Toth exact/arbitrary target facades.
    `FinalConditional.EquationPeriodSearchCrossBlockFamily` is legacy
    obstruction/conditional plumbing over the translated-equation route; it is
    not the live proof deliverable.
  - Conditional status: they still require actual same/opposite transition
    data, period certificates/equations, and cross-block lower-bound
    inequalities.

- [ ] Build the compact all-positive finite-certificate obligation package.
  - Paper step: stronger Lean route for `GEO.2-GEO.3`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FiniteCertificateObligationSummary.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ConcretePeriodSearchFamily.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockSqTableSearch.lean`.
  - Target skeleton:

```lean
noncomputable def finiteCertificateObligations :
    FiniteCertificateObligationSummary.Obligations := by
  sorry

theorem targetUpperConstructionFiveSixteen_verified :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen :=
  finiteCertificateObligations.targetUpperConstructionFiveSixteen
```

  - How: supply refined same/opposite transitions from P3, one orientation
    word and sixteen algebraic period equations for every positive `k`, and an
    upper-triangle square-value table proving every distinct cross-block pair
    has generated squared distance at least `1`.
  - Completion gate: the exact `16 * k` target follows through
    `FiniteCertificateObligationSummary.Obligations.targetUpperConstructionFiveSixteen`.

- [ ] Decide whether separation is proved by the stronger all-pairs table or
  the reduced non-connector table.
  - All-pairs route:
    `CrossBlockSqTableSearch.UpperTriangleSqValueTableFamily` to
    `CrossBlockDistanceSqReduction.IndexedCrossBlockSqDistanceTableFamily`.
  - Reduced route:
    `NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily`
    plus the checked connector-pair separation lemmas.
  - Reduced target skeleton:

```lean
noncomputable def indexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily) :
    NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
      F := by
  constructor
  intro k hk
  constructor
  intro i u j v hij hnotConnector
  sorry
```

  - How: connector-pair distances are handled by
    `NonRigidConnectorSeparationFacts`; remaining table rows need only cover
    `Ne i j` and
    `Not (NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair hk i u j v)`.
  - Completion gate: the chosen table route supplies
    `GeneratedSeparationInterface.GeneratedGlobalSeparation` for every
    generated chain used by the period route.

- [ ] Add a source-faithful thresholded/eventual finite-certificate package if
  the all-positive route is too strong.
  - Paper step: Pach--Toth `GEO.3` / `PT96.Main`, sufficiently large `k`.
  - Target skeleton for a new imported module:

```lean
structure EventualFiniteCertificateObligations (K0 : Nat) where
  transitions : FiniteCertificateObligationSummary.RoleHingeTransitions
  word :
    forall (k : Nat), K0 <= k -> 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hK hk))
        (BlockPartition.localVertexEquivFin16.symm i)
  separated :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        (fun i => word k hK hk i)

theorem targetUpperConstructionFiveSixteenEventually_of_eventualFiniteObligations
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenEventually := by
  sorry
```

  - How: mirror the all-positive obligation summary but index all data by
    `K0 <= k`.  Then combine with small cases in P5/P6 for the arbitrary-`n`
    theorem.
  - Completion gate: the eventual target is proved without claiming
    all-positive period/separation data.

- [ ] Prove sufficiently-large closed placement certificates.
  - Best home: `ClosedChainExistence.lean`.
  - Source-faithful target:

```lean
def closedChainThreshold : Nat

theorem exists_explicitClosedPlacementCertificate_large
    (k : Nat) (hlarge : closedChainThreshold <= k) (hk : 0 < k) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk

theorem targetUpperConstructionFiveSixteenEventually_verified :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    ClosedChainReduction.targetUpperConstructionFiveSixteenEventually_of_eventualExplicitClosedPlacementCertificates
      closedChainThreshold
      (fun k hlarge hk =>
        exists_explicitClosedPlacementCertificate_large k hlarge hk)
```

  - Next action: build macro-step certificates, express every large `k` by the
    macro lengths, close cyclic displacement, prove global separation, and
    package the resulting orbit through `ClosedChainExistence`.

- [ ] Optionally prove all-small exact-chain certificates.
  - Needed only for the stronger all-`k` / all-`n` theorem.
  - Target:

```lean
theorem exactChainUpper_small
    (k : Nat) (hk : 0 < k) (hsmall : k < closedChainThreshold) :
    SplitSoundness.ExactChainUpper k

noncomputable def exactChainSmallCaseCertificates_all :
    SmallCaseReduction.ExactChainSmallCaseCertificates
      (16 * closedChainThreshold) := by
  sorry
```

  - Next action: either explicitly construct finite small placements or do not
    claim the all-`n` Pach-Toth theorem.

- [ ] If choosing the stronger route, prove all-positive closed placement
  certificates.
  - Stronger target:

```lean
theorem exists_explicitClosedPlacementCertificate
    (k : Nat) (hk : 0 < k) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk
```

  - Next action: combine the large construction with the small certificates.

#### P5. Route placements to exact and arbitrary targets

- [x] Add small-case and split-realization routing modules.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SmallCaseReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SmallCaseCertificates.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SplitArbitraryNNonRigidBridge.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SplitRealizationClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SplitRealizationFinal.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeometricSoundness.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PlacementBridge.lean`.
  - Current state: imported, build-checked, and scan-clean.
    `SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_sixteen`
    discharges the target for `n < 16` via the translated-remainder route.
    `SplitRealizationClosure` packages supplied generated closed-chain data
    with explicit far-apart split realization data.
  - Conditional status: this does not supply the eventual large generated
    closed chains / large closed-placement data.  The remainder far-apart
    routing is checked; the missing input is the generated-chain global
    separation and closed-placement family, not a new remainder construction.

- [x] Prove the eventual target from large certificates.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedChainReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/EventualReduction.lean`.
  - Checked theorems:

```lean
theorem targetUpperConstructionFiveSixteenEventually_of_eventualExplicitClosedPlacementCertificates
    (K0 : Nat)
    (Hclosed :
      forall (k : Nat), K0 <= k -> forall hk : 0 < k,
        ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk) :
    targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary_of_eventualExplicitClosedPlacement_and_small
```

  - Current state: exact chains from eventual explicit certificates plus the
    existing translated remainder route give an eventual target; finite
    small-case coverage then routes to the arbitrary-`n` target.  The large
    certificates and any finite cases beyond the proved `n < 16` window remain
    open geometry/data.

- [ ] Prove the exact `16 * k` target if all-positive certificates are supplied.
  - Target theorem:

```lean
theorem targetUpperConstructionFiveSixteen_verified :
    targetUpperConstructionFiveSixteen
```

  - Next action: apply
    `ClosedChainReduction.targetUpperConstructionFiveSixteen_of_explicitClosedPlacementCertificates`.

- [ ] Prove the arbitrary all-`n` target only after the large route and
  threshold-matching small cases are supplied.
  - Target theorem:

```lean
theorem targetUpperConstructionFiveSixteenArbitrary_verified :
    targetUpperConstructionFiveSixteenArbitrary
```

  - Next action: combine the eventual large route with the checked
    `SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_sixteen`
    if the threshold is `16`, or extend the small-case certificate up to the
    eventual threshold.

#### P6. Add public Pach-Toth wrappers

- [ ] Add the source-faithful eventual wrapper first.
  - File: `E:/Personal/Erdosproblems/1066/ErdosProblems1066/KnownBounds.lean`.
  - Target theorem:

```lean
theorem upper_construction_five_sixteen_eventual :
    exists N0 : Nat, forall n : Nat, N0 <= n ->
      exists C : UDConfig n,
        forall s : Finset (Fin n), C.IsIndep s ->
          s.card <= PachToth.Arithmetic.ceilDiv (5 * n) 16
```

- [ ] Add exact and arbitrary all-`n` wrappers only if the matching internal
  verified targets are closed.
  - Target theorem names:

```lean
theorem upper_construction_five_sixteen_exact
theorem upper_construction_five_sixteen
```

  - Next action: keep these wrappers absent until
    `targetUpperConstructionFiveSixteen_verified` and
    `targetUpperConstructionFiveSixteenArbitrary_verified` are closed.

## Mathlib Landing Points

Use Mathlib for:

- finite graph bridge, induced graphs, independence, walks/cycles:
  `Mathlib.Combinatorics.SimpleGraph.Basic`,
  `Mathlib.Combinatorics.SimpleGraph.Maps`,
  `Mathlib.Combinatorics.SimpleGraph.Subgraph`,
  `Mathlib.Combinatorics.SimpleGraph.Finite`,
  `Mathlib.Combinatorics.SimpleGraph.Clique`,
  `Mathlib.Combinatorics.SimpleGraph.Walks.Basic`,
  `Mathlib.Combinatorics.SimpleGraph.Paths`,
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`;
- polygon and betweenness primitives:
  `Mathlib.Geometry.Polygon.Basic`,
  `Mathlib.Analysis.Convex.Between`;
- Euclidean angle/trig facts:
  `Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine`,
  `Mathlib.Geometry.Euclidean.Angle.Oriented.Affine`,
  `Mathlib.Geometry.Euclidean.Triangle`,
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`;
- finite cardinal and cyclic-index plumbing:
  `Mathlib.Data.Finset.Card`,
  `Mathlib.Data.Fintype.Card`,
  `Mathlib.Algebra.BigOperators.Fin`,
  `Mathlib.Logic.Equiv.Fin.Rotate`.

Do not expect Mathlib to provide the Swanepoel planar outer-face/Jordan
construction or the Pach-Toth non-rigid closed-chain construction.  Those are
project-local proof obligations.

## Final Completion Gates

- [x] Every `.lean` source file under
  `E:/Personal/Erdosproblems/1066/ErdosProblems1066` is imported by
  `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`.
  - Current coverage: 213 imported modules for 213 Lean files.
- [x] Pinned build succeeds.
  - Current command succeeded for the root target with 8240 jobs.
- [x] Forbidden-token scan is clean over `ErdosProblems1066` and
  `ErdosProblems1066.lean`.
- [x] CI-style axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
  - Current audit: passed for 374 declarations after the current interface
    wave was imported, build-checked, and scan-checked.
- [x] `KnownBounds.lean` exposes only the theorems actually closed in Lean.
  - Next action: add no new public wrappers until the matching internal
    `*_verified` theorem exists and builds.
