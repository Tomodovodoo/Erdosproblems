# Global Task Tracker

This is the living completion plan for the Lean formalization of Erdos problem
1066.  Keep it as an executable checklist: every open item names the current
state, the exact Lean target, and the next action needed to mark it off.

Ground rule: mark a task `DONE` only after the relevant Lean declarations are
imported by `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, compile
with the pinned toolchain, and pass the forbidden-token scan.  Conditional
bridges are progress, but they are not final theorem completion until their
hypotheses are discharged.

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
Build completed successfully (8197 jobs).

Lean source forbidden-token scan over ErdosProblems1066/ and
ErdosProblems1066.lean: clean.

Root import coverage: 170 imported modules for 170 Lean files under
ErdosProblems1066/.

CI-style axiom audit: passed for 250 declarations; every checked declaration
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
    `PachToth.IndexedCrossBlockTableConcrete`,
    `PachToth.CrossBlockDistanceSqReduction`,
    `PachToth.ClosedPlacementNonRigidComponents`,
    `PachToth.PeriodWordCertificates`, and
    `PachToth.TranslatedEquationObstruction`.
  - Recent Swanepoel M8 assembly modules imported:
    `Swanepoel.M8ConstructionDataBridge`,
    `Swanepoel.MinimalFailureComponentPackage`,
    `Swanepoel.M8TurnWindowNoEarlyFinal`,
    `Swanepoel.BoundaryFaceCountingToM8`,
    `Swanepoel.BoundaryLabelExtractionTasks`,
    `Swanepoel.CutVertexSlackFromDeletion`,
    `Swanepoel.JordanBoundaryExtraction`, and
    `Swanepoel.Lemma8CombinatoricsConcrete`.
  - Current root target build succeeds and root import coverage is complete:
    170 imported package modules for 170 Lean files under
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/`.

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
    `Swanepoel.PlanarBoundaryClosure`, and
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

- [ ] Prove no cut vertex without extra conditional data.
  - Target declaration:

```lean
theorem unitDistanceSimpleGraph_noCutVertex_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C
```

  - Next action: either construct the uniform
    `CutVertexClosure.AllCutVertexSlackGluingData` package from honest
    cut-vertex geometry, or replace the conditional route by a direct proof.

- [x] Add connectedness-plus-conditional cut-vertex closure adapter.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexFromConnectedness.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    axiom audit.  It combines checked connectedness extraction, the
    conditional all-cut-vertex slack package, and the minimal-failure degree
    range into `ConnectedNoCutVertexCertificate`.
  - Conditional status: this still does not prove the all-cut-vertex slack
    package from minimality; that is the remaining no-cut payload.

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

- [ ] Construct `OuterBoundaryCore` from a minimal cleared failure.
  - Next action: construct this using S3 plus the checked noncrossing
    straight-line graph.  Mathlib has useful
    `SimpleGraph.Walk`, `Walk.IsCycle`, `Polygon`, `Wbtw`, `Sbtw`, but no
    ready planar-face/Jordan theorem; the face construction is project-local.

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
  - Next action: define count functions from the actual boundary data and
    prove they match the fields consumed by `BoundaryCounting`.

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
  - Next action: define subpolygon counts from the induced graph and prove the
    degree range needed by the existing low-degree inequality.

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
  - Target theorem:

```lean
theorem boundaryCounts_angleLowerBound_of_outerBoundary
    (P : BoundaryTurnPackage G) :
    P.counts.AngleLowerBound
```

  - Next action: use polygon interior-angle sum plus local triangle angle
    facts to feed `BoundaryCounts.boundary_angle_count_inequality`.

- [ ] Prove subpolygon angle lower bound.
  - Target theorem:

```lean
theorem subpolygonCounts_angleLowerBound_of_subpolygon
    (Q : HonestSubpolygon G) :
    Q.counts.AngleLowerBound
```

  - Next action: mirror the outer-boundary angle proof for induced subpolygons
    and feed `SubpolygonDegreeCounts.subpolygon_low_degree_inequality`.

#### S6. Formalize Swanepoel Lemmas 6, 7, 5, 8, and 9

- [ ] Prove Lemma 6 / forced negative after a gap.
  - Best home: new `LongArc.lean`.
  - Next action: express the paper's gap condition using the computed boundary
    arc package and apply S5 subpolygon contradictions.

- [ ] Prove Lemma 7 / degree-three gap induction.
  - Best home: `LongArc.lean`.
  - Next action: turn repeated Lemma 6 applications into the induction used by
    the nonconcave long-arc argument.

- [ ] Prove Lemma 5 / existence of nonconcave long arc for `m = 8`.
  - Best home: `LongArc.lean`.
  - Next action: package the turn function, nonnegativity, and
    `totalTurn turn < Real.pi / 3`.

- [ ] Prove Lemma 8 / construction of the `r_i, s_i` witnesses.
  - Best home: new `BrokenLattice.lean`.
  - Next action: use the long-arc package and local boundary classification to
    construct the broken-lattice labels.

- [ ] Prove Lemma 9 / late triples.
  - Best home: `BrokenLattice.lean`.
  - Next action: show any triple equality in the honest `m = 8` label package
    starts late enough to satisfy `P.LateTriples`.

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
  - Existing data structure:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/AngleBridgeFacts.lean`.
  - Target theorem:

```lean
theorem figure8_distance_data_of_failed_separated :
  ...
```

  - Next action: map the broken-lattice witnesses into
    `Figure8DistanceData`.

- [ ] Prove Figure 8 central-angle containment.
  - Best home: new `AngleContainment.lean`.
  - Target field:
    `Figure8SeparatedAngleToTurnBridge.central_angle_le_separatedTurn`.
  - Next action: prove the oriented angle lies inside the separated turn
    window.  The local `pi / 3` angle lower bound is already checked.

- [ ] Extract Figure 9 distance data from failed adjacent labels.
  - Target theorem:

```lean
theorem figure9_distance_data_of_failed_adjacent :
  ...
```

  - Next action: map adjacent failed labels into `Figure9DistanceData`.

- [ ] Prove Figure 9 left-angle containment.
  - Best home: `AngleContainment.lean`.
  - Target field:
    `Figure9AdjacentLeftAngleToTurnBridge.left_angle_le_adjacentTurn`.
  - Next action: prove the oriented Figure 9 angle lies inside the adjacent
    three-turn window, then package the field with the distance data from the
    previous item.

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

  - Next action: either construct `Figure8SeparatedAngleToTurnBridge` and
    `Figure9AdjacentLeftAngleToTurnBridge`, or use the newer
    `Lemma10WindowGeometry` wrappers directly from extracted distance data and
    window-containment lemmas.

- [x] Add containment-to-M8 window geometry adapter.
  - File:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8WindowGeometryFromContainment.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    axiom audit.  It repackages supplied Figure 8/Figure 9 containment
    interfaces into the window-geometry fields consumed by
    `M8ConstructionInterface`.
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
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8LateTriplesFromNoEarly.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8MinimalFailureEliminatorInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/FinalConditional.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    axiom audit.  These files package the structural boundary/no-cut/degree
    context, explicit Lemma 8 labels, nonconcave-arc turn data, no-early
    triple exclusions, and final separated M8 eliminator into the current
    conditional Swanepoel target route.
  - Conditional status: the paper Lemma 8 combinatorics, nonconcave arc,
    no-early-triple proof, containment data, and separated M8 construction
    fields still must be constructed from an actual minimal cleared failure.

- [x] Add concrete M8 assembly and reducer modules.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8ConstructionDataBridge.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureComponentPackage.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnWindowNoEarlyFinal.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryFaceCountingToM8.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BoundaryLabelExtractionTasks.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexSlackFromDeletion.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/JordanBoundaryExtraction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma8CombinatoricsConcrete.lean`.
  - Current state: imported, build-checked, scan-clean, and representative
    declarations are covered by the axiom audit.
  - Current purpose: the remaining Swanepoel construction has been narrowed to
    the explicit `MinimalFailureM8PaperFacts` fields: positive cardinality,
    cut-vertex slack, planar boundary/Jordan data, the M8 boundary spine,
    Lemma 8 extra-neighbor combinatorics, nonconcave-arc turn data, no-early
    triples, and Figure 8/Figure 9 containment.
  - Conditional status: these fields are still paper facts to prove, not
    completed Lean constructions.

- [ ] Prove the minimal-failure `m = 8` construction eliminator.
  - Existing conditional home:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BrokenLatticeMinimalFailure.lean`.
  - Checked target shape now consumed by the closure:

```lean
def MinimalFailureM8ConstructionEliminator : Prop :=
  forall {n : Nat} (C : UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin)
```

  - Equivalent data still to construct for each minimal cleared failure:

```lean
theorem BrokenLatticePipeline.exists_m8_honestLocalPredicates_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    Exists fun P : Lemma10Bridge.M8HonestLocalPredicates
        (GraphBridge.unitDistanceLocalGraph C) =>
      Exists fun turn : Nat -> Real =>
        (forall k : Nat, 0 <= turn k) /\
        Lemma10Inequalities.totalTurn turn < Real.pi / 3 /\
        P.LateTriples /\
        Lemma10AnalyticBridge.HonestFigure8SeparatedWindowLowerE22 P turn /\
        Lemma10AnalyticBridge.HonestFigure9AdjacentWindowLowerE23 P turn
```

  - Next action: combine S4-S7 into the `M8ConstructionData` package, then
    apply `M8ConstructionDataBridge.separatedConstructionEliminator_of_constructionDataEliminator`
    or `MinimalFailureComponentPackage.MinimalFailureM8PaperFactsFamily.targetLowerBoundEightThirtyOne`.

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

- [x] Add an eventual public/internal target.
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

- [ ] For a proof-sufficient Lean construction, state the theorem in terms of
  the current relations.
  - Same-block relation:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FiniteGraph.lean`.
  - Cross-block relation:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlock.lean`.
  - Next action: make public wording avoid claiming a full Figure 2 edge-table
    transcription unless P2 source-faithful items below are proved.

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
  - Needed data:
    primitive side table, same-block edge projection to `FiniteGraph.adj`,
    orientation-indexed next-block relation or projection to
    `CrossBlock.NextConnector`, `p/q` roles, farthest-vertex roles, and
    no-duplicate/no-gap theorems.
  - Next action: encode only the proof-used edge subset first, then decide
    whether a complete table is necessary for the public claim.

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

- [ ] Build concrete hinged same/opposite transition data.
  - Target shape:

```lean
def concreteSameOppositeTransitionRealization :
  BaseTransitionRealization.BaseSameOppositeTransitionRealization
```

  - Next action: choose the role angles and transition maps, prove same-block
    distance preservation for each next block, and discharge the connector
    role equations through the hinge lemmas.

- [x] Add non-rigid/role-hinged transition and closed-placement wrappers.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeTransitionSearch.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/NonRigidClosedPlacementInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedPlacementNonRigidComponents.lean`.
  - Current state: imported, build-checked, scan-clean, and representative
    declarations are covered by the axiom audit.
  - Current purpose: these modules route explicit non-rigid point/orbit
    fields and role-hinged transition facts to closed placements, exact-block
    targets, and exact-family targets without using the contradictory
    translated four-equation data.
  - Conditional status: concrete role-angle maps, same-block preservation,
    successor connector unit edges, and global separation are still fields to
    prove.

- [ ] Prove same-block unit edges for the hinged block.
  - Target theorem:

```lean
theorem hingedBlock_same_edges_unit :
  ...
```

  - Next action: case-split over `FiniteGraph.adj` and discharge each edge by
    exact trig/vector algebra.

- [ ] Prove connector-port unit edges.
  - Target theorem:

```lean
theorem hingedBlock_connector_ports_unit :
  ...
```

  - Next action: show the four connector equations are equilateral completions
    of the chosen input/output ports.

- [ ] Build same/opposite transition maps, or bypass them with direct
  certificates.
  - Existing conditional interface:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/Figure2Certificate.lean`.
  - Target declaration if using the interface:

```lean
def concreteSameOppositeTransitionObligations :
  Figure2Certificate.SameOppositeTransitionObligations
```

  - Current state: `HingedTransitionInterface.toFigure2TransitionObligations`
    and `BaseTransitionRealization.toFigure2TransitionObligations` route a
    supplied metric realization into the existing Figure 2 transition
    obligations.
  - Next action: instantiate the supplied metric realization; global
    separation and period closure still remain separate obligations.

#### P4. Construct closed placements

- [x] Add generated closed-chain packaging and reduction plumbing.
  - Files:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChain.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedClosedChainReduction.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedSeparationInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodInterface.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeneratedPeriodClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/ClosedPlacementClosure.lean`.
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
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/CrossBlockDistanceSqReduction.lean`.
  - Current state: imported, build-checked, scan-clean, and representative
    declarations are covered by the axiom audit.
  - Current purpose: period words/equations and finite indexed cross-block
    inequalities now have direct table-style Lean surfaces, including a
    squared-distance reducer for generated cross-block lower bounds.
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
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PeriodCertificateExamples.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FinalConditional.lean`.
  - Current state: imported, build-checked, scan-clean, and covered by the
    axiom audit.  The files route explicit connector equations, same-block
    distance preservation, finite period-search certificates, and quantitative
    cross-block lower-bound tables into the strongest current conditional
    Pach-Toth exact/arbitrary target facades.
  - Conditional status: they still require actual same/opposite transition
    data, period certificates, and cross-block lower-bound inequalities.

- [ ] Prove sufficiently-large closed placement certificates.
  - Best home: `ClosedChainExistence.lean`.
  - Source-faithful target:

```lean
def closedChainThreshold : Nat

theorem exists_explicitClosedPlacementCertificate_large
    (k : Nat) (hk : 0 < k) (hlarge : closedChainThreshold <= k) :
    ClosedPlacementInterface.ExplicitClosedPlacementCertificate k hk
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
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/SplitRealizationClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/GeometricSoundness.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/PlacementBridge.lean`.
  - Current state: imported, build-checked, and scan-clean.
    `SmallCaseCertificates.targetUpperConstructionFiveSixteenSmallUpTo_sixteen`
    discharges the target for `n < 16` via the translated-remainder route.
    `SplitRealizationClosure` packages supplied generated closed-chain data
    with explicit far-apart split realization data.
  - Conditional status: this does not supply the eventual large generated
    closed chains or the global far-apart placements for arbitrary large `n`.

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
  - Current coverage: 142 imported modules for 142 Lean files.
- [x] Pinned build succeeds.
  - Current command succeeded for the root target with 8169 jobs.
- [x] Forbidden-token scan is clean over `ErdosProblems1066` and
  `ErdosProblems1066.lean`.
- [x] CI-style axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
  - Current audit: passed for 216 declarations after the current interface
    wave was imported, build-checked, and scan-checked.
- [x] `KnownBounds.lean` exposes only the theorems actually closed in Lean.
  - Next action: add no new public wrappers until the matching internal
    `*_verified` theorem exists and builds.
