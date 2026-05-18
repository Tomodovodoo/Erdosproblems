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
elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066
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
Build completed successfully (8850 jobs).

Lean source forbidden-token scan over ErdosProblems1066/ and
ErdosProblems1066.lean: clean.

Root import coverage: 823 imported modules for 823 Lean files under
ErdosProblems1066/.  No missing, extra, or duplicate root imports.

Trust-source scan for `native_decide`, `trustCompiler`, and `ofReduceBool`:
clean.

CI-style dependency audit: passed for 1127 declarations, including W13-W31
endpoint and gate declarations.  Every checked declaration reports only
Lean/mathlib base axioms `propext`, `Classical.choice`, and `Quot.sound`.
W18-W31 endpoint declarations are imported, build-clean, source-scan clean,
trust-source clean, and represented in the CI-style declaration list.

Encoding hygiene is not a proof-state gate.  A broad marker scan reports older
legacy non-ASCII/mojibake-looking text, so do not use encoding hygiene as
evidence for or against the current certified bounds route.
```

## Active Snapshot

- [x] W13 through W31 route and source-package layers are integrated and root-imported.
  - Current coverage: 823 imported package modules for 823 Lean files.
  - Current root target build succeeds with 8850 jobs under
    `leanprover/lean4:v4.28.0`.
  - Lean-source forbidden-token and trust-source scans are clean.
  - The W15-W31 final-gate modules are conditional gates, not
    unconditional final closures.

- [x] W16 proof wave is integrated.
  - W16 ownership map:
    `PayForCutArithmeticW16`, `NoCutFromMinimalityW16`,
    `BoundaryArcFiniteWalkConstructionW16`, `BoundaryTopologyArcBridgeW16`,
    `Figure8WindowContainmentW16`, `Figure9WindowContainmentW16`,
    `Lemma8LocalLabelsW16`, `Lemma9LateTriplesW16`,
    `LongArcFactsSelectionW16`, `TailPolynomialRowsW16`,
    `SmallRowsTwoThreeW16`, `SmallRowsFourFiveW16`,
    `PeriodBaseFixingSameW16`, `PeriodBaseFixingOppositeW16`,
    `PeriodBaseFixingCertificateW16`, `LargeKGlobalSeparationW16`,
    `SmallComplementExactBlocksW16`, and
    `EventualClosedPlacementCertificateW16`.
  - W16 audit result:
    keep W16 focused on concrete input rows and local package fields.  The
    W15 final gates are endpoint bookkeeping until their concrete blockers are
    supplied, and `Verified`-namespace conditional wrappers are not completion
    evidence.
  - W16 verification:
    current root build passes at 8830 jobs; coverage is 803/803;
    forbidden-token scan, trust-source scan, and 1106-declaration dependency
    audit pass.
  - W16 status:
    the new modules are checked reducers/adapters, not unconditional final
    theorem closures.  Swanepoel still needs a uniform construction of the
    concrete pointwise remaining input rows.  Pach--Toth still needs viable
    transition/base-fixing data and concrete inequality/certificate rows rather
    than only conditional adapter surfaces.

- [x] W17 concrete interface surface is integrated and root-imported.
  - Swanepoel W17 modules:
    `BoundaryBudgetLongArcConcreteW17`, `FigureWitnessConcreteAssemblyW17`,
    `Lemma8FiniteDataConstructionW17`, `Lemma9CoverageConcreteW17`,
    `PayForCutConcreteInequalityW17`, `PointwiseRemainingRowAssemblyW17`,
    `SwanepoelConcreteBlockerLedgerW17`, `SwanepoelUniformFamilyGateW17`,
    `TopologyTrianglePipelineW17`, and `TriangleRunSelectorW17`.
  - Pach--Toth W17 modules:
    `AllPositiveFinalCertificateW17`, `BaseFixingRowsViableW17`,
    `LargeK0ExplicitSeparationDataW17`, `PachTothEventualFinalGateW17`,
    `SmallComplementConcreteBlocksW17`, `SmallRowValueCertificatesW17`,
    `TailValueCertificateConcreteW17`, and `ViableTransitionPackageW17`.
  - W17 status:
    these are rooted reducer/adapter surfaces over the W16/W15 gates.  They do
    not yet make the Swanepoel 8/31 or Pach--Toth 5/16 bounds public
    unconditional `KnownBounds` theorems.

- [x] W17 concrete final-input lane is integrated.
  - W17 completed the rooted adapter/reducer layer feeding W16 and W15.
    Every W17 file is imported by `ErdosProblems1066.lean`, targeted-checked,
    source-scan clean, included in the current 8830-job root build, and
    represented in the 1106-declaration dependency audit.
  - W17 does not close the final paper bounds unconditionally.  It sharpens the
    remaining work to inhabiting concrete input packages rather than proving
    more endpoint wrappers.

- [x] W18 concrete input-production surface is integrated and root-imported.
  - W18 modules now build through the root target and route into the W17/W16
    packages.  W18 is still conditional plumbing: it does not prove the final
    Swanepoel or Pach--Toth public bounds without the W19 concrete closure
    inputs below.

- [x] W19 closure surface is integrated and root-imported.
  - Swanepoel W19 modules:
    `AngleContainmentBridgeProducerW19`, `BoundaryFrameCoreProducerW19`,
    `FigureWitnessClosureW19`, `Lemma8ConcreteGeometryProducerW19`,
    `Lemma9NatLateTripleProducerW19`, `NoCutMinimalityClosureW19`,
    `PointwiseAssemblyClosureW19`, `PositiveCyclicOrderProducerW19`,
    `SwanepoelFinalClosureW19`, and `TopologyArcClosureW19`.
  - Pach--Toth W19 modules:
    `ArbitraryNClosedPlacementRouteW19`, `ClosedPlacementCrossConnectorEdgesW19`,
    `ClosedPlacementObstructionBypassW19`, `ClosedPlacementSameBlockEdgesW19`,
    `ClosedPlacementSeparationW19`, `ClosedPlacementSmallKCertificatesW19`,
    `ClosedPlacementTargetWrappersW19`, `ExplicitClosedPlacementProducerW19`,
    `NonRigidClosedPlacementDataW19`, and `PachTothClosedPlacementAuditW19`.
  - W19 status:
    these are rooted closure/adaptor surfaces.  They expose the exact remaining
    concrete input packages, but `KnownBounds.lean` is still intentionally not
    extended to the two requested public bounds.

- [x] W20 source-package and audit surface is integrated and root-imported.
  - Pach--Toth W20 modules:
    `ClosedPlacementCIEndpointsW20`, `ClosedPlacementUnconditionalAttemptW20`,
    `ExplicitClosedPlacementInputPackageW20`, `GeneratedChainClosureProducerW20`,
    `GeneratedChainFamilyProducerW20`, `GeneratedMetricAuditW20`,
    `LargeKClosedPlacementSourceW20`, `PachTothFinalRouteW20`,
    `ReducedMetricHypothesesProducerW20`, and
    `SmallKClosedPlacementSourceW20`.
  - Swanepoel W20 modules:
    `FigureProducerFamilyW20`, `Lemma8ProducerFamilyW20`,
    `Lemma9ProducerFamilyW20`, `PayForCutProducerFamilyW20`,
    `PointwiseProducerFamilyFieldsW20`, `RemainingObligationLedgerW20`,
    `SwanepoelCIEndpointsW20`, `SwanepoelSourcePackageW20`,
    `SwanepoelUnconditionalAttemptW20`, and `TopologyArcProducerFamilyW20`.
  - W20 status:
    the project now has checked source-package adapters and audit endpoints for
    the W19 final closures.  It does not yet have unconditional inhabitants of
    those source packages, so `KnownBounds.lean` must not expose the requested
    `8 / 31` or `5 / 16` paper bounds.

- [x] W21 source-package and KnownBounds-gate surface is integrated and root-imported.
  - Pach--Toth W21 modules package the generated-chain source route, concrete
    value-matrix adapters, period/base/large-small source fields, and the
    closed-placement KnownBounds exposure gate.
  - Swanepoel W21 modules package the no-cut, topology, Lemma 8, Lemma 9,
    figure-angle, remaining-field, boundary-topology, broken-lattice, and
    Swanepoel KnownBounds exposure surfaces.
  - W21 status:
    the files are imported by the root, build-clean, forbidden-token clean, and
    trust-source clean.  They still reduce the final public bounds to concrete
    source-package inhabitants; they do not close the requested public
    `KnownBounds` wrappers.

- [x] W22 source-inhabitation audit surface is integrated and root-imported.
  - Pach--Toth W22 modules expose the value-matrix, source-field,
    remaining-separation, small-complement, arbitrary-`n`, and dependency-audit
    surfaces for the W21/W20 route.
  - Swanepoel W22 modules expose the no-cut, topology, Lemma 8, Lemma 9,
    figure-angle, geometry-closure, remaining-source, M8 blocker, and final
    KnownBounds source-component surfaces.
  - W22 status:
    all 20 W22 files are root-imported, build-clean, forbidden-token clean,
    trust-source clean, and represented in the 1106-declaration CI-style axiom
    audit.  They remain conditional source-package surfaces.

- [x] W23 concrete route/audit surface is integrated and root-imported.
  - Pach--Toth W23 modules route concrete value-matrix rows, generated-chain
    closure/source fields, base-fixing, separation, small-length targets, and
    KnownBounds-from-rows/audit wrappers.
  - Swanepoel W23 modules route concrete no-cut, topology/Jordan, Lemma 8,
    Lemma 9, figure-angle, M8 component lanes, lane-product, KnownBounds, and
    route-audit wrappers.
  - W23 status:
    all 20 W23 files are root-imported and represented in the current
    CI-style axiom audit.  They are conditional route surfaces, not final
    unconditional public-bound closures.

- [x] W24 concrete source-package/audit surface is integrated and root-imported.
  - Pach--Toth W24 modules expose role-free alternative value-matrix routes,
    direct cross-block/full-metric/free-placement packages, non-role period
    routes, concrete remainder split bridges, route obstruction facts, and
    small-length exact target surfaces.
  - Swanepoel W24 modules expose no-cut blocker elimination, Jordan boundary
    witness data, Lemma 8 frame/order bridges, Lemma 9 no-early packages,
    figure-angle E22/E23 bridges, minimal still-open components, lane-product
    assembly, and W20 source-package concrete bridges.
  - W24 status:
    all W24 files are root-imported, build-clean, forbidden-token clean,
    trust-source clean, and represented in the 1106-declaration CI-style axiom
    audit.  They remain conditional source-package surfaces.

- [x] W25 source-inhabitation/audit surface is integrated and root-imported.
  - Pach--Toth W25 modules add generated-closure metric packages,
    same-family closure sources, reduced-metric fields, free-placement field
    equivalences, non-role split sources, appended-remainder separation,
    direct full-metric source packages, closed-placement witness assembly, and
    W25 route-audit endpoints.
  - Swanepoel W25 modules add cut-vertex contradiction equivalences,
    minimal boundary-topology witness inhabitation, Lemma 8 frame rows, Lemma
    9 no-early obstruction packages, selected figure witnesses, concrete W23
    component assembly, lane-product final gates, pointwise source-field
    bridges, planar topology extraction bridges, and W25 route-audit
    endpoints.
  - W25 verification:
    root build passes at 8830 jobs; coverage is 803/803; forbidden-token scan,
    trust-source scan, and the 1106-declaration dependency audit pass.
  - W25 status:
    W25 narrows the remaining proof obligations and adds checked
    equivalence/adapter layers.  It does not yet close Swanepoel 8/31 or
    Pach--Toth 5/16 as unconditional public `KnownBounds` theorems.

- [ ] Concrete source-inhabitation beyond W30 is live.
  - Swanepoel target:
    produce an actual
    `Swanepoel.SwanepoelW30FinalAssembly.FinalSourceGate`,
    `Swanepoel.SwanepoelW30FinalAssembly.LaneProductSourceAlternatives`, or
    `Swanepoel.PointwiseProductDataClosureW30.SourceData`,
    and route it through the W30 final-source gate without target-to-source
    shortcuts.
  - Pach--Toth target:
    do not target the W27 role-hinged
    `ConcreteNonConnectorLowerTableFamily` alias as a live source; W27 proves
    that lane blocked.  Produce actual W30 generated-closure/completion-row
    data, `PachToth.PositiveChainComponentClosureW30.ExactPositiveChainComponentData`,
    `PachToth.LargeTailCertificateRowsW30.LargeTailCertificateRows`, or
    `PachToth.RemainderExactDependencyClosureW30.RemainderSplitExactSourcePackage`,
    and route it through the W30 exact/arbitrary source gates.
  - Completion gate:
    root-imported declarations build with the pinned toolchain; root coverage
    is complete; forbidden-token and trust-source scans are clean; endpoint
    declarations are added to the CI-style axiom audit and report only
    Lean/mathlib base axioms; public `KnownBounds` wrappers are added only
    after the matching internal `*_verified` theorem exists and builds.

- [x] W26 parallel proof wave is integrated and audited.
  - Pach--Toth workers:
    `DirectReducedMetricInputW26`,
    `NonRoleSplitSourceConstructionW26`,
    `ClosedPlacementConcreteConstructionW26`,
    `FullToReducedMetricClosureW26`,
    `ArbitraryNFinalAssemblyW26`,
    `PositiveExactChainPackageW26`,
    `ConcreteReducedMetricCertificatesW26`,
    `PachTothW26RouteAudit`, and
    `ExactTargetClosureW26`.
  - Swanepoel workers:
    `NoCutConcreteEliminationW26`,
    `ConcreteW23ComponentsInhabitationW26`,
    `PlanarTopologyActualExtractionW26`,
    `Lemma8FrameRowsConstructionW26`,
    `Lemma9NoEarlyConstructionW26`,
    `FigureWitnessConstructionW26`,
    `BoundaryWitnessRemainingFieldsW26`,
    `SwanepoelW26FinalAssembly`, and
    `BrokenLatticeMinimalFailureConstructionW26`.
  - Read-only auditors:
    Lean proof-surface/no-axiom practice audit and Mathlib route audit.
  - W26 agent inventory is condensed after verification; the checked artifacts
    above are the durable handoff.
  - W26 verification:
    all W26 files are root-imported.  The root build succeeds at 8830 jobs;
    root import coverage is 803/803; forbidden-token scan and trust-source
    scan are clean; the expanded CI-style axiom audit passes for 1106
    declarations.
  - W26 status:
    W26 closes several missing-field adapters and exact dependency
    equivalences.  Pach--Toth now has checked reduced-metric/full-metric
    handoffs and exact/arbitrary target equivalences, but still needs an
    actual concrete lower-table/full-metric/free-placement source rather than
    target repackaging.  Swanepoel now has no-cut, topology, Lemma 8, Lemma 9,
    figure, boundary-witness, concrete-component, broken-lattice, and final
    assembly adapters, but still needs actual inhabitants of the concrete
    component/source packages before a public unconditional `8 / 31` wrapper
    may be added.

- [x] W27 concrete source/audit wave is integrated and audited.
  - Pach--Toth W27 modules:
    concrete closed-orbit/squared-distance adapters, blocked lower-table audit,
    direct full-metric source construction, finite reduced-metric certificates,
    free-placement fields, positive exact-chain assembly, large-tail blockers,
    remainder exact sources, and W27 route/final assembly.
  - Swanepoel W27 modules:
    actual selected topology, boundary components, cut/pay-for-cut fields,
    figure witnesses, lane product, Lemma 8 geometry, Lemma 9 source families,
    no-cut local deletion, pointwise source fields, and W27 final assembly.
  - W27 verification:
    all W27 files are root-imported.  The root build succeeds at 8830 jobs;
    root import coverage is 803/803; forbidden-token and trust-source scans
    are clean; the expanded CI-style axiom audit passes for 1106 declarations.
  - W27 status:
    Swanepoel made real conditional source-package progress.  Pach--Toth also
    added useful W27 assembly and obstruction data, but the role-hinged lower
    table alias is proved blocked and must not be treated as the live source
    construction route.

- [x] W28 source-inhabitation/audit wave is integrated and audited.
  - Pach--Toth W28 modules:
    alternative non-role sources, generated-closure metrics, squared-orbit
    closure, large-tail exact-source blockers, positive-chain components,
    remainder split exact sources, finite-row no-go audit, exact/arbitrary
    source assembly, route audit, and final assembly.
  - Swanepoel W28 modules:
    no-cut source construction, side-card/pay-for-cut source fields, outer
    boundary core construction, selected-face witnesses, Lemma 8 finite
    geometry rows, Lemma 9 no-early rows, exact figure-angle sources,
    pointwise product blockers, lane-product final sources, and final assembly.
  - W28 verification:
    all W28 files are root-imported.  The current root build succeeds at 8830
    jobs; root import coverage is 803/803; forbidden-token and trust-source
    scans are clean; the expanded CI-style axiom audit passes for 1106
    declarations.
  - W28 status:
    W28 adds checked source packages and blocker equivalences.  It still does
    not close Swanepoel 8/31 or Pach--Toth 5/16 unconditionally, so public
    `KnownBounds` wrappers remain absent for those two bounds.

- [x] W29 source-inhabitation/audit wave is integrated and audited.
  - Pach--Toth W29 modules:
    completion-row sources, squared-orbit closure rows, large-tail fields,
    positive-chain component data, exact-chain family sources, remainder-split
    closure, closed-orbit branch assembly, no-fake audit, route audit, and
    final assembly.
  - Swanepoel W29 modules:
    outer-boundary source construction, extracted boundary witnesses, uniform
    finite geometry rows, concrete no-early source families, exact figure-angle
    data, pointwise product blockers, lane-product alternatives, no-cut blocker
    contradiction, route audit, and final assembly.
  - W29 verification:
    all W29 files are root-imported.  The root build succeeds at 8830 jobs;
    root import coverage is 803/803; forbidden-token and trust-source scans
    are clean; the expanded CI-style axiom audit passes for 1106 declarations.
  - W29 status:
    W29 fixes the previous pending blockers and gives the current live final
    gates.  It does not add public unconditional Swanepoel 8/31 or Pach--Toth
    5/16 `KnownBounds` wrappers, because the final gates still require actual
    source-package inhabitants.

- [x] W30 source-inhabitation/audit wave is integrated and audited.
  - Pach--Toth W30 modules:
    generated-closure metric rows, completion-row closure, closed-orbit branch
    sources, exact-chain family closure, positive-chain component closure,
    large-tail certificate rows, remainder exact-dependency closure, no-fake
    audit, route audit, and final assembly.
  - Swanepoel W30 modules:
    selected-face enclosure sources, extracted-witness components, frame/cyclic
    order rows, no-early route-data closure, exact figure inequalities,
    pointwise-product data closure, lane-product final closure, no-cut blocker
    elimination, route audit, and final assembly.
  - W30 verification:
    all W30 files are root-imported.  The root build succeeds at 8830 jobs;
    root import coverage is 803/803; forbidden-token and trust-source scans
    are clean; the expanded CI-style axiom audit passes for 1106 declarations.
  - W30 status:
    W30 fixed the pending W29/W30 compile/name blockers and is the current
    live final-gate layer.  It still does not add public unconditional
    Swanepoel 8/31 or Pach--Toth 5/16 `KnownBounds` wrappers, because actual
    source-package inhabitants are still required.

## Current Certified State

- [x] The imported project builds through the pinned Lean toolchain.
  - `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean` imports every
    Lean source module under `E:/Personal/Erdosproblems/1066/ErdosProblems1066`.
  - Current coverage: 803 imported package modules for 803 Lean files.
  - Current root target build succeeds with 8830 jobs.  W7/W8/W9/W10/W11/W12 route and matrix modules
    remain included, especially `PachTothRemainingMatrix`,
    `PachTothW8ClosureMatrix`, `ExactLocalTransitionObligationMatrix`,
    `SwanepoelRemainingMatrix`, `SwanepoelW8ClosureMatrix`,
    `M8RefinedInputConcrete`, `MinimalFailureConcreteDataMatrix`,
    `MinimalFailureDirectMatrixW10`, `GeometryRemainingFieldsW10`, and
    `SwanepoelW10ClosureMatrix`, plus the imported W11-W30
    closure, summary, gate, and certificate layers.

- [x] Third parallel proof wave is integrated.
  - Pach--Toth workers PT3-1--PT3-10 own:
    `RoleHingeConcreteSearch.lean`, `ConcretePeriodSearchFamily.lean`,
    `CrossBlockSqTableSearch.lean`, `FiniteCertificateObligationSummary.lean`,
    `ExactFiveSixteenRouteMatrix.lean`, `GeneratedSeparationFarApart.lean`,
    `SplitRealizationFinal.lean`, `NonRigidClosedPlacementInterface.lean`,
    `ClosedPlacementComponentsAssembly.lean`, and
    `SmallCaseCertificates.lean`.
  - Swanepoel workers SW3-1--SW3-10 own:
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

- [x] Fourth parallel proof wave is integrated.
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
  - Fourth-wave conditional bridges now integrated:
    `ConcretePeriodCandidateSearch` exposes the period-equation family plus
    lower-bound route under the current target spelling;
    `EventualRoleHingeClosure` exposes the eventual role-hinged closure route
    with exact-target small-case complement;
    `ExactFiveSixteenRouteMatrix` routes square-value certificates and
    reduced non-connector polynomial tables to the current conditional
    exact/arbitrary Pach--Toth facades; `BoundaryWalkConstruction` exposes a
    reusable long-arc contribution and planar-boundary count-realization
    projection; and `NonconcaveArcConcrete` exposes a finite long-arc count-gap
    selector that produces boundary-budget data and M8 turn bounds.
  - Refined remaining blockers: the conditional bridges above do not supply
    unconditional Pach--Toth `5 / 16` or Swanepoel `8 / 31` bounds.  Pach--Toth
    still needs actual same/opposite transition data, period
    certificates/equations, cross-block lower-bound inequalities, and the
    large/even-threshold closed-chain family.  Swanepoel still needs the
    honest boundary classifications/count gap from an actual outer boundary,
    Lemmas 6 and 7 as project-local geometry, and the final
    `NonconcaveArcGeometricAngleFacts` package.
  - Completion gate passed: completed workers were closed after completion,
    their touched modules received targeted pinned checks and source scans, and
    the root build, source scan, coverage scan, encoding scan, and CI-style
    axiom audit all passed after integration.

- [x] Fifth parallel proof wave is integrated.
  - Pach--Toth workers PT5-1--PT5-10 own concrete construction files:
    `RoleHingeTransitionSearch.lean`, `RoleHingeAngleCertificates.lean`,
    `PeriodWordCertificates.lean`, `PeriodCertificateExamples.lean`,
    `CrossBlockUpperTriangleConcrete.lean`,
    `IndexedCrossBlockTableConcrete.lean`, `SmallCaseCertificates.lean`,
    `EventualRoleHingeClosure.lean`, `NonRigidClosedPlacementInterface.lean`,
    and `GeneratedSeparationFarApart.lean`.
  - Swanepoel workers SW5-1--SW5-10 own concrete geometry/topology files:
    `JordanBoundaryConcrete.lean`, `PlanarBoundaryFinal.lean`,
    `BoundaryLabelExtractionTasks.lean`, `NonconcaveArcAngleFacts.lean`,
    `NonconcaveArcBudgetFromBoundary.lean`,
    `Lemma8NeighborExtractionConcrete.lean`,
    `NoEarlyTripleObstructionConcrete.lean`, `BrokenLatticePipeline.lean`,
    `MinimalGraphFacts.lean`, and `OuterBoundaryAssembly.lean`.
  - Fifth-wave results integrated: Pach--Toth now has explicit obstruction
    facts for the too-strong role-hinge transition package, equilateral
    role-angle exact-local bridges, all-positive and threshold period-word
    families, concrete upper-triangle/non-connector cross-block projections,
    generated reduced closed-placement routes, and small-case threshold
    plumbing.  Swanepoel now has stronger Jordan/topology equivalences,
    boundary-walk-to-face-counting bridges, boundary-label projections,
    Lemma 7 angle-to-turn projections, long-arc budget routes, Lemma 8
    extraction projections, no-early/K23 routes, broken-lattice fact
    constructors, minimal-failure closure wrappers, and outer-boundary count
    projections.
  - Completion gate passed: all completed workers were closed after
    completion; targeted pinned checks passed; root build, source scan,
    coverage scan, encoding scan, diff whitespace check, and CI-style axiom
    audit passed.

- [x] Sixth parallel proof wave is integrated.
  - Pach--Toth workers W6-P1--W6-P10 owned:
    `RoleHingeTransitionSearch.lean`, `RoleHingeAngleCertificates.lean`,
    `PeriodWordCertificates.lean`, `PeriodCertificateExamples.lean`,
    `CrossBlockUpperTriangleConcrete.lean`,
    `IndexedCrossBlockTableConcrete.lean`, `SmallCaseCertificates.lean`,
    `EventualRoleHingeClosure.lean`, `NonRigidClosedPlacementInterface.lean`,
    `ClosedPlacementClosure.lean`, and `GeneratedSeparationFarApart.lean`.
  - Swanepoel workers W6-S1--W6-S10 owned:
    `JordanBoundaryConcrete.lean`, `PlanarBoundaryFinal.lean`,
    `BoundaryLabelExtractionTasks.lean`, `NonconcaveArcAngleFacts.lean`,
    `NonconcaveArcBudgetFromBoundary.lean`,
    `Lemma8NeighborExtractionConcrete.lean`,
    `NoEarlyTripleObstructionConcrete.lean`, `BrokenLatticePipeline.lean`,
    `BrokenLatticeClosure.lean`, `MinimalGraphFacts.lean`,
    `MinimalGraphClosure.lean`, and `OuterBoundaryAssembly.lean`.
  - Sixth-wave results integrated: the non-rigid Pach--Toth route now has
    weaker connector-only role-hinge transition facts separated from the
    impossible all-pairs preservation package; period-word families project to
    generated-chain families; two-step nontrivial period examples are
    available; non-connector distance and squared-distance lower-bound routes
    feed exact, eventual, and arbitrary-`n` targets; and generated
    period/reduced-metric data routes to closed-placement families.  The
    Swanepoel route now has planar-boundary consumer bridges from topology
    data, direct face-counting constructors from boundary walks, stronger
    label/projection surfaces, turn-bound output packages, K23-to-no-early
    construction packages, broken-lattice closure adapters, and minimal graph
    target wrappers.
  - Remaining blockers after this wave: Pach--Toth still needs actual
    numerical/finite certificates for the non-rigid period and non-connector
    lower-bound inputs rather than just the consuming route.  Swanepoel still
    needs the honest construction of the topology/core boundary data and the
    concrete paper facts that fill the refined M8 input matrix.
  - Completion gate passed and remains covered by the current full verification
    snapshot above.

- [x] Seventh parallel proof wave is integrated.
  - W7 Pach--Toth and Swanepoel route modules are root-imported,
    build-checked, scan-clean, and consumed by `PachTothRemainingMatrix` and
    `SwanepoelRemainingMatrix`.
  - Remaining blockers after this wave: Pach--Toth must replace the blocked
    four-target exact-local transition with a viable non-rigid transition
    model and then fill actual numeric lower tables for the resulting
    candidate.  Swanepoel must still supply the concrete topology, boundary,
    label, window-containment, and no-early fields carried by the W7 matrices.
  - Completion gate passed and remains covered by the current full verification
    snapshot above.

- [x] Eighth parallel proof wave is integrated.
  - Pach--Toth workers W8-P1--W8-P10 own:
    `FlexibleExactLocalTransition.lean`,
    `ExactLocalTransitionObligationMatrix.lean`,
    `RoleHingeCandidateSearchSurface.lean`,
    `ConcretePeriodWordSearch.lean`,
    `PeriodCandidateTargetRoute.lean`,
    `GeneratedPolynomialLowerTableRoute.lean`,
    `ConcreteNonConnectorValueMatrix.lean`,
    `ArbitraryNExactRemainderClosure.lean`,
    `GeneratedPointPolynomialFacts.lean`, and
    `PachTothW8ClosureMatrix.lean`.
  - Swanepoel workers W8-S1--W8-S10 own:
    `OuterBoundaryExistenceConcrete.lean`,
    `BoundaryWalkFinitePartitions.lean`,
    `SubpolygonFaceConstruction.lean`,
    `BoundaryAngleAssembly.lean`,
    `LongArcGapConcrete.lean`,
    `K23NoEarlyClosure.lean`,
    `M8WindowContainmentConcrete.lean`,
    `Lemma9NoStartConcrete.lean`,
    `MinimalFailureW8RowAssembly.lean`, and
    `SwanepoelW8ClosureMatrix.lean`.
  - Eighth-wave results integrated: Pach--Toth now has a flexible exact-local
    transition interface, a checked exact-local possible-row/obstruction
    matrix with no `trustCompiler` dependency, a role-hinge finite-search
    surface, reusable checked period-word families, period-candidate target
    routing, generated polynomial lower-table routing, concrete value-matrix
    certificate wrappers, exact-remainder arbitrary-`n` closure, generated
    point polynomial normalization facts, and a W8 closure matrix.  Swanepoel
    now has exact outer-boundary topology fields, finite boundary-walk
    partitions, subpolygon-face construction bridges, boundary/subpolygon
    angle assembly, long-arc gap-to-turn-bound routing, K23/common-neighbor
    no-early closure, M8 window containment packaging, Lemma 9 no-start
    adapters, minimal-failure W8 row assembly, and a W8 closure matrix.
  - Remaining blockers after this wave: Pach--Toth still needs concrete
    same/opposite flexible branch data and actual polynomial/value lower-table
    certificates for a viable period family.  Swanepoel still needs actual
    topology extraction, boundary-label facts, window containment witnesses,
    and no-start/no-early fields instantiated from the geometric graph rather
    than carried as row data.
  - Completion gate passed and remains covered by the current full verification
    snapshot above.

- [x] Ninth parallel proof wave is integrated.
  - Pach--Toth workers W9-P1--W9-P10 own:
    `FlexibleBranchCoordinateSearch.lean`,
    `ExactLocalBranchSolverSurface.lean`,
    `PeriodFamilyCandidateSearchW9.lean`,
    `PolynomialCertificateExtraction.lean`,
    `ConcreteValueCertificateExamples.lean`,
    `PachTothFinalDataAssembly.lean`,
    `ExactRemainderPublicBridge.lean`,
    `UnitVectorParameterizationSearch.lean`,
    `CrossBlockLowerBoundSearchW9.lean`, and
    `PachTothRemainingObligationsW9.lean`.
  - Swanepoel workers W9-S1--W9-S10 own:
    `TopologyExtractionFromNoncrossing.lean`,
    `OuterBoundaryLabelFacts.lean`,
    `BoundaryPartitionInstantiation.lean`,
    `SubpolygonInstantiation.lean`,
    `BoundaryAngleWitnessConstruction.lean`,
    `M8WindowContainmentConcrete.lean`,
    `NoStartInstantiation.lean`,
    `K23MinimalFailureInstantiation.lean`,
    `MinimalFailureW8RowAssembly.lean`, and
    `SwanepoelRemainingObligationsW9.lean`.
  - Ninth-wave results integrated: Pach--Toth now has explicit coordinate
    search surfaces for the blocked same/opposite branch, a filtered
    exact-local row API, unit-vector parameterization routing, generated
    period/equation family surfaces, polynomial/value certificate extraction
    facades, concrete value examples, exact-remainder public routing, cross-block
    lower-bound facades, final-data assembly wrappers, and an explicit
    W9 remaining-obligation matrix.  Swanepoel now has topology-from-noncrossing
    frontier equivalences, boundary-label projections, partition/count
    instantiation, subpolygon instantiation fields, unit-separated angle
    witnesses, expanded M8 containment routes, no-start/K23 minimal-failure
    row adapters, W8 row assembly extensions, and a W9 remaining-obligation
    matrix.
  - Remaining blockers after this wave: Pach--Toth still needs an actually
    viable non-rigid transition family, period equations, and non-connector
    lower/value tables that inhabit the explicit closing fields.  The concrete
    same/opposite four-target coordinates remain formally blocked by the
    `T1_1,r` exact-local row.  Swanepoel still needs concrete topology,
    enclosure, label, angle, containment, and no-early witnesses instantiated
    uniformly for every minimal failure, rather than carried as explicit row
    fields.
  - Completion gate passed: all 20 W9 workers were closed only after completion;
    all owned modules received targeted pinned Lean checks and source scans;
    root import coverage, full build, forbidden-token scan,
    `native_decide`/`trustCompiler` source scan, diff whitespace check, and
    CI-style axiom audit passed.

- [x] Tenth parallel proof wave is integrated.
  - Pach--Toth workers W10-P1--W10-P10 own:
    `FlexibleTransitionSearchW10.lean`,
    `RoleHingePolynomialSystemW10.lean`,
    `NonRigidPeriodCandidateW10.lean`,
    `CrossBlockValueSearchW10.lean`,
    `LengthTwoThreeCaseW10.lean`,
    `ExactLocalObstructionExpansionW10.lean`,
    `FlexibleBranchSearchSummaryW10.lean`,
    `ArbitraryNBridgeW10.lean`,
    `GeneratedPointNormalizationW10.lean`, and
    `PachTothW10ClosureMatrix.lean`.
  - Swanepoel workers W10-S1--W10-S10 own:
    `TopologyFrontierW10.lean`,
    `BoundaryLabelInstantiationW10.lean`,
    `BoundaryCountingInstantiationW10.lean`,
    `SubpolygonAngleW10.lean`,
    `WindowContainmentW10.lean`,
    `NoEarlyK23AssemblyW10.lean`,
    `MinimalFailureDirectMatrixW10.lean`,
    `SwanepoelTargetFacadeW10.lean`,
    `GeometryRemainingFieldsW10.lean`, and
    `SwanepoelW10ClosureMatrix.lean`.
  - Tenth-wave results integrated: Pach--Toth now has sharper non-rigid
    transition search surfaces, role-hinge polynomial systems, period-candidate
    routing, cross-block value/inequality ledgers, length-two/length-three
    missing-data ledgers, exact-local obstruction expansions, generated-point
    normalization certificates, arbitrary-`n` routing, and a W10 closure
    matrix.  Swanepoel now has topology-frontier equivalences, boundary-label
    instantiation rows, boundary/subpolygon angle-count adapters, M8 window
    containment adapters, no-early/K23 assembly rows, minimal-failure direct
    matrices, remaining geometry-field packages, target facades, and a W10
    closure matrix.
  - Remaining blockers after this wave: Pach--Toth still needs concrete
    non-rigid transition/period data and actual polynomial/value lower-table
    certificates for a viable generated closed-chain family.  Swanepoel still
    needs concrete inhabitants of the topology/enclosure, boundary-label,
    angle/long-arc, window-containment, no-start/no-early, K23/common-neighbor,
    and broken-lattice geometry fields.
  - W10 status: these modules provide checked conditional direct/K23/component
    and geometry projection routes, plus 20 CI axiom-audit entries.  They do
    not yet provide uniform row-family inhabitants for either final bound.
  - Completion gate passed: all 20 W10 workers were closed only after
    completion; all owned modules received targeted pinned Lean checks and
    source scans; root import coverage, full build, forbidden-token scan,
    `native_decide`/`trustCompiler` source scan, diff whitespace check, and
    CI-style axiom audit passed.

- [x] Eleventh parallel proof wave is integrated.
  - Pach--Toth W11 worker and terminal-route modules are root-imported,
    build-checked, and scan-clean.
  - Swanepoel W11 worker and terminal-route modules are root-imported,
    build-checked, and scan-clean.
  - Completion gate passed: the 19 W11 terminal-route files that were outside
    the root import surface now import through
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`; targeted checks,
    root build, source scan, `native_decide`/`trustCompiler` source scan,
    coverage scan, diff whitespace check, and CI-style axiom audit passed.
  - Current status: W11 closes the terminal-summary import/build plumbing; it
    still does not supply the final unconditional
    Swanepoel `8 / 31` or Pach--Toth `5 / 16` public theorem data.

- [x] Twelfth parallel proof wave surface is integrated.
  - Pach--Toth W12 modules are root-imported, build-checked, and scan-clean:
    `FiniteCertificateObligationsW12`, `LargeClosedPlacementW12`,
    `NonConnectorSeparationW12`, and `OrbitSqDistancesW12`.
  - Swanepoel W12 modules are root-imported, build-checked, and scan-clean:
    `BoundaryArcW12`, `BoundaryClassificationW12`, `CutVertexSlackW12`,
    `E22E23BridgeW12`, `Figure8ContainmentW12`,
    `Figure9ContainmentW12`, `Lemma6NegativeAfterGapW12`,
    `Lemma7GapInductionW12`, `Lemma8WitnessW12`, `M8TurnPackageW12`,
    `OuterBoundaryAngleW12`, `SubpolygonAngleW12`, and
    `SubpolygonPackageW12`.
  - Current W12 route correction: `OrbitSqDistancesW12` proves the old fully
    quantified concrete connector-only orbit-distance target is blocked, so
    Pach--Toth work must instantiate a replacement transition/orbit package or
    use the restricted exact-block route that avoids the obstructed all-same
    two-block word.
  - Completion gate passed: all 17 W12 files import through
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`; targeted checks,
    root build, source scan, `native_decide`/`trustCompiler` source scan,
    coverage scan, diff whitespace check, and CI-style axiom audit passed.

- [x] Thirteenth parallel proof wave surface is integrated.
  - Swanepoel W13 bridge/assembly modules are root-imported, build-checked,
    and scan-clean.
  - Pach--Toth W13 bridge/assembly modules are root-imported, build-checked,
    and scan-clean.
  - Current status: W13 routes the W12 package surfaces into narrower
    endpoint/assembly paths, but the final theorem data is still conditional.

- [x] Fourteenth parallel proof wave surface is integrated.
  - Pach--Toth W14 endpoint and certificate modules are root-imported,
    build-checked, and scan-clean, including exact-to-arbitrary, large/small,
    period/non-connector, and known-bound-spine surfaces.
  - Swanepoel W14 endpoint and remaining-input modules are root-imported,
    build-checked, and scan-clean, including boundary-arc, boundary-angle,
    Lemma 6/7, Lemma 8/9, face-reduction, and final endpoint attempts.
  - Current status: W14 gives the live conditional endpoint facades; it does
    not by itself supply the concrete final gate inputs.

- [x] Fifteenth proof-surface wave is integrated.
  - Pach--Toth W15 modules are root-imported, build-checked, and scan-clean:
    `AllPositiveCertificateAssemblyW15`, `FinalPachTothGateW15`,
    `LargeThresholdSmallCasesW15`, `PeriodRowsAllPositiveProofW15`, and
    `TailPolynomialLowerProofW15`.
  - Swanepoel W15 modules are root-imported, build-checked, and scan-clean:
    `BoundaryArcExtractionProofW15`, `FinalSwanepoelGateW15`,
    `Lemma89WindowContainmentProofW15`, `NoCutMinimalityProofW15`,
    `OuterAngleBudgetProofW15`, and `RemainingInputConcreteAssemblyW15`.
  - Current status: W15 provides the final-gate shape.  The final bounds are
    still conditional on constructing `FinalPachTothGateW15.FinalGate` and
    `FinalSwanepoelGateW15.FinalGate`.

- [x] Sixteenth proof-surface wave is integrated.
  - Pach--Toth W16 modules are root-imported, build-checked, and scan-clean:
    `EventualClosedPlacementCertificateW16`, `LargeKGlobalSeparationW16`,
    `PeriodBaseFixingCertificateW16`, `PeriodBaseFixingOppositeW16`,
    `PeriodBaseFixingSameW16`, `SmallComplementExactBlocksW16`,
    `SmallRowsFourFiveW16`, `SmallRowsTwoThreeW16`, and
    `TailPolynomialRowsW16`.
  - Swanepoel W16 modules are root-imported, build-checked, and scan-clean:
    `BoundaryArcFiniteWalkConstructionW16`, `BoundaryTopologyArcBridgeW16`,
    `Figure8WindowContainmentW16`, `Figure9WindowContainmentW16`,
    `Lemma8LocalLabelsW16`, `Lemma9LateTriplesW16`,
    `LongArcFactsSelectionW16`, `NoCutFromMinimalityW16`, and
    `PayForCutArithmeticW16`.
  - Current status: W16 tightens the final-gate input contracts, but it still
    leaves the concrete final-gate constructors as the live proof work.

- [x] Import and scan the completed interface-wave modules.
  - Completed interface-wave modules are root-imported and covered by the
    current full-tree forbidden-token scan.  The long per-module inventory has
    been retired; remaining active work is tracked by the open items below.

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

File hygiene note.
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
| `E14-E16` | Lemmas 6, 7, 5: long nonconcave arc | S6, current Lean has reducers/adapters; the remaining proof must construct `NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData` |
| `E17` | `m = 8` thirteen-turn specialization of the long-arc data | S6, `NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData` to `M8TurnBoundsFromArc.NonconcaveArcTurnData` |
| `E18-E19` | Lemma 8 labels and Lemma 9 late triples | S6/S8, `M8FinitePQSpineCertificate`, `M8Lemma8MissingExistenceConditions`, `M8Lemma9FiveStartLateFacts` |
| `E21-E23` | Euclidean Lemma 10 and Figure 8/Figure 9 inequalities | S7, `HonestFigure8ExplicitEuclideanFacts`, `HonestFigure9AdjacentLeftEuclideanFactWitnesses`, then `MinimalFailureM8RefinedPaperFacts.windowGeometry` |
| `E24` | `m = 8` contradiction and lower-bound target | S8, `MinimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne` |

Current source-refined paper package:

```lean
M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily
```

This is the cleanest paper-facing checklist.  The smallest Lean-efficient
conditional gate below it is:

```lean
BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator
```

The source-refined package closes the target through:

```text
MinimalFailureM8RefinedPaperFacts
-> MinimalFailureM8RefinedPaperFacts.toM8ConstructionData
-> MinimalFailureM8RefinedPaperFactsFamily.toM8ConstructionEliminator
-> MinimalFailureM8RefinedPaperFactsFamily.no_minimalClearedFailure
-> MinimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne
-> Swanepoel.targetLowerBoundEightThirtyOne
```

The older separated-construction gate remains checked separately through:

```text
M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator
-> M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator
-> MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure
-> Swanepoel.targetLowerBoundEightThirtyOne
```

The paper-facing `MinimalFailureM8RefinedPaperFacts` package still has a
`positiveCard` field, but the concrete matrix routes derive it from minimality.
The remaining source obligations are no-cut slack, arc budget, spine
certificate, Lemma 8, Lemma 9, and Figure 8/Figure 9 facts.

For current parallel handoff, use the rooted W20/W21 source-package lane.
Swanepoel agents should target
`RemainingObligationLedgerW20.RemainingObligationFields`,
`PointwiseProducerFamilyFieldsW20.PointwiseSourceFamilyFields`,
`SwanepoelSourcePackageW20.ExactRemainingFields`, and
`SwanepoelKnownBoundsGateW21.KnownBoundsExposureGate`.  Pach--Toth agents
should target
`ExplicitClosedPlacementInputPackageW20.GeneratedFamilyClosureReducedMetricSourceFields`,
`GeneratedChainFamilyProducerW20.SourceFields`,
`ExplicitClosedPlacementProducerW19.InputPackage`, and
`ClosedPlacementKnownBoundsGateW21.KnownBoundsExposureGate`.  W12-W21 package
surfaces remain the component contracts underneath this handoff.

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

- [ ] Prove the W16 no-cut payload from minimality.
  - Paper step: Swanepoel `E7`, Lemma 3 two-connectedness/no-cut-vertex
    reduction.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexFromConnectedness.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/CutVertexFinal.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoCutMinimalityProofW15.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/PayForCutArithmeticW16.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NoCutFromMinimalityW16.lean`,
    consumed downstream by
    `NoCutFromMinimalityW16.PointwiseNoCutMinimalityInputs.noCutVertex`
    and eventually `FinalSwanepoelGateW15.FinalGate`.
  - Current checked W16 localization:

```lean
def NoCutMinimalityProofW15.MinimalitySelectedPayForCut

theorem PayForCutArithmeticW16
  .minimalitySelectedPayForCut_iff_sideCardExactFact
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <->
      CutVertexDeletionSideCardExactFact hmin

theorem PayForCutArithmeticW16
  .minimalitySelectedPayForCut_iff_noCutVertex_of_minimalFailure
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    MinimalitySelectedPayForCut hmin <-> CutVertexInterface.NoCutVertex C
```

  - Correct next target: prove the partition-independent W15 pay-for-cut
    statement from minimality, or prove `NoCutVertex C` directly and recover
    the pay-for-cut statement by the checked equivalence.

```lean
theorem minimalitySelectedPayForCut_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    NoCutMinimalityProofW15.MinimalitySelectedPayForCut hmin := by
  sorry

theorem noCutVertex_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C) :
    CutVertexInterface.NoCutVertex C := by
  exact
    NoCutMinimalityProofW15
      .noCutVertex_of_minimalFailure_minimalitySelectedPayForCut
        hmin
        (minimalitySelectedPayForCut_of_minimalFailure hmin)
```

  - How: argue by contradiction from a supplied `CutVertexPartition C`.
    `NoCutMinimalityProofW15` proves that a concrete partition obstructs the
    uniform pay-for-cut input, so the proof must extract an actual contradiction
    from the partition using deletion/gluing and `CutVertexPayForCutArithmetic`,
    not merely assert that the minimality-selected side surplus pays the cut
    vertex while the partition remains live.
  - Completion gate: root-import a theorem providing `NoCutVertex C` for every
    minimal cleared failure, then consume it through
    `NoCutFromMinimalityW16.NoCutMinimalityRemainingInputFamily` or directly in
    `FinalSwanepoelGateW15.FinalGate`.

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
  - Dependency: the full `OuterBoundaryCore`/`PlanarBoundaryData` route needs
    `remainingNoCutSlackFact_of_minimalFailure` from S3.  Until then,
    `MissingTopologyFacts`-style topology extraction is the parallel-safe
    subtask.
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
  - Conditional bridge now present: `BoundaryWalkConstruction` has
    `longArcContribution`, `longArcIndicator_sum_eq_B` in terms of that
    contribution, and `toPlanarBoundaryData_countsRealization` for projecting
    the count realization carried by the constructed planar-boundary package.
    This is bookkeeping glue only; the actual boundary classifications and
    count data still have to be extracted from the outer boundary.
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
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma6NegativeAfterGapW12.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcBudgetFromBoundary.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/SubpolygonAssembly.lean`.
  - Deliverable: instantiate the checked W12
    `BoundaryWalkLemma6Obstruction` or `BoundaryArcIndexMap` for the actual
    boundary walk, then use `negativeAfter_of_gap` / `negativeAfterAt_of_gapAt`
    to feed the nonconcave-arc package.
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
    `NonconcaveArcBoundaryBudgetData` and its
    `toNonconcaveArcGeometricAngleFacts` projection.

- [ ] Prove Lemma 5 / existence of a nonconcave long arc.
  - Paper step: Swanepoel `E16`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcConcrete.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsFromArc.lean`.
  - Deliverable: construct the existing geometric-angle package from the S4/S5
    boundary and subpolygon facts plus Lemmas 6 and 7.
  - Conditional bridge now present: `NonconcaveArcConcrete.BoundaryLongArcFacts`
    packages a finite family of long arcs, a concavity predicate, the strict
    count gap, raw turn functions, nonnegativity, and the `concave_iff`
    comparison.  It already selects a nonconcave long arc and routes it to
    `NonconcaveArcBoundaryBudgetData` and `M8ConstructionInterface.M8TurnBounds`.
    This does not prove Lemma 5 by itself; the remaining work is to build the
    `BoundaryLongArcFacts` instance from the real boundary data and connect
    Lemmas 6 and 7 to `NonconcaveArcGeometricAngleFacts`.

```lean
noncomputable def nonconcaveArcBoundaryBudgetData_of_minimalFailure
    {n : Nat} {C : UDConfig n}
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C)
    (planarBoundary :
      PlanarBoundaryClosure.PlanarBoundaryData
        (BoundaryFaceCountingToM8.CanonicalUDGraph C)) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData
      (BoundaryFaceCountingToM8.CanonicalUDGraph C) := by
  sorry
```

  - How: package the selected long arc, the turn function, turn
    nonnegativity, and the `totalTurn < Real.pi / 3` budget from Lemmas 6 and
    7.
  - Completion gate: the refined M8 package field `arcBoundaryBudget` is filled.

- [ ] Specialize the long-arc data to the `m = 8` thirteen-turn package.
  - Paper step: Swanepoel `E17`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnPackageW12.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/NonconcaveArcAngleFacts.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsFromArc.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8TurnBoundsConcrete.lean`.
  - Target skeleton:

```lean
noncomputable def m8ThirteenTurnData_of_nonconcaveArc
    {G : Type u} [Fintype G] [DecidableEq G]
    (D : NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData G) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  D.toNonconcaveArcTurnData
```

  - How: prove that the paper's selected `m = 8` arc is exactly the current
    `turnIndexSet = {1, ..., 13}` and that all off-arc turns are normalized to
    zero by the checked adapter.
  - Completion gate: S7 can use the resulting
    `M8TurnPackageW12.BoundaryLongArcM8TurnPackage` turn function in the
    Figure 8/Figure 9 Euclidean fact fields.

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
  - Completion gate: the refined M8 package field `figure8EuclideanFacts` can
    be constructed for the honest M8 labels.

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
    into `HonestFigure8ExplicitEuclideanFacts`.

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
  - Completion gate: the refined M8 package field `figure9EuclideanFacts` can
    be constructed for the honest M8 labels.

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
    into `HonestFigure9AdjacentLeftEuclideanFactWitnesses`.

- [ ] Build the honest E22/E23 hypotheses.
  - Existing final bridge:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10AngleToTurn.lean`.
  - Window-geometry bridge:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/Lemma10WindowGeometry.lean`.
  - W12 route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/E22E23BridgeW12.lean`.
  - Target route:

```lean
figure8SeparatedWindowLowerE22_of_angleToTurnBridge
figure9AdjacentWindowLowerE23_of_leftAngleToTurnBridge
E22_E23_of_angleToTurnBridges

Lemma10WindowGeometry.honestE22_E23_of_leftWindowGeometry
M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts.windowGeometry
E22E23BridgeW12.contradiction_of_constructionDataFromContainment
```

  - Deliverable:

```lean
noncomputable def figure8EuclideanFacts_of_m8LabelsAndArc
    {n : Nat} {C : UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (D :
      NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData
        (BoundaryFaceCountingToM8.CanonicalUDGraph C)) :
    Figure8EuclideanFactsConcrete.HonestFigure8ExplicitEuclideanFacts
      localLabels.predicates D.toM8TurnBounds.turn := by
  sorry

noncomputable def figure9EuclideanFacts_of_m8LabelsAndArc
    {n : Nat} {C : UDConfig n}
    (localLabels : M8ConstructionInterface.M8LocalLabels C)
    (D :
      NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData
        (BoundaryFaceCountingToM8.CanonicalUDGraph C)) :
    Figure9EuclideanFactsConcrete.HonestFigure9AdjacentLeftEuclideanFactWitnesses
      localLabels.predicates D.toM8TurnBounds.turn := by
  sorry
```

  - How: construct `Figure8SeparatedAngleToTurnBridge` and
    `Figure9AdjacentLeftAngleToTurnBridge`, or use the newer containment
    wrappers directly from extracted distance data and window-containment
    lemmas.
  - Completion gate: the refined M8 package fields `figure8EuclideanFacts` and
    `figure9EuclideanFacts` are filled.

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
    the explicit `MinimalFailureM8RefinedPaperFacts` fields: positive
    cardinality, cut-vertex slack, boundary-attached nonconcave arc budget,
    the M8 boundary spine certificate, Lemma 8 extra-neighbor combinatorics,
    Lemma 9 five-start late facts, and Figure 8/Figure 9 Euclidean facts.
  - Conditional status: these fields are still paper facts to prove, not
    completed Lean constructions.

- [ ] Prove the minimal-failure `m = 8` construction eliminator.
  - Paper step: Swanepoel `E24`, final `m = 8` contradiction.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/M8PaperFactsAssemblyRefined.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/BrokenLatticeMinimalFailure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailureClosure.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/Swanepoel/MinimalFailurePaperFactMatrix.lean`.
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

  - Lean-efficient construction-data gate:

```lean
noncomputable def minimalFailureM8ConstructionEliminator :
    BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator := by
  intro C hmin
  sorry
```

  - Exact gate definition already checked in Lean:

```lean
def BrokenLatticeMinimalFailure.MinimalFailureM8ConstructionEliminator : Prop :=
  forall {n : Nat} (C : _root_.UDConfig n)
    (hmin : MinimalGraphFacts.IsMinimalClearedFailure C),
      Nonempty (BrokenLatticeMinimalFailure.M8ConstructionData C hmin)
```

  - How: assemble the S3 cut-slack field, S4/S5 planar-boundary field, S6
    boundary-attached arc budget plus spine/Lemma 8/Lemma 9 fields, and S7
    Figure 8/Figure 9 Euclidean fields into
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
already present as
`EventualRoleHingeClosure.EventualFiniteCertificateObligations`; the remaining
work is supplying concrete eventual transition, orientation, period, and
separation data, plus matching small cases for the chosen threshold.
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
  - Conditional status: concrete connector-only same/opposite role-hinge
    transition obligations are now checked; exact-local same-block
    square-distance preservation, period/closure data, and generated global
    separation remain supplied data.

- [x] Build concrete connector-only same/opposite role-hinge transition data.
  - Live target shape:

```lean
def RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations :
    Figure2Certificate.SameOppositeTransitionObligations
```

  - Current state: `RoleHingeConcreteSearch` defines the concrete role angles,
    same/opposite maps, connector unit-edge proofs, and the bundled
    `concreteSameOppositeTransitionObligations`; `RoleHingeInterfaceRefinement`
    routes this object into exact-block conditional bridges.
  - Remaining blocker: prove exact-local same-block square-distance
    preservation for these concrete maps, plus period/closure data and global
    separation.  Do not target the old
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
  - Conditional status: the old full exact-local preservation field for the
    concrete connector-only obligations is blocked by W12.  The live fields are
    replacement transition/orbit data, period/closure data, and generated
    global separation/non-connector lower tables.

- [ ] Replace the blocked concrete connector-only orbit-distance route.
  - Checked W12 facts:

```lean
OrbitSqDistancesW12.sameBlockIsometry_of_concreteTransitionObligations_orbitSqDistances
OrbitSqDistancesW12.exactBlockTarget_of_concreteTransitionObligations_orbitSqDistances
OrbitSqDistancesW12.concreteTransitionObligations_transitionExactLocalSqDistances_blocked
OrbitSqDistancesW12.concreteTransitionObligations_orbitSqDistances_twoSame_blocked
OrbitSqDistancesW12.concreteTransitionObligations_orbitSqDistances_blocked
```

  - Next action: do not target the old fully quantified theorem for
    `RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations`.
    It is false for the current concrete map.  A proof agent should either
    choose replacement transition data whose orbit rows avoid the checked
    obstruction, or keep the current connector-only map and instantiate only
    the restricted closure/separation/orbit data consumed by
    `OrbitSqDistancesW12.exactBlockTarget_of_concreteTransitionObligations_orbitSqDistances`.
  - Completion gate: a root-imported route supplies the exact-block target
    through either the replacement transition package or the checked restricted
    W12 exact-block theorem, without contradicting
    `OrbitSqDistancesW12.concreteTransitionObligations_orbitSqDistances_blocked`.

- [x] Prove the generic connector-port unit-edge reducer.
  - Checked route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeConnectorAlgebra.lean`,
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/RoleHingeInterfaceRefinement.lean`.
  - Current state: the generic role-hinge connector algebra is imported,
    build-checked, and scan-clean.

- [x] Instantiate concrete connector-port unit edges.
  - Checked declarations:

```lean
RoleHingeConcreteSearch.concreteRoleHingePlace_connector_unit_edges
RoleHingeConcreteSearch.same_connector_unit_edges
RoleHingeConcreteSearch.opposite_connector_unit_edges
RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations
```

  - Remaining blocker: connector-pair unit edges are done; non-connector
    separation and same-block metric preservation remain open.

- [x] Build connector-only same/opposite transition maps.
  - Checked declaration:

```lean
def RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations :
  Figure2Certificate.SameOppositeTransitionObligations
```

  - Remaining dependencies: residual/orbit exact-local metric data, period
    equations, and reduced non-connector separation.  The old all-source
    preservation route remains only an obstruction audit surface.

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
  - Fourth-wave bridge status: the live conditional names include
    `ConcretePeriodCandidateSearch.targetUpperConstructionFiveSixteenAt_ofPeriodEquationFamilyAndLowerBounds`,
    `EventualRoleHingeClosure.targetUpperConstructionFiveSixteenArbitrary_of_eventual_roleHingedClosure_exactTarget`,
    the square-value certificate projections
    `PeriodSearchSqValueFactsInput.targetUpperConstructionFiveSixteen` and
    `PeriodSearchSqValueFactsInput.targetUpperConstructionFiveSixteenArbitrary`,
    and
    `ExactFiveSixteenRouteMatrix.targetUpperConstructionFiveSixteenArbitrary_of_nonConnectorPolynomialTableFamily`.
    These are conditional bridge names only; they do not close an
    unconditional Pach--Toth bound.

- [x] Build the compact all-positive finite-certificate obligation package.
  - Paper step: stronger Lean route for `GEO.2-GEO.3`.
  - Lean route:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/FiniteCertificateObligationsW12.lean`.
  - Checked facade:

```lean
structure FiniteCertificateObligationsW12.PeriodEquationFields
structure FiniteCertificateObligationsW12.AllPositiveNonConnectorFields
structure FiniteCertificateObligationsW12.TableFamilyPackage
structure FiniteCertificateObligationsW12.VectorPackage
structure FiniteCertificateObligationsW12.ListPackage
theorem FiniteCertificateObligationsW12.targetUpperConstructionFiveSixteenArbitrary_of_rawFields
```

  - Current state: the W12 facade is root-imported, build-checked, scan-clean,
    and covered by the CI-style axiom audit.
  - Remaining open work: instantiate `PeriodEquationFields` and one of
    `AllPositiveNonConnectorFields`, `TableFamilyPackage`, `VectorPackage`, or
    `ListPackage` with actual period equations and non-connector lower tables.
    That instantiation, not another facade, is the live proof task.

- [x] Choose the reduced non-connector separation route.
  - Verified route choice: use reduced non-connector tables through
    `ConcreteCrossBlockLowerTable`, `NonConnectorPolynomialCertificates`, and
    `PachTothRemainingMatrix`; keep all-pairs tables only as fallback.
  - Remaining numeric-certificate target skeleton:

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

- [x] Add a source-faithful thresholded/eventual finite-certificate package if
  the all-positive route is too strong.
  - Paper step: Pach--Toth `GEO.3` / `PT96.Main`, sufficiently large `k`.
  - Current bridge status: `EventualRoleHingeClosure` already carries the
    thresholded role-hinged closure route down to exact-target small-case
    complement data.  The remaining blocker is not another facade theorem but
    the actual eventual transition, orientation, period, and separation data,
    plus enough small cases to match the chosen threshold.
  - Existing imported structure:

```lean
structure EventualFiniteCertificateObligations (K0 : Nat) where
  transitions : EventualRoleHingeClosure.RoleHingeTransitions
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
        ((word k hK hk).toFin)

theorem EventualFiniteCertificateObligations.targetUpperConstructionFiveSixteenEventually
    {K0 : Nat} (O : EventualFiniteCertificateObligations K0) :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenEventually
```

  - Current state: the package and eventual/arbitrary wrappers are imported
    and build-checked.
  - Remaining blocker: instantiate the structure by supplying concrete
    transitions, orientation words, period equations, and generated global
    separation for all `K0 <= k`, then combine with matching small cases.

- [ ] Prove sufficiently-large closed placement certificates.
  - Best home:
    `E:/Personal/Erdosproblems/1066/ErdosProblems1066/PachToth/LargeClosedPlacementW12.lean`
    or a new imported module directly instantiating its W12 structures.
  - Source-faithful target:

```lean
def closedChainThreshold : Nat

noncomputable def largeExplicitClosedPlacementCertificates_verified :
    LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates
      closedChainThreshold := by
  sorry

theorem targetUpperConstructionFiveSixteenEventually_verified :
    _root_.ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenEventually := by
  exact
    largeExplicitClosedPlacementCertificates_verified
      |>.targetUpperConstructionFiveSixteenEventually
```

  - Next action: build macro-step certificates, express every large `k` by the
    macro lengths, close cyclic displacement, prove global separation, and
    package the resulting certificates through
    `LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates`.

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
  - Current coverage: 823 imported modules for 823 Lean files, with no missing,
    extra, or duplicate root imports.
- [x] Pinned build succeeds.
  - Current command succeeded for the root target with 8850 jobs.
- [x] Forbidden-token scan is clean over `ErdosProblems1066` and
  `ErdosProblems1066.lean`.
- [x] Trust-source scan is clean for `native_decide`, `trustCompiler`, and
  `ofReduceBool`.
- [x] CI-style axiom audit declaration list covers the current W13-W31
  endpoint layer.
  - Current configured audit checks 1127 declarations and reports only
    `propext`, `Classical.choice`, and `Quot.sound`.
  - Current source-level no-additional-declared-axiom evidence: the full
    Lean-source forbidden-token scan is clean over the 823-module root surface.
- [x] Add W18/W19/W20 endpoint declarations to the CI-style axiom audit.
  - The configured audit now includes the W18 final/ledger endpoints, the W19
    Pach-Toth closed-placement audit aliases, the W19 Swanepoel
    pointwise/final closure endpoints, and the W20 Pach-Toth/Swanepoel
    endpoint surfaces.
- [x] Add W21/W22 endpoint declarations to the CI-style axiom audit.
  - The W21/W22 subset is folded into the current 1127-declaration replayed
    audit, which passed with only Lean/mathlib base axioms.
- [x] Add W23/W24/W25/W26/W27/W28 endpoint declarations to the CI-style axiom audit.
  - The configured audit now includes W23 route/audit wrappers, W24 source and
    obstruction surfaces, W25 source-inhabitation/audit endpoints, and W26
    concrete-adapter/final-gate endpoints, plus W27/W28 source/audit endpoints.
  - The replayed audit passed for 1127 declarations with only Lean/mathlib base
    axioms.
- [x] Add W29 endpoint declarations to the CI-style axiom audit.
  - The configured audit now includes W29 Pach--Toth source/assembly/audit
    endpoints and W29 Swanepoel source/final-gate endpoints.
  - The replayed audit passed for 1127 declarations with only Lean/mathlib base
    axioms.
- [x] Add W30 endpoint declarations to the CI-style axiom audit.
  - The configured audit now includes W30 Pach--Toth generated-closure,
    completion-row, branch/source, large-tail, route-audit, no-fake, and final
    conditional endpoints, plus W30 Swanepoel selected-face, extracted-witness,
    frame/cyclic-order, no-cut, no-early, figure, pointwise, route-audit, and
    final-source endpoints.
  - The replayed audit passed for 1127 declarations with only Lean/mathlib base
    axioms.
- [x] Add W31 endpoint declarations to the CI-style axiom audit.
  - The configured audit now includes W31 Pach--Toth explicit generated metric
    rows, completion-row inhabitants, closed-orbit branch, exact-chain family,
    positive-chain small blocks, large-tail row realization, remainder
    dependency, route/no-fake audit, and final conditional assembly endpoints.
  - The configured audit also includes W31 Swanepoel selected-face/enclosure,
    extracted components, frame/cyclic rows, no-early rows, figure inequalities,
    pointwise/lane product, route audit, and final conditional endpoints.
  - The replayed audit passed for 1127 declarations with only Lean/mathlib base
    axioms.
- [x] `KnownBounds.lean` exposes only the theorems actually closed in Lean.
  - Next action: add no new public wrappers until the matching internal
    `*_verified` theorem exists and builds.

## Latest W31 Status

- [x] W20-W31 waves integrated and verified.
  - Root surface: 823 Lean files imported by 823 root imports.
  - Pinned build: `elan run leanprover/lean4:v4.28.0 lake build ErdosProblems1066`
    succeeded with 8850 jobs.
  - Forbidden-token scan, trust-source scan, root import coverage, and the
    1127-declaration CI-style axiom audit all pass.
  - W31 fixes the W31 face-boundary/enclosure audit namespace by using
    `ErdosProblems1066.Swanepoel.Verified.swanepoelW31_source_exactly_exactTopologyFields`.

- [x] W23-W31 waves integrated, root-build verified, and CI-audited.
  - All W23, W24, W25, W26, W27, W28, W29, W30, and W31 files are root-imported
    and covered by the current 823/823 import surface.
  - W23-W31 add concrete route/audit wrappers, source-package equivalences,
    route obstruction records, and sharper lane/row package names; they do not
    prove the final public bounds unconditionally.

- [ ] Next action: inhabit the concrete source packages beyond W31.
  - Pach--Toth: produce actual completion-row/generated-orbit, positive-chain,
    large-tail, and remainder-split source data for the W31 final gate; do not
    target the blocked role-hinged lower-table alias.
  - Swanepoel: produce actual W31 final-source gate data from minimal failure
    topology/geometry, no-cut, no-early, finite-row, figure-angle, pointwise,
    and lane-product data.
  - Public `KnownBounds` wrappers remain closed until the internal
    `*_verified` theorem builds through the W31 gate and the expanded axiom
    audit is clean.

- [x] W30 parallel source-inhabitation wave is integrated and verified.
  - Pool policy: keep active agents running long enough to do real proof work;
    prune only agents that are finished or genuinely stale.
  - Agent pool completed:
    Laplace/Meitner/Mencius/McClintock/Archimedes/Sagan/Kepler/Raman/
    Confucius/Rawls own the Pach--Toth W30 tasks; Locke/Boyle/Epicurus/
    Newton/Kierkegaard/Galileo/Einstein/Ohm/Descartes/Turing own the
    Swanepoel W30 tasks.
  - Pach--Toth completed tasks:
    `GeneratedClosureMetricRowsW30`, `CompletionRowsClosureW30`,
    `ClosedOrbitBranchSourceW30`, `ExactChainFamilyClosureW30`,
    `PositiveChainComponentClosureW30`, `LargeTailCertificateRowsW30`,
    `RemainderExactDependencyClosureW30`, `PachTothW30NoFakeAudit`,
    `PachTothW30RouteAudit`, and `PachTothW30FinalAssembly`.
  - Swanepoel completed tasks:
    `SelectedFaceEnclosureSourceW30`, `ExtractedWitnessComponentsW30`,
    `FrameCyclicOrderRowsW30`, `NoEarlyRouteDataClosureW30`,
    `ExactFigureInequalitiesW30`, `PointwiseProductDataClosureW30`,
    `LaneProductFinalClosureW30`, `NoCutBlockerEliminationW30`,
    `SwanepoelW30RouteAudit`, and `SwanepoelW30FinalAssembly`.
  - W30 completion gate:
    all 20 produced `.lean` files compile with pinned Lean 4.28.0, are
    root-imported, scan-clean, trust-source clean, included in the 8830-job root
    build, and covered by the 1106-declaration CI-style axiom audit.

- [x] W31 parallel source-inhabitation wave is integrated and verified.
  - Pool policy: W30 agents were closed only after their work was integrated,
    root-built, and audited.  W31 agents were likewise kept active until all
    outputs were locally checked, root-imported, root-built, and CI-audited.
  - Agent pool completed:
    Popper/Mendel/Leibniz/Plato/Russell/Bacon/Godel/Avicenna/Hegel/Pauli own
    the Pach--Toth W31 tasks; Pasteur/Curie/Ampere/Faraday/Bohr/Herschel/Gibbs/
    Volta/Erdos/Parfit own the Swanepoel W31 tasks.
  - Pach--Toth W31 completed tasks:
    `GeneratedMetricSourceFieldsW31`, `CompletionRowsInhabitationW31`,
    `ClosedOrbitConcreteBranchW31`, `ExactChainFamilyInhabitationW31`,
    `PositiveChainSmallBlocksW31`, `LargeTailRowsRealizationW31`,
    `RemainderDependencyFinalW31`, `PachTothW31NoFakeAudit`,
    `PachTothW31RouteAudit`, and `PachTothW31FinalAssembly`.
  - Swanepoel W31 completed tasks:
    `SelectedOuterFaceConstructionW31`, `EnclosureAndFaceBoundaryW31`,
    `ExtractedComponentsInhabitationW31`, `FrameRowsInhabitationW31`,
    `CyclicOrderRowsInhabitationW31`, `NoEarlyConcreteRowsW31`,
    `FigureInequalityRowsW31`, `PointwiseLaneProductInhabitationW31`,
    `SwanepoelW31RouteAudit`, and `SwanepoelW31FinalAssembly`.
  - W31 completion gate:
    all 20 produced `.lean` files compile with pinned Lean 4.28.0, are
    root-imported, scan-clean, trust-source clean, included in the 8850-job root
    build, and covered by the 1127-declaration CI-style axiom audit.

- [ ] W32 parallel source-inhabitation wave is queued.
  - Pool policy: close the integrated W31 agents, then keep W32 agents active
    long enough to do real Lean work; prune only finished or genuinely stale
    agents.
  - Pach--Toth W32 targets:
    `ExplicitMetricRowsInhabitationW32`, `CompletionRowsConcretePayloadsW32`,
    `ClosedOrbitPayloadInhabitationW32`, `ExactChainSourceCertificateW32`,
    `PositiveChainLargeTailAssemblyW32`, `LargeTailClosedPlacementRowsW32`,
    `RemainderSplitSourceClosureW32`, `PachTothW32NoFakeAudit`,
    `PachTothW32RouteAudit`, and `PachTothW32FinalAssembly`.
  - Swanepoel W32 targets:
    `SelectedFaceEnclosureBridgeW32`, `FaceBoundaryTopologySourceW32`,
    `ExtractedComponentsConcreteClosureW32`, `FrameCyclicOrderAssemblyW32`,
    `NoEarlyRouteCoverageClosureW32`, `ExactFigureRowsAssemblyW32`,
    `NoCutPointwiseBridgeW32`, `PointwiseLaneFinalBridgeW32`,
    `SwanepoelW32RouteAudit`, and `SwanepoelW32FinalAssembly`.
  - W32 completion gate:
    each produced `.lean` file must compile with pinned Lean 4.28.0 before root
    import, then the root import surface, source scans, trust scans, root build,
    and CI-style axiom audit must be expanded and replayed.
