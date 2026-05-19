# Global Task Tracker

This file is the executable task queue for the Lean formalization of Erdos
problem 1066.  It is intentionally not a wave ledger, route encyclopedia, build
log, or project-structure document.

Detailed theorem dependencies live in
`E:/Personal/Erdosproblems/1066/proof_workings/theorem_dependency_map.md`.
Source-paper proof plans live in `proof_workings/*_lean_ready.md`.

## Operating Rules

- Completion of the proof project is the target.  File count is not the
  scoreboard.
- A worker should own a closing obligation: prove a needed lemma, inhabit a
  concrete source field/package, verify a claimed closure, search mathlib,
  sharpen a theorem statement, or remove a blocked route from the live path.
- Add a new Lean file only when it gives a real ownership, import-boundary,
  reusable-certificate, or compile-time advantage.  Prefer proving related
  results near the existing owner module.
- Do not add another numbered facade/audit layer unless it directly shortens or
  closes a real obligation.
- Mark a task done only after the relevant declaration is imported by
  `E:/Personal/Erdosproblems/1066/ErdosProblems1066.lean`, builds with the
  pinned toolchain, and the forbidden-token scan is clean.
- `proof_workings/` is for proof-plan `.md` files only.  Disposable logs belong
  under ignored `proof_logs/`.

## Verification Gates

Before any public-bound claim or checked-off task:

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

Active certification tasks:

- [ ] Run the pinned full root build on the current checkout.
- [x] Run the forbidden-token scan on the current checkout.
- [x] Run the trust-source scan on the current checkout.
- [x] Run retained root import coverage and resolve missing, extra, or
  duplicate imports on that surface.
- [ ] Replay the CI-style axiom audit for the current endpoint list.
- [ ] Keep `KnownBounds.lean` closed to Swanepoel `8 / 31` and Pach--Toth
  `5 / 16` until unconditional internal verified theorems exist.

Root-state ledger: current retained source surface has root import coverage
`872/872` and clean forbidden/trust scans.  Earlier successful logs
`proof_logs/root_build_20260519_082033.out.log` and
`proof_logs/ci_axiom_audit_stdout_20260519_082158.txt` predate later Lean-file
edits, so they are no longer certification for the current checkout.  Re-run
the pinned full root build and CI-style axiom audit before crediting new
checked-off work.  The exact-base all-positive flexible source is refuted by
the root-imported W33/W34 blocker stack.  W33/W34 files are completion evidence
only for the conditional endpoints they prove; they do not close Swanepoel
`8 / 31` or Pach--Toth `5 / 16` without an unconditional internal theorem.
Lean/Lake CLI resolution has been repaired at the User PATH level: the WinGet
elan shim directory now precedes `C:/Users/Tom/bin`, so new shells resolve
`lean`/`lake` through the `leanprover/lean4:v4.28.0` toolchain.  Existing
shells should refresh PATH before verification.  Concurrent Lake jobs still
cause silent `-1` exits in this workspace; serialize final certification
builds.

## Swanepoel First

Finish Swanepoel `8 / 31` before broadening Pach--Toth work.  The live work is
source inhabitation for the compact `W34ActualRoutePremises` route, not more
facades or route ledgers.

### S1. No-Cut Minimal Failure

- [x] Treat no-cut as checked infrastructure and integration-only.
  - Checked route: `CutVertexSideCardFromMinimality` refutes
    `CutPartitionBothPlusSidesCutForcedData`; W32/W34 expose
    `NoCutPointwiseBridgeW32.noCutDependency_of_refuting_bothPlusSidesCutForced`
    and `NoCutMinimalityClosureW34.noCutVertexFamily_of_refuting_bothPlusSidesCutForced`.
  - Current action: use the checked no-cut family in final assembly.  Do not
    reopen cut-partition deletion, side-card, or actual-route-premise no-cut
    branches unless a theorem name has become stale.

### S2. Minimal-Failure Topology And Boundary Rows

- [ ] Construct the honest nondegenerate outer-boundary topology source.
  - Paper steps: `E8-E11`.
  - Owners:
    `Swanepoel/FaceBoundaryTopologySourceW32.lean`,
    `Swanepoel/OuterBoundaryCoreConstructionW28.lean`,
    `Swanepoel/JordanBoundaryConcrete.lean`,
    `Swanepoel/SelectedTopologyRowsInhabitationW33.lean`,
    `Swanepoel/BoundarySpineFiniteCertificate.lean`.
  - Live target:
    `FaceBoundaryTopologySourceW32.MinimalFailureRemainingActualOuterBoundaryCycleTheoremTarget`,
    equivalently `MinimalFailureNondegenerateMissingTopologyFactsTarget`.
  - Current exact S2 blocker:
    construct the actual unbounded-frontier boundary-edge carrier from
    `JordanTopologyFactsConcrete.MinimalFailureTopology.FinitePlanarOuterComponentInputs C`.
    The checked reducer
    `ExteriorComponentTopology.unboundedExteriorFrontierCycleRows_of_connected_two_regular_frontier_graph`
    closes S2 once this carrier is supplied as a finite connected two-regular
    graph whose injective hom into `GraphBridge.unitDistanceSimpleGraph C`
    has vertex image exactly the graph vertices on
    `frontier (ExteriorComponentTopology.unboundedExteriorComponentRows C inputs).exterior`.
    Do not use the induced graph on all frontier vertices as the target:
    boundary chords can make that graph degree greater than two.
  - Newest reduction: `OuterBoundaryCoreConstructionW28.outerBoundaryCoreSource_with_length_iff_remainingActualOuterBoundaryCycleTheorem`
    identifies the remaining actual-cycle theorem with a concrete W28
    `OuterBoundaryCoreSource` plus `3 <= outerCycle.length`; the weak
    adjacent-pair selected-face witness is not enough for this route.
  - Latest source-with-length bridge:
    `FaceBoundaryTopologySourceW32.remainingActualOuterBoundaryCycleTheorem_of_exactFiniteNoncrossingActualOuterBoundaryCycleTheorem`
    now factors the exact finite-noncrossing face-boundary package through W28
    `OuterBoundaryCoreSourceWithLength`, with
    `EnclosureAndFaceBoundaryW31.ofOuterBoundaryCore_toOuterBoundaryCore` as
    the W31 projection helper.  Stale graph-cycle adapters are out of the live
    route.
  - Boundary-witness split:
    `SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologyWitnessFamily_nonempty_iff_exists_skeleton_missingLongArcTriangleRunField`
    reduces the old witness-family target to a skeleton plus the exact missing
    field
    `JordanBoundaryConcreteInhabitationW24.MinimalBoundaryTopologySkeleton.MissingLongArcTriangleRunField`.
    The skeleton carries topology, classification/counts, angle comparison, and
    subpolygon rows; the missing field carries only the concrete long-arc data
    and triangle run over that assembled planar boundary.
  - Next action: prove the finite noncrossing canonical unit-distance graph has
    that nondegenerate actual outer-boundary core, then build the
    `MinimalBoundaryTopologySkeletonFamily` rows that S3 and the exact missing
    field can complete into `ActualTopologyComponentClosurePackage` and the
    finite `p_i/q_i` spine.
  - Latest exact field bridge:
    `FaceBoundaryTopologySourceW32.minimalFailureFiniteNoncrossingSourceTarget_iff_minimalFaceBoundaryFieldPackage`
    identifies the finite-noncrossing source with dependent face-boundary rows:
    `UnitDistanceFaceBoundaryHypotheses`, selected outer face `F`,
    `H.IsOuterFace F`, `3 <= H.boundaryLength F`, and a matching
    `OuterBoundaryEnclosure`.  The remaining S2 work is to prove those rows
    for the canonical unit-distance graph of each minimal failure.
  - Mencius bridge now available:
    `FaceReduction.UnitDistanceFaceBoundaryHypotheses.ofOuterBoundaryCycle`
    and
    `FaceReduction.UnitDistanceFaceBoundaryHypotheses.exists_outerFace_length_ge_three_ofOuterBoundaryCycle`
    turn an extracted simple cyclic outer-boundary row into the required
    `H/F/outer/length >= 3` rows.  Current S2 work should connect the existing
    extracted-boundary row and matching enclosure predicates to
    `OuterBoundaryExistenceConcrete.ExactActualTopologyFields`; do not search
    for a Mathlib face API or duplicate this bridge.
  - Latest concrete field package:
    `OuterBoundaryExistenceConcrete.ExactActualTopologyFields` is the current
    nondegenerate S2 package.  It is equivalent to the remaining actual
    outer-boundary-cycle theorem and to an `OuterBoundaryCore` with
    `3 <= outerCycle.length`.  The task is now positive inhabitation of this
    package, not another bridge.
  - Newest target name:
    `FaceBoundaryTopologySourceW32.MinimalFailureExactActualTopologyFieldsTarget`
    is the source-level S2 target.  It is equivalent to the exact finite
    noncrossing actual-cycle target and the remaining actual-cycle theorem via
    `minimalFailureExactActualTopologyFieldsTarget_iff_exactFiniteNoncrossingActualOuterBoundaryCycleTheoremTarget`
    and
    `minimalFailureExactActualTopologyFieldsTarget_iff_remainingActualOuterBoundaryCycleTheoremTarget`.
    The exact positive obligation is to supply, for every minimal failure,
    either face-boundary field rows through
    `minimalFailureExactActualTopologyFieldsTarget_of_faceBoundaryFieldRows`
    or an `OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryRow`
    plus matching enclosure rows through
    `minimalFailureExactActualTopologyFieldsTarget_of_extractedOuterBoundaryCycle_enclosureRows`.
  - Latest exact row entrances:
    `minimalFailureExactActualTopologyFieldsTarget_of_w31JordanSourceRows_with_length`
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_outerBoundaryCoreSourceWithLengthRows`
    are the current shortest S2 constructors.  The remaining positive work is
    not another bridge; it is an honest
    `MinimalFailureOuterBoundaryCoreSourceWithLengthRows` family or the
    extracted simple cyclic boundary row plus matching `insideOrOn`,
    `onBoundary`, and enclosure predicates.
  - Latest bundled S2 source:
    `OuterBoundaryExistenceConcrete.ExtractedSimpleCyclicOuterBoundaryEnclosureRows`
    packages the extracted cyclic boundary with the matching enclosure
    predicates, and
    `FaceBoundaryTopologySourceW32.MinimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows`
    is the minimal-failure row family that feeds
    `minimalFailureExactActualTopologyFieldsTarget_of_extractedSimpleCyclicOuterBoundaryEnclosureRows`.
    Inhabit that bundle or `MinimalFailureOuterBoundaryCoreSourceWithLengthRows`;
    do not add another S2 target synonym.
  - Latest positive S2 projection:
    `ExtractedSimpleCyclicOuterBoundaryEnclosureRows.ofOuterBoundaryCoreWithLength`
    and `.ofActualOuterBoundaryCycleData` show that the bundled S2 rows are
    inhabited exactly by the strong W28/source-with-length or actual-cycle
    sources.  The weak adjacent-pair selected-face lane has boundary length `2`
    and is not the live route.
  - Newest checked S2 bridge:
    `FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_actualOuterBoundaryCycleDataRows`
    maps a minimal-failure family of actual outer-boundary-cycle data directly
    to `MinimalFailureExactActualTopologyFieldsTarget`.  In
    `OuterBoundaryExistenceConcrete`,
    `ExtractedSimpleCyclicOuterBoundaryEnclosureRows.nonempty_iff_exactActualTopologyFields`
    and
    `.nonempty_iff_outerBoundaryCore_with_length_ge_three` identify the row
    bundle with exact actual topology fields or a real `OuterBoundaryCore`
    with `3 <= outerCycle.length`.
  - Current checked S2 adapter status:
    `minimalFailureExtractedSimpleCyclicOuterBoundaryEnclosureRows` still passes
    through an extracted-cycle compatibility shim whose enclosure predicates are
    trivial (`insideOrOn := fun _ => True`).  Treat this as
    compile/bookkeeping progress only, not as an honest planar
    outer-boundary/enclosure source.  The no-argument theorem previously named
    `minimalFailureExactActualTopologyFieldsTarget` has been quarantined as
    `bookkeeping_minimalFailureExactActualTopologyFieldsTarget_of_syntheticCycleEnclosure`
    so it cannot masquerade as a live S2 proof.  The live S2 proof remains the
    strong W28/source-with-length route or actual outer-boundary-cycle data with
    nontrivial `OuterBoundaryEnclosure` fields.  The shortest positive source
    is now a minimal-failure family of nondegenerate actual outer-boundary
    cores, equivalently `MinimalFailureOuterBoundaryCoreSourceWithLengthRows`.
    Newest honest S2 adapters:
    `OuterBoundaryExistenceConcrete.exactActualTopologyFields_of_outerBoundaryCoreWithLength`
    and `.exactActualTopologyFields_of_actualOuterBoundaryCycleData` route
    exact topology fields through the real `outerEnclosure` carried by
    outer-boundary core/cycle data, not through the synthetic extracted-cycle
    shim.  `FaceBoundaryTopologySourceW32` now also has nonempty forms
    `minimalFailureExactActualTopologyFieldsTarget_of_nonempty_outerBoundaryCoreSourceWithLengthRows`
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_nonempty_actualOuterBoundaryCycleDataRows`.
    Separately, `JordanBoundaryConcrete.SimpleCyclicOuterBoundaryEnclosureRows`
    is the concrete nondegenerate simple-cycle-plus-matching-enclosure row
    surface and feeds actual outer-boundary-cycle data via
    `MissingTopologyFacts.remainingActualOuterBoundaryCycleTheorem_of_simpleCyclicOuterBoundaryEnclosureRows`.
    `FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_simpleCyclicOuterBoundaryEnclosureRows`
    is the direct minimal-failure adapter from that concrete row family to the
    live exact S2 target.
  - S2-J flexible Jordan source:
    `JordanBoundaryConcrete.MinimalFailureJordanOuterComponentSourceRows` is
    the live S2 bridge: choose a genuine outer-component unit-distance cycle
    together with matching `insideOrOn`, `onBoundary`, all-vertices-inside, and
    boundary-iff-cycle predicates.  It feeds W33 through
    `FaceBoundaryTopologySourceW32.minimalFailureActualOuterBoundaryCycleDataRowsOfJordanOuterComponentSourceRows`,
    `minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_jordanOuterComponentSourceRows`,
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_nonempty_jordanOuterComponentSourceRows`.
    The canonical girth-cycle source remains a sufficient special case, but it
    is not the required live route unless that selected cycle is proved to be
    outer.
  - S2-K chosen-cycle usability surface:
    `JordanBoundaryConcrete.ChosenJordanOuterComponentRow` is the positive
    one-configuration package for an explicitly chosen outer-component
    `UnitDistanceCycleBoundary` plus its matching
    `JordanOuterComponentEnclosure`.
    `minimalFailureJordanOuterComponentSourceRowsOfChosen`,
    `simpleCyclicOuterBoundaryEnclosureRowsOfChosenJordanOuterComponentRows`,
    and
    `actualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows`
    project that chosen-cycle source to the existing S2 rows without using the
    canonical girth cycle or the synthetic extracted-cycle enclosure shim.
    Newest checked W32 consumer adapters:
    `FaceBoundaryTopologySourceW32.minimalFailureJordanOuterComponentSourceRowsOfChosenJordanOuterComponentRows`,
    `minimalFailureActualOuterBoundaryCycleDataRowsOfChosenJordanOuterComponentRows`,
    `minimalFailureRemainingActualOuterBoundaryCycleTheoremTarget_of_chosenJordanOuterComponentRows`,
    and
    `minimalFailureExactActualTopologyFieldsTarget_of_chosenJordanOuterComponentRows`
    route the chosen outer-component family directly into the live S2 exact
    topology target.  Do not retask workers with this consumer bridge; the
    remaining S2 obligation is the positive chosen-row theorem itself.
    `minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem`
    now composes the finite planar outer-component theorem directly into the
    live exact topology target.  Remaining S2 work is the actual finite planar
    outer-component theorem source, not another W32 consumer bridge.
    Verified consumer chain:
    `FinitePlanarStraightLineOuterComponentTheorem` ->
    `minimalFailureChosenRows_of_finitePlanarOuterComponentTheorem` ->
    `minimalFailureExactActualTopologyFieldsTarget_of_chosenJordanOuterComponentRows`
    -> `minimalFailureExactActualTopologyFieldsTarget_of_finitePlanarOuterComponentTheorem`.
    `SelectedTopologyRowsInhabitationW33.MinimalFailureExactActualTopologyFieldsTarget`
    is an abbrev of the same W32 target, so S6 can consume this path directly.
    Newest chosen-row constructors:
    `JordanBoundaryConcrete.chosenJordanOuterComponentRowOfBoundaryEnclosure`,
    `chosenJordanOuterComponentRowOfJordanOuterComponentSource`,
    `chosenJordanOuterComponentRow_of_minimalClearedFailure`,
    `minimalFailureChosenJordanOuterComponentRowsOfSourceRows`, and
    `minimalFailureChosenJordanOuterComponentRowsOfCanonical` reduce
    `MinimalFailureChosenJordanOuterComponentRows` to either a real
    `MinimalFailureJordanOuterComponentSourceRows` family or a matching
    `JordanOuterComponentEnclosure` for the canonical minimal-failure cycle.
    Exact remaining positive theorem:
    produce that source/enclosure family.  The missing mathematical lemma is
    the finite planar straight-line graph theorem:
    connected noncrossing unit-edge graph, no cut vertex, and at least one
    cycle imply an outer face bounded by a simple graph cycle, with
    `insideOrOn`, `onBoundary`, all-vertices-inside, and
    boundary-iff-cycle predicates.  Convex-hull vertices do not solve this
    because `UDConfig.sep` gives distance `>= 1`, not unit graph edges.
    `JordanTopologyFactsConcrete.FinitePlanarOuterComponentInputs` is the
    checked graph-side source package for that theorem, and
    `FinitePlanarStraightLineOuterComponentTheorem` is the exact missing
    theorem surface:
    for each `UDConfig`, those inputs produce a nonempty
    `ChosenJordanOuterComponentRow`.  `minimalFailureChosenRows_of_finitePlanarOuterComponentTheorem`
    then closes the chosen-row S2 family.
    `OuterBoundaryInterface.OuterBoundaryEnclosure` now has projection helpers
    (`boundaryCycle_vertex_onBoundary`, `boundaryCycle_point_insideOrOn`,
    `onBoundary_iff_boundaryCycle`, `insideOrOn_of_onBoundary`, and package
    projections) for consuming that future outer-face theorem.
    `OuterBoundaryExistenceConcrete` now has the real-enclosure equivalences
    `exactActualTopologyFields_iff_nonempty_actualOuterBoundaryCycleData`,
    `nonempty_actualOuterBoundaryCycleData_iff_exactActualTopologyFields`,
    `exactActualTopologyFields_iff_nonempty_simpleCyclicOuterBoundaryEnclosureRows`,
    `nonempty_simpleCyclicOuterBoundaryEnclosureRows_iff_exactActualTopologyFields`,
    and `remainingActualOuterBoundaryCycleTheorem_iff_exactActualTopologyFields`.
    These routes preserve `outerEnclosure`; avoid any synthetic
    `insideOrOn := True` closure when consuming exact topology fields.
    Minimal implementation plan for
    `FinitePlanarStraightLineOuterComponentTheorem`: build a local
    dart/rotation-system theorem for the canonical straight-line graph; define
    the face successor on oriented unit edges by cyclic angular order; choose
    the orbit of an extremal exterior dart; prove that orbit is a simple
    unit-edge cycle using connectedness/no-cut to rule out bridge-like repeats;
    define the exterior component with `connectedComponentIn` on the complement
    of the finite embedded edge set; and package the resulting enclosure
    predicates into `ChosenJordanOuterComponentRow`.
    The first checked dart surface is in place:
    `UnitDistanceDart`, `VertexCyclicAngularSuccessor`,
    `UnitDistanceRotationSystem`, `FaceDartOrbit`,
    `ExteriorDartOrbitEnclosure`, `ExteriorDartOrbitSource`,
    `FinitePlanarStraightLineExteriorDartOrbitTheorem`, and
    `finitePlanarStraightLineOuterComponentTheorem_of_exteriorDartOrbitTheorem`.
    `JordanTopologyFactsConcrete` now constructs the face orbit from concrete
    cycle successor data: `UnitDistanceDart.ofBoundary`,
    `UnitDistanceCycleFaceSuccRows`, and `FaceDartOrbit.ofBoundaryFaceSuccRows`
    turn a unit-distance cycle plus rotation-system successor rows into a
    simple face orbit.  With a matching `JordanOuterComponentEnclosure`,
    `selectedExteriorDartOrbitSource` produces the exterior orbit source.
    Remaining S2 input is choosing/proving the genuine exterior cycle, its
    `UnitDistanceCycleFaceSuccRows`, and the matching enclosure.
    Newest dart reduction:
    `UnitDistanceRotationSystem.faceSucc_dist_eq_one`,
    `FaceDartOrbit.dart_injective`,
    `ExteriorDartOrbitEnclosure` boundary/inside projections, and
    `finitePlanarStraightLineOuterComponentTheorem_of_faceOrbitJordanEnclosure`
    reduce S2 to the concrete source: construct a real
    `UnitDistanceRotationSystem`, a simple exterior `FaceDartOrbit`, and a
    matching `JordanOuterComponentEnclosure` for each
    `FinitePlanarOuterComponentInputs C`.
    `JordanTopologyExteriorEnclosure` is now root-imported and reduces the
    enclosure side further: exterior frontier/closure rows construct a
    `JordanOuterComponentEnclosure`, then `FaceOrbitJordanEnclosureSource`,
    then `FinitePlanarStraightLineExteriorDartOrbitTheorem` and
    `FinitePlanarStraightLineOuterComponentTheorem`.  The remaining S2 topology
    source is the actual exterior frontier/closure rows and simple face orbit,
    not another enclosure adapter.
    Latest exterior-frontier reduction: boundary vertices are on the frontier
    from the single `frontier_iff_cycle_vertex` row, and boundary closure rows
    follow from `frontier_compl` / `frontier_subset_closure`.  The exact
    remaining topological fact is: graph vertices on `frontier exterior` are
    exactly the chosen orbit vertices, and non-orbit graph vertices lie in
    `closure exteriorᶜ` (stronger: are not in `exterior`).
    Latest reduced S2 source layer:
    `VertexFiniteUnitNeighborCyclicOrder`,
    `FiniteUnitNeighborRotationSource`,
    `UnitDistanceRotationSystem.nonempty_iff_finiteUnitNeighborRotationSource`,
    `FaceOrbitJordanEnclosureSource`,
    `finitePlanarStraightLineExteriorDartOrbitTheorem_iff_faceOrbitJordanEnclosureSource`,
    and
    `finitePlanarStraightLineOuterComponentTheorem_of_faceOrbitJordanEnclosureSource`.
    Remaining: prove finite unit-neighbor cyclic angular order and a genuine
    face-orbit Jordan enclosure source; do not add another equivalent wrapper.
    `finitePlanarStraightLineOuterComponentTheorem_of_angularSuccessorRows`
    now consumes actual per-vertex `VertexCyclicAngularSuccessor` rows together
    with a matching `FaceDartOrbit` and `JordanOuterComponentEnclosure`.
    Remaining S2 work is the real angular-successor construction and the
    exterior face-orbit/Jordan enclosure proof.
    `finitePlanarStraightLineOuterComponentTheorem_of_finiteUnitNeighborCyclicOrderRows`
    now reduces the angular-successor input to finite-neighbor cyclic-order
    rows, using `VertexFiniteUnitNeighborCyclicOrder.angularSuccessorRows` and
    `FiniteUnitNeighborRotationSource.angularSuccessorRows`.  Remaining S2
    work is actual cyclic angular order for each finite neighbor set and the
    face-orbit/Jordan enclosure proof.
    `VertexFiniteUnitNeighborCyclicOrder.identity`, `.identityRows`,
    `.rows_nonempty`, and the refactored
    `finitePlanarStraightLineOuterComponentTheorem_of_angularSuccessorRows`
    are checked convenience paths.  They do not replace the need for a genuine
    exterior face-orbit/Jordan enclosure source.
    Newest S2 source rows:
    `VertexFiniteUnitNeighborCyclicOrder.identityAngularSuccessorRows`,
    `FiniteUnitNeighborRotationSource.ofCyclicOrderRows`,
    `FiniteUnitNeighborRotationSource.identity`, and
    `UnitDistanceRotationSystem.ofFiniteUnitNeighborCyclicOrderRows` now supply
    the finite unit-neighbor rotation-system side.  The remaining honest S2
    topology payload is exactly the exterior `FaceDartOrbit` plus matching
    `JordanOuterComponentEnclosure`.
    `OuterBoundaryExistenceConcrete` now has real-enclosure consumers
    `exactActualTopologyFields_of_chosenJordanOuterComponentRow`,
    `exactActualTopologyFields_of_nonempty_chosenJordanOuterComponentRow`, and
    `exactActualTopologyFields_of_finitePlanarOuterComponentTheorem`.  These
    preserve the chosen row's `JordanOuterComponentSource`; the remaining S2
    theorem is still the positive
    `FinitePlanarStraightLineOuterComponentTheorem`.
    Latest S2 positive adapters:
    `JordanBoundaryConcrete.JordanOuterComponentSource.ofBoundaryEnclosureRow`,
    `minimalFailureJordanOuterComponentSourceRowsOfBoundaryEnclosureRows`, and
    `minimalFailureChosenJordanOuterComponentRowsOfBoundaryEnclosureRows`
    consume an actual unit-distance cycle plus matching
    `JordanOuterComponentEnclosure` without importing the downstream face-orbit
    module.  In `JordanTopologyFactsConcrete`, concrete
    `UnitDistanceCycleFaceSuccRows` plus such an enclosure now build
    `FinitePlanarStraightLineExteriorDartOrbitTheorem` and
    `FinitePlanarStraightLineOuterComponentTheorem`.  In
    `FaceBoundaryTopologySourceW32`,
    `minimalFailureExactActualTopologyFieldsTarget_of_exterior_frontier_not_mem`
    consumes the sharper exterior-frontier route from
    `JordanTopologyExteriorEnclosure.finitePlanarStraightLineOuterComponentTheorem_of_exterior_frontier_not_mem`.
    Remaining S2 work is the actual exterior unit-distance cycle and its
    nontrivial exterior frontier row.
    Shortest current checked reducer:
    `JordanTopologyExteriorEnclosure.finitePlanarStraightLineOuterComponentTheorem_of_exterior_cycle_frontier_not_mem`
    now packages the boundary-following rotation system and face orbit from a
    selected cycle.  The exact remaining blocker is therefore the finite
    planar straight-line outer-component theorem in the following row shape:
    for every `C` and `FinitePlanarOuterComponentInputs C`, choose
    `B : JordanBoundaryConcrete.UnitDistanceCycleBoundary C` and
    `exterior : Set PlanarInterface.Point` such that graph vertices on
    `frontier exterior` are exactly the vertices of `B`; once `exterior` is a
    subset of the drawing complement, non-cycle graph vertices not in
    `exterior` are automatic.
    Drawing groundwork now lives in `Swanepoel/FinitePlaneDrawing.lean`:
    `closedSegment_eq_image_Icc`, `isCompact_closedSegment`,
    `isClosed_closedSegment`, `embeddedEdgePairs`,
    `mem_embeddedEdgeSet_iff_exists_embeddedEdgePairs`,
    `embeddedEdgeSet_closed`, `embeddedEdgeSet_compact`,
    `drawingComplement_open`, `drawingComplement_nonempty`,
    `frontier_drawingComplement_subset_embeddedEdgeSet`, and
    `vertex_mem_embeddedEdgeSet_of_inputs` are checked.  Do not reprove
    finite-union closedness, compactness, complement nonemptiness, or endpoint
    membership.
    `Swanepoel/ExteriorComponentTopology.lean` is the current next reducer:
    `ExteriorComponentRows` records an open exterior subset of
    `drawingComplement C`, `drawingComplementRows` gives the whole open
    complement as a candidate, and `ExteriorConnectedComponentRows` packages
    open connected components of the drawing complement.  The unbounded
    component is now constructed by `unboundedExteriorComponentRows`, using a
    rightward x-axis ray outside the compact embedded drawing; graph vertices
    are proved outside it and its frontier lies in the embedded drawing.  The
    helper `unboundedExteriorFrontierCycleRowsOfBoundary` shows the exact
    remaining S2 source: choose the simple unit-distance outer cycle for that
    unbounded component and prove `frontier_iff_cycle_vertex`.
    `FaceBoundaryTopologySourceW32.minimalFailureExactActualTopologyFieldsTarget_of_unboundedExteriorFrontierCycleRows`
    consumes that row family and the no-cut rows directly.

### S3. Angle And Subpolygon Packages

- [ ] Prove selected nondegenerate outer-face sector/order rows.
  - Paper steps: `E12-E13`.
  - Owners:
    `Swanepoel/OuterBoundaryAngleSourceW34.lean`,
    `Swanepoel/BoundaryCountingInstantiationW10.lean`,
    `Swanepoel/PlanarBoundaryFaceDataRefinement.lean`,
    `Swanepoel/SubpolygonSelectedGeometrySourceW34.lean`.
  - Live target:
    `OuterBoundaryAngleSourceW34.SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`
    for the S2 nondegenerate topology target.
  - Newest reduction: that single theorem projects to
    `SelectedTopologyLocalAngleGeometryRows`,
    `ActualSelectedBoundaryEuclideanAngleRows`, and
    `MinimalFailureActualOuterBoundaryAngleDataRows` through the checked
    W34/W10 accounting path.  The concrete accounting support theorem is
    `OuterBoundaryAngleSourceW34.selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_polygon_of_angleMassBudgets`,
    backed by
    `BoundaryCountingInstantiationW10.ClassifiedBoundary.UnitSeparatedLocalAngleFamilies.accountedAngleSum_le_polygon_of_angleMassBudgets`.
  - Next action: choose the selected `longArc` predicate and prove the local
    angle rows are ordered, disjoint outer-face sectors whose accounted mass is
    bounded by the simple-polygon interior-angle sum.  Subpolygon realization
    is already on the selected outer-face lane; do not add another adapter.
  - Latest exact projection:
    `selectedTopologyLocalAngleFamiliesOfMinimalFailure_accountedAngleSum_le_simpleOuterPolygonInteriorAngleSum_of_outerFaceSectorOrder`
    extracts the scalar inequality from
    `SelectedTopologyLocalAngleOuterFaceSectorOrderRows`.  The remaining fields
    are the honest sector angles, nonnegativity, local accounted-mass
    containment in the ordered sector sum, and the simple-polygon sector-sum
    bound.
  - Scalar-accounting bookkeeping:
    `OuterBoundaryAngleSourceW34.selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_generatedAccountedAngleSum`
    and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_iff_exists_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum`
    are checked bookkeeping equivalences only.  Do not present the generated
    scalar inequality as the live S3 proof route.  The remaining S3 source is
    honest sector-containment, genuine triangulation, or genuine
    ear-decomposition angle-mass data.
  - Latest S2 adapter:
    `OuterBoundaryAngleSourceW34.remainingActualCycleSkeletonRemainderRowsOfOuterFaceSectorOrderTheorem`
    converts a proved honest
    `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem` into the exact
    `RemainingActualCycleSkeletonRemainderRows` field required by W34 final
    assembly.
  - Newest positive sources:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_angleMassBudgetedSectorRows`,
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_triangulationAngleMassBudgetRows`,
    and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_earDecompositionAngleMassBudgetRows`
    are the current concrete S3 entrances.  Prove one honest sector/triangulation
    or ear-decomposition angle-mass package; do not add another scalar wrapper.
    The triangulation/ear packages now require
    `budgetSum_le_orderedOuterFaceSectorSum`, so the budget rows must fit
    directly inside the ordered outer-face sector sum before using
    `orderedOuterFaceSectorSum_eq_simpleOuterPolygonInteriorAngleSum`.
    The triangulation rows are currently inhabited from the generated scalar budget by
    `selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRowsOfGeneratedAccountedAngleSum`
    and
    `nonempty_selectedNondegenerateTopologyLocalAngleOuterFaceTriangulationAngleMassBudgetRows_of_generatedAccountedAngleSum_le_simpleOuterPolygonInteriorAngleSum`.
    Treat these as scalar bookkeeping helpers only: they concentrate the whole
    polygon angle sum into one sector and use formal constant-angle triangles,
    so they must not be credited as an honest E12/E13 proof.
    Preferred current entrance:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_sectorContainmentRows`.
    It uses `SelectedTopologyLocalAngleOuterFaceSectorContainmentRows`, where
    generated local angle slots are assigned to selected outer-face sectors and
    per-sector loads are bounded directly.  Populate those sector-containment
    rows rather than reviving the arbitrary generated-witness scalar route.
    The honest missing row is actual outer-face sector angles at each selected
    boundary vertex, Swanepoel cyclic unit-neighbor gaps for the generated
    local slots, correct per-slot sector assignment, per-sector load
    containment, and the real polygon angle-sum theorem.
    Subpolygon bookkeeping is not the current blocker:
    `SubpolygonSelectedGeometrySourceW34.planarBoundaryFaceDataOfMinimalFailureSelectedClassification_subpolygonData_eq_realizationFamily`
    identifies the skeleton subpolygon-data projection with the selected
    outer-face W33 realization family, and
    `selectedOuterFaceRealizationFamilyDataOfMinimalFailureSelectedClassificationFields_lowDegreeWithHighDegreeSlack`
    exposes the E13 high-degree slack row from that family.
    The clean honest sector route should pass through
    `SelectedTopologyActualBoundaryNeighborSectorContainmentRows`; its existing
    converter fills the generic budget rows by the actual local angle values.
    The sector angle source is the predecessor/current/successor boundary
    angle, available via
    `BoundaryAngleWitnessConstruction.UnitSeparatedAngle.ofOuterBoundaryCoreIndex`
    or the `BoundaryWalkBridge` predecessor/successor angle rows.  The missing
    S3 content is therefore the six slot-to-sector maps, per-sector load
    containment into those actual PCS angles, and the real polygon sector-sum
    bound.
    Newest checked S3 reduction:
    `selectedBoundaryDegree3SlotSectorOfIndex`,
    `selectedBoundaryDegree4SlotSectorOfIndex`,
    `selectedBoundaryDegree5SlotSectorOfIndex`,
    `selectedBoundaryDegree6SlotSectorOfIndex`,
    `selectedBoundaryNontriangleSlotSectorOfIndex`, and
    `selectedBoundaryLongArcSlotSectorOfIndex` assign all generated slots to
    the same actual boundary-index sector.  The compact entrance is now
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexSectorRows`.
    The remaining honest S3 inputs are exactly the pointwise
    `selectedBoundaryIndexSectorLoad <= actualBoundaryNeighborSector` row and
    the actual PCS boundary-sector angle-sum bound by the simple-polygon
    interior-angle sum.
    W10 now exposes that second input as an honest row package:
    `BoundaryCountingInstantiationW10.ClassifiedBoundary.BoundaryNeighborSectorAngleSumRows`,
    with `boundaryCyclePolygonAngleSum` matching the selected-topology
    cycle-length polygon sum.  `BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndex`
    builds the package from canonical predecessor/current/successor boundary
    sectors once the genuine polygon sector-sum inequality is proved.  The
    remaining S3 geometric inequality is therefore the local pointwise
    sector-load bound, plus the still-genuine proof of the PCS sector-sum
    inequality for the simple outer polygon.
    W34 adapter now available:
    `boundaryNeighborSectorAngleSumRows_le_simpleOuterPolygonInteriorAngleSum`
    and
    `selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfBoundaryIndexSectorsAndAngleSumRows`
    consume W10's `BoundaryNeighborSectorAngleSumRows` directly on the selected
    topology route.  The remaining local S3 source is the pointwise
    `selectedBoundaryIndexSectorLoad <= actualBoundaryNeighborSector` proof.
    Newest W10 polygon-angle bridge:
    `ClassifiedBoundary.simplePolygonInteriorAngleAt` and
    `simplePolygonInteriorAngleSum` spell the actual PCS interior-angle sum.
    `BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfSimplePolygonInteriorAngleSum`
    constructs W10 sector-sum rows from the genuine theorem
    `simplePolygonInteriorAngleSum P <= boundaryCyclePolygonAngleSum P`.
    This is the exact polygon-angle theorem still needed on the selected outer
    cycle; no generated scalar budget closes it.
    Newest W10 sector/polygon accounting:
    `triangulationAngleSum_eq_boundaryCyclePolygonAngleSum`,
    `simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum_of_triangulationAngleSum`,
    `BoundaryNeighborSectorAngleSumRows.boundarySector_value_eq_simplePolygonInteriorAngleAt`,
    `.sectorAngleSum_eq_simplePolygonInteriorAngleSum`, and
    `.ofOuterBoundaryCoreIndexOfTriangulationAngleSum`.  Remaining W10-facing
    S3 input is genuine triangulation angle-sum data and the matching
    boundary-sector equality for the selected topology rows.
    Newest S3 gap-decomposition source:
    `SelectedTopologyBoundaryCyclicNeighborGapRows` is the explicit row package
    for the missing pointwise load proof.  It carries, per boundary vertex, the
    neighbor interval from boundary predecessor to successor, consecutive gap
    angles, generated-slot-to-gap maps, slot value equalities,
    slot-load-to-gap-sum, and gap-sum-to-PCS-sector inequalities.  It feeds the
    current S3 route through
    `selectedTopologyActualBoundaryNeighborSectorContainmentRowsOfCyclicNeighborGapRowsAndAngleSumRows`
    and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborGapRowsAndAngleSumRows`.
    The remaining positive S3 work is honest construction of these cyclic
    neighbor gap rows from planar unit-neighbor order geometry.
    Newest S3 interval source:
    `SelectedTopologyBoundaryCyclicNeighborIntervalRows` reduces the gap-row
    package to an ordered unit-neighbor interval.  The consecutive
    `UnitSeparatedAngle` gap witnesses are now constructed from
    `neighbor_unit` plus `neighbor_injective` by
    `SelectedTopologyBoundaryCyclicNeighborIntervalRows.toCyclicNeighborGapRows`.
    The final S3 constructor
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_cyclicNeighborIntervalRowsAndAngleSumRows`
    consumes these interval rows plus W10 sector-sum rows.  The remaining
    honest S3 theorem is construction of the interval rows from real planar
    cyclic unit-neighbor order data, including slot-to-gap value equalities,
    load-to-gap-sum, and gap-sum-to-PCS-sector inequalities.
    Newest per-index source:
    `SelectedBoundaryIndexCyclicNeighborIntervalRows` and
    `SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows` localize that
    obligation at each selected boundary index; their `.toIntervalRows`
    projection builds the global interval rows.  The exact remaining S3 source
    is now the real ordered unit-neighbor interval from boundary predecessor
    to successor at each boundary vertex.
    Latest interval-to-sector bridge:
    `SelectedTopologyBoundaryIndexCyclicNeighborIntervalRows.toCyclicNeighborGapRows`,
    `.sectorLoad_le_boundarySectorAngle`,
    `.toActualBoundaryNeighborSectorContainmentRowsAndAngleSumRows`,
    `.toLocalAngleOuterFaceSectorOrderRowsAndAngleSumRows`, and
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndAngleSumRows`
    connect per-boundary-index interval rows plus W10 sector-sum rows to the
    live sector-order theorem.  Remaining S3 work is actual interval rows,
    matching `BoundaryNeighborSectorAngleSumRows`, and `boundarySector_eq`.
    The generic interval constructor is now
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndBoundaryNeighborSectorAngleSumRows`,
    and `actualBoundaryNeighborSectorOfOuterBoundaryCoreIndex_sectorAngleSum_eq_simplePolygonInteriorAngleSum`
    removes the remaining explicit `boundarySector_eq` input.  The
    triangulation variant builds W10 rows via
    `BoundaryNeighborSectorAngleSumRows.ofOuterBoundaryCoreIndexOfTriangulationAngleSum`.
    Newest canonical S3 constructor:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSimplePolygonInteriorAngleSumRows`
    builds the W10 sector rows canonically from the genuine simple-polygon
    interior-angle inequality and discharges `boundarySector_eq` by `rfl`.
    Remaining S3 inputs are now actual boundary-index cyclic-neighbor interval
    rows and the genuine simple-polygon interior-angle inequality.
    Latest triangle-point S3 constructor:
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalRowsAndSelectedOuterBoundaryNondegenerateTrianglePointRows`
    and the source-row variant consume selected outer-boundary nondegenerate
    triangle-point rows directly.  Remaining S3 inputs are actual interval
    rows and selected triangle-point rows.
    S3 source rows are now split as
    `SelectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows` and
    `SelectedNondegenerateTopologySimplePolygonInteriorAngleSumRows`, with
    `selectedNondegenerateTopologyOuterFaceSectorOrderTheorem_of_boundaryIndexCyclicNeighborIntervalSourceRowsAndSimplePolygonInteriorAngleSumRows`
    as the canonical constructor.  The simple-polygon row is supplied by
    triangulation rows through
    `selectedNondegenerateTopologySimplePolygonInteriorAngleSumRowsOfTriangulationRows`.
    `PlanarBoundaryFaceDataRefinement.SelectedOuterBoundaryNondegenerateTrianglePointRows.ofCorePolygonTriangleVertices`
    now constructs the selected nondegenerate triangle-point rows from distinct
    triangle corners in the actual core outer cycle, proving the side vector is
    nonzero internally.  Do not rebuild this point-distinctness argument in S3;
    focus workers on the interval rows and the polygon angle-sum/triangulation
    source.
    `AngleGeometry.gapAngleSum_eq_sectorAngle_of_realAngle_eq_no_wrap` and
    `gapAngleSum_le_sectorAngle_of_realAngle_eq_no_wrap` are checked helpers
    for the last inequality: once cyclic order/no-crossing supplies the
    oriented `Real.Angle` telescope and the no-wrap bounds, they turn the
    telescope into the real-valued sector inequality required by the interval
    rows.  The remaining geometry is the oriented telescope and no-wrap proof,
    not another scalar accounting bridge.
    `AngleGeometry.oangle_sum_range_succ_eq_oangle` and
    `gapAngleSum_eq_sectorAngle_of_oangle_chain_no_wrap` now discharge the
    algebraic telescope once each consecutive gap is identified with the
    oriented angle between successive nonzero rays and the sector is identified
    with the first-to-last oriented angle.  S3 still must prove the actual
    cyclic-order/no-wrap hypotheses from planar neighbor order.
    Newest AngleGeometry support also includes Nat and `Fin (m + 1)` chain
    no-wrap equality/inequality forms plus concrete `angleAt` neighbor-chain
    lemmas shaped for downstream `UnitSeparatedAngle.value` goals.  The
    remaining S3 geometry is now the real planar neighbor-order/no-wrap input,
    not algebraic telescope manipulation.
    `BoundaryWalkBridge.EndpointNeighborInterval` supplies the honest
    endpoint-only interval data: predecessor first, successor last, adjacency
    to the center, and injectivity for length at least three.  The missing
    interval data is the full ordered unit-neighbor enumeration between those
    endpoints and the slot-to-gap/angle-sum fields.
    `OuterBoundaryAngleSourceW34` now has boundary-data row carriers based on
    `OuterBoundaryInterface.BoundaryCycle.EndpointNeighborInterval`, with
    `selectedNondegenerateTopologyBoundaryIndexCyclicNeighborIntervalRows_of_boundaryDataRows`
    projecting them into the selected-nondegenerate interval target.  The live
    S3 interval source is construction of those boundary-data endpoint/ordered
    neighbor rows from the actual outer boundary, not another interval adapter.
    `SelectedBoundaryIndexOrderedUnitNeighborData` and
    `SelectedBoundaryIndexCyclicNeighborSlotToGapRows` are the newest explicit
    boundary-index row surfaces: the first records the ordered cyclic
    unit-neighbor list, endpoints, unit proofs, and injectivity, and the second
    records the class-slot to consecutive-gap identifications and load/gap
    inequalities.  These feed the existing interval route; the remaining work
    is proving the real ordered unit-neighbor list and slot-to-gap geometry,
    not adding another carrier type.
    `OuterBoundaryAngleSourceW34` now consumes those two boundary-index rows
    directly, projecting them through actual/local sector-containment rows into
    `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`.  Do not add
    more S3 sector-containment wrappers; prove the ordered-neighbor and
    slot-to-gap rows or a real planar-cyclic-order source for them.
    `OuterBoundaryCoreConstructionW28` now constructs
    `EndpointNeighborInterval` with `gapCount = 1` from any nondegenerate
    boundary cycle, `OuterBoundaryCore`, source-with-length rows,
    actual-cycle data, or chosen Jordan outer-component rows.  The remaining S3
    boundary-order fact is the full ordered unit-neighbor/slot-to-gap data:
    cyclic neighbor list, class-slot maps, angle-value equalities,
    `slotLoad_le_gapAngleSum`, and `gapAngleSum_le_boundarySectorAngle`.
    `OuterBoundaryCoreConstructionW28.BoundaryIndexOrderedUnitNeighborData`
    is now the import-acyclic W28 endpoint-backed carrier and has constructors
    from boundary cycles, outer cores, source-with-length rows, actual-cycle
    data, and chosen Jordan rows.  It is positive endpoint data only; W34 still
    needs the full ordered unit-neighbor enumeration and slot-to-gap geometry.
    `PlanarBoundaryFaceDataRefinement.SimplePolygonInteriorAngleTriangulationRows`
    reduces the genuine simple-polygon angle bound to real triangulation rows:
    `length - 2` triangles, each with `angleAt` sum `pi`, and equality between
    polygon PCS angles and triangle-corner angles.  Construct these rows from
    a real triangulation or ear decomposition of the selected outer polygon.
    `PlanarBoundaryFaceData.SimplePolygonInteriorAngleTriangulationRows.ofNondegenerateTrianglePoints`
    now discharges each triangle's `pi` angle-sum from actual triangle corner
    points plus one nonzero side vector.  The remaining triangulation source is
    therefore the actual triangle-point/ear-decomposition data and polygon
    angle compatibility.
    `PlanarBoundaryFaceDataRefinement.SelectedOuterBoundaryNondegenerateTrianglePointRows`
    is the selected outer-boundary version of that source; its projections
    `toSimplePolygonInteriorAngleTriangulationRows`,
    `simplePolygonInteriorAngleSum_le_boundaryCyclePolygonAngleSum`, and
    `toBoundaryNeighborSectorAngleSumRows` feed the W10/S3 angle route from
    actual triangle points plus nonzero side data.
    `SelectedOuterBoundaryCorePolygonTriangulationRows` is now the strongest S3
    triangulation source: actual indexed outer-cycle triangle vertices,
    nondegenerate side data, and PCS polygon-angle compatibility.  It projects
    to selected nondegenerate triangle-point rows, honest triangulation rows,
    the pointwise `simplePolygonInteriorAngleSum <= boundaryCyclePolygonAngleSum`
    row, and W10 boundary-neighbor sector rows.  Remaining S3 work is positive
    construction of these triangulation rows and the endpoint/ordered-neighbor
    interval rows from the actual outer boundary.
    `SelectedOuterBoundaryCorePolygonEarDecompositionRows` is the newest
    ear-decomposition source in `PlanarBoundaryFaceDataRefinement`: it records
    actual ear triangles on the selected outer cycle, the `length - 2` count,
    nondegenerate side data, and PCS polygon-angle compatibility, and projects
    to the selected triangulation rows.  Remaining S3 triangulation work is
    honest construction of these ear rows from the simple outer polygon.
    `PlanarBoundaryFaceDataRefinement` now also carries actual indexed
    triangulation/ear angle fields (`triangleAngle`, `earAngle`), nonnegativity,
    and per-triangle/per-ear angle-sum-to-`pi` rows, and its W10 sector-sum
    constructors route directly through those real angle rows.  The import
    cycle still makes W34 the downstream consumer; the remaining source is an
    honest ear decomposition/triangulation of the selected outer polygon.
    `SubpolygonAngleRealization.ConcreteSubpolygonInteriorAngleTriangulationRows`
    is the native subpolygon version of the same triangulation obligation,
    avoiding an import cycle with `PlanarBoundaryFaceDataRefinement`.  It
    exposes actual triangle points, `AngleGeometry.angleAt` corner sums,
    boundary predecessor data, equality between boundary interior-angle sum and
    triangle-angle sum, and compatibility with the E13 degree-count total.
    `SubpolygonDataConcrete.CoreOuterBoundaryInteriorAngleTriangulationRows`
    is the upstream outer-core package equivalent to the downstream W10
    polygon-angle rows.  Its
    `.ofConcreteSubpolygonInteriorAngleTriangulationRows` bridge connects the
    native subpolygon triangulation surface to the selected outer-core sector
    sum route without reversing imports.
    `SubpolygonDataConcrete` now also supplies
    `CoreSubpolygonAngleData.ofConcreteSubpolygonInteriorAngleTriangulationRows`,
    `CoreSubpolygonAngleData.lowDegreeWithHighDegreeSlack_ofConcreteSubpolygonInteriorAngleTriangulationRows`,
    and matching `CoreFaceSubpolygonAngleData` constructors.  Remaining
    subpolygon work is genuine triangulation and boundary-angle-sum input, not
    another E13 consumer.
  - Compile status:
    `OuterBoundaryAngleSourceW34` builds with the pinned toolchain after the
    recursive finite-sum simplification loops were replaced by explicit
    `change`/`rw`/`Finset.sum_le_sum` proofs.  This is compile progress only;
    the honest S3 obligation remains a genuine sector-containment,
    triangulation, or ear-decomposition angle-mass source.

### S4. Missing Long-Arc/Triangle-Run Field, Lemma 6/7, And Lemma 9 Rows

- [ ] Inhabit the exact boundary missing field for the S2/S3 skeleton.
  - Paper steps: long-arc and thirteen-edge triangle-run material in
    `E14-E21`.
  - Owners:
    `Swanepoel/JordanBoundaryConcreteInhabitationW24.lean`,
    `Swanepoel/LongArcExistenceConcrete.lean`,
    `Swanepoel/BoundaryArcFiniteWalkConstructionW16.lean`,
    `Swanepoel/TriangleRunSelectorW17.lean`.
  - Live target:
    `SelectedTopologyRowsInhabitationW33.MinimalBoundaryTopologyMissingLongArcTriangleRunField`
    for the `MinimalBoundaryTopologySkeletonFamily` produced by S2/S3; rowwise
    this is
    `MinimalBoundaryTopologySkeleton.MissingLongArcTriangleRunField`.
  - Next action: prove the concrete
    `LongArcExistenceConcrete.BoundaryLongArcExistenceFields` and
    `BoundaryArcTriangleRun` over the skeleton's `planarBoundary`.  Do not
    resurrect older separate "missing long arc" or "triangle run" route names
    except as compatibility aliases in Lean comments/docs.
  - Latest non-circular finite-`p/q` integration:
    `BoundaryArcFiniteWalkConstructionW16.FinitePQSpineCyclicSuccessorRowsTheorem`
    is now the explicit theorem surface that supplies cyclic-successor rows
    for arbitrary topology/angle/subpolygon/long-arc rows.  W17, W24, and W33
    route this theorem to
    `MinimalBoundaryTopologyMissingLongArcTriangleRunField`; in particular use
    `SelectedTopologyRowsInhabitationW33.minimalBoundaryTopologyMissingLongArcTriangleRunFieldOfRemainingActualCycleSkeletonRowsFinitePQSpineCyclicSuccessorRowsTheorem`
    once the W34 skeleton long-arc family is available.  Do not use
    `FrameCyclicOrderAssemblyW32.selectedFinitePQSpineCyclicSuccessorRowsSourceFamilyOfActualTopologyClosureGeneratedOrderRows`
    to build this missing field, because that theorem is keyed to the
    `componentClosure` produced only after the missing field is supplied.
    The next real source field is the skeleton-level
    `MinimalBoundaryTopologyLongArcFieldFamily`.
  - Latest skeleton closure bridge:
    `SelectedTopologyRowsInhabitationW33.actualTopologyClosurePackageOfRemainingActualCycleSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem`
    constructs the actual topology closure package from S2/S3 skeleton rows,
    `MinimalBoundaryTopologyLongArcFieldFamily`, and the W16 finite-`p/q`
    cyclic successor theorem.  The remaining honest S4 missing-field work is
    therefore the long-arc family plus the W16 finite-`p/q` theorem.
    The W16 theorem is now produced from a uniform finite boundary-walk source
    by
    `BoundaryArcFiniteWalkConstructionW16.finitePQSpineCyclicSuccessorRowsTheorem_of_finiteWalkTheorem`.
    Newest W16 pointwise extraction:
    `BoundaryArcFiniteWalkConstructionW16.finitePQSpineCyclicSuccessorRowsTarget_of_frameCoreTarget`
    turns a `BoundaryArcFiniteWalkFrameCoreTarget` directly into the W16
    finite-`p/q` successor-row target, using its concrete finite walk and
    frame-core fields only.  The remaining finite-walk payload is now a real
    `Nonempty BoundaryArcFiniteWalkFrameCoreData` for the selected skeleton.
    Latest W16 certificate adapters:
    `finitePQSpineCyclicSuccessorRowsOfBoundaryArcCertificate`,
    `finitePQSpineCyclicSuccessorRowsOfBoundaryArcFrameCoreFields`,
    `finitePQSpineCyclicSuccessorRows_nonempty_of_frameCoreData`,
    `finitePQSpineCyclicSuccessorRowsTarget_of_boundaryArcCertificate`, and
    `finitePQSpineCyclicSuccessorRowsTarget_of_boundaryArcFrameCoreFields`
    route boundary-arc certificate/frame-core fields into the finite-`p/q`
    target.  Remaining work is to construct those actual boundary-arc
    certificate/frame-core fields from the selected boundary spine.
    Latest finite-spine raw-fact constructors:
    `BoundarySpineFiniteCertificate.M8BoundaryCorePQSpineRows.ofCyclicOrder_pIndex`,
    `.ofCyclicOrder_q`, `.ofCyclicOrder_edgeIndex`,
    `.finitePQSpineCertificateOfCyclicOrder_pIndex`, and the analogous
    `M8BoundaryWalkPQSpineRows.ofCyclicOrder*` plus
    `frameCoreFieldsOfRawFacts` / `rawFactsOfFrameCoreFields` conversions
    expose the selected finite spine as raw cyclic-order/frame-core data.
    Use these in generated-order and W16 source construction; do not rebuild
    finite-spine raw facts elsewhere.
    Boundary-spine also now exposes explicit finite-spine source packages:
    `M8FinitePQSpineCertificate.ExplicitCyclicOrderRows`,
    `M8FinitePQSpineRawFrameCoreFacts`, and
    `M8FinitePQSpineExplicitFrameCoreSource`, with conversions to/from
    `M8FinitePQSpineFrameCoreFields` and projection to
    `M8FinitePQSpineBoundaryArcFrameCoreFields`.  Use this source when feeding
    W16 or generated-order rows.
    Boundary-spine now also exposes upstream boundary-arc fields:
    `M8FinitePQSpineBoundaryArcCertificateFields`,
    `M8FinitePQSpineCertificate.toBoundaryArcCertificateFields`,
    `M8FinitePQSpineBoundaryArcFrameCoreFields`,
    `M8FinitePQSpineCertificate.toBoundaryArcFrameCoreFields`, and the core /
    walk `boundaryArcCertificateFieldsOfCyclicOrder` /
    `boundaryArcFrameCoreFieldsOfRawFacts` constructors.  Downstream W16 work
    should consume these fields rather than rebuilding them.
    W16 now has an import-safe raw finite-spine bridge:
    `finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts`,
    `finitePQSpineCyclicSuccessorRowsOfRawFinitePQFacts_val`, and
    `finitePQSpineCyclicSuccessorRowsTarget_of_rawFinitePQFacts`.
    W16 also consumes the upstream boundary-spine fields directly via
    `boundaryArcCertificateOfFinitePQSpineBoundaryArcCertificateFields`,
    `boundaryArcCertificateOfFinitePQSpineBoundaryArcFrameCoreFields`,
    `finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcCertificateFields`,
    `finitePQSpineCyclicSuccessorRowsOfFinitePQSpineBoundaryArcFrameCoreFields`,
    and the matching `finitePQSpineCyclicSuccessorRowsTarget_of_*` theorems.
    W16 theorem-level source surfaces are now available:
    `FinitePQSpineBoundaryArcCertificateFieldsTheorem` and
    `FinitePQSpineRawFinitePQFactsTheorem`; both reduce to
    `FinitePQSpineCyclicSuccessorRowsTheorem`.  The raw route preserves the
    frame-core raw facts needed later for generated-order rows.  Remaining W16
    work is positive inhabitation of one of these source theorems, not another
    W16 bridge.
    W16 now has direct positive constructors from finite-walk or triangle-run
    data:
    `finitePQSpineBoundaryArcCertificateFieldsOfFiniteWalkData`,
    `finitePQSpineBoundaryArcCertificateFieldsOfTriangleRun`,
    `finitePQSpineBoundaryArcCertificateFieldsTheorem_of_finiteWalkDataTheorem`,
    and `finitePQSpineBoundaryArcCertificateFieldsTheorem_of_triangleRunTheorem`.
    Remaining W16 input is therefore an actual finite-walk theorem or triangle
    run theorem for the selected skeleton.
  - Latest long-arc source:
    `MinimalBoundaryTopologyLongArcRawTurnRows` feeds
    `MinimalBoundaryTopologyLongArcFieldFamily`.  The remaining honest long-arc
    blocker is the raw row package: `d3 <= negativeCount + card longArcIndices`
    for the skeleton boundary, plus raw-turn nonnegativity and threshold
    interpretation.
    Lemma6/Lemma7 coverage already supplies the count inequality through
    `longArcRawTurnRowsOfGapNegativeCoverageDataAndRawTurns` or
    `longArcRawTurnRowsOfBoundaryWalkGapNegativeCoverageOutputsAndRawTurns`.
    Checked W24 bridge:
    `longArcFieldFamilyOfBoundaryLongArcGapNegativePackages` composes W13
    `BoundaryLongArcGapNegativePackage` families and a carrier equivalence into
    the live long-arc family; with the W16 theorem,
    `missingFieldOfBoundaryLongArcGapNegativePackagesFinitePQSpineCyclicSuccessorRowsTheorem`
    produces the skeleton missing field.  Remaining inputs are the actual
    package family on the selected skeleton, the equivalence to concrete
    `longArcIndices`, and the W16 finite-`p/q` theorem.
    The remaining positive long-arc content is an honest
    `rawTurn : longArcIndices -> Nat -> Real` and its nonnegativity on the
    selected arc; Lemma9 is downstream and does not construct raw turns.
    `JordanBoundaryConcreteInhabitationW24.longArcRawTurnRowsOfBoundaryLongArcGapNegativePackages`
    now builds the skeleton raw-turn rows from W13
    `BoundaryLongArcGapNegativePackage` families using the package's real
    `rawTurn` and Lemma6/Lemma7 coverage.  This is a non-circular bridge only:
    the live missing source is still construction of genuine raw turns from
    boundary geometry.
    Checked W13 source closure:
    `boundaryLongArcGapNegativePackageOfBoundaryWalkGapNegativeCoverageOutputAndRawTurns`
    and
    `boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurns`
    build the package family from Lemma6/Lemma7 coverage plus the actual
    classified `longArcIndices` raw-turn rows.  The remaining positive input is
    still the honest raw-turn family and its nonnegativity; the boundary-walk
    output route also needs the count equality identifying the output's
    `longArcCount` with `card longArcIndices`.
    The existing honest raw-turn source type is
    `BoundaryAngleTurnW11.UDConfigRoute.BoundaryAngleTurnTopologyPackage.MinimalBoundaryTopologyBoundaryTurnAngleRows`;
    its `rawTurn` is the value of real `UnitSeparatedAngle` witnesses on the
    thirteen turn slots, and `toLongArcRawTurnRows` /
    `toLongArcFieldFamily` already route those rows into the W24 long-arc
    family.  The missing geometry is to inhabit that W11 row package: actual
    `turnVertex`, `turnAngle`, and predecessor/center/successor equalities for
    each selected long arc and turn slot.
    Newest W11 constructor:
    `MinimalBoundaryTopologyBoundaryTurnAngleRows.ofOuterBoundaryTurnVertex`
    constructs the actual `UnitSeparatedAngle` turn rows once a per-long-arc,
    per-slot outer-cycle vertex map is supplied.  The remaining positive map is
    a family
    `classification.longArcIndices -> Nat -> Fin outerCycle.length` naming the
    boundary vertex where each raw turn slot is measured; the existing single
    triangle-run `pIndex` does not yet supply this uniformly for all long arcs.
    Newest W11 triangle-run source:
    `MinimalBoundaryTopologyBoundaryTurnVertexRows.ofTriangleRun` and
    `MinimalBoundaryTopologyBoundaryTurnAngleRows.ofTriangleRun` provide that
    per-long-arc/per-slot map from the established M8 triangle-run indexing,
    using `BoundaryArcIndexMap.m8BoundaryIndexOfNat` for slots `1..13`.  The
    live W11/W13 integration task is now to feed the available triangle-run
    theorem plus Lemma6/Lemma7 count coverage into the W24 long-arc family for
    the selected skeleton.
    `TriangleRunSelectorW17.ExplicitM8TriangleRunIndices` is the explicit
    triangle-run source surface: construct the actual boundary indices
    `p_0, ..., p_13`, prove the 13 cyclic-successor rows, and prove the 13
    `IsTriangleEdge` rows.  `triangleRunTheorem_of_explicitM8TriangleRunIndicesTheorem`
    then feeds the existing triangle-run theorem.
    `ExplicitM8TriangleRunIndices` now exposes concrete projections `p0`
    through `p13`, `cyclicOrder0` through `cyclicOrder12`, and `triangleEdge0`
    through `triangleEdge12`.  Use those named row projections when proving
    W11 turn-angle rows or W16/raw finite-spine facts; do not add another
    triangle-run unpacking layer.
    W17 now reduces `ExplicitM8TriangleRunIndicesTheorem` from the existing
    triangle-run theorem, extraction targets, finite-walk data, finite-`p/q`
    successor rows, boundary-arc certificate fields, or raw finite-`p/q` facts,
    with `explicitM8TriangleRunIndicesTheorem_iff_triangleRunTheorem` as the
    main equivalence.  W11/W16 workers should consume these reductions rather
    than re-proving the named `p0..p13` surface.
    The classified Lemma 6 obstruction specialization
    `boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurns`
    discharges that count equality internally via `counts_B`.
    Newest W13/W24 integration:
    `Lemma6Lemma7AssemblyW13.ClassifiedBoundary.BoundaryLongArcRawTurnRows`
    and `BoundaryLongArcGapNegativeRows` are the cycle-safe row interface
    between W11-style turn rows and W13 gap packages.
    `boundaryLongArcGapNegativePackageOfLemma6ObstructionAndRawTurnRows`
    packages Lemma6/Lemma7 coverage with raw-turn rows into the exact W13
    package, and
    `JordanBoundaryConcreteInhabitationW24.longArcFieldFamilyOfTurnRowsAndBoundaryLongArcGapNegativePackages`
    routes W11 turn rows plus W13 packages into the W24
    `MinimalBoundaryTopologyLongArcFieldFamily`.
    Latest W13 bridge:
    `BoundaryLongArcRawTurnRows.ofRawTurns`,
    `BoundaryLongArcGapNegativeRows.ofCoverageOutputAndRawTurns`, and
    `BoundaryLongArcGapNegativeRows.ofLemma6ObstructionAndRawTurns` preserve
    the selected `longArcIndices`, route
    `longArcCount = card longArcIndices = counts.B`, keep the supplied raw
    turns, and preserve nonnegativity.  There is no remaining W13 count/card
    blocker; the external source is W11 turn-angle/raw-turn geometry.
    `LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows` now provides that
    raw-turn interpretation layer: `rawTurn a k` is the actual
    `UnitSeparatedAngle.value` on `turnIndexSet` and `0` off it, with
    nonnegativity from `UnitSeparatedAngle.value_nonnegative` and projection to
    `BoundaryLongArcCarrierRawTurnRows` preserving the carrier, `card = B`, and
    Lemma6/Lemma7 count row.  Remaining long-arc source is construction of
    these turn-angle rows from the actual selected boundary turns.
    `BoundaryAngleTurnW11` now connects the W11 turn-angle package to W13 raw
    turns via `BoundaryLongArcRawTurnRows.ofRawTurns`, routes the W24 raw rows
    through that adapter, and supplies the explicit-triangle-run theorem bridge
    into the `ofTriangleRun` constructor.  No boundary-vertex/turn-angle
    equality rows remain for this W11 route.
    `BoundaryAngleWitnessConstruction` now exposes cycle-safe constructors for
    canonical boundary predecessor/current/successor witnesses, explicit triple
    witnesses requiring exactly the two cyclic-successor equalities, and
    pointwise long-arc/turn-slot witness families matching
    `BoundaryLongArcTurnAngleRows.turnAngle` and S5 actual-turn consumers.
    Use these constructors rather than reproving boundary-index equalities.
    `LongArcExistenceConcrete.BoundaryLongArcTurnAngleRows.ofOuterBoundaryCoreTurnVertex`
    now imports those witness constructors and builds actual W11 turn-angle
    rows from selected boundary turn vertices; `carrierRawTurnRowsOfOuterBoundaryCoreTurnVertex`
    projects the corresponding carrier/raw-turn rows with the actual angle
    value on turn slots.  W13 also has
    `boundaryLongArcGapNegativePackageOfGapNegativeCoverageDataAndRawTurnRows`
    and `longArcExistenceFieldsOfGapNegativeCoverageAndRawTurnRows`, so actual
    raw-turn rows plus `GapNegativeCoverageData` now build the W13
    package/fields directly.
    W24's gap-negative and no-boundary-gap missing-field sources already consume
    W13 packages plus the W16 theorem; the latest cleanup reuses
    `toBoundaryLongArcCarrierRawTurnRows` directly.  The live long-arc blocker
    remains the genuine W11/W13 raw-turn package and W16 source, not W24
    plumbing.
    `LongArcExistenceConcrete.BoundaryLongArcCarrierRawTurnRows` is the
    concrete positive source surface for the same content: a finite long-arc
    carrier, cardinality `B`, Lemma6/Lemma7 coverage, and nonnegative real
    raw turns.
    `BoundaryLongArcCarrierRawTurnRows.ofFiniteCarrierRawTurns`,
    `.nonempty_of_finiteCarrierRawTurns`, and
    `.exists_nonconcave_longArc_with_turn_bounds` sharpen that upstream
    carrier route.  The exact remaining long-arc inputs are now the finite
    carrier, `card = B`, Lemma6/Lemma7 coverage `d3 <= N + card`, the real
    `rawTurn`, and raw-turn nonnegativity on the turn slots.
    Newest W11/W24 composition:
    `BoundaryAngleTurnW11.ofTriangleRunAndBoundaryLongArcGapNegativeRows`
    consumes a triangle-run family and W13 gap-negative rows to build the W11
    real turn-angle row package, and
    `missingFieldOfTriangleRunBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem`
    routes those rows plus the W16 finite-`p/q` theorem directly to the W24
    missing long-arc/triangle-run field.
    Newest compact W24 route:
    `JordanBoundaryConcreteInhabitationW24.longArcFieldFamilyOfBoundaryLongArcGapNegativeRows`
    and
    `missingFieldOfBoundaryLongArcGapNegativeRowsFinitePQSpineCyclicSuccessorRowsTheorem`
    consume W13 `BoundaryLongArcGapNegativeRows` (using their real raw-turn
    rows) plus the W16 finite-`p/q` theorem.  The exact remaining source
    inputs are genuine W13 gap-negative rows and either explicit triangle-run
    rows or the W16 finite-`p/q` theorem over the selected skeleton.
    No-boundary-gap W24 route:
    `BoundaryLongArcNoBoundaryGapTriangleDegree34Rows`,
    `.toBoundaryLongArcGapNegativeRows`,
    `.toLongArcFieldFamily`,
    `missingFieldOfNoBoundaryGapTriangleDegree34RowsFinitePQSpineCyclicSuccessorRowsTheorem`,
    and
    `ofSkeletonNoBoundaryGapTriangleDegree34RowsAndFinitePQSpineCyclicSuccessorRowsTheorem`
    route no-boundary-gap rows plus W16 finite-`p/q` rows to the missing field.
    Remaining work is the actual no-boundary-gap/no-gap rows, not another W24
    bridge.
    W24 now has `missingField_nonempty_of_noBoundaryGapTriangleDegree34Rows_explicitM8TriangleRunIndicesTheorem`,
    consuming no-boundary-gap rows plus explicit M8 triangle-run indices through
    the W17 finite-`p/q` theorem.  `BoundaryAngleTurnW11` also exposes
    `missingFieldOfTriangleRunAndBoundaryLongArcGapNegativeRows` and a
    nonempty theorem from triangle-run rows plus W13 gap-negative rows.
    `SelectedTopologyRowsInhabitationW33` packages these into
    `exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsBoundaryLongArcGapNegativeRowsExplicitM8TriangleRunIndicesTheorem`.
    Remaining long-arc/W24 work is positive row inhabitation, not another
    missing-field bridge.
    `Lemma6Lemma7AssemblyW13` now consumes `BoundaryLongArcGapNegativeRows`
    into classified long-arc existence fields, concrete count-gap input, and
    `M8ConstructionInterface.M8TurnBounds`, including
    `m8TurnBoundsOfBoundaryLongArcGapNegativeRows_totalTurn_lt_pi_div_three`.
    Remaining W13 work is positive gap-negative row inhabitation, not turn-bound
    extraction.
    K23 now supplies a W24-facing no-boundary-gap reduction from skeleton
    realization-carrier rows via
    `SkeletonBoundaryGapTriangleDegree34RealizationCarrierRows`,
    `noBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows`,
    `boundaryLongArcNoBoundaryGapTriangleDegree34RowsOfSkeletonRealizationCarrierRows`,
    `longArcFieldFamilyOfSkeletonRealizationCarrierRows`, and
    `missingFieldOfSkeletonRealizationCarrierRowsFinitePQSpineCyclicSuccessorRowsTheorem`.
    Remaining work is the actual skeleton realization-carrier rows and raw-turn
    rows.
    Shortest W13 source route:
    supply `ClassifiedBoundary.BoundaryLongArcRawTurnRows` for each selected
    skeleton row, then combine with Lemma6/Lemma7 coverage using
    `ClassifiedBoundary.BoundaryLongArcGapNegativeRows` or
    `BoundaryLongArcGapNegativeRows.ofLemma6Obstruction`.  W11 is optional on
    this shortest route; the real missing data is still the raw-turn family and
    nonnegativity on `turnIndexSet`.

- [ ] Instantiate boundary-walk gap-negative coverage on the selected frame.
  - Paper steps: `E14-E21`.
  - Owners:
    `Swanepoel/Lemma6NegativeAfterGapW12.lean`,
    `Swanepoel/Lemma7GapInductionW12.lean`,
    `Swanepoel/Lemma6Lemma7AssemblyW13.lean`,
    `Swanepoel/K23RouteCoverageSourceW34.lean`,
    `Swanepoel/Lemma9NatLateTripleInhabitationW22.lean`.
  - Coverage target:
    `K23RouteCoverageSourceW34.SelectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem`.
  - Lemma 9 target:
    `K23RouteCoverageSourceW34.SelectedFrameLemma9NatLateTripleInputsSourceTheorem`
    or the family theorem
    `SelectedFrameLemma9NatLateTripleSourceFamilyTheorem`.
  - Newest reduction: concrete five-start no-early equality now projects to
    nat-late rows via
    `lemma9NatLateTripleInputsFamilyOfConcreteNoEarlyTripleEquality`,
    `selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_concreteNoEarlyTripleEquality`,
    and then to five-start late facts / route coverage via the checked
    `*_of_natLateTripleInputs` constructors.
  - Next action: prove the actual positive nat-late rows for the selected
    frame/cyclic package and pair them with boundary-walk gap-negative
    coverage.  Do not add another no-early equality wrapper.
  - Latest route-coverage-to-Lemma9 projections:
    `NoEarlyRouteCoverageClosureW32.lemma9SourceFieldsOfRouteData`,
    `natLateTripleInputsOfRouteData`,
    `lemma9SourceFieldsOfRouteCoverageAvailable`,
    `natLateTripleInputsOfRouteCoverageAvailable`, and
    `nonempty_lemma9SourceFields_of_routeCoverage` feed Lemma 9 source fields
    directly from route-coverage data.  Remaining work is the concrete route
    coverage source plus five-start exclusions, not another Lemma 9 projection
    bridge.
    The W32 route-coverage handoff has been re-verified and is already
    sufficient; W34 already contains the selected-frame consumers from route
    coverage plus five-start exclusions.  Do not add another W32 wrapper unless
    a real theorem-shape mismatch reappears.
    W22 now has import-safe projections
    `Lemma9NatLateTripleInhabitationW22.natLateTripleInputsOfSourceFields`,
    `concreteNoEarlyTripleEqualityOfSourceFields`,
    `fiveStartExclusionsOfSourceFields`, and
    `assembledNatLateTripleInputsFamilyOfSourceFamily`, so W34 can compose
    route coverage with Lemma 9 without importing W32 back into W22.
    Newest W22 reductions:
    `concreteNoEarlyTripleEquality_iff_fiveStartExclusions`,
    `nonempty_natLateTripleInputs_iff_fiveStartExclusions`,
    `natCoverageInputs_of_coverage_and_fiveStartExclusions`,
    `nonempty_coverageConcreteRow_iff_exists_coverage_and_fiveStartExclusions`,
    and `nonempty_sourceFields_of_coverage_and_fiveStartExclusions` reduce the
    nat-late/Lemma 9 side to actual coverage plus the five-start exclusions.
    `NoEarlyTripleFromLemma9` now gives row-level conversions
    `M8Lemma9FiveStartLateFacts.iff_fiveStartExclusions`,
    `fiveStartExclusions_of_lateTriples`,
    `fiveStartExclusions_of_natLateTripleInputs`, and
    `fiveStartExclusions_of_earlyTripleObstructionInputs`, so selected-frame
    five-start exclusions can be sourced from any of those concrete inputs.
    K23/W34 now has
    `selectedFrameLemma9NatLateTripleSourceFamilyTheorem_of_routeCoverageAvailable`
    and
    `selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_routeCoverageAvailable`,
    so route coverage directly supplies the selected-frame Lemma 9 source.
    Remaining K23 work is concrete route coverage/no-gap/incidence inputs.
    K23/W34 also has direct selected-frame five-start exclusion constructors
    `selectedFrameConcreteFiveStartExclusionSourceTheorem_of_lemma9FiveStartLateFacts`,
    `_of_lateTriples`, `_of_natLateTripleInputs`, and
    `_of_earlyTripleObstructionInputs`, plus
    `selectedFrameConcreteFiveStartExclusionSourceTheorem_iff_natLateTripleInputs`.
    Do not route through W22 nat-late unless that is the actual available
    source.
    `NoEarlyTripleFromLemma9.M8FiveStartExclusions` is now the named
    five-start payload, with selected-row conversions from restricted Lemma 9
    late facts, raw late triples, nat-late inputs, or early-obstruction inputs
    into both five-start exclusions and concrete no-early equality rows.
  - Latest exact carrier reduction:
    `K23RouteCoverageSourceW34.selectedFrameBoundaryWalkGapNegativeCoverageSourceTheorem_of_actualSelectedNoGapRows`
    now consumes actual selected no-gap rows directly through
    `boundaryWalkGapNegativeCoverageRowsOfActualSelectedNoGapRows`, instead of
    routing through the older no-gap-to-carrier equivalence.
    Actual selected no-gap rows can be produced from pointwise component-row
    refutations by
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentRows`.
    The remaining no-gap blocker is the pointwise no-component row, not another
    coverage adapter.
    `SubpolygonConcreteRealizationW33.FaceSubpolygonRealizationFamilyData` now
    exposes flattened source reductions from component-pattern carrier rows to
    actual pointwise no-bad component rows and then into the selected
    `BoundaryGapTriangleDegree34Row` no-gap field.  Use this flattened family
    when connecting selected subpolygon realizations to route coverage.
  - Latest common-neighbor reduction:
    `K23RouteCoverageSourceW34.SelectedFrameCommonNeighborGeometrySourceTheorem`
    and the three-common-neighbor analogue now bridge to concrete no-early
    equality and nat-late/source-family/route coverage.  The remaining honest
    geometry fields are the five start-indexed common-neighbor witnesses:
    `witness_start1` through `witness_start5`, each proving the appropriate
    common-neighbor cardinality or explicit three-neighbor incidences.
  - Newest positive sources:
    `SelectedFrameThreeCommonNeighborWitnessRowsSourceTheorem` or
    `SelectedFrameCommonNeighborWitnessRowsSourceTheorem`, together with the
    actual no-gap carrier rows consumed by
    `routeCoverageAvailable_of_selectedFrameBoundaryGapTriangleDegree34CarrierRows_and_threeCommonNeighborGeometrySource`,
    are enough for the current S4 route-coverage side.  The exact remaining
    obligations are the actual selected no-gap rows and one of those five-start
    witness-row source theorems.
  - Latest positive K23 source reductions:
    `selectedFrameThreeCommonNeighborGeometrySourceTheorem_iff_witnessRows`,
    `selectedFrameCommonNeighborGeometrySourceTheorem_iff_witnessRows`, and
    `selectedFrameK23GeometrySourceTheorem_iff_witnessRows` identify the
    geometry source theorems with positive witness-row families.  Use these to
    avoid no-start/no-early geometry manufacture; the proof obligation remains
    the five-start witness rows plus actual no-gap carrier rows.
    The common-neighbor and three-neighbor witness-row formulations are now
    interconvertible through
    `selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_iff_commonNeighborWitnessRows`.
    Do not add another K23 adapter; prove the actual five-start
    incidence/cardinality rows.
    Newest checked K23 conversion:
    `CommonNeighborRouteCoverageSourceW34.ThreeCommonNeighborIncidenceDatum`
    and `threeCommonNeighborObstructionInputsOfIncidenceRows` convert explicit
    third-neighbor incidence data into the three-common-neighbor witness rows.
    Current known blocker: triple-equality rows give only the standard two
    common neighbors for adjacent `q` pairs.  The exact missing positive
    incidences are `Adj q_1 s_2`, `Adj q_2 s_3`, `Adj q_3 s_4`,
    `Adj q_4 s_5`, and `Adj q_5 s_6`, equivalently
    `Adj s_{i+1} q_i` for starts `i = 1..5`.
    `K23ObstructionConcrete` now names the Euclidean version of this blocker:
    `M8BadAdjacencyCrossAdjacencyRows` is equivalent to
    `M8BadAdjacencyCrossDistanceRows`, and the local-label aliases are
    `M8LocalLabelBadAdjacencyCrossAdjacencyRows` /
    `M8LocalLabelBadAdjacencyCrossDistanceRows`.  The precise remaining K23
    geometric source is proving those five unit-distance rows for the actual
    selected labels.
    `M8BadAdjacencyCrossFigure9DistanceRows` packages the five selected-label
    Figure 9 distance rows with `qi = q_i` and `s = s_{i+1}`;
    `m8LocalLabelBadAdjacencyCrossDistanceRows_of_figure9DistanceRows` turns
    them into the local-label cross-distance package.  The remaining K23 source
    is exactly those five Figure 9 distance rows for the cross pairs.
    `K23RouteCoverageSourceW34.BadAdjacencyCommonNeighborDatum` is the
    route-facing source package for exactly these five incidences:
    `threeCommonNeighborObstructionInputsOfBadAdjacencyData` consumes five
    such rows and feeds the common-neighbor/K23 route.
  - Latest no-gap reduction:
    `SelectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem`
    reduces through
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_componentRows`
    to the pointwise component-row source.  The concrete missing fields are a
    uniform `coreSubpolygonData`, the exact `RowBoundary` equality, and the
    pointwise absence of the four-field bad pattern: degree-3 at `k`, not
    long-arc, triangular successor edge, and successor degree 3 or 4.  The
    carrier route may close this by producing `CoreSubpolygonCarrierCountData`
    from every bad pattern and applying the existing E13 contradiction.
    Checked row-level shortcut:
    `K23RouteCoverageSourceW34.actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_componentCarrierRows`
    now composes those component-carrier rows directly into actual selected
    no-gap rows, preserving the same `coreSubpolygonData` and `RowBoundary`
    equality fields.  This is still conditional on producing the actual
    component-carrier rows for every bad pattern.
    Newest no-gap and K23 row bridges:
    `ActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsForFrameCyclicRows`
    feeds
    `actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_realizationCarrierRows`.
    `SubpolygonSelectedGeometrySourceW34.false_of_selectedOuterFaceCoreSubpolygonCarrierCountDataOfMinimalFailureSelectedClassificationFields`
    exposes the E13 high-degree-slack contradiction for selected outer-face
    carrier data.  The remaining no-gap source is therefore an actual
    realization-carrier row for each bad pattern, not another no-gap adapter.
    Subpolygon triangulation consumers now include
    `ConcreteSubpolygonInteriorAngleTriangulationRows.toConcreteAngleBoundsOfBoundaryInteriorAngleSum`,
    `.angleLowerBound_of_forced_le_boundaryInteriorAngleSum`,
    `.lowDegreeWithHighDegreeSlack_of_forced_le_boundaryInteriorAngleSum`, and
    `.lowDegreeInequality_of_forced_le_boundaryInteriorAngleSum`; use these to
    turn genuine triangulation rows plus the boundary interior-angle inequality
    into the E13 low-degree conclusions.
    No-gap carrier realization now reduces to pointwise no-bad rows through
    `SubpolygonConcreteRealizationW33.coreSubpolygonAngleRealizationFamily_carrier_false`,
    `noBadRows_of_coreSubpolygonAngleRealizationFamily_carrierRows`,
    `coreSubpolygonAngleRealizationFamily_carrierRows_iff_noBadRows`, and the
    matching face-subpolygon variants.  Remaining no-gap work is the actual
    pointwise no-bad row source.
    `SubpolygonSelectedGeometrySourceW34` now specializes the W33
    `FaceSubpolygonRealizationFamilyData` bridge to minimal-failure selected
    classification/realization fields.  The exact remaining no-gap blocker is
    pointwise absence of `BoundaryGapTriangleDegree34ComponentPattern`, or
    equivalently producing `CoreSubpolygonCarrierCountData` for any such bad
    pattern and applying the existing E13 high-degree-slack contradiction.
    `SubpolygonConcreteRealizationW33` now has pointwise contradiction lemmas
    for core, face-subpolygon, and flattened selected face-subpolygon
    realization families: a bad
    `BoundaryGapTriangleDegree34ComponentPattern` plus matching
    `CoreSubpolygonCarrierCountData` is contradictory over the same W33
    realization family.  The remaining no-gap source is construction of that
    actual carrier-count data for any selected bad component pattern.
    `SubpolygonSelectedGeometrySourceW34` now packages selected realization
    rows as W33 `FaceSubpolygonRealizationFamilyData` and proves the
    K23-consumable no-gap theorem
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_selectedFaceRealizationRows`.
    `K23RouteCoverageSourceW34` also has exact realization carrier row data
    and
    `selectedFrameActualSelectedBoundaryNoGapTriangleDegree34RowsSourceTheorem_of_exactRealizationCarrierRows`,
    consuming W33's exact component-carrier contradiction directly.  Remaining
    no-gap work is positive selected realization/exact-carrier data, not a
    no-gap adapter.
    Latest component-pattern reduction:
    `SubpolygonConcreteRealizationW33.BoundaryGapTriangleDegree34ComponentPattern`,
    `boundaryGapTriangleDegree34Row_iff_componentPattern`,
    `coreSubpolygonAngleRealizationFamily_componentPatternCarrierRows_iff_noBadRows`,
    and
    `no_boundaryGapTriangleDegree34Rows_of_coreSubpolygonAngleRealizationFamily_componentCarrierRows`
    reduce selected no-gap to the actual four-field bad pattern
    (degree/long-arc/triangular-successor/successor degree).
    K23 now aliases `ActualSelectedBoundaryGapTriangleDegree34ComponentRow` to
    that W33 component pattern and uses the same no-boundary-gap theorem in
    `actualSelectedBoundaryNoGapTriangleDegree34RowsForFrameCyclicRows_of_realizationCarrierRows`.
    For K23 common-neighbor geometry,
    `SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem` is the compact
    five-incidence source; it feeds the three/common-neighbor witness rows and
    route coverage through
    `selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborRows`
    and
    `routeCoverageAvailable_of_selectedFrameCoverage_and_badAdjacencyCommonNeighborRows`.
    Newest positive incidence surface:
    `SelectedFrameBadAdjacencyCommonNeighborIncidenceRows` and
    `selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_incidenceRows`
    package the five start-indexed E19 incidence rows directly into the compact
    bad-adjacency source.  The remaining exact fields are the five explicit
    third-neighbor incidences `Adj q_1 s_2`, `Adj q_2 s_3`, `Adj q_3 s_4`,
    `Adj q_4 s_5`, and `Adj q_5 s_6`, plus the standard bundled distinctness
    and common-neighbor data required by each
    `BadAdjacencyCommonNeighborDatum`.
    `CommonNeighborRouteCoverageSourceW34.M8ConcreteThreeCommonNeighborIncidenceInputs`
    is the lower-level no-cycle package for the same five local incidences,
    with projections `start1_left0_adj_third` through
    `start5_left0_adj_third` and conversions to the three/common-neighbor
    obstruction inputs.
    Newest incidence/no-gap bridge:
    `M8ConcreteThreeCommonNeighborIncidenceInputs.ofWitnessStarts`,
    `start1_left1_adj_third` through `start5_left1_adj_third`,
    `k23ObstructionInputsOfIncidenceRows`,
    `selectedFrameThreeCommonNeighborWitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows`,
    `selectedFrameK23WitnessRowsSourceTheorem_of_badAdjacencyCommonNeighborIncidenceRows`,
    `selectedFrameConcreteNoEarlySourceFamilyTheorem_of_actualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows`,
    and
    `routeCoverageAvailable_of_selectedFrameActualSelectedNoGapRows_and_badAdjacencyCommonNeighborIncidenceRows`
    route the five bad-adjacency incidences into K23/no-early coverage.  The
    remaining content is the actual five incidences from the selected finite
    labels, not another K23 adapter.
    Root-imported downstream bridge `BoundaryLabelBadAdjacencyRoute` now turns
    finite-label `BadAdjacencyIncidenceRows` into
    `M8ConcreteBadAdjacencyCommonNeighborObstructionInputs` through
    `badAdjacencyCommonNeighborDatumOfStart` and
    `badAdjacencyCommonNeighborObstructionInputsOfRows`, avoiding a K23 import
    cycle.  Remaining incidence work is the actual five adjacency rows
    `adj_q1_s2` through `adj_q5_s6` inside the finite label certificate.
    Do not import `BoundaryLabelBadAdjacencyRoute` back into K23: it already
    imports K23, so finite-label-to-selected-frame consumption must remain in a
    downstream module importing both.
    `BoundaryLabelCertificateAssembly.BadAdjacencyFiniteLabelIncidenceRows`
    is now the finite-label-facing positive target for those five rows, with
    `badAdjacencyIncidenceRows_iff_finiteLabelIncidenceRows` and
    `badAdjacencyIncidenceRows_nonempty_of_finiteLabelIncidenceRows` converting
    it to the route-facing incidence package.  Remaining incidence work is to
    prove these finite-label rows from the actual generated label certificate.
    Important blocker: the generated finite label certificate currently gives
    `q_i ~ q_{i-1}`, `q_i ~ q_{i+1}`, `q_i ~ r_i`, and `q_i ~ s_i`, but not
    the cross adjacencies `q_i ~ s_{i+1}` needed for
    `BadAdjacencyFiniteLabelIncidenceRows`.  Those five rows need a geometric
    proof or stronger selected-label construction; they are not obtainable by
    unpacking the present certificate fields alone.
    `BoundaryLabelBadAdjacencyRoute` now also consumes finite-label incidence
    rows directly through
    `selectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem_of_finiteLabelBadAdjacencyIncidenceRows`
    and `selectedFrameK23WitnessRowsSourceTheorem_of_finiteLabelBadAdjacencyIncidenceRows`.
    The remaining K23 incidence source is therefore exactly the finite-label
    row package, not a route-facing bridge.
    `CommonNeighborRouteCoverageSourceW34.BadAdjacencyCommonNeighborStandardDatumAt`
    and `M8BadAdjacencyCommonNeighborStandardRows` now package the same five
    selected bad-adjacency incidences together with the standard two adjacent
    common neighbors, and project to concrete three-common-neighbor incidence,
    three-common-neighbor obstruction, and common-neighbor card-obstruction
    inputs.  The remaining K23 source is still the five cross adjacencies or
    Figure 9 cross-distance rows; the standard-row bridge is complete.
    `M8BadAdjacencyCommonNeighborStandardRowFamily` now lifts those standard
    rows to common-neighbor route data and route-coverage availability.  The
    selected-frame consumer belongs in `K23RouteCoverageSourceW34` because that
    file imports the common-neighbor layer.
    `K23ObstructionConcrete.M8BadAdjacencyCrossSelectedFiniteLabelFigure9Rows`
    now reduces actual selected Figure 9 cross rows to cross-distance rows and
    to finite/local label incidence rows:
    `badAdjacencyFiniteLabelIncidenceRows_of_selectedFiniteLabelFigure9Rows`
    and `badAdjacencyLocalLabelIncidenceRowAt_of_selectedFiniteLabelFigure9Rows`.
    `ExactFigureWitnessSourceW34` now supplies finite-PQ wrappers from bad
    adjacency local-label or finite-label rows to exact K23 cross-distance rows.
    `BoundaryLabelCertificateAssembly` now has an import-cycle-free local
    surface for the same source:
    `BadAdjacencySelectedFiniteLabelFigure9RowAt` and
    `BadAdjacencySelectedFiniteLabelFigure9Rows`, projecting to
    `BadAdjacencyLocalLabelIncidenceRowAt`,
    `BadAdjacencyFiniteLabelIncidenceRows`, and route-facing
    `BadAdjacencyIncidenceRows`.  Remaining K23 incidence work is positive
    construction of those selected finite-label Figure 9 rows.
    For Lemma 9, `SelectedFrameConcreteFiveStartExclusionSourceTheorem` feeds
    `selectedFrameLemma9NatLateTripleInputsSourceTheorem_of_fiveStartExclusions`
    and the five-start route-coverage bridges.
    Latest compact S4 route-coverage constructors:
    `routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_badAdjacencyCommonNeighborRows`,
    `routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_and_fiveStartExclusions`,
    and
    `routeCoverageAvailable_of_selectedFrameRealizationCarrierRows_badAdjacencyCommonNeighborRows_and_fiveStartExclusions`
    combine realization-carrier no-gap rows with the bad-adjacency K23 source
    and/or five-start Lemma9 source for final assembly.

### S5. Figure 8 / Figure 9 Containment

- [ ] Prove the selected-frame local-window containment source.
  - Paper step: Lemma 10 / `E22-E23`.
  - Owners:
    `Swanepoel/Figure8ContainmentW12.lean`,
    `Swanepoel/Figure9ContainmentW12.lean`,
    `Swanepoel/ExactFigureRowsAssemblyW32.lean`,
    `Swanepoel/ExactFigureWitnessSourceW34.lean`.
  - Live target:
    `ExactFigureWitnessSourceW34.LocalWindowContainmentFieldsForFrameCyclicSource`
    for the selected frame/cyclic rows.
  - Newest reduction: local-window containment projects to both Figure 8 and
    Figure 9 distance/angle rows and directly to final-assembly figure
    components via
    `honestEuclideanSourceComponentsForFrameCyclicSource_of_localWindowContainmentFields`.
    The interface constructors from Figure 8 separated containment and Figure 9
    adjacent-left containment are checked.
  - Next action: construct the actual selected figure witnesses, Figure 8
    central-angle containment rows, and Figure 9 middle-turn realization rows
    for the selected frame; then feed them through
    `localWindowContainmentFieldsForFrameCyclicSource_of_actualS5_sourceRows`.
  - Latest compact constructor:
    `ExactFigureWitnessSourceW34.localWindowContainmentFieldsForFrameCyclicSource_of_actualS5_sourceRows`
    reduces local-window containment to selected figure witnesses, Figure 8
    central-angle containment rows, and Figure 9 middle-turn realization rows.
  - Latest Figure 8 projection:
    `ExactFigureWitnessSourceW34.figure8CentralAngleContainmentRowsForFrameCyclicSource_of_localHonestEuclideanRows`
    and
    `figure8SeparatedContainmentInterfacesForFrameCyclicSource_of_localHonestEuclideanRows`
    project Figure 8 containment directly from the honest Euclidean row package.
  - Latest selected-figure bridge:
    `ExactFigureRowsAssemblyW32` now projects existing exact row assembly to
    `LocalSelectedFigureWitnessFieldsFamily`, and
    `ExactFigureWitnessSourceW34` projects local honest Euclidean rows to
    `SelectedFigureWitnessSourceFieldsForFrameCyclicSource`, including the
    actual finite-`p_i/q_i` generated frame packages.  The remaining S5 blocker
    is honest Figure 9 middle-turn realization for the selected frame.
  - Newest compact S5 entrances:
    `localWindowContainmentFieldsForFrameCyclicSource_of_localHonestEuclideanRows`
    reduces local-window containment to
    `LocalHonestEuclideanRowsForFrameCyclicSource`; the Figure 9 side uses the
    left-angle containment row, which is the typed Lemma 10 interface.  The
    older middle-turn realization row is a stronger producer, not a final-route
    blocker.
    Equivalently, prove the Figure 8/Figure 9 distance-and-angle rows through
    `localHonestEuclideanRowsForFrameCyclicSource_iff_distance_and_angle_rows`.
    No new Figure 8 adapter is needed.
  - Latest bundled S5 source:
    `LocalHonestS5FigureRowsForFrameCyclicSource` is the compact obligation
    bundling local honest Euclidean rows with the genuine Figure 9 middle-turn
    realization.  It feeds
    `localWindowContainmentFieldsForFrameCyclicSource_nonempty_of_localHonestS5FigureRows`.
  - Latest atomic S5 entrance:
    `localHonestEuclideanRowsForFrameCyclicSource_of_distance_and_angle_rows`
    builds local honest Euclidean rows from the four atomic distance/angle row
    families.  The final constructor
    `w34ActualRoutePremises_of_exactRemainingInputPackage_distance_and_angle_rows`
    now consumes those four row families plus Figure 9 middle-turn rows.
    The current shortest final S5 route is the atomic four-row variant:
    Figure 8 distance rows, Figure 8 central-angle containment rows, Figure 9
    distance rows, and Figure 9 left-angle containment rows.  The Figure 9
    middle-turn row is a stronger producer, not required by that shortest
    route.
    Newest Figure 9 simplification:
    `Figure9ContainmentConcrete.leftAngleContainmentRows_of_angleLeMiddleTurnRows`
    proves the left-angle containment row from turn nonnegativity plus the
    pointwise upper bound `angleAt p qi s <= turn (i + 1)`.  The remaining S5
    angle source can therefore use this weaker pointwise middle-turn upper
    bound instead of the older equality-style middle-turn realization row.
    W19 exposes the same weaker source through
    `AngleContainmentBridgeProducerW19.Figure9UniversalLeftAngleLeMiddleTurnRows`
    and
    `figure9UniversalLeftAngleContainment_of_angleLeMiddleTurnRows`, with
    certificate constructors ending in
    `ofDistanceWitnessRowsAndAngleLeMiddleTurnRows`.
    Newest checked S5 integration:
    `Figure9LeftAngleLeMiddleTurnRowsForFrameCyclicSource` and
    `Figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource`
    expose that weaker pointwise bound on the frame/finite-`p_i/q_i` route.
    `localHonestEuclideanRowsForFrameCyclicSource_of_distance_rows_and_angleLeMiddleTurnRows`,
    `localWindowContainmentFieldsForFrameCyclicSource_of_distance_rows_and_angleLeMiddleTurnRows`,
    and
    `honestEuclideanSourceComponentsForFrameCyclicSource_of_distance_rows_and_angleLeMiddleTurnRows`
    now turn Figure 8 distance rows, Figure 8 central-angle containment, Figure
    9 distance rows, and the weaker Figure 9 middle-turn upper-bound rows into
    the S5 local-window/Euclidean components.  The remaining S5 geometry is
    Figure 8 central-angle containment plus the actual pointwise Figure 9
    middle-turn upper-bound rows for the generated frame.
    Newest Figure 8 bridge:
    `Figure8ContainmentW12.dataWitnesses_of_distanceWitnessRowsAndCentralAngleContainmentRows`
    and `E22_of_distanceWitnessRowsAndCentralAngleContainmentRows` turn
    Figure 8 distance rows plus central-angle containment rows into the E22
    interface.  In `ExactFigureWitnessSourceW34`,
    `Figure8CentralAngleLeSeparatedTurnRowsForFrameCyclicSource` and
    `Figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource`
    are now the compact positive row surfaces for the remaining Figure 8 angle
    source, with finite-label and Figure9 upper-bound constructors ending in
    `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_finiteLabelRows_centralAngleLeSeparatedTurnRows_and_figure9AngleLeMiddleTurnRows`.
    `BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.S5AngleRows`
    is the compact label-certificate angle row package for the quantitative
    S5 angle facts that the finite label data itself does not contain; it
    assembles to `AngleContainmentBridges` via
    `angleContainmentBridgesOfS5AngleRows`.
    `M8FiniteBoundaryFrameCoreLabelCertificate.S5FiniteLabelAngleRows` now
    bundles the same explicit finite-label angle inequalities with direct
    projections to the Figure 8/Figure 9 containment interfaces.  The remaining
    S5 angle inputs are exactly: for Figure 8, prove
    `angleAt qi p qj <= separatedTurn turn i j` for each failed separated
    pair; for Figure 9, prove `angleAt p qi s <= turn (i + 1)` for each
    adjacent failed pair.
    Figure 8 has now been reduced to turn-window geometry:
    `Figure8ExplicitEuclideanFactsCompletionW33.Figure8CentralAngleTurnSubwindowRows`
    or `Figure8CentralAngleTurnSubwindowEqRows` feed
    `centralAngleContainmentRows_of_turnSubwindowRows` /
    `centralAngleContainmentRows_of_turnSubwindowEqRows`.  The exact remaining
    Figure 8 source is a real central-angle telescope/subwindow inside
    `Finset.Icc (i + 1) j` for each separated failed pair, plus turn
    nonnegativity.
    Latest Figure 8 source refinements:
    `Figure8CentralAngleTurnIccSubwindowRows`,
    `Figure8CentralAngleTurnIccSubwindowEqRows`,
    `Figure8CentralAngleTurnIndexedSubwindowRows`, and
    `Figure8CentralAngleTurnIndexedSubwindowEqRows` feed containment through
    the checked `centralAngleContainmentRows_of_*` constructors, including
    M8-turn-bound variants.  The remaining proof content is now the actual
    indexed/Icc window selection for every separated failed pair.
    Figure 9 has now been reduced to concrete turn geometry:
    `Figure9EuclideanFactsConcrete.Figure9AdjacentLeftCosineTurnRows` or
    `Figure9AdjacentLeftTurnChordRows` feed
    `angleLeMiddleTurnRows_of_cosineTurnRows` /
    `angleLeMiddleTurnRows_of_turnChordRows`.  The exact remaining rows are
    `turn (i + 1) ∈ [0, pi]` and either
    `Real.cos (turn (i + 1)) <= dotAt p qi s` or
    `sqDist p s <= 2 - 2 * Real.cos (turn (i + 1))`.
    Latest Figure 9 row calculus:
    `cosineTurnRows_iff_turnChordRows`,
    `middleTurn_mem_Icc_zero_pi_of_totalTurn_lt_pi_div_three`,
    `cosineTurnRows_of_totalTurn_and_cosineComparisons`,
    `turnChordRows_of_totalTurn_and_chordComparisons`,
    `angleLeMiddleTurnRows_of_totalTurn_and_cosineComparisons`, and
    `angleLeMiddleTurnRows_of_totalTurn_and_chordComparisons` reduce the
    remaining Figure 9 source to total-turn control plus pointwise cosine or
    chord comparisons.
    `Figure9EuclideanFactsConcrete` now also has pointwise comparison lemmas
    turning `angleAt p qi s <= theta` into cosine/chord comparison rows, with
    `UnitSeparatedAngle.value` and equality variants for the common case where
    the certified turn angle is exactly the Figure 9 left comparison angle.
    Remaining S5 work is to prove those pointwise angle upper bounds from the
    actual selected turn-angle geometry.
    W19 containment now consumes those concrete Figure 9 rows through
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_cosineTurnRows`,
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_turnChordRows`,
    `Figure9ExactAngleContainmentCertificate.ofDistanceWitnessRowsAndCosineTurnRows`,
    and `.ofDistanceWitnessRowsAndTurnChordRows`.
    Newest W19 total-turn constructors:
    `Figure9UniversalLeftCosineComparisonRows`,
    `Figure9UniversalLeftTurnChordComparisonRows`,
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_totalTurn_and_cosineComparisons`,
    `figure9UniversalLeftAngleLeMiddleTurnRows_of_totalTurn_and_chordComparisons`,
    and the corresponding `Figure9ExactAngleContainmentCertificate` /
    `PointwiseFigure9SelectedExactAngleContainmentCertificate` constructors
    let S5 use total-turn control plus pointwise cosine/chord comparisons
    directly.
    Exact finite-`p_i/q_i` S5 route:
    `ExactFigureWitnessSourceW34.S5AngleRowsForFinitePQSpineGeneratedOrderSource`
    is the row-wise S5 angle package for the generated finite label
    certificate.  The label certificate supplies distance rows via
    `figure8FiniteLabelAdjacencyDistinctnessRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificate`
    and
    `figure9FiniteLabelAdjacencyDistinctnessRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificate`,
    while `S5AngleRows` supplies the quantitative angle rows via
    `figure8CentralAngleLeSeparatedTurnRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`
    and
    `figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`.
    The compact S5 bundle is
    `distance_and_angle_rowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`,
    and the direct local-window/honest-Euclidean constructors are
    `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`
    and
    `localWindowContainmentFieldsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`.
    Newest finite-PQ concrete row wrappers:
    `Figure8CentralAngleTurnSubwindowRowsForFinitePQSpineGeneratedOrderSource`,
    `Figure8CentralAngleTurnSubwindowEqRowsForFinitePQSpineGeneratedOrderSource`,
    `Figure9AdjacentLeftCosineTurnRowsForFinitePQSpineGeneratedOrderSource`,
    `Figure9AdjacentLeftTurnChordRowsForFinitePQSpineGeneratedOrderSource`,
    their Figure 8/Figure 9 projections, and the four compact
    `s5AngleRowsForFinitePQSpineGeneratedOrderSource_of_*` constructors reduce
    finite-PQ S5 angle rows to actual Figure 8 subwindow rows plus Figure 9
    cosine/chord rows.
    Additional finite-PQ wrappers now cover Figure 8 Icc/indexed
    subwindow/equality rows and total-turn Figure 9 cosine/chord comparison
    rows, including `figure9LeftAngleLeMiddleTurnRowsForFinitePQSpineGeneratedOrderSource_of_totalTurn_and_cosineComparisonRows`,
    the chord analogue, and the `S5AngleRowsForFinitePQSpineGeneratedOrderSource`
    constructors from Icc/indexed Figure 8 rows plus middle-turn/comparison
    rows.  Direct `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource`
    constructors also consume those combinations.  Remaining S5 content is the
    actual subwindow selection and comparison rows from finite-label geometry.
    Boundary-label S5 now exposes local finite-label row surfaces
    `M8FiniteBoundaryFrameCoreLabelCertificate.Figure8CentralAngleTurnSubwindowRows`,
    `Figure8CentralAngleTurnIccSubwindowRows`,
    `Figure8CentralAngleTurnIndexedSubwindowRows`,
    `Figure9AdjacentLeftCosineTurnRows`, `Figure9AdjacentLeftTurnChordRows`,
    and cosine/chord comparison row aliases, with `S5AngleRows` constructors
    such as `.ofTurnSubwindowRowsAndCosineTurnRows` and
    `.ofTurnSubwindowRowsAndCosineComparisonRows`.  Remaining S5 work is to
    inhabit these rows from the actual finite label/turn geometry.
    W34 also has local-honest finite-PQ wrappers
    `localHonestEuclideanRowsForFinitePQSpineGeneratedOrderSource_of_distance_rows_and_cosineComparisonRows`,
    `.of_distance_rows_and_chordComparisonRows`, and the finite-label-row
    variants with central-angle rows plus Figure 9 comparison rows.  Remaining
    S5 content is still the actual comparison/subwindow row source.
    W11 now exposes actual-turn S5 carriers
    `Figure8CentralAngleActualTurnIccSubwindowRows`,
    `Figure8CentralAngleActualTurnIndexedSubwindowRows`,
    `Figure9AdjacentLeftActualTurnCosineComparisonRows`, and
    `Figure9AdjacentLeftActualTurnChordComparisonRows`, plus adapters
    `s5AngleRows_of_actualTurnIccRowsAndCosineComparisonRows` and indexed /
    chord variants.  Remaining S5 work is to inhabit those actual-turn rows
    from triangle-run/turn-angle geometry.
    Newest W11 turn-angle reductions:
    `Figure8CentralAngleTurnAngleIccSubwindowRows`,
    `Figure8CentralAngleTurnAngleIndexedSubwindowRows`,
    `Figure9AdjacentLeftTurnAngleCosineComparisonRows`, and
    `Figure9AdjacentLeftTurnAngleChordComparisonRows` feed the actual-turn
    carriers via the `*_of_turnAngleRows` constructors.  The exact S5 source
    now is the real turn-angle row package for the selected triangle run:
    subwindow membership for Figure 8 and pointwise cosine/chord comparisons
    for Figure 9.
    Latest Figure 8 turn-angle bridge:
    `Figure8CentralAngleTriangleRunIccSubwindowRows` plus
    `figure8CentralAngleTurnAngleIccSubwindowRows_of_triangleRunIccSubwindowRows`
    turns explicit triangle-run Icc subwindow rows into the W11 Figure 8
    turn-angle row package.  The remaining Figure 8 source is the actual
    triangle-run Icc subwindow selection for each separated failed pair.
    `ExactFigureWitnessSourceW34` now has finite-PQ wrappers that connect W11
    actual-turn Figure 8/Figure 9 rows to
    `S5AngleRowsForFinitePQSpineGeneratedOrderSource` using the existing
    finite-label distance machinery.  The remaining S5 source is the actual W11
    turn rows themselves, not a finite-PQ adapter.
    `ExactFigureRowsAssemblyW32` now also has local adapters from finite-label
    `S5AngleRows` to `LocalHonestEuclideanInequalitySourceFields`, plus direct
    W11 turn-angle adapters for Figure 8 Icc/indexed rows with Figure 9
    cosine/chord comparison rows.  Do not add more S5 adapter layers unless the
    source row shape changes.

### S6. Swanepoel Final Assembly

- [ ] Inhabit `SwanepoelW32FinalAssembly.W34ActualRoutePremises`.
  - Short route inputs:
    checked no-cut family; actual topology/component closure; compatible
    finite-spine generated-order rows; S4 route coverage; S5 exact figure rows
    or local-window containment.
  - Preferred final constructors:
    `w34ActualRoutePremises_of_exactRemainingInputPackage`,
    `w34ActualRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_lemma9Late_localWindowContainment`,
    `w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_localWindowContainment`,
    and `w34ActualRoutePremises_of_boundaryWalkGapCoverage_lemma9Late_figure8_figure9_rows`.
    The nat-late plus containment-interface constructor
    `w34K23LocalExactAngleRoutePremises_of_refuting_bothPlusSidesCutForced_finitePQSpineRows_boundaryWalkGapCoverage_natLate_containmentInterfaces`
    is a checked compatibility alias for the same `W34ActualRoutePremises`
    route; name it that way if it appears in handoff text.
  - Use `W34ActualRoutePremises` as the live route name in task text.  Older
    route names are compatibility aliases only; do not create new tasks around
    them.
  - Latest compact package:
    `w34ActualRoutePremises_of_exactRemainingInputPackage` consumes exactly the
    S2 boundary target, S3 skeleton/angle rows, S4 missing long-arc/triangle-run
    field, finite `p_i/q_i` generated-order rows, S4 carrier plus K23 geometry,
    and S5 selected-figure/Figure 8/Figure 9 rows.  Use this as the final
    assembly surface while proving the remaining positive source fields.
    The newer
    `w34ActualRoutePremises_of_exactRemainingInputPackage_honestSourceRows`
    consumes the honest source rows directly: K23 witness rows plus local
    honest S5 rows and Figure 9 middle-turn rows.  Prefer this constructor
    when integrating the latest S4/S5 obligations.
    The distance/angle-row variant
    `w34ActualRoutePremises_of_exactRemainingInputPackage_distance_and_angle_rows`
    is the current shortest S5-facing constructor when the four atomic figure
    row families are available.
    The newer
    `w34ActualRoutePremises_of_exactRemainingInputPackage_atomicFigureRows`
    removes the stronger Figure 9 middle-turn input from that shortest route.
    The compact S4/S5 route
    `w34ActualRoutePremises_of_exactRemainingInputPackage_actualNoGap_compactS4S5`
    consumes long-arc rows, the W16 finite-`p/q` theorem, actual no-gap rows,
    K23 witness rows, and bundled S5 rows directly.
    Finite generated-order rows after closure can also be sourced from W16 /
    finite-walk data via
    `selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreData` and
    `selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreData`.
    W16 finite `p/q` cyclic-successor rows alone are not enough for generated
    order.  The exact upgrade surface is
    `selectedFinitePQSpineGeneratedOrderRows_nonempty_of_finiteWalkFrameCoreCenterDegreeSix`
    or the direct-extra-cardinality variant.  The missing payload is
    `BoundaryArcFiniteWalkFrameCoreData`, `boundaryArc_eq`,
    `centerDegreeSix` or `extraNeighborCardTwo`, and generated cyclic-order
    rows for the finite-walk frame core.
    Newest generated-order source:
    `FrameCyclicOrderAssemblyW32.SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows`
    and the center-degree-six variant package the missing finite-walk frame
    core, boundary-arc equality, extra-neighbor-cardinality/degree-six, and
    generated cyclic-order rows.  They feed
    `selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreGeneratedOrderSourceRows`
    and
    `selectedFinitePQSpineGeneratedOrderRowsOfFiniteWalkFrameCoreCenterDegreeSixGeneratedOrderSourceRows`.
    The selected finite-walk generated-order source rows now store the current
    frame-core fields directly and expose raw-fact plus bundled
    boundary-arc-frame-core constructors.  Remaining generated-order work is
    positive inhabitation of those raw/frame-core and generated cyclic-order
    inputs, not another row-shape adapter.
    Newest generated-order bridge:
    `selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfFinitePQSpineFrameCoreLemma8Rows`
    and its nonempty form produce final-consumable generated-order source rows
    from finite-spine frame-core/Lemma 8 rows plus
    `SelectedFinitePQSpineGeneratedCyclicRows`; the extra-neighbor cardinality
    row is derived from `finiteRows.lemma8`.  The remaining generated-order
    blocker on this route is exactly the selected finite-`p/q` generated cyclic
    rows.
    `FrameCyclicOrderAssemblyW32` now constructs those selected generated
    cyclic rows from
    `BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate.ExplicitCyclicOrderRows`
    through `selectedFinitePQSpineGeneratedCyclicRowsOfExplicitCyclicOrderRows`
    and its nonempty form.  Remaining generated-order source is therefore the
    explicit finite-spine cyclic-order rows, already available from the
    boundary-spine source package.
    Newest raw-fact route:
    `PointwiseFinitePQSpineRawFrameCoreFacts`,
    `finitePQSpineFrameCoreFields_iff_rawFacts`,
    `finitePQSpineGeneratedOrderRowsOfRawFacts`,
    `selectedFinitePQSpineGeneratedOrderRowsOfRawFacts`,
    `SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows.rawFacts`, and
    `selectedFiniteWalkFrameCoreGeneratedOrderSourceRowsOfRawFacts` connect
    finite-spine raw cyclic-order/frame-core facts to generated-order rows.
    M8 construction now has the local-honest shortest route
    `m8ConstructionData_nonempty_of_exactTopology_longArc_finitePQTheorem_generatedFiniteWalk_realizationCarrier_badAdjacencyIncidence_localHonestRows`.
    Final assembly now has the matching constructor
    `w34ActualRoutePremises_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`.
    The remaining final-route inputs are the actual source rows named in that
    theorem: S2 exact topology, S3 sector theorem, long-arc rows, W16 finite
    p/q theorem, finite-walk generated-order rows, realization-carrier no-gap
    rows, K23 incidence rows, and S5 label-angle rows.
    `BrokenLatticeMinimalFailure` already closes
    `no_minimalClearedFailure` from a `MinimalFailureM8ConstructionEliminator`
    via `M8ConstructionData.contradiction` and
    `no_minimalClearedFailure_of_m8ConstructionEliminator`.  Do not import
    `M8ConstructionDataInhabitationW33` back into that file; it would form a
    cycle.  The remaining bridge is upstream construction of M8 data for every
    minimal failure from the current source rows.
    Current M8 endpoint:
    `m8ConstructionData_nonempty_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`
    and
    `contradiction_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w16_finiteWalkGeneratedOrder_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`
    match the final source surface exactly.  Remaining blockers are only the
    positive source inputs themselves.
    `SwanepoelW32FinalAssembly` now also exposes the exact-source contradiction
    composition theorem with that same source-row surface, so the contradiction
    route and M8 data route are aligned.  Do not add another final-assembly
    shape wrapper unless the source inputs change.
    Current closure-package M8 endpoint:
    `m8ConstructionData_nonempty_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows`
    consumes the exact closure/missing-field package, finite-walk generated
    order, realization-carrier rows, bad-adjacency rows, and S5 rows directly.
    No M8 constructor mismatch remains; remaining work is positive inhabitation
    of those source inputs.
    `SwanepoelW32FinalAssembly` now has the same closure-package-shaped
    conditional M8 source and contradiction wrapper, and older long-arc/W16
    adapters route through it.  Do not add more M8 source-shape wrappers unless
    the final source inputs themselves change.
    `MinimalGraphFacts` cannot import the M8 route without a cycle
    (`MinimalGraphFacts -> BrokenLatticeMinimalFailure -> ... -> MinimalGraphFacts`).
    Downstream closure already exists via
    `BrokenLatticeMinimalFailure.no_minimalClearedFailure_of_m8ConstructionEliminator`
    and `M8ConstructionDataInhabitationW33.no_minimalClearedFailure_of_routeCertificate`.
    The exact remaining route source is
    `Nonempty M8ConstructionDataInhabitationW33.StrongestRouteSource`,
    equivalently `NoCutMinimalityClosureW34.ExactRemainingPremiseForNoCutMinimalityClosure`.
    W16 also exposes
    `finitePQSpineCyclicSuccessorRowsTarget_of_frameCoreData` for frame-core
    finite-`p/q` successor rows.
    W16 now has the assembly-facing
    `FinitePQSpineExplicitCyclicOrderRowsAndRawFactsTheorem` and
    `finitePQSpineCyclicSuccessorRowsTheorem_of_explicitCyclicOrderRowsAndRawFactsTheorem`,
    reducing the final W16 theorem to finite label certificate,
    explicit cyclic-order rows, and raw frame-core facts.
    The old exact-input constructor that listed ten independent inputs is now
    stale.  The current compact final route has seven positive source
    obligations:
    S2 `MinimalFailureExactActualTopologyFieldsTarget`;
    S3 `SelectedNondegenerateTopologyOuterFaceSectorOrderTheorem`; an
    `ExactActualTopologyClosureMissingFieldPackage` for the resulting skeleton
    rows, or its expanded long-arc plus W16 source; finite-walk
    `SelectedFiniteWalkFrameCoreGeneratedOrderSourceRows`; K23
    `SelectedFrameActualSelectedBoundaryGapTriangleDegree34RealizationCarrierRowsSourceTheorem`;
    K23 `SelectedFrameBadAdjacencyCommonNeighborRowsSourceTheorem`; and compact
    S5 `S5AngleRowsForFinitePQSpineGeneratedOrderSource`.  `MinimalBoundaryTopologySkeletonFamily`,
    old actual-cycle targets, atomic distance rows, and separate K23 witness
    rows are not independent blockers on this compact surface.
    W33 now has the exact-S2 package route
    `ExactActualTopologyClosureMissingFieldPackage` and
    `exactActualTopologyClosureMissingFieldPackageOfSkeletonRowsLongArcFinitePQSpineCyclicSuccessorRowsTheorem`,
    consuming exact actual topology fields, W33 skeleton rows, W24 long-arc
    family, and the W16 finite-`p/q` theorem to produce the matching
    missing-field/closure pair for final assembly.
    `SelectedTopologyRowsInhabitationW33` also exposes direct constructors for
    `ExactActualTopologyClosureMissingFieldPackage` from W24 missing-field
    rows, W13 gap-negative rows plus W16, no-boundary-gap rows plus W16, and
    the explicit triangle-run/long-arc row surfaces.  Use these constructors
    before adding any new W33 closure layer; the remaining work is positive
    source inhabitation.
    Newest exact-S2/source-row constructor:
    `w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelAngleRows`
    composes exact topology fields, the S3 sector theorem, W33's
    `ExactActualTopologyClosureMissingFieldPackage`, finite-walk generated
    order rows, realization-carrier no-gap rows, bad-adjacency K23 rows, and
    finite label/S5 angle rows into `W34ActualRoutePremises`.  This is now the
    preferred S6 integration surface after S2/S3/S4/S5 positive sources are
    inhabited.
    `w34ActualRoutePremises_of_exactActualTopologyClosureMissingFieldPackage_finiteWalkGeneratedOrder_realizationCarrier_badAdjacency_labelCertificateS5AngleRows`
    is the still-shorter S5-facing form: it consumes the generated finite label
    certificate plus `S5AngleRowsForFinitePQSpineGeneratedOrderSource`; the
    label certificate supplies the two distinctness rows and the S5 angle rows
    supply Figure 8 central-angle plus Figure 9 middle-turn upper bounds.
    On the S5 distance side,
    `BoundaryLabelCertificateAssembly.M8FiniteBoundaryFrameCoreLabelCertificate.figure8DistanceWitnessRows`
    and `.figure9DistanceWitnessRows` already construct the local Figure 8/9
    distance witness rows from a finite boundary frame-core label certificate.
    The remaining S5 proof work is the actual Figure 8 central-angle
    containment and Figure 9 left-angle or middle-turn-upper-bound rows for the
    generated frame.
    Latest final/S5 integration:
    `ExactFigureRowsAssemblyW32` now has finite-label S5 constructors for
    Figure 8 containment and Figure 9 middle-turn-to-left-angle containment,
    and `ExactFigureWitnessSourceW34.honestEuclideanSourceComponentsForFinitePQSpineGeneratedOrderSource_of_labelCertificateS5AngleRows`
    hands compact S5 rows to exact figure components.  `SwanepoelW32FinalAssembly`
    checks again after removing an unused proof-irrelevance cast theorem and
    routing the exact topology/S3/long-arc/W16/generated-order/no-gap/K23/S5
    surface through the closure-package helper.  M8 also exposes
    `routeCertificate_of_exactActualTopologyFields_outerFaceSectorOrderTheorem_longArc_w24NoCut_w16FinitePQ_generatedFiniteWalk_realizationCarrier_incidenceRows_labelCertificateS5AngleRows`
    as the strongest route-certificate endpoint for that source surface.
  - Compile status:
    `SwanepoelW32FinalAssembly` now builds with the pinned toolchain after
    removing duplicate `Verified` aliases already exported by
    `SwanepoelW32RouteAudit` and fixing the generated-order row universe.
    This does not inhabit `W34ActualRoutePremises`; it only verifies the
    conditional assembly surface.

- [ ] Derive the internal lower-bound target from the inhabited route.
  - Target: `Swanepoel.targetLowerBoundEightThirtyOne`.
  - Current conditional wrappers are not enough; `W34ActualRoutePremises` must
    be inhabited unconditionally and imported.

- [ ] Add public Swanepoel wrappers only after the internal theorem builds and
  the audit is clean.
  - File: `ErdosProblems1066/KnownBounds.lean`.
  - Public theorem shape: `Verified.lower_bound_eight_thirty_one` and a
    source-specific alias.

## Pach--Toth After Swanepoel

Do not spend effort on blocked rigid or translated-equation routes.  The
Pach--Toth public wrapper remains absent until the exact/arbitrary internal
targets are unconditional and audited.

### P1. Quarantine Blocked Routes

- [x] The proof-used Figure 2 edge-role table is checked infrastructure.
  Keep names/docstrings honest: it is not a complete PostScript transcription.

- [x] Treat the exact-base all-positive direct-flexible W33 source as refuted.
  - Checked blockers:
    `FiniteReducedMetricCandidateSearchW33.not_directFlexibleSourceShape`,
    `FlexibleCandidateMetricInhabitationW33.not_nonempty_directFlexibleSourcePayload`,
    and related length-one exact-base obstruction theorems.
  - Consequence: do not task workers with inhabiting the all-positive
    `DirectFlexibleSourcePayload` / `CandidatePeriodMetricData` lane unless
    they first explain why the checked obstruction no longer applies.
  - Current status:
    `CrossBlockMetricInequalitiesW33` pins the obstruction to the forced
    `T2_2 -> T1_1` unit row versus exact squared distance `12`.  This is a
    real no-go result for the exact-base all-positive flexible surface.
    W34 non-rigid material may supply conditional eventual/threshold
    endpoints, but not an unconditional Pach--Toth theorem by itself.

- [ ] Keep concrete four-target / translated-equation lanes out of the live
  proof route.
  - Blocked or audit-only modules include:
    `RoleHingeConcreteSearch`,
    `OrbitSqDistancesW12`,
    `TransitionAlternativeW13`,
    `ConcreteLowerTableValueDataBlockerW32`,
    `PeriodCandidateConcreteTableBlockerW32`.

### P2. Choose The Live Closed-Placement Route

- [ ] Target an eventual/threshold non-rigid route unless a verified
  alternative supersedes the W33 obstruction.
  - Deliverable:
    `EventualRoleHingeClosure.EventualFiniteCertificateObligations K0` or
    `LargeClosedPlacementW12.LargeExplicitClosedPlacementCertificates K0`.
  - Fields: same/opposite transition data, thresholded orientation words,
    indexed algebraic period equations, and global separation.
  - Gate: yields explicit closed-placement certificates for all large block
    counts.
  - Latest checked bridge:
    `RoleHingeCandidateSearchSurface` now has a positive thresholded route via
    `EventualPeriodSearchData T K0` and `EventualCrossBlockMetricData P`,
    proving eventual, large-block, and arbitrary-`n` targets once those
    thresholded sources and the matching small-case package are inhabited.
    `AlternativeNonRigidClosedPlacementW34` and
    `PachTothRemainingSourceLedgerW34` now also expose the threshold-six metric
    route: large closed-placement fields for `k >= 6` plus
    `BelowThresholdMetricFieldsSix` yield the full deformed metric-field
    family and the exact/arbitrary targets.  `BelowThresholdMetricFieldsSix`
    is now obtained from
    `ClosedPlacementSmallKCertificatesW19.SmallExplicitTransitionCertificateSource`,
    so the exact small source has the same honest geometry surface as the
    existing small-certificate route.
    Large exact blocks from six onward now route through threshold-six
    closed-placement fields via
    `largeExactBlockTargetsFromSix_of_largeClosedPlacementFieldsSix` and
    related adapters in `EventualClosedPlacementSourceW34`,
    `RemainderSplitSourceClosureW32`, and
    `AlternativeNonRigidClosedPlacementW34`.  This remains secondary until the
    Swanepoel route is closed.

- [ ] Provide the finite small-complement package for the chosen threshold.
  - Deliverable: exact certificates below the threshold induced by `K0`.
  - Owners:
    `PachToth/ClosedPlacementSmallKCertificatesW19.lean`,
    `PachToth/SmallLengthExactTargetsConcreteW24.lean`.
  - Warning: `SmallUpTo_sixteen` only suffices for arbitrary `n` when the
    block threshold is compatible with `K0 <= 1`.
  - Current blocker:
    the checked small-source lane still needs a genuine
    `DeformedLengthOneTransitionGeometry` / `DeformedLengthOneSource`; the
    helper route through exact-base flexible generated closure depends on the
    now-refuted W33 direct-flexible gate.
  - Checked W34 status:
    `PachToth/DeformedLengthOneSourceW34.lean` records the honest
    geometry-to-source constructors and the blocker theorem
    `not_nonempty_directFlexibleSourcePayload`, citing the W33
    `T2_2 -> T1_1` exact-base length-one obstruction.
    The current reduced small side is
    `DeformedLengthOneExactBlocksTwoThroughFiveSource`, equivalently a genuine
    deformed length-one source plus exact blocks two through five; it feeds the
    threshold-six arbitrary/exact adapters in
    `SmallLengthExactTargetsConcreteW24`, `RemainderSplitSourceClosureW32`, and
    `FarApartRemainderSourceW34`.

### P3. Prove Closed Placements And Separation

- [ ] Construct same/opposite non-rigid transition data.
  - Owners:
    `PachToth/RoleHingeCandidateSearchSurface.lean`,
    `PachToth/FlexibleTransitionSearchW11.lean`,
    `PachToth/EventualRoleHingeClosure.lean`.

- [ ] Construct period/closure certificates for the selected route.
  - Owners:
    `PachToth/PeriodSearchInterface.lean`,
    `PachToth/PeriodWordCertificates.lean`,
    `PachToth/EventualRoleHingeClosure.lean`.

- [ ] Prove global separation through reduced cross-block metric tables.
  - Owners:
    `PachToth/GeneratedSeparationFarApart.lean`,
    `PachToth/CrossBlockLowerBoundsInterface.lean`,
    `PachToth/RoleHingeCandidateSearchSurface.lean`.

### P4. Pach--Toth Final Assembly

- [ ] Derive the eventual target after large closed placements are inhabited.
  - Target: `PachToth.targetUpperConstructionFiveSixteenEventually`.

- [ ] Derive the exact all-block target only from an all-positive certificate
  family.
  - Target: `PachToth.targetUpperConstructionFiveSixteen`.

- [ ] Derive the arbitrary target only after the exact target or a threshold
  route plus matching finite small cases.
  - Target: `PachToth.targetUpperConstructionFiveSixteenArbitrary`.
  - Latest far-apart split bridge:
    `FarApartRemainderSourceW34` and `RemainderSplitSourceClosureW32` now build
    `CanonicalSplitRealization k r` internally from an exact chain/closed
    placement family and checked finite remainders using translated far-apart
    placement.  The remaining split blocker is no longer far-apart placement;
    it is `MinimalExactRemainderSplitSourceBlocker`, equivalently
    `ExactBlocksOneThroughFive /\ LargeExactBlockTargetsFromSix`.

- [ ] Add public `KnownBounds` wrappers only after the matching internal
  theorem builds and passes the audit.

## Project Structure Tasks

- [ ] Keep `TASK.md` as this active execution queue.  Put theorem dependency
  explanations in `proof_workings/theorem_dependency_map.md`.
- [ ] Do not create new W-numbered files for bookkeeping.  If a W-numbered file
  remains, it must be a checked proof/certificate/blocker or a documented
  compatibility surface.
- [ ] For every unrooted Lean file, either root-import it after a targeted
  pinned check, merge it into the owning module, or remove/quarantine it with
  the owner decision recorded outside TASK.md.
- [ ] Defer physical folder moves until imports are stabilized.  When moving
  later, move one semantic cluster at a time and leave old-path import shims
  until all downstream imports are migrated.
