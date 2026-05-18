# Current Lean frontier

This note records the documentation/Lean frontier after a read-only pass over
`proof_workings/*_lean_ready.md`, `Proof_Files/`, and the current Lean modules.
It is a handoff note for kernel-checked work; it is not a new proof document.

## Source documents

- `Proof_Files/Po85.pdf` -> `proof_workings/pollack_1985_lean_ready.md`.
- `Proof_Files/Cs98.pdf` -> `proof_workings/csizmadia_1998_lean_ready.md`.
- `Proof_Files/Sw02.pdf` -> `proof_workings/swanepoel_2002_lean_ready.md`.
- `Proof_Files/PaTo96.ps` -> `proof_workings/pach_toth_1996_lean_ready.md`
  and the source audit in `proof_workings/pach_toth_postscript_audit.md`.

## Kernel-checked public facade

The only public verified theorem wrappers are still:

- `ErdosProblems1066.Verified.upper_bound_third`.
- `ErdosProblems1066.Verified.lower_bound_quarter`.
- `ErdosProblems1066.PollackPach.lower_bound_quarter`.

These are backed by `ErdosProblems1066/UnitDistanceBounds.lean` and
`ErdosProblems1066/KnownBounds.lean`, with reusable support in
`ErdosProblems1066/Combinatorics/*` and `ErdosProblems1066/Geometry/*`.
The source-faithful Pollack planarity/four-color route remains untranscribed;
the theorem-level `n / 4` result is checked by the Pach-style semicircle and
greedy-coloring route described as Q1-Q10 in the Pollack proof plan.

## Pollack 1985

Backed by Lean:

- Q1-Q3: semicircle obstruction lemmas are checked in
  `UnitDistanceBounds.lean` and mirrored in `Geometry/Semicircle.lean`.
- Q7-Q10: greedy coloring, large color class, and the final lower bound are
  checked in `UnitDistanceBounds.lean`, `Combinatorics/Coloring.lean`,
  `Combinatorics/Independence.lean`, and `KnownBounds.lean`.

Still explicit assumptions or untranscribed source route:

- P3-P6, the literal Pollack route through crossing unit diagonals, planar
  unit-distance graphs, and a planar four-color theorem interface.

Next Lean modules only if a source-faithful Pollack route is desired:

- `Pollack/Planarity.lean` for crossing-unit-segment and straight-line planar
  graph facts.
- `Pollack/FourColorBridge.lean` for a finite planar graph coloring interface.

## Csizmadia 1998

Backed by Lean:

- No Csizmadia-specific Lean module exists yet. Only shared finite-set,
  independent-set, distance, and arithmetic infrastructure can be reused.

Still explicit assumptions:

- Boundary cycle and turn package, boundary degree bound, strict turn lower
  bound, irregular-vertex common-neighbor lemma, figure inequalities,
  block decomposition, eight adjacent-block cases, Case A independence and
  neighbor counting, and the final nine-point Lemma 3 checks.

Next modules to transcribe:

- `Csizmadia/LocalDeletion.lean` for Lemma 3.2, Theorem 3.3, and Lemmas
  4.1-4.3.
- `Csizmadia/BoundaryTurns.lean` for the outer-boundary and turn interfaces.
- `Csizmadia/BlockDecomposition.lean` for Lemmas 8.6-8.7 once turn bounds are
  available.
- `Csizmadia/FigureGeometry.lean` for Lemma 7.1 and Lemma 12.1 analytic
  obligations.

## Swanepoel 2002

Backed by Lean:

- Target proposition only: `Swanepoel.Bridge` defines
  `targetLowerBoundEightThirtyOne`; `Swanepoel.TargetReduction` proves that
  cleared `8 / 31` interfaces imply it.
- E1/E2-facing graph and Euclidean edge infrastructure:
  `GraphBridge`, including the Mathlib `SimpleGraph` bridge,
  `PlanarInterface`, `NoncrossingUnitEdges`, `FaceReduction`,
  `FaceCountingBridge`, `DegreeBound`, and `DegreePipeline`.
- E5-E7-facing minimal-counterexample arithmetic and deletion bookkeeping:
  `MinimalCounterexample`, `CounterexamplePipeline`, `MinimalGraphFacts`,
  `InducedSubconfiguration`, and `MinimalFailureClosure`.
- E10-E13 arithmetic side of boundary counting:
  `BoundaryCounting`, `AngleArithmetic`, and `OuterBoundaryInterface`,
  conditional on explicit face, polygon, and angle-lower-bound data.
  `OuterBoundaryReduction` derives the simple-polygon noncrossing witnesses
  from supplied canonical boundary cycles.
- E21-E24 finite Lemma 10 contradiction:
  `Lemma10Inequalities`, `Lemma10Bridge`, `Lemma10Pipeline`,
  `Lemma10AnalyticBridge`, `Lemma10EuclideanBridge`, `AngleBridgeFacts`,
  `Lemma10AngleToTurn`, `AngleGeometry`, `TriangleAngleFacts`, and
  `BrokenLatticePipeline`, conditional on angle-containment facts for the
  Figure 8/Figure 9 turn windows and Lemma 8/Lemma 9 label hypotheses.
- Local graph exclusion infrastructure:
  `LocalExclusions` proves common-neighbor, `K_{2,3}`, and local-degree
  bookkeeping lemmas used by the planned Lemma 8/Lemma 9 construction.
  `MinimalFailureLocalExclusions` proves the conditional minimal-failure
  closure principle for locally certified degree-deletion patterns.
  `CommonNeighborGeometry` proves the geometric two-circle common-neighbor cap
  directly, so the `K_{2,3}` exclusion itself is no longer conditional on a
  deletion reducer.  `MinimalFailureLocalExclusions` now also constructs the
  induced smaller `UDConfig` and embedding automatically from local
  deleted/reinserted sets.  `LocalDeletionConstructors` packages the global
  closure theorem from a minimal-failure local-deletion eliminator to the
  Swanepoel target proposition.

Still explicit assumptions:

- Construction of the outer-face/simple-boundary and subpolygon witnesses
  from an arbitrary separated unit-distance configuration.
- Oriented/interior angle API, polygon angle sums, and face angle lower bounds;
  the local unoriented `pi / 3` angle bridge is now checked in
  `AngleGeometry`.
- Convex four-cycle and unique common-neighbor facts beyond the now-checked
  generic `K_{2,3}`/common-neighbor cap, plus the concrete local
  deleted/reinserted sets for remaining reducible patterns.
- Subpolygon low-degree construction used by E13/E14/E18/E19.
- Actual containment of the checked Figure 8/Figure 9 geometric angles inside
  the corresponding E22/E23 turn windows.
- Full Lemmas 6, 8, and 9 as graph/geometric constructions rather than
  hypotheses feeding the checked finite pipelines.
- Nonparalleloid Section 5 remains isolated in N0-N9 and is not a prerequisite
  for the Euclidean theorem E.

Next modules to transcribe:

- `Swanepoel/OuterBoundary.lean` for constructing the E8/E9 boundary-cycle
  and face data currently packaged explicitly by `OuterBoundaryInterface`.
- `Swanepoel/AngleContainment.lean` for the oriented turn-window containment
  facts feeding E22 and E23.
- `Swanepoel/LocalDegreeReductions.lean` for E4 and unique common-neighbor
  inputs through certified deletion data.
- `Swanepoel/SubpolygonLowDegree.lean` for E13 and the repeated polygon
  contradiction pattern.
- `Swanepoel/BrokenLattice.lean` for Lemmas 6, 8, and 9 as honest geometric
  outputs.
- `Swanepoel/Lemma10Geometry.lean` for the Figure 8/Figure 9 analytic proofs
  currently named by `Lemma10AnalyticBridge`.

## Pach--Toth 1996

Backed by Lean:

- Target proposition only: `PachToth.Bridge` defines
  `targetUpperConstructionFiveSixteen`; `PachToth.TargetReduction` proves
  indexed-chain realizations imply it.
- Finite arithmetic, block partition, and chain counting:
  `Arithmetic`, `FiniteGraph`, `Chain`, `BlockPartition`, `IndexedChain`,
  `ConditionalUpper`, `ArbitraryN`, `Remainder`, `RemainderConstruction`, and
  `SplitSoundness`.
- Exact one-block and same-block geometry:
  `ExactLocalGeometry`, `AffineLocalGeometry`, and `OneBlockSoundness`.
- Cross-block obstruction and partial connector data:
  `CrossBlock`, `CrossBlockGeometry`, `OrientedCrossBlockGeometry`, and
  `ConnectorEquationFacts`, `RealTranslationObstruction`, and
  `Figure2Certificate`.
- Honest placement interfaces:
  `PlacementBridge`, `GeometricSoundness`, `DeformedPlacement`,
  `OrientationData`, `DeformedOrientationBridge`, and
  `ClosedPlacementInterface`. `ClosedChainConstruction` repackages supplied
  closed-chain/oriented-placement data into those explicit certificates.
  `ClosedPlacementAlgebra` proves transition-iteration facts for supplied
  same/opposite transition data.
- Arbitrary-`n` split packaging:
  `SplitCertificateBridge` reduces the final split construction to an exact
  closed placement plus an explicit far-apart remainder certificate, and
  `RemainderPlacement` constructs that certificate by translating the
  checked remainder block far from the exact chain.
- Final conditional spine:
  `ClosedChainReduction` routes explicit closed-placement certificates to the
  exact-multiple and arbitrary-`n` target propositions; the arbitrary-`n`
  route no longer assumes separate far-apart remainder data.

Still explicit assumptions:

- Complete Figure 2 finite graph transcription and audit certificate.
- Finite enumeration/certificate for "full block forces next block at most 4"
  in both same/opposite transition cases.
- Certified non-rigid closed-chain construction with explicit `K0`.
- Global separation for all vertices in the closed chain.
- The far-apart remainder placement is checked; the remaining arbitrary-`n`
  blocker is the same closed-placement family needed for the exact blocks.

Next modules to transcribe:

- `PachToth/Figure2Certificate.lean` for the complete finite graph and
  transition data certificate.
- `PachToth/BlockEnumeration.lean` for the full-block/next-small theorem.
- `PachToth/ClosedChainExistence.lean` for the non-rigid closed chain and
  explicit threshold.

## Trust notes

A source scan of Lean files under `ErdosProblems1066/` found no `sorry`,
`admit`, or `axiom`. The target names for Swanepoel `8 / 31` and Pach--Toth
`5 / 16` are definitions of propositions, not public verified theorems.
