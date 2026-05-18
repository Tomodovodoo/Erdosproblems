# ErdosProblems1066

Lean formalization workspace for Erdos problem 1066, pinned to the Aristotle
compatible Lean and Mathlib versions.

## Toolchain

- Lean: `leanprover/lean4:v4.28.0`
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- Build command on this machine:

```powershell
elan run leanprover/lean4:v4.28.0 lake build
```

The plain `lake` shim on this Windows PATH may resolve incorrectly. Prefer the
toolchain-routed `elan run ...` command above.

The Aristotle API key is expected to live in the user/system environment as
`ARISTOTLE_API_KEY`. It is not stored in this repository.

## Lean Layout

- `ErdosProblems1066.lean`: root import file. It imports every retained checked
  Lean module so a root build covers the whole project.
- `ErdosProblems1066/KnownBounds.lean`: public facade. It exposes only
  kernel-checked theorem wrappers.
- `ErdosProblems1066/UnitDistanceBounds.lean`: legacy imported proof file with
  the core definitions and the currently verified `1 / 3` upper construction
  and `1 / 4` lower bound.
- `ErdosProblems1066/Combinatorics/`: reusable finite coloring and
  independent-set helpers.
- `ErdosProblems1066/Geometry/`: reusable Euclidean distance and semicircle
  lemmas.
- `ErdosProblems1066/Swanepoel/`: checked arithmetic, vocabulary, Lemma-10
  inequality/pipeline modules, and counterexample reduction modules for the
  future `8 / 31` proof, plus a bridge module that records the target statement
  as an in-progress proposition.
- `ErdosProblems1066/PachToth/`: checked arithmetic, raw coordinate facts,
  first-block finite graph data, block partition accounting, cross-block
  connector data, geometric soundness adapters, and target-reduction modules for
  the future `5 / 16` proof, plus bridge modules that keep the remaining
  realization obligations explicit.
- `proof_workings/`: Lamport-style proof plans transcribed from the downloaded
  papers. These are roadmaps, not Lean theorems.

## Current Verified Public Theorems

The public facade is namespace-scoped:

- `ErdosProblems1066.Verified.upper_bound_third`
- `ErdosProblems1066.Verified.lower_bound_quarter`
- `ErdosProblems1066.PollackPach.lower_bound_quarter`

The Swanepoel `8 / 31` lower bound and Pach--Toth `5 / 16` upper construction
are not declared as Lean theorems yet. They will remain absent from the public
facade until their proof terms are fully formalized without `axiom`, `sorry`,
or `admit`.

Bridge modules:

- `ErdosProblems1066.Swanepoel.Bridge` defines
  `Swanepoel.targetLowerBoundEightThirtyOne`, the intended `8 / 31` statement as
  a proposition only.
- `ErdosProblems1066.PachToth.Bridge` defines
  `PachToth.targetUpperConstructionFiveSixteen`, the intended `5 / 16` block
  construction statement as a proposition only.
- `ErdosProblems1066.PachToth.ConditionalUpper` proves the checked chain-to-
  `UDConfig` upper bound from an explicit `KBlockRealization`; it is conditional
  until the geometric realization fields are proved.
- `ErdosProblems1066.PachToth.IndexedChain` fixes the canonical `16 * k`
  indexing and derives the same exact-multiple upper bound from only the
  remaining local-independence and cross-independence soundness fields.
- `ErdosProblems1066.PachToth.ExactLocalGeometry` gives an exact checked
  one-block coordinate realization for the finite Pach--Toth local graph.
- `ErdosProblems1066.PachToth.AffineLocalGeometry` proves translation
  invariance for distances, separation, unit edges, and independent sets.
- `ErdosProblems1066.PachToth.CrossBlockGeometry` checks exact connector-edge
  equations and proves a single pure grid translation cannot realize all four
  cross-block connector edges.
- `ErdosProblems1066.PachToth.ConnectorEquationFacts` packages reusable real
  algebra around the four connector equations and proves inconsistent triples.
- `ErdosProblems1066.PachToth.Figure2Certificate` bundles the currently
  checked local finite graph facts and same/opposite transition obligations
  without claiming a closed non-rigid construction.
- `ErdosProblems1066.PachToth.OrientedCrossBlockGeometry` checks the analogous
  finite family of triangular-grid rotations/reflections and proves a single
  oriented grid copy still cannot realize all connector edges at once.
- `ErdosProblems1066.PachToth.RealTranslationObstruction` proves that even an
  arbitrary real translation of the exact local block cannot realize all four
  connector edges, so the remaining route must be genuinely non-rigid.
- `ErdosProblems1066.PachToth.OneBlockSoundness` reindexes that realization as
  a concrete `UDConfig 16` and proves same-block edge soundness for the local
  finite graph.
- `ErdosProblems1066.PachToth.DeformedPlacement` defines the direct
  non-rigid closed-placement interface, where same-block unit edges, cyclic
  connector unit edges, and global separation are explicit geometric fields
  sufficient for the `5 / 16` block target.
- `ErdosProblems1066.PachToth.DeformedOrientationBridge` routes oriented
  transition certificates into that non-rigid placement interface while keeping
  global separation explicit.
- `ErdosProblems1066.PachToth.ClosedPlacementInterface` names the exact
  coordinate-level certificate needed to construct a closed placement; it does
  not assert the certificate exists.
- `ErdosProblems1066.PachToth.ClosedChainConstruction` repackages honest
  closed-chain/oriented-placement data into the explicit closed-placement
  certificates consumed by the final reductions.
- `ErdosProblems1066.PachToth.ClosedPlacementAlgebra` proves transition
  iteration facts for supplied same/opposite transition data, without claiming
  the transition word or closed placement exists.
- `ErdosProblems1066.PachToth.OrientationData` records the source-backed
  same/opposite transition layer and packages certified oriented transitions
  into the existing placement bridge.
- `ErdosProblems1066.PachToth.PlacementBridge` defines the honest
  closed-chain placement interface that would imply the existing indexed-chain
  realization, keeping global separation and cyclic connector soundness as
  explicit geometric fields.
- `ErdosProblems1066.PachToth.GeometricSoundness` turns explicit local and
  cross-edge soundness hypotheses into an `IndexedChainRealization`.
- `ErdosProblems1066.PachToth.RemainderConstruction` supplies checked
  remainder-size configurations by restricting the existing verified
  `n / 3` construction.
- `ErdosProblems1066.PachToth.SplitSoundness` proves the checked finite
  counting bridge from a canonical exact chain plus remainder realization to
  the arbitrary-`n` `5 / 16` ceiling bound.
- `ErdosProblems1066.PachToth.SplitCertificateBridge` reduces the arbitrary
  split construction to an exact closed chain plus an explicit far-apart
  remainder certificate.
- `ErdosProblems1066.PachToth.RemainderPlacement` constructs the far-apart
  remainder placement for any finite exact chain by translating the checked
  remainder block far enough in the horizontal direction.
- `ErdosProblems1066.PachToth.ClosedChainReduction` packages the final
  Pach--Toth spine as conditional theorems from explicit closed-placement
  certificates; arbitrary remainders are now placed by `RemainderPlacement`.
- `ErdosProblems1066.PachToth.TargetReduction` proves that the proposition
  target follows from indexed chain realizations for all positive block counts.
- `ErdosProblems1066.Swanepoel.Lemma10Bridge` proves the checked finite
  `m = 8` contradiction from explicit Lemma 9/Lemma 10 index hypotheses tied to
  broken-lattice labels.
- `ErdosProblems1066.Swanepoel.Lemma10Inequalities` checks the finite turn
  inequalities that bound the Lemma-10 failure set by one.
- `ErdosProblems1066.Swanepoel.Lemma10Pipeline` packages those turn
  inequalities with the existing Lemma-10 bridge contradiction.
- `ErdosProblems1066.Swanepoel.AngleArithmetic` proves finite turn-window
  arithmetic feeding the Lemma-10 inequality interface.
- `ErdosProblems1066.Swanepoel.BoundaryCounting` proves the integer algebraic
  side of the boundary angle-count and subpolygon low-degree inequalities from
  explicit real angle lower-bound hypotheses.
- `ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge` names the remaining
  Figure 8/Figure 9 analytic hypotheses and transports them into the checked
  Lemma-10 finite contradiction.
- `ErdosProblems1066.Swanepoel.AngleBridgeFacts` proves Euclidean
  distance-to-dot-product bridge facts used by the Figure 8/Figure 9 route.
- `ErdosProblems1066.Swanepoel.AngleGeometry` connects the concrete
  dot-product algebra to mathlib's unoriented angle API, including checked
  `pi / 3` lower bounds for unit sides with separated base.
- `ErdosProblems1066.Swanepoel.Lemma10EuclideanBridge` packages the checked
  distance/dot-product consequences for Figure 8 and Figure 9 and keeps only
  the analytic angle-to-turn lower bounds explicit.
- `ErdosProblems1066.Swanepoel.Lemma10AngleToTurn` converts checked local
  `pi / 3` angle lower bounds into E22/E23 turn-window lower bounds under
  explicit angle-containment hypotheses.
- `ErdosProblems1066.Swanepoel.CommonNeighborGeometry` proves the geometric
  two-circle common-neighbor cap and excludes labelled `K_{2,3}` patterns in
  every separated unit-distance configuration.
- `ErdosProblems1066.Swanepoel.BrokenLatticePipeline` transports label-level
  broken-lattice consequences into the checked finite `m = 8` contradiction.
- `ErdosProblems1066.Swanepoel.MinimalCounterexample` proves the checked
  cleared `8 / 31` deletion arithmetic under explicit closed-neighborhood and
  distance-preservation hypotheses.
- `ErdosProblems1066.Swanepoel.MinimalFailureClosure` proves the well-founded
  closure step from an explicit no-minimal-failure theorem to the Swanepoel
  target proposition.
- `ErdosProblems1066.Swanepoel.CounterexamplePipeline` connects the graph and
  `UDConfig` versions of the cleared independent-set deletion pipeline.
- `ErdosProblems1066.Swanepoel.InducedSubconfiguration` constructs induced
  `UDConfig` subconfigurations from finite vertex sets and proves distance and
  independence transfer.
- `ErdosProblems1066.Swanepoel.DegreeBound` proves the Euclidean unit-distance
  neighbor set of any vertex in a separated configuration has cardinality at
  most six.
- `ErdosProblems1066.Swanepoel.DegreePipeline` feeds that degree bound into the
  deletion/reinsertion pipeline while keeping the remaining reinsertion
  hypotheses explicit.
- `ErdosProblems1066.Swanepoel.FaceReduction` proves canonical unit-distance
  edges are pairwise noncrossing and removes that field from the unit-distance
  face-boundary interface.
- `ErdosProblems1066.Swanepoel.FaceCountingBridge` routes canonical
  face-boundary packages into the existing boundary and subpolygon counting
  theorems.
- `ErdosProblems1066.Swanepoel.OuterBoundaryInterface` records the explicit
  outer-boundary, simple-polygon, enclosure, subpolygon, and angle fields
  needed before those counting theorems can be applied to an arbitrary
  configuration.
- `ErdosProblems1066.Swanepoel.OuterBoundaryReduction` derives
  simple-polygon noncrossing witnesses from supplied canonical boundary cycles,
  removing a redundant field from the boundary-construction route.
- `ErdosProblems1066.Swanepoel.MinimalGraphFacts` adds checked finite-set and
  minimal-counterexample bookkeeping facts for the deletion pipeline.
- `ErdosProblems1066.Swanepoel.NoncrossingUnitEdges` proves the analytic
  obstruction that two disjoint unit edges in a separated configuration cannot
  cross in their relative interiors.
- `ErdosProblems1066.Swanepoel.TriangleAngleFacts` proves reusable squared-
  distance and dot-product facts for unit and equilateral triangles, intended
  for later angle/E22/E23 work.
- `ErdosProblems1066.Swanepoel.PlanarInterface` provides straight-line
  unit-distance graph, noncrossing, and face-boundary interfaces with proved
  distance bridge lemmas.
- `ErdosProblems1066.Swanepoel.GraphBridge` includes both the local graph view
  and a Mathlib `SimpleGraph` view of a `UDConfig`, with checked independence
  equivalence.
- `ErdosProblems1066.Swanepoel.LocalExclusions` adds common-neighbor,
  `K_{2,3}`, and local degree bookkeeping for the graph-theoretic exclusion
  route.
- `ErdosProblems1066.Swanepoel.MinimalFailureLocalExclusions` proves that any
  locally certified degree-deletion pattern is absent from a minimal cleared
  failure, and now packages the unconditional geometric common-neighbor cap for
  unit-distance configurations. It also rebuilds the induced smaller
  configuration automatically from local deleted/reinserted sets.
- `ErdosProblems1066.Swanepoel.LocalDeletionConstructors` packages the next
  closure layer: a global local-deletion eliminator implies no minimal cleared
  failures, the cleared `8 / 31` pipeline, and the Swanepoel target
  proposition.
- `ErdosProblems1066.Swanepoel.TargetReduction` proves that the proposition
  target follows from a cleared `8 / 31` independent set in every configuration.

## Trust Audit

Run:

```powershell
elan run leanprover/lean4:v4.28.0 lake build
rg -n -i -e '\baxiom\b' -e '\bconstant\b' -e '\bsorry\b' -e '\badmit\b' -e 'unsafe' -e 'opaque' -e 'implemented_by' -e '#check' -e '#print' -e '#eval' ErdosProblems1066 --glob '*.lean'
```

`rg` exits with code `1` when there are no matches; that is the clean result.
The source scan is intentionally restricted to Lean files under
`ErdosProblems1066`; docs and CI helper scripts may contain audit commands such
as `#print axioms`.

The CI workflow is the source of truth for the full axiom-audit list. It
auto-counts the `#print axioms` declarations and checks their output with
`.github/scripts/check_lean_axioms.py`. The local block below is a compact
manual sample, not the complete CI list:

```powershell
@'
import ErdosProblems1066
#print axioms ErdosProblems1066.Verified.upper_bound_third
#print axioms ErdosProblems1066.Verified.lower_bound_quarter
#print axioms ErdosProblems1066.PollackPach.lower_bound_quarter
#print axioms ErdosProblems1066.PachToth.ConditionalUpper.independent_card_le_five_mul
#print axioms ErdosProblems1066.PachToth.ConditionalUpper.exists_config_with_independent_card_le_five_mul
#print axioms ErdosProblems1066.PachToth.ConditionalUpper.exists_config_with_independent_card_le_floor_ratio
#print axioms ErdosProblems1066.PachToth.IndexedChain.independent_card_le_five_mul
#print axioms ErdosProblems1066.PachToth.IndexedChain.exists_config_with_independent_card_le_five_mul
#print axioms ErdosProblems1066.PachToth.IndexedChain.exists_config_with_independent_card_le_floor_ratio
#print axioms ErdosProblems1066.PachToth.ExactLocalGeometry.exact_local_realization
#print axioms ErdosProblems1066.PachToth.AffineLocalGeometry.distSq_translate_translate
#print axioms ErdosProblems1066.PachToth.AffineLocalGeometry.UDConfig.isIndep_translate
#print axioms ErdosProblems1066.PachToth.AffineLocalGeometry.translatedLocal_adj_unit_distance
#print axioms ErdosProblems1066.PachToth.AffineLocalGeometry.translatedLocal_root_adj_unit_distance
#print axioms ErdosProblems1066.PachToth.CrossBlockGeometry.no_single_translation_realizes_all_connector_units
#print axioms ErdosProblems1066.PachToth.CrossBlockGeometry.t2ConnectorOffsetA_unit_T1_1
#print axioms ErdosProblems1066.PachToth.OrientedCrossBlockGeometry.no_oriented_grid_placement_realizes_all_connector_units
#print axioms ErdosProblems1066.PachToth.OrientedCrossBlockGeometry.orientedLocal_adj_unit_distance
#print axioms ErdosProblems1066.PachToth.OneBlockSoundness.oneBlock_separated
#print axioms ErdosProblems1066.PachToth.OneBlockSoundness.oneBlock_adj_unit_distance
#print axioms ErdosProblems1066.PachToth.OneBlockSoundness.oneBlock_local_adj_unit_distance
#print axioms ErdosProblems1066.PachToth.DeformedPlacement.ClosedPlacement.toExplicitEdgeSoundness
#print axioms ErdosProblems1066.PachToth.DeformedPlacement.ClosedPlacement.toIndexedChainRealization
#print axioms ErdosProblems1066.PachToth.DeformedPlacement.targetUpperConstructionFiveSixteen_of_deformedPlacements
#print axioms ErdosProblems1066.PachToth.OrientationData.TransitionCertificate.connector_unit_target
#print axioms ErdosProblems1066.PachToth.OrientationData.OrientedClosedChainPlacement.toIndexedChainRealization
#print axioms ErdosProblems1066.PachToth.PlacementBridge.ClosedChainPlacement.toExplicitEdgeSoundness
#print axioms ErdosProblems1066.PachToth.PlacementBridge.TranslatedClosedChainPlacement.toIndexedChainRealization
#print axioms ErdosProblems1066.PachToth.Remainder.independent_card_le_of_split
#print axioms ErdosProblems1066.PachToth.RemainderConstruction.exists_remainder_config
#print axioms ErdosProblems1066.PachToth.RemainderConstruction.exists_remainder_config_mod_sixteen
#print axioms ErdosProblems1066.PachToth.GeometricSoundness.mem_blockSelection_iff
#print axioms ErdosProblems1066.PachToth.GeometricSoundness.globalVertex_ne_of_local_ne
#print axioms ErdosProblems1066.PachToth.GeometricSoundness.nextConnector_ne
#print axioms ErdosProblems1066.PachToth.GeometricSoundness.ExplicitEdgeSoundness.blocks_independent_of_independent
#print axioms ErdosProblems1066.PachToth.GeometricSoundness.ExplicitEdgeSoundness.cross_independent_of_independent
#print axioms ErdosProblems1066.PachToth.GeometricSoundness.ExplicitEdgeSoundness.toIndexedChainRealization
#print axioms ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen_of_indexedChainRealizations
#print axioms ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen_of_explicitEdgeSoundness
#print axioms ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenAt_of_explicitSplitConstruction
#print axioms ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary_of_explicitSplitConstructions
#print axioms ErdosProblems1066.PachToth.SplitSoundness.independent_card_le_five_sixteen
#print axioms ErdosProblems1066.PachToth.SplitSoundness.targetUpperConstructionFiveSixteenAt_of_canonicalSplitRealization
#print axioms ErdosProblems1066.Swanepoel.Lemma10Bridge.contradiction_of_atMostOneFailure_and_lateTriples
#print axioms ErdosProblems1066.Swanepoel.Lemma10Bridge.M8HonestLocalPredicates.contradiction
#print axioms ErdosProblems1066.Swanepoel.Lemma10Inequalities.failureSet_card_le_one_of_turn_hypotheses
#print axioms ErdosProblems1066.Swanepoel.Lemma10Inequalities.card_le_one_failures_of_turn_hypotheses
#print axioms ErdosProblems1066.Swanepoel.Lemma10Pipeline.contradiction_of_turn_hypotheses
#print axioms ErdosProblems1066.Swanepoel.Lemma10Pipeline.honestContradiction_of_turn_hypotheses
#print axioms ErdosProblems1066.Swanepoel.AngleArithmetic.card_le_one_failures_of_window_lowers
#print axioms ErdosProblems1066.Swanepoel.AngleArithmetic.separated_failures_impossible_of_weightedTurn
#print axioms ErdosProblems1066.Swanepoel.BoundaryCounting.BoundaryCounts.boundary_angle_count_inequality
#print axioms ErdosProblems1066.Swanepoel.BoundaryCounting.SubpolygonDegreeCounts.subpolygon_low_degree_inequality
#print axioms ErdosProblems1066.Swanepoel.Lemma10AnalyticBridge.honestContradiction_of_E22_E23
#print axioms ErdosProblems1066.Swanepoel.BrokenLatticePipeline.M8HonestLocalPredicates.contradiction_of_labelFailures_and_labelLateTriples
#print axioms ErdosProblems1066.Swanepoel.CounterexamplePipeline.DeletionReinsertionData.hasCleared_of_deletionReinsertion
#print axioms ErdosProblems1066.Swanepoel.CounterexamplePipeline.DeletionReinsertionData.hasCleared_of_deletionReinsertion_graphSmall
#print axioms ErdosProblems1066.Swanepoel.CounterexamplePipeline.DeletionReinsertionData.graphHasCleared_of_deletionReinsertion
#print axioms ErdosProblems1066.Swanepoel.CounterexamplePipeline.e1_pipeline_of_explicit_deletion
#print axioms ErdosProblems1066.Swanepoel.CounterexamplePipeline.e5_pipeline_of_explicit_deletion_graphSmall
#print axioms ErdosProblems1066.Swanepoel.DegreeBound.UDConfig.unitDistanceNeighborSet_card_le_six
#print axioms ErdosProblems1066.Swanepoel.DegreePipeline.closedUnitNeighborhood_card_le_seven
#print axioms ErdosProblems1066.Swanepoel.DegreePipeline.e1_pipeline_of_degree_deletion
#print axioms ErdosProblems1066.Swanepoel.FaceReduction.unitDistanceEdges_pairwiseNoncrossing
#print axioms ErdosProblems1066.Swanepoel.FaceReduction.UnitDistanceFaceBoundaryHypotheses.toFaceBoundaryHypotheses
#print axioms ErdosProblems1066.Swanepoel.PlanarInterface.StraightLineUnitDistanceGraph.adj_geometry_dist_eq_one
#print axioms ErdosProblems1066.Swanepoel.PlanarInterface.FaceBoundaryHypotheses.boundary_edge_root_dist_eq_one
#print axioms ErdosProblems1066.Swanepoel.MinimalGraphFacts.exists_smallerBound_data_of_minimalFailure_and_two_le_reinsertion
#print axioms ErdosProblems1066.Swanepoel.NoncrossingUnitEdges.separated_unit_edges_not_cross
#print axioms ErdosProblems1066.Swanepoel.NoncrossingUnitEdges.unitDistanceEdges_not_cross
#print axioms ErdosProblems1066.Swanepoel.TriangleAngleFacts.dotAt_eq_half_of_equilateral_unit
#print axioms ErdosProblems1066.Swanepoel.TriangleAngleFacts.one_le_sqDist_of_unit_sides_dotAt_le_half
#print axioms ErdosProblems1066.Swanepoel.TriangleAngleFacts.dotAt_origin_of_concrete_equilateral
#print axioms ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_clearedBound
#print axioms ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne_of_pipelineCleared
'@ | elan run leanprover/lean4:v4.28.0 lake env lean --stdin
```

The expected dependencies for the current public and checked conditional bridge
theorems remain Lean/mathlib foundations only: `propext`, `Classical.choice`,
and `Quot.sound`; the complete checked declaration set is maintained in
`.github/workflows/lean_action_ci.yml`. The target proposition names
`ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne` and
`ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen` are definitions,
not verified theorem claims.
