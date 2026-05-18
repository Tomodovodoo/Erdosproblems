# Current conditional spines

This note records the exact conditional proof spines currently present in the
Lean modules for Swanepoel and Pach--Toth.  It is a proof-working handoff, not
a claim that either final paper theorem has been completed unconditionally.

The two public target names below are propositions internal to their
namespaces.  The conditional wrappers in the final modules are deliberately
not exposed through `KnownBounds`.

## Swanepoel conditional spine

Source modules:

- `ErdosProblems1066/Swanepoel/FinalConditional.lean`
- `ErdosProblems1066/Swanepoel/M8PipelineClosure.lean`
- `ErdosProblems1066/Swanepoel/BrokenLatticeMinimalFailure.lean`
- `ErdosProblems1066/Swanepoel/MinimalFailureClosure.lean`
- `ErdosProblems1066/Swanepoel/Lemma10WindowGeometry.lean`

Target proposition:

- `ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne`.

Exact remaining top-level hypothesis:

```lean
Swanepoel.FinalConditional.MinimalFailureM8SeparatedConstructionEliminator
```

Unfolded, this is the uniform assertion that for every `n`, every unit-distance
configuration `C : UDConfig n`, and every proof
`hmin : IsMinimalClearedFailure C`, there is a nonempty package

```lean
M8PipelineClosure.M8SeparatedConstructionFields C hmin
```

For one minimal cleared failure, that package consists of:

- `predicates : M8HonestLocalPredicates (unitDistanceLocalGraph C)`;
- `turn : Nat -> Real`;
- `turnBounds`, namely nonnegativity of every turn and
  `totalTurn turn < Real.pi / 3`;
- `windowGeometry`, namely honest Figure 8 separated-window geometry and
  honest Figure 9 adjacent-left window geometry for those predicates and
  turns;
- `lateTriples`, namely the late-triples field for the same honest predicates.

Lamport-style checked route:

S1. Assume `hbuild :
MinimalFailureM8SeparatedConstructionEliminator`.

S2. Fix any minimal cleared failure `C` with proof `hmin`.  By S1 choose
`D : M8SeparatedConstructionFields C hmin`.

S3. From `D.windowGeometry`, the checked lemmas in
`Lemma10WindowGeometry.lean` derive the E22 and E23 lower-bound fields:
`HonestFigure8SeparatedWindowLowerE22 D.predicates D.turn` and
`HonestFigure9AdjacentWindowLowerE23 D.predicates D.turn`.

S4. `M8PipelineClosure.M8SeparatedConstructionFields.toConstructionData`
repackages `D` as
`BrokenLatticeMinimalFailure.M8ConstructionData C hmin`.

S5. `BrokenLatticeMinimalFailure.M8ConstructionData.contradiction` sends that
construction data through the existing broken-lattice interface and proves
`False`.

S6. Therefore
`M8PipelineClosure.no_minimalClearedFailure_of_separatedConstructionEliminator`
proves that no minimal cleared failure exists.

S7. `MinimalFailureClosure.targetLowerBoundEightThirtyOne_of_no_minimalClearedFailure`
turns the absence of minimal cleared failures into
`Swanepoel.targetLowerBoundEightThirtyOne`.

S8. `Swanepoel.FinalConditional.targetLowerBoundEightThirtyOne` is exactly S1
through S7 packaged as the current conditional theorem.

What remains open for an unconditional Swanepoel result:

- Construct the uniform `M8SeparatedConstructionFields` package for every
  minimal cleared failure.
- In particular, construct the honest local predicates, the turn function, the
  turn-budget proof, the Figure 8/Figure 9 window witnesses and containment
  facts, and the late-triples field from an arbitrary minimal cleared failure.
- This file does not claim that Lemmas 6, 8, or 9 from the paper have been
  fully transcribed as unconditional geometric/combinatorial constructions.

## Pach--Toth conditional spine

Source modules:

- `ErdosProblems1066/PachToth/FinalConditional.lean`
- `ErdosProblems1066/PachToth/ConnectorEquationClosure.lean`
- `ErdosProblems1066/PachToth/PeriodSearchInterface.lean`
- `ErdosProblems1066/PachToth/GeneratedSeparationFarApart.lean`
- `ErdosProblems1066/PachToth/GeneratedPeriodClosure.lean`
- `ErdosProblems1066/PachToth/ExactFamilyClosure.lean`

Target propositions:

- `ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteen`, for exact
  multiples of the 16-vertex block.
- `ErdosProblems1066.PachToth.targetUpperConstructionFiveSixteenArbitrary`,
  for arbitrary `n`, using the checked small cases below 16.

Exact remaining top-level hypothesis for the final conditional family:

```lean
PachToth.FinalConditional.EquationPeriodSearchCrossBlockFamily
```

Unfolded, this is one family package with the following fields:

- `transitions :
  ConnectorEquationClosure.SameOppositeEquationTransition`;
- `orientation : forall k, 0 < k -> Fin k ->
  OrientationData.BlockOrientation`;
- `period : forall k hk,
  PeriodSearchInterface.IndexedAlgebraicPeriodCertificate ...`, for the
  finite orientation word of length `k`;
- `lower : forall k hk, Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real`;
- `lower_ge_one : forall k hk,
  GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
  (lower k hk)`;
- `lower_bound : forall k hk,
  GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds ...`.

The transition field itself is still structured data.  A
`SameOppositeEquationTransition` contains same and opposite
`EquationTransition`s.  Each `EquationTransition` supplies:

- an offset in `Prod Real Real`;
- the four connector equations `eq211`, `eq212`, `eq400`, and `eq402` at that
  offset;
- a proof that the resulting carried transition preserves same-block
  distances.

The connector unit-edge obligations are checked consequences of the four
explicit connector equations.  The same-block preservation proofs are not
derived by `ConnectorEquationClosure`; they remain fields of the transition
data.

Lamport-style checked route:

P1. Assume `F : EquationPeriodSearchCrossBlockFamily`.

P2. The same/opposite equation transitions in `F.transitions` forget to the
generated-chain Figure 2 transition interface via
`toFigure2TransitionObligations`.

P3. `FinalConditional.equationTransitions_preserveSameBlockDistances` converts
the same-block preservation fields of the same and opposite equation
transitions into
`GeneratedTransitionsPreserveSameBlockDistances` for that Figure 2 interface.

P4. For each positive block count `k`, `F.period k hk` is an indexed finite
algebraic period certificate.  Through `PeriodSearchInterface`, this gives the
generated period equation used downstream.

P5. For the same `k`, `F.lower_ge_one k hk` and `F.lower_bound k hk` give
explicit quantitative cross-block separation.  Together with the checked base
same-block isometry of `BaseTransitionRealization.exactBase` and P3,
`GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced`
gives generated global separation.

P6. P4 and P5 form the reduced generated metric package in
`EquationPeriodSearchCrossBlockFamily.reducedMetricHypotheses`.

P7. `GeneratedPeriodClosure.targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced`
proves `targetUpperConstructionFiveSixteenAt (16 * k)` for each positive `k`.

P8. Varying `k`, `GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock`
proves the exact-multiple target
`PachToth.targetUpperConstructionFiveSixteen`.

P9. `ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget`
combines the exact-multiple target with the checked small cases below 16 and
the translated remainder construction, yielding
`PachToth.targetUpperConstructionFiveSixteenArbitrary`.

P10. `PachToth.FinalConditional.exactTarget_of_periodSearch_equationTransitions_crossBlock`
is P1 through P8 packaged as the current exact-multiple conditional theorem.
`PachToth.FinalConditional.arbitraryTarget_of_periodSearch_equationTransitions_crossBlock`
is P1 through P9 packaged as the current arbitrary-`n` conditional theorem.

What remains open for an unconditional Pach--Toth result:

- Supply concrete same and opposite equation transitions, including offsets
  satisfying `eq211`, `eq212`, `eq400`, and `eq402`.
- Prove same-block distance preservation for those same and opposite carried
  transition maps.
- For every positive block count `k`, supply an orientation word and a finite
  indexed algebraic period certificate for that word.
- For every positive `k`, supply the cross-block lower-bound table and prove
  both `lower_ge_one` and the generated cross-block distance lower-bound
  inequalities.
- No module in this spine asserts that the period search, transition data, or
  cross-block tables already exist.

## Trust status

The spines above are conditional Lean closures extracted from the existing
modules.  They intentionally keep the remaining geometric, finite-search, and
quantitative certificate obligations explicit.  They do not assert final
unconditional completion of Swanepoel's `8 / 31` bound or Pach--Toth's
`5 / 16` construction.
