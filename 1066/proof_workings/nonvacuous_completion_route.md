# Non-vacuous completion route after the translated connector obstruction

This note records the intended handoff after the translated
connector-equation obstruction.  It is a proof-working note only.  It does not
claim that either the Pach--Toth `5 / 16` construction or the Swanepoel
`8 / 31` lower bound has been completed unconditionally.

The common point is that a conditional endpoint is useful only when its
remaining hypothesis has an honest geometric source.  A route that proves the
remaining hypothesis from contradictory translated data is vacuous and must not
be counted as progress toward the paper theorem.

## 1. The obstruction that must be respected

For Pach--Toth, the translated-copy shortcut is now explicitly blocked.

The relevant checked files are:

- `ErdosProblems1066/PachToth/RealTranslationObstruction.lean`;
- `ErdosProblems1066/PachToth/ConnectorEquationConcrete.lean`;
- `ErdosProblems1066/PachToth/ConnectorEquationClosure.lean`;
- `ErdosProblems1066/PachToth/EquationTransitionClosure.lean`;
- `ErdosProblems1066/PachToth/FinalConditional.lean`.

`RealTranslationObstruction.no_real_offset_connector_equations` proves that the
four real equations

- `eq211`;
- `eq212`;
- `eq400`;
- `eq402`;

are inconsistent for one arbitrary real translation of the exact local block.
The geometric form is
`no_real_translation_realizes_all_connector_units`: no single translated copy
of the next exact block realizes all four proof-used connector unit edges.
The closed-chain specialization
`no_translated_closed_chain_placement` rules out the corresponding translated
closed-placement shortcut.

`ConnectorEquationConcrete` goes further: the raw structure
`ConnectorEquationTransitionFacts`, and hence the same/opposite structure built
from it, is contradictory when it asks for all four translated exact-block
equations at the exact height.  In particular,
`false_of_equationTransitionData` and
`false_of_sameOppositeEquationTransitionData` show that the existing
`ConnectorEquationClosure.EquationTransition` package is uninhabited in this
translated exact-block interpretation.

Therefore the following is not an acceptable completion route:

1. Supply a `ConnectorEquationClosure.SameOppositeEquationTransition`.
2. Use the connector-equation closure to obtain the final conditional
   Pach--Toth target.
3. Treat that as an honest construction.

That route would be vacuous unless the transition interface has first been
replaced by a non-translated/deformed source of connector unit edges.

## 2. Pach--Toth: non-vacuous route

The viable Pach--Toth route should target deformed or role-hinged transition
data, not full translated connector-equation data.

The non-vacuous target shape is:

1. Keep the checked exact one-block geometry:
   `BaseTransitionRealization.exactBase` and its same-block isometry facts.
2. Replace the impossible translated four-equation transition with honest
   same/opposite transition maps whose connector unit edges are proved from
   their own deformed construction data.
3. Prove same-block distance preservation for those same/opposite transition
   maps.
4. For each positive block count `k`, supply an orientation word and an indexed
   algebraic period certificate for the resulting generated chain.
5. For each positive `k`, supply cross-block lower bounds and prove both:
   all lower entries are at least `1`, and the generated Euclidean distances
   dominate those lower entries.
6. Route this data through the existing generated-chain closure to the exact
   `16 * k` construction, and then through the checked arbitrary-`n` remainder
   route.

The current Lean modules already contain useful non-vacuous-shaped interfaces:

- `ConcretePeriodSearchFamily.PeriodSearchData` stores finite orientation
  words and pointwise algebraic period equations.
- `ConcretePeriodSearchFamily.ConcreteCrossBlockFamily` adds the cross-block
  lower-bound table and inequalities.
- `CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily` and the
  associated lower-bound interface are the better downstream shape for a
  role-hinged construction, because they do not require the contradictory
  translated four-equation package.

The intended next Pach--Toth Lean work is therefore not to instantiate
`FinalConditional.EquationPeriodSearchCrossBlockFamily` using
`ConnectorEquationClosure.SameOppositeEquationTransition`.  That family is now
best understood as an audited closure around an impossible translated model.
Instead, the route should either:

- move the final facade to the role-hinged/deformed transition interfaces
  already used by `ConcretePeriodSearchFamily`, or
- introduce a new final conditional family whose transition field is an honest
  deformed metric obligation package, with connector unit edges and
  same-block preservation supplied directly.

Only after that replacement should period-search certificates and cross-block
tables be attached.  At that point the completion is non-vacuous: each field
has a concrete geometric or finite-search meaning, and no field is known to
imply `False` before it reaches the target theorem.

## 3. Swanepoel: non-vacuous route

Swanepoel is not blocked by the Pach--Toth translated connector equations, but
the same anti-vacuity rule applies.  The checked Swanepoel endpoint is a
conditional minimal-failure eliminator:

- `FinalConditional.MinimalFailureM8SeparatedConstructionEliminator`;
- `M8MinimalFailureEliminatorInterface.M8MinimalFailureEliminator`;
- `M8SeparatedConstructionConcrete.M8SeparatedConstructionComponents`.

For one minimal cleared failure, the required non-vacuous package is the
actual separated `m = 8` construction data:

- honest local labels/predicates;
- nonnegative turn values with total turn `< pi / 3`;
- Figure 8 separated-window geometry;
- Figure 9 adjacent-left window geometry;
- late-triples data.

`M8SeparatedConstructionConcrete` gives the clean component-level source:

- `M8LabelsFromBoundaryData C`;
- `NonconcaveArcTurnData`;
- `M8ConstructionNoEarlyTriples labels.toM8LocalLabels`;
- `M8WindowContainment labels.toM8LocalLabels arc.toM8TurnBounds`.

These assemble into
`M8PipelineClosure.M8SeparatedConstructionFields C hmin`, and the checked
pipeline then gives a contradiction for that fixed minimal failure.  Uniformly
supplying such a component package for every minimal cleared failure gives
`targetLowerBoundEightThirtyOne` through the existing minimal-failure closure.

The non-vacuous Swanepoel completion route is therefore:

1. From an arbitrary minimal cleared failure, construct the boundary and
   Lemma 8 label data used by `M8LabelsFromBoundaryData`.
2. Construct the nonconcave arc and its turn function, including
   nonnegativity and the strict total-turn bound.
3. Prove the Lemma 9/no-early-triples input for those labels.
4. Prove the Figure 8/Figure 9 angle-window containment facts for the same
   labels and turns.
5. Assemble those four components with
   `M8SeparatedConstructionComponentPackage.toM8SeparatedConstructionFields`.
6. Apply the existing `M8PipelineClosure` contradiction and then
   `MinimalFailureClosure`.

This route is non-vacuous because the component package is not obtained by
assuming the final contradiction.  It is meant to be built from the geometry of
an arbitrary minimal cleared failure.  The remaining burden is exactly the
paper-facing construction work: boundary extraction, Lemma 8 labels, the
nonconcave-arc turn budget, Lemma 9 late triples, and window containment.

## 4. Practical guardrails

- Do not use the translated exact-block connector equations as a Pach--Toth
  construction source.  They are now checked inconsistent.
- Do not expose conditional Pach--Toth or Swanepoel endpoints through
  `KnownBounds` until their remaining packages have honest source data.
- For Pach--Toth, prefer deformed/role-hinged transition interfaces over
  `ConnectorEquationClosure` for any future final facade.
- For Swanepoel, keep the completion target at the component level.  The
  useful object to construct is
  `M8SeparatedConstructionComponents`, not a theorem-shaped black box.
- Any future note or Lean wrapper should state whether its input package is
  known inhabited, merely conditional, or known contradictory.

## 5. Current status

Pach--Toth: the translated connector-equation route is obstructed.  A
non-vacuous completion must replace that route with deformed/role-hinged
transition data, then add period-search and cross-block lower-bound
certificates.

Swanepoel: the checked closure from explicit separated `m = 8` components to
the target proposition is available conditionally.  A non-vacuous completion
must construct those components uniformly from arbitrary minimal cleared
failures.

Neither status is a final proof completion.
