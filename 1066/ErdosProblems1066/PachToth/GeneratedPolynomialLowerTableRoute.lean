import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts
import ErdosProblems1066.PachToth.CrossBlockSqTableSearch

set_option autoImplicit false

/-!
# Generated-polynomial lower-table route

This module packages the final non-connector metric obligations in the
generated-point polynomial spelling.  It introduces no numeric data: callers
provide exactly the upper-triangle, non-connector inequalities that a finite
search has to prove, and the route converts those inequalities to the
downstream non-connector square-distance table family and cross-block
lower-bound facade.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedPolynomialLowerTableRoute

open CrossBlockLowerBoundsInterface

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockSqTableSearch.IndexedCyclicConnectorPair hk i u j v

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  CrossBlockSqTableSearch.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  CrossBlockSqTableSearch.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds

/-- The generated-point polynomial attached to finite local indices.

This is definitionally the same polynomial as
`CrossBlockSqTableSearch.indexedGeneratedSqPolynomial`, but it exposes the
generated-point expression from `GeneratedPointDistanceFacts` as the
certificate-facing target. -/
def indexedGeneratedPointSqPolynomial
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  GeneratedPointDistanceFacts.generatedPointSqPolynomial
    F.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase (F.orientation k hk)
    i (localVertexOfIndex u) j (localVertexOfIndex v)

@[simp]
theorem indexedGeneratedSqPolynomial_eq_generatedPoint
    (F : RoleHingedPeriodSearchFamily)
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    CrossBlockSqTableSearch.indexedGeneratedSqPolynomial F hk i u j v =
      indexedGeneratedPointSqPolynomial F hk i u j v := by
  rfl

/-- The exact search-facing inequality table for one block count: only
strict upper-triangle block pairs that are not cyclic connector pairs must be
certified, and the certified expression is the generated-point coordinate
polynomial. -/
structure GeneratedPointNonConnectorPolynomialTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  polynomial_ge_one_lt :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= indexedGeneratedPointSqPolynomial F hk i u j v

namespace GeneratedPointNonConnectorPolynomialTable

/-- Reinterpret generated-point polynomial facts as the native
`CrossBlockSqTableSearch` upper-triangle non-connector polynomial table. -/
def toUpperTriangleNonConnectorPolynomialTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : GeneratedPointNonConnectorPolynomialTable F k hk) :
    CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTable F k hk
    where
  polynomial_ge_one_lt := by
    intro i u j v hlt hnot_connector
    simpa using T.polynomial_ge_one_lt i u j v hlt hnot_connector

/-- Generated-point polynomial inequalities give the finite
non-connector square-distance table expected by the connector-separated
route. -/
def toNonConnectorSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : GeneratedPointNonConnectorPolynomialTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk :=
  T.toUpperTriangleNonConnectorPolynomialTable.toNonConnectorSqDistanceTable

/-- The one-period generated global separation obtained from the packaged
generated-point polynomial inequalities. -/
theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : GeneratedPointNonConnectorPolynomialTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toNonConnectorSqDistanceTable.generatedGlobalSeparation

end GeneratedPointNonConnectorPolynomialTable

/-- A family of generated-point polynomial lower tables, one for each
positive block count. -/
structure GeneratedPointNonConnectorPolynomialTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      GeneratedPointNonConnectorPolynomialTable F k hk

namespace GeneratedPointNonConnectorPolynomialTableFamily

/-- Convert the generated-point polynomial family to the native
non-connector square-distance table family. -/
def toNonConnectorSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedPointNonConnectorPolynomialTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk => (T.table k hk).toNonConnectorSqDistanceTable

/-- Convert the generated-point polynomial family to the downstream
cross-block lower-bound facade. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedPointNonConnectorPolynomialTableFamily F) :
    CrossBlockLowerBounds F :=
  T.toNonConnectorSqDistanceTableFamily.toCrossBlockLowerBounds

/-- The finite family gives generated separation at every positive block
count. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedPointNonConnectorPolynomialTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toNonConnectorSqDistanceTableFamily.separated k hk

/-- Exact Pach--Toth target from period-search data plus generated-point
non-connector polynomial inequalities. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedPointNonConnectorPolynomialTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toNonConnectorSqDistanceTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target obtained after projecting the
generated-point polynomial inequalities to `CrossBlockLowerBounds`. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : GeneratedPointNonConnectorPolynomialTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end GeneratedPointNonConnectorPolynomialTableFamily

/-- Build the route directly from the raw generated-point polynomial
inequality family. -/
def tableFamilyOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <= indexedGeneratedPointSqPolynomial F hk i u j v) :
    GeneratedPointNonConnectorPolynomialTableFamily F where
  table := fun k hk =>
    { polynomial_ge_one_lt := polynomial_ge_one_lt k hk }

/-- Direct route from generated-point polynomial inequalities to the
non-connector square-distance table family. -/
def nonConnectorSqDistanceTableFamilyOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <= indexedGeneratedPointSqPolynomial F hk i u j v) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  (tableFamilyOfGeneratedPointPolynomialFacts
    F polynomial_ge_one_lt).toNonConnectorSqDistanceTableFamily

/-- Direct route from generated-point polynomial inequalities to
`CrossBlockLowerBounds`. -/
def crossBlockLowerBoundsOfGeneratedPointPolynomialFacts
    (F : RoleHingedPeriodSearchFamily)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <= indexedGeneratedPointSqPolynomial F hk i u j v) :
    CrossBlockLowerBounds F :=
  (tableFamilyOfGeneratedPointPolynomialFacts
    F polynomial_ge_one_lt).toCrossBlockLowerBounds

end

end GeneratedPolynomialLowerTableRoute
end PachToth
end ErdosProblems1066
