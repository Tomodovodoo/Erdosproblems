import ErdosProblems1066.PachToth.ConcretePeriodSearchFamily
import ErdosProblems1066.PachToth.CrossBlockSqTableSearch

set_option autoImplicit false

/-!
# Concrete finite indexed cross-block tables

This module is the concrete wrapper for finite-index cross-block lower tables.
The only remaining numerical obligations are the finite inequalities stored in
`IndexedCrossBlockLowerTable`: entries on distinct blocks are at least one, and
each entry is bounded above by the corresponding generated distance.
-/

namespace ErdosProblems1066
namespace PachToth
namespace IndexedCrossBlockTableConcrete

open CrossBlockLowerBoundsInterface
open ConcretePeriodSearchFamily
open FiniteGraph

noncomputable section

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev IndexedCrossBlockLowerTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTable F k hk

abbrev IndexedCrossBlockLowerTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.IndexedCrossBlockLowerTableFamily F

abbrev CrossBlockLowerBounds
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CrossBlockSqTableSearch.IndexedCyclicConnectorPair hk i u j v

abbrev IndexedNonConnectorCrossBlockSqDistanceTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable
    F k hk

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily F

abbrev UpperTriangleNonConnectorPolynomialTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTable F k hk

abbrev UpperTriangleNonConnectorPolynomialTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorPolynomialTableFamily F

abbrev UpperTriangleNonConnectorSqValueTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTable F k hk

abbrev UpperTriangleNonConnectorSqValueTableFamily
    (F : RoleHingedPeriodSearchFamily) :=
  CrossBlockSqTableSearch.UpperTriangleNonConnectorSqValueTableFamily F

namespace IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete

/-- Expand reduced non-connector square-distance tables to the indexed
cross-block lower-table family by filling connector slots with the checked
connector-unit value. -/
def toIndexedCrossBlockLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    IndexedCrossBlockLowerTableFamily F :=
  T.toCrossBlockLowerTableFamily

@[simp]
theorem toIndexedCrossBlockLowerTableFamily_table
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    ((toIndexedCrossBlockLowerTableFamily T).table k hk) =
      (T.table k hk).toCrossBlockLowerTable :=
  rfl

/-- Reduced non-connector square-distance tables as the downstream
cross-block lower-bound facade. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    CrossBlockLowerBounds F :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.ofIndexedTables
    T.toCrossBlockLowerTableFamily

@[simp]
theorem toCrossBlockLowerBounds_lower
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    (toCrossBlockLowerBounds T).lower k hk =
      (toIndexedCrossBlockLowerTableFamily T).lower k hk :=
  rfl

/-- The `>= 1` finite inequalities project through the reduced
non-connector facade. -/
theorem toCrossBlockLowerBounds_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((toCrossBlockLowerBounds T).lower k hk) :=
  (toCrossBlockLowerBounds T).toLowerBoundsAtLeastOne k hk

/-- The finite metric inequalities project through the reduced
non-connector facade. -/
theorem toCrossBlockLowerBounds_bound
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      ((toCrossBlockLowerBounds T).lower k hk) :=
  (toCrossBlockLowerBounds T).toDistanceLowerBounds k hk

/-- The reduced `>= 1` projection is exactly the expanded table-family
projection. -/
theorem toCrossBlockLowerBounds_ge_one_eq
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    (toCrossBlockLowerBounds T).toLowerBoundsAtLeastOne k hk =
      (toIndexedCrossBlockLowerTableFamily T).lower_ge_one k hk :=
  rfl

/-- The reduced metric projection is exactly the expanded table-family
projection. -/
theorem toCrossBlockLowerBounds_bound_eq
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    (toCrossBlockLowerBounds T).toDistanceLowerBounds k hk =
      (toIndexedCrossBlockLowerTableFamily T).lower_bound k hk :=
  rfl

/-- Generated global separation supplied by reduced non-connector
square-distance tables and the checked connector facts. -/
def separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (toCrossBlockLowerBounds T).separated k hk

/-- The reduced separation wrapper reduces to the expanded one-table
separation projection. -/
theorem separated_eq_table
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    separated T k hk =
      ((toIndexedCrossBlockLowerTableFamily T).table k hk).generatedGlobalSeparation :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.separated_ofIndexedTables
    (toIndexedCrossBlockLowerTableFamily T) k hk

/-- Exact-multiple target obtained from reduced non-connector
square-distance tables. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (toCrossBlockLowerBounds T).targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target obtained from reduced non-connector square-distance
tables and the checked small cases imported downstream. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (toCrossBlockLowerBounds T).targetUpperConstructionFiveSixteenArbitrary

end IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete

/-- Build the reduced non-connector square-distance table family directly
from explicit finite square-distance checks. -/
def indexedNonConnectorCrossBlockSqDistanceTableFamilyOfFacts
    {F : RoleHingedPeriodSearchFamily}
    (sqDist_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          Ne i j ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                  F hk i u j v) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    { sqDist_ge_one := fun i u j v hij hnot_connector =>
        sqDist_ge_one k hk i u j v hij hnot_connector }

/-- Explicit non-connector square-distance checks, expanded to concrete
indexed cross-block lower tables. -/
def indexedCrossBlockLowerTableFamilyOfNonConnectorSqDistanceFacts
    {F : RoleHingedPeriodSearchFamily}
    (sqDist_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          Ne i j ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                  F hk i u j v) :
    IndexedCrossBlockLowerTableFamily F :=
  IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete.toIndexedCrossBlockLowerTableFamily
    (indexedNonConnectorCrossBlockSqDistanceTableFamilyOfFacts
      sqDist_ge_one)

/-- Package upper-triangle non-connector polynomial facts as the table family
consumed by the connector-separated square-distance route. -/
def upperTriangleNonConnectorPolynomialTableFamilyOfFacts
    {F : RoleHingedPeriodSearchFamily}
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  F hk i u j v) :
    UpperTriangleNonConnectorPolynomialTableFamily F where
  table := fun k hk =>
    { polynomial_ge_one_lt := fun i u j v hlt hnot_connector =>
        polynomial_ge_one_lt k hk i u j v hlt hnot_connector }

/-- Existing upper-triangle non-connector polynomial facts, expanded to the
finite non-connector square-distance table family. -/
def indexedNonConnectorCrossBlockSqDistanceTableFamilyOfPolynomialFacts
    {F : RoleHingedPeriodSearchFamily}
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  F hk i u j v) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F :=
  (upperTriangleNonConnectorPolynomialTableFamilyOfFacts
    polynomial_ge_one_lt).toNonConnectorSqDistanceTableFamily

/-- Existing upper-triangle non-connector polynomial facts, expanded all the
way to concrete indexed cross-block lower tables. -/
def indexedCrossBlockLowerTableFamilyOfNonConnectorPolynomialFacts
    {F : RoleHingedPeriodSearchFamily}
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  F hk i u j v) :
    IndexedCrossBlockLowerTableFamily F :=
  IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete.toIndexedCrossBlockLowerTableFamily
    (indexedNonConnectorCrossBlockSqDistanceTableFamilyOfPolynomialFacts
      polynomial_ge_one_lt)


namespace IndexedCrossBlockLowerTableFamily

/-- Forget a finite-index table family to the lower-bound facade used by the
generated-family closure route. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    CrossBlockLowerBounds F :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.ofIndexedTables T

@[simp]
theorem toCrossBlockLowerBounds_lower
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    (T.toCrossBlockLowerBounds).lower k hk = T.lower k hk :=
  rfl

/-- The `>= 1` finite inequalities project through the concrete facade. -/
theorem toCrossBlockLowerBounds_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((T.toCrossBlockLowerBounds).lower k hk) :=
  (T.toCrossBlockLowerBounds).toLowerBoundsAtLeastOne k hk

/-- The finite metric inequalities project through the concrete facade. -/
theorem toCrossBlockLowerBounds_bound
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      ((T.toCrossBlockLowerBounds).lower k hk) :=
  (T.toCrossBlockLowerBounds).toDistanceLowerBounds k hk

/-- The projected `>= 1` facade is exactly the table-family projection. -/
theorem toCrossBlockLowerBounds_ge_one_eq
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    T.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk =
      T.lower_ge_one k hk :=
  rfl

/-- The projected metric facade is exactly the table-family projection. -/
theorem toCrossBlockLowerBounds_bound_eq
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    T.toCrossBlockLowerBounds.toDistanceLowerBounds k hk =
      T.lower_bound k hk :=
  rfl

/-- Generated global separation supplied by the finite indexed tables. -/
def separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toCrossBlockLowerBounds.separated k hk

/-- The separation wrapper reduces to the one-table generated separation
projection. -/
theorem separated_eq_table
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F)
    (k : Nat) (hk : 0 < k) :
    T.separated k hk = (T.table k hk).generatedGlobalSeparation := by
  exact CrossBlockLowerBoundsInterface.CrossBlockLowerBounds.separated_ofIndexedTables
    T k hk

/-- Exact-multiple target obtained directly from finite indexed tables. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target obtained directly from finite indexed tables. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedCrossBlockLowerTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end IndexedCrossBlockLowerTableFamily

/-- Concrete period-search data plus finite indexed cross-block lower tables. -/
structure IndexedConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    IndexedCrossBlockLowerTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace IndexedConcreteCrossBlockFamily

/-- Forget concrete words to the period-search family expected by the
cross-block lower-bound interface. -/
def toRoleHingedPeriodSearchFamily
    (F : IndexedConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  F.periodSearch.toRoleHingedPeriodSearchFamily

@[simp]
theorem toRoleHingedPeriodSearchFamily_eq
    (F : IndexedConcreteCrossBlockFamily) :
    F.toRoleHingedPeriodSearchFamily =
      F.periodSearch.toRoleHingedPeriodSearchFamily :=
  rfl

/-- The stored finite indexed table family, reindexed through the concrete
period-search facade. -/
def toIndexedCrossBlockLowerTableFamily
    (F : IndexedConcreteCrossBlockFamily) :
    IndexedCrossBlockLowerTableFamily F.toRoleHingedPeriodSearchFamily :=
  F.tables

@[simp]
theorem toIndexedCrossBlockLowerTableFamily_table
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toIndexedCrossBlockLowerTableFamily.table k hk) =
      F.tables.table k hk :=
  rfl

/-- Forget finite indexed tables to the downstream cross-block lower-bound
facade. -/
def toCrossBlockLowerBounds
    (F : IndexedConcreteCrossBlockFamily) :
    CrossBlockLowerBounds F.toRoleHingedPeriodSearchFamily :=
  F.toIndexedCrossBlockLowerTableFamily.toCrossBlockLowerBounds

@[simp]
theorem toCrossBlockLowerBounds_lower
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toCrossBlockLowerBounds).lower k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower k hk :=
  rfl

/-- The `>= 1` finite inequalities project to `CrossBlockLowerBounds`. -/
theorem toCrossBlockLowerBounds_ge_one
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((F.toCrossBlockLowerBounds).lower k hk) :=
  F.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

/-- The finite metric inequalities project to `CrossBlockLowerBounds`. -/
theorem toCrossBlockLowerBounds_bound
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk)
      ((F.toCrossBlockLowerBounds).lower k hk) :=
  F.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

/-- The concrete `>= 1` projection is the stored finite table-family
projection. -/
theorem toCrossBlockLowerBounds_ge_one_eq
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower_ge_one k hk :=
  rfl

/-- The concrete metric projection is the stored finite table-family
projection. -/
theorem toCrossBlockLowerBounds_bound_eq
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.toCrossBlockLowerBounds.toDistanceLowerBounds k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower_bound k hk :=
  rfl

/-- Generated global separation supplied by the finite indexed table family. -/
def separated
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  F.toCrossBlockLowerBounds.separated k hk

/-- The concrete separation wrapper reduces to the one-table separation
projection. -/
theorem separated_eq_table
    (F : IndexedConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.separated k hk =
      (F.toIndexedCrossBlockLowerTableFamily.table k hk).generatedGlobalSeparation :=
  F.toIndexedCrossBlockLowerTableFamily.separated_eq_table k hk

/-- The role-hinged generated-closure family obtained from concrete
period-search data and finite indexed cross-block tables. -/
def toRoleHingedGeneratedClosureFamily
    (F : IndexedConcreteCrossBlockFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  F.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- Exact-multiple Pach-Toth target from concrete period-search data and finite
indexed cross-block tables. -/
theorem targetUpperConstructionFiveSixteen
    (F : IndexedConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toIndexedCrossBlockLowerTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target from concrete period-search data, finite
indexed cross-block tables, and the checked small cases imported downstream. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : IndexedConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toIndexedCrossBlockLowerTableFamily.targetUpperConstructionFiveSixteenArbitrary

end IndexedConcreteCrossBlockFamily

/-- Concrete period-search data plus reduced finite non-connector
square-distance tables.  Connector slots are supplied by the checked
role-hinge connector-unit facts when this package is expanded to indexed
cross-block lower tables. -/
structure IndexedNonConnectorConcreteCrossBlockFamily where
  periodSearch : PeriodSearchData
  tables :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      periodSearch.toRoleHingedPeriodSearchFamily

namespace IndexedNonConnectorConcreteCrossBlockFamily

/-- Forget concrete words to the period-search family expected by the
non-connector square-distance interface. -/
def toRoleHingedPeriodSearchFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    RoleHingedPeriodSearchFamily :=
  F.periodSearch.toRoleHingedPeriodSearchFamily

@[simp]
theorem toRoleHingedPeriodSearchFamily_eq
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    F.toRoleHingedPeriodSearchFamily =
      F.periodSearch.toRoleHingedPeriodSearchFamily :=
  rfl

/-- The stored reduced non-connector table family, reindexed through the
concrete period-search facade. -/
def toIndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily
      F.toRoleHingedPeriodSearchFamily :=
  F.tables

@[simp]
theorem toIndexedNonConnectorCrossBlockSqDistanceTableFamily_table
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toIndexedNonConnectorCrossBlockSqDistanceTableFamily.table k hk) =
      F.tables.table k hk :=
  rfl

/-- Expand reduced non-connector square-distance tables to the concrete
indexed cross-block lower-table family. -/
def toIndexedCrossBlockLowerTableFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    IndexedCrossBlockLowerTableFamily F.toRoleHingedPeriodSearchFamily :=
  IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete.toIndexedCrossBlockLowerTableFamily
    F.toIndexedNonConnectorCrossBlockSqDistanceTableFamily

@[simp]
theorem toIndexedCrossBlockLowerTableFamily_table
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toIndexedCrossBlockLowerTableFamily.table k hk) =
      (F.tables.table k hk).toCrossBlockLowerTable :=
  rfl

/-- View the reduced non-connector package as the older concrete indexed
lower-table package. -/
def toIndexedConcreteCrossBlockFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    IndexedConcreteCrossBlockFamily where
  periodSearch := F.periodSearch
  tables := F.toIndexedCrossBlockLowerTableFamily

@[simp]
theorem toIndexedConcreteCrossBlockFamily_periodSearch
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    F.toIndexedConcreteCrossBlockFamily.periodSearch = F.periodSearch :=
  rfl

@[simp]
theorem toIndexedConcreteCrossBlockFamily_tables
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    F.toIndexedConcreteCrossBlockFamily.tables =
      F.toIndexedCrossBlockLowerTableFamily :=
  rfl

/-- Forget reduced finite tables to the downstream cross-block lower-bound
facade. -/
def toCrossBlockLowerBounds
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    CrossBlockLowerBounds F.toRoleHingedPeriodSearchFamily :=
  IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete.toCrossBlockLowerBounds
    F.toIndexedNonConnectorCrossBlockSqDistanceTableFamily

@[simp]
theorem toCrossBlockLowerBounds_lower
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    (F.toCrossBlockLowerBounds).lower k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower k hk :=
  rfl

/-- The `>= 1` finite inequalities project to `CrossBlockLowerBounds`. -/
theorem toCrossBlockLowerBounds_ge_one
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      ((F.toCrossBlockLowerBounds).lower k hk) :=
  F.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk

/-- The finite metric inequalities project to `CrossBlockLowerBounds`. -/
theorem toCrossBlockLowerBounds_bound
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk)
      ((F.toCrossBlockLowerBounds).lower k hk) :=
  F.toCrossBlockLowerBounds.toDistanceLowerBounds k hk

/-- The concrete `>= 1` projection is the expanded finite table-family
projection. -/
theorem toCrossBlockLowerBounds_ge_one_eq
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.toCrossBlockLowerBounds.toLowerBoundsAtLeastOne k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower_ge_one k hk :=
  rfl

/-- The concrete metric projection is the expanded finite table-family
projection. -/
theorem toCrossBlockLowerBounds_bound_eq
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.toCrossBlockLowerBounds.toDistanceLowerBounds k hk =
      F.toIndexedCrossBlockLowerTableFamily.lower_bound k hk :=
  rfl

/-- Generated global separation supplied by the reduced finite
non-connector square-distance table family. -/
def separated
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.periodSearch.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase
      (F.periodSearch.orientation k hk) :=
  IndexedNonConnectorCrossBlockSqDistanceTableFamilyConcrete.separated
    F.toIndexedNonConnectorCrossBlockSqDistanceTableFamily k hk

/-- The concrete separation wrapper reduces to the expanded one-table
separation projection. -/
theorem separated_eq_table
    (F : IndexedNonConnectorConcreteCrossBlockFamily)
    (k : Nat) (hk : 0 < k) :
    F.separated k hk =
      (F.toIndexedCrossBlockLowerTableFamily.table k hk).generatedGlobalSeparation :=
  F.toIndexedCrossBlockLowerTableFamily.separated_eq_table k hk

/-- The role-hinged generated-closure family obtained from concrete
period-search data and reduced finite non-connector square-distance tables. -/
def toRoleHingedGeneratedClosureFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily :=
  F.toCrossBlockLowerBounds.toRoleHingedGeneratedClosureFamily

/-- Exact-multiple Pach-Toth target from the expanded indexed lower-table
route. -/
theorem targetUpperConstructionFiveSixteen_viaIndexedConcreteCrossBlockFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toIndexedConcreteCrossBlockFamily.targetUpperConstructionFiveSixteen

/-- Exact-multiple Pach-Toth target from concrete period-search data and
reduced finite non-connector square-distance tables. -/
theorem targetUpperConstructionFiveSixteen
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach-Toth target from the expanded indexed lower-table
route. -/
theorem targetUpperConstructionFiveSixteenArbitrary_viaIndexedConcreteCrossBlockFamily
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toIndexedConcreteCrossBlockFamily.targetUpperConstructionFiveSixteenArbitrary

/-- Arbitrary-`n` Pach-Toth target from concrete period-search data, reduced
finite non-connector square-distance tables, and the checked small cases
imported downstream. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : IndexedNonConnectorConcreteCrossBlockFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end IndexedNonConnectorConcreteCrossBlockFamily

/-- Concrete period-search data plus explicit non-connector square-distance
checks, bundled as the reduced concrete cross-block family. -/
def indexedNonConnectorConcreteCrossBlockFamilyOfFacts
    (periodSearch : PeriodSearchData)
    (sqDist_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          Ne i j ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                  periodSearch.toRoleHingedPeriodSearchFamily hk i u j v) :
    IndexedNonConnectorConcreteCrossBlockFamily where
  periodSearch := periodSearch
  tables :=
    indexedNonConnectorCrossBlockSqDistanceTableFamilyOfFacts sqDist_ge_one

/-- Exact-multiple target directly from concrete period-search data plus
non-connector square-distance checks. -/
theorem targetUpperConstructionFiveSixteen_ofNonConnectorSqDistanceFacts
    (periodSearch : PeriodSearchData)
    (sqDist_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          Ne i j ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                  periodSearch.toRoleHingedPeriodSearchFamily hk i u j v) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (indexedNonConnectorConcreteCrossBlockFamilyOfFacts
    periodSearch sqDist_ge_one).targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target directly from concrete period-search data plus
non-connector square-distance checks. -/
theorem targetUpperConstructionFiveSixteenArbitrary_ofNonConnectorSqDistanceFacts
    (periodSearch : PeriodSearchData)
    (sqDist_ge_one :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          Ne i j ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockDistanceSqReduction.indexedGeneratedSqDist
                  periodSearch.toRoleHingedPeriodSearchFamily hk i u j v) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (indexedNonConnectorConcreteCrossBlockFamilyOfFacts
    periodSearch sqDist_ge_one).targetUpperConstructionFiveSixteenArbitrary

/-- Concrete period-search data plus upper-triangle non-connector polynomial
facts, bundled as the reduced concrete cross-block family. -/
def indexedNonConnectorConcreteCrossBlockFamilyOfPolynomialFacts
    (periodSearch : PeriodSearchData)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  periodSearch.toRoleHingedPeriodSearchFamily hk i u j v) :
    IndexedNonConnectorConcreteCrossBlockFamily where
  periodSearch := periodSearch
  tables :=
    indexedNonConnectorCrossBlockSqDistanceTableFamilyOfPolynomialFacts
      polynomial_ge_one_lt

/-- Exact-multiple target directly from concrete period-search data plus
upper-triangle non-connector polynomial checks. -/
theorem targetUpperConstructionFiveSixteen_ofNonConnectorPolynomialFacts
    (periodSearch : PeriodSearchData)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  periodSearch.toRoleHingedPeriodSearchFamily hk i u j v) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (indexedNonConnectorConcreteCrossBlockFamilyOfPolynomialFacts
    periodSearch polynomial_ge_one_lt).targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target directly from concrete period-search data plus
upper-triangle non-connector polynomial checks. -/
theorem targetUpperConstructionFiveSixteenArbitrary_ofNonConnectorPolynomialFacts
    (periodSearch : PeriodSearchData)
    (polynomial_ge_one_lt :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertexIndex)
        (j : Fin k) (v : LocalVertexIndex),
          i.val < j.val ->
            Not (IndexedCyclicConnectorPair hk i u j v) ->
              1 <=
                CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
                  periodSearch.toRoleHingedPeriodSearchFamily hk i u j v) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (indexedNonConnectorConcreteCrossBlockFamilyOfPolynomialFacts
    periodSearch polynomial_ge_one_lt).targetUpperConstructionFiveSixteenArbitrary

end

end IndexedCrossBlockTableConcrete
end PachToth
end ErdosProblems1066
