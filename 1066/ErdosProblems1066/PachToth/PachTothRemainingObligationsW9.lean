import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.ExactFiveSixteenRouteMatrix
import ErdosProblems1066.PachToth.ExactLocalTransitionObligationMatrix
import ErdosProblems1066.PachToth.FiniteCertificateObligationSummary
import ErdosProblems1066.PachToth.PachTothRemainingMatrix

set_option autoImplicit false

/-!
# W9 Pach--Toth remaining obligations

This module is the W9 consolidation point for the current Pach--Toth
`5 / 16` blockers.  It records the viable route as explicit data packages
and projection theorems, and it records the known obstruction from the
concrete four-target role-hinge map.

There is intentionally no unconditional final closure here.  Every target
theorem below consumes a concrete package carrying the period equations and
non-connector square-value/lower-table fields still needed downstream.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothRemainingObligationsW9

open FiniteGraph
open FiniteGraph.LocalVertex
open FiniteCertificateObligationSummary
open ConcreteNonConnectorValueMatrix

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingeTransitions :=
  FiniteCertificateObligationSummary.RoleHingeTransitions

abbrev PeriodSearchData :=
  FiniteCertificateObligationSummary.PeriodSearchData

abbrev SqValueCertificate :=
  FiniteCertificateObligationSummary.SqValueCertificate

abbrev LocalVertexIndex :=
  FiniteCertificateObligationSummary.LocalVertexIndex

/-- A target-producing row in the W9 remaining-obligation matrix. -/
structure ProjectionRow (alpha : Type) where
  exactBlock :
    alpha -> forall (k : Nat), 0 < k ->
      targetUpperConstructionFiveSixteenAt (16 * k)
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- The exact flattened fields needed by the current finite-certificate route
to close the exact `16 * k` family and then the arbitrary-`n` target.

The first three fields are the role-hinged period-search data: transition
facts, one finite orientation word for every positive block count, and the
sixteen indexed period equations for that word.  The last three fields are
the remaining non-connector square-value table data: stored values, equality
to the generated coordinate square polynomial, and the lower bound `1 <=`.
-/
structure FiveSixteenClosingFields where
  transitions : RoleHingeTransitions
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  equation :
    forall (k : Nat) (hk : 0 < k) (i : Fin 16),
      PeriodSearchInterface.AlgebraicVertexPeriodEquation
        transitions.toFigure2TransitionObligations
        BaseTransitionRealization.exactBase
        (PeriodCertificateExamples.finiteOrientationWordOfWord hk
          (word k hk))
        (BlockPartition.localVertexEquivFin16.symm i)
  sqValue :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertexIndex -> Fin k -> LocalVertexIndex -> Real
  sqValue_eq_polynomial_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val ->
          sqValue k hk i u j v =
            CrossBlockSqTableSearch.indexedGeneratedSqPolynomial
              (ConcretePeriodSearchFamily.PeriodSearchData.toRoleHingedPeriodSearchFamily
                ({ transitions := transitions
                   word := word
                   equation := equation } : PeriodSearchData))
              hk i u j v
  sqValue_ge_one_lt :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        i.val < j.val -> 1 <= sqValue k hk i u j v

namespace FiveSixteenClosingFields

/-- Repackage the flattened W9 fields as the existing finite-certificate
obligation summary. -/
def toObligations
    (F : FiveSixteenClosingFields) :
    FiniteCertificateObligationSummary.Obligations where
  transitions := F.transitions
  word := F.word
  equation := F.equation
  sqValue := F.sqValue
  sqValue_eq_polynomial_lt := F.sqValue_eq_polynomial_lt
  sqValue_ge_one_lt := F.sqValue_ge_one_lt

@[simp]
theorem toObligations_transitions
    (F : FiveSixteenClosingFields) :
    F.toObligations.transitions = F.transitions :=
  rfl

@[simp]
theorem toObligations_sqValue
    (F : FiveSixteenClosingFields) :
    F.toObligations.sqValue = F.sqValue :=
  rfl

/-- The period-search package projected from the flattened fields. -/
def toPeriodSearchData
    (F : FiveSixteenClosingFields) :
    PeriodSearchData :=
  F.toObligations.toPeriodSearchData

/-- The non-connector square-value certificate projected from the flattened
fields. -/
def toSqValueCertificate
    (F : FiveSixteenClosingFields) :
    SqValueCertificate F.toPeriodSearchData :=
  F.toObligations.toSqValueCertificate

/-- Exact-block projection from the explicit W9 closing fields. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (F : FiveSixteenClosingFields)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  F.toObligations.targetUpperConstructionFiveSixteenAt_exactBlock k hk

/-- Exact target projection from the explicit W9 closing fields. -/
theorem targetUpperConstructionFiveSixteen
    (F : FiveSixteenClosingFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toObligations.targetUpperConstructionFiveSixteen_nonConnector

/-- Arbitrary-`n` target projection from the explicit W9 closing fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : FiveSixteenClosingFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  F.toObligations.targetUpperConstructionFiveSixteenArbitrary_nonConnector

end FiveSixteenClosingFields

/-- The same viable route with the period-search package already assembled
and only the dependent square-value certificate left as a separate field. -/
structure PeriodSearchSqValuePackage where
  periodSearch : PeriodSearchData
  sqValue : SqValueCertificate periodSearch

namespace PeriodSearchSqValuePackage

/-- Exact-block projection from assembled period-search data and the
remaining square-value certificate. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (P : PeriodSearchSqValuePackage)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  targetUpperConstructionFiveSixteenAt_exactBlock_of_periodSearchData_sqValueCertificate
    P.periodSearch P.sqValue k hk

/-- Exact target through the reduced non-connector route. -/
theorem targetUpperConstructionFiveSixteen
    (P : PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_nonConnector_of_periodSearchData_sqValueCertificate
    P.periodSearch P.sqValue

/-- Arbitrary target through the reduced non-connector exact target and the
checked exact-to-arbitrary bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (P : PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_nonConnector_of_sqValueCertificate
    P.periodSearch P.sqValue

end PeriodSearchSqValuePackage

/-- The old all-non-port-pair same-branch residual exact-local field.  W9
keeps this spelling only to mark the blocked route. -/
abbrev FullSameRestForConcreteFourTargetMap : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (RoleHingeConcreteSearch.samePlaceNext source u)
              (RoleHingeConcreteSearch.samePlaceNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- The concrete four-target map cannot provide the full same-branch residual
field.  The viable W9 route therefore avoids using this field as a closure
input. -/
theorem concreteFourTargetMap_obstructs_fullSameRest :
    Not FullSameRestForConcreteFourTargetMap :=
  RoleHingeExactLocalFinite.not_samePlaceNext_full_nonPortPair_rest

/-- The explicit row witnessing the obstruction: on the exact base, the row
`T1_1, r` is not preserved by the current concrete same-branch map. -/
abbrev ConcreteFourTargetT11RRowObstruction : Prop :=
  RoleHingeSameBlockAlgebra.sqDist
      (RoleHingeConcreteSearch.samePlaceNext
        ExactLocalGeometry.localPoint T1_1)
      (RoleHingeConcreteSearch.samePlaceNext
        ExactLocalGeometry.localPoint LocalVertex.r) ≠
    ((ExactLocalGeometry.localNorm4 T1_1 LocalVertex.r : Int) : Real) / 4

/-- The concrete `T1_1, r` obstruction, exposed in the W9 matrix. -/
theorem concreteFourTarget_T11RRow_obstruction :
    ConcreteFourTargetT11RRowObstruction :=
  ExactLocalTransitionObligationMatrix.samePlaceNext_exactBase_T1_1_r_forces_contradiction

/-- A compact inventory of what is still required before the W9 route becomes
an unconditional proof. -/
structure RemainingObligationInventory where
  period_words_and_equations : Type
  nonConnector_square_values : Type
  exactLocal_fullSameRest_blocked : Not FullSameRestForConcreteFourTargetMap
  explicit_blocked_row : ConcreteFourTargetT11RRowObstruction

/-- The current inventory: the exact closing data are the flattened W9 fields;
the same-rest shortcut is blocked by the concrete four-target map. -/
def remainingObligations : RemainingObligationInventory where
  period_words_and_equations := FiveSixteenClosingFields
  nonConnector_square_values := FiveSixteenClosingFields
  exactLocal_fullSameRest_blocked :=
    concreteFourTargetMap_obstructs_fullSameRest
  explicit_blocked_row := concreteFourTarget_T11RRow_obstruction

/-- The flattened-field row: this is the most explicit viable W9 route. -/
def fiveSixteenClosingFieldsRow :
    ProjectionRow FiveSixteenClosingFields where
  exactBlock :=
    FiveSixteenClosingFields.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := FiveSixteenClosingFields.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    FiveSixteenClosingFields.targetUpperConstructionFiveSixteenArbitrary

/-- The assembled period-search plus square-value-certificate row. -/
def periodSearchSqValuePackageRow :
    ProjectionRow PeriodSearchSqValuePackage where
  exactBlock :=
    PeriodSearchSqValuePackage.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget := PeriodSearchSqValuePackage.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    PeriodSearchSqValuePackage.targetUpperConstructionFiveSixteenArbitrary

/-- The concrete value-matrix row: period-search data plus generated
non-connector value matrices. -/
def concreteValueMatrixFamilyRow :
    ProjectionRow ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily where
  exactBlock :=
    ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily.targetUpperConstructionFiveSixteenAt
  exactTarget :=
    ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    ConcreteValueMatrixFamily.targetUpperConstructionFiveSixteenArbitrary

/-- The older concrete-remaining-data row is retained as a projection route,
but its fields are still explicit data; the matrix does not manufacture
period equations, exact-local rows, or non-connector tables. -/
def concreteRemainingDataRow :
    ProjectionRow PachTothRemainingMatrix.ConcreteRemainingData where
  exactBlock :=
    PachTothRemainingMatrix.ConcreteRemainingData.targetUpperConstructionFiveSixteenAt_exactBlock
  exactTarget :=
    PachTothRemainingMatrix.ConcreteRemainingData.targetUpperConstructionFiveSixteen
  arbitraryTarget :=
    PachTothRemainingMatrix.ConcreteRemainingData.targetUpperConstructionFiveSixteenArbitrary

/-- The W9 remaining-obligation matrix.  Every target-producing row is
conditional on an explicit package, and the blocked same-rest shortcut is
recorded as an obstruction rather than a closure theorem. -/
structure Matrix where
  inventory : RemainingObligationInventory
  flattenedFields : ProjectionRow FiveSixteenClosingFields
  periodSearchSqValue : ProjectionRow PeriodSearchSqValuePackage
  concreteValueMatrices :
    ProjectionRow ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily
  concreteRemainingData :
    ProjectionRow PachTothRemainingMatrix.ConcreteRemainingData

/-- The checked W9 matrix. -/
def matrix : Matrix where
  inventory := remainingObligations
  flattenedFields := fiveSixteenClosingFieldsRow
  periodSearchSqValue := periodSearchSqValuePackageRow
  concreteValueMatrices := concreteValueMatrixFamilyRow
  concreteRemainingData := concreteRemainingDataRow

/-- Exact-block target from the flattened W9 closing fields. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_closingFields
    (F : FiveSixteenClosingFields)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.flattenedFields.exactBlock F k hk

/-- Exact target from the flattened W9 closing fields. -/
theorem targetUpperConstructionFiveSixteen_of_closingFields
    (F : FiveSixteenClosingFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.flattenedFields.exactTarget F

/-- Arbitrary target from the flattened W9 closing fields. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_closingFields
    (F : FiveSixteenClosingFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flattenedFields.arbitraryTarget F

/-- Exact target from assembled period-search data and a dependent
square-value certificate. -/
theorem targetUpperConstructionFiveSixteen_of_periodSearchSqValue
    (P : PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.periodSearchSqValue.exactTarget P

/-- Arbitrary target from assembled period-search data and a dependent
square-value certificate. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_periodSearchSqValue
    (P : PeriodSearchSqValuePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.periodSearchSqValue.arbitraryTarget P

/-- Exact target from concrete non-connector value matrices. -/
theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteValueMatrices.exactTarget C

/-- Arbitrary target from concrete non-connector value matrices. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteValueMatrices.arbitraryTarget C

/-- Exact target from the older concrete remaining-data package. -/
theorem targetUpperConstructionFiveSixteen_of_concreteRemainingData
    (D : PachTothRemainingMatrix.ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concreteRemainingData.exactTarget D

/-- Arbitrary target from the older concrete remaining-data package. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteRemainingData
    (D : PachTothRemainingMatrix.ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concreteRemainingData.arbitraryTarget D

end

end PachTothRemainingObligationsW9
end PachToth
end ErdosProblems1066
