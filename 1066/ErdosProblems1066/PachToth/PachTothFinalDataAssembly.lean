import ErdosProblems1066.PachToth.ArbitraryNExactRemainderClosure
import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable
import ErdosProblems1066.PachToth.ConcreteNonConnectorValueMatrix
import ErdosProblems1066.PachToth.ConcretePeriodWordSearch
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition
import ErdosProblems1066.PachToth.PachTothW8ClosureMatrix

set_option autoImplicit false

/-!
# Final Pach--Toth data assembly

This module is the final honest assembly layer for the W8 Pach--Toth route.
It does not manufacture any missing period, exact-local, lower-table, or
value-matrix data.  Every public target theorem below takes an explicit data
package whose fields contain the concrete information needed by the route.

For the arbitrary-`n` target, this file routes the exact `16 * k` target
through `ArbitraryNExactRemainderClosure`, so the checked exact-remainder
split is the only exact-to-arbitrary bridge used here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothFinalDataAssembly

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The exact-remainder bridge is available once an exact target has been
proved from explicit data. -/
theorem exactRemainderBridge_present
    (H : PachToth.targetUpperConstructionFiveSixteen) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ArbitraryNExactRemainderClosure.arbitrary_of_exactTarget_checkedRemainder
      H

/-- Period words and cross-block lower tables over a flexible exact-local
same/opposite branch.

The fields are the missing data: a flexible branch, a checked period equation
for every positive block count, and explicit cross-block lower bounds. -/
structure FlexiblePeriodLowerTableFamily where
  transitions : FlexibleExactLocalTransition.SameOpposite
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedPeriodEquation
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
  lower :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  lower_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (lower k hk)
  lower_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
        (lower k hk)

namespace FlexiblePeriodLowerTableFamily

def orientation
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    Fin k -> OrientationData.BlockOrientation :=
  (F.word k hk).toFin

@[simp]
theorem orientation_apply
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) (i : Fin k) :
    F.orientation k hk i = F.word k hk i := by
  rfl

/-- Closure equation derived from the stored period equation. -/
def closure
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  GeneratedPeriodClosure.generatedClosureEquation_of_generatedPeriodEquation
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    (F.period k hk)

/-- Same-block isometry supplied by the flexible exact-local branch. -/
def sameBlockIsometry
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  F.transitions.generatedSameBlockIsometry hk (F.orientation k hk)

/-- Global separation from the explicit lower tables and the flexible
same-block exact-local data. -/
def separated
    (F : FlexiblePeriodLowerTableFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (F.orientation k hk) :=
  GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
    F.transitions.toFigure2TransitionObligations
    hk
    BaseTransitionRealization.exactBase
    (F.orientation k hk)
    (F.sameBlockIsometry k hk)
    (F.lower k hk)
    (F.lower_ge_one k hk)
    (F.lower_bound k hk)

/-- Repackage the explicit fields as the flexible generated-closure family. -/
def toGeneratedClosureFamily
    (F : FlexiblePeriodLowerTableFamily) :
    FlexibleExactLocalTransition.GeneratedClosureFamily where
  transitions := F.transitions
  orientation := F.orientation
  closure := F.closure
  separated := F.separated

/-- Exact Pach--Toth target from explicit flexible branch, period equations,
and lower tables. -/
theorem targetUpperConstructionFiveSixteen
    (F : FlexiblePeriodLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toGeneratedClosureFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target from the same explicit data, using only
the checked exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (F : FlexiblePeriodLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  exactRemainderBridge_present F.targetUpperConstructionFiveSixteen

end FlexiblePeriodLowerTableFamily

/-- Value-matrix spelling of the flexible route.  The `value` field is the
lower table; the two proof fields are exactly the `>= 1` and distance-bound
obligations consumed by the flexible lower-table route. -/
structure FlexiblePeriodValueMatrixFamily where
  transitions : FlexibleExactLocalTransition.SameOpposite
  word : forall (k : Nat), 0 < k -> OrientationWord.Word k
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedPeriodEquation
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
  value :
    forall (k : Nat), 0 < k ->
      Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real
  value_ge_one :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
        (value k hk)
  value_bound :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
        transitions.toFigure2TransitionObligations
        hk
        BaseTransitionRealization.exactBase
        ((word k hk).toFin)
        (value k hk)

namespace FlexiblePeriodValueMatrixFamily

/-- Forget value-matrix naming to the lower-table route. -/
def toLowerTableFamily
    (V : FlexiblePeriodValueMatrixFamily) :
    FlexiblePeriodLowerTableFamily where
  transitions := V.transitions
  word := V.word
  period := V.period
  lower := V.value
  lower_ge_one := V.value_ge_one
  lower_bound := V.value_bound

/-- Exact Pach--Toth target from explicit flexible branch, period equations,
and value matrices. -/
theorem targetUpperConstructionFiveSixteen
    (V : FlexiblePeriodValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  V.toLowerTableFamily.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` Pach--Toth target from explicit flexible branch, period
equations, and value matrices, using only the checked exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (V : FlexiblePeriodValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  V.toLowerTableFamily.targetUpperConstructionFiveSixteenArbitrary

end FlexiblePeriodValueMatrixFamily

/-- The final assembly field shapes.  These are data types, not solved
theorems; target wrappers below require inhabitants explicitly. -/
structure RequiredFieldShapes where
  flexibleBranch : Type
  periodLowerTables : Type
  periodValueMatrices : Type
  exactRemainderBridge : Prop

/-- Public record of what this final assembly layer consumes. -/
def requiredFieldShapes : RequiredFieldShapes where
  flexibleBranch := FlexibleExactLocalTransition.SameOpposite
  periodLowerTables := FlexiblePeriodLowerTableFamily
  periodValueMatrices := FlexiblePeriodValueMatrixFamily
  exactRemainderBridge :=
    PachToth.targetUpperConstructionFiveSixteen ->
      PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- The only unconditional row in the final field-shape record: exact targets
extend to arbitrary `n` by the checked exact-remainder construction. -/
theorem requiredFieldShapes_exactRemainderBridge :
    requiredFieldShapes.exactRemainderBridge :=
  exactRemainderBridge_present

/-- Exact target from the minimal W8 certificate row. -/
theorem targetUpperConstructionFiveSixteen_of_minimalExactTargetCertificate
    (C : PachTothW8ClosureMatrix.MinimalExactTargetCertificate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PachTothW8ClosureMatrix.targetUpperConstructionFiveSixteen_of_minimalExactTargetCertificate
    C

/-- Arbitrary target from the minimal W8 certificate row, routed through the
exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_minimalExactTargetCertificate
    (C : PachTothW8ClosureMatrix.MinimalExactTargetCertificate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  exactRemainderBridge_present
    (targetUpperConstructionFiveSixteen_of_minimalExactTargetCertificate C)

/-- Exact target from the concrete remaining-data package. -/
theorem targetUpperConstructionFiveSixteen_of_concreteRemainingData
    (D : PachTothW8ClosureMatrix.ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  PachTothW8ClosureMatrix.targetUpperConstructionFiveSixteen_of_concreteRemainingData
    D

/-- Arbitrary target from the concrete remaining-data package, routed through
the exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteRemainingData
    (D : PachTothW8ClosureMatrix.ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  exactRemainderBridge_present
    (targetUpperConstructionFiveSixteen_of_concreteRemainingData D)

/-- Exact target from concrete period-search data plus non-connector lower
tables. -/
theorem targetUpperConstructionFiveSixteen_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.targetUpperConstructionFiveSixteen

/-- Arbitrary target from concrete period-search data plus non-connector
lower tables, routed through the exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteNonConnectorLowerTableFamily
    (C : ConcreteCrossBlockLowerTable.ConcreteNonConnectorLowerTableFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  exactRemainderBridge_present
    (targetUpperConstructionFiveSixteen_of_concreteNonConnectorLowerTableFamily C)

/-- Exact target from concrete period-search data plus checked value
matrices. -/
theorem targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.targetUpperConstructionFiveSixteen

/-- Arbitrary target from concrete period-search data plus checked value
matrices, routed through the exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.ConcreteValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  exactRemainderBridge_present
    (targetUpperConstructionFiveSixteen_of_concreteValueMatrixFamily C)

/-- Exact target from a candidate-family value matrix package. -/
theorem targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.targetUpperConstructionFiveSixteen

/-- Arbitrary target from a candidate-family value matrix package, routed
through the exact-remainder bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (C : ConcreteNonConnectorValueMatrix.CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  exactRemainderBridge_present
    (targetUpperConstructionFiveSixteen_of_candidateValueMatrixFamily C)

end

end PachTothFinalDataAssembly
end PachToth
end ErdosProblems1066
