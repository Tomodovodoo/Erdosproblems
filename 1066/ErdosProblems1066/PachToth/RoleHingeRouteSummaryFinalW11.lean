import ErdosProblems1066.PachToth.RoleHingeTargetFinalW11
import ErdosProblems1066.PachToth.RoleHingeFinalIntegratedW11
import ErdosProblems1066.PachToth.TransitionRoleHingeFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final role-hinge route summary

This leaf module gives a compact checked summary for the role-hinge route.
It records the imported W11 ledgers, displays the equation, exact-local, and
cross-block input fields explicitly, and exposes only target projections that
still take their source package as an argument.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeRouteSummaryFinalW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

/-! ## Imported checked ledgers -/

/-- W11 ledgers used by this role-hinge route summary. -/
structure CheckedLedgers where
  roleHingeTarget : RoleHingeTargetFinalW11.Matrix
  roleHingeFinal : RoleHingeFinalIntegratedW11.Matrix
  transitionRoleHinge : TransitionRoleHingeFinalW11.Matrix
  pachTothFinalAggregate : PachTothW11FinalAggregate.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

/-- Imported checked W11 role-hinge ledgers. -/
def checkedLedgers : CheckedLedgers where
  roleHingeTarget := RoleHingeTargetFinalW11.matrix
  roleHingeFinal := RoleHingeFinalIntegratedW11.matrix
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix
  pachTothFinalAggregate := PachTothW11FinalAggregate.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Explicit role-hinge fields -/

/-- Equation fields exposed by the checked role-hinge facades. -/
structure EquationFields where
  finalIntegrated : RoleHingeFinalIntegratedW11.EquationFieldLedger
  targetFinal : RoleHingeFinalIntegratedW11.EquationFieldLedger
  transitionFacade : RoleHingeFinalIntegratedW11.EquationFieldLedger

/-- Exact-local fields exposed by the checked role-hinge facades. -/
structure ExactLocalFields where
  finalIntegrated : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger
  targetFinal : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger
  transitionFacade : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger

/-- Cross-block fields exposed by the checked role-hinge facades. -/
structure CrossBlockFields where
  finalIntegrated : RoleHingeFinalIntegratedW11.CrossBlockLowerBoundFieldLedger
  targetFinal : RoleHingeFinalIntegratedW11.CrossBlockLowerBoundFieldLedger
  transitionFacade :
    RoleHingeFinalIntegratedW11.CrossBlockLowerBoundFieldLedger

/-- Explicit equation, exact-local, and cross-block fields. -/
structure ExplicitRouteFields where
  equation : EquationFields
  exactLocal : ExactLocalFields
  crossBlock : CrossBlockFields
  targetLedger : RoleHingeTargetFinalW11.RoleHingeTargetFieldLedger
  consistencyOpenInputs : PachTothW11FinalConsistency.OpenInputLedgers
  aggregateOpenData : PachTothW11FinalAggregate.ExplicitOpenData

/-- Checked explicit field summary for the role-hinge route. -/
def explicitRouteFields : ExplicitRouteFields where
  equation :=
    { finalIntegrated := RoleHingeFinalIntegratedW11.equationFieldLedger
      targetFinal :=
        RoleHingeTargetFinalW11.roleHingeTargetFieldLedger.equation
      transitionFacade :=
        TransitionRoleHingeFinalW11.explicitRoutePackages.roleHingeEquationFields }
  exactLocal :=
    { finalIntegrated := RoleHingeFinalIntegratedW11.exactLocalFieldLedger
      targetFinal :=
        RoleHingeTargetFinalW11.roleHingeTargetFieldLedger.exactLocal
      transitionFacade :=
        TransitionRoleHingeFinalW11.explicitRoutePackages.roleHingeExactLocalFields }
  crossBlock :=
    { finalIntegrated :=
        RoleHingeFinalIntegratedW11.crossBlockLowerBoundFieldLedger
      targetFinal :=
        RoleHingeTargetFinalW11.roleHingeTargetFieldLedger.crossBlockLowerBound
      transitionFacade :=
        TransitionRoleHingeFinalW11.explicitRoutePackages.roleHingeCrossBlockFields }
  targetLedger := RoleHingeTargetFinalW11.roleHingeTargetFieldLedger
  consistencyOpenInputs := PachTothW11FinalConsistency.openInputLedgers
  aggregateOpenData := PachTothW11FinalAggregate.explicitOpenData

/-! ## Conditional target rows -/

/-- Exact, eventual, and arbitrary projections from an explicit package. -/
structure ConditionalProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ConditionalProjection

def ofRoleHingeTarget
    {alpha : Sort u}
    (R : RoleHingeTargetFinalW11.TargetProjection alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofRoleHingeFinal
    {alpha : Sort u}
    (R : RoleHingeFinalIntegratedW11.TargetProjection alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofTransitionRoleHinge
    {alpha : Sort u}
    (R : TransitionRoleHingeFinalW11.TargetProjection alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end ConditionalProjection

/-- Equation and ledger-candidate projections retained by the summary. -/
structure EquationProjectionSummary where
  roleEquation :
    ConditionalProjection RoleHingeTargetFinalW11.RoleEquationRouteFields
  roleEquationViaTransition :
    ConditionalProjection RoleHingeTargetFinalW11.RoleEquationRouteFields
  roleEquationViaFacade :
    ConditionalProjection RoleHingeFinalIntegratedW11.RoleEquationRouteFields
  ledgerCandidateAssembly :
    ConditionalProjection
      RoleHingeTargetFinalW11.RoleLedgerCandidateAssemblyFields
  ledgerCandidateAssemblyViaFacade :
    ConditionalProjection
      RoleHingeFinalIntegratedW11.RoleLedgerCandidateAssemblyFields

/-- Checked equation projections, each still requiring its route package. -/
def equationProjectionSummary : EquationProjectionSummary where
  roleEquation :=
    ConditionalProjection.ofRoleHingeTarget
      RoleHingeTargetFinalW11.matrix.equation.roleEquation
  roleEquationViaTransition :=
    ConditionalProjection.ofRoleHingeTarget
      RoleHingeTargetFinalW11.matrix.equation.roleEquationViaTransition
  roleEquationViaFacade :=
    ConditionalProjection.ofTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.roleHingeEquationRoute
  ledgerCandidateAssembly :=
    ConditionalProjection.ofRoleHingeTarget
      RoleHingeTargetFinalW11.matrix.equation.ledgerCandidateAssembly
  ledgerCandidateAssemblyViaFacade :=
    ConditionalProjection.ofTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.roleHingeLedgerCandidateAssembly

/-- Exact-local projections retained by the summary. -/
structure ExactLocalProjectionSummary where
  routeFields :
    ConditionalProjection RoleHingeTargetFinalW11.ExactLocalRouteFields
  routeFieldsViaFacade :
    ConditionalProjection RoleHingeFinalIntegratedW11.ExactLocalRouteFields
  reducedEquations :
    forall S : RoleHingeTargetFinalW11.ExactLocalSameOppositeEquationPackage,
      ConditionalProjection
        (RoleHingeTargetFinalW11.ExactLocalTransitionRemainingFields S)

/-- Checked exact-local projections, each still requiring its package. -/
def exactLocalProjectionSummary : ExactLocalProjectionSummary where
  routeFields :=
    ConditionalProjection.ofRoleHingeTarget
      RoleHingeTargetFinalW11.matrix.exactLocal.routeFields
  routeFieldsViaFacade :=
    ConditionalProjection.ofTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.roleHingeExactLocalRoute
  reducedEquations := fun S =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.exactLocal.reducedEquations S)

/-- Cross-block projections retained by the summary. -/
structure CrossBlockProjectionSummary where
  lowerBoundClosure :
    forall F : RoleHingeTargetFinalW11.RoleHingePeriodFamily,
      ConditionalProjection
        (RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundClosure F)
  checkedLowerBoundFields :
    forall F : RoleHingeTargetFinalW11.RoleHingePeriodFamily,
      ConditionalProjection
        (RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundFields F)
  rawInequalityLedger :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      ConditionalProjection
        (RoleHingeTargetFinalW11.RawCrossBlockInequalityLedger F)
  numericLedgerClosure :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      ConditionalProjection
        (RoleHingeTargetFinalW11.NumericLedgerClosure F)
  closureLedger :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      ConditionalProjection
        (RoleHingeTargetFinalW11.CrossBlockClosureLedger F)
  roleHingeInequalityPackage :
    forall F : RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily,
      ConditionalProjection
        (RoleHingeTargetFinalW11.RoleHingeCrossBlockInequalityPackage F)

/-- Checked cross-block projections, each still requiring its package. -/
def crossBlockProjectionSummary : CrossBlockProjectionSummary where
  lowerBoundClosure := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound.lowerBoundClosure F)
  checkedLowerBoundFields := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound.checkedLowerBoundFields
        F)
  rawInequalityLedger := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound.rawInequalityLedger F)
  numericLedgerClosure := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound.numericLedgerClosure F)
  closureLedger := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound.closureLedger F)
  roleHingeInequalityPackage := fun F =>
    ConditionalProjection.ofRoleHingeTarget
      (RoleHingeTargetFinalW11.matrix.crossBlockLowerBound.roleHingeInequalityPackage
        F)

/-! ## Final summary matrix -/

/-- Final checked role-hinge route summary. -/
structure Matrix where
  checked : CheckedLedgers
  fields : ExplicitRouteFields
  equation : EquationProjectionSummary
  exactLocal : ExactLocalProjectionSummary
  crossBlock : CrossBlockProjectionSummary
  blockers : TransitionRoleHingeFinalW11.BlockerFields

/-- The checked W11 final role-hinge route summary. -/
def matrix : Matrix where
  checked := checkedLedgers
  fields := explicitRouteFields
  equation := equationProjectionSummary
  exactLocal := exactLocalProjectionSummary
  crossBlock := crossBlockProjectionSummary
  blockers := TransitionRoleHingeFinalW11.blockerFields

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public conditional equation projections -/

theorem exactTarget_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ExactTarget :=
  matrix.equation.roleEquation.exactTarget R

theorem eventualTarget_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    EventualTarget :=
  matrix.equation.roleEquation.eventualTarget R

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.equation.roleEquation.arbitraryTarget R

theorem exactTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ExactTarget :=
  matrix.equation.roleEquationViaTransition.exactTarget R

theorem arbitraryTarget_of_roleLedgerCandidateAssemblyFields
    (R : RoleHingeTargetFinalW11.RoleLedgerCandidateAssemblyFields) :
    ArbitraryTarget :=
  matrix.equation.ledgerCandidateAssembly.arbitraryTarget R

/-! ## Public conditional exact-local projections -/

theorem exactTarget_of_exactLocalRouteFields
    (R : RoleHingeTargetFinalW11.ExactLocalRouteFields) :
    ExactTarget :=
  matrix.exactLocal.routeFields.exactTarget R

theorem eventualTarget_of_exactLocalRouteFields
    (R : RoleHingeTargetFinalW11.ExactLocalRouteFields) :
    EventualTarget :=
  matrix.exactLocal.routeFields.eventualTarget R

theorem arbitraryTarget_of_exactLocalRouteFields
    (R : RoleHingeTargetFinalW11.ExactLocalRouteFields) :
    ArbitraryTarget :=
  matrix.exactLocal.routeFields.arbitraryTarget R

theorem arbitraryTarget_of_exactLocalReducedEquations
    (S : RoleHingeTargetFinalW11.ExactLocalSameOppositeEquationPackage)
    (R : RoleHingeTargetFinalW11.ExactLocalTransitionRemainingFields S) :
    ArbitraryTarget :=
  (matrix.exactLocal.reducedEquations S).arbitraryTarget R

/-! ## Public conditional cross-block projections -/

theorem exactTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingeTargetFinalW11.RoleHingePeriodFamily}
    (C : RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundClosure F) :
    ExactTarget :=
  (matrix.crossBlock.lowerBoundClosure F).exactTarget C

theorem eventualTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingeTargetFinalW11.RoleHingePeriodFamily}
    (C : RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundFields F) :
    EventualTarget :=
  (matrix.crossBlock.checkedLowerBoundFields F).eventualTarget C

theorem arbitraryTarget_of_rawCrossBlockInequalityLedger
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (L : RoleHingeTargetFinalW11.RawCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.rawInequalityLedger F).arbitraryTarget L

theorem arbitraryTarget_of_numericLedgerClosure
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (L : RoleHingeTargetFinalW11.NumericLedgerClosure F) :
    ArbitraryTarget :=
  (matrix.crossBlock.numericLedgerClosure F).arbitraryTarget L

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (C : RoleHingeTargetFinalW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlock.closureLedger F).arbitraryTarget C

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily}
    (R : RoleHingeTargetFinalW11.RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.crossBlock.roleHingeInequalityPackage F).arbitraryTarget R

/-! ## Public blocker projections -/

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

end

end RoleHingeRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
