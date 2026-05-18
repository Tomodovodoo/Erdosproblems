import ErdosProblems1066.PachToth.RoleHingeFinalIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.CrossBlockFinalIntegratedW11
import ErdosProblems1066.PachToth.GeneratedTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final role-hinge target aggregate

This target-facing layer gathers the checked W11 role-hinge ledgers with the
generated/cross-block target ledger and the broad Pach--Toth consistency
ledger.  It records the equation, exact-local, and cross-block lower-bound
input fields explicitly, then exposes only package-dependent exact, eventual,
and arbitrary target projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeTargetFinalW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev RoleEquationRouteFields :=
  RoleHingeFinalIntegratedW11.RoleEquationRouteFields

abbrev RoleLedgerCandidateAssemblyFields :=
  RoleHingeFinalIntegratedW11.RoleLedgerCandidateAssemblyFields

abbrev ExactLocalRouteFields :=
  RoleHingeFinalIntegratedW11.ExactLocalRouteFields

abbrev ExactLocalSameOppositeEquationPackage :=
  RoleHingeFinalIntegratedW11.ExactLocalSameOppositeEquationPackage

abbrev ExactLocalTransitionRemainingFields
    (S : ExactLocalSameOppositeEquationPackage) :=
  RoleHingeFinalIntegratedW11.ExactLocalTransitionRemainingFields S

abbrev RoleHingePeriodFamily :=
  RoleHingeFinalIntegratedW11.RoleHingePeriodFamily

abbrev RoleCrossBlockLowerBoundClosure
    (F : RoleHingePeriodFamily) :=
  RoleHingeFinalIntegratedW11.RoleCrossBlockLowerBoundClosure F

abbrev RoleCrossBlockLowerBoundFields
    (F : RoleHingePeriodFamily) :=
  RoleHingeFinalIntegratedW11.RoleCrossBlockLowerBoundFields F

abbrev LedgerPeriodFamily :=
  RoleHingeFinalIntegratedW11.LedgerPeriodFamily

abbrev RawCrossBlockInequalityLedger
    (F : LedgerPeriodFamily) :=
  RoleHingeFinalIntegratedW11.RawCrossBlockInequalityLedger F

abbrev NumericLedgerClosure
    (F : LedgerPeriodFamily) :=
  RoleHingeFinalIntegratedW11.NumericLedgerClosure F

abbrev CrossBlockClosureLedger
    (F : LedgerPeriodFamily) :=
  RoleHingeFinalIntegratedW11.CrossBlockClosureLedger F

abbrev CrossBlockRoleHingeFamily :=
  GeneratedTargetFinalW11.RoleHingeCrossBlockFamily

abbrev RoleHingeCrossBlockInequalityPackage
    (F : CrossBlockRoleHingeFamily) :=
  GeneratedTargetFinalW11.RoleHingeCrossBlockInequalityPackage F

abbrev GeneratedPointFamily :=
  GeneratedTargetFinalW11.GeneratedPointFamily

abbrev GeneratedPointLowerBoundFields
    (F : GeneratedPointFamily) :=
  GeneratedTargetFinalW11.GeneratedPointLowerBoundFields F

abbrev ConsistencyTransitionRouteFields :=
  TransitionIntegratedW11.TransitionRouteFields

/-! ## Shared route shape -/

/-- Exact, eventual, and arbitrary projections from one explicit input. -/
structure TargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace TargetProjection

def ofRoleHingeFinal
    {alpha : Sort u}
    (R : RoleHingeFinalIntegratedW11.TargetProjection alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofGeneratedTargetFinal
    {alpha : Sort u}
    (R : GeneratedTargetFinalW11.ProjectionRoute alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofExactAndArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> ExactTarget)
    (arbitraryTarget : alpha -> ArbitraryTarget) :
    TargetProjection alpha where
  exactTarget := exactTarget
  eventualTarget := fun a =>
    GeneratedTargetFinalW11.ProjectionRoute.eventualOfArbitrary
      (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget

end TargetProjection

/-! ## Explicit field ledgers -/

/-- Explicit role-hinge target input shapes. -/
structure RoleHingeTargetFieldLedger where
  equation : RoleHingeFinalIntegratedW11.EquationFieldLedger
  exactLocal : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger
  crossBlockLowerBound :
    RoleHingeFinalIntegratedW11.CrossBlockLowerBoundFieldLedger
  generatedTarget : GeneratedTargetFinalW11.ExplicitInputLedgers
  finalConsistency : PachTothW11FinalConsistency.OpenInputLedgers

/-- Public package-shape ledger for this role-hinge target aggregate. -/
def roleHingeTargetFieldLedger : RoleHingeTargetFieldLedger where
  equation := RoleHingeFinalIntegratedW11.equationFieldLedger
  exactLocal := RoleHingeFinalIntegratedW11.exactLocalFieldLedger
  crossBlockLowerBound :=
    RoleHingeFinalIntegratedW11.crossBlockLowerBoundFieldLedger
  generatedTarget := GeneratedTargetFinalW11.explicitInputLedgers
  finalConsistency := PachTothW11FinalConsistency.openInputLedgers

/-! ## Imported checked matrices -/

/-- Checked W11 matrices imported by the target aggregate. -/
structure ImportedMatrices where
  roleHingeFinal : RoleHingeFinalIntegratedW11.Matrix
  roleHingeIntegrated : RoleHingeIntegratedW11.Matrix
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  generatedTargetFinal : GeneratedTargetFinalW11.Matrix
  crossBlockFinal : CrossBlockFinalIntegratedW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

/-- Imported checked W11 matrices. -/
def importedMatrices : ImportedMatrices where
  roleHingeFinal := RoleHingeFinalIntegratedW11.matrix
  roleHingeIntegrated := RoleHingeIntegratedW11.matrix
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  generatedTargetFinal := GeneratedTargetFinalW11.matrix
  crossBlockFinal := CrossBlockFinalIntegratedW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Conditional route ledgers -/

/-- Equation routes through the checked role-hinge aggregate. -/
structure EquationProjectionLedger where
  roleEquation :
    TargetProjection RoleEquationRouteFields
  roleEquationViaTransition :
    TargetProjection RoleEquationRouteFields
  roleEquationViaBroadIntegrated :
    TargetProjection RoleEquationRouteFields
  ledgerCandidateAssembly :
    TargetProjection RoleLedgerCandidateAssemblyFields
  ledgerCandidateAssemblyViaCheckedTransition :
    TargetProjection RoleLedgerCandidateAssemblyFields

/-- Checked equation projection routes. -/
def equationProjectionLedger : EquationProjectionLedger where
  roleEquation :=
    TargetProjection.ofRoleHingeFinal
      RoleHingeFinalIntegratedW11.matrix.equation.roleHingeIntegrated
  roleEquationViaTransition :=
    TargetProjection.ofRoleHingeFinal
      RoleHingeFinalIntegratedW11.matrix.equation.transitionChecked
  roleEquationViaBroadIntegrated :=
    TargetProjection.ofRoleHingeFinal
      RoleHingeFinalIntegratedW11.matrix.equation.broadIntegrated
  ledgerCandidateAssembly :=
    TargetProjection.ofRoleHingeFinal
      RoleHingeFinalIntegratedW11.matrix.equation.ledgerCandidateAssembly
  ledgerCandidateAssemblyViaCheckedTransition :=
    TargetProjection.ofRoleHingeFinal
      RoleHingeFinalIntegratedW11.matrix.equation.checkedLedgerCandidateAssembly

/-- Exact-local routes from checked route fields and reduced equations. -/
structure ExactLocalProjectionLedger where
  routeFields : TargetProjection ExactLocalRouteFields
  reducedEquations :
    forall S : ExactLocalSameOppositeEquationPackage,
      TargetProjection (ExactLocalTransitionRemainingFields S)

/-- Checked exact-local projection routes. -/
def exactLocalProjectionLedger : ExactLocalProjectionLedger where
  routeFields :=
    TargetProjection.ofRoleHingeFinal
      RoleHingeFinalIntegratedW11.matrix.exactLocal.checkedRouteFields
  reducedEquations := fun S =>
    TargetProjection.ofRoleHingeFinal
      (RoleHingeFinalIntegratedW11.matrix.exactLocal.reducedEquationRoutes S)

/-- Cross-block lower-bound routes retained by the role-hinge aggregate. -/
structure CrossBlockLowerBoundProjectionLedger where
  lowerBoundClosure :
    forall F : RoleHingePeriodFamily,
      TargetProjection (RoleCrossBlockLowerBoundClosure F)
  checkedLowerBoundFields :
    forall F : RoleHingePeriodFamily,
      TargetProjection (RoleCrossBlockLowerBoundFields F)
  rawInequalityLedger :
    forall F : LedgerPeriodFamily,
      TargetProjection (RawCrossBlockInequalityLedger F)
  numericLedgerClosure :
    forall F : LedgerPeriodFamily,
      TargetProjection (NumericLedgerClosure F)
  closureLedger :
    forall F : LedgerPeriodFamily,
      TargetProjection (CrossBlockClosureLedger F)
  roleHingeInequalityPackage :
    forall F : CrossBlockRoleHingeFamily,
      TargetProjection (RoleHingeCrossBlockInequalityPackage F)

/-- Checked cross-block lower-bound projection routes. -/
def crossBlockLowerBoundProjectionLedger :
    CrossBlockLowerBoundProjectionLedger where
  lowerBoundClosure := fun F =>
    TargetProjection.ofRoleHingeFinal
      (RoleHingeFinalIntegratedW11.matrix.crossBlockLowerBound.lowerBoundClosure
        F)
  checkedLowerBoundFields := fun F =>
    TargetProjection.ofRoleHingeFinal
      (RoleHingeFinalIntegratedW11.matrix.crossBlockLowerBound.checkedLowerBoundFields
        F)
  rawInequalityLedger := fun F =>
    TargetProjection.ofRoleHingeFinal
      (RoleHingeFinalIntegratedW11.matrix.crossBlockLowerBound.rawInequalityLedger
        F)
  numericLedgerClosure := fun F =>
    TargetProjection.ofRoleHingeFinal
      (RoleHingeFinalIntegratedW11.matrix.crossBlockLowerBound.numericLedgerClosure
        F)
  closureLedger := fun F =>
    TargetProjection.ofRoleHingeFinal
      (RoleHingeFinalIntegratedW11.matrix.crossBlockLowerBound.closureLedger
        F)
  roleHingeInequalityPackage := fun F =>
    TargetProjection.ofGeneratedTargetFinal
      (GeneratedTargetFinalW11.matrix.crossBlock.roleHingeInequalityPackages F)

/-- Final-consistency routes currently exposed as arbitrary projections. -/
structure FinalConsistencyProjectionLedger where
  transitionArbitrary :
    ConsistencyTransitionRouteFields -> ArbitraryTarget
  generatedLowerBoundArbitrary :
    forall {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily},
      GeneratedTargetIntegratedW11.LowerBoundFields F -> ArbitraryTarget
  arbitraryNCrossBlockClosureArbitrary :
    forall {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily},
      ArbitraryNIntegratedW11.CrossBlockClosureLedger F -> ArbitraryTarget

/-- Checked broad final-consistency arbitrary projections. -/
def finalConsistencyProjectionLedger : FinalConsistencyProjectionLedger where
  transitionArbitrary :=
    GeneratedTargetFinalW11.matrix.finalConsistency.transitionArbitrary
  generatedLowerBoundArbitrary := fun C =>
    GeneratedTargetFinalW11.matrix.finalConsistency.generatedLowerBoundArbitrary
      C
  arbitraryNCrossBlockClosureArbitrary := fun C =>
    GeneratedTargetFinalW11.matrix.finalConsistency.arbitraryNCrossBlockClosureArbitrary
      C

/-! ## Final aggregate -/

/-- Final role-hinge target aggregate.

The route fields below are all functions out of explicit source packages.
-/
structure Matrix where
  fields : RoleHingeTargetFieldLedger
  imports : ImportedMatrices
  equation : EquationProjectionLedger
  exactLocal : ExactLocalProjectionLedger
  crossBlockLowerBound : CrossBlockLowerBoundProjectionLedger
  finalConsistency : FinalConsistencyProjectionLedger
  blockers : RoleHingeFinalIntegratedW11.BlockerFields

/-- Checked final role-hinge target aggregate. -/
def matrix : Matrix where
  fields := roleHingeTargetFieldLedger
  imports := importedMatrices
  equation := equationProjectionLedger
  exactLocal := exactLocalProjectionLedger
  crossBlockLowerBound := crossBlockLowerBoundProjectionLedger
  finalConsistency := finalConsistencyProjectionLedger
  blockers := RoleHingeFinalIntegratedW11.blockerFields

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public equation projections -/

theorem exactTarget_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    ExactTarget :=
  matrix.equation.roleEquation.exactTarget R

theorem eventualTarget_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    EventualTarget :=
  matrix.equation.roleEquation.eventualTarget R

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.equation.roleEquation.arbitraryTarget R

theorem exactTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    ExactTarget :=
  matrix.equation.roleEquationViaTransition.exactTarget R

theorem eventualTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    EventualTarget :=
  matrix.equation.roleEquationViaTransition.eventualTarget R

theorem arbitraryTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.equation.roleEquationViaTransition.arbitraryTarget R

theorem exactTarget_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    ExactTarget :=
  matrix.equation.ledgerCandidateAssembly.exactTarget L

theorem eventualTarget_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    EventualTarget :=
  matrix.equation.ledgerCandidateAssembly.eventualTarget L

theorem arbitraryTarget_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    ArbitraryTarget :=
  matrix.equation.ledgerCandidateAssembly.arbitraryTarget L

/-! ## Public exact-local projections -/

theorem exactTarget_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    ExactTarget :=
  matrix.exactLocal.routeFields.exactTarget R

theorem eventualTarget_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    EventualTarget :=
  matrix.exactLocal.routeFields.eventualTarget R

theorem arbitraryTarget_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    ArbitraryTarget :=
  matrix.exactLocal.routeFields.arbitraryTarget R

theorem exactTarget_of_exactLocalReducedEquations
    (S : ExactLocalSameOppositeEquationPackage)
    (R : ExactLocalTransitionRemainingFields S) :
    ExactTarget :=
  (matrix.exactLocal.reducedEquations S).exactTarget R

theorem eventualTarget_of_exactLocalReducedEquations
    (S : ExactLocalSameOppositeEquationPackage)
    (R : ExactLocalTransitionRemainingFields S) :
    EventualTarget :=
  (matrix.exactLocal.reducedEquations S).eventualTarget R

theorem arbitraryTarget_of_exactLocalReducedEquations
    (S : ExactLocalSameOppositeEquationPackage)
    (R : ExactLocalTransitionRemainingFields S) :
    ArbitraryTarget :=
  (matrix.exactLocal.reducedEquations S).arbitraryTarget R

/-! ## Public cross-block lower-bound projections -/

theorem exactTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundClosure F) :
    ExactTarget :=
  (matrix.crossBlockLowerBound.lowerBoundClosure F).exactTarget C

theorem eventualTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundClosure F) :
    EventualTarget :=
  (matrix.crossBlockLowerBound.lowerBoundClosure F).eventualTarget C

theorem arbitraryTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundClosure F) :
    ArbitraryTarget :=
  (matrix.crossBlockLowerBound.lowerBoundClosure F).arbitraryTarget C

theorem exactTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundFields F) :
    ExactTarget :=
  (matrix.crossBlockLowerBound.checkedLowerBoundFields F).exactTarget C

theorem eventualTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundFields F) :
    EventualTarget :=
  (matrix.crossBlockLowerBound.checkedLowerBoundFields F).eventualTarget C

theorem arbitraryTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.crossBlockLowerBound.checkedLowerBoundFields F).arbitraryTarget C

theorem exactTarget_of_rawCrossBlockInequalityLedger
    {F : LedgerPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    ExactTarget :=
  (matrix.crossBlockLowerBound.rawInequalityLedger F).exactTarget L

theorem eventualTarget_of_rawCrossBlockInequalityLedger
    {F : LedgerPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    EventualTarget :=
  (matrix.crossBlockLowerBound.rawInequalityLedger F).eventualTarget L

theorem arbitraryTarget_of_rawCrossBlockInequalityLedger
    {F : LedgerPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlockLowerBound.rawInequalityLedger F).arbitraryTarget L

theorem exactTarget_of_numericLedgerClosure
    {F : LedgerPeriodFamily}
    (L : NumericLedgerClosure F) :
    ExactTarget :=
  (matrix.crossBlockLowerBound.numericLedgerClosure F).exactTarget L

theorem eventualTarget_of_numericLedgerClosure
    {F : LedgerPeriodFamily}
    (L : NumericLedgerClosure F) :
    EventualTarget :=
  (matrix.crossBlockLowerBound.numericLedgerClosure F).eventualTarget L

theorem arbitraryTarget_of_numericLedgerClosure
    {F : LedgerPeriodFamily}
    (L : NumericLedgerClosure F) :
    ArbitraryTarget :=
  (matrix.crossBlockLowerBound.numericLedgerClosure F).arbitraryTarget L

theorem exactTarget_of_crossBlockClosureLedger
    {F : LedgerPeriodFamily}
    (C : CrossBlockClosureLedger F) :
    ExactTarget :=
  (matrix.crossBlockLowerBound.closureLedger F).exactTarget C

theorem eventualTarget_of_crossBlockClosureLedger
    {F : LedgerPeriodFamily}
    (C : CrossBlockClosureLedger F) :
    EventualTarget :=
  (matrix.crossBlockLowerBound.closureLedger F).eventualTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : LedgerPeriodFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.crossBlockLowerBound.closureLedger F).arbitraryTarget C

theorem exactTarget_of_roleHingeInequalityPackage
    {F : CrossBlockRoleHingeFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ExactTarget :=
  (matrix.crossBlockLowerBound.roleHingeInequalityPackage F).exactTarget R

theorem eventualTarget_of_roleHingeInequalityPackage
    {F : CrossBlockRoleHingeFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    EventualTarget :=
  (matrix.crossBlockLowerBound.roleHingeInequalityPackage F).eventualTarget R

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : CrossBlockRoleHingeFamily}
    (R : RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.crossBlockLowerBound.roleHingeInequalityPackage F).arbitraryTarget R

/-! ## Public final-consistency projections -/

theorem arbitraryTarget_viaFinalConsistency_of_transitionRouteFields
    (R : ConsistencyTransitionRouteFields) :
    ArbitraryTarget :=
  matrix.finalConsistency.transitionArbitrary R

theorem arbitraryTarget_viaFinalConsistency_of_generatedLowerBoundFields
    {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily}
    (C : GeneratedTargetIntegratedW11.LowerBoundFields F) :
    ArbitraryTarget :=
  matrix.finalConsistency.generatedLowerBoundArbitrary C

theorem arbitraryTarget_viaFinalConsistency_of_arbitraryNCrossBlockClosureLedger
    {F : ArbitraryNIntegratedW11.CrossBlockPeriodSearchFamily}
    (C : ArbitraryNIntegratedW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  matrix.finalConsistency.arbitraryNCrossBlockClosureArbitrary C

/-! ## Public blocker projections -/

theorem concreteFourTargetT11R_not_possible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r) :=
  matrix.blockers.t11rNotPossible

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    RoleHingeFinalIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.sameOppositeCandidateFields

theorem concreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.blockers.exactLocalMissingRows C

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

end

end RoleHingeTargetFinalW11
end PachToth
end ErdosProblems1066
