import ErdosProblems1066.PachToth.TransitionConsistencyW11
import ErdosProblems1066.PachToth.RoleHingeFinalIntegratedW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.ExactLocalFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final transition and role-hinge facade

This file gathers the checked W11 transition consistency ledger, the final
role-hinge aggregate, the final transition package aggregate, the final
exact-local aggregate, and the final Pach--Toth consistency ledger.

Every target conclusion below is a projection from an explicit route or
package value.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionRoleHingeFinalW11

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Shared package-indexed target rows -/

/-- Exact, fixed, eventual, and arbitrary targets from one package shape. -/
structure TargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

def projectionOfFinalRow
    {alpha : Type}
    (R : TransitionFinalIntegratedW11.FinalTargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfConsistencyRow
    {alpha : Sort u}
    (R : TransitionConsistencyW11.UnifiedTargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfThree
    {alpha : Sort u}
    (exactTarget : alpha -> ExactTarget)
    (eventualTarget : alpha -> EventualTarget)
    (arbitraryTarget : alpha -> ArbitraryTarget) :
    TargetProjection alpha where
  exactTarget := exactTarget
  fixedTarget := fun a n => arbitraryTarget a n
  eventualTarget := eventualTarget
  arbitraryTarget := arbitraryTarget

/-! ## Imported final ledgers -/

/-- Final W11 matrices used by this aggregate. -/
structure ImportedMatrices where
  transitionConsistency : TransitionConsistencyW11.Matrix
  roleHingeFinal : RoleHingeFinalIntegratedW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  exactLocalFinal : ExactLocalFinalIntegratedW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

def importedMatrices : ImportedMatrices where
  transitionConsistency := TransitionConsistencyW11.matrix
  roleHingeFinal := RoleHingeFinalIntegratedW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  exactLocalFinal := ExactLocalFinalIntegratedW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Explicit route packages -/

/-- Route and package ledgers exposed by the imported final layers. -/
structure ExplicitRoutePackages where
  transitionFinal : TransitionFinalIntegratedW11.ExplicitPackageLedger
  roleHingeEquationFields : RoleHingeFinalIntegratedW11.EquationFieldLedger
  roleHingeExactLocalFields : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger
  roleHingeCrossBlockFields :
    RoleHingeFinalIntegratedW11.CrossBlockLowerBoundFieldLedger
  transitionConsistencyRows : TransitionConsistencyW11.ProjectionRows
  exactLocalSources : ExactLocalFinalIntegratedW11.FinalSourceLedger
  pachTothOpenInputs : PachTothW11FinalConsistency.OpenInputLedgers

def explicitRoutePackages : ExplicitRoutePackages where
  transitionFinal := TransitionFinalIntegratedW11.explicitPackageLedger
  roleHingeEquationFields :=
    RoleHingeFinalIntegratedW11.equationFieldLedger
  roleHingeExactLocalFields :=
    RoleHingeFinalIntegratedW11.exactLocalFieldLedger
  roleHingeCrossBlockFields :=
    RoleHingeFinalIntegratedW11.crossBlockLowerBoundFieldLedger
  transitionConsistencyRows := TransitionConsistencyW11.projectionRows
  exactLocalSources := ExactLocalFinalIntegratedW11.finalSourceLedger
  pachTothOpenInputs := PachTothW11FinalConsistency.openInputLedgers

/-! ## Conditional projection routes -/

/-- Package-indexed target rows from the transition, role-hinge, and
exact-local final ledgers. -/
structure ProjectionRoutes where
  transitionConsistencyRoute :
    TargetProjection TransitionConsistencyW11.TransitionRouteFields
  transitionFinalRoute :
    TargetProjection TransitionFinalIntegratedW11.RoutePackage
  transitionFinalCandidate :
    TargetProjection TransitionFinalIntegratedW11.CandidatePackage
  transitionFinalRoleHinge :
    TargetProjection TransitionFinalIntegratedW11.RoleHingePackage
  transitionFinalPeriod :
    TargetProjection TransitionFinalIntegratedW11.PeriodPackage
  transitionFinalCrossBlock :
    TargetProjection TransitionFinalIntegratedW11.CrossBlockPackage
  transitionFinalPeriodBlock :
    TransitionFinalIntegratedW11.PeriodBlockTargetRow
  roleHingeEquationRoute :
    TargetProjection RoleHingeFinalIntegratedW11.RoleEquationRouteFields
  roleHingeLedgerCandidateAssembly :
    TargetProjection RoleHingeFinalIntegratedW11.RoleLedgerCandidateAssemblyFields
  roleHingeTransitionRoute :
    TargetProjection RoleHingeFinalIntegratedW11.TransitionRouteFields
  roleHingeExactLocalRoute :
    TargetProjection RoleHingeFinalIntegratedW11.ExactLocalRouteFields
  exactLocalFinalPackage :
    TargetProjection ExactLocalFinalIntegratedW11.FinalExactLocalPackage

def projectionRoutes : ProjectionRoutes where
  transitionConsistencyRoute :=
    projectionOfConsistencyRow TransitionConsistencyW11.checkedTransitionRouteRow
  transitionFinalRoute :=
    projectionOfFinalRow TransitionFinalIntegratedW11.routeTargetRow
  transitionFinalCandidate :=
    projectionOfFinalRow TransitionFinalIntegratedW11.candidateTargetRow
  transitionFinalRoleHinge :=
    projectionOfFinalRow TransitionFinalIntegratedW11.roleHingeTargetRow
  transitionFinalPeriod :=
    projectionOfFinalRow TransitionFinalIntegratedW11.periodTargetRow
  transitionFinalCrossBlock :=
    projectionOfFinalRow TransitionFinalIntegratedW11.crossBlockTargetRow
  transitionFinalPeriodBlock :=
    TransitionFinalIntegratedW11.periodBlockTargetRow
  roleHingeEquationRoute :=
    projectionOfThree
      RoleHingeFinalIntegratedW11.exactTarget_of_roleEquationRouteFields
      RoleHingeFinalIntegratedW11.eventualTarget_of_roleEquationRouteFields
      RoleHingeFinalIntegratedW11.arbitraryTarget_of_roleEquationRouteFields
  roleHingeLedgerCandidateAssembly :=
    projectionOfThree
      RoleHingeFinalIntegratedW11.exactTarget_of_roleLedgerCandidateAssemblyFields
      RoleHingeFinalIntegratedW11.eventualTarget_of_roleLedgerCandidateAssemblyFields
      RoleHingeFinalIntegratedW11.arbitraryTarget_of_roleLedgerCandidateAssemblyFields
  roleHingeTransitionRoute :=
    projectionOfThree
      RoleHingeFinalIntegratedW11.exactTarget_of_transitionRouteFields
      RoleHingeFinalIntegratedW11.eventualTarget_of_transitionRouteFields
      RoleHingeFinalIntegratedW11.arbitraryTarget_of_transitionRouteFields
  roleHingeExactLocalRoute :=
    projectionOfThree
      RoleHingeFinalIntegratedW11.exactTarget_of_exactLocalRouteFields
      RoleHingeFinalIntegratedW11.eventualTarget_of_exactLocalRouteFields
      RoleHingeFinalIntegratedW11.arbitraryTarget_of_exactLocalRouteFields
  exactLocalFinalPackage :=
    projectionOfThree
      ExactLocalFinalIntegratedW11.exactTarget_of_finalExactLocalPackage
      ExactLocalFinalIntegratedW11.eventualTarget_of_finalExactLocalPackage
      ExactLocalFinalIntegratedW11.arbitraryTarget_of_finalExactLocalPackage

/-! ## Cross-layer consistency witnesses -/

/-- Consistency rows retained from the imported final layers. -/
structure ConsistencyRoutes where
  transitionRoute :
    forall R : TransitionConsistencyW11.TransitionRouteFields,
      TransitionConsistencyW11.TransitionRouteConsistency R
  roleEquationRoute :
    forall R : TransitionConsistencyW11.RoleEquationRouteFields,
      TransitionConsistencyW11.RoleEquationRouteConsistency R
  crossBlockClosure :
    forall {F : TransitionConsistencyW11.CrossBlockPeriodSearchFamily}
      (C : TransitionConsistencyW11.CrossBlockClosureLedger F),
        TransitionConsistencyW11.CrossBlockClosureConsistency C
  exactLocalRoute :
    forall P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage,
      PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
        P.equations P.remaining
  roleHingePeriodRoute :
    forall R : RoleHingeClosureW11.EquationRouteFields,
      PachTothW11ConsistencyMatrix.RoleHingePeriodRouteConsistency R

def consistencyRoutes : ConsistencyRoutes where
  transitionRoute := TransitionConsistencyW11.matrix.transitionRoute
  roleEquationRoute := TransitionConsistencyW11.matrix.roleEquationRoute
  crossBlockClosure := fun C =>
    TransitionConsistencyW11.matrix.crossBlockClosure C
  exactLocalRoute := fun P =>
    ExactLocalFinalIntegratedW11.matrix.consistency.exactLocalRoute P
  roleHingePeriodRoute :=
    PachTothW11FinalConsistency.matrix.consistency.roleHingePeriodRoute

/-! ## Blockers -/

/-- Named blocker rows carried by the final transition and role-hinge facade. -/
structure BlockerFields where
  transitionConsistency : TransitionConsistencyW11.ExplicitBlockers
  roleHingeFinal : RoleHingeFinalIntegratedW11.BlockerFields
  transitionFinal : TransitionFinalIntegratedW11.BlockerProjections
  exactLocalFinal : ExactLocalFinalIntegratedW11.FinalEndpointBlockerLedger
  pachTothFinal : PachTothW11FinalConsistency.FinalBlockerLedger
  routeClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  completedFilteredRoute :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  sameOppositeCandidateFields :
    Not TransitionConsistencyW11.ConcreteSameOppositeCandidateFields
  missingCandidateRows :
    forall C : ExactLocalClosureW11.CandidateRows,
      Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C)
  fullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  endpointShortcut :
    forall E : ExactLocalFinalIntegratedW11.EndpointShortcutRow,
      Not (ExactLocalFinalIntegratedW11.PossibleRow E.u E.v)

def blockerFields : BlockerFields where
  transitionConsistency := TransitionConsistencyW11.explicitBlockers
  roleHingeFinal := RoleHingeFinalIntegratedW11.blockerFields
  transitionFinal := TransitionFinalIntegratedW11.blockerProjections
  exactLocalFinal := ExactLocalFinalIntegratedW11.finalEndpointBlockerLedger
  pachTothFinal := PachTothW11FinalConsistency.finalBlockerLedger
  routeClaim :=
    TransitionFinalIntegratedW11.checked_concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionFinalIntegratedW11.checked_concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    TransitionConsistencyW11.concreteFourTargetSameOppositeCandidateFields_blocked
  missingCandidateRows :=
    TransitionFinalIntegratedW11.checked_concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    TransitionFinalIntegratedW11.concreteFourTargetFullSameRestShortcut_blocked
  endpointShortcut :=
    ExactLocalFinalIntegratedW11.endpointShortcut_not_possible

/-! ## Final aggregate -/

/-- Final W11 transition/role-hinge consistency aggregate. -/
structure Matrix where
  imported : ImportedMatrices
  packages : ExplicitRoutePackages
  projections : ProjectionRoutes
  consistency : ConsistencyRoutes
  blockers : BlockerFields

def matrix : Matrix where
  imported := importedMatrices
  packages := explicitRoutePackages
  projections := projectionRoutes
  consistency := consistencyRoutes
  blockers := blockerFields

/-! ## Public package projections -/

theorem exactTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ExactTarget :=
  matrix.projections.transitionFinalRoute.exactTarget package

theorem fixedTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) (n : Nat) :
    FixedTarget n :=
  matrix.projections.transitionFinalRoute.fixedTarget package n

theorem eventualTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    EventualTarget :=
  matrix.projections.transitionFinalRoute.eventualTarget package

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionFinalRoute.arbitraryTarget package

theorem exactTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ExactTarget :=
  matrix.projections.transitionFinalRoleHinge.exactTarget package

theorem eventualTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    EventualTarget :=
  matrix.projections.transitionFinalRoleHinge.eventualTarget package

theorem arbitraryTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionFinalRoleHinge.arbitraryTarget package

theorem exactTarget_of_roleEquationRouteFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    ExactTarget :=
  matrix.projections.roleHingeEquationRoute.exactTarget R

theorem eventualTarget_of_roleEquationRouteFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    EventualTarget :=
  matrix.projections.roleHingeEquationRoute.eventualTarget R

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.projections.roleHingeEquationRoute.arbitraryTarget R

theorem exactTarget_of_exactLocalFinalPackage
    (package : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    ExactTarget :=
  matrix.projections.exactLocalFinalPackage.exactTarget package

theorem eventualTarget_of_exactLocalFinalPackage
    (package : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    EventualTarget :=
  matrix.projections.exactLocalFinalPackage.eventualTarget package

theorem arbitraryTarget_of_exactLocalFinalPackage
    (package : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.projections.exactLocalFinalPackage.arbitraryTarget package

def transitionRouteConsistency
    (R : TransitionConsistencyW11.TransitionRouteFields) :
    TransitionConsistencyW11.TransitionRouteConsistency R :=
  matrix.consistency.transitionRoute R

def roleEquationRouteConsistency
    (R : TransitionConsistencyW11.RoleEquationRouteFields) :
    TransitionConsistencyW11.RoleEquationRouteConsistency R :=
  matrix.consistency.roleEquationRoute R

def exactLocalRouteConsistency
    (package : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
      package.equations package.remaining :=
  matrix.consistency.exactLocalRoute package

/-! ## Public blocker projections -/

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not TransitionConsistencyW11.ConcreteSameOppositeCandidateFields :=
  matrix.blockers.sameOppositeCandidateFields

theorem concreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.blockers.missingCandidateRows C

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

theorem endpointShortcut_not_possible
    (E : ExactLocalFinalIntegratedW11.EndpointShortcutRow) :
    Not (ExactLocalFinalIntegratedW11.PossibleRow E.u E.v) :=
  matrix.blockers.endpointShortcut E

end

end TransitionRoleHingeFinalW11
end PachToth
end ErdosProblems1066
