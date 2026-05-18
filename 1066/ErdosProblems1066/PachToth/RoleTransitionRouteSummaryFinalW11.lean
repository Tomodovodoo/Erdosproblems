import ErdosProblems1066.PachToth.RoleHingeRouteSummaryFinalW11
import ErdosProblems1066.PachToth.TransitionRoleTargetFinalW11
import ErdosProblems1066.PachToth.TransitionRoleHingeFinalW11

set_option autoImplicit false

/-!
# W11 final role/transition route summary

This leaf module records the checked role-hinge and transition-role target
facades, displays the route package shapes explicitly, and exposes target
facts only as projections from supplied packages or field ledgers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleTransitionRouteSummaryFinalW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev TransitionRoutePackage :=
  TransitionFinalIntegratedW11.RoutePackage

abbrev TransitionCandidatePackage :=
  TransitionFinalIntegratedW11.CandidatePackage

abbrev TransitionRoleHingePackage :=
  TransitionFinalIntegratedW11.RoleHingePackage

abbrev TransitionPeriodPackage :=
  TransitionFinalIntegratedW11.PeriodPackage

abbrev TransitionCrossBlockPackage :=
  TransitionFinalIntegratedW11.CrossBlockPackage

abbrev ExactLocalFinalPackage :=
  ExactLocalFinalIntegratedW11.FinalExactLocalPackage

abbrev RoleEquationFinalFields :=
  RoleHingeFinalIntegratedW11.RoleEquationRouteFields

abbrev RoleLedgerCandidateFinalFields :=
  RoleHingeFinalIntegratedW11.RoleLedgerCandidateAssemblyFields

abbrev RoleTransitionFinalFields :=
  RoleHingeFinalIntegratedW11.TransitionRouteFields

abbrev RoleEquationTargetFields :=
  RoleHingeTargetFinalW11.RoleEquationRouteFields

abbrev RoleLedgerCandidateTargetFields :=
  RoleHingeTargetFinalW11.RoleLedgerCandidateAssemblyFields

abbrev RoleExactLocalTargetFields :=
  RoleHingeTargetFinalW11.ExactLocalRouteFields

/-! ## Checked ledgers -/

/-- Imported checked W11 role and transition ledgers. -/
structure CheckedLedgers where
  roleHingeRoute : RoleHingeRouteSummaryFinalW11.Matrix
  transitionRoleTarget : TransitionRoleTargetFinalW11.Matrix
  transitionRoleHinge : TransitionRoleHingeFinalW11.Matrix

/-- Checked ledgers summarized by this route facade. -/
def checkedLedgers : CheckedLedgers where
  roleHingeRoute := RoleHingeRouteSummaryFinalW11.matrix
  transitionRoleTarget := TransitionRoleTargetFinalW11.matrix
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix

/-! ## Explicit package shapes -/

/-- Route package families carried by the summary. -/
structure PackageTypes where
  transitionRoute : Type
  transitionCandidate : Type
  transitionRoleHinge : Type
  transitionPeriod : Type
  transitionCrossBlock : Type
  exactLocalFinal : Type
  roleEquationFinal : Type
  roleLedgerCandidateFinal : Type
  roleTransitionFinal : Type
  roleEquationTarget : Type
  roleLedgerCandidateTarget : Type
  roleExactLocalTarget : Type
  roleHingePeriodFamily : Type
  ledgerPeriodFamily : Type
  roleHingeCrossBlockFamily : Type

/-- Explicit package families used by the role/transition route. -/
def packageTypes : PackageTypes where
  transitionRoute := TransitionRoutePackage
  transitionCandidate := TransitionCandidatePackage
  transitionRoleHinge := TransitionRoleHingePackage
  transitionPeriod := TransitionPeriodPackage
  transitionCrossBlock := TransitionCrossBlockPackage
  exactLocalFinal := ExactLocalFinalPackage
  roleEquationFinal := RoleEquationFinalFields
  roleLedgerCandidateFinal := RoleLedgerCandidateFinalFields
  roleTransitionFinal := RoleTransitionFinalFields
  roleEquationTarget := RoleEquationTargetFields
  roleLedgerCandidateTarget := RoleLedgerCandidateTargetFields
  roleExactLocalTarget := RoleExactLocalTargetFields
  roleHingePeriodFamily := RoleHingeTargetFinalW11.RoleHingePeriodFamily
  ledgerPeriodFamily := RoleHingeTargetFinalW11.LedgerPeriodFamily
  roleHingeCrossBlockFamily :=
    RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily

/-- Explicit ledgers and package shapes retained by the summary. -/
structure ExplicitPackages where
  packageTypes : PackageTypes
  roleHingeRouteFields : RoleHingeRouteSummaryFinalW11.ExplicitRouteFields
  transitionRoleTargetSources : TransitionRoleTargetFinalW11.SourceLedger
  transitionRoleHingePackages : TransitionRoleHingeFinalW11.ExplicitRoutePackages
  transitionFinalPackages : TransitionFinalIntegratedW11.ExplicitPackageLedger
  aggregateOpenData : PachTothW11FinalAggregate.ExplicitOpenData
  consistencyOpenInputs : PachTothW11FinalConsistency.OpenInputLedgers

/-- Explicit packages and ledgers imported by this facade. -/
def explicitPackages : ExplicitPackages where
  packageTypes := packageTypes
  roleHingeRouteFields := RoleHingeRouteSummaryFinalW11.explicitRouteFields
  transitionRoleTargetSources := TransitionRoleTargetFinalW11.sourceLedger
  transitionRoleHingePackages := TransitionRoleHingeFinalW11.explicitRoutePackages
  transitionFinalPackages := TransitionFinalIntegratedW11.explicitPackageLedger
  aggregateOpenData := PachTothW11FinalAggregate.explicitOpenData
  consistencyOpenInputs := PachTothW11FinalConsistency.openInputLedgers

/-! ## Conditional projections -/

/-- Role-hinge and transition target projections retained by the summary. -/
structure ProjectionMatrix where
  transitionRoute :
    TransitionRoleTargetFinalW11.ConditionalTargetProjection
      TransitionRoutePackage
  transitionRoleHinge :
    TransitionRoleTargetFinalW11.ConditionalTargetProjection
      TransitionRoleHingePackage
  transitionCandidateAggregate :
    TransitionRoleTargetFinalW11.ConditionalArbitraryProjection
      TransitionCandidatePackage
  transitionRouteAggregate :
    TransitionRoleTargetFinalW11.ConditionalArbitraryProjection
      TransitionRoutePackage
  roleEquationFinal :
    TransitionRoleTargetFinalW11.ConditionalTargetProjection
      RoleEquationFinalFields
  roleLedgerCandidateFinal :
    TransitionRoleTargetFinalW11.ConditionalTargetProjection
      RoleLedgerCandidateFinalFields
  roleTransitionFinal :
    TransitionRoleTargetFinalW11.ConditionalTargetProjection
      RoleTransitionFinalFields
  exactLocalFinal :
    TransitionRoleTargetFinalW11.ConditionalTargetProjection
      ExactLocalFinalPackage
  roleEquationTarget :
    RoleHingeRouteSummaryFinalW11.ConditionalProjection
      RoleEquationTargetFields
  roleLedgerCandidateTarget :
    RoleHingeRouteSummaryFinalW11.ConditionalProjection
      RoleLedgerCandidateTargetFields
  roleExactLocalTarget :
    RoleHingeRouteSummaryFinalW11.ConditionalProjection
      RoleExactLocalTargetFields
  roleCrossBlockLowerBound :
    forall F : RoleHingeTargetFinalW11.RoleHingePeriodFamily,
      RoleHingeRouteSummaryFinalW11.ConditionalProjection
        (RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundClosure F)
  rawCrossBlockInequality :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      RoleHingeRouteSummaryFinalW11.ConditionalProjection
        (RoleHingeTargetFinalW11.RawCrossBlockInequalityLedger F)
  numericLedgerClosure :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      RoleHingeRouteSummaryFinalW11.ConditionalProjection
        (RoleHingeTargetFinalW11.NumericLedgerClosure F)
  roleHingeInequalityPackage :
    forall F : RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily,
      RoleHingeRouteSummaryFinalW11.ConditionalProjection
        (RoleHingeTargetFinalW11.RoleHingeCrossBlockInequalityPackage F)

/-- Checked conditional role/transition projections. -/
def projectionMatrix : ProjectionMatrix where
  transitionRoute :=
    TransitionRoleTargetFinalW11.matrix.transitionRoleExact.transitionRoute
  transitionRoleHinge :=
    TransitionRoleTargetFinalW11.matrix.transitionRoleExact.transitionRoleHinge
  transitionCandidateAggregate :=
    TransitionRoleTargetFinalW11.matrix.pachTothAggregate.transitionCandidate
  transitionRouteAggregate :=
    TransitionRoleTargetFinalW11.matrix.pachTothAggregate.transitionRoute
  roleEquationFinal :=
    TransitionRoleTargetFinalW11.matrix.transitionRoleExact.roleEquation
  roleLedgerCandidateFinal :=
    TransitionRoleTargetFinalW11.matrix.transitionRoleExact
      |>.roleLedgerCandidateAssembly
  roleTransitionFinal :=
    TransitionRoleTargetFinalW11.matrix.transitionRoleExact.roleTransition
  exactLocalFinal :=
    TransitionRoleTargetFinalW11.matrix.transitionRoleExact.exactLocal
  roleEquationTarget :=
    RoleHingeRouteSummaryFinalW11.matrix.equation.roleEquation
  roleLedgerCandidateTarget :=
    RoleHingeRouteSummaryFinalW11.matrix.equation.ledgerCandidateAssembly
  roleExactLocalTarget :=
    RoleHingeRouteSummaryFinalW11.matrix.exactLocal.routeFields
  roleCrossBlockLowerBound :=
    RoleHingeRouteSummaryFinalW11.matrix.crossBlock.lowerBoundClosure
  rawCrossBlockInequality :=
    RoleHingeRouteSummaryFinalW11.matrix.crossBlock.rawInequalityLedger
  numericLedgerClosure :=
    RoleHingeRouteSummaryFinalW11.matrix.crossBlock.numericLedgerClosure
  roleHingeInequalityPackage :=
    RoleHingeRouteSummaryFinalW11.matrix.crossBlock.roleHingeInequalityPackage

/-! ## Blockers -/

/-- Named blockers carried by the final role/transition route. -/
structure BlockerLedger where
  roleHingeRoute : TransitionRoleHingeFinalW11.BlockerFields
  transitionRoleTarget : TransitionRoleTargetFinalW11.BlockerLedger
  transitionRoleHinge : TransitionRoleHingeFinalW11.BlockerFields
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

/-- Checked blocker ledger for shortcut and missing-row routes. -/
def blockerLedger : BlockerLedger where
  roleHingeRoute := RoleHingeRouteSummaryFinalW11.matrix.blockers
  transitionRoleTarget := TransitionRoleTargetFinalW11.matrix.blockers
  transitionRoleHinge := TransitionRoleHingeFinalW11.blockerFields
  routeClaim := TransitionRoleTargetFinalW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionRoleTargetFinalW11.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    TransitionRoleTargetFinalW11.concreteFourTargetSameOppositeCandidateFields_blocked
  missingCandidateRows :=
    TransitionRoleTargetFinalW11.concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    TransitionRoleTargetFinalW11.concreteFourTargetFullSameRestShortcut_blocked
  endpointShortcut := TransitionRoleTargetFinalW11.endpointShortcut_not_possible

/-! ## Final matrix -/

/-- Concise checked final role/transition route summary. -/
structure Matrix where
  checked : CheckedLedgers
  packages : ExplicitPackages
  projections : ProjectionMatrix
  blockers : BlockerLedger

/-- The checked W11 final role/transition route summary. -/
def matrix : Matrix where
  checked := checkedLedgers
  packages := explicitPackages
  projections := projectionMatrix
  blockers := blockerLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public transition projections -/

theorem exactTarget_of_transitionRoutePackage
    (package : TransitionRoutePackage) :
    ExactTarget :=
  matrix.projections.transitionRoute.exactTarget package

theorem fixedTarget_of_transitionRoutePackage
    (package : TransitionRoutePackage) (n : Nat) :
    FixedTarget n :=
  matrix.projections.transitionRoute.fixedTarget package n

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionRoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoute.arbitraryTarget package

theorem arbitraryTarget_of_transitionRoleHingePackage
    (package : TransitionRoleHingePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleHinge.arbitraryTarget package

theorem arbitraryTarget_viaAggregate_of_transitionRoutePackage
    (package : TransitionRoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRouteAggregate.arbitraryTarget package

theorem arbitraryTarget_viaAggregate_of_transitionCandidatePackage
    (package : TransitionCandidatePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionCandidateAggregate.arbitraryTarget package

/-! ## Public role projections -/

theorem arbitraryTarget_of_roleEquationFinalFields
    (fields : RoleEquationFinalFields) :
    ArbitraryTarget :=
  matrix.projections.roleEquationFinal.arbitraryTarget fields

theorem arbitraryTarget_of_roleLedgerCandidateFinalFields
    (fields : RoleLedgerCandidateFinalFields) :
    ArbitraryTarget :=
  matrix.projections.roleLedgerCandidateFinal.arbitraryTarget fields

theorem arbitraryTarget_of_roleTransitionFinalFields
    (fields : RoleTransitionFinalFields) :
    ArbitraryTarget :=
  matrix.projections.roleTransitionFinal.arbitraryTarget fields

theorem exactTarget_of_exactLocalFinalPackage
    (package : ExactLocalFinalPackage) :
    ExactTarget :=
  matrix.projections.exactLocalFinal.exactTarget package

theorem arbitraryTarget_of_exactLocalFinalPackage
    (package : ExactLocalFinalPackage) :
    ArbitraryTarget :=
  matrix.projections.exactLocalFinal.arbitraryTarget package

theorem arbitraryTarget_of_roleEquationTargetFields
    (fields : RoleEquationTargetFields) :
    ArbitraryTarget :=
  matrix.projections.roleEquationTarget.arbitraryTarget fields

theorem arbitraryTarget_of_roleExactLocalTargetFields
    (fields : RoleExactLocalTargetFields) :
    ArbitraryTarget :=
  matrix.projections.roleExactLocalTarget.arbitraryTarget fields

/-! ## Public cross-block projections -/

theorem arbitraryTarget_of_roleCrossBlockLowerBound
    {F : RoleHingeTargetFinalW11.RoleHingePeriodFamily}
    (fields : RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundClosure F) :
    ArbitraryTarget :=
  (matrix.projections.roleCrossBlockLowerBound F).arbitraryTarget fields

theorem arbitraryTarget_of_rawCrossBlockInequality
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (fields : RoleHingeTargetFinalW11.RawCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.projections.rawCrossBlockInequality F).arbitraryTarget fields

theorem arbitraryTarget_of_numericLedgerClosure
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (fields : RoleHingeTargetFinalW11.NumericLedgerClosure F) :
    ArbitraryTarget :=
  (matrix.projections.numericLedgerClosure F).arbitraryTarget fields

theorem arbitraryTarget_of_roleHingeInequalityPackage
    {F : RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily}
    (fields : RoleHingeTargetFinalW11.RoleHingeCrossBlockInequalityPackage F) :
    ArbitraryTarget :=
  (matrix.projections.roleHingeInequalityPackage F).arbitraryTarget fields

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

end RoleTransitionRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
