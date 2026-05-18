import ErdosProblems1066.PachToth.PachTothW11RouteSummaryFinal
import ErdosProblems1066.PachToth.PachTothFinalRouteLedgerW11
import ErdosProblems1066.PachToth.TransitionPeriodRouteSummaryFinalW11
import ErdosProblems1066.PachToth.TransitionRoleLedgerFinalW11
import ErdosProblems1066.PachToth.GeneratedCrossBlockSummaryFinalW11
import ErdosProblems1066.PachToth.ArbitraryNRouteSummaryFinalW11

set_option autoImplicit false
set_option linter.style.longLine false

/-!
Terminal W11 Pach--Toth route summary ledger.

This file only records checked final route ledgers, explicit open data, and
target conclusions as projections from displayed source packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothTerminalRouteSummaryW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! Requested route-summary availability. -/

inductive SummaryStatus where
  | present
  | absent
deriving DecidableEq

structure RequestedSummaryAvailability where
  pachTothRouteSummaryFinal : SummaryStatus
  pachTothFinalRouteLedger : SummaryStatus
  transitionPeriodRouteSummary : SummaryStatus
  transitionRoleLedger : SummaryStatus
  smallArbitraryRouteSummary : SummaryStatus
  generatedCrossBlockSummary : SummaryStatus
  arbitraryNRouteSummary : SummaryStatus

def requestedSummaryAvailability : RequestedSummaryAvailability where
  pachTothRouteSummaryFinal := SummaryStatus.present
  pachTothFinalRouteLedger := SummaryStatus.present
  transitionPeriodRouteSummary := SummaryStatus.present
  transitionRoleLedger := SummaryStatus.present
  smallArbitraryRouteSummary := SummaryStatus.absent
  generatedCrossBlockSummary := SummaryStatus.present
  arbitraryNRouteSummary := SummaryStatus.present

theorem smallArbitraryRouteSummary_absent :
    requestedSummaryAvailability.smallArbitraryRouteSummary =
      SummaryStatus.absent :=
  rfl

theorem generatedCrossBlockSummary_present :
    requestedSummaryAvailability.generatedCrossBlockSummary =
      SummaryStatus.present :=
  rfl

/-! Imported checked ledgers. -/

structure ImportedLedgers where
  pachTothRouteSummary :
    PachTothW11RouteSummaryFinal.Matrix
  pachTothFinalRouteLedger :
    PachTothFinalRouteLedgerW11.Matrix
  transitionPeriodRouteSummary :
    TransitionPeriodRouteSummaryFinalW11.Matrix
  transitionRoleLedger :
    TransitionRoleLedgerFinalW11.Matrix
  generatedCrossBlockSummary :
    GeneratedCrossBlockSummaryFinalW11.Matrix
  arbitraryNRouteSummary :
    ArbitraryNRouteSummaryFinalW11.Matrix

def importedLedgers : ImportedLedgers where
  pachTothRouteSummary := PachTothW11RouteSummaryFinal.matrix
  pachTothFinalRouteLedger := PachTothFinalRouteLedgerW11.matrix
  transitionPeriodRouteSummary :=
    TransitionPeriodRouteSummaryFinalW11.matrix
  transitionRoleLedger := TransitionRoleLedgerFinalW11.matrix
  generatedCrossBlockSummary := GeneratedCrossBlockSummaryFinalW11.matrix
  arbitraryNRouteSummary := ArbitraryNRouteSummaryFinalW11.matrix

/-! Explicit open data. -/

structure ExplicitOpenData where
  availability : RequestedSummaryAvailability
  pachTothRouteSummary :
    PachTothW11RouteSummaryFinal.ExplicitOpenData
  pachTothFinalRouteLedger :
    PachTothFinalRouteLedgerW11.ExplicitOpenData
  transitionPeriod :
    TransitionPeriodRouteSummaryFinalW11.ExplicitPackageLedger
  transitionRole :
    TransitionRoleLedgerFinalW11.ExplicitPackageLedger
  generatedCrossBlockChecked :
    GeneratedCrossBlockSummaryFinalW11.CheckedLedgers
  generatedCrossBlockNumeric :
    GeneratedCrossBlockSummaryFinalW11.NumericFieldSummary
  arbitraryNRouteSummary :
    ArbitraryNRouteSummaryFinalW11.RouteSourceSummary

def explicitOpenData : ExplicitOpenData where
  availability := requestedSummaryAvailability
  pachTothRouteSummary := PachTothW11RouteSummaryFinal.explicitOpenData
  pachTothFinalRouteLedger := PachTothFinalRouteLedgerW11.explicitOpenData
  transitionPeriod :=
    TransitionPeriodRouteSummaryFinalW11.explicitPackageLedger
  transitionRole := TransitionRoleLedgerFinalW11.explicitPackageLedger
  generatedCrossBlockChecked :=
    GeneratedCrossBlockSummaryFinalW11.checkedLedgers
  generatedCrossBlockNumeric :=
    GeneratedCrossBlockSummaryFinalW11.numericFieldSummary
  arbitraryNRouteSummary := ArbitraryNRouteSummaryFinalW11.routeSourceSummary

/-! Conditional target projection ledgers. -/

structure ConditionalTargetProjections where
  pachTothRouteSummary :
    PachTothW11RouteSummaryFinal.ConditionalProjectionMatrix
  pachTothFinalRouteLedger :
    PachTothFinalRouteLedgerW11.ConditionalRouteLedger
  transitionPeriod :
    TransitionPeriodRouteSummaryFinalW11.ConditionalProjectionMatrix
  transitionRoleTransition :
    TransitionRoleLedgerFinalW11.TransitionProjectionLedger
  transitionRoleFields :
    TransitionRoleLedgerFinalW11.RoleProjectionLedger
  transitionRoleAggregate :
    TransitionRoleLedgerFinalW11.AggregateProjectionLedger
  generated :
    GeneratedCrossBlockSummaryFinalW11.GeneratedProjectionSummary
  crossBlock :
    GeneratedCrossBlockSummaryFinalW11.CrossBlockProjectionSummary
  generatedCrossBlockAggregate :
    GeneratedCrossBlockSummaryFinalW11.AggregateProjectionSummary
  arbitraryNExact :
    ArbitraryNTargetFinalW11.ExactFields
  arbitraryNEventual :
    ArbitraryNTargetFinalW11.EventualFields
  arbitraryNSmall :
    ArbitraryNFinalAggregateW11.SmallLengthRouteData
  arbitraryNGenerated :
    ArbitraryNFinalAggregateW11.GeneratedRouteData
  arbitraryNCrossBlock :
    ArbitraryNFinalAggregateW11.CrossBlockRouteData

def conditionalTargetProjections : ConditionalTargetProjections where
  pachTothRouteSummary :=
    PachTothW11RouteSummaryFinal.conditionalProjectionMatrix
  pachTothFinalRouteLedger :=
    PachTothFinalRouteLedgerW11.conditionalRouteLedger
  transitionPeriod :=
    TransitionPeriodRouteSummaryFinalW11.conditionalProjectionMatrix
  transitionRoleTransition :=
    TransitionRoleLedgerFinalW11.transitionProjectionLedger
  transitionRoleFields :=
    TransitionRoleLedgerFinalW11.roleProjectionLedger
  transitionRoleAggregate :=
    TransitionRoleLedgerFinalW11.aggregateProjectionLedger
  generated :=
    GeneratedCrossBlockSummaryFinalW11.generatedProjectionSummary
  crossBlock :=
    GeneratedCrossBlockSummaryFinalW11.crossBlockProjectionSummary
  generatedCrossBlockAggregate :=
    GeneratedCrossBlockSummaryFinalW11.aggregateProjectionSummary
  arbitraryNExact :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.exact.targetRoutes
  arbitraryNEventual :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.eventual.targetRoutes
  arbitraryNSmall :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.small.routes
  arbitraryNGenerated :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.generated.routes
  arbitraryNCrossBlock :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.crossBlock.routes

/-! Blockers retained beside the route projections. -/

structure BlockerLedger where
  pachTothRouteSummary :
    PachTothW11RouteSummaryFinal.BlockerLedger
  pachTothFinalRouteLedger :
    PachTothFinalRouteLedgerW11.BlockerLedger
  transitionRole :
    TransitionRoleLedgerFinalW11.BlockerFields
  generatedCrossBlock :
    GeneratedTargetIntegratedW11.TransitionBlockers
  arbitraryNFinalConsistency :
    PachTothW11FinalConsistency.FinalBlockerLedger

def blockerLedger : BlockerLedger where
  pachTothRouteSummary := PachTothW11RouteSummaryFinal.blockerLedger
  pachTothFinalRouteLedger := PachTothFinalRouteLedgerW11.blockerLedger
  transitionRole := TransitionRoleLedgerFinalW11.blockerFields
  generatedCrossBlock := GeneratedCrossBlockSummaryFinalW11.matrix.blockers
  arbitraryNFinalConsistency :=
    ArbitraryNRouteSummaryFinalW11.matrix.consistency.blockers

/-! Terminal matrix. -/

structure Matrix where
  imported : ImportedLedgers
  openData : ExplicitOpenData
  projections : ConditionalTargetProjections
  blockers : BlockerLedger

def matrix : Matrix where
  imported := importedLedgers
  openData := explicitOpenData
  projections := conditionalTargetProjections
  blockers := blockerLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! Public availability fields. -/

theorem matrix_smallArbitraryRouteSummary_absent :
    matrix.openData.availability.smallArbitraryRouteSummary =
      SummaryStatus.absent :=
  rfl

theorem matrix_generatedCrossBlockSummary_present :
    matrix.openData.availability.generatedCrossBlockSummary =
      SummaryStatus.present :=
  rfl

/-! Public conditional projection wrappers. -/

theorem arbitraryTarget_of_pachTothRoute_transitionRoute
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.pachTothRouteSummary.transitionRoute.arbitraryTarget
    package

theorem arbitraryTarget_of_terminalFinal_transitionPeriod
    (package : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.projections.pachTothFinalRouteLedger.routeSummary.transitionPeriod
    |>.arbitraryTarget package

theorem arbitraryTarget_of_transitionPeriod_routePackage
    (package : TransitionPeriodRouteSummaryFinalW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionPeriod.route.arbitraryTarget package

theorem arbitraryTarget_of_transitionRole_routePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleTransition.route.arbitraryTarget package

theorem exactTarget_of_transitionRole_roleEquation
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ExactTarget :=
  matrix.projections.transitionRoleFields.equation.exactTarget R

theorem arbitraryTarget_of_transitionRole_exactLocalRoute
    (R : RoleHingeTargetFinalW11.ExactLocalRouteFields) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleFields.exactLocalRoute.arbitraryTarget R

theorem arbitraryTarget_of_arbitraryNExactAssumptions
    (A : ArbitraryNRouteSummaryFinalW11.ExactTargetAssumptions) :
    ArbitraryTarget :=
  matrix.projections.arbitraryNExact.exactAssumptions.arbitraryTarget A

theorem arbitraryTarget_of_arbitraryNExactClosedChains
    (P : ArbitraryNRouteSummaryFinalW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryNExact.closedChains.arbitraryTarget P

theorem largeTarget_of_arbitraryNEventualClosedChains
    (P : ArbitraryNRouteSummaryFinalW11.EventualClosedChainPackage)
    (n : Nat)
    (hn :
      matrix.projections.arbitraryNEventual.closedChains.vertexThreshold P <=
        n) :
    FixedTarget n :=
  matrix.projections.arbitraryNEventual.closedChains.largeTarget P n hn

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedCrossBlockSummaryFinalW11.GeneratedPointFamily}
    (C : GeneratedCrossBlockSummaryFinalW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.projections.generated.lowerBound F).arbitraryTarget C

theorem arbitraryTarget_of_generatedCrossBlockClosure
    {F : GeneratedCrossBlockSummaryFinalW11.GeneratedCrossBlockFamily}
    (C :
      GeneratedCrossBlockSummaryFinalW11.GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.projections.generated.crossBlockClosure F).arbitraryTarget C

theorem arbitraryTarget_of_crossBlockClosure
    {F : GeneratedCrossBlockSummaryFinalW11.CrossBlockFamily}
    (C : GeneratedCrossBlockSummaryFinalW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.projections.crossBlock.closureLedgers F).arbitraryTarget C

theorem arbitraryTarget_viaFinalLedger_of_generatedCrossBlockClosure
    {F : GeneratedCrossBlockFinalW11.GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockFinalW11.GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.projections.pachTothFinalRouteLedger.generatedViaArbitraryN
    |>.generatedCrossBlockClosure F)
    |>.arbitraryTarget C

/-! Public blocker wrappers. -/

theorem transitionRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.pachTothFinalRouteLedger.routeSummary.transitionRouteClaim

theorem completedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.pachTothFinalRouteLedger.routeSummary.completedFilteredRoute

theorem fullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.pachTothFinalRouteLedger.routeSummary.fullSameRestShortcut

end

end PachTothTerminalRouteSummaryW11
end PachToth
end ErdosProblems1066
