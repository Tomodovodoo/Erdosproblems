import ErdosProblems1066.PachToth.PachTothBlockerSummaryFinalW11
import ErdosProblems1066.PachToth.PachTothW11RouteSummaryFinal
import ErdosProblems1066.PachToth.TransitionRoleTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false

/-!
# W11 terminal Pach--Toth blocker and open-data summary

This file is a terminal facade over the checked W11 Pach--Toth blocker,
route, transition-role, and aggregate summaries.  It records the imported
matrices, the displayed open-data ledgers, the terminal blocker rows, and only
package- or field-indexed target projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothTerminalBlockerSummaryW11

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

/-! ## Imported terminal ledgers -/

/-- Checked W11 ledgers summarized by this terminal facade. -/
structure ImportedTerminalLedgers where
  blockerSummary : PachTothBlockerSummaryFinalW11.Matrix
  routeSummary : PachTothW11RouteSummaryFinal.Matrix
  transitionRoleTarget : TransitionRoleTargetFinalW11.Matrix
  finalAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked W11 terminal ledgers. -/
def importedTerminalLedgers : ImportedTerminalLedgers where
  blockerSummary := PachTothBlockerSummaryFinalW11.matrix
  routeSummary := PachTothW11RouteSummaryFinal.matrix
  transitionRoleTarget := TransitionRoleTargetFinalW11.matrix
  finalAggregate := PachTothW11FinalAggregate.matrix

/-! ## Terminal open-data summary -/

/-- Open-data ledgers retained by the terminal facade. -/
structure TerminalOpenData where
  blockerExactLocal : PachTothBlockerSummaryFinalW11.ExactLocalMissingDataLedger
  blockerNumeric : PachTothBlockerSummaryFinalW11.NumericMissingDataLedger
  blockerPeriod : PachTothBlockerSummaryFinalW11.PeriodMissingDataLedger
  routeSummary : PachTothW11RouteSummaryFinal.ExplicitOpenData
  transitionRoleSources : TransitionRoleTargetFinalW11.SourceLedger
  aggregate : PachTothW11FinalAggregate.ExplicitOpenData
  aggregateAvailability : PachTothW11FinalAggregate.FinalLedgerAvailability
  periodFinalStatus :
    aggregateAvailability.periodFinal =
      PachTothW11FinalAggregate.LedgerAvailability.absent

/-- Combined open-data summary for the terminal facade. -/
def terminalOpenData : TerminalOpenData where
  blockerExactLocal := PachTothBlockerSummaryFinalW11.matrix.exactLocal
  blockerNumeric := PachTothBlockerSummaryFinalW11.matrix.numeric
  blockerPeriod := PachTothBlockerSummaryFinalW11.matrix.period
  routeSummary := PachTothW11RouteSummaryFinal.matrix.openData
  transitionRoleSources := TransitionRoleTargetFinalW11.matrix.sources
  aggregate := PachTothW11FinalAggregate.matrix.openData
  aggregateAvailability := PachTothW11FinalAggregate.finalLedgerAvailability
  periodFinalStatus := PachTothW11FinalAggregate.periodFinalIntegratedW11_absent

/-! ## Terminal blocker summary -/

/-- Blocker rows collected from the terminal W11 summaries. -/
structure TerminalBlockerLedger where
  blockerSummary : PachTothBlockerSummaryFinalW11.ConcreteShortcutBlockerLedger
  routeSummary : PachTothW11RouteSummaryFinal.BlockerLedger
  transitionRoleTarget : TransitionRoleTargetFinalW11.BlockerLedger
  aggregate : PachTothW11FinalConsistency.FinalBlockerLedger
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
  exactLocalEndpointShortcut :
    forall E : ExactLocalTargetFinalW11.EndpointShortcutRow,
      Not (ExactLocalTargetFinalW11.PossibleRow E.u E.v)
  finalEndpointShortcut :
    forall E : ExactLocalFinalIntegratedW11.EndpointShortcutRow,
      Not (ExactLocalFinalIntegratedW11.PossibleRow E.u E.v)
  pUpperForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_1)
  pUpperReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.T2_2)
  pLowerForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_2)
  pLowerReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T1_2 FiniteGraph.LocalVertex.T2_2)
  qUpperForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_0)
  qUpperReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_0 FiniteGraph.LocalVertex.T4_0)
  qLowerForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_2)
  qLowerReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_2 FiniteGraph.LocalVertex.T4_0)

/-- Terminal blocker ledger. -/
def terminalBlockerLedger : TerminalBlockerLedger where
  blockerSummary := PachTothBlockerSummaryFinalW11.matrix.shortcuts
  routeSummary := PachTothW11RouteSummaryFinal.matrix.blockers
  transitionRoleTarget := TransitionRoleTargetFinalW11.matrix.blockers
  aggregate := PachTothW11FinalAggregate.matrix.blockers
  routeClaim := PachTothBlockerSummaryFinalW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    PachTothBlockerSummaryFinalW11.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    PachTothBlockerSummaryFinalW11.concreteFourTargetSameOppositeCandidateFields_blocked
  missingCandidateRows :=
    PachTothBlockerSummaryFinalW11.concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    PachTothBlockerSummaryFinalW11.concreteFourTargetFullSameRestShortcut_blocked
  exactLocalEndpointShortcut :=
    PachTothBlockerSummaryFinalW11.endpointShortcut_not_possible
  finalEndpointShortcut := TransitionRoleTargetFinalW11.endpointShortcut_not_possible
  pUpperForward :=
    PachTothBlockerSummaryFinalW11.pUpperForward_endpointShortcut_not_possible
  pUpperReverse :=
    PachTothBlockerSummaryFinalW11.pUpperReverse_endpointShortcut_not_possible
  pLowerForward :=
    PachTothBlockerSummaryFinalW11.pLowerForward_endpointShortcut_not_possible
  pLowerReverse :=
    PachTothBlockerSummaryFinalW11.pLowerReverse_endpointShortcut_not_possible
  qUpperForward :=
    PachTothBlockerSummaryFinalW11.qUpperForward_endpointShortcut_not_possible
  qUpperReverse :=
    PachTothBlockerSummaryFinalW11.qUpperReverse_endpointShortcut_not_possible
  qLowerForward :=
    PachTothBlockerSummaryFinalW11.qLowerForward_endpointShortcut_not_possible
  qLowerReverse :=
    PachTothBlockerSummaryFinalW11.qLowerReverse_endpointShortcut_not_possible

/-! ## Conditional target projections -/

/-- Exact, fixed, eventual, and arbitrary projections from an explicit row. -/
structure ConditionalTargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Arbitrary projection from an explicit row. -/
structure ConditionalArbitraryProjection (alpha : Sort u) : Sort (max 1 u) where
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Fixed projection from an explicit row whose index is part of the row. -/
structure ConditionalFixedBlockProjection (alpha : Sort u) : Sort (max 1 u) where
  blockIndex : alpha -> Nat
  fixedBlockTarget : forall a : alpha, FixedTarget (16 * blockIndex a)

def projectionOfRouteSummary
    {alpha : Sort u}
    (R : PachTothW11RouteSummaryFinal.ConditionalProjection alpha) :
    ConditionalTargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfTransitionRoleTarget
    {alpha : Sort u}
    (R : TransitionRoleTargetFinalW11.ConditionalTargetProjection alpha) :
    ConditionalTargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-- Package- and field-indexed target projections retained at the terminal
layer. -/
structure TerminalConditionalProjections where
  blockerExactLocalPackage :
    ConditionalArbitraryProjection ExactLocalTargetFinalW11.FinalExactLocalPackage
  routeTransitionRoute :
    ConditionalTargetProjection TransitionFinalIntegratedW11.RoutePackage
  routeTransitionPeriod :
    ConditionalTargetProjection TransitionFinalIntegratedW11.PeriodPackage
  routePeriodExactCandidate :
    forall T : PeriodFinalIntegratedW11.Candidate,
      ConditionalTargetProjection (PeriodFinalIntegratedW11.ExactCandidateFields T)
  routeGeneratedLowerBound :
    forall F : GeneratedTargetFinalW11.GeneratedPointFamily,
      ConditionalTargetProjection
        (GeneratedTargetFinalW11.GeneratedPointLowerBoundFields F)
  transitionRoleRoute :
    ConditionalTargetProjection TransitionFinalIntegratedW11.RoutePackage
  transitionRoleHinge :
    ConditionalTargetProjection TransitionFinalIntegratedW11.RoleHingePackage
  transitionRoleEquation :
    ConditionalTargetProjection RoleHingeFinalIntegratedW11.RoleEquationRouteFields
  transitionExactLocal :
    ConditionalTargetProjection ExactLocalFinalIntegratedW11.FinalExactLocalPackage
  aggregateTransitionRoute :
    ConditionalArbitraryProjection TransitionFinalIntegratedW11.RoutePackage
  aggregateTransitionPeriod :
    ConditionalArbitraryProjection TransitionFinalIntegratedW11.PeriodPackage
  aggregateTransitionPeriodBlock :
    ConditionalFixedBlockProjection TransitionFinalIntegratedW11.PeriodBlockPackage
  aggregateGeneratedPointLowerBound :
    forall F : GeneratedFinalIntegratedW11.GeneratedPointFamily,
      ConditionalArbitraryProjection
        (GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F)
  aggregateCrossBlockClosure :
    forall F : CrossBlockFinalIntegratedW11.PeriodSearchFamily,
      ConditionalArbitraryProjection
        (CrossBlockFinalIntegratedW11.CrossBlockClosureLedger F)
  aggregateExactClosedChains :
    ConditionalArbitraryProjection
      ArbitraryNFinalIntegratedW11.ExactClosedChainPackage
  aggregateSmallLength :
    ConditionalArbitraryProjection SmallLengthFinalIntegratedW11.AggregateFields

/-- Terminal conditional target projections. -/
def terminalConditionalProjections : TerminalConditionalProjections where
  blockerExactLocalPackage := {
    arbitraryTarget :=
      PachTothBlockerSummaryFinalW11.arbitraryTarget_of_finalExactLocalPackage }
  routeTransitionRoute :=
    projectionOfRouteSummary
      PachTothW11RouteSummaryFinal.matrix.projections.transitionRoute
  routeTransitionPeriod :=
    projectionOfRouteSummary
      PachTothW11RouteSummaryFinal.matrix.projections.transitionPeriod
  routePeriodExactCandidate := fun T =>
    projectionOfRouteSummary
      (PachTothW11RouteSummaryFinal.matrix.projections.periodExactCandidate T)
  routeGeneratedLowerBound := fun F =>
    projectionOfRouteSummary
      (PachTothW11RouteSummaryFinal.matrix.projections.generatedLowerBound F)
  transitionRoleRoute :=
    projectionOfTransitionRoleTarget
      TransitionRoleTargetFinalW11.matrix.transitionRoleExact.transitionRoute
  transitionRoleHinge :=
    projectionOfTransitionRoleTarget
      TransitionRoleTargetFinalW11.matrix.transitionRoleExact.transitionRoleHinge
  transitionRoleEquation :=
    projectionOfTransitionRoleTarget
      TransitionRoleTargetFinalW11.matrix.transitionRoleExact.roleEquation
  transitionExactLocal :=
    projectionOfTransitionRoleTarget
      TransitionRoleTargetFinalW11.matrix.transitionRoleExact.exactLocal
  aggregateTransitionRoute := {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_transitionRoutePackage }
  aggregateTransitionPeriod := {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_transitionPeriodPackage }
  aggregateTransitionPeriodBlock := {
    blockIndex := TransitionFinalIntegratedW11.PeriodBlockPackage.blockIndex
    fixedBlockTarget :=
      PachTothW11FinalAggregate.fixedTarget_of_transitionPeriodBlockPackage }
  aggregateGeneratedPointLowerBound := fun _F => {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_generatedPointLowerBoundFields }
  aggregateCrossBlockClosure := fun _F => {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_crossBlockClosureLedger }
  aggregateExactClosedChains := {
    arbitraryTarget := PachTothW11FinalAggregate.arbitraryTarget_of_exactClosedChains }
  aggregateSmallLength := {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_smallLengthAggregateFiniteCertificates }

/-! ## Terminal matrix -/

/-- Terminal W11 Pach--Toth blocker/open-data summary. -/
structure Matrix where
  imported : ImportedTerminalLedgers
  openData : TerminalOpenData
  blockers : TerminalBlockerLedger
  projections : TerminalConditionalProjections

/-- Checked terminal W11 Pach--Toth blocker/open-data matrix. -/
def matrix : Matrix where
  imported := importedTerminalLedgers
  openData := terminalOpenData
  blockers := terminalBlockerLedger
  projections := terminalConditionalProjections

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public blocker wrappers -/

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
    (E : ExactLocalTargetFinalW11.EndpointShortcutRow) :
    Not (ExactLocalTargetFinalW11.PossibleRow E.u E.v) :=
  matrix.blockers.exactLocalEndpointShortcut E

theorem finalEndpointShortcut_not_possible
    (E : ExactLocalFinalIntegratedW11.EndpointShortcutRow) :
    Not (ExactLocalFinalIntegratedW11.PossibleRow E.u E.v) :=
  matrix.blockers.finalEndpointShortcut E

theorem pUpperForward_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_1) :=
  matrix.blockers.pUpperForward

theorem qLowerReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_2 FiniteGraph.LocalVertex.T4_0) :=
  matrix.blockers.qLowerReverse

/-! ## Public conditional target wrappers -/

theorem arbitraryTarget_of_finalExactLocalPackage
    (P : ExactLocalTargetFinalW11.FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.projections.blockerExactLocalPackage.arbitraryTarget P

theorem arbitraryTarget_of_routeTransitionRoutePackage
    (P : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.routeTransitionRoute.arbitraryTarget P

theorem arbitraryTarget_of_routeTransitionPeriodPackage
    (P : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.projections.routeTransitionPeriod.arbitraryTarget P

theorem arbitraryTarget_of_routePeriodExactCandidate
    {T : PeriodFinalIntegratedW11.Candidate}
    (D : PeriodFinalIntegratedW11.ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.projections.routePeriodExactCandidate T).arbitraryTarget D

theorem arbitraryTarget_of_routeGeneratedLowerBound
    {F : GeneratedTargetFinalW11.GeneratedPointFamily}
    (D : GeneratedTargetFinalW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.projections.routeGeneratedLowerBound F).arbitraryTarget D

theorem exactTarget_of_transitionRoleRoutePackage
    (P : TransitionFinalIntegratedW11.RoutePackage) :
    ExactTarget :=
  matrix.projections.transitionRoleRoute.exactTarget P

theorem arbitraryTarget_of_transitionRoleRoutePackage
    (P : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleRoute.arbitraryTarget P

theorem arbitraryTarget_of_transitionRoleHingePackage
    (P : TransitionFinalIntegratedW11.RoleHingePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleHinge.arbitraryTarget P

theorem arbitraryTarget_of_transitionRoleEquationFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleEquation.arbitraryTarget R

theorem arbitraryTarget_of_transitionExactLocalPackage
    (P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.projections.transitionExactLocal.arbitraryTarget P

theorem arbitraryTarget_viaAggregate_of_transitionRoutePackage
    (P : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.aggregateTransitionRoute.arbitraryTarget P

theorem fixedTarget_viaAggregate_of_transitionPeriodBlockPackage
    (P : TransitionFinalIntegratedW11.PeriodBlockPackage) :
    FixedTarget
      (16 * matrix.projections.aggregateTransitionPeriodBlock.blockIndex P) :=
  matrix.projections.aggregateTransitionPeriodBlock.fixedBlockTarget P

theorem arbitraryTarget_viaAggregate_of_generatedPointLowerBoundFields
    {F : GeneratedFinalIntegratedW11.GeneratedPointFamily}
    (D : GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.projections.aggregateGeneratedPointLowerBound F).arbitraryTarget D

theorem arbitraryTarget_viaAggregate_of_crossBlockClosureLedger
    {F : CrossBlockFinalIntegratedW11.PeriodSearchFamily}
    (D : CrossBlockFinalIntegratedW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.projections.aggregateCrossBlockClosure F).arbitraryTarget D

theorem arbitraryTarget_viaAggregate_of_exactClosedChains
    (P : ArbitraryNFinalIntegratedW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.aggregateExactClosedChains.arbitraryTarget P

theorem arbitraryTarget_viaAggregate_of_smallLengthAggregate
    (D : SmallLengthFinalIntegratedW11.AggregateFields) :
    ArbitraryTarget :=
  matrix.projections.aggregateSmallLength.arbitraryTarget D

end

end PachTothTerminalBlockerSummaryW11
end PachToth
end ErdosProblems1066
