import ErdosProblems1066.PachToth.PachTothW11RouteSummaryFinal
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency
import ErdosProblems1066.PachToth.PeriodTargetFinalW11
import ErdosProblems1066.PachToth.ArbitraryNRouteSummaryFinalW11
import ErdosProblems1066.PachToth.GeneratedCrossBlockFinalW11

set_option autoImplicit false

/-!
# W11 Pach--Toth final route ledger

This is the terminal conditional ledger for the W11 Pach--Toth route files
present in this checkout.  It records the checked endpoint matrices, the
explicit open-data ledgers, the absent generated-cross-block summary file, and
only package-indexed target projections.

There is no unconditional five-sixteenths target theorem in this file.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothFinalRouteLedgerW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Imported endpoint ledgers -/

/-- Presence status for optional W11 terminal summaries. -/
inductive OptionalSummaryStatus where
  | present
  | absent
deriving DecidableEq

/-- Optional summaries mentioned by the final route task. -/
structure OptionalSummaryLedger where
  arbitraryNRouteSummary : OptionalSummaryStatus
  generatedCrossBlockSummary : OptionalSummaryStatus
  generatedCrossBlockFinal : OptionalSummaryStatus

/-- Optional-summary availability in this checkout. -/
def optionalSummaryLedger : OptionalSummaryLedger where
  arbitraryNRouteSummary := OptionalSummaryStatus.present
  generatedCrossBlockSummary := OptionalSummaryStatus.absent
  generatedCrossBlockFinal := OptionalSummaryStatus.present

theorem generatedCrossBlockSummary_absent :
    optionalSummaryLedger.generatedCrossBlockSummary =
      OptionalSummaryStatus.absent :=
  rfl

/-- Checked endpoint matrices carried by the terminal route ledger. -/
structure ImportedEndpointLedgers where
  routeSummary : PachTothW11RouteSummaryFinal.Matrix
  finalAggregate : PachTothW11FinalAggregate.Matrix
  finalConsistency : PachTothW11FinalConsistency.Matrix
  periodTarget : PeriodTargetFinalW11.Matrix
  arbitraryNRouteSummary : ArbitraryNRouteSummaryFinalW11.Matrix
  generatedCrossBlockFinal : GeneratedCrossBlockFinalW11.Matrix

/-- Imported checked endpoint matrices. -/
def importedEndpointLedgers : ImportedEndpointLedgers where
  routeSummary := PachTothW11RouteSummaryFinal.matrix
  finalAggregate := PachTothW11FinalAggregate.matrix
  finalConsistency := PachTothW11FinalConsistency.matrix
  periodTarget := PeriodTargetFinalW11.matrix
  arbitraryNRouteSummary := ArbitraryNRouteSummaryFinalW11.matrix
  generatedCrossBlockFinal := GeneratedCrossBlockFinalW11.matrix

/-! ## Explicit open data -/

/-- Open-data shapes retained by the terminal route ledger. -/
structure ExplicitOpenData where
  routeSummary : PachTothW11RouteSummaryFinal.ExplicitOpenData
  finalAggregate : PachTothW11FinalAggregate.ExplicitOpenData
  finalConsistency : PachTothW11FinalConsistency.OpenInputLedgers
  periodTarget : PeriodTargetFinalW11.ExplicitPackageLedger
  arbitraryNRouteSummary : ArbitraryNRouteSummaryFinalW11.RouteSourceSummary
  generatedCrossBlockFinal : GeneratedCrossBlockFinalW11.ExplicitFinalLedgers
  optionalSummaries : OptionalSummaryLedger

/-- Combined open-data ledger. -/
def explicitOpenData : ExplicitOpenData where
  routeSummary := PachTothW11RouteSummaryFinal.explicitOpenData
  finalAggregate := PachTothW11FinalAggregate.explicitOpenData
  finalConsistency := PachTothW11FinalConsistency.openInputLedgers
  periodTarget := PeriodTargetFinalW11.explicitPackageLedger
  arbitraryNRouteSummary := ArbitraryNRouteSummaryFinalW11.routeSourceSummary
  generatedCrossBlockFinal := GeneratedCrossBlockFinalW11.explicitFinalLedgers
  optionalSummaries := optionalSummaryLedger

/-! ## Conditional route projections -/

/-- Package-indexed projections retained by the terminal route ledger. -/
structure ConditionalRouteLedger where
  routeSummary : PachTothW11RouteSummaryFinal.ConditionalProjectionMatrix
  periodTarget : PeriodTargetFinalW11.PeriodProjectionLedger
  arbitraryNExact : ArbitraryNTargetFinalW11.ExactFields
  arbitraryNEventual : ArbitraryNTargetFinalW11.EventualFields
  generated : GeneratedCrossBlockFinalW11.GeneratedRouteLedger
  generatedCrossBlock : GeneratedCrossBlockFinalW11.CrossBlockRouteLedger
  generatedViaArbitraryN : GeneratedCrossBlockFinalW11.ArbitraryNRouteLedger
  generatedFinalConsistency :
    GeneratedCrossBlockFinalW11.FinalConsistencyRouteLedger

/-- Checked conditional route ledger. -/
def conditionalRouteLedger : ConditionalRouteLedger where
  routeSummary := PachTothW11RouteSummaryFinal.conditionalProjectionMatrix
  periodTarget := PeriodTargetFinalW11.periodProjectionLedger
  arbitraryNExact :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.exact.targetRoutes
  arbitraryNEventual :=
    ArbitraryNRouteSummaryFinalW11.matrix.source.eventual.targetRoutes
  generated := GeneratedCrossBlockFinalW11.generatedRouteLedger
  generatedCrossBlock := GeneratedCrossBlockFinalW11.crossBlockRouteLedger
  generatedViaArbitraryN := GeneratedCrossBlockFinalW11.arbitraryNRouteLedger
  generatedFinalConsistency :=
    GeneratedCrossBlockFinalW11.finalConsistencyRouteLedger

/-! ## Blockers -/

/-- Blockers retained beside the conditional target projections. -/
structure BlockerLedger where
  routeSummary : PachTothW11RouteSummaryFinal.BlockerLedger
  finalConsistency : PachTothW11FinalConsistency.FinalBlockerLedger
  generatedCrossBlock : GeneratedTargetIntegratedW11.TransitionBlockers

/-- Checked blocker ledger. -/
def blockerLedger : BlockerLedger where
  routeSummary := PachTothW11RouteSummaryFinal.blockerLedger
  finalConsistency := PachTothW11FinalConsistency.finalBlockerLedger
  generatedCrossBlock := GeneratedCrossBlockFinalW11.matrix.blockers

/-! ## Final ledger -/

/-- Terminal W11 Pach--Toth conditional route ledger. -/
structure Matrix where
  imported : ImportedEndpointLedgers
  openData : ExplicitOpenData
  routes : ConditionalRouteLedger
  blockers : BlockerLedger

/-- The checked terminal W11 Pach--Toth conditional route ledger. -/
def matrix : Matrix where
  imported := importedEndpointLedgers
  openData := explicitOpenData
  routes := conditionalRouteLedger
  blockers := blockerLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public conditional target wrappers -/

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.routes.routeSummary.transitionRoute.arbitraryTarget package

theorem arbitraryTarget_of_transitionPeriodPackage
    (package : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.routes.routeSummary.transitionPeriod.arbitraryTarget package

theorem fixedTarget_of_periodWordSeparationFields
    {T : PeriodTargetFinalW11.Candidate}
    (D : PeriodTargetFinalW11.WordSeparationFields T) :
    FixedTarget (16 * D.length) :=
  (matrix.routes.periodTarget.wordSeparation T).fixedBlockTarget D

theorem arbitraryTarget_of_periodSeparatedFamilyFields
    {T : PeriodTargetFinalW11.Candidate}
    (D : PeriodTargetFinalW11.SeparatedFamilyFields T) :
    ArbitraryTarget :=
  (matrix.routes.periodTarget.separatedFamily T).projection.arbitraryTarget D

theorem arbitraryTarget_of_periodLowerBoundFields
    {T : PeriodTargetFinalW11.Candidate}
    (D : PeriodTargetFinalW11.LowerBoundFields T) :
    ArbitraryTarget :=
  (matrix.routes.periodTarget.lowerBound T).projection.arbitraryTarget D

theorem arbitraryTarget_of_periodExactCandidateFields
    {T : PeriodTargetFinalW11.Candidate}
    (D : PeriodTargetFinalW11.ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.routes.periodTarget.exactCandidate T).projection.arbitraryTarget D

theorem arbitraryTarget_of_arbitraryNExactAssumptions
    (A : ArbitraryNRouteSummaryFinalW11.ExactTargetAssumptions) :
    ArbitraryTarget :=
  matrix.routes.arbitraryNExact.exactAssumptions.arbitraryTarget A

theorem arbitraryTarget_of_arbitraryNExactClosedChains
    (P : ArbitraryNRouteSummaryFinalW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.routes.arbitraryNExact.closedChains.arbitraryTarget P

theorem largeTarget_of_arbitraryNEventualClosedChains
    (P : ArbitraryNRouteSummaryFinalW11.EventualClosedChainPackage)
    (n : Nat)
    (hn :
      matrix.routes.arbitraryNEventual.closedChains.vertexThreshold P <= n) :
    FixedTarget n :=
  matrix.routes.arbitraryNEventual.closedChains.largeTarget P n hn

theorem arbitraryTarget_of_arbitraryNEventualGeneratedClosedChains
    (P : ArbitraryNRouteSummaryFinalW11.EventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.routes.arbitraryNEventual.generatedClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_generatedLowerBoundFields
    {F : GeneratedCrossBlockFinalW11.GeneratedPointFamily}
    (C : GeneratedCrossBlockFinalW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.routes.generated.lowerBound F).arbitraryTarget C

theorem arbitraryTarget_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFinalW11.GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockFinalW11.GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.routes.generated.crossBlockClosure F).arbitraryTarget C

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : GeneratedCrossBlockFinalW11.CrossBlockFamily}
    (C : GeneratedCrossBlockFinalW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.routes.generatedCrossBlock.closureLedgers F).arbitraryTarget C

theorem arbitraryTarget_viaArbitraryN_of_generatedCrossBlockClosureLedger
    {F : GeneratedCrossBlockFinalW11.GeneratedCrossBlockFamily}
    (C : GeneratedCrossBlockFinalW11.GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.routes.generatedViaArbitraryN.generatedCrossBlockClosure F)
    |>.arbitraryTarget C

/-! ## Public blocker wrappers -/

theorem transitionRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.routeSummary.transitionRouteClaim

theorem completedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.routeSummary.completedFilteredRoute

theorem fullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.routeSummary.fullSameRestShortcut

end

end PachTothFinalRouteLedgerW11
end PachToth
end ErdosProblems1066
