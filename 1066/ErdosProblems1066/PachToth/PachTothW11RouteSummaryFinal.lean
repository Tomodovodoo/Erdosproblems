import ErdosProblems1066.PachToth.PachTothW11FinalAggregate
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency
import ErdosProblems1066.PachToth.TransitionRoleHingeFinalW11
import ErdosProblems1066.PachToth.GeneratedTargetFinalW11
import ErdosProblems1066.PachToth.ArbitraryNTargetFinalW11
import ErdosProblems1066.PachToth.PeriodFinalIntegratedW11

set_option autoImplicit false

/-!
# W11 Pach--Toth final route summary

This file is a compact checked summary of the final W11 Pach--Toth route
facades in this checkout.  It records the imported matrices, the displayed
open-data ledgers, the remaining blocker rows, and package-indexed target
projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothW11RouteSummaryFinal

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

/-! ## Imported checked matrices -/

/-- The final W11 matrices summarized by this file. -/
structure CheckedMatrices where
  finalAggregate : PachTothW11FinalAggregate.Matrix
  finalConsistency : PachTothW11FinalConsistency.Matrix
  transitionRoleHinge : TransitionRoleHingeFinalW11.Matrix
  generatedTarget : GeneratedTargetFinalW11.Matrix
  arbitraryNTarget : ArbitraryNTargetFinalW11.Matrix
  periodFinal : PeriodFinalIntegratedW11.Matrix

/-- Imported checked W11 matrices. -/
def checkedMatrices : CheckedMatrices where
  finalAggregate := PachTothW11FinalAggregate.matrix
  finalConsistency := PachTothW11FinalConsistency.matrix
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix
  generatedTarget := GeneratedTargetFinalW11.matrix
  arbitraryNTarget := ArbitraryNTargetFinalW11.matrix
  periodFinal := PeriodFinalIntegratedW11.matrix

/-! ## Explicit open-data ledgers -/

/-- Package shapes for the arbitrary-`n` rows that remain external data. -/
structure ArbitraryNOpenData where
  exactAssumptions : Prop
  exactClosedChains : Sort 1
  exactGeneratedClosedChains : Sort 1
  eventualSmallCases : Sort 1
  eventualClosedChains : Sort 1
  eventualGeneratedClosedChains : Sort 1
  smallLengthEventualClosedChains : Sort 1
  smallLengthEventualGeneratedClosedChains : Sort 1
  smallExact : Sort 1
  smallEventualLarge : Sort 1
  smallEventualClosedChains : Sort 1
  smallEventualGeneratedClosedChains : Sort 1
  smallEventualFiniteCertificates : Sort 1
  smallAggregate : Sort 1
  generatedFlexibleCandidateAssembly : Sort 1
  generatedFinalConditionalFamily : Sort 1

/-- Displayed arbitrary-`n` package shapes. -/
def arbitraryNOpenData : ArbitraryNOpenData where
  exactAssumptions := ArbitraryNTargetFinalW11.ExactTargetAssumptions
  exactClosedChains := ArbitraryNTargetFinalW11.ExactClosedChainPackage
  exactGeneratedClosedChains :=
    ArbitraryNTargetFinalW11.ExactGeneratedClosedChainPackage
  eventualSmallCases := ArbitraryNTargetFinalW11.EventualSmallCaseAssumptions
  eventualClosedChains := ArbitraryNTargetFinalW11.EventualClosedChainPackage
  eventualGeneratedClosedChains :=
    ArbitraryNTargetFinalW11.EventualGeneratedClosedChainPackage
  smallLengthEventualClosedChains :=
    ArbitraryNTargetFinalW11.SmallLengthEventualClosedChains
  smallLengthEventualGeneratedClosedChains :=
    ArbitraryNTargetFinalW11.SmallLengthEventualGeneratedClosedChains
  smallExact := ArbitraryNTargetFinalW11.SmallExactFields
  smallEventualLarge := ArbitraryNTargetFinalW11.SmallEventualLargeFields
  smallEventualClosedChains :=
    ArbitraryNTargetFinalW11.SmallEventualClosedChainFields
  smallEventualGeneratedClosedChains :=
    ArbitraryNTargetFinalW11.SmallEventualGeneratedClosedChainFields
  smallEventualFiniteCertificates :=
    ArbitraryNTargetFinalW11.SmallEventualFiniteCertificateFields
  smallAggregate := ArbitraryNTargetFinalW11.SmallAggregateFields
  generatedFlexibleCandidateAssembly :=
    ArbitraryNTargetFinalW11.GeneratedFlexibleCandidateAssemblyFields
  generatedFinalConditionalFamily :=
    ArbitraryNTargetFinalW11.GeneratedFinalConditionalFamily

/-- Package-shape ledgers for the final period rows. -/
structure PeriodOpenData where
  candidate : Type
  fields : PeriodFinalIntegratedW11.FieldLedger
  targetInputs : PeriodTargetIntegratedW11.ExplicitPeriodTargetInputs
  aggregate : PeriodFinalIntegratedW11.Candidate -> Type

/-- Displayed final period package shapes. -/
def periodOpenData : PeriodOpenData where
  candidate := PeriodFinalIntegratedW11.Candidate
  fields := PeriodFinalIntegratedW11.fieldLedger
  targetInputs := PeriodTargetIntegratedW11.explicitPeriodTargetInputs
  aggregate := PeriodFinalIntegratedW11.AggregateFields

/-- Open-data ledgers carried by the final route summary. -/
structure ExplicitOpenData where
  finalAggregate : PachTothW11FinalAggregate.ExplicitOpenData
  finalConsistency : PachTothW11FinalConsistency.OpenInputLedgers
  transitionRoleHinge : TransitionRoleHingeFinalW11.ExplicitRoutePackages
  generatedTarget : GeneratedTargetFinalW11.ExplicitInputLedgers
  arbitraryN : ArbitraryNOpenData
  period : PeriodOpenData

/-- Combined explicit open-data ledger. -/
def explicitOpenData : ExplicitOpenData where
  finalAggregate := PachTothW11FinalAggregate.explicitOpenData
  finalConsistency := PachTothW11FinalConsistency.openInputLedgers
  transitionRoleHinge := TransitionRoleHingeFinalW11.explicitRoutePackages
  generatedTarget := GeneratedTargetFinalW11.explicitInputLedgers
  arbitraryN := arbitraryNOpenData
  period := periodOpenData

/-! ## Summary rows -/

/-- A package-indexed row that may project exact, fixed, eventual, and
arbitrary target statements from explicit data. -/
structure ConditionalProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- A threshold row with an explicit finite complement. -/
structure ThresholdProjection (alpha : Sort u) : Sort (max 1 u) where
  vertexThreshold : alpha -> Nat
  largeTarget :
    forall a : alpha, forall n : Nat, vertexThreshold a <= n -> FixedTarget n
  arbitraryTarget : alpha -> ArbitraryTarget

def projectionOfTransition
    {alpha : Type}
    (R : TransitionFinalIntegratedW11.FinalTargetRow alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfPeriod
    {alpha : Sort u}
    (R : PeriodFinalIntegratedW11.TargetRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfGenerated
    {alpha : Sort u}
    (R : GeneratedTargetFinalW11.ProjectionRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := fun a _n => R.arbitraryTarget a _n
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfArbitraryNExact
    {alpha : Sort u}
    (R : ArbitraryNTargetFinalW11.ExactTargetRoute alpha) :
    ConditionalProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def thresholdOfArbitraryN
    {alpha : Sort u}
    (R : ArbitraryNTargetFinalW11.EventualTargetRoute alpha) :
    ThresholdProjection alpha where
  vertexThreshold := R.vertexThreshold
  largeTarget := R.largeTarget
  arbitraryTarget := R.arbitraryTarget

/-- Principal conditional rows in the final summary. -/
structure ConditionalProjectionMatrix where
  transitionRoute :
    ConditionalProjection TransitionFinalIntegratedW11.RoutePackage
  transitionCandidate :
    ConditionalProjection TransitionFinalIntegratedW11.CandidatePackage
  transitionRoleHinge :
    ConditionalProjection TransitionFinalIntegratedW11.RoleHingePackage
  transitionPeriod :
    ConditionalProjection TransitionFinalIntegratedW11.PeriodPackage
  transitionCrossBlock :
    ConditionalProjection TransitionFinalIntegratedW11.CrossBlockPackage
  periodSeparatedFamily :
    forall T : PeriodFinalIntegratedW11.Candidate,
      ConditionalProjection (PeriodFinalIntegratedW11.SeparatedFamilyFields T)
  periodLowerBound :
    forall T : PeriodFinalIntegratedW11.Candidate,
      ConditionalProjection (PeriodFinalIntegratedW11.LowerBoundFields T)
  periodExactCandidate :
    forall T : PeriodFinalIntegratedW11.Candidate,
      ConditionalProjection (PeriodFinalIntegratedW11.ExactCandidateFields T)
  generatedLowerBound :
    forall F : GeneratedTargetFinalW11.GeneratedPointFamily,
      ConditionalProjection
        (GeneratedTargetFinalW11.GeneratedPointLowerBoundFields F)
  generatedCrossBlockInequality :
    forall F : GeneratedTargetFinalW11.GeneratedCrossBlockFamily,
      ConditionalProjection
        (GeneratedTargetFinalW11.GeneratedCrossBlockInequalityLedger F)
  generatedCrossBlockClosure :
    forall F : GeneratedTargetFinalW11.GeneratedCrossBlockFamily,
      ConditionalProjection
        (GeneratedTargetFinalW11.GeneratedCrossBlockClosureLedger F)
  arbitraryNExactAssumptions :
    ConditionalProjection ArbitraryNTargetFinalW11.ExactTargetAssumptions
  arbitraryNExactClosedChains :
    ConditionalProjection ArbitraryNTargetFinalW11.ExactClosedChainPackage
  arbitraryNExactGeneratedClosedChains :
    ConditionalProjection
      ArbitraryNTargetFinalW11.ExactGeneratedClosedChainPackage
  arbitraryNEventualClosedChains :
    ThresholdProjection ArbitraryNTargetFinalW11.EventualClosedChainPackage
  arbitraryNEventualGeneratedClosedChains :
    ThresholdProjection
      ArbitraryNTargetFinalW11.EventualGeneratedClosedChainPackage

/-- Checked conditional projection matrix. -/
def conditionalProjectionMatrix : ConditionalProjectionMatrix where
  transitionRoute :=
    projectionOfTransition TransitionFinalIntegratedW11.routeTargetRow
  transitionCandidate :=
    projectionOfTransition TransitionFinalIntegratedW11.candidateTargetRow
  transitionRoleHinge :=
    projectionOfTransition TransitionFinalIntegratedW11.roleHingeTargetRow
  transitionPeriod :=
    projectionOfTransition TransitionFinalIntegratedW11.periodTargetRow
  transitionCrossBlock :=
    projectionOfTransition TransitionFinalIntegratedW11.crossBlockTargetRow
  periodSeparatedFamily := fun T =>
    projectionOfPeriod (PeriodFinalIntegratedW11.separatedFamilyTargetRoute T)
  periodLowerBound := fun T =>
    projectionOfPeriod (PeriodFinalIntegratedW11.lowerBoundTargetRoute T)
  periodExactCandidate := fun T =>
    projectionOfPeriod (PeriodFinalIntegratedW11.exactCandidateTargetRoute T)
  generatedLowerBound := fun F =>
    projectionOfGenerated
      ((GeneratedTargetFinalW11.matrix.generated.lowerBound F))
  generatedCrossBlockInequality := fun F =>
    projectionOfGenerated
      ((GeneratedTargetFinalW11.matrix.generated.crossBlockInequality F))
  generatedCrossBlockClosure := fun F =>
    projectionOfGenerated
      ((GeneratedTargetFinalW11.matrix.generated.crossBlockClosure F))
  arbitraryNExactAssumptions :=
    projectionOfArbitraryNExact
      ArbitraryNTargetFinalW11.matrix.exact.exactAssumptions
  arbitraryNExactClosedChains :=
    projectionOfArbitraryNExact
      ArbitraryNTargetFinalW11.matrix.exact.closedChains
  arbitraryNExactGeneratedClosedChains :=
    projectionOfArbitraryNExact
      ArbitraryNTargetFinalW11.matrix.exact.generatedClosedChains
  arbitraryNEventualClosedChains :=
    thresholdOfArbitraryN
      ArbitraryNTargetFinalW11.matrix.eventual.closedChains
  arbitraryNEventualGeneratedClosedChains :=
    thresholdOfArbitraryN
      ArbitraryNTargetFinalW11.matrix.eventual.generatedClosedChains

/-! ## Blockers -/

/-- Named blockers retained beside the conditional route rows. -/
structure BlockerLedger where
  finalAggregate : PachTothW11FinalConsistency.FinalBlockerLedger
  transitionRoleHinge : TransitionRoleHingeFinalW11.BlockerFields
  generatedTarget : GeneratedTargetIntegratedW11.TransitionBlockers
  transitionRouteClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  completedFilteredRoute :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  fullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap

/-- Checked blocker ledger for still-missing shortcut data. -/
def blockerLedger : BlockerLedger where
  finalAggregate := PachTothW11FinalConsistency.finalBlockerLedger
  transitionRoleHinge := TransitionRoleHingeFinalW11.blockerFields
  generatedTarget := GeneratedTargetIntegratedW11.transitionBlockers
  transitionRouteClaim :=
    TransitionRoleHingeFinalW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionRoleHingeFinalW11.concreteFourTargetCompletedFilteredRoute_blocked
  fullSameRestShortcut :=
    TransitionRoleHingeFinalW11.concreteFourTargetFullSameRestShortcut_blocked

/-! ## Final summary matrix -/

/-- Concise final checked W11 route summary matrix. -/
structure Matrix where
  checked : CheckedMatrices
  openData : ExplicitOpenData
  projections : ConditionalProjectionMatrix
  blockers : BlockerLedger

/-- The final checked W11 Pach--Toth route summary matrix. -/
def matrix : Matrix where
  checked := checkedMatrices
  openData := explicitOpenData
  projections := conditionalProjectionMatrix
  blockers := blockerLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Conditional projection wrappers -/

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoute.arbitraryTarget package

theorem arbitraryTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ArbitraryTarget :=
  matrix.projections.transitionRoleHinge.arbitraryTarget package

theorem arbitraryTarget_of_transitionPeriodPackage
    (package : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.projections.transitionPeriod.arbitraryTarget package

theorem arbitraryTarget_of_periodSeparatedFamily
    {T : PeriodFinalIntegratedW11.Candidate}
    (D : PeriodFinalIntegratedW11.SeparatedFamilyFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodSeparatedFamily T).arbitraryTarget D

theorem arbitraryTarget_of_periodLowerBound
    {T : PeriodFinalIntegratedW11.Candidate}
    (D : PeriodFinalIntegratedW11.LowerBoundFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodLowerBound T).arbitraryTarget D

theorem arbitraryTarget_of_periodExactCandidate
    {T : PeriodFinalIntegratedW11.Candidate}
    (D : PeriodFinalIntegratedW11.ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodExactCandidate T).arbitraryTarget D

theorem arbitraryTarget_of_generatedLowerBound
    {F : GeneratedTargetFinalW11.GeneratedPointFamily}
    (D : GeneratedTargetFinalW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.projections.generatedLowerBound F).arbitraryTarget D

theorem arbitraryTarget_of_generatedCrossBlockInequality
    {F : GeneratedTargetFinalW11.GeneratedCrossBlockFamily}
    (D : GeneratedTargetFinalW11.GeneratedCrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.projections.generatedCrossBlockInequality F).arbitraryTarget D

theorem arbitraryTarget_of_generatedCrossBlockClosure
    {F : GeneratedTargetFinalW11.GeneratedCrossBlockFamily}
    (D : GeneratedTargetFinalW11.GeneratedCrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.projections.generatedCrossBlockClosure F).arbitraryTarget D

theorem arbitraryTarget_of_arbitraryNExactClosedChains
    (P : ArbitraryNTargetFinalW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryNExactClosedChains.arbitraryTarget P

theorem arbitraryTarget_of_arbitraryNEventualGeneratedClosedChains
    (P : ArbitraryNTargetFinalW11.EventualGeneratedClosedChainPackage) :
    ArbitraryTarget :=
  matrix.projections.arbitraryNEventualGeneratedClosedChains.arbitraryTarget P

theorem largeTarget_of_arbitraryNEventualClosedChains
    (P : ArbitraryNTargetFinalW11.EventualClosedChainPackage)
    (n : Nat)
    (hn :
      matrix.projections.arbitraryNEventualClosedChains.vertexThreshold P <=
        n) :
    FixedTarget n :=
  matrix.projections.arbitraryNEventualClosedChains.largeTarget P n hn

/-! ## Blocker wrappers -/

theorem transitionRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.transitionRouteClaim

theorem completedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem fullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

end

end PachTothW11RouteSummaryFinal
end PachToth
end ErdosProblems1066
