import ErdosProblems1066.PachToth.TransitionPeriodFinalW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.PeriodFinalIntegratedW11
import ErdosProblems1066.PachToth.PeriodTargetIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Final W11 transition/period route summary

This module is a compact facade over the checked transition-period adapter and
the final transition, period, period-target, and aggregate ledgers.  It records
the package families explicitly and exposes target statements only as
projections from supplied packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionPeriodRouteSummaryFinalW11

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

abbrev RoutePackage :=
  TransitionPeriodFinalW11.RoutePackage

abbrev PeriodPackage :=
  TransitionPeriodFinalW11.PeriodPackage

abbrev PeriodBlockPackage :=
  TransitionPeriodFinalW11.PeriodBlockPackage

abbrev TransitionFinalRoutePackage :=
  TransitionPeriodFinalW11.TransitionFinalRoutePackage

abbrev TransitionFinalPeriodPackage :=
  TransitionPeriodFinalW11.TransitionFinalPeriodPackage

abbrev TransitionTargetRoutePackage :=
  TransitionPeriodFinalW11.TransitionTargetRoutePackage

abbrev TransitionTargetPeriodPackage :=
  TransitionPeriodFinalW11.TransitionTargetPeriodPackage

abbrev PeriodCandidate :=
  PeriodFinalIntegratedW11.Candidate

/-! ## Checked ledgers -/

/-- Checked ledgers summarized by this facade. -/
structure CheckedLedgers where
  transitionPeriod : TransitionPeriodFinalW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  periodFinal : PeriodFinalIntegratedW11.Matrix
  periodTarget : PeriodTargetIntegratedW11.Matrix
  finalAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked ledgers. -/
def checkedLedgers : CheckedLedgers where
  transitionPeriod := TransitionPeriodFinalW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  periodFinal := PeriodFinalIntegratedW11.matrix
  periodTarget := PeriodTargetIntegratedW11.matrix
  finalAggregate := PachTothW11FinalAggregate.matrix

/-! ## Explicit package ledger -/

/-- Package families carried by the transition/period route summary. -/
structure ExplicitPackageLedger where
  transitionPeriodFields :
    TransitionPeriodFinalW11.ExplicitRoutePeriodPackageFields
  routePackages : Type
  periodPackages : Type
  periodBlockPackages : Type
  transitionFinalRoutePackages : Type
  transitionFinalPeriodPackages : Type
  transitionTargetRoutePackages : Type
  transitionTargetPeriodPackages : Type
  periodCandidates : Type
  periodFinalWordSeparationFields : periodCandidates -> Type
  periodFinalSeparatedFamilyFields : periodCandidates -> Type
  periodFinalLowerBoundFields : periodCandidates -> Type
  periodFinalExactCandidateFields : periodCandidates -> Type
  periodFinalAggregateFields : periodCandidates -> Type
  periodTargetInputs : PeriodTargetIntegratedW11.ExplicitPeriodTargetInputs
  finalAggregateOpenData : PachTothW11FinalAggregate.ExplicitOpenData
  finalAggregateAvailability :
    PachTothW11FinalAggregate.FinalLedgerAvailability

/-- Explicit package families and open-data ledgers used by the summary. -/
def explicitPackageLedger : ExplicitPackageLedger where
  transitionPeriodFields :=
    TransitionPeriodFinalW11.explicitRoutePeriodPackageFields
  routePackages := RoutePackage
  periodPackages := PeriodPackage
  periodBlockPackages := PeriodBlockPackage
  transitionFinalRoutePackages := TransitionFinalRoutePackage
  transitionFinalPeriodPackages := TransitionFinalPeriodPackage
  transitionTargetRoutePackages := TransitionTargetRoutePackage
  transitionTargetPeriodPackages := TransitionTargetPeriodPackage
  periodCandidates := PeriodCandidate
  periodFinalWordSeparationFields :=
    PeriodFinalIntegratedW11.WordSeparationFields
  periodFinalSeparatedFamilyFields :=
    PeriodFinalIntegratedW11.SeparatedFamilyFields
  periodFinalLowerBoundFields :=
    PeriodFinalIntegratedW11.LowerBoundFields
  periodFinalExactCandidateFields :=
    PeriodFinalIntegratedW11.ExactCandidateFields
  periodFinalAggregateFields :=
    PeriodFinalIntegratedW11.AggregateFields
  periodTargetInputs := PeriodTargetIntegratedW11.explicitPeriodTargetInputs
  finalAggregateOpenData := PachTothW11FinalAggregate.explicitOpenData
  finalAggregateAvailability :=
    PachTothW11FinalAggregate.finalLedgerAvailability

/-! ## Conditional projection rows -/

/-- Exact, fixed, eventual, and arbitrary target projections from one package. -/
structure TargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Fixed-block projection from one period-block package. -/
structure BlockProjection (alpha : Type) where
  blockIndex : alpha -> Nat
  fixedBlockTarget :
    forall package : alpha, FixedTarget (16 * blockIndex package)

def projectionOfTransitionPeriod
    {alpha : Type}
    (R : TransitionPeriodFinalW11.TargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def blockProjectionOfTransitionPeriod
    {alpha : Type}
    (R : TransitionPeriodFinalW11.BlockTargetRow alpha) :
    BlockProjection alpha where
  blockIndex := R.blockIndex
  fixedBlockTarget := R.fixedBlockTarget

def projectionOfPeriodFinal
    {alpha : Sort u}
    (R : PeriodFinalIntegratedW11.TargetRoute alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-- Conditional projections exposed by the route summary. -/
structure ConditionalProjectionMatrix where
  route : TargetProjection RoutePackage
  period : TargetProjection PeriodPackage
  periodBlock : BlockProjection PeriodBlockPackage
  transitionFinalRoute : TargetProjection TransitionFinalRoutePackage
  transitionFinalPeriod : TargetProjection TransitionFinalPeriodPackage
  transitionTargetRoute : TargetProjection TransitionTargetRoutePackage
  transitionTargetPeriod : TargetProjection TransitionTargetPeriodPackage
  periodFinalSeparatedFamily :
    forall T : PeriodCandidate,
      TargetProjection (PeriodFinalIntegratedW11.SeparatedFamilyFields T)
  periodFinalLowerBound :
    forall T : PeriodCandidate,
      TargetProjection (PeriodFinalIntegratedW11.LowerBoundFields T)
  periodFinalExactCandidate :
    forall T : PeriodCandidate,
      TargetProjection (PeriodFinalIntegratedW11.ExactCandidateFields T)

/-- Checked conditional projection matrix. -/
def conditionalProjectionMatrix : ConditionalProjectionMatrix where
  route :=
    projectionOfTransitionPeriod TransitionPeriodFinalW11.routeTargetRow
  period :=
    projectionOfTransitionPeriod TransitionPeriodFinalW11.periodTargetRow
  periodBlock :=
    blockProjectionOfTransitionPeriod
      TransitionPeriodFinalW11.periodBlockTargetRow
  transitionFinalRoute :=
    projectionOfTransitionPeriod
      TransitionPeriodFinalW11.projectionRows.transitionFinalRoute
  transitionFinalPeriod :=
    projectionOfTransitionPeriod
      TransitionPeriodFinalW11.projectionRows.transitionFinalPeriod
  transitionTargetRoute :=
    projectionOfTransitionPeriod
      TransitionPeriodFinalW11.projectionRows.transitionTargetRoute
  transitionTargetPeriod :=
    projectionOfTransitionPeriod
      TransitionPeriodFinalW11.projectionRows.transitionTargetPeriod
  periodFinalSeparatedFamily := fun T =>
    projectionOfPeriodFinal
      (PeriodFinalIntegratedW11.separatedFamilyTargetRoute T)
  periodFinalLowerBound := fun T =>
    projectionOfPeriodFinal
      (PeriodFinalIntegratedW11.lowerBoundTargetRoute T)
  periodFinalExactCandidate := fun T =>
    projectionOfPeriodFinal
      (PeriodFinalIntegratedW11.exactCandidateTargetRoute T)

/-! ## Final summary matrix -/

/-- Concise checked transition/period route summary. -/
structure Matrix where
  checked : CheckedLedgers
  packages : ExplicitPackageLedger
  projections : ConditionalProjectionMatrix

/-- The checked W11 transition/period route summary. -/
def matrix : Matrix where
  checked := checkedLedgers
  packages := explicitPackageLedger
  projections := conditionalProjectionMatrix

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Combined route and period projections -/

theorem exactTarget_of_routePackage
    (package : RoutePackage) : ExactTarget :=
  matrix.projections.route.exactTarget package

theorem fixedTarget_of_routePackage
    (package : RoutePackage) (n : Nat) : FixedTarget n :=
  matrix.projections.route.fixedTarget package n

theorem eventualTarget_of_routePackage
    (package : RoutePackage) : EventualTarget :=
  matrix.projections.route.eventualTarget package

theorem arbitraryTarget_of_routePackage
    (package : RoutePackage) : ArbitraryTarget :=
  matrix.projections.route.arbitraryTarget package

theorem exactTarget_of_periodPackage
    (package : PeriodPackage) : ExactTarget :=
  matrix.projections.period.exactTarget package

theorem fixedTarget_of_periodPackage
    (package : PeriodPackage) (n : Nat) : FixedTarget n :=
  matrix.projections.period.fixedTarget package n

theorem eventualTarget_of_periodPackage
    (package : PeriodPackage) : EventualTarget :=
  matrix.projections.period.eventualTarget package

theorem arbitraryTarget_of_periodPackage
    (package : PeriodPackage) : ArbitraryTarget :=
  matrix.projections.period.arbitraryTarget package

theorem fixedTarget_of_periodBlockPackage
    (package : PeriodBlockPackage) :
    FixedTarget
      (16 * TransitionPeriodFinalW11.PeriodBlockPackage.blockIndex package) :=
  matrix.projections.periodBlock.fixedBlockTarget package

/-! ## Source-package projections -/

theorem arbitraryTarget_of_transitionFinalRoutePackage
    (package : TransitionFinalRoutePackage) : ArbitraryTarget :=
  matrix.projections.transitionFinalRoute.arbitraryTarget package

theorem arbitraryTarget_of_transitionFinalPeriodPackage
    (package : TransitionFinalPeriodPackage) : ArbitraryTarget :=
  matrix.projections.transitionFinalPeriod.arbitraryTarget package

theorem arbitraryTarget_of_transitionTargetRoutePackage
    (package : TransitionTargetRoutePackage) : ArbitraryTarget :=
  matrix.projections.transitionTargetRoute.arbitraryTarget package

theorem arbitraryTarget_of_transitionTargetPeriodPackage
    (package : TransitionTargetPeriodPackage) : ArbitraryTarget :=
  matrix.projections.transitionTargetPeriod.arbitraryTarget package

theorem arbitraryTarget_of_periodFinalSeparatedFamily
    {T : PeriodCandidate}
    (fields : PeriodFinalIntegratedW11.SeparatedFamilyFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodFinalSeparatedFamily T).arbitraryTarget fields

theorem arbitraryTarget_of_periodFinalLowerBound
    {T : PeriodCandidate}
    (fields : PeriodFinalIntegratedW11.LowerBoundFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodFinalLowerBound T).arbitraryTarget fields

theorem arbitraryTarget_of_periodFinalExactCandidate
    {T : PeriodCandidate}
    (fields : PeriodFinalIntegratedW11.ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodFinalExactCandidate T).arbitraryTarget fields

/-! ## Aggregate status -/

theorem aggregate_periodFinalStatus :
    matrix.packages.finalAggregateAvailability.periodFinal =
      PachTothW11FinalAggregate.LedgerAvailability.absent :=
  PachTothW11FinalAggregate.periodFinalIntegratedW11_absent

end

end TransitionPeriodRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
