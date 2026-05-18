import ErdosProblems1066.PachToth.PeriodTargetFinalW11
import ErdosProblems1066.PachToth.PeriodFinalIntegratedW11
import ErdosProblems1066.PachToth.TransitionPeriodFinalW11
import ErdosProblems1066.PachToth.PachTothW11RouteSummaryFinal
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Final W11 period route summary

This module is a compact facade for the checked W11 period route.  It records
the final period ledgers, displays the period package families, and exposes
target statements only as projections from explicit packages.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PeriodRouteSummaryFinalW11

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

abbrev Candidate :=
  PeriodTargetFinalW11.Candidate

abbrev WordSeparationPackage (T : Candidate) :=
  PeriodTargetFinalW11.WordSeparationFields T

abbrev SeparatedFamilyPackage (T : Candidate) :=
  PeriodTargetFinalW11.SeparatedFamilyFields T

abbrev LowerBoundPackage (T : Candidate) :=
  PeriodTargetFinalW11.LowerBoundFields T

abbrev ExactCandidatePackage (T : Candidate) :=
  PeriodTargetFinalW11.ExactCandidateFields T

abbrev AggregatePackage (T : Candidate) :=
  PeriodTargetFinalW11.AggregateFields T

abbrev BaseWordSeparationPackage (T : Candidate) :=
  PeriodTargetFinalW11.BaseWordSeparationFields T

abbrev BaseExactCandidatePackage (T : Candidate) :=
  PeriodTargetFinalW11.BaseExactCandidateFields T

abbrev TransitionPeriodRoutePackage :=
  PeriodTargetFinalW11.TransitionPeriodRoutePackage

abbrev TransitionPeriodPeriodPackage :=
  PeriodTargetFinalW11.TransitionPeriodPeriodPackage

abbrev TransitionPeriodBlockPackage :=
  PeriodTargetFinalW11.TransitionPeriodBlockPackage

/-! ## Checked ledgers -/

/-- Checked W11 ledgers summarized by this period route facade. -/
structure CheckedLedgers where
  periodTargetFinal : PeriodTargetFinalW11.Matrix
  periodFinal : PeriodFinalIntegratedW11.Matrix
  transitionPeriodFinal : TransitionPeriodFinalW11.Matrix
  pachTothRouteSummary : PachTothW11RouteSummaryFinal.Matrix
  pachTothFinalAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked W11 period-route ledgers. -/
def checkedLedgers : CheckedLedgers where
  periodTargetFinal := PeriodTargetFinalW11.matrix
  periodFinal := PeriodFinalIntegratedW11.matrix
  transitionPeriodFinal := TransitionPeriodFinalW11.matrix
  pachTothRouteSummary := PachTothW11RouteSummaryFinal.matrix
  pachTothFinalAggregate := PachTothW11FinalAggregate.matrix

/-! ## Explicit package ledger -/

/-- Package families carried by the final period route summary. -/
structure ExplicitPackageLedger where
  periodTargetFinal : PeriodTargetFinalW11.ExplicitPackageLedger
  periodFinalFields : PeriodFinalIntegratedW11.FieldLedger
  transitionPeriodFields :
    TransitionPeriodFinalW11.ExplicitRoutePeriodPackageFields
  routeSummaryOpenData : PachTothW11RouteSummaryFinal.ExplicitOpenData
  finalAggregateOpenData : PachTothW11FinalAggregate.ExplicitOpenData
  candidate : Type
  targetPackages : Type
  fixedBlockPackages : Type
  wordSeparationPackages : Candidate -> Type
  separatedFamilyPackages : Candidate -> Type
  lowerBoundPackages : Candidate -> Type
  exactCandidatePackages : Candidate -> Type
  aggregatePackages : Candidate -> Type
  baseWordSeparationPackages : Candidate -> Sort 1
  baseExactCandidatePackages : Candidate -> Sort 1
  transitionPeriodRoutePackages : Type
  transitionPeriodPeriodPackages : Type
  transitionPeriodBlockPackages : Type

/-! ## Combined target packages -/

/-- Period packages with exact, eventual, and arbitrary projections. -/
inductive TargetPackage where
  | separatedFamily {T : Candidate} (fields : SeparatedFamilyPackage T)
  | lowerBound {T : Candidate} (fields : LowerBoundPackage T)
  | exactCandidate {T : Candidate} (fields : ExactCandidatePackage T)
  | aggregateSeparatedFamily {T : Candidate} (fields : AggregatePackage T)
  | aggregateLowerBound {T : Candidate} (fields : AggregatePackage T)
  | aggregateExactCandidate {T : Candidate} (fields : AggregatePackage T)
  | transitionPeriodRoute (package : TransitionPeriodRoutePackage)
  | transitionPeriodPeriod (package : TransitionPeriodPeriodPackage)

namespace TargetPackage

def exactTarget : TargetPackage -> ExactTarget
  | separatedFamily fields =>
      PeriodTargetFinalW11.exactTarget_of_separatedFamilyFields fields
  | lowerBound fields =>
      PeriodTargetFinalW11.exactTarget_of_lowerBoundFields fields
  | exactCandidate fields =>
      PeriodTargetFinalW11.exactTarget_of_exactCandidateFields fields
  | aggregateSeparatedFamily fields =>
      PeriodTargetFinalW11.exactTarget_of_aggregateSeparatedFamily fields
  | aggregateLowerBound fields =>
      PeriodTargetFinalW11.exactTarget_of_aggregateLowerBound fields
  | aggregateExactCandidate fields =>
      PeriodTargetFinalW11.exactTarget_of_aggregateExactCandidate fields
  | transitionPeriodRoute package =>
      PeriodTargetFinalW11.matrix.transitionPeriod.routePackage.exactTarget
        package
  | transitionPeriodPeriod package =>
      PeriodTargetFinalW11.exactTarget_of_transitionPeriodPackage package

def eventualTarget : TargetPackage -> EventualTarget
  | separatedFamily fields =>
      PeriodTargetFinalW11.eventualTarget_of_separatedFamilyFields fields
  | lowerBound fields =>
      PeriodTargetFinalW11.eventualTarget_of_lowerBoundFields fields
  | exactCandidate fields =>
      PeriodTargetFinalW11.eventualTarget_of_exactCandidateFields fields
  | aggregateSeparatedFamily fields =>
      PeriodTargetFinalW11.eventualTarget_of_aggregateSeparatedFamily fields
  | aggregateLowerBound fields =>
      PeriodTargetFinalW11.eventualTarget_of_aggregateLowerBound fields
  | aggregateExactCandidate fields =>
      PeriodTargetFinalW11.eventualTarget_of_aggregateExactCandidate fields
  | transitionPeriodRoute package =>
      PeriodTargetFinalW11.matrix.transitionPeriod.routePackage.eventualTarget
        package
  | transitionPeriodPeriod package =>
      PeriodTargetFinalW11.eventualTarget_of_transitionPeriodPackage package

def arbitraryTarget : TargetPackage -> ArbitraryTarget
  | separatedFamily fields =>
      PeriodTargetFinalW11.arbitraryTarget_of_separatedFamilyFields fields
  | lowerBound fields =>
      PeriodTargetFinalW11.arbitraryTarget_of_lowerBoundFields fields
  | exactCandidate fields =>
      PeriodTargetFinalW11.arbitraryTarget_of_exactCandidateFields fields
  | aggregateSeparatedFamily fields =>
      PeriodTargetFinalW11.arbitraryTarget_of_aggregateSeparatedFamily fields
  | aggregateLowerBound fields =>
      PeriodTargetFinalW11.arbitraryTarget_of_aggregateLowerBound fields
  | aggregateExactCandidate fields =>
      PeriodTargetFinalW11.arbitraryTarget_of_aggregateExactCandidate fields
  | transitionPeriodRoute package =>
      PeriodTargetFinalW11.matrix.transitionPeriod.routePackage.arbitraryTarget
        package
  | transitionPeriodPeriod package =>
      PeriodTargetFinalW11.arbitraryTarget_of_transitionPeriodPackage package

end TargetPackage

/-! ## Fixed block packages -/

/-- Period packages whose natural conclusion is one fixed block count. -/
inductive FixedBlockPackage where
  | wordSeparation {T : Candidate} (fields : WordSeparationPackage T)
  | separatedFamily
      {T : Candidate} (fields : SeparatedFamilyPackage T)
      (k : Nat) (positive : 0 < k)
  | lowerBound
      {T : Candidate} (fields : LowerBoundPackage T)
      (k : Nat) (positive : 0 < k)
  | baseWordSeparation {T : Candidate} (fields : BaseWordSeparationPackage T)
  | transitionPeriod (package : TransitionPeriodBlockPackage)

namespace FixedBlockPackage

def blockIndex : FixedBlockPackage -> Nat
  | wordSeparation fields => fields.length
  | separatedFamily _ k _ => k
  | lowerBound _ k _ => k
  | baseWordSeparation fields => fields.checkedWord.length
  | transitionPeriod package =>
      TransitionPeriodFinalW11.PeriodBlockPackage.blockIndex package

theorem fixedBlockTarget
    (package : FixedBlockPackage) :
    FixedTarget (16 * blockIndex package) := by
  cases package with
  | wordSeparation fields =>
      exact PeriodTargetFinalW11.fixedTarget_of_wordSeparationFields fields
  | separatedFamily fields k hk =>
      exact
        PeriodTargetFinalW11.fixedBlockTarget_of_separatedFamilyFields
          fields k hk
  | lowerBound fields k hk =>
      exact
        PeriodTargetFinalW11.fixedBlockTarget_of_lowerBoundFields fields k hk
  | baseWordSeparation fields =>
      exact
        PeriodTargetFinalW11.aggregate_fixedTarget_of_baseWordSeparationFields
          fields
  | transitionPeriod package =>
      exact
        PeriodTargetFinalW11.fixedTarget_of_transitionPeriodBlockPackage
          package

end FixedBlockPackage

/-! ## Conditional projection rows -/

/-- Exact, eventual, and arbitrary target projections from one package. -/
structure ConditionalProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Exact, fixed, eventual, and arbitrary target projections from one package. -/
structure FullProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Fixed-block projection from one package. -/
structure BlockProjection (alpha : Type) where
  blockIndex : alpha -> Nat
  fixedBlockTarget :
    forall package : alpha, FixedTarget (16 * blockIndex package)

def projectionOfPeriodFinal
    {alpha : Sort u}
    (R : PeriodFinalIntegratedW11.TargetRoute alpha) :
    FullProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def projectionOfRouteSummary
    {alpha : Sort u}
    (R : PachTothW11RouteSummaryFinal.ConditionalProjection alpha) :
    FullProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def targetPackageProjection : ConditionalProjection TargetPackage where
  exactTarget := TargetPackage.exactTarget
  eventualTarget := TargetPackage.eventualTarget
  arbitraryTarget := TargetPackage.arbitraryTarget

def fixedBlockProjection : BlockProjection FixedBlockPackage where
  blockIndex := FixedBlockPackage.blockIndex
  fixedBlockTarget := FixedBlockPackage.fixedBlockTarget

/-- Conditional projection rows retained by the period route summary. -/
structure ConditionalProjectionRows where
  targetPackages : ConditionalProjection TargetPackage
  fixedBlocks : BlockProjection FixedBlockPackage
  periodFinalSeparatedFamily :
    forall T : Candidate,
      FullProjection (PeriodFinalIntegratedW11.SeparatedFamilyFields T)
  periodFinalLowerBound :
    forall T : Candidate,
      FullProjection (PeriodFinalIntegratedW11.LowerBoundFields T)
  periodFinalExactCandidate :
    forall T : Candidate,
      FullProjection (PeriodFinalIntegratedW11.ExactCandidateFields T)
  routeSummarySeparatedFamily :
    forall T : Candidate,
      FullProjection (PeriodFinalIntegratedW11.SeparatedFamilyFields T)
  routeSummaryLowerBound :
    forall T : Candidate,
      FullProjection (PeriodFinalIntegratedW11.LowerBoundFields T)
  routeSummaryExactCandidate :
    forall T : Candidate,
      FullProjection (PeriodFinalIntegratedW11.ExactCandidateFields T)

/-- Checked conditional projections for period packages. -/
def conditionalProjectionRows : ConditionalProjectionRows where
  targetPackages := targetPackageProjection
  fixedBlocks := fixedBlockProjection
  periodFinalSeparatedFamily := fun T =>
    projectionOfPeriodFinal
      (PeriodFinalIntegratedW11.separatedFamilyTargetRoute T)
  periodFinalLowerBound := fun T =>
    projectionOfPeriodFinal
      (PeriodFinalIntegratedW11.lowerBoundTargetRoute T)
  periodFinalExactCandidate := fun T =>
    projectionOfPeriodFinal
      (PeriodFinalIntegratedW11.exactCandidateTargetRoute T)
  routeSummarySeparatedFamily := fun T =>
    projectionOfRouteSummary
      (PachTothW11RouteSummaryFinal.matrix.projections.periodSeparatedFamily
        T)
  routeSummaryLowerBound := fun T =>
    projectionOfRouteSummary
      (PachTothW11RouteSummaryFinal.matrix.projections.periodLowerBound T)
  routeSummaryExactCandidate := fun T =>
    projectionOfRouteSummary
      (PachTothW11RouteSummaryFinal.matrix.projections.periodExactCandidate
        T)

/-! ## Final aggregate consistency rows -/

/-- Final aggregate period projections retained beside the period rows. -/
structure FinalAggregateProjectionRows where
  baseWordSeparation :
    forall {T : Candidate}, forall fields : BaseWordSeparationPackage T,
      FixedTarget (16 * fields.checkedWord.length)
  baseExactCandidate :
    forall {T : Candidate}, BaseExactCandidatePackage T -> ArbitraryTarget
  transitionFinalPeriod :
    TransitionFinalIntegratedW11.PeriodPackage -> ArbitraryTarget

/-- Checked final aggregate period projections. -/
def finalAggregateProjectionRows : FinalAggregateProjectionRows where
  baseWordSeparation := fun D =>
    PeriodTargetFinalW11.aggregate_fixedTarget_of_baseWordSeparationFields D
  baseExactCandidate := fun D =>
    PeriodTargetFinalW11.aggregate_arbitraryTarget_of_baseExactCandidateFields
      D
  transitionFinalPeriod := fun package =>
    PachTothW11FinalAggregate.arbitraryTarget_of_transitionPeriodPackage
      package

/-! ## Explicit package ledger value -/

/-- Explicit package families and open-data ledgers used by this summary. -/
def explicitPackageLedger : ExplicitPackageLedger where
  periodTargetFinal := PeriodTargetFinalW11.explicitPackageLedger
  periodFinalFields := PeriodFinalIntegratedW11.fieldLedger
  transitionPeriodFields :=
    TransitionPeriodFinalW11.explicitRoutePeriodPackageFields
  routeSummaryOpenData := PachTothW11RouteSummaryFinal.explicitOpenData
  finalAggregateOpenData := PachTothW11FinalAggregate.explicitOpenData
  candidate := Candidate
  targetPackages := TargetPackage
  fixedBlockPackages := FixedBlockPackage
  wordSeparationPackages := WordSeparationPackage
  separatedFamilyPackages := SeparatedFamilyPackage
  lowerBoundPackages := LowerBoundPackage
  exactCandidatePackages := ExactCandidatePackage
  aggregatePackages := AggregatePackage
  baseWordSeparationPackages := BaseWordSeparationPackage
  baseExactCandidatePackages := BaseExactCandidatePackage
  transitionPeriodRoutePackages := TransitionPeriodRoutePackage
  transitionPeriodPeriodPackages := TransitionPeriodPeriodPackage
  transitionPeriodBlockPackages := TransitionPeriodBlockPackage

/-! ## Final summary matrix -/

/-- Concise checked final W11 period route summary. -/
structure Matrix where
  checked : CheckedLedgers
  packages : ExplicitPackageLedger
  projections : ConditionalProjectionRows
  finalAggregate : FinalAggregateProjectionRows

/-- The checked final W11 period route summary matrix. -/
def matrix : Matrix where
  checked := checkedLedgers
  packages := explicitPackageLedger
  projections := conditionalProjectionRows
  finalAggregate := finalAggregateProjectionRows

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public conditional projections -/

theorem exactTarget_of_targetPackage
    (package : TargetPackage) : ExactTarget :=
  matrix.projections.targetPackages.exactTarget package

theorem eventualTarget_of_targetPackage
    (package : TargetPackage) : EventualTarget :=
  matrix.projections.targetPackages.eventualTarget package

theorem arbitraryTarget_of_targetPackage
    (package : TargetPackage) : ArbitraryTarget :=
  matrix.projections.targetPackages.arbitraryTarget package

theorem fixedTarget_of_fixedBlockPackage
    (package : FixedBlockPackage) :
    FixedTarget (16 * FixedBlockPackage.blockIndex package) :=
  matrix.projections.fixedBlocks.fixedBlockTarget package

theorem arbitraryTarget_of_periodFinalSeparatedFamily
    {T : Candidate}
    (fields : PeriodFinalIntegratedW11.SeparatedFamilyFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodFinalSeparatedFamily T).arbitraryTarget fields

theorem arbitraryTarget_of_periodFinalLowerBound
    {T : Candidate}
    (fields : PeriodFinalIntegratedW11.LowerBoundFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodFinalLowerBound T).arbitraryTarget fields

theorem arbitraryTarget_of_periodFinalExactCandidate
    {T : Candidate}
    (fields : PeriodFinalIntegratedW11.ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.projections.periodFinalExactCandidate T).arbitraryTarget fields

theorem exactTarget_of_routeSummarySeparatedFamily
    {T : Candidate}
    (fields : PeriodFinalIntegratedW11.SeparatedFamilyFields T) :
    ExactTarget :=
  (matrix.projections.routeSummarySeparatedFamily T).exactTarget fields

theorem eventualTarget_of_routeSummaryLowerBound
    {T : Candidate}
    (fields : PeriodFinalIntegratedW11.LowerBoundFields T) :
    EventualTarget :=
  (matrix.projections.routeSummaryLowerBound T).eventualTarget fields

theorem arbitraryTarget_of_routeSummaryExactCandidate
    {T : Candidate}
    (fields : PeriodFinalIntegratedW11.ExactCandidateFields T) :
    ArbitraryTarget :=
  (matrix.projections.routeSummaryExactCandidate T).arbitraryTarget fields

/-! ## Public final aggregate consistency projections -/

theorem fixedTarget_of_baseWordSeparationPackage
    {T : Candidate}
    (fields : BaseWordSeparationPackage T) :
    FixedTarget (16 * fields.checkedWord.length) :=
  matrix.finalAggregate.baseWordSeparation fields

theorem arbitraryTarget_of_baseExactCandidatePackage
    {T : Candidate}
    (fields : BaseExactCandidatePackage T) :
    ArbitraryTarget :=
  matrix.finalAggregate.baseExactCandidate fields

theorem arbitraryTarget_of_transitionFinalPeriodPackage
    (package : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.finalAggregate.transitionFinalPeriod package

end

end PeriodRouteSummaryFinalW11
end PachToth
end ErdosProblems1066
