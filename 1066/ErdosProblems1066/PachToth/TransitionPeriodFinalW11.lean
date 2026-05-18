import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.PeriodFinalIntegratedW11
import ErdosProblems1066.PachToth.PeriodTargetIntegratedW11
import ErdosProblems1066.PachToth.TransitionTargetIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Final W11 transition/period consistency layer

This module is a package-indexed adapter between the final transition ledger,
the final period ledger, the target-facing route files, and the W11 aggregate
ledger.  Target conclusions below are projections from explicit route or period
packages only.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionPeriodFinalW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

abbrev TransitionFinalRoutePackage :=
  TransitionFinalIntegratedW11.RoutePackage

abbrev TransitionFinalPeriodPackage :=
  TransitionFinalIntegratedW11.PeriodPackage

abbrev TransitionFinalPeriodBlockPackage :=
  TransitionFinalIntegratedW11.PeriodBlockPackage

abbrev TransitionTargetRoutePackage :=
  TransitionTargetIntegratedW11.RoutePackage

abbrev TransitionTargetPeriodPackage :=
  TransitionTargetIntegratedW11.PeriodPackage

abbrev TransitionTargetCheckedWordSeparationPackage :=
  TransitionTargetIntegratedW11.CheckedWordSeparationPackage

abbrev TransitionTargetPeriodExplicitLowerBoundPackage :=
  TransitionTargetIntegratedW11.PeriodExplicitLowerBoundPackage

abbrev PeriodCandidate :=
  PeriodTargetIntegratedW11.Candidate

abbrev PeriodFinalWordSeparationFields :=
  PeriodFinalIntegratedW11.WordSeparationFields

abbrev PeriodFinalSeparatedFamilyFields :=
  PeriodFinalIntegratedW11.SeparatedFamilyFields

abbrev PeriodFinalLowerBoundFields :=
  PeriodFinalIntegratedW11.LowerBoundFields

abbrev PeriodFinalExactCandidateFields :=
  PeriodFinalIntegratedW11.ExactCandidateFields

abbrev PeriodFinalAggregateFields :=
  PeriodFinalIntegratedW11.AggregateFields

abbrev PeriodTargetCheckedWordSeparationFields :=
  PeriodTargetIntegratedW11.CheckedWordSeparationFields

abbrev PeriodTargetSeparatedFamilyFields :=
  PeriodTargetIntegratedW11.GeneratedFamilyRemainingFields

abbrev PeriodTargetCrossBlockLedgerFields :=
  PeriodTargetIntegratedW11.CrossBlockLedgerClosureFields

abbrev PeriodTargetExplicitLowerBoundFields :=
  PeriodTargetIntegratedW11.ExplicitLowerBoundClosureFields

abbrev PeriodTargetExactCandidateFields :=
  PeriodTargetIntegratedW11.ExactCandidatePeriodFields

abbrev PeriodTargetNonRigidRouteFields :=
  PeriodTargetIntegratedW11.PeriodNonRigidRouteFields

abbrev PeriodTargetTransitionRouteFields :=
  PeriodTargetIntegratedW11.TransitionRouteFields

/-! ## Shared conditional rows -/

/-- Full target projections from an explicit package shape. -/
structure TargetRow (alpha : Type) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Fixed-block projections from an explicit package shape. -/
structure BlockTargetRow (alpha : Type) where
  blockIndex : alpha -> Nat
  fixedBlockTarget :
    forall package : alpha, FixedTarget (16 * blockIndex package)

def rowOfTransitionFinal
    {alpha : Type}
    (R : TransitionFinalIntegratedW11.FinalTargetRow alpha) :
    TargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfTransitionTarget
    {alpha : Type}
    (R : TransitionTargetIntegratedW11.TargetProjectionRow alpha) :
    TargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := fun package n => R.arbitraryTarget package n
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfPeriodTarget
    {alpha : Type}
    (R : PeriodTargetIntegratedW11.TargetRoute alpha) :
    TargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfPeriodFinal
    {alpha : Type}
    (R : PeriodFinalIntegratedW11.TargetRoute alpha) :
    TargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-! ## Combined route packages -/

/-- Route packages from the final transition and target-facing period layers. -/
inductive RoutePackage where
  | transitionFinal (package : TransitionFinalRoutePackage)
  | transitionTarget (package : TransitionTargetRoutePackage)
  | periodTargetTransition (fields : PeriodTargetTransitionRouteFields)

namespace RoutePackage

def exactTarget (package : RoutePackage) : ExactTarget :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
        package
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
        package
  | periodTargetTransition fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionRouteFields
        fields

def fixedTarget (package : RoutePackage) (n : Nat) : FixedTarget n :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_routePackage
        package n
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
        package n
  | periodTargetTransition fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
        fields n

def eventualTarget (package : RoutePackage) : EventualTarget :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
        package
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
        package
  | periodTargetTransition fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
        fields

def arbitraryTarget (package : RoutePackage) : ArbitraryTarget :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
        package
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
        package
  | periodTargetTransition fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
        fields

end RoutePackage

def routeTargetRow : TargetRow RoutePackage where
  exactTarget := RoutePackage.exactTarget
  fixedTarget := RoutePackage.fixedTarget
  eventualTarget := RoutePackage.eventualTarget
  arbitraryTarget := RoutePackage.arbitraryTarget

/-! ## Combined period packages -/

/-- Period packages from transition-final, period-final, and target layers. -/
inductive PeriodPackage where
  | transitionFinal (package : TransitionFinalPeriodPackage)
  | transitionTarget (package : TransitionTargetPeriodPackage)
  | periodFinalSeparatedFamily
      {candidate : PeriodCandidate}
      (fields : PeriodFinalSeparatedFamilyFields candidate)
  | periodFinalLowerBound
      {candidate : PeriodCandidate}
      (fields : PeriodFinalLowerBoundFields candidate)
  | periodFinalExactCandidate
      {candidate : PeriodCandidate}
      (fields : PeriodFinalExactCandidateFields candidate)
  | periodFinalAggregateSeparatedFamily
      {candidate : PeriodCandidate}
      (fields : PeriodFinalAggregateFields candidate)
  | periodFinalAggregateLowerBound
      {candidate : PeriodCandidate}
      (fields : PeriodFinalAggregateFields candidate)
  | periodFinalAggregateExactCandidate
      {candidate : PeriodCandidate}
      (fields : PeriodFinalAggregateFields candidate)
  | periodTargetSeparatedFamily
      {candidate : PeriodCandidate}
      (fields : PeriodTargetSeparatedFamilyFields candidate)
  | periodTargetCrossBlockLedger
      {candidate : PeriodCandidate}
      (fields : PeriodTargetCrossBlockLedgerFields candidate)
  | periodTargetExplicitLowerBound
      {candidate : PeriodCandidate}
      (fields : PeriodTargetExplicitLowerBoundFields candidate)
  | periodTargetExactCandidate
      {candidate : PeriodCandidate}
      (fields : PeriodTargetExactCandidateFields candidate)
  | periodTargetNonRigidRoute (fields : PeriodTargetNonRigidRouteFields)

namespace PeriodPackage

def exactTarget (package : PeriodPackage) : ExactTarget :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_periodPackage
        package
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_periodPackage
        package
  | periodFinalSeparatedFamily fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_separatedFamilyFields
        fields
  | periodFinalLowerBound fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_lowerBoundFields
        fields
  | periodFinalExactCandidate fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_exactCandidateFields
        fields
  | periodFinalAggregateSeparatedFamily fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_aggregateSeparatedFamily
        fields
  | periodFinalAggregateLowerBound fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_aggregateLowerBound
        fields
  | periodFinalAggregateExactCandidate fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_aggregateExactCandidate
        fields
  | periodTargetSeparatedFamily fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_separatedFamilyFields
        fields
  | periodTargetCrossBlockLedger fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_crossBlockLedgerFields
        fields
  | periodTargetExplicitLowerBound fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
        fields
  | periodTargetExactCandidate fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
        fields
  | periodTargetNonRigidRoute fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_periodNonRigidRouteFields
        fields

def fixedTarget (package : PeriodPackage) (n : Nat) : FixedTarget n :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodPackage
        package n
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
        package n
  | periodFinalSeparatedFamily fields =>
      PeriodFinalIntegratedW11.SeparatedFamilyFields.fixedTarget fields n
  | periodFinalLowerBound fields =>
      PeriodFinalIntegratedW11.LowerBoundFields.fixedTarget fields n
  | periodFinalExactCandidate fields =>
      PeriodFinalIntegratedW11.ExactCandidateFields.fixedTarget fields n
  | periodFinalAggregateSeparatedFamily fields =>
      fields.separatedFamily.fixedTarget n
  | periodFinalAggregateLowerBound fields =>
      fields.lowerBound.fixedTarget n
  | periodFinalAggregateExactCandidate fields =>
      fields.exactCandidate.fixedTarget n
  | periodTargetSeparatedFamily fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_separatedFamilyFields
        fields n
  | periodTargetCrossBlockLedger fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_crossBlockLedgerFields
        fields n
  | periodTargetExplicitLowerBound fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_explicitLowerBoundFields
        fields n
  | periodTargetExactCandidate fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_exactCandidatePeriodFields
        fields n
  | periodTargetNonRigidRoute fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodNonRigidRouteFields
        fields n

def eventualTarget (package : PeriodPackage) : EventualTarget :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_periodPackage
        package
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_periodPackage
        package
  | periodFinalSeparatedFamily fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_separatedFamilyFields
        fields
  | periodFinalLowerBound fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_lowerBoundFields
        fields
  | periodFinalExactCandidate fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactCandidateFields
        fields
  | periodFinalAggregateSeparatedFamily fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_aggregateSeparatedFamily
        fields
  | periodFinalAggregateLowerBound fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_aggregateLowerBound
        fields
  | periodFinalAggregateExactCandidate fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_aggregateExactCandidate
        fields
  | periodTargetSeparatedFamily fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_separatedFamilyFields
        fields
  | periodTargetCrossBlockLedger fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_crossBlockLedgerFields
        fields
  | periodTargetExplicitLowerBound fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_explicitLowerBoundFields
        fields
  | periodTargetExactCandidate fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactCandidatePeriodFields
        fields
  | periodTargetNonRigidRoute fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_periodNonRigidRouteFields
        fields

def arbitraryTarget (package : PeriodPackage) : ArbitraryTarget :=
  match package with
  | transitionFinal package =>
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
        package
  | transitionTarget package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
        package
  | periodFinalSeparatedFamily fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_separatedFamilyFields
        fields
  | periodFinalLowerBound fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_lowerBoundFields
        fields
  | periodFinalExactCandidate fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidateFields
        fields
  | periodFinalAggregateSeparatedFamily fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_aggregateSeparatedFamily
        fields
  | periodFinalAggregateLowerBound fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_aggregateLowerBound
        fields
  | periodFinalAggregateExactCandidate fields =>
      PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_aggregateExactCandidate
        fields
  | periodTargetSeparatedFamily fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_separatedFamilyFields
        fields
  | periodTargetCrossBlockLedger fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLedgerFields
        fields
  | periodTargetExplicitLowerBound fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
        fields
  | periodTargetExactCandidate fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
        fields
  | periodTargetNonRigidRoute fields =>
      PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
        fields

end PeriodPackage

def periodTargetRow : TargetRow PeriodPackage where
  exactTarget := PeriodPackage.exactTarget
  fixedTarget := PeriodPackage.fixedTarget
  eventualTarget := PeriodPackage.eventualTarget
  arbitraryTarget := PeriodPackage.arbitraryTarget

/-! ## Fixed period block packages -/

/-- Packages whose natural conclusion is an exact target at one block count. -/
inductive PeriodBlockPackage where
  | transitionFinal (package : TransitionFinalPeriodBlockPackage)
  | transitionTargetCheckedWordSeparation
      (package : TransitionTargetCheckedWordSeparationPackage)
  | transitionTargetExplicitLowerBound
      (package : TransitionTargetPeriodExplicitLowerBoundPackage)
      (k : Nat) (positive : 0 < k)
  | periodFinalWordSeparation
      {candidate : PeriodCandidate}
      (fields : PeriodFinalWordSeparationFields candidate)
  | periodFinalSeparatedFamily
      {candidate : PeriodCandidate}
      (fields : PeriodFinalSeparatedFamilyFields candidate)
      (k : Nat) (positive : 0 < k)
  | periodFinalLowerBound
      {candidate : PeriodCandidate}
      (fields : PeriodFinalLowerBoundFields candidate)
      (k : Nat) (positive : 0 < k)
  | periodTargetCheckedWordSeparation
      {candidate : PeriodCandidate}
      (fields : PeriodTargetCheckedWordSeparationFields candidate)
  | periodTargetSeparatedFamily
      {candidate : PeriodCandidate}
      (fields : PeriodTargetSeparatedFamilyFields candidate)
      (k : Nat) (positive : 0 < k)
  | periodTargetExplicitLowerBound
      {candidate : PeriodCandidate}
      (fields : PeriodTargetExplicitLowerBoundFields candidate)
      (k : Nat) (positive : 0 < k)

namespace PeriodBlockPackage

def blockIndex : PeriodBlockPackage -> Nat
  | transitionFinal package =>
      TransitionFinalIntegratedW11.PeriodBlockPackage.blockIndex package
  | transitionTargetCheckedWordSeparation package =>
      package.fields.checkedWord.length
  | transitionTargetExplicitLowerBound _ k _ => k
  | periodFinalWordSeparation fields => fields.length
  | periodFinalSeparatedFamily _ k _ => k
  | periodFinalLowerBound _ k _ => k
  | periodTargetCheckedWordSeparation fields => fields.checkedWord.length
  | periodTargetSeparatedFamily _ k _ => k
  | periodTargetExplicitLowerBound _ k _ => k

theorem fixedBlockTarget
    (package : PeriodBlockPackage) :
    FixedTarget (16 * package.blockIndex) := by
  cases package with
  | transitionFinal package =>
      exact
        TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodBlockPackage
          package
  | transitionTargetCheckedWordSeparation package =>
      exact
        TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparationPackage
          package
  | transitionTargetExplicitLowerBound package k hk =>
      exact
        TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundPackage
          package k hk
  | periodFinalWordSeparation fields =>
      exact
        PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_wordSeparationFields
          fields
  | periodFinalSeparatedFamily fields k hk =>
      exact
        PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_separatedFamilyFields
          fields k hk
  | periodFinalLowerBound fields k hk =>
      exact
        PeriodFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_lowerBoundFields
          fields k hk
  | periodTargetCheckedWordSeparation fields =>
      exact
        PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
          fields
  | periodTargetSeparatedFamily fields k hk =>
      exact
        PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_separatedFamilyFields
          fields k hk
  | periodTargetExplicitLowerBound fields k hk =>
      exact
        PeriodTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundFields
          fields k hk

end PeriodBlockPackage

def periodBlockTargetRow : BlockTargetRow PeriodBlockPackage where
  blockIndex := PeriodBlockPackage.blockIndex
  fixedBlockTarget := PeriodBlockPackage.fixedBlockTarget

/-! ## Explicit package ledgers -/

/-- Explicit route and period package fields consumed by this layer. -/
structure ExplicitRoutePeriodPackageFields where
  routePackages : Type
  periodPackages : Type
  periodBlockPackages : Type
  transitionFinalRoutePackages : Type
  transitionFinalPeriodPackages : Type
  transitionTargetRoutePackages : Type
  transitionTargetPeriodPackages : Type
  periodFinalCandidates : Type
  periodFinalWordSeparationFields : periodFinalCandidates -> Type
  periodFinalSeparatedFamilyFields : periodFinalCandidates -> Type
  periodFinalLowerBoundFields : periodFinalCandidates -> Type
  periodFinalExactCandidateFields : periodFinalCandidates -> Type
  periodFinalAggregateFields : periodFinalCandidates -> Type
  periodTargetInputs : PeriodTargetIntegratedW11.ExplicitPeriodTargetInputs
  transitionFinalLedger : TransitionFinalIntegratedW11.ExplicitPackageLedger
  transitionTargetLedger :
    TransitionTargetIntegratedW11.ExplicitTargetPackageLedger
  finalAggregateOpenData : PachTothW11FinalAggregate.ExplicitOpenData

def explicitRoutePeriodPackageFields :
    ExplicitRoutePeriodPackageFields where
  routePackages := RoutePackage
  periodPackages := PeriodPackage
  periodBlockPackages := PeriodBlockPackage
  transitionFinalRoutePackages := TransitionFinalRoutePackage
  transitionFinalPeriodPackages := TransitionFinalPeriodPackage
  transitionTargetRoutePackages := TransitionTargetRoutePackage
  transitionTargetPeriodPackages := TransitionTargetPeriodPackage
  periodFinalCandidates := PeriodCandidate
  periodFinalWordSeparationFields := PeriodFinalWordSeparationFields
  periodFinalSeparatedFamilyFields := PeriodFinalSeparatedFamilyFields
  periodFinalLowerBoundFields := PeriodFinalLowerBoundFields
  periodFinalExactCandidateFields := PeriodFinalExactCandidateFields
  periodFinalAggregateFields := PeriodFinalAggregateFields
  periodTargetInputs := PeriodTargetIntegratedW11.explicitPeriodTargetInputs
  transitionFinalLedger :=
    TransitionFinalIntegratedW11.explicitPackageLedger
  transitionTargetLedger :=
    TransitionTargetIntegratedW11.explicitTargetPackageLedger
  finalAggregateOpenData := PachTothW11FinalAggregate.explicitOpenData

/-- Checked ledgers imported by this adapter. -/
structure ImportedLedgers where
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  periodFinal : PeriodFinalIntegratedW11.Matrix
  periodTarget : PeriodTargetIntegratedW11.Matrix
  transitionTarget : TransitionTargetIntegratedW11.Matrix
  finalAggregate : PachTothW11FinalAggregate.Matrix

def importedLedgers : ImportedLedgers where
  transitionFinal := TransitionFinalIntegratedW11.matrix
  periodFinal := PeriodFinalIntegratedW11.matrix
  periodTarget := PeriodTargetIntegratedW11.matrix
  transitionTarget := TransitionTargetIntegratedW11.matrix
  finalAggregate := PachTothW11FinalAggregate.matrix

/-- Conditional projection rows exposed by the consistency layer. -/
structure ProjectionRows where
  route : TargetRow RoutePackage
  period : TargetRow PeriodPackage
  periodBlock : BlockTargetRow PeriodBlockPackage
  transitionFinalRoute : TargetRow TransitionFinalRoutePackage
  transitionFinalPeriod : TargetRow TransitionFinalPeriodPackage
  transitionTargetRoute : TargetRow TransitionTargetRoutePackage
  transitionTargetPeriod : TargetRow TransitionTargetPeriodPackage

def projectionRows : ProjectionRows where
  route := routeTargetRow
  period := periodTargetRow
  periodBlock := periodBlockTargetRow
  transitionFinalRoute :=
    rowOfTransitionFinal TransitionFinalIntegratedW11.routeTargetRow
  transitionFinalPeriod :=
    rowOfTransitionFinal TransitionFinalIntegratedW11.periodTargetRow
  transitionTargetRoute :=
    rowOfTransitionTarget TransitionTargetIntegratedW11.routeTargetRow
  transitionTargetPeriod :=
    rowOfTransitionTarget TransitionTargetIntegratedW11.periodTargetRow

/-- Final transition/period consistency matrix. -/
structure Matrix where
  fields : ExplicitRoutePeriodPackageFields
  imported : ImportedLedgers
  projections : ProjectionRows
  aggregateAvailability : PachTothW11FinalAggregate.FinalLedgerAvailability

def matrix : Matrix where
  fields := explicitRoutePeriodPackageFields
  imported := importedLedgers
  projections := projectionRows
  aggregateAvailability :=
    PachTothW11FinalAggregate.finalLedgerAvailability

/-! ## Public conditional route projections -/

theorem targetUpperConstructionFiveSixteen_of_routePackage
    (package : RoutePackage) : ExactTarget :=
  matrix.projections.route.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_routePackage
    (package : RoutePackage) (n : Nat) : FixedTarget n :=
  matrix.projections.route.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_routePackage
    (package : RoutePackage) : EventualTarget :=
  matrix.projections.route.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_routePackage
    (package : RoutePackage) : ArbitraryTarget :=
  matrix.projections.route.arbitraryTarget package

/-! ## Public conditional period projections -/

theorem targetUpperConstructionFiveSixteen_of_periodPackage
    (package : PeriodPackage) : ExactTarget :=
  matrix.projections.period.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_periodPackage
    (package : PeriodPackage) (n : Nat) : FixedTarget n :=
  matrix.projections.period.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_periodPackage
    (package : PeriodPackage) : EventualTarget :=
  matrix.projections.period.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
    (package : PeriodPackage) : ArbitraryTarget :=
  matrix.projections.period.arbitraryTarget package

theorem targetUpperConstructionFiveSixteenAt_of_periodBlockPackage
    (package : PeriodBlockPackage) :
    FixedTarget (16 * PeriodBlockPackage.blockIndex package) :=
  matrix.projections.periodBlock.fixedBlockTarget package

/-! ## Aggregate-facing conditional projections -/

theorem aggregate_arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalRoutePackage) : ArbitraryTarget :=
  PachTothW11FinalAggregate.arbitraryTarget_of_transitionRoutePackage
    package

theorem aggregate_arbitraryTarget_of_transitionPeriodPackage
    (package : TransitionFinalPeriodPackage) : ArbitraryTarget :=
  PachTothW11FinalAggregate.arbitraryTarget_of_transitionPeriodPackage
    package

theorem aggregate_arbitraryTarget_of_periodTargetExactCandidateFields
    {candidate : PeriodCandidate}
    (fields : PeriodTargetExactCandidateFields candidate) :
    ArbitraryTarget :=
  PachTothW11FinalAggregate.arbitraryTarget_of_periodExactCandidateFields
    fields

theorem aggregate_periodFinalStatus :
    matrix.aggregateAvailability.periodFinal =
      PachTothW11FinalAggregate.LedgerAvailability.absent :=
  PachTothW11FinalAggregate.periodFinalIntegratedW11_absent

end

end TransitionPeriodFinalW11
end PachToth
end ErdosProblems1066
