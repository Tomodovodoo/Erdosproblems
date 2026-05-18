import ErdosProblems1066.PachToth.TransitionCheckedIntegratedW11
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.PeriodIntegratedW11
import ErdosProblems1066.PachToth.ArbitraryNIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 transition consistency matrix

This file checks that the corrected W11 transition package rows, the period
facade rows, the arbitrary-`n` facade rows, and the top-level W11 integrated
matrix can be imported and projected together.

All target rows below are still conditional on a visible package argument.
Concrete four-target route gaps stay recorded as blockers.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionConsistencyW11

noncomputable section

universe u

abbrev TransitionCandidate :=
  TransitionCheckedIntegratedW11.TransitionCandidate

abbrev FilteredSameOpposite :=
  TransitionCheckedIntegratedW11.FilteredSameOpposite

abbrev TransitionRemainingFields (T : TransitionCandidate) :=
  TransitionCheckedIntegratedW11.TransitionRemainingFields T

abbrev TransitionRouteFields :=
  TransitionCheckedIntegratedW11.TransitionRouteFields

abbrev CompletedFilteredRouteFields (F : FilteredSameOpposite) :=
  TransitionCheckedIntegratedW11.CompletedFilteredRouteFields F

abbrev CandidateAssemblyFields :=
  TransitionCheckedIntegratedW11.CandidateAssemblyFields

abbrev RoleEquationRouteFields :=
  TransitionCheckedIntegratedW11.RoleEquationRouteFields

abbrev CrossBlockPeriodSearchFamily :=
  TransitionCheckedIntegratedW11.InequalityPeriodFamily

abbrev CrossBlockInequalityLedger
    (F : CrossBlockPeriodSearchFamily) :=
  TransitionCheckedIntegratedW11.RawCrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : CrossBlockPeriodSearchFamily) :=
  TransitionCheckedIntegratedW11.CrossBlockClosureLedger F

abbrev ExactTargetAssumptions :=
  PeriodIntegratedW11.ExactTargetAssumptions

abbrev EventualSmallCaseAssumptions :=
  PeriodIntegratedW11.EventualSmallCaseAssumptions

abbrev ArbitraryNTargetFacade :=
  ArbitraryNIntegratedW11.ArbitraryNTargetFacade

abbrev ThresholdTargetFacade :=
  ArbitraryNIntegratedW11.ThresholdTargetFacade

abbrev ConcreteSameOppositeCandidateFields : Prop :=
  exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
    F.same.parameters.placeNext =
      RoleHingeConcreteSearch.samePlaceNext /\
    F.opposite.parameters.placeNext =
      RoleHingeConcreteSearch.oppositePlaceNext

/-! ## Shared target facade rows -/

theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

def targetFacadeOfFixedArbitrary
    (fixedTarget :
      forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n)
    (arbitraryTarget :
      PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    ArbitraryNTargetFacade where
  fixedTarget := fixedTarget
  arbitraryTarget := arbitraryTarget

/-- Exact, fixed, eventual, arbitrary, and arbitrary-`n` facade projections
from one explicit package shape. -/
structure UnifiedTargetRow (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  targetFacade : alpha -> ArbitraryNTargetFacade

def rowOfCheckedTargetRow
    {alpha : Sort u}
    (R : TransitionCheckedIntegratedW11.CheckedTargetRow alpha) :
    UnifiedTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := fun a =>
    targetFacadeOfFixedArbitrary (R.fixedTarget a) (R.arbitraryTarget a)

def rowOfPeriodTargetRow
    {alpha : Sort u}
    (R : PeriodIntegratedW11.TargetFacadeRow alpha) :
    UnifiedTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

def rowOfArbitraryExactBlockRow
    {alpha : Sort u}
    (R : ArbitraryNIntegratedW11.ExactBlockFacadeRow alpha) :
    UnifiedTargetRow alpha where
  exactTarget := R.blockTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget
  targetFacade := R.targetFacade

/-! ## Imported matrices and blockers -/

/-- The checked W11 matrices used by this consistency layer. -/
structure ImportedMatrices where
  checkedTransition : TransitionCheckedIntegratedW11.Matrix
  transition : TransitionIntegratedW11.Matrix
  period : PeriodIntegratedW11.Matrix
  arbitraryN : ArbitraryNIntegratedW11.Matrix
  pachToth : PachTothW11IntegratedMatrix.Matrix

def importedMatrices : ImportedMatrices where
  checkedTransition := TransitionCheckedIntegratedW11.matrix
  transition := TransitionIntegratedW11.matrix
  period := PeriodIntegratedW11.matrix
  arbitraryN := ArbitraryNIntegratedW11.matrix
  pachToth := PachTothW11IntegratedMatrix.matrix

/-- Concrete blockers that prevent this matrix from asserting a bare target. -/
structure ExplicitBlockers where
  checked : TransitionCheckedIntegratedW11.BlockerLedger
  transition : TransitionIntegratedW11.BlockerLedger
  inherited : PachTothW11ClosureMatrix.InheritedFieldLedger
  checkedRouteClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  checkedCompletedFilteredRoute :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  checkedSameOppositeCandidateFields :
    Not ConcreteSameOppositeCandidateFields
  checkedMissingCandidateRows :
    forall C : ExactLocalClosureW11.CandidateRows,
      Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C)
  inheritedRouteClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  inheritedCompletedFilteredRoute :
    PachTothW11ClosureMatrix.W11CompletedFilteredRouteFields
        FlexibleTransitionSearchW11.concreteFourTargetCheckedRows.filtered ->
      False
  inheritedFullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap

def explicitBlockers : ExplicitBlockers where
  checked := TransitionCheckedIntegratedW11.matrix.blockers
  transition := TransitionIntegratedW11.matrix.blockers
  inherited := PachTothW11ClosureMatrix.inheritedFieldLedger
  checkedRouteClaim :=
    TransitionCheckedIntegratedW11.concreteFourTargetRouteClaim_blocked
  checkedCompletedFilteredRoute :=
    TransitionCheckedIntegratedW11.concreteFourTargetCompletedFilteredRoute_blocked
  checkedSameOppositeCandidateFields :=
    TransitionCheckedIntegratedW11.concreteFourTargetSameOppositeCandidateFields_blocked
  checkedMissingCandidateRows :=
    TransitionCheckedIntegratedW11.concreteMissingCandidateRows_blocked
  inheritedRouteClaim :=
    TransitionIntegratedW11.inheritedConcreteFourTargetRouteClaim_blocked
  inheritedCompletedFilteredRoute :=
    TransitionIntegratedW11.inheritedConcreteFourTargetCompletedFilteredRoute_blocked
  inheritedFullSameRestShortcut :=
    TransitionIntegratedW11.inheritedConcreteFourTargetFullSameRestShortcut_blocked

/-! ## Unified route rows -/

def checkedTransitionRouteRow :
    UnifiedTargetRow TransitionRouteFields :=
  rowOfCheckedTargetRow
    TransitionCheckedIntegratedW11.matrix.transitionRouteFields

def periodTransitionRouteRow :
    UnifiedTargetRow TransitionRouteFields :=
  rowOfPeriodTargetRow PeriodIntegratedW11.matrix.transitionRouteFields

def pachTothTransitionRouteRow :
    UnifiedTargetRow TransitionRouteFields where
  exactTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_transitionRouteFields
  fixedTarget := fun R n =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
      R n
  eventualTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
  arbitraryTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
  targetFacade := fun R =>
    targetFacadeOfFixedArbitrary
      (fun n =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
          R n)
      (PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
        R)

def checkedTransitionRemainingRow
    (T : TransitionCandidate) :
    UnifiedTargetRow (TransitionRemainingFields T) :=
  rowOfCheckedTargetRow
    (TransitionCheckedIntegratedW11.matrix.transitionRemainingFields T)

def periodTransitionRemainingRow
    (T : TransitionCandidate) :
    UnifiedTargetRow (TransitionRemainingFields T) :=
  rowOfPeriodTargetRow
    (PeriodIntegratedW11.matrix.transitionRemainingFields T)

def pachTothTransitionRemainingRow
    (T : TransitionCandidate) :
    UnifiedTargetRow (TransitionRemainingFields T) where
  exactTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_transitionRemainingFields
  fixedTarget := fun R n =>
    (PachTothW11IntegratedMatrix.matrix.flexibleTransitionClosure
      |>.transitionRemainingTargets T).fixedTarget R n
  eventualTarget := fun R =>
    (PachTothW11IntegratedMatrix.matrix.flexibleTransitionClosure
      |>.transitionRemainingTargets T).eventualTarget R
  arbitraryTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRemainingFields
  targetFacade := fun R =>
    targetFacadeOfFixedArbitrary
      (fun n =>
        (PachTothW11IntegratedMatrix.matrix.flexibleTransitionClosure
          |>.transitionRemainingTargets T).fixedTarget R n)
      (PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRemainingFields
        R)

def checkedCrossBlockClosureRow
    (F : CrossBlockPeriodSearchFamily) :
    UnifiedTargetRow (CrossBlockClosureLedger F) :=
  rowOfCheckedTargetRow
    (TransitionCheckedIntegratedW11.matrix.crossBlockClosureLedger F)

def periodCrossBlockClosureRow
    (F : CrossBlockPeriodSearchFamily) :
    UnifiedTargetRow (CrossBlockClosureLedger F) :=
  rowOfPeriodTargetRow
    (PeriodIntegratedW11.matrix.crossBlockClosureLedgers F)

def arbitraryNCrossBlockClosureRow
    (F : CrossBlockPeriodSearchFamily) :
    UnifiedTargetRow (CrossBlockClosureLedger F) where
  exactTarget := fun C =>
    (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).blockTarget C
  fixedTarget := fun C n =>
    (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).fixedTarget C n
  eventualTarget := fun C =>
    (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).eventualTarget C
  arbitraryTarget := fun C =>
    (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).arbitraryTarget C
  targetFacade := fun C =>
    (ArbitraryNIntegratedW11.matrix.crossBlockClosure F).targetFacade C

def pachTothCrossBlockClosureRow
    (F : CrossBlockPeriodSearchFamily) :
    UnifiedTargetRow (CrossBlockClosureLedger F) where
  exactTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
  fixedTarget := fun C n =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
      C n
  eventualTarget := fun C =>
    eventualTargetOfArbitrary
      (PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        C)
  arbitraryTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
  targetFacade := fun C =>
    targetFacadeOfFixedArbitrary
      (fun n =>
        PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
          C n)
      (PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        C)

def periodExactAssumptionsRow :
    UnifiedTargetRow ExactTargetAssumptions :=
  rowOfPeriodTargetRow PeriodIntegratedW11.matrix.exactTargetAssumptions

def arbitraryNExactAssumptionsRow :
    UnifiedTargetRow ExactTargetAssumptions :=
  rowOfArbitraryExactBlockRow
    ArbitraryNIntegratedW11.matrix.exactTargetAssumptions

def pachTothExactAssumptionsRow :
    UnifiedTargetRow ExactTargetAssumptions where
  exactTarget := fun A =>
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.exactAssumptions
      |>.exactTarget A
  fixedTarget := fun A n =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_exactTargetAssumptions
      A n
  eventualTarget := fun A =>
    eventualTargetOfArbitrary
      (PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_exactTargetAssumptions
        A)
  arbitraryTarget :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_exactTargetAssumptions
  targetFacade := fun A =>
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.exactAssumptions
      |>.targetFacade A

/-! ## Consistency snapshots -/

/-- One transition route package projected through all checked route facades. -/
structure TransitionRouteConsistency
    (R : TransitionRouteFields) where
  checkedExact : PachToth.targetUpperConstructionFiveSixteen
  checkedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  checkedEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  checkedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  checkedFacade : ArbitraryNTargetFacade
  transitionExact : PachToth.targetUpperConstructionFiveSixteen
  transitionEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  transitionArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  periodArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodFacade : ArbitraryNTargetFacade
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothFacade : ArbitraryNTargetFacade

def transitionRouteConsistency
    (R : TransitionRouteFields) :
    TransitionRouteConsistency R where
  checkedExact := checkedTransitionRouteRow.exactTarget R
  checkedFixed := checkedTransitionRouteRow.fixedTarget R
  checkedEventual := checkedTransitionRouteRow.eventualTarget R
  checkedArbitrary := checkedTransitionRouteRow.arbitraryTarget R
  checkedFacade := checkedTransitionRouteRow.targetFacade R
  transitionExact :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionRouteFields
      R
  transitionEventual :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
      R
  transitionArbitrary :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
      R
  periodExact := periodTransitionRouteRow.exactTarget R
  periodFixed := periodTransitionRouteRow.fixedTarget R
  periodEventual := periodTransitionRouteRow.eventualTarget R
  periodArbitrary := periodTransitionRouteRow.arbitraryTarget R
  periodFacade := periodTransitionRouteRow.targetFacade R
  pachTothExact := pachTothTransitionRouteRow.exactTarget R
  pachTothFixed := pachTothTransitionRouteRow.fixedTarget R
  pachTothEventual := pachTothTransitionRouteRow.eventualTarget R
  pachTothArbitrary := pachTothTransitionRouteRow.arbitraryTarget R
  pachTothFacade := pachTothTransitionRouteRow.targetFacade R

/-- One transition remaining-fields package projected through checked,
period, and top-level W11 rows. -/
structure TransitionRemainingConsistency
    {T : TransitionCandidate}
    (R : TransitionRemainingFields T) where
  checkedExact : PachToth.targetUpperConstructionFiveSixteen
  checkedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  checkedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  transitionExact : PachToth.targetUpperConstructionFiveSixteen
  transitionArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodFacade : ArbitraryNTargetFacade
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothFacade : ArbitraryNTargetFacade

def transitionRemainingConsistency
    {T : TransitionCandidate}
    (R : TransitionRemainingFields T) :
    TransitionRemainingConsistency R where
  checkedExact := (checkedTransitionRemainingRow T).exactTarget R
  checkedFixed := (checkedTransitionRemainingRow T).fixedTarget R
  checkedArbitrary := (checkedTransitionRemainingRow T).arbitraryTarget R
  transitionExact :=
    (TransitionIntegratedW11.matrix.transitionRemainingFields T).exactTarget R
  transitionArbitrary :=
    (TransitionIntegratedW11.matrix.transitionRemainingFields T).arbitraryTarget R
  periodExact := (periodTransitionRemainingRow T).exactTarget R
  periodFixed := (periodTransitionRemainingRow T).fixedTarget R
  periodFacade := (periodTransitionRemainingRow T).targetFacade R
  pachTothExact := (pachTothTransitionRemainingRow T).exactTarget R
  pachTothFixed := (pachTothTransitionRemainingRow T).fixedTarget R
  pachTothArbitrary :=
    (pachTothTransitionRemainingRow T).arbitraryTarget R
  pachTothFacade := (pachTothTransitionRemainingRow T).targetFacade R

/-- A completed filtered route remains conditional and is also blocked for
the concrete four-target filtered package. -/
structure CompletedFilteredRouteConsistency
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) where
  checkedExact : PachToth.targetUpperConstructionFiveSixteen
  checkedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  checkedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  transitionExact : PachToth.targetUpperConstructionFiveSixteen
  transitionArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def completedFilteredRouteConsistency
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    CompletedFilteredRouteConsistency R where
  checkedExact :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_completedFilteredRouteFields
      R
  checkedFixed :=
    (TransitionCheckedIntegratedW11.matrix.completedFilteredRouteFields F)
      |>.fixedTarget R
  checkedArbitrary :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
      R
  transitionExact :=
    TransitionIntegratedW11.matrix.completedFilteredRouteFields F
      |>.exactTarget R
  transitionArbitrary :=
    TransitionIntegratedW11.matrix.completedFilteredRouteFields F
      |>.arbitraryTarget R
  pachTothExact :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_completedFilteredRouteFields
      R
  pachTothArbitrary :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
      R

/-- Role-hinge route fields compared with the period non-rigid facade after
forgetting to the transition route package. -/
structure RoleEquationRouteConsistency
    (R : RoleEquationRouteFields) where
  checkedExact : PachToth.targetUpperConstructionFiveSixteen
  checkedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  checkedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  transitionExact : PachToth.targetUpperConstructionFiveSixteen
  transitionArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def roleEquationRouteConsistency
    (R : RoleEquationRouteFields) :
    RoleEquationRouteConsistency R where
  checkedExact :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_roleEquationRouteFields
      R
  checkedFixed :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_roleEquationRouteFields
      R
  checkedArbitrary :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleEquationRouteFields
      R
  transitionExact :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteen_of_roleEquationRouteFields
      R
  transitionArbitrary :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleEquationRouteFields
      R
  periodExact :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteen_of_periodNonRigidRouteFields
      R.toNonRigidRouteFields
  periodFixed :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodNonRigidRouteFields
      R.toNonRigidRouteFields
  periodArbitrary :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
      R.toNonRigidRouteFields

/-- A cross-block closure ledger projected through transition, period,
arbitrary-`n`, and top-level W11 rows. -/
structure CrossBlockClosureConsistency
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) where
  checkedExact : PachToth.targetUpperConstructionFiveSixteen
  checkedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  checkedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  transitionExact : PachToth.targetUpperConstructionFiveSixteen
  transitionArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodFacade : ArbitraryNTargetFacade
  arbitraryNExact : PachToth.targetUpperConstructionFiveSixteen
  arbitraryNFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryNExactBlock :
    forall k : Nat, 0 < k ->
      PachToth.targetUpperConstructionFiveSixteenAt (16 * k)
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryNFacade : ArbitraryNTargetFacade
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothFacade : ArbitraryNTargetFacade

def crossBlockClosureConsistency
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    CrossBlockClosureConsistency C where
  checkedExact := (checkedCrossBlockClosureRow F).exactTarget C
  checkedFixed := (checkedCrossBlockClosureRow F).fixedTarget C
  checkedArbitrary := (checkedCrossBlockClosureRow F).arbitraryTarget C
  transitionExact :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
      C
  transitionArbitrary :=
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
      C
  periodExact := (periodCrossBlockClosureRow F).exactTarget C
  periodFixed := (periodCrossBlockClosureRow F).fixedTarget C
  periodFacade := (periodCrossBlockClosureRow F).targetFacade C
  arbitraryNExact := (arbitraryNCrossBlockClosureRow F).exactTarget C
  arbitraryNFixed := (arbitraryNCrossBlockClosureRow F).fixedTarget C
  arbitraryNExactBlock :=
    ArbitraryNIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockClosureLedger
      C
  arbitraryNArbitrary := (arbitraryNCrossBlockClosureRow F).arbitraryTarget C
  arbitraryNFacade := (arbitraryNCrossBlockClosureRow F).targetFacade C
  pachTothExact := (pachTothCrossBlockClosureRow F).exactTarget C
  pachTothFixed := (pachTothCrossBlockClosureRow F).fixedTarget C
  pachTothArbitrary := (pachTothCrossBlockClosureRow F).arbitraryTarget C
  pachTothFacade := (pachTothCrossBlockClosureRow F).targetFacade C

/-- A raw cross-block inequality ledger compared after each checked route
wraps it as a closure ledger. -/
structure RawCrossBlockLedgerConsistency
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) where
  checkedExact : PachToth.targetUpperConstructionFiveSixteen
  checkedFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  checkedArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodFacade : ArbitraryNTargetFacade
  arbitraryNFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryNFacade : ArbitraryNTargetFacade
  pachTothClosure : CrossBlockClosureLedger F
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary

def rawCrossBlockLedgerConsistency
    {F : CrossBlockPeriodSearchFamily}
    (L : CrossBlockInequalityLedger F) :
    RawCrossBlockLedgerConsistency L where
  checkedExact :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
      L
  checkedFixed :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_rawCrossBlockInequalityLedger
      L
  checkedArbitrary :=
    TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
      L
  periodExact :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
      L
  periodFixed :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_of_rawCrossBlockInequalityLedger
      L
  periodFacade :=
    (PeriodIntegratedW11.matrix.rawCrossBlockInequalityLedgers F)
      |>.targetFacade L
  arbitraryNFixed :=
    ArbitraryNIntegratedW11.fixedTargetOfRawCrossBlockInequalityLedger L
  arbitraryNArbitrary :=
    ArbitraryNIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
      L
  arbitraryNFacade :=
    ArbitraryNIntegratedW11.targetFacade_of_rawCrossBlockInequalityLedger L
  pachTothClosure := TransitionCheckedIntegratedW11.toCrossBlockClosureLedger L
  pachTothExact :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
      (TransitionCheckedIntegratedW11.toCrossBlockClosureLedger L)
  pachTothFixed := fun n =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
      (TransitionCheckedIntegratedW11.toCrossBlockClosureLedger L) n
  pachTothArbitrary :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
      (TransitionCheckedIntegratedW11.toCrossBlockClosureLedger L)

/-- Exact-target assumptions compared between the period, arbitrary-`n`, and
top-level W11 facades. -/
structure ExactAssumptionsConsistency
    (A : ExactTargetAssumptions) where
  periodExact : PachToth.targetUpperConstructionFiveSixteen
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodFacade : ArbitraryNTargetFacade
  arbitraryNExact : PachToth.targetUpperConstructionFiveSixteen
  arbitraryNFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryNFacade : ArbitraryNTargetFacade
  pachTothExact : PachToth.targetUpperConstructionFiveSixteen
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothFacade : ArbitraryNTargetFacade

def exactAssumptionsConsistency
    (A : ExactTargetAssumptions) :
    ExactAssumptionsConsistency A where
  periodExact := periodExactAssumptionsRow.exactTarget A
  periodFixed := periodExactAssumptionsRow.fixedTarget A
  periodArbitrary := periodExactAssumptionsRow.arbitraryTarget A
  periodFacade := periodExactAssumptionsRow.targetFacade A
  arbitraryNExact := arbitraryNExactAssumptionsRow.exactTarget A
  arbitraryNFixed := arbitraryNExactAssumptionsRow.fixedTarget A
  arbitraryNArbitrary := arbitraryNExactAssumptionsRow.arbitraryTarget A
  arbitraryNFacade := arbitraryNExactAssumptionsRow.targetFacade A
  pachTothExact := pachTothExactAssumptionsRow.exactTarget A
  pachTothFixed := pachTothExactAssumptionsRow.fixedTarget A
  pachTothArbitrary := pachTothExactAssumptionsRow.arbitraryTarget A
  pachTothFacade := pachTothExactAssumptionsRow.targetFacade A

/-- Eventual large-case plus finite small-case assumptions compared across
the period, arbitrary-`n`, and top-level W11 facades. -/
structure EventualSmallCaseConsistency
    (A : EventualSmallCaseAssumptions) where
  periodThreshold : Nat
  periodEventual : PachToth.targetUpperConstructionFiveSixteenEventually
  periodFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  periodArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  periodFacade : ArbitraryNTargetFacade
  arbitraryNThreshold : Nat
  arbitraryNFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryNLarge :
    forall n : Nat, arbitraryNThreshold <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  arbitraryNSmall :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo arbitraryNThreshold
  arbitraryNArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  arbitraryNThresholdFacade : ThresholdTargetFacade
  arbitraryNFacade : ArbitraryNTargetFacade
  pachTothThreshold : Nat
  pachTothFixed :
    forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothLarge :
    forall n : Nat, pachTothThreshold <= n ->
      PachToth.targetUpperConstructionFiveSixteenAt n
  pachTothSmall :
    PachToth.targetUpperConstructionFiveSixteenSmallUpTo pachTothThreshold
  pachTothArbitrary : PachToth.targetUpperConstructionFiveSixteenArbitrary
  pachTothFacade : ArbitraryNTargetFacade

def eventualSmallCaseConsistency
    (A : EventualSmallCaseAssumptions) :
    EventualSmallCaseConsistency A where
  periodThreshold :=
    PeriodIntegratedW11.matrix.eventualSmallCaseAssumptions.vertexThreshold A
  periodEventual :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_eventualSmallCaseAssumptions
      A
  periodFixed :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_of_eventualSmallCaseAssumptions
      A
  periodArbitrary :=
    PeriodIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_eventualSmallCaseAssumptions
      A
  periodFacade :=
    PeriodIntegratedW11.matrix.eventualSmallCaseAssumptions.targetFacade A
  arbitraryNThreshold :=
    ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions.vertexThreshold A
  arbitraryNFixed :=
    fun n =>
      ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions
        |>.arbitraryTarget A n
  arbitraryNLarge :=
    ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions.largeTarget A
  arbitraryNSmall :=
    ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions.smallTarget A
  arbitraryNArbitrary :=
    ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions.arbitraryTarget A
  arbitraryNThresholdFacade :=
    ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions.thresholdFacade A
  arbitraryNFacade :=
    ArbitraryNIntegratedW11.matrix.eventualSmallCaseAssumptions.targetFacade A
  pachTothThreshold :=
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.eventualSmallCaseAssumptions
      |>.vertexThreshold A
  pachTothFixed :=
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.eventualSmallCaseAssumptions
      |>.fixedTarget A
  pachTothLarge :=
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.eventualSmallCaseAssumptions
      |>.largeTarget A
  pachTothSmall :=
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.eventualSmallCaseAssumptions
      |>.smallTarget A
  pachTothArbitrary :=
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_eventualSmallCaseAssumptions
      A
  pachTothFacade :=
    PachTothW11IntegratedMatrix.matrix.arbitraryNTargetClosure
      |>.eventualSmallCaseAssumptions
      |>.targetFacade A

/-! ## Checked consistency matrix -/

/-- Public conditional projections assembled from the checked W11 transition,
period, arbitrary-`n`, and integrated Pach--Toth rows. -/
structure ProjectionRows where
  checkedTransitionRoute : UnifiedTargetRow TransitionRouteFields
  periodTransitionRoute : UnifiedTargetRow TransitionRouteFields
  pachTothTransitionRoute : UnifiedTargetRow TransitionRouteFields
  checkedTransitionRemaining :
    forall T : TransitionCandidate,
      UnifiedTargetRow (TransitionRemainingFields T)
  periodTransitionRemaining :
    forall T : TransitionCandidate,
      UnifiedTargetRow (TransitionRemainingFields T)
  pachTothTransitionRemaining :
    forall T : TransitionCandidate,
      UnifiedTargetRow (TransitionRemainingFields T)
  checkedCrossBlockClosure :
    forall F : CrossBlockPeriodSearchFamily,
      UnifiedTargetRow (CrossBlockClosureLedger F)
  periodCrossBlockClosure :
    forall F : CrossBlockPeriodSearchFamily,
      UnifiedTargetRow (CrossBlockClosureLedger F)
  arbitraryNCrossBlockClosure :
    forall F : CrossBlockPeriodSearchFamily,
      UnifiedTargetRow (CrossBlockClosureLedger F)
  pachTothCrossBlockClosure :
    forall F : CrossBlockPeriodSearchFamily,
      UnifiedTargetRow (CrossBlockClosureLedger F)
  periodExactAssumptions : UnifiedTargetRow ExactTargetAssumptions
  arbitraryNExactAssumptions : UnifiedTargetRow ExactTargetAssumptions
  pachTothExactAssumptions : UnifiedTargetRow ExactTargetAssumptions

def projectionRows : ProjectionRows where
  checkedTransitionRoute := checkedTransitionRouteRow
  periodTransitionRoute := periodTransitionRouteRow
  pachTothTransitionRoute := pachTothTransitionRouteRow
  checkedTransitionRemaining := checkedTransitionRemainingRow
  periodTransitionRemaining := periodTransitionRemainingRow
  pachTothTransitionRemaining := pachTothTransitionRemainingRow
  checkedCrossBlockClosure := checkedCrossBlockClosureRow
  periodCrossBlockClosure := periodCrossBlockClosureRow
  arbitraryNCrossBlockClosure := arbitraryNCrossBlockClosureRow
  pachTothCrossBlockClosure := pachTothCrossBlockClosureRow
  periodExactAssumptions := periodExactAssumptionsRow
  arbitraryNExactAssumptions := arbitraryNExactAssumptionsRow
  pachTothExactAssumptions := pachTothExactAssumptionsRow

/-- The checked W11 transition consistency matrix. -/
structure Matrix where
  imports : ImportedMatrices
  blockers : ExplicitBlockers
  projections : ProjectionRows
  transitionRoute :
    forall R : TransitionRouteFields, TransitionRouteConsistency R
  transitionRemaining :
    forall {T : TransitionCandidate} (R : TransitionRemainingFields T),
      TransitionRemainingConsistency R
  completedFilteredRoute :
    forall {F : FilteredSameOpposite} (R : CompletedFilteredRouteFields F),
      CompletedFilteredRouteConsistency R
  roleEquationRoute :
    forall R : RoleEquationRouteFields, RoleEquationRouteConsistency R
  crossBlockClosure :
    forall {F : CrossBlockPeriodSearchFamily} (C : CrossBlockClosureLedger F),
      CrossBlockClosureConsistency C
  rawCrossBlock :
    forall {F : CrossBlockPeriodSearchFamily} (L : CrossBlockInequalityLedger F),
      RawCrossBlockLedgerConsistency L
  exactAssumptions :
    forall A : ExactTargetAssumptions, ExactAssumptionsConsistency A
  eventualSmallCase :
    forall A : EventualSmallCaseAssumptions,
      EventualSmallCaseConsistency A

def matrix : Matrix where
  imports := importedMatrices
  blockers := explicitBlockers
  projections := projectionRows
  transitionRoute := transitionRouteConsistency
  transitionRemaining := fun R => transitionRemainingConsistency R
  completedFilteredRoute := fun R => completedFilteredRouteConsistency R
  roleEquationRoute := roleEquationRouteConsistency
  crossBlockClosure := fun C => crossBlockClosureConsistency C
  rawCrossBlock := fun L => rawCrossBlockLedgerConsistency L
  exactAssumptions := exactAssumptionsConsistency
  eventualSmallCase := eventualSmallCaseConsistency

/-! ## Public projections -/

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.transitionRoute R).checkedExact

theorem targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    (R : TransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.transitionRoute R).checkedFixed n

theorem targetFacade_of_transitionRouteFields
    (R : TransitionRouteFields) :
    ArbitraryNTargetFacade :=
  (matrix.transitionRoute R).checkedFacade

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockClosure C).arbitraryNArbitrary

theorem targetFacade_of_crossBlockClosureLedger
    {F : CrossBlockPeriodSearchFamily}
    (C : CrossBlockClosureLedger F) :
    ArbitraryNTargetFacade :=
  (matrix.crossBlockClosure C).arbitraryNFacade

theorem targetFacade_of_exactTargetAssumptions
    (A : ExactTargetAssumptions) :
    ArbitraryNTargetFacade :=
  (matrix.exactAssumptions A).arbitraryNFacade

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.checkedRouteClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.checkedCompletedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not ConcreteSameOppositeCandidateFields :=
  matrix.blockers.checkedSameOppositeCandidateFields

theorem inheritedFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.inheritedFullSameRestShortcut

end

end TransitionConsistencyW11
end PachToth
end ErdosProblems1066
