import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.FlexibleCandidateAssemblyW11
import ErdosProblems1066.PachToth.FlexibleBranchSearchSummaryW10
import ErdosProblems1066.PachToth.PachTothW10ClosureMatrix

set_option autoImplicit false

/-!
# W11 flexible transition closure ledger

This module is a checked ledger over the W11 flexible transition route.  It
records exactly which conditional Pach--Toth targets follow from the explicit
route fields, and keeps the concrete four-target shortcuts as named blockers.

No unconditional construction is added here: every target-producing statement
still consumes one visible field package.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleTransitionClosureW11

open FiniteGraph
open FiniteGraph.LocalVertex

universe u

abbrev R2 := Prod Real Real

abbrev BranchCandidate :=
  FlexibleTransitionSearchW11.BranchCandidate

abbrev SameOppositeCandidate :=
  FlexibleTransitionSearchW11.SameOppositeCandidate

abbrev FilteredSameOpposite :=
  FlexibleTransitionSearchW11.FilteredSameOpposite

abbrev TransitionRemainingFields (T : SameOppositeCandidate) :=
  FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields T

abbrev TransitionRouteFields :=
  FlexibleTransitionSearchW11.NonRigidRouteFields

abbrev CompletedFilteredRouteFields (F : FilteredSameOpposite) :=
  FlexibleTransitionSearchW11.CompletedFilteredRouteFields F

abbrev W10CompleteNonRigidFamilyFields :=
  FlexibleTransitionSearchW11.W10CompleteNonRigidFamilyFields

abbrev CandidateAssemblyFields :=
  FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields

abbrev PackedCandidateInequalities :=
  FlexibleCandidateAssemblyW11.PackedCandidateInequalities

abbrev W10RemainingDataLedger :=
  PachTothW10ClosureMatrix.RemainingDataLedger

abbrev W10ClosureMatrix :=
  PachTothW10ClosureMatrix.Matrix

abbrev W10BranchSurfaceRows :=
  FlexibleBranchSearchSummaryW10.BranchSurfaceRows

abbrev W10BlockedRoutes :=
  FlexibleBranchSearchSummaryW10.BlockedRoutes

/-! ## Target rows -/

/-- The strongest target facade used by this ledger: exact block-form target,
every fixed-`n` target, source-faithful eventual target, and arbitrary-`n`
target. -/
structure StrongTargetRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

namespace StrongTargetRow

/-- Build the full target facade from an exact target and the current
arbitrary-`n` target. -/
def ofExactArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    StrongTargetRow alpha where
  exactTarget := exactTarget
  fixedTarget := fun a n => arbitraryTarget a n
  eventualTarget := fun a =>
    Exists.intro 0 (fun n _hn => arbitraryTarget a n)
  arbitraryTarget := arbitraryTarget

end StrongTargetRow

/-- A supplied same/opposite candidate plus its explicit remaining period and
metric fields closes the current exact and arbitrary Pach--Toth targets. -/
def transitionRemainingFieldsRow
    (T : SameOppositeCandidate) :
    StrongTargetRow (TransitionRemainingFields T) :=
  StrongTargetRow.ofExactArbitrary
    FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields.targetUpperConstructionFiveSixteen
    FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields.targetUpperConstructionFiveSixteenArbitrary

/-- The W11 flexible non-rigid route fields close the strongest currently
available conditional Pach--Toth targets. -/
def transitionRouteFieldsRow :
    StrongTargetRow TransitionRouteFields :=
  StrongTargetRow.ofExactArbitrary
    FlexibleTransitionSearchW11.NonRigidRouteFields.targetUpperConstructionFiveSixteen
    FlexibleTransitionSearchW11.NonRigidRouteFields.targetUpperConstructionFiveSixteenArbitrary

/-- W10 complete non-rigid family fields close the same targets after
forgetting to the smaller W11 route interface. -/
def w10CompleteNonRigidFamilyFieldsRow :
    StrongTargetRow W10CompleteNonRigidFamilyFields :=
  StrongTargetRow.ofExactArbitrary
    FlexibleTransitionSearchW11.targetUpperConstructionFiveSixteen_of_w10CompleteNonRigidFamilyFields
    FlexibleTransitionSearchW11.targetUpperConstructionFiveSixteenArbitrary_of_w10CompleteNonRigidFamilyFields

/-- Completed filtered route fields also close the target once the missing
completion, period, and metric packages are all explicitly supplied. -/
def completedFilteredRouteFieldsRow
    (F : FilteredSameOpposite) :
    StrongTargetRow (CompletedFilteredRouteFields F) :=
  StrongTargetRow.ofExactArbitrary
    FlexibleTransitionSearchW11.CompletedFilteredRouteFields.targetUpperConstructionFiveSixteen
    (fun R =>
      R.toNonRigidRouteFields.targetUpperConstructionFiveSixteenArbitrary)

/-- The W11 candidate-assembly package closes the same target facade through
the packed cross-block inequality route. -/
def candidateAssemblyFieldsRow :
    StrongTargetRow CandidateAssemblyFields :=
  StrongTargetRow.ofExactArbitrary
    FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteen
    FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenArbitrary

/-! ## Concrete four-target blocker ledger -/

/-- Concrete shortcut branches currently blocked by checked W10/W11 rows. -/
structure ConcreteFourTargetShortcutBlockers where
  t11rNotPossible :
    Not (ExactLocalBranchSolverSurface.PossibleRow T1_1 LocalVertex.r)
  sameT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r
  oppositeT11RExactBase :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r
  sameFullExactLocal :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.samePlaceNext)
  oppositeFullExactLocal :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.oppositePlaceNext)
  coordinateRemainingRows :
    Not FlexibleBranchSearchSummaryW10.W10CoordinateRemainingRows
  transitionRemainingRows :
    Not FlexibleTransitionSearchW10.ConcreteFourTargetRemainingExactLocalEquations
  transitionFilteredCompletion :
    Not FlexibleBranchSearchSummaryW10.W10ConcreteFilteredCompletion
  sameBranchCandidate :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext)
  oppositeBranchCandidate :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.oppositePlaceNext)
  sameW10BranchCandidateFields :
    Not
      (exists B : FlexibleBranchSearchSummaryW10.W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.samePlaceNext)
  oppositeW10BranchCandidateFields :
    Not
      (exists B : FlexibleBranchSearchSummaryW10.W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.oppositePlaceNext)
  sameOppositeCandidateFields :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  routeClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  completedFilteredRoute :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  fullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  t11rRow :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction

/-- The checked concrete four-target blocker ledger. -/
def concreteFourTargetShortcutBlockers :
    ConcreteFourTargetShortcutBlockers where
  t11rNotPossible :=
    FlexibleBranchSearchSummaryW10.concreteT11R_not_possible
  sameT11RExactBase :=
    FlexibleBranchSearchSummaryW10.concreteSameT11R_exactBase_obstruction
  oppositeT11RExactBase :=
    FlexibleBranchSearchSummaryW10.concreteOppositeT11R_exactBase_obstruction
  sameFullExactLocal :=
    FlexibleBranchSearchSummaryW10.concreteSameFullExactLocal_blocked
  oppositeFullExactLocal :=
    FlexibleBranchSearchSummaryW10.concreteOppositeFullExactLocal_blocked
  coordinateRemainingRows :=
    FlexibleBranchSearchSummaryW10.concreteCoordinateRemainingRows_blocked
  transitionRemainingRows :=
    FlexibleBranchSearchSummaryW10.w10ConcreteTransitionRemainingRows_blocked
  transitionFilteredCompletion :=
    FlexibleBranchSearchSummaryW10.w10ConcreteFilteredCompletion_blocked
  sameBranchCandidate :=
    FlexibleTransitionSearchW11.not_sameConcreteBranchCandidate
  oppositeBranchCandidate :=
    FlexibleTransitionSearchW11.not_oppositeConcreteBranchCandidate
  sameW10BranchCandidateFields :=
    FlexibleBranchSearchSummaryW10.w10SameBranchCandidateFields_blocked
  oppositeW10BranchCandidateFields :=
    FlexibleBranchSearchSummaryW10.w10OppositeBranchCandidateFields_blocked
  sameOppositeCandidateFields :=
    FlexibleBranchSearchSummaryW10.w10SameOppositeCandidateFields_blocked
  routeClaim :=
    FlexibleTransitionSearchW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    FlexibleTransitionSearchW11.concreteFourTargetCompletedFilteredRoute_blocked
  fullSameRestShortcut :=
    PachTothW10ClosureMatrix.fullSameRestShortcut_blocked
  t11rRow :=
    PachTothW10ClosureMatrix.concreteT11RRow_blocked

/-! ## Explicit remaining construction data -/

/-- The construction data that is still assumed rather than produced. -/
structure RemainingConstructionLedger where
  transitionRemainingFields : SameOppositeCandidate -> Type
  transitionRouteFields : Type
  completedFilteredRouteFields : FilteredSameOpposite -> Type
  w10CompleteNonRigidFamilyFields : Type
  candidateAssemblyFields : Type
  packedCandidateInequalities : Type
  w10Matrix : Type 1
  w10RemainingDataLedger : Type 1
  w10BranchSurfaces : W10BranchSurfaceRows
  w10BlockedRoutes : W10BlockedRoutes
  transitionCheckedRows :
    FlexibleTransitionSearchW11.ConcreteFourTargetCheckedRows
  shortcutBlockers : ConcreteFourTargetShortcutBlockers

/-- The public W11 remaining-construction ledger. -/
def remainingConstructionLedger : RemainingConstructionLedger where
  transitionRemainingFields := TransitionRemainingFields
  transitionRouteFields := TransitionRouteFields
  completedFilteredRouteFields := CompletedFilteredRouteFields
  w10CompleteNonRigidFamilyFields := W10CompleteNonRigidFamilyFields
  candidateAssemblyFields := CandidateAssemblyFields
  packedCandidateInequalities := PackedCandidateInequalities
  w10Matrix := W10ClosureMatrix
  w10RemainingDataLedger := W10RemainingDataLedger
  w10BranchSurfaces := FlexibleBranchSearchSummaryW10.matrix.branchSurfaces
  w10BlockedRoutes := FlexibleBranchSearchSummaryW10.matrix.blocked
  transitionCheckedRows :=
    FlexibleTransitionSearchW11.concreteFourTargetCheckedRows
  shortcutBlockers := concreteFourTargetShortcutBlockers

/-! ## Closure matrix -/

/-- The W11 flexible transition closure matrix. -/
structure Matrix where
  remaining : RemainingConstructionLedger
  transitionRemainingTargets :
    forall T : SameOppositeCandidate,
      StrongTargetRow (TransitionRemainingFields T)
  transitionRouteTargets : StrongTargetRow TransitionRouteFields
  w10CompleteNonRigidFamilyTargets :
    StrongTargetRow W10CompleteNonRigidFamilyFields
  completedFilteredRouteTargets :
    forall F : FilteredSameOpposite,
      StrongTargetRow (CompletedFilteredRouteFields F)
  candidateAssemblyTargets : StrongTargetRow CandidateAssemblyFields
  concreteShortcutBlockers : ConcreteFourTargetShortcutBlockers

/-- The checked W11 flexible transition closure matrix. -/
def matrix : Matrix where
  remaining := remainingConstructionLedger
  transitionRemainingTargets := transitionRemainingFieldsRow
  transitionRouteTargets := transitionRouteFieldsRow
  w10CompleteNonRigidFamilyTargets := w10CompleteNonRigidFamilyFieldsRow
  completedFilteredRouteTargets := completedFilteredRouteFieldsRow
  candidateAssemblyTargets := candidateAssemblyFieldsRow
  concreteShortcutBlockers := concreteFourTargetShortcutBlockers

/-! ## Public target projections from W11 route fields -/

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (F : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transitionRouteTargets.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    (F : TransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.transitionRouteTargets.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
    (F : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transitionRouteTargets.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (F : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionRouteTargets.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_transitionRouteFields
    (F : TransitionRouteFields) (k : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  matrix.transitionRouteTargets.fixedTarget F (16 * k)

/-! ## Public projections from adjacent explicit field packages -/

theorem targetUpperConstructionFiveSixteen_of_transitionRemainingFields
    {T : SameOppositeCandidate} (R : TransitionRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.transitionRemainingTargets T).exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRemainingFields
    {T : SameOppositeCandidate} (R : TransitionRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.transitionRemainingTargets T).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.w10CompleteNonRigidFamilyTargets.exactTarget F

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_w10CompleteNonRigidFamilyFields
    (F : W10CompleteNonRigidFamilyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.w10CompleteNonRigidFamilyTargets.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_completedFilteredRouteFields
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.completedFilteredRouteTargets F).exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.completedFilteredRouteTargets F).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateAssemblyTargets.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.candidateAssemblyTargets.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.candidateAssemblyTargets.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateAssemblyTargets.arbitraryTarget F

/-! ## Public concrete shortcut blockers -/

theorem concreteFourTargetT11R_not_possible :
    Not (ExactLocalBranchSolverSurface.PossibleRow T1_1 LocalVertex.r) :=
  matrix.concreteShortcutBlockers.t11rNotPossible

theorem concreteFourTargetSameT11R_exactBase_obstruction :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext T1_1 LocalVertex.r :=
  matrix.concreteShortcutBlockers.sameT11RExactBase

theorem concreteFourTargetOppositeT11R_exactBase_obstruction :
    ExactLocalBranchSolverSurface.ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext T1_1 LocalVertex.r :=
  matrix.concreteShortcutBlockers.oppositeT11RExactBase

theorem concreteFourTargetSameFullExactLocal_blocked :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.samePlaceNext) :=
  matrix.concreteShortcutBlockers.sameFullExactLocal

theorem concreteFourTargetOppositeFullExactLocal_blocked :
    Not
      (RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
        RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.concreteShortcutBlockers.oppositeFullExactLocal

theorem concreteFourTargetCoordinateRemainingRows_blocked :
    Not FlexibleBranchSearchSummaryW10.W10CoordinateRemainingRows :=
  matrix.concreteShortcutBlockers.coordinateRemainingRows

theorem concreteFourTargetTransitionRemainingRows_blocked :
    Not FlexibleTransitionSearchW10.ConcreteFourTargetRemainingExactLocalEquations :=
  matrix.concreteShortcutBlockers.transitionRemainingRows

theorem concreteFourTargetFilteredCompletion_blocked :
    Not FlexibleBranchSearchSummaryW10.W10ConcreteFilteredCompletion :=
  matrix.concreteShortcutBlockers.transitionFilteredCompletion

theorem concreteFourTargetSameBranchCandidate_blocked :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.samePlaceNext) :=
  matrix.concreteShortcutBlockers.sameBranchCandidate

theorem concreteFourTargetOppositeBranchCandidate_blocked :
    Not
      (exists T : BranchCandidate,
        T.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.concreteShortcutBlockers.oppositeBranchCandidate

theorem concreteFourTargetSameW10BranchCandidateFields_blocked :
    Not
      (exists B : FlexibleBranchSearchSummaryW10.W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.samePlaceNext) :=
  matrix.concreteShortcutBlockers.sameW10BranchCandidateFields

theorem concreteFourTargetOppositeW10BranchCandidateFields_blocked :
    Not
      (exists B : FlexibleBranchSearchSummaryW10.W10BranchCandidateFields,
        B.parameters.placeNext = RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.concreteShortcutBlockers.oppositeW10BranchCandidateFields

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.concreteShortcutBlockers.sameOppositeCandidateFields

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.concreteShortcutBlockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.concreteShortcutBlockers.completedFilteredRoute

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.concreteShortcutBlockers.fullSameRestShortcut

theorem concreteFourTargetT11RRow_obstruction :
    PachTothRemainingObligationsW9.ConcreteFourTargetT11RRowObstruction :=
  matrix.concreteShortcutBlockers.t11rRow

end FlexibleTransitionClosureW11
end PachToth
end ErdosProblems1066

end
