import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.FlexibleAssemblyTargetW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.PeriodClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11

set_option autoImplicit false

/-!
# Checked W11 transition integration

This file is a standalone checked replacement for the W11 transition
integration route.  It imports only checked closure layers, records the field
packages consumed by each route, and keeps concrete blockers as named data.

Every target-producing projection below still takes an explicit package
argument.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionCheckedIntegratedW11

noncomputable section

universe u

abbrev TransitionCandidate :=
  FlexibleTransitionClosureW11.SameOppositeCandidate

abbrev FilteredSameOpposite :=
  FlexibleTransitionClosureW11.FilteredSameOpposite

abbrev TransitionRemainingFields (T : TransitionCandidate) :=
  FlexibleTransitionClosureW11.TransitionRemainingFields T

abbrev TransitionRouteFields :=
  FlexibleTransitionClosureW11.TransitionRouteFields

abbrev CompletedFilteredRouteFields (F : FilteredSameOpposite) :=
  FlexibleTransitionClosureW11.CompletedFilteredRouteFields F

abbrev CandidateAssemblyFields :=
  FlexibleTransitionClosureW11.CandidateAssemblyFields

abbrev FlexibleCandidateFields :=
  FlexibleAssemblyTargetW11.CandidateFields

abbrev CandidateValueMatrixFamily :=
  FlexibleAssemblyTargetW11.CandidateValueMatrixFamily

abbrev FinalConditionalFamily :=
  FlexibleAssemblyTargetW11.FinalConditionalFamily

abbrev ExactLocalSameOppositeEquationPackage :=
  ExactLocalClosureW11.SameOppositeExactLocalEquationPackage

abbrev ExactLocalTransitionRemainingFields
    (S : ExactLocalSameOppositeEquationPackage) :=
  ExactLocalClosureW11.TransitionRemainingFields S.toSameOppositeCandidate

abbrev RoleEquationRouteFields :=
  RoleHingeClosureW11.EquationRouteFields

abbrev RoleLedgerCandidateAssemblyFields :=
  RoleHingeClosureW11.LedgerCandidateAssemblyFields

abbrev RoleHingePeriodFamily :=
  RoleHingeClosureW11.RoleHingedPeriodSearchFamily

abbrev PeriodCandidate :=
  PeriodClosureW11.Candidate

abbrev SeparatedFamilyFields (T : PeriodCandidate) :=
  PeriodClosureW11.GeneratedFamilyRemainingFields T

abbrev PeriodCrossBlockLedgerFields (T : PeriodCandidate) :=
  PeriodClosureW11.CrossBlockLedgerClosureFields T

abbrev ExplicitLowerBoundFields (T : PeriodCandidate) :=
  PeriodClosureW11.ExplicitLowerBoundClosureFields T

abbrev ExactCandidatePeriodFields (T : PeriodCandidate) :=
  PeriodClosureW11.ExactCandidatePeriodFields T

abbrev PeriodNonRigidRouteFields :=
  PeriodClosureW11.W11NonRigidRouteFields

abbrev InequalityPeriodFamily :=
  CrossBlockInequalityClosureW11.RoleHingedPeriodSearchFamily

abbrev RawCrossBlockInequalityLedger
    (F : InequalityPeriodFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : InequalityPeriodFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger F

/-! ## Extra explicit route packages -/

/-- Exact-local equations paired with the remaining period and metric fields
required by the W11 non-rigid transition route. -/
structure ExactLocalRouteFields where
  equations : ExactLocalSameOppositeEquationPackage
  remaining : ExactLocalTransitionRemainingFields equations

/-- Role-hinge cross-block lower-bound data as a Type-shaped field package. -/
structure RoleCrossBlockLowerBoundFields
    (F : RoleHingePeriodFamily) where
  marker : Unit := ()
  closure : RoleHingeClosureW11.CrossBlockLowerBoundClosure F

/-! ## Uniform target rows -/

/-- A target row with exact, fixed-`n`, eventual, and arbitrary projections
from one explicit package shape. -/
structure CheckedTargetRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- Eventual target obtained from an arbitrary-`n` target. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

def rowOfExactArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    CheckedTargetRow alpha where
  exactTarget := exactTarget
  fixedTarget := fun a n => arbitraryTarget a n
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget

def rowOfStrongTargetRow
    {alpha : Sort u}
    (R : FlexibleTransitionClosureW11.StrongTargetRow alpha) :
    CheckedTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfThresholdSmallCaseRoute
    {alpha : Sort u}
    (R : FlexibleAssemblyTargetW11.ThresholdSmallCaseRoute alpha) :
    CheckedTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => R.eventualTarget a
  arbitraryTarget := fun a => R.arbitraryTarget a

def rowOfCheckedRemainderRoute
    {alpha : Sort u}
    (R : ArbitraryNBridgeW10.CheckedRemainderRouteRow alpha) :
    CheckedTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget

def rowOfPeriodTargetRow
    {alpha : Type}
    (R : PeriodClosureW11.TargetProjectionRow alpha) :
    CheckedTargetRow alpha :=
  rowOfExactArbitrary R.exactTarget R.arbitraryTarget

/-! ## Package and blocker ledgers -/

/-- The explicit package shapes routed by this checked transition matrix. -/
structure FieldPackageLedger where
  transitionRemainingFields : TransitionCandidate -> Type
  transitionRouteFields : Type
  completedFilteredRouteFields : FilteredSameOpposite -> Type
  candidateAssemblyFields : Type
  flexibleCandidateFields : Type
  candidateValueMatrixFamily : Type
  finalConditionalFamily : Type
  exactLocalRouteFields : Type
  roleEquationRouteFields : Type
  roleLedgerCandidateAssemblyFields : Type
  roleCrossBlockLowerBoundFields : RoleHingePeriodFamily -> Type
  separatedFamilyFields : PeriodCandidate -> Type
  periodCrossBlockLedgerFields : PeriodCandidate -> Type
  explicitLowerBoundFields : PeriodCandidate -> Type
  exactCandidatePeriodFields : PeriodCandidate -> Type
  periodNonRigidRouteFields : Type
  rawCrossBlockInequalityLedger : InequalityPeriodFamily -> Type
  crossBlockClosureLedger : InequalityPeriodFamily -> Type

def fieldPackageLedger : FieldPackageLedger where
  transitionRemainingFields := TransitionRemainingFields
  transitionRouteFields := TransitionRouteFields
  completedFilteredRouteFields := CompletedFilteredRouteFields
  candidateAssemblyFields := CandidateAssemblyFields
  flexibleCandidateFields := FlexibleCandidateFields
  candidateValueMatrixFamily := CandidateValueMatrixFamily
  finalConditionalFamily := FinalConditionalFamily
  exactLocalRouteFields := ExactLocalRouteFields
  roleEquationRouteFields := RoleEquationRouteFields
  roleLedgerCandidateAssemblyFields := RoleLedgerCandidateAssemblyFields
  roleCrossBlockLowerBoundFields := RoleCrossBlockLowerBoundFields
  separatedFamilyFields := SeparatedFamilyFields
  periodCrossBlockLedgerFields := PeriodCrossBlockLedgerFields
  explicitLowerBoundFields := ExplicitLowerBoundFields
  exactCandidatePeriodFields := ExactCandidatePeriodFields
  periodNonRigidRouteFields := PeriodNonRigidRouteFields
  rawCrossBlockInequalityLedger := RawCrossBlockInequalityLedger
  crossBlockClosureLedger := CrossBlockClosureLedger

/-- Concrete blockers carried by the checked W11 transition layers. -/
structure BlockerLedger where
  transitionShortcuts :
    FlexibleTransitionClosureW11.ConcreteFourTargetShortcutBlockers
  exactLocalObstructions :
    ExactLocalClosureW11.ObstructionRowsLedger
  routeClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  completedFilteredRoute :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  sameOppositeCandidateFields :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  exactLocalMissingRows :
    forall C : ExactLocalClosureW11.CandidateRows,
      Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C)

def blockerLedger : BlockerLedger where
  transitionShortcuts :=
    FlexibleTransitionClosureW11.concreteFourTargetShortcutBlockers
  exactLocalObstructions := ExactLocalClosureW11.matrix.obstructions
  routeClaim := PachTothW11IntegratedMatrix.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    PachTothW11IntegratedMatrix.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    PachTothW11IntegratedMatrix.concreteFourTargetSameOppositeCandidateFields_blocked
  exactLocalMissingRows := ExactLocalClosureW11.concreteMissingCandidateRows_blocked

/-! ## Integrated rows -/

def transitionRemainingFieldsRow
    (T : TransitionCandidate) :
    CheckedTargetRow (TransitionRemainingFields T) :=
  rowOfStrongTargetRow
    (FlexibleTransitionClosureW11.matrix.transitionRemainingTargets T)

def transitionRouteFieldsRow :
    CheckedTargetRow TransitionRouteFields :=
  rowOfStrongTargetRow
    FlexibleTransitionClosureW11.matrix.transitionRouteTargets

def completedFilteredRouteFieldsRow
    (F : FilteredSameOpposite) :
    CheckedTargetRow (CompletedFilteredRouteFields F) :=
  rowOfStrongTargetRow
    (FlexibleTransitionClosureW11.matrix.completedFilteredRouteTargets F)

def candidateAssemblyFieldsRow :
    CheckedTargetRow CandidateAssemblyFields :=
  rowOfStrongTargetRow
    FlexibleTransitionClosureW11.matrix.candidateAssemblyTargets

def flexibleCandidateFieldsRow :
    CheckedTargetRow FlexibleCandidateFields :=
  rowOfThresholdSmallCaseRoute
    FlexibleAssemblyTargetW11.matrix.candidateFields

def candidateValueMatrixFamilyRow :
    CheckedTargetRow CandidateValueMatrixFamily :=
  rowOfCheckedRemainderRoute
    FlexibleAssemblyTargetW11.matrix.w10CandidateValueMatrices

def finalConditionalFamilyRow :
    CheckedTargetRow FinalConditionalFamily :=
  rowOfThresholdSmallCaseRoute
    FlexibleAssemblyTargetW11.matrix.finalConditionalFamily

def exactLocalRouteFieldsRow :
    CheckedTargetRow ExactLocalRouteFields :=
  rowOfExactArbitrary
    (fun R =>
      ExactLocalClosureW11.targetUpperConstructionFiveSixteen_of_sameOppositeEquationPackage
        R.equations
        R.remaining)
    (fun R =>
      ExactLocalClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_sameOppositeEquationPackage
        R.equations
        R.remaining)

def roleEquationRouteFieldsRow :
    CheckedTargetRow RoleEquationRouteFields :=
  rowOfExactArbitrary
    RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_equationRoute
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_equationRoute

def roleLedgerCandidateAssemblyFieldsRow :
    CheckedTargetRow RoleLedgerCandidateAssemblyFields :=
  rowOfExactArbitrary
    RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_ledgerCandidateAssembly
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_ledgerCandidateAssembly

def roleCrossBlockLowerBoundFieldsRow
    (F : RoleHingePeriodFamily) :
    CheckedTargetRow (RoleCrossBlockLowerBoundFields F) :=
  rowOfExactArbitrary
    (fun P =>
      RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_crossBlockLowerBoundClosure
        P.closure)
    (fun P =>
      RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBoundClosure
        P.closure)

def separatedFamilyFieldsRow
    (T : PeriodCandidate) :
    CheckedTargetRow (SeparatedFamilyFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.separatedFamilies T)

def periodCrossBlockLedgerFieldsRow
    (T : PeriodCandidate) :
    CheckedTargetRow (PeriodCrossBlockLedgerFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.crossBlockLedgerClosures T)

def explicitLowerBoundFieldsRow
    (T : PeriodCandidate) :
    CheckedTargetRow (ExplicitLowerBoundFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.explicitLowerBoundClosures T)

def exactCandidatePeriodFieldsRow
    (T : PeriodCandidate) :
    CheckedTargetRow (ExactCandidatePeriodFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.exactCandidatePeriods T)

def periodNonRigidRouteFieldsRow :
    CheckedTargetRow PeriodNonRigidRouteFields :=
  rowOfPeriodTargetRow PeriodClosureW11.matrix.nonRigidRoutes

def toCrossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F where
  inequalityLedger := L

def rawCrossBlockInequalityLedgerRow
    (F : InequalityPeriodFamily) :
    CheckedTargetRow (RawCrossBlockInequalityLedger F) :=
  rowOfExactArbitrary
    (fun L =>
      CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteen
        (toCrossBlockClosureLedger L))
    (fun L =>
      CrossBlockInequalityClosureW11.CrossBlockClosureLedger.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders
        (toCrossBlockClosureLedger L))

def crossBlockClosureLedgerRow
    (F : InequalityPeriodFamily) :
    CheckedTargetRow (CrossBlockClosureLedger F) :=
  rowOfCheckedRemainderRoute
    (CrossBlockInequalityClosureW11.conditionalTargetRouteLedger F).crossBlockClosure

/-! ## Integrated matrix -/

/-- Checked W11 transition integration matrix. -/
structure Matrix where
  packages : FieldPackageLedger
  blockers : BlockerLedger
  integratedW11 : PachTothW11IntegratedMatrix.Matrix
  flexibleTransition : FlexibleTransitionClosureW11.Matrix
  flexibleAssemblyTarget : FlexibleAssemblyTargetW11.Matrix
  exactLocalClosure : ExactLocalClosureW11.Matrix
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  periodClosure : PeriodClosureW11.Matrix
  crossBlockRoutes :
    forall F : InequalityPeriodFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  transitionRemainingFields :
    forall T : TransitionCandidate,
      CheckedTargetRow (TransitionRemainingFields T)
  transitionRouteFields :
    CheckedTargetRow TransitionRouteFields
  completedFilteredRouteFields :
    forall F : FilteredSameOpposite,
      CheckedTargetRow (CompletedFilteredRouteFields F)
  candidateAssemblyFields :
    CheckedTargetRow CandidateAssemblyFields
  flexibleCandidateFields :
    CheckedTargetRow FlexibleCandidateFields
  candidateValueMatrixFamily :
    CheckedTargetRow CandidateValueMatrixFamily
  finalConditionalFamily :
    CheckedTargetRow FinalConditionalFamily
  exactLocalRouteFields :
    CheckedTargetRow ExactLocalRouteFields
  roleEquationRouteFields :
    CheckedTargetRow RoleEquationRouteFields
  roleLedgerCandidateAssemblyFields :
    CheckedTargetRow RoleLedgerCandidateAssemblyFields
  roleCrossBlockLowerBoundFields :
    forall F : RoleHingePeriodFamily,
      CheckedTargetRow (RoleCrossBlockLowerBoundFields F)
  separatedFamilyFields :
    forall T : PeriodCandidate,
      CheckedTargetRow (SeparatedFamilyFields T)
  periodCrossBlockLedgerFields :
    forall T : PeriodCandidate,
      CheckedTargetRow (PeriodCrossBlockLedgerFields T)
  explicitLowerBoundFields :
    forall T : PeriodCandidate,
      CheckedTargetRow (ExplicitLowerBoundFields T)
  exactCandidatePeriodFields :
    forall T : PeriodCandidate,
      CheckedTargetRow (ExactCandidatePeriodFields T)
  periodNonRigidRouteFields :
    CheckedTargetRow PeriodNonRigidRouteFields
  rawCrossBlockInequalityLedger :
    forall F : InequalityPeriodFamily,
      CheckedTargetRow (RawCrossBlockInequalityLedger F)
  crossBlockClosureLedger :
    forall F : InequalityPeriodFamily,
      CheckedTargetRow (CrossBlockClosureLedger F)

def matrix : Matrix where
  packages := fieldPackageLedger
  blockers := blockerLedger
  integratedW11 := PachTothW11IntegratedMatrix.matrix
  flexibleTransition := FlexibleTransitionClosureW11.matrix
  flexibleAssemblyTarget := FlexibleAssemblyTargetW11.matrix
  exactLocalClosure := ExactLocalClosureW11.matrix
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  periodClosure := PeriodClosureW11.matrix
  crossBlockRoutes := CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  transitionRemainingFields := transitionRemainingFieldsRow
  transitionRouteFields := transitionRouteFieldsRow
  completedFilteredRouteFields := completedFilteredRouteFieldsRow
  candidateAssemblyFields := candidateAssemblyFieldsRow
  flexibleCandidateFields := flexibleCandidateFieldsRow
  candidateValueMatrixFamily := candidateValueMatrixFamilyRow
  finalConditionalFamily := finalConditionalFamilyRow
  exactLocalRouteFields := exactLocalRouteFieldsRow
  roleEquationRouteFields := roleEquationRouteFieldsRow
  roleLedgerCandidateAssemblyFields := roleLedgerCandidateAssemblyFieldsRow
  roleCrossBlockLowerBoundFields := roleCrossBlockLowerBoundFieldsRow
  separatedFamilyFields := separatedFamilyFieldsRow
  periodCrossBlockLedgerFields := periodCrossBlockLedgerFieldsRow
  explicitLowerBoundFields := explicitLowerBoundFieldsRow
  exactCandidatePeriodFields := exactCandidatePeriodFieldsRow
  periodNonRigidRouteFields := periodNonRigidRouteFieldsRow
  rawCrossBlockInequalityLedger := rawCrossBlockInequalityLedgerRow
  crossBlockClosureLedger := crossBlockClosureLedgerRow

/-! ## Public transition and candidate projections -/

theorem targetUpperConstructionFiveSixteen_of_transitionRemainingFields
    {T : TransitionCandidate}
    (R : TransitionRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.transitionRemainingFields T).exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_transitionRemainingFields
    {T : TransitionCandidate}
    (R : TransitionRemainingFields T) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.transitionRemainingFields T).fixedTarget R n

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRemainingFields
    {T : TransitionCandidate}
    (R : TransitionRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.transitionRemainingFields T).eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRemainingFields
    {T : TransitionCandidate}
    (R : TransitionRemainingFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.transitionRemainingFields T).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transitionRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    (R : TransitionRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.transitionRouteFields.fixedTarget R n

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transitionRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_completedFilteredRouteFields
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.completedFilteredRouteFields F).exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
    {F : FilteredSameOpposite}
    (R : CompletedFilteredRouteFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.completedFilteredRouteFields F).arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateAssemblyFields.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.candidateAssemblyFields.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.candidateAssemblyFields.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateAssemblyFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenAt_of_flexibleCandidateFields
    (F : FlexibleCandidateFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.flexibleCandidateFields.fixedTarget F n

theorem targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateFields
    (F : FlexibleCandidateFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.flexibleCandidateFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixFamily
    (F : CandidateValueMatrixFamily) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.candidateValueMatrixFamily.fixedTarget F n

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
    (F : CandidateValueMatrixFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateValueMatrixFamily.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.finalConditionalFamily.exactTarget F

theorem targetUpperConstructionFiveSixteenAt_of_finalConditionalFamily
    (F : FinalConditionalFamily) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.finalConditionalFamily.fixedTarget F n

theorem targetUpperConstructionFiveSixteenEventually_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.finalConditionalFamily.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finalConditionalFamily.arbitraryTarget F

/-! ## Public exact-local, role-hinge, period, and cross-block projections -/

theorem targetUpperConstructionFiveSixteen_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.exactLocalRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactLocalRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleEquationRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.roleEquationRouteFields.fixedTarget R n

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleEquationRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleLedgerCandidateAssemblyFields.exactTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleLedgerCandidateAssemblyFields.arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_roleCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (P : RoleCrossBlockLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.roleCrossBlockLowerBoundFields F).exactTarget P

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (P : RoleCrossBlockLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.roleCrossBlockLowerBoundFields F).arbitraryTarget P

theorem targetUpperConstructionFiveSixteen_of_periodCrossBlockLedgerFields
    {T : PeriodCandidate}
    (D : PeriodCrossBlockLedgerFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodCrossBlockLedgerFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodCrossBlockLedgerFields
    {T : PeriodCandidate}
    (D : PeriodCrossBlockLedgerFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodCrossBlockLedgerFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
    {T : PeriodCandidate}
    (D : ExplicitLowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.explicitLowerBoundFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
    {T : PeriodCandidate}
    (D : ExplicitLowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.explicitLowerBoundFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
    {T : PeriodCandidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.exactCandidatePeriodFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
    {T : PeriodCandidate}
    (D : ExactCandidatePeriodFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.exactCandidatePeriodFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_periodNonRigidRouteFields
    (D : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.periodNonRigidRouteFields.exactTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
    (D : PeriodNonRigidRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.periodNonRigidRouteFields.arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.rawCrossBlockInequalityLedger F).exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.rawCrossBlockInequalityLedger F).fixedTarget L n

theorem targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.rawCrossBlockInequalityLedger F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockClosureLedger F).exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  (matrix.crossBlockClosureLedger F).fixedTarget L n

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockClosureLedger F).arbitraryTarget L

/-! ## Public blocker projections -/

theorem concreteFourTargetT11R_not_possible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r) :=
  matrix.blockers.transitionShortcuts.t11rNotPossible

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.sameOppositeCandidateFields

theorem concreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.blockers.exactLocalMissingRows C

end

end TransitionCheckedIntegratedW11
end PachToth
end ErdosProblems1066
