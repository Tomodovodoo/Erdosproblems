import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.PeriodClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.FlexibleAssemblyTargetW11
import ErdosProblems1066.PachToth.PachTothW11ClosureMatrix

set_option autoImplicit false

/-!
# W11 integrated transition matrix

This module only routes explicit W11 data packages to the conditional
Pach--Toth target facades already available in the transition, role-hinge,
period, cross-block inequality, and target-assembly layers.

Every target statement below still consumes a visible package argument.
The concrete shortcut blockers are carried forward as named ledger fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionIntegratedW11

noncomputable section

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
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger F

abbrev CrossBlockClosureLedger
    (F : InequalityPeriodFamily) :=
  CrossBlockInequalityClosureW11.CrossBlockClosureLedger F

abbrev ExactLocalSameOppositeEquationPackage :=
  ExactLocalClosureW11.SameOppositeExactLocalEquationPackage

abbrev ExactLocalTransitionRemainingFields
    (S : ExactLocalSameOppositeEquationPackage) :=
  ExactLocalClosureW11.TransitionRemainingFields S.toSameOppositeCandidate

/-- A Type-level wrapper around the role-hinge lower-bound closure, whose
underlying proof object is Prop-shaped. -/
structure RoleCrossBlockLowerBoundPackage
    (F : RoleHingePeriodFamily) where
  tag : Unit := ()
  closure : RoleHingeClosureW11.CrossBlockLowerBoundClosure F

/-- Exact-local same/opposite equations together with the remaining W11
transition fields needed by the non-rigid route. -/
structure ExactLocalRouteFields where
  equations : ExactLocalSameOppositeEquationPackage
  remaining : ExactLocalTransitionRemainingFields equations

namespace ExactLocalRouteFields

def toTransitionRouteFields
    (R : ExactLocalRouteFields) :
    ExactLocalClosureW11.TransitionRouteFields :=
  ExactLocalClosureW11.sameOppositeEquationPackage_toRouteFields
    R.equations R.remaining

theorem exactTarget
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.toTransitionRouteFields.targetUpperConstructionFiveSixteen

theorem arbitraryTarget
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  R.toTransitionRouteFields.targetUpperConstructionFiveSixteenArbitrary

end ExactLocalRouteFields

/-! ## Shared target rows -/

/-- Exact, eventual, and arbitrary target projections from one explicit
package shape. -/
structure ConditionalTargetRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- Eventual target obtained from a conditional arbitrary target. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

def rowOfExactArbitrary
    {alpha : Type}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    ConditionalTargetRow alpha where
  exactTarget := exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget

def rowOfStrongTargetRow
    {alpha : Type}
    (R : FlexibleTransitionClosureW11.StrongTargetRow alpha) :
    ConditionalTargetRow alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfPeriodTargetRow
    {alpha : Type}
    (R : PeriodClosureW11.TargetProjectionRow alpha) :
    ConditionalTargetRow alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfThresholdSmallCaseRoute
    {alpha : Type}
    (R : FlexibleAssemblyTargetW11.ThresholdSmallCaseRoute alpha) :
    ConditionalTargetRow alpha where
  exactTarget := R.exactTarget
  eventualTarget := fun a => R.eventualTarget a
  arbitraryTarget := fun a => R.arbitraryTarget a

def rowOfCheckedRemainderRoute
    {alpha : Type}
    (R : ArbitraryNBridgeW10.CheckedRemainderRouteRow alpha) :
    ConditionalTargetRow alpha where
  exactTarget := R.exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (R.arbitraryTarget a)
  arbitraryTarget := R.arbitraryTarget

/-! ## Package and blocker ledgers -/

/-- The explicit package shapes routed by the integrated W11 matrix. -/
structure PackageLedger where
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
  roleCrossBlockLowerBoundClosure : RoleHingePeriodFamily -> Type
  separatedFamilyFields : PeriodCandidate -> Type
  periodCrossBlockLedgerFields : PeriodCandidate -> Type
  explicitLowerBoundFields : PeriodCandidate -> Type
  exactCandidatePeriodFields : PeriodCandidate -> Type
  periodNonRigidRouteFields : Type
  rawCrossBlockInequalityLedger : InequalityPeriodFamily -> Type
  crossBlockClosureLedger : InequalityPeriodFamily -> Type

def packageLedger : PackageLedger where
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
  roleCrossBlockLowerBoundClosure := RoleCrossBlockLowerBoundPackage
  separatedFamilyFields := SeparatedFamilyFields
  periodCrossBlockLedgerFields := PeriodCrossBlockLedgerFields
  explicitLowerBoundFields := ExplicitLowerBoundFields
  exactCandidatePeriodFields := ExactCandidatePeriodFields
  periodNonRigidRouteFields := PeriodNonRigidRouteFields
  rawCrossBlockInequalityLedger := RawCrossBlockInequalityLedger
  crossBlockClosureLedger := CrossBlockClosureLedger

/-- Blocker facts carried forward from the W11 transition and closure ledgers. -/
structure BlockerLedger where
  transitionShortcuts :
    FlexibleTransitionClosureW11.ConcreteFourTargetShortcutBlockers
  exactLocalObstructions :
    ExactLocalClosureW11.ObstructionRowsLedger
  inheritedW11Fields :
    PachTothW11ClosureMatrix.InheritedFieldLedger

def blockerLedger : BlockerLedger where
  transitionShortcuts :=
    FlexibleTransitionClosureW11.concreteFourTargetShortcutBlockers
  exactLocalObstructions := ExactLocalClosureW11.matrix.obstructions
  inheritedW11Fields := PachTothW11ClosureMatrix.inheritedFieldLedger

/-! ## Integrated rows -/

def transitionRemainingFieldsRow
    (T : TransitionCandidate) :
    ConditionalTargetRow (TransitionRemainingFields T) :=
  rowOfStrongTargetRow
    (FlexibleTransitionClosureW11.matrix.transitionRemainingTargets T)

def transitionRouteFieldsRow :
    ConditionalTargetRow TransitionRouteFields :=
  rowOfStrongTargetRow
    FlexibleTransitionClosureW11.matrix.transitionRouteTargets

def completedFilteredRouteFieldsRow
    (F : FilteredSameOpposite) :
    ConditionalTargetRow (CompletedFilteredRouteFields F) :=
  rowOfStrongTargetRow
    (FlexibleTransitionClosureW11.matrix.completedFilteredRouteTargets F)

def candidateAssemblyFieldsRow :
    ConditionalTargetRow CandidateAssemblyFields :=
  rowOfStrongTargetRow
    FlexibleTransitionClosureW11.matrix.candidateAssemblyTargets

def flexibleCandidateFieldsRow :
    ConditionalTargetRow FlexibleCandidateFields :=
  rowOfThresholdSmallCaseRoute
    FlexibleAssemblyTargetW11.matrix.candidateFields

def candidateValueMatrixFamilyRow :
    ConditionalTargetRow CandidateValueMatrixFamily :=
  rowOfCheckedRemainderRoute
    FlexibleAssemblyTargetW11.matrix.w10CandidateValueMatrices

def finalConditionalFamilyRow :
    ConditionalTargetRow FinalConditionalFamily :=
  rowOfThresholdSmallCaseRoute
    FlexibleAssemblyTargetW11.matrix.finalConditionalFamily

def exactLocalRouteFieldsRow :
    ConditionalTargetRow ExactLocalRouteFields :=
  rowOfExactArbitrary
    ExactLocalRouteFields.exactTarget
    ExactLocalRouteFields.arbitraryTarget

def roleEquationRouteFieldsRow :
    ConditionalTargetRow RoleEquationRouteFields :=
  rowOfExactArbitrary
    RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_equationRoute
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_equationRoute

def roleLedgerCandidateAssemblyFieldsRow :
    ConditionalTargetRow RoleLedgerCandidateAssemblyFields :=
  rowOfExactArbitrary
    RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_ledgerCandidateAssembly
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_ledgerCandidateAssembly

def roleCrossBlockLowerBoundClosureRow
    (F : RoleHingePeriodFamily) :
    ConditionalTargetRow (RoleCrossBlockLowerBoundPackage F) :=
  rowOfExactArbitrary
    (fun P =>
      RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_crossBlockLowerBoundClosure
        P.closure)
    (fun P =>
      RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBoundClosure
        P.closure)

def separatedFamilyFieldsRow
    (T : PeriodCandidate) :
    ConditionalTargetRow (SeparatedFamilyFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.separatedFamilies T)

def periodCrossBlockLedgerFieldsRow
    (T : PeriodCandidate) :
    ConditionalTargetRow (PeriodCrossBlockLedgerFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.crossBlockLedgerClosures T)

def explicitLowerBoundFieldsRow
    (T : PeriodCandidate) :
    ConditionalTargetRow (ExplicitLowerBoundFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.explicitLowerBoundClosures T)

def exactCandidatePeriodFieldsRow
    (T : PeriodCandidate) :
    ConditionalTargetRow (ExactCandidatePeriodFields T) :=
  rowOfPeriodTargetRow (PeriodClosureW11.matrix.exactCandidatePeriods T)

def periodNonRigidRouteFieldsRow :
    ConditionalTargetRow PeriodNonRigidRouteFields :=
  rowOfPeriodTargetRow PeriodClosureW11.matrix.nonRigidRoutes

theorem crossBlockClosureLedgerArbitraryTarget
    {F : InequalityPeriodFamily}
    (C : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.targetUpperConstructionFiveSixteenArbitrary_checkedRemainders

def crossBlockClosureLedgerRow
    (F : InequalityPeriodFamily) :
    ConditionalTargetRow (CrossBlockClosureLedger F) :=
  rowOfExactArbitrary
    (fun C => C.targetUpperConstructionFiveSixteen)
    crossBlockClosureLedgerArbitraryTarget

def toCrossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F where
  inequalityLedger := L

def rawCrossBlockInequalityLedgerRow
    (F : InequalityPeriodFamily) :
    ConditionalTargetRow (RawCrossBlockInequalityLedger F) where
  exactTarget := fun L =>
    (toCrossBlockClosureLedger L).targetUpperConstructionFiveSixteen
  eventualTarget := fun L =>
    eventualTargetOfArbitrary
      (crossBlockClosureLedgerArbitraryTarget (toCrossBlockClosureLedger L))
  arbitraryTarget := fun L =>
    crossBlockClosureLedgerArbitraryTarget (toCrossBlockClosureLedger L)

/-! ## Integrated matrix -/

/-- Integrated W11 transition/candidate/period/inequality routing matrix. -/
structure Matrix where
  packages : PackageLedger
  blockers : BlockerLedger
  flexibleTransitionMatrix : FlexibleTransitionClosureW11.Matrix
  exactLocalMatrix : ExactLocalClosureW11.Matrix
  roleHingeMatrix : RoleHingeClosureW11.ClosureMatrix
  periodMatrix : PeriodClosureW11.Matrix
  crossBlockRoutes :
    forall F : InequalityPeriodFamily,
      CrossBlockInequalityClosureW11.ConditionalTargetRouteLedger F
  assemblyTargetMatrix : FlexibleAssemblyTargetW11.Matrix
  transitionRemainingFields :
    forall T : TransitionCandidate,
      ConditionalTargetRow (TransitionRemainingFields T)
  transitionRouteFields :
    ConditionalTargetRow TransitionRouteFields
  completedFilteredRouteFields :
    forall F : FilteredSameOpposite,
      ConditionalTargetRow (CompletedFilteredRouteFields F)
  candidateAssemblyFields :
    ConditionalTargetRow CandidateAssemblyFields
  flexibleCandidateFields :
    ConditionalTargetRow FlexibleCandidateFields
  candidateValueMatrixFamily :
    ConditionalTargetRow CandidateValueMatrixFamily
  finalConditionalFamily :
    ConditionalTargetRow FinalConditionalFamily
  exactLocalRouteFields :
    ConditionalTargetRow ExactLocalRouteFields
  roleEquationRouteFields :
    ConditionalTargetRow RoleEquationRouteFields
  roleLedgerCandidateAssemblyFields :
    ConditionalTargetRow RoleLedgerCandidateAssemblyFields
  roleCrossBlockLowerBoundClosure :
    forall F : RoleHingePeriodFamily,
      ConditionalTargetRow (RoleCrossBlockLowerBoundPackage F)
  separatedFamilyFields :
    forall T : PeriodCandidate,
      ConditionalTargetRow (SeparatedFamilyFields T)
  periodCrossBlockLedgerFields :
    forall T : PeriodCandidate,
      ConditionalTargetRow (PeriodCrossBlockLedgerFields T)
  explicitLowerBoundFields :
    forall T : PeriodCandidate,
      ConditionalTargetRow (ExplicitLowerBoundFields T)
  exactCandidatePeriodFields :
    forall T : PeriodCandidate,
      ConditionalTargetRow (ExactCandidatePeriodFields T)
  periodNonRigidRouteFields :
    ConditionalTargetRow PeriodNonRigidRouteFields
  rawCrossBlockInequalityLedger :
    forall F : InequalityPeriodFamily,
      ConditionalTargetRow (RawCrossBlockInequalityLedger F)
  crossBlockClosureLedger :
    forall F : InequalityPeriodFamily,
      ConditionalTargetRow (CrossBlockClosureLedger F)

def matrix : Matrix where
  packages := packageLedger
  blockers := blockerLedger
  flexibleTransitionMatrix := FlexibleTransitionClosureW11.matrix
  exactLocalMatrix := ExactLocalClosureW11.matrix
  roleHingeMatrix := RoleHingeClosureW11.closureMatrix
  periodMatrix := PeriodClosureW11.matrix
  crossBlockRoutes :=
    CrossBlockInequalityClosureW11.conditionalTargetRouteLedger
  assemblyTargetMatrix := FlexibleAssemblyTargetW11.matrix
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
  roleCrossBlockLowerBoundClosure := roleCrossBlockLowerBoundClosureRow
  separatedFamilyFields := separatedFamilyFieldsRow
  periodCrossBlockLedgerFields := periodCrossBlockLedgerFieldsRow
  explicitLowerBoundFields := explicitLowerBoundFieldsRow
  exactCandidatePeriodFields := exactCandidatePeriodFieldsRow
  periodNonRigidRouteFields := periodNonRigidRouteFieldsRow
  rawCrossBlockInequalityLedger := rawCrossBlockInequalityLedgerRow
  crossBlockClosureLedger := crossBlockClosureLedgerRow

/-! ## Public routing projections -/

theorem targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transitionRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transitionRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateAssemblyFields.exactTarget F

theorem targetUpperConstructionFiveSixteenEventually_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.candidateAssemblyFields.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidateAssemblyFields
    (F : CandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateAssemblyFields.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.finalConditionalFamily.exactTarget F

theorem targetUpperConstructionFiveSixteenEventually_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.finalConditionalFamily.eventualTarget F

theorem targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily
    (F : FinalConditionalFamily) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.finalConditionalFamily.arbitraryTarget F

theorem targetUpperConstructionFiveSixteen_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleEquationRouteFields.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.roleEquationRouteFields.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleEquationRouteFields.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleLedgerCandidateAssemblyFields.exactTarget L

theorem
    targetUpperConstructionFiveSixteenEventually_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.roleLedgerCandidateAssemblyFields.eventualTarget L

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleLedgerCandidateAssemblyFields.arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_periodCrossBlockLedgerFields
    {T : PeriodCandidate}
    (D : PeriodCrossBlockLedgerFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.periodCrossBlockLedgerFields T).exactTarget D

theorem
    targetUpperConstructionFiveSixteenEventually_of_periodCrossBlockLedgerFields
    {T : PeriodCandidate}
    (D : PeriodCrossBlockLedgerFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.periodCrossBlockLedgerFields T).eventualTarget D

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_periodCrossBlockLedgerFields
    {T : PeriodCandidate}
    (D : PeriodCrossBlockLedgerFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.periodCrossBlockLedgerFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
    {T : PeriodCandidate}
    (D : ExplicitLowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.explicitLowerBoundFields T).exactTarget D

theorem targetUpperConstructionFiveSixteenEventually_of_explicitLowerBoundFields
    {T : PeriodCandidate}
    (D : ExplicitLowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.explicitLowerBoundFields T).eventualTarget D

theorem targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
    {T : PeriodCandidate}
    (D : ExplicitLowerBoundFields T) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.explicitLowerBoundFields T).arbitraryTarget D

theorem targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.rawCrossBlockInequalityLedger F).exactTarget L

theorem
    targetUpperConstructionFiveSixteenEventually_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.rawCrossBlockInequalityLedger F).eventualTarget L

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
    {F : InequalityPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.rawCrossBlockInequalityLedger F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockClosureLedger F).exactTarget L

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockClosureLedger
    {F : InequalityPeriodFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockClosureLedger F).eventualTarget L

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
  matrix.blockers.transitionShortcuts.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.transitionShortcuts.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.transitionShortcuts.sameOppositeCandidateFields

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.transitionShortcuts.fullSameRestShortcut

theorem inheritedConcreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.inheritedW11Fields.w11ConcreteFourTargetRouteBlocker

theorem inheritedConcreteFourTargetCompletedFilteredRoute_blocked :
    PachTothW11ClosureMatrix.W11CompletedFilteredRouteFields
        FlexibleTransitionSearchW11.concreteFourTargetCheckedRows.filtered ->
      False :=
  matrix.blockers.inheritedW11Fields.w11ConcreteFilteredRouteBlocker

theorem inheritedConcreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.inheritedW11Fields.inheritedFullSameRestBlocker

end

end TransitionIntegratedW11
end PachToth
end ErdosProblems1066
