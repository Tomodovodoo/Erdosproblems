import ErdosProblems1066.PachToth.TransitionTargetIntegratedW11
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.TransitionCheckedIntegratedW11
import ErdosProblems1066.PachToth.ExactLocalTargetIntegratedW11

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Final W11 transition aggregate

This module is a terminal transition ledger over the W11 target, integrated,
checked, and exact-local target adapters.  It records route, candidate,
role-hinge, period, and cross-block package shapes explicitly, and exposes
target conclusions only as projections from one of those package values.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionFinalIntegratedW11

noncomputable section

abbrev TargetMatrix := TransitionTargetIntegratedW11.Matrix
abbrev IntegratedMatrix := TransitionIntegratedW11.Matrix
abbrev CheckedMatrix := TransitionCheckedIntegratedW11.Matrix
abbrev ExactLocalTargetMatrix := ExactLocalTargetIntegratedW11.Matrix

abbrev TargetRoutePackage := TransitionTargetIntegratedW11.RoutePackage
abbrev TargetCandidatePackage :=
  TransitionTargetIntegratedW11.CandidatePackage
abbrev TargetRoleHingePackage :=
  TransitionTargetIntegratedW11.RoleHingePackage
abbrev TargetPeriodPackage := TransitionTargetIntegratedW11.PeriodPackage
abbrev TargetCrossBlockPackage :=
  TransitionTargetIntegratedW11.CrossBlockPackage
abbrev TargetCheckedWordSeparationPackage :=
  TransitionTargetIntegratedW11.CheckedWordSeparationPackage
abbrev TargetPeriodExplicitLowerBoundPackage :=
  TransitionTargetIntegratedW11.PeriodExplicitLowerBoundPackage

abbrev CheckedTransitionCandidate :=
  TransitionCheckedIntegratedW11.TransitionCandidate
abbrev CheckedFilteredSameOpposite :=
  TransitionCheckedIntegratedW11.FilteredSameOpposite
abbrev CheckedTransitionRemainingFields
    (T : CheckedTransitionCandidate) :=
  TransitionCheckedIntegratedW11.TransitionRemainingFields T
abbrev CheckedTransitionRouteFields :=
  TransitionCheckedIntegratedW11.TransitionRouteFields
abbrev CheckedCompletedFilteredRouteFields
    (F : CheckedFilteredSameOpposite) :=
  TransitionCheckedIntegratedW11.CompletedFilteredRouteFields F
abbrev CheckedCandidateAssemblyFields :=
  TransitionCheckedIntegratedW11.CandidateAssemblyFields
abbrev CheckedFlexibleCandidateFields :=
  TransitionCheckedIntegratedW11.FlexibleCandidateFields
abbrev CheckedCandidateValueMatrixFamily :=
  TransitionCheckedIntegratedW11.CandidateValueMatrixFamily
abbrev CheckedFinalConditionalFamily :=
  TransitionCheckedIntegratedW11.FinalConditionalFamily
abbrev CheckedExactLocalRouteFields :=
  TransitionCheckedIntegratedW11.ExactLocalRouteFields
abbrev CheckedRoleEquationRouteFields :=
  TransitionCheckedIntegratedW11.RoleEquationRouteFields
abbrev CheckedRoleLedgerCandidateAssemblyFields :=
  TransitionCheckedIntegratedW11.RoleLedgerCandidateAssemblyFields
abbrev CheckedRoleHingePeriodFamily :=
  TransitionCheckedIntegratedW11.RoleHingePeriodFamily
abbrev CheckedRoleCrossBlockLowerBoundFields
    (F : CheckedRoleHingePeriodFamily) :=
  TransitionCheckedIntegratedW11.RoleCrossBlockLowerBoundFields F
abbrev CheckedPeriodCandidate :=
  TransitionCheckedIntegratedW11.PeriodCandidate
abbrev CheckedSeparatedFamilyFields (T : CheckedPeriodCandidate) :=
  TransitionCheckedIntegratedW11.SeparatedFamilyFields T
abbrev CheckedPeriodCrossBlockLedgerFields
    (T : CheckedPeriodCandidate) :=
  TransitionCheckedIntegratedW11.PeriodCrossBlockLedgerFields T
abbrev CheckedExplicitLowerBoundFields (T : CheckedPeriodCandidate) :=
  TransitionCheckedIntegratedW11.ExplicitLowerBoundFields T
abbrev CheckedExactCandidatePeriodFields
    (T : CheckedPeriodCandidate) :=
  TransitionCheckedIntegratedW11.ExactCandidatePeriodFields T
abbrev CheckedPeriodNonRigidRouteFields :=
  TransitionCheckedIntegratedW11.PeriodNonRigidRouteFields
abbrev CheckedInequalityPeriodFamily :=
  TransitionCheckedIntegratedW11.InequalityPeriodFamily
abbrev CheckedRawCrossBlockInequalityLedger
    (F : CheckedInequalityPeriodFamily) :=
  TransitionCheckedIntegratedW11.RawCrossBlockInequalityLedger F
abbrev CheckedCrossBlockClosureLedger
    (F : CheckedInequalityPeriodFamily) :=
  TransitionCheckedIntegratedW11.CrossBlockClosureLedger F

abbrev ExactLocalTargetFields :=
  ExactLocalTargetIntegratedW11.ExactLocalTargetFields
abbrev ExactLocalEndpointShortcutRow :=
  ExactLocalTargetIntegratedW11.EndpointShortcutRow
abbrev ExactLocalPossibleRow :=
  ExactLocalTargetIntegratedW11.PossibleRow

/-! ## Shared target rows -/

/-- Exact, fixed-`n`, eventual, and arbitrary target projections from one
explicit package shape. -/
structure FinalTargetRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  fixedTarget :
    alpha -> forall n : Nat, PachToth.targetUpperConstructionFiveSixteenAt n
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- An arbitrary target gives an eventual route with threshold zero. -/
theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

def rowOfTargetProjectionRow
    {alpha : Type}
    (R : TransitionTargetIntegratedW11.TargetProjectionRow alpha) :
    FinalTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := fun a n => R.arbitraryTarget a n
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfCheckedTargetRow
    {alpha : Type}
    (R : TransitionCheckedIntegratedW11.CheckedTargetRow alpha) :
    FinalTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def rowOfExactLocalTargetRoute
    {alpha : Type}
    (R : ExactLocalTargetIntegratedW11.TargetRoute alpha) :
    FinalTargetRow alpha where
  exactTarget := R.exactTarget
  fixedTarget := fun a n => R.arbitraryTarget a n
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-! ## Explicit route packages -/

structure CheckedTransitionRemainingPackage where
  candidate : CheckedTransitionCandidate
  fields : CheckedTransitionRemainingFields candidate

structure CheckedCompletedFilteredRoutePackage where
  filtered : CheckedFilteredSameOpposite
  fields : CheckedCompletedFilteredRouteFields filtered

/-- Final transition-route package variants. -/
inductive RoutePackage where
  | target (package : TargetRoutePackage)
  | checkedTransitionRemaining
      (package : CheckedTransitionRemainingPackage)
  | checkedTransitionRoute (fields : CheckedTransitionRouteFields)
  | checkedCompletedFiltered
      (package : CheckedCompletedFilteredRoutePackage)
  | checkedExactLocal (fields : CheckedExactLocalRouteFields)
  | exactLocalIntegratedTransition (fields : ExactLocalTargetFields)
  | exactLocalTransitionFacade (fields : ExactLocalTargetFields)
  | exactLocalPachTothTransitionFacade (fields : ExactLocalTargetFields)

namespace RoutePackage

def exactTarget
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
        package
  | checkedTransitionRemaining package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionRemainingFields
        package.fields
  | checkedTransitionRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionRouteFields
        fields
  | checkedCompletedFiltered package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_completedFilteredRouteFields
        package.fields
  | checkedExactLocal fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_exactLocalRouteFields
        fields
  | exactLocalIntegratedTransition fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_exactLocalTransition
        fields
  | exactLocalTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionFacade
        fields
  | exactLocalPachTothTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_pachTothTransitionFacade
        fields

def fixedTarget
    (package : RoutePackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
        package n
  | checkedTransitionRemaining package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_transitionRemainingFields
        package.fields n
  | checkedTransitionRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
        fields n
  | checkedCompletedFiltered package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
        package.fields n
  | checkedExactLocal fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRouteFields
        fields n
  | exactLocalIntegratedTransition fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalTransition
        fields n
  | exactLocalTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionFacade
        fields n
  | exactLocalPachTothTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_pachTothTransitionFacade
        fields n

def eventualTarget
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
        package
  | checkedTransitionRemaining package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_transitionRemainingFields
        package.fields
  | checkedTransitionRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
        fields
  | checkedCompletedFiltered package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
          package.fields)
  | checkedExactLocal fields =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRouteFields
          fields)
  | exactLocalIntegratedTransition fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactLocalTransition
        fields
  | exactLocalTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_transitionFacade
        fields
  | exactLocalPachTothTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_pachTothTransitionFacade
        fields

def arbitraryTarget
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
        package
  | checkedTransitionRemaining package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionRemainingFields
        package.fields
  | checkedTransitionRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
        fields
  | checkedCompletedFiltered package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_completedFilteredRouteFields
        package.fields
  | checkedExactLocal fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRouteFields
        fields
  | exactLocalIntegratedTransition fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalTransition
        fields
  | exactLocalTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionFacade
        fields
  | exactLocalPachTothTransitionFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_pachTothTransitionFacade
        fields

end RoutePackage

def routeTargetRow : FinalTargetRow RoutePackage where
  exactTarget := RoutePackage.exactTarget
  fixedTarget := RoutePackage.fixedTarget
  eventualTarget := RoutePackage.eventualTarget
  arbitraryTarget := RoutePackage.arbitraryTarget

/-! ## Explicit candidate packages -/

/-- Final candidate package variants. -/
inductive CandidatePackage where
  | target (package : TargetCandidatePackage)
  | checkedCandidateAssembly (fields : CheckedCandidateAssemblyFields)
  | checkedFlexibleCandidate (fields : CheckedFlexibleCandidateFields)
  | checkedCandidateValueMatrix
      (fields : CheckedCandidateValueMatrixFamily)
  | checkedFinalConditional (fields : CheckedFinalConditionalFamily)

namespace CandidatePackage

def exactTarget
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_candidatePackage
        package
  | checkedCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_candidateAssemblyFields
        fields
  | checkedFlexibleCandidate fields =>
      TransitionCheckedIntegratedW11.matrix.flexibleCandidateFields.exactTarget
        fields
  | checkedCandidateValueMatrix fields =>
      TransitionCheckedIntegratedW11.matrix.candidateValueMatrixFamily.exactTarget
        fields
  | checkedFinalConditional fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_finalConditionalFamily
        fields

def fixedTarget
    (package : CandidatePackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_candidatePackage
        package n
  | checkedCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_candidateAssemblyFields
        fields n
  | checkedFlexibleCandidate fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_flexibleCandidateFields
        fields n
  | checkedCandidateValueMatrix fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_candidateValueMatrixFamily
        fields n
  | checkedFinalConditional fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_finalConditionalFamily
        fields n

def eventualTarget
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_candidatePackage
        package
  | checkedCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_candidateAssemblyFields
        fields
  | checkedFlexibleCandidate fields =>
      TransitionCheckedIntegratedW11.matrix.flexibleCandidateFields.eventualTarget
        fields
  | checkedCandidateValueMatrix fields =>
      TransitionCheckedIntegratedW11.matrix.candidateValueMatrixFamily.eventualTarget
        fields
  | checkedFinalConditional fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_finalConditionalFamily
        fields

def arbitraryTarget
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_candidatePackage
        package
  | checkedCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_candidateAssemblyFields
        fields
  | checkedFlexibleCandidate fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateFields
        fields
  | checkedCandidateValueMatrix fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_candidateValueMatrixFamily
        fields
  | checkedFinalConditional fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_finalConditionalFamily
        fields

end CandidatePackage

def candidateTargetRow : FinalTargetRow CandidatePackage where
  exactTarget := CandidatePackage.exactTarget
  fixedTarget := CandidatePackage.fixedTarget
  eventualTarget := CandidatePackage.eventualTarget
  arbitraryTarget := CandidatePackage.arbitraryTarget

/-! ## Explicit role-hinge packages -/

structure CheckedRoleCrossBlockLowerBoundPackage where
  family : CheckedRoleHingePeriodFamily
  fields : CheckedRoleCrossBlockLowerBoundFields family

/-- Final role-hinge package variants. -/
inductive RoleHingePackage where
  | target (package : TargetRoleHingePackage)
  | checkedEquationRoute (fields : CheckedRoleEquationRouteFields)
  | checkedLedgerCandidateAssembly
      (fields : CheckedRoleLedgerCandidateAssemblyFields)
  | checkedCrossBlockLowerBound
      (package : CheckedRoleCrossBlockLowerBoundPackage)
  | exactLocalIntegratedRoleHinge (fields : ExactLocalTargetFields)
  | exactLocalRoleHingeFacade (fields : ExactLocalTargetFields)

namespace RoleHingePackage

def exactTarget
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_roleHingePackage
        package
  | checkedEquationRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_roleEquationRouteFields
        fields
  | checkedLedgerCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_roleLedgerCandidateAssemblyFields
        fields
  | checkedCrossBlockLowerBound package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_roleCrossBlockLowerBoundFields
        package.fields
  | exactLocalIntegratedRoleHinge fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_exactLocalRoleHinge
        fields
  | exactLocalRoleHingeFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_roleHingeFacade
        fields

def fixedTarget
    (package : RoleHingePackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleHingePackage
        package n
  | checkedEquationRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_roleEquationRouteFields
        fields n
  | checkedLedgerCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleLedgerCandidateAssemblyFields
        fields n
  | checkedCrossBlockLowerBound package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleCrossBlockLowerBoundFields
        package.fields n
  | exactLocalIntegratedRoleHinge fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRoleHinge
        fields n
  | exactLocalRoleHingeFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleHingeFacade
        fields n

def eventualTarget
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_roleHingePackage
        package
  | checkedEquationRoute fields =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleEquationRouteFields
          fields)
  | checkedLedgerCandidateAssembly fields =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleLedgerCandidateAssemblyFields
          fields)
  | checkedCrossBlockLowerBound package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleCrossBlockLowerBoundFields
          package.fields)
  | exactLocalIntegratedRoleHinge fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactLocalRoleHinge
        fields
  | exactLocalRoleHingeFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_roleHingeFacade
        fields

def arbitraryTarget
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleHingePackage
        package
  | checkedEquationRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleEquationRouteFields
        fields
  | checkedLedgerCandidateAssembly fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleLedgerCandidateAssemblyFields
        fields
  | checkedCrossBlockLowerBound package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleCrossBlockLowerBoundFields
        package.fields
  | exactLocalIntegratedRoleHinge fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRoleHinge
        fields
  | exactLocalRoleHingeFacade fields =>
      ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_roleHingeFacade
        fields

end RoleHingePackage

def roleHingeTargetRow : FinalTargetRow RoleHingePackage where
  exactTarget := RoleHingePackage.exactTarget
  fixedTarget := RoleHingePackage.fixedTarget
  eventualTarget := RoleHingePackage.eventualTarget
  arbitraryTarget := RoleHingePackage.arbitraryTarget

/-! ## Explicit period packages -/

structure CheckedSeparatedFamilyPackage where
  candidate : CheckedPeriodCandidate
  fields : CheckedSeparatedFamilyFields candidate

structure CheckedPeriodCrossBlockLedgerPackage where
  candidate : CheckedPeriodCandidate
  fields : CheckedPeriodCrossBlockLedgerFields candidate

structure CheckedExplicitLowerBoundPackage where
  candidate : CheckedPeriodCandidate
  fields : CheckedExplicitLowerBoundFields candidate

structure CheckedExactCandidatePeriodPackage where
  candidate : CheckedPeriodCandidate
  fields : CheckedExactCandidatePeriodFields candidate

/-- Final period package variants. -/
inductive PeriodPackage where
  | target (package : TargetPeriodPackage)
  | checkedSeparatedFamily (package : CheckedSeparatedFamilyPackage)
  | checkedCrossBlockLedger
      (package : CheckedPeriodCrossBlockLedgerPackage)
  | checkedExplicitLowerBound
      (package : CheckedExplicitLowerBoundPackage)
  | checkedExactCandidate
      (package : CheckedExactCandidatePeriodPackage)
  | checkedNonRigidRoute (fields : CheckedPeriodNonRigidRouteFields)

namespace PeriodPackage

def exactTarget
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_periodPackage
        package
  | checkedSeparatedFamily package =>
      (TransitionCheckedIntegratedW11.matrix.separatedFamilyFields
        package.candidate).exactTarget package.fields
  | checkedCrossBlockLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_periodCrossBlockLedgerFields
        package.fields
  | checkedExplicitLowerBound package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_explicitLowerBoundFields
        package.fields
  | checkedExactCandidate package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_exactCandidatePeriodFields
        package.fields
  | checkedNonRigidRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_periodNonRigidRouteFields
        fields

def fixedTarget
    (package : PeriodPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
        package n
  | checkedSeparatedFamily package =>
      (TransitionCheckedIntegratedW11.matrix.separatedFamilyFields
        package.candidate).fixedTarget package.fields n
  | checkedCrossBlockLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodCrossBlockLedgerFields
        package.fields n
  | checkedExplicitLowerBound package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
        package.fields n
  | checkedExactCandidate package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
        package.fields n
  | checkedNonRigidRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
        fields n

def eventualTarget
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_periodPackage
        package
  | checkedSeparatedFamily package =>
      (TransitionCheckedIntegratedW11.matrix.separatedFamilyFields
        package.candidate).eventualTarget package.fields
  | checkedCrossBlockLedger package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodCrossBlockLedgerFields
          package.fields)
  | checkedExplicitLowerBound package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
          package.fields)
  | checkedExactCandidate package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
          package.fields)
  | checkedNonRigidRoute fields =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
          fields)

def arbitraryTarget
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
        package
  | checkedSeparatedFamily package =>
      (TransitionCheckedIntegratedW11.matrix.separatedFamilyFields
        package.candidate).arbitraryTarget package.fields
  | checkedCrossBlockLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodCrossBlockLedgerFields
        package.fields
  | checkedExplicitLowerBound package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_explicitLowerBoundFields
        package.fields
  | checkedExactCandidate package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactCandidatePeriodFields
        package.fields
  | checkedNonRigidRoute fields =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodNonRigidRouteFields
        fields

end PeriodPackage

def periodTargetRow : FinalTargetRow PeriodPackage where
  exactTarget := PeriodPackage.exactTarget
  fixedTarget := PeriodPackage.fixedTarget
  eventualTarget := PeriodPackage.eventualTarget
  arbitraryTarget := PeriodPackage.arbitraryTarget

/-! ## Fixed period block packages -/

/-- Period packages whose natural projection is an exact block target. -/
inductive PeriodBlockPackage where
  | checkedWordSeparation
      (package : TargetCheckedWordSeparationPackage)
  | explicitLowerBound
      (package : TargetPeriodExplicitLowerBoundPackage)
      (k : Nat) (positive : 0 < k)

namespace PeriodBlockPackage

def blockIndex : PeriodBlockPackage -> Nat
  | checkedWordSeparation package => package.fields.checkedWord.length
  | explicitLowerBound _ k _ => k

theorem fixedBlockTarget
    (package : PeriodBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * package.blockIndex) := by
  cases package with
  | checkedWordSeparation package =>
      exact
        TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparationPackage
          package
  | explicitLowerBound package k hk =>
      exact
        TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundPackage
          package k hk

end PeriodBlockPackage

structure PeriodBlockTargetRow where
  blockIndex : PeriodBlockPackage -> Nat
  fixedBlockTarget :
    forall package : PeriodBlockPackage,
      PachToth.targetUpperConstructionFiveSixteenAt
        (16 * blockIndex package)

def periodBlockTargetRow : PeriodBlockTargetRow where
  blockIndex := PeriodBlockPackage.blockIndex
  fixedBlockTarget := PeriodBlockPackage.fixedBlockTarget

/-! ## Explicit cross-block packages -/

structure CheckedRawCrossBlockLedgerPackage where
  family : CheckedInequalityPeriodFamily
  fields : CheckedRawCrossBlockInequalityLedger family

structure CheckedCrossBlockClosurePackage where
  family : CheckedInequalityPeriodFamily
  fields : CheckedCrossBlockClosureLedger family

/-- Final cross-block package variants. -/
inductive CrossBlockPackage where
  | target (package : TargetCrossBlockPackage)
  | checkedRawInequalityLedger
      (package : CheckedRawCrossBlockLedgerPackage)
  | checkedClosureLedger (package : CheckedCrossBlockClosurePackage)

namespace CrossBlockPackage

def exactTarget
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_crossBlockPackage
        package
  | checkedRawInequalityLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
        package.fields
  | checkedClosureLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
        package.fields

def fixedTarget
    (package : CrossBlockPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockPackage
        package n
  | checkedRawInequalityLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_rawCrossBlockInequalityLedger
        package.fields n
  | checkedClosureLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
        package.fields n

def eventualTarget
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_crossBlockPackage
        package
  | checkedRawInequalityLedger package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
          package.fields)
  | checkedClosureLedger package =>
      eventualTargetOfArbitrary
        (TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
          package.fields)

def arbitraryTarget
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  match package with
  | target package =>
      TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockPackage
        package
  | checkedRawInequalityLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
        package.fields
  | checkedClosureLedger package =>
      TransitionCheckedIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        package.fields

end CrossBlockPackage

def crossBlockTargetRow : FinalTargetRow CrossBlockPackage where
  exactTarget := CrossBlockPackage.exactTarget
  fixedTarget := CrossBlockPackage.fixedTarget
  eventualTarget := CrossBlockPackage.eventualTarget
  arbitraryTarget := CrossBlockPackage.arbitraryTarget

/-! ## Package ledgers and blocker projections -/

/-- Explicit package shapes accepted by the final transition aggregate. -/
structure ExplicitPackageLedger where
  routePackages : Type
  candidatePackages : Type
  roleHingePackages : Type
  periodPackages : Type
  periodBlockPackages : Type
  crossBlockPackages : Type
  exactLocalTargetFields : Type

def explicitPackageLedger : ExplicitPackageLedger where
  routePackages := RoutePackage
  candidatePackages := CandidatePackage
  roleHingePackages := RoleHingePackage
  periodPackages := PeriodPackage
  periodBlockPackages := PeriodBlockPackage
  crossBlockPackages := CrossBlockPackage
  exactLocalTargetFields := ExactLocalTargetFields

/-- Checked matrices imported by this final aggregate. -/
structure ImportedMatrices where
  transitionTarget : TargetMatrix
  transitionIntegrated : IntegratedMatrix
  transitionChecked : CheckedMatrix
  exactLocalTarget : ExactLocalTargetMatrix

def importedMatrices : ImportedMatrices where
  transitionTarget := TransitionTargetIntegratedW11.matrix
  transitionIntegrated := TransitionIntegratedW11.matrix
  transitionChecked := TransitionCheckedIntegratedW11.matrix
  exactLocalTarget := ExactLocalTargetIntegratedW11.matrix

/-- Blocker facts projected by the final transition aggregate. -/
structure BlockerProjections where
  targetBlockers : TransitionTargetIntegratedW11.ConcreteBlockerProjections
  checkedBlockers : TransitionCheckedIntegratedW11.BlockerLedger
  exactLocalEndpointBlockers :
    ExactLocalTargetIntegratedW11.EndpointBlockerLedger
  targetRouteClaimBlocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  checkedRouteClaimBlocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  targetCompletedFilteredRouteBlocked :
    TransitionTargetIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  checkedCompletedFilteredRouteBlocked :
    TransitionCheckedIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  targetSameOppositeCandidateFieldsBlocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  checkedSameOppositeCandidateFieldsBlocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  fullSameRestShortcutBlocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  checkedMissingCandidateRowsBlocked :
    forall C : ExactLocalClosureW11.CandidateRows,
      Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C)
  endpointShortcutBlocked :
    forall E : ExactLocalEndpointShortcutRow,
      Not (ExactLocalPossibleRow E.u E.v)

def blockerProjections : BlockerProjections where
  targetBlockers := TransitionTargetIntegratedW11.concreteBlockerProjections
  checkedBlockers := TransitionCheckedIntegratedW11.blockerLedger
  exactLocalEndpointBlockers :=
    ExactLocalTargetIntegratedW11.endpointBlockerLedger
  targetRouteClaimBlocked :=
    TransitionTargetIntegratedW11.transitionConcreteFourTargetRouteClaim_blocked
  checkedRouteClaimBlocked :=
    TransitionCheckedIntegratedW11.concreteFourTargetRouteClaim_blocked
  targetCompletedFilteredRouteBlocked :=
    TransitionTargetIntegratedW11.transitionConcreteFourTargetCompletedFilteredRoute_blocked
  checkedCompletedFilteredRouteBlocked :=
    TransitionCheckedIntegratedW11.concreteFourTargetCompletedFilteredRoute_blocked
  targetSameOppositeCandidateFieldsBlocked :=
    TransitionTargetIntegratedW11.transitionConcreteFourTargetSameOppositeCandidateFields_blocked
  checkedSameOppositeCandidateFieldsBlocked :=
    TransitionCheckedIntegratedW11.concreteFourTargetSameOppositeCandidateFields_blocked
  fullSameRestShortcutBlocked :=
    TransitionTargetIntegratedW11.transitionConcreteFourTargetFullSameRestShortcut_blocked
  checkedMissingCandidateRowsBlocked :=
    TransitionCheckedIntegratedW11.concreteMissingCandidateRows_blocked
  endpointShortcutBlocked :=
    ExactLocalTargetIntegratedW11.endpointShortcut_not_possible

/-! ## Final matrix -/

/-- Final W11 transition aggregate matrix. -/
structure Matrix where
  packages : ExplicitPackageLedger
  imported : ImportedMatrices
  routeTargets : FinalTargetRow RoutePackage
  candidateTargets : FinalTargetRow CandidatePackage
  roleHingeTargets : FinalTargetRow RoleHingePackage
  periodTargets : FinalTargetRow PeriodPackage
  periodBlockTargets : PeriodBlockTargetRow
  crossBlockTargets : FinalTargetRow CrossBlockPackage
  blockers : BlockerProjections

/-- The checked final W11 transition aggregate. -/
def matrix : Matrix where
  packages := explicitPackageLedger
  imported := importedMatrices
  routeTargets := routeTargetRow
  candidateTargets := candidateTargetRow
  roleHingeTargets := roleHingeTargetRow
  periodTargets := periodTargetRow
  periodBlockTargets := periodBlockTargetRow
  crossBlockTargets := crossBlockTargetRow
  blockers := blockerProjections

/-! ## Public route projections -/

theorem targetUpperConstructionFiveSixteen_of_routePackage
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.routeTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_routePackage
    (package : RoutePackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.routeTargets.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_routePackage
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.routeTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_routePackage
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.routeTargets.arbitraryTarget package

/-! ## Public candidate projections -/

theorem targetUpperConstructionFiveSixteen_of_candidatePackage
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_candidatePackage
    (package : CandidatePackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.candidateTargets.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_candidatePackage
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.candidateTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidatePackage
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateTargets.arbitraryTarget package

/-! ## Public role-hinge projections -/

theorem targetUpperConstructionFiveSixteen_of_roleHingePackage
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleHingeTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_roleHingePackage
    (package : RoleHingePackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.roleHingeTargets.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_roleHingePackage
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.roleHingeTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleHingePackage
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleHingeTargets.arbitraryTarget package

/-! ## Public period projections -/

theorem targetUpperConstructionFiveSixteen_of_periodPackage
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.periodTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_periodPackage
    (package : PeriodPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.periodTargets.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_periodPackage
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.periodTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.periodTargets.arbitraryTarget package

theorem targetUpperConstructionFiveSixteenAt_of_periodBlockPackage
    (package : PeriodBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * matrix.periodBlockTargets.blockIndex package) :=
  matrix.periodBlockTargets.fixedBlockTarget package

/-! ## Public cross-block projections -/

theorem targetUpperConstructionFiveSixteen_of_crossBlockPackage
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.crossBlockTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockPackage
    (package : CrossBlockPackage) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  matrix.crossBlockTargets.fixedTarget package n

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockPackage
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.crossBlockTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockPackage
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockTargets.arbitraryTarget package

/-! ## Public blocker projections -/

theorem target_concreteFourTargetT11R_not_possible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r) :=
  matrix.blockers.targetBlockers.t11rNotPossible

theorem target_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.targetRouteClaimBlocked

theorem checked_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.checkedRouteClaimBlocked

theorem target_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionTargetIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.targetCompletedFilteredRouteBlocked

theorem checked_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionCheckedIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.checkedCompletedFilteredRouteBlocked

theorem target_concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.targetSameOppositeCandidateFieldsBlocked

theorem checked_concreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.checkedSameOppositeCandidateFieldsBlocked

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcutBlocked

theorem checked_concreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.blockers.checkedMissingCandidateRowsBlocked C

theorem exactLocal_endpointShortcut_not_possible
    (E : ExactLocalEndpointShortcutRow) :
    Not (ExactLocalPossibleRow E.u E.v) :=
  matrix.blockers.endpointShortcutBlocked E

theorem exactLocal_pUpperForward_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_1) :=
  matrix.blockers.exactLocalEndpointBlockers.pUpperForward

theorem exactLocal_pUpperReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.T2_2) :=
  matrix.blockers.exactLocalEndpointBlockers.pUpperReverse

theorem exactLocal_pLowerForward_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_2) :=
  matrix.blockers.exactLocalEndpointBlockers.pLowerForward

theorem exactLocal_pLowerReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T1_2 FiniteGraph.LocalVertex.T2_2) :=
  matrix.blockers.exactLocalEndpointBlockers.pLowerReverse

theorem exactLocal_qUpperForward_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_0) :=
  matrix.blockers.exactLocalEndpointBlockers.qUpperForward

theorem exactLocal_qUpperReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T0_0 FiniteGraph.LocalVertex.T4_0) :=
  matrix.blockers.exactLocalEndpointBlockers.qUpperReverse

theorem exactLocal_qLowerForward_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_2) :=
  matrix.blockers.exactLocalEndpointBlockers.qLowerForward

theorem exactLocal_qLowerReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalPossibleRow
        FiniteGraph.LocalVertex.T0_2 FiniteGraph.LocalVertex.T4_0) :=
  matrix.blockers.exactLocalEndpointBlockers.qLowerReverse

end

end TransitionFinalIntegratedW11
end PachToth
end ErdosProblems1066
