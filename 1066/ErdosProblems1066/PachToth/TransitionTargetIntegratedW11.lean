import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.PeriodIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 transition target aggregate

This module is the target-facing aggregate over the checked transition,
candidate, role-hinge, period, cross-block, and W11 integrated matrices.

Each target projection consumes an explicit package value.  The concrete
four-target blockers are exposed as projections from a blocker ledger, rather
than as target conclusions.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionTargetIntegratedW11

noncomputable section

abbrev TransitionCandidate := TransitionIntegratedW11.TransitionCandidate
abbrev FilteredSameOpposite := TransitionIntegratedW11.FilteredSameOpposite
abbrev TransitionRemainingFields :=
  TransitionIntegratedW11.TransitionRemainingFields
abbrev TransitionRouteFields := TransitionIntegratedW11.TransitionRouteFields
abbrev CompletedFilteredRouteFields :=
  TransitionIntegratedW11.CompletedFilteredRouteFields
abbrev ExactLocalRouteFields := TransitionIntegratedW11.ExactLocalRouteFields

abbrev CandidateAssemblyFields :=
  TransitionIntegratedW11.CandidateAssemblyFields
abbrev FlexibleCandidateFields :=
  TransitionIntegratedW11.FlexibleCandidateFields
abbrev CandidateValueMatrixFamily :=
  TransitionIntegratedW11.CandidateValueMatrixFamily
abbrev FinalConditionalFamily :=
  TransitionIntegratedW11.FinalConditionalFamily

abbrev RoleHingePeriodFamily :=
  TransitionIntegratedW11.RoleHingePeriodFamily
abbrev RoleEquationRouteFields :=
  TransitionIntegratedW11.RoleEquationRouteFields
abbrev RoleLedgerCandidateAssemblyFields :=
  TransitionIntegratedW11.RoleLedgerCandidateAssemblyFields
abbrev RoleCrossBlockLowerBoundPackage :=
  TransitionIntegratedW11.RoleCrossBlockLowerBoundPackage

abbrev PeriodCandidate := PeriodIntegratedW11.Candidate
abbrev CheckedWordSeparationFields :=
  PeriodIntegratedW11.CheckedWordSeparationFields
abbrev GeneratedFamilyRemainingFields :=
  PeriodIntegratedW11.GeneratedFamilyRemainingFields
abbrev CrossBlockLedgerClosureFields :=
  PeriodIntegratedW11.CrossBlockLedgerClosureFields
abbrev ExplicitLowerBoundClosureFields :=
  PeriodIntegratedW11.ExplicitLowerBoundClosureFields
abbrev ExactCandidatePeriodFields :=
  PeriodIntegratedW11.ExactCandidatePeriodFields
abbrev PeriodNonRigidRouteFields :=
  PeriodIntegratedW11.PeriodNonRigidRouteFields

abbrev InequalityPeriodFamily := PeriodIntegratedW11.InequalityPeriodFamily
abbrev RawCrossBlockInequalityLedger :=
  PeriodIntegratedW11.RawCrossBlockInequalityLedger
abbrev CrossBlockClosureLedger :=
  PeriodIntegratedW11.CrossBlockClosureLedger

/-! ## Shared rows -/

/-- Exact, eventual, and arbitrary target projections from one package shape. -/
structure TargetProjectionRow (alpha : Type) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-! ## Explicit package variants -/

structure TransitionRemainingPackage where
  candidate : TransitionCandidate
  fields : TransitionRemainingFields candidate

structure CompletedFilteredRoutePackage where
  filtered : FilteredSameOpposite
  fields : CompletedFilteredRouteFields filtered

/-- Route-facing packages accepted by the transition target aggregate. -/
inductive RoutePackage where
  | transitionRemaining (package : TransitionRemainingPackage)
  | transitionRoute (fields : TransitionRouteFields)
  | completedFiltered (package : CompletedFilteredRoutePackage)
  | exactLocal (fields : ExactLocalRouteFields)

/-- Candidate-facing packages accepted by the transition target aggregate. -/
inductive CandidatePackage where
  | candidateAssembly (fields : CandidateAssemblyFields)
  | flexibleCandidate (fields : FlexibleCandidateFields)
  | candidateValueMatrix (fields : CandidateValueMatrixFamily)
  | finalConditional (fields : FinalConditionalFamily)

structure RoleCrossBlockLowerBoundClosurePackage where
  family : RoleHingePeriodFamily
  fields : RoleCrossBlockLowerBoundPackage family

/-- Role-hinge-facing packages accepted by the aggregate. -/
inductive RoleHingePackage where
  | equationRoute (fields : RoleEquationRouteFields)
  | ledgerCandidateAssembly (fields : RoleLedgerCandidateAssemblyFields)
  | crossBlockLowerBound (package : RoleCrossBlockLowerBoundClosurePackage)

structure CheckedWordSeparationPackage where
  candidate : PeriodCandidate
  fields : CheckedWordSeparationFields candidate

structure PeriodSeparatedPackage where
  candidate : PeriodCandidate
  fields : GeneratedFamilyRemainingFields candidate

structure PeriodCrossBlockLedgerPackage where
  candidate : PeriodCandidate
  fields : CrossBlockLedgerClosureFields candidate

structure PeriodExplicitLowerBoundPackage where
  candidate : PeriodCandidate
  fields : ExplicitLowerBoundClosureFields candidate

structure PeriodExactCandidatePackage where
  candidate : PeriodCandidate
  fields : ExactCandidatePeriodFields candidate

/-- Period-facing packages accepted by the aggregate. -/
inductive PeriodPackage where
  | separatedFamily (package : PeriodSeparatedPackage)
  | crossBlockLedger (package : PeriodCrossBlockLedgerPackage)
  | explicitLowerBound (package : PeriodExplicitLowerBoundPackage)
  | exactCandidate (package : PeriodExactCandidatePackage)
  | nonRigidRoute (fields : PeriodNonRigidRouteFields)

structure RawCrossBlockLedgerPackage where
  family : InequalityPeriodFamily
  fields : RawCrossBlockInequalityLedger family

structure CrossBlockClosureLedgerPackage where
  family : InequalityPeriodFamily
  fields : CrossBlockClosureLedger family

/-- Cross-block packages accepted by the aggregate. -/
inductive CrossBlockPackage where
  | rawInequalityLedger (package : RawCrossBlockLedgerPackage)
  | closureLedger (package : CrossBlockClosureLedgerPackage)

/-! ## Package ledgers -/

/-- The explicit target-facing package shapes gathered by this aggregate. -/
structure ExplicitTargetPackageLedger where
  routePackages : Type
  candidatePackages : Type
  roleHingePackages : Type
  periodPackages : Type
  checkedWordSeparationPackages : Type
  crossBlockPackages : Type

def explicitTargetPackageLedger : ExplicitTargetPackageLedger where
  routePackages := RoutePackage
  candidatePackages := CandidatePackage
  roleHingePackages := RoleHingePackage
  periodPackages := PeriodPackage
  checkedWordSeparationPackages := CheckedWordSeparationPackage
  crossBlockPackages := CrossBlockPackage

/-! ## Target projections for package variants -/

namespace RoutePackage

def exactTarget : RoutePackage -> PachToth.targetUpperConstructionFiveSixteen
  | transitionRemaining package =>
      (TransitionIntegratedW11.matrix.transitionRemainingFields
        package.candidate).exactTarget package.fields
  | transitionRoute fields =>
      TransitionIntegratedW11.matrix.transitionRouteFields.exactTarget fields
  | completedFiltered package =>
      (TransitionIntegratedW11.matrix.completedFilteredRouteFields
        package.filtered).exactTarget package.fields
  | exactLocal fields =>
      TransitionIntegratedW11.matrix.exactLocalRouteFields.exactTarget fields

def eventualTarget :
    RoutePackage -> PachToth.targetUpperConstructionFiveSixteenEventually
  | transitionRemaining package =>
      (TransitionIntegratedW11.matrix.transitionRemainingFields
        package.candidate).eventualTarget package.fields
  | transitionRoute fields =>
      TransitionIntegratedW11.matrix.transitionRouteFields.eventualTarget
        fields
  | completedFiltered package =>
      (TransitionIntegratedW11.matrix.completedFilteredRouteFields
        package.filtered).eventualTarget package.fields
  | exactLocal fields =>
      TransitionIntegratedW11.matrix.exactLocalRouteFields.eventualTarget
        fields

def arbitraryTarget :
    RoutePackage -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  | transitionRemaining package =>
      (TransitionIntegratedW11.matrix.transitionRemainingFields
        package.candidate).arbitraryTarget package.fields
  | transitionRoute fields =>
      TransitionIntegratedW11.matrix.transitionRouteFields.arbitraryTarget
        fields
  | completedFiltered package =>
      (TransitionIntegratedW11.matrix.completedFilteredRouteFields
        package.filtered).arbitraryTarget package.fields
  | exactLocal fields =>
      TransitionIntegratedW11.matrix.exactLocalRouteFields.arbitraryTarget
        fields

end RoutePackage

def routeTargetRow : TargetProjectionRow RoutePackage where
  exactTarget := RoutePackage.exactTarget
  eventualTarget := RoutePackage.eventualTarget
  arbitraryTarget := RoutePackage.arbitraryTarget

namespace CandidatePackage

def exactTarget :
    CandidatePackage -> PachToth.targetUpperConstructionFiveSixteen
  | candidateAssembly fields =>
      TransitionIntegratedW11.matrix.candidateAssemblyFields.exactTarget
        fields
  | flexibleCandidate fields =>
      TransitionIntegratedW11.matrix.flexibleCandidateFields.exactTarget
        fields
  | candidateValueMatrix fields =>
      TransitionIntegratedW11.matrix.candidateValueMatrixFamily.exactTarget
        fields
  | finalConditional fields =>
      TransitionIntegratedW11.matrix.finalConditionalFamily.exactTarget fields

def eventualTarget :
    CandidatePackage -> PachToth.targetUpperConstructionFiveSixteenEventually
  | candidateAssembly fields =>
      TransitionIntegratedW11.matrix.candidateAssemblyFields.eventualTarget
        fields
  | flexibleCandidate fields =>
      TransitionIntegratedW11.matrix.flexibleCandidateFields.eventualTarget
        fields
  | candidateValueMatrix fields =>
      TransitionIntegratedW11.matrix.candidateValueMatrixFamily.eventualTarget
        fields
  | finalConditional fields =>
      TransitionIntegratedW11.matrix.finalConditionalFamily.eventualTarget
        fields

def arbitraryTarget :
    CandidatePackage -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  | candidateAssembly fields =>
      TransitionIntegratedW11.matrix.candidateAssemblyFields.arbitraryTarget
        fields
  | flexibleCandidate fields =>
      TransitionIntegratedW11.matrix.flexibleCandidateFields.arbitraryTarget
        fields
  | candidateValueMatrix fields =>
      TransitionIntegratedW11.matrix.candidateValueMatrixFamily.arbitraryTarget
        fields
  | finalConditional fields =>
      TransitionIntegratedW11.matrix.finalConditionalFamily.arbitraryTarget
        fields

end CandidatePackage

def candidateTargetRow : TargetProjectionRow CandidatePackage where
  exactTarget := CandidatePackage.exactTarget
  eventualTarget := CandidatePackage.eventualTarget
  arbitraryTarget := CandidatePackage.arbitraryTarget

namespace RoleHingePackage

def exactTarget :
    RoleHingePackage -> PachToth.targetUpperConstructionFiveSixteen
  | equationRoute fields =>
      TransitionIntegratedW11.matrix.roleEquationRouteFields.exactTarget
        fields
  | ledgerCandidateAssembly fields =>
      TransitionIntegratedW11.matrix.roleLedgerCandidateAssemblyFields
        |>.exactTarget fields
  | crossBlockLowerBound package =>
      (TransitionIntegratedW11.matrix.roleCrossBlockLowerBoundClosure
        package.family).exactTarget package.fields

def eventualTarget :
    RoleHingePackage -> PachToth.targetUpperConstructionFiveSixteenEventually
  | equationRoute fields =>
      TransitionIntegratedW11.matrix.roleEquationRouteFields.eventualTarget
        fields
  | ledgerCandidateAssembly fields =>
      TransitionIntegratedW11.matrix.roleLedgerCandidateAssemblyFields
        |>.eventualTarget fields
  | crossBlockLowerBound package =>
      (TransitionIntegratedW11.matrix.roleCrossBlockLowerBoundClosure
        package.family).eventualTarget package.fields

def arbitraryTarget :
    RoleHingePackage -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  | equationRoute fields =>
      TransitionIntegratedW11.matrix.roleEquationRouteFields.arbitraryTarget
        fields
  | ledgerCandidateAssembly fields =>
      TransitionIntegratedW11.matrix.roleLedgerCandidateAssemblyFields
        |>.arbitraryTarget fields
  | crossBlockLowerBound package =>
      (TransitionIntegratedW11.matrix.roleCrossBlockLowerBoundClosure
        package.family).arbitraryTarget package.fields

end RoleHingePackage

def roleHingeTargetRow : TargetProjectionRow RoleHingePackage where
  exactTarget := RoleHingePackage.exactTarget
  eventualTarget := RoleHingePackage.eventualTarget
  arbitraryTarget := RoleHingePackage.arbitraryTarget

namespace PeriodPackage

def exactTarget : PeriodPackage -> PachToth.targetUpperConstructionFiveSixteen
  | separatedFamily package =>
      (PeriodIntegratedW11.matrix.separatedFamilies
        package.candidate).exactTarget package.fields
  | crossBlockLedger package =>
      (PeriodIntegratedW11.matrix.crossBlockLedgerFields
        package.candidate).exactTarget package.fields
  | explicitLowerBound package =>
      (PeriodIntegratedW11.matrix.explicitLowerBoundFields
        package.candidate).exactTarget package.fields
  | exactCandidate package =>
      (PeriodIntegratedW11.matrix.exactCandidatePeriodFields
        package.candidate).exactTarget package.fields
  | nonRigidRoute fields =>
      PeriodIntegratedW11.matrix.periodNonRigidRouteFields.exactTarget fields

def eventualTarget :
    PeriodPackage -> PachToth.targetUpperConstructionFiveSixteenEventually
  | separatedFamily package =>
      (PeriodIntegratedW11.matrix.separatedFamilies
        package.candidate).eventualTarget package.fields
  | crossBlockLedger package =>
      (PeriodIntegratedW11.matrix.crossBlockLedgerFields
        package.candidate).eventualTarget package.fields
  | explicitLowerBound package =>
      (PeriodIntegratedW11.matrix.explicitLowerBoundFields
        package.candidate).eventualTarget package.fields
  | exactCandidate package =>
      (PeriodIntegratedW11.matrix.exactCandidatePeriodFields
        package.candidate).eventualTarget package.fields
  | nonRigidRoute fields =>
      PeriodIntegratedW11.matrix.periodNonRigidRouteFields.eventualTarget
        fields

def arbitraryTarget :
    PeriodPackage -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  | separatedFamily package =>
      (PeriodIntegratedW11.matrix.separatedFamilies
        package.candidate).arbitraryTarget package.fields
  | crossBlockLedger package =>
      (PeriodIntegratedW11.matrix.crossBlockLedgerFields
        package.candidate).arbitraryTarget package.fields
  | explicitLowerBound package =>
      (PeriodIntegratedW11.matrix.explicitLowerBoundFields
        package.candidate).arbitraryTarget package.fields
  | exactCandidate package =>
      (PeriodIntegratedW11.matrix.exactCandidatePeriodFields
        package.candidate).arbitraryTarget package.fields
  | nonRigidRoute fields =>
      PeriodIntegratedW11.matrix.periodNonRigidRouteFields.arbitraryTarget
        fields

end PeriodPackage

def periodTargetRow : TargetProjectionRow PeriodPackage where
  exactTarget := PeriodPackage.exactTarget
  eventualTarget := PeriodPackage.eventualTarget
  arbitraryTarget := PeriodPackage.arbitraryTarget

namespace CrossBlockPackage

def exactTarget :
    CrossBlockPackage -> PachToth.targetUpperConstructionFiveSixteen
  | rawInequalityLedger package =>
      (PeriodIntegratedW11.matrix.rawCrossBlockInequalityLedgers
        package.family).exactTarget package.fields
  | closureLedger package =>
      (PeriodIntegratedW11.matrix.crossBlockClosureLedgers
        package.family).exactTarget package.fields

def eventualTarget :
    CrossBlockPackage -> PachToth.targetUpperConstructionFiveSixteenEventually
  | rawInequalityLedger package =>
      (PeriodIntegratedW11.matrix.rawCrossBlockInequalityLedgers
        package.family).eventualTarget package.fields
  | closureLedger package =>
      (PeriodIntegratedW11.matrix.crossBlockClosureLedgers
        package.family).eventualTarget package.fields

def arbitraryTarget :
    CrossBlockPackage -> PachToth.targetUpperConstructionFiveSixteenArbitrary
  | rawInequalityLedger package =>
      (PeriodIntegratedW11.matrix.rawCrossBlockInequalityLedgers
        package.family).arbitraryTarget package.fields
  | closureLedger package =>
      (PeriodIntegratedW11.matrix.crossBlockClosureLedgers
        package.family).arbitraryTarget package.fields

end CrossBlockPackage

def crossBlockTargetRow : TargetProjectionRow CrossBlockPackage where
  exactTarget := CrossBlockPackage.exactTarget
  eventualTarget := CrossBlockPackage.eventualTarget
  arbitraryTarget := CrossBlockPackage.arbitraryTarget

/-! ## Fixed period block projections -/

theorem targetUpperConstructionFiveSixteenAt_of_checkedWordSeparationPackage
    (package : CheckedWordSeparationPackage) :
    PachToth.targetUpperConstructionFiveSixteenAt
      (16 * package.fields.checkedWord.length) :=
  PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_of_checkedWordSeparation
    package.fields

theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundPackage
    (package : PeriodExplicitLowerBoundPackage)
    (k : Nat) (hk : 0 < k) :
    PachToth.targetUpperConstructionFiveSixteenAt (16 * k) :=
  PeriodIntegratedW11.targetUpperConstructionFiveSixteenAt_exactBlock_of_explicitLowerBoundFields
    package.fields k hk

/-! ## Concrete blocker ledger -/

structure ConcreteBlockerProjections where
  t11rNotPossible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r)
  transitionRouteClaimBlocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  transitionCompletedFilteredRouteBlocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  transitionSameOppositeCandidateFieldsBlocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)
  transitionFullSameRestShortcutBlocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  inheritedRouteClaimBlocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  inheritedCompletedFilteredRouteBlocked :
    PachTothW11ClosureMatrix.W11CompletedFilteredRouteFields
        FlexibleTransitionSearchW11.concreteFourTargetCheckedRows.filtered ->
      False
  inheritedFullSameRestShortcutBlocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  checkedMatrixRouteClaimBlocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  checkedMatrixCompletedFilteredRouteBlocked :
    FlexibleTransitionSearchW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  checkedMatrixSameOppositeCandidateFieldsBlocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext)

def concreteBlockerProjections : ConcreteBlockerProjections where
  t11rNotPossible :=
    TransitionIntegratedW11.concreteFourTargetT11R_not_possible
  transitionRouteClaimBlocked :=
    TransitionIntegratedW11.concreteFourTargetRouteClaim_blocked
  transitionCompletedFilteredRouteBlocked :=
    TransitionIntegratedW11.concreteFourTargetCompletedFilteredRoute_blocked
  transitionSameOppositeCandidateFieldsBlocked :=
    TransitionIntegratedW11.concreteFourTargetSameOppositeCandidateFields_blocked
  transitionFullSameRestShortcutBlocked :=
    TransitionIntegratedW11.concreteFourTargetFullSameRestShortcut_blocked
  inheritedRouteClaimBlocked :=
    TransitionIntegratedW11.inheritedConcreteFourTargetRouteClaim_blocked
  inheritedCompletedFilteredRouteBlocked :=
    TransitionIntegratedW11.inheritedConcreteFourTargetCompletedFilteredRoute_blocked
  inheritedFullSameRestShortcutBlocked :=
    TransitionIntegratedW11.inheritedConcreteFourTargetFullSameRestShortcut_blocked
  checkedMatrixRouteClaimBlocked :=
    PachTothW11IntegratedMatrix.concreteFourTargetRouteClaim_blocked
  checkedMatrixCompletedFilteredRouteBlocked :=
    PachTothW11IntegratedMatrix.concreteFourTargetCompletedFilteredRoute_blocked
  checkedMatrixSameOppositeCandidateFieldsBlocked :=
    PachTothW11IntegratedMatrix.concreteFourTargetSameOppositeCandidateFields_blocked

/-! ## Aggregate matrix -/

/-- Target-facing W11 transition aggregate. -/
structure Matrix where
  packages : ExplicitTargetPackageLedger
  transitionMatrix : TransitionIntegratedW11.Matrix
  periodMatrix : PeriodIntegratedW11.Matrix
  checkedW11Matrix : PachTothW11IntegratedMatrix.Matrix
  routeTargets : TargetProjectionRow RoutePackage
  candidateTargets : TargetProjectionRow CandidatePackage
  roleHingeTargets : TargetProjectionRow RoleHingePackage
  periodTargets : TargetProjectionRow PeriodPackage
  crossBlockTargets : TargetProjectionRow CrossBlockPackage
  blockers : ConcreteBlockerProjections

def matrix : Matrix where
  packages := explicitTargetPackageLedger
  transitionMatrix := TransitionIntegratedW11.matrix
  periodMatrix := PeriodIntegratedW11.matrix
  checkedW11Matrix := PachTothW11IntegratedMatrix.matrix
  routeTargets := routeTargetRow
  candidateTargets := candidateTargetRow
  roleHingeTargets := roleHingeTargetRow
  periodTargets := periodTargetRow
  crossBlockTargets := crossBlockTargetRow
  blockers := concreteBlockerProjections

/-! ## Public target projections -/

theorem targetUpperConstructionFiveSixteen_of_routePackage
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.routeTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenEventually_of_routePackage
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.routeTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_routePackage
    (package : RoutePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.routeTargets.arbitraryTarget package

theorem targetUpperConstructionFiveSixteen_of_candidatePackage
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.candidateTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenEventually_of_candidatePackage
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.candidateTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_candidatePackage
    (package : CandidatePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.candidateTargets.arbitraryTarget package

theorem targetUpperConstructionFiveSixteen_of_roleHingePackage
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleHingeTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenEventually_of_roleHingePackage
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.roleHingeTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleHingePackage
    (package : RoleHingePackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleHingeTargets.arbitraryTarget package

theorem targetUpperConstructionFiveSixteen_of_periodPackage
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.periodTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenEventually_of_periodPackage
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.periodTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
    (package : PeriodPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.periodTargets.arbitraryTarget package

theorem targetUpperConstructionFiveSixteen_of_crossBlockPackage
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.crossBlockTargets.exactTarget package

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockPackage
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.crossBlockTargets.eventualTarget package

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockPackage
    (package : CrossBlockPackage) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.crossBlockTargets.arbitraryTarget package

/-! ## Public blocker projections -/

theorem concreteFourTargetT11R_not_possible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r) :=
  matrix.blockers.t11rNotPossible

theorem transitionConcreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.transitionRouteClaimBlocked

theorem transitionConcreteFourTargetCompletedFilteredRoute_blocked :
    CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.transitionCompletedFilteredRouteBlocked

theorem transitionConcreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.transitionSameOppositeCandidateFieldsBlocked

theorem transitionConcreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.transitionFullSameRestShortcutBlocked

theorem inheritedConcreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.inheritedRouteClaimBlocked

theorem inheritedConcreteFourTargetCompletedFilteredRoute_blocked :
    PachTothW11ClosureMatrix.W11CompletedFilteredRouteFields
        FlexibleTransitionSearchW11.concreteFourTargetCheckedRows.filtered ->
      False :=
  matrix.blockers.inheritedCompletedFilteredRouteBlocked

theorem inheritedConcreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.inheritedFullSameRestShortcutBlocked

theorem checkedMatrixConcreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.checkedMatrixRouteClaimBlocked

theorem checkedMatrixConcreteFourTargetCompletedFilteredRoute_blocked :
    FlexibleTransitionSearchW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.checkedMatrixCompletedFilteredRouteBlocked

theorem checkedMatrixConcreteFourTargetSameOppositeCandidateFields_blocked :
    Not
      (exists F : FlexibleBranchSearchSummaryW10.W10SameOppositeCandidateFields,
        F.same.parameters.placeNext =
          RoleHingeConcreteSearch.samePlaceNext /\
        F.opposite.parameters.placeNext =
          RoleHingeConcreteSearch.oppositePlaceNext) :=
  matrix.blockers.checkedMatrixSameOppositeCandidateFieldsBlocked

end

end TransitionTargetIntegratedW11
end PachToth
end ErdosProblems1066
