import ErdosProblems1066.PachToth.TransitionRoleTargetFinalW11
import ErdosProblems1066.PachToth.TransitionRoleHingeFinalW11
import ErdosProblems1066.PachToth.RoleHingeTargetFinalW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# W11 final transition/role ledger

This file is a concise terminal ledger over the checked W11 transition,
role-hinge, target, and Pach--Toth aggregate facades.  It records the explicit
package ledgers and blocker rows, then exposes target conclusions only as
projections from displayed package or field inputs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionRoleLedgerFinalW11

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

/-! ## Shared projection rows -/

/-- Exact, fixed, eventual, and arbitrary target projections from one input. -/
structure ConditionalTargets (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Exact, eventual, and arbitrary target projections from one input. -/
structure RoleTargets (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Arbitrary target projection from one input. -/
structure ArbitraryTargets (alpha : Sort u) : Sort (max 1 u) where
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Fixed block projection whose block index stays attached to the input. -/
structure FixedBlockTargets (alpha : Sort u) : Sort (max 1 u) where
  blockIndex : alpha -> Nat
  fixedBlockTarget : forall a : alpha, FixedTarget (16 * blockIndex a)

/-! ## Explicit packages and imports -/

/-- Explicit package and field ledgers retained by the terminal facade. -/
structure ExplicitPackageLedger where
  transitionFinal : TransitionFinalIntegratedW11.ExplicitPackageLedger
  transitionRoleHinge : TransitionRoleHingeFinalW11.ExplicitRoutePackages
  transitionRoleTarget : TransitionRoleTargetFinalW11.SourceLedger
  roleHingeTarget : RoleHingeTargetFinalW11.RoleHingeTargetFieldLedger
  pachTothOpenData : PachTothW11FinalAggregate.ExplicitOpenData
  pachTothAvailability : PachTothW11FinalAggregate.FinalLedgerAvailability

/-- Checked package and field ledgers. -/
def explicitPackageLedger : ExplicitPackageLedger where
  transitionFinal := TransitionFinalIntegratedW11.explicitPackageLedger
  transitionRoleHinge := TransitionRoleHingeFinalW11.explicitRoutePackages
  transitionRoleTarget := TransitionRoleTargetFinalW11.sourceLedger
  roleHingeTarget := RoleHingeTargetFinalW11.roleHingeTargetFieldLedger
  pachTothOpenData := PachTothW11FinalAggregate.explicitOpenData
  pachTothAvailability := PachTothW11FinalAggregate.finalLedgerAvailability

/-- Checked matrices imported by this terminal ledger. -/
structure ImportedMatrices where
  transitionRoleTarget : TransitionRoleTargetFinalW11.Matrix
  transitionRoleHinge : TransitionRoleHingeFinalW11.Matrix
  roleHingeTarget : RoleHingeTargetFinalW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  pachTothAggregate : PachTothW11FinalAggregate.Matrix

/-- Imported checked W11 matrices. -/
def importedMatrices : ImportedMatrices where
  transitionRoleTarget := TransitionRoleTargetFinalW11.matrix
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix
  roleHingeTarget := RoleHingeTargetFinalW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  pachTothAggregate := PachTothW11FinalAggregate.matrix

/-! ## Transition package projections -/

/-- Package-indexed projections carried by the final transition aggregate. -/
structure TransitionProjectionLedger where
  route : ConditionalTargets TransitionFinalIntegratedW11.RoutePackage
  candidate : ConditionalTargets TransitionFinalIntegratedW11.CandidatePackage
  roleHinge : ConditionalTargets TransitionFinalIntegratedW11.RoleHingePackage
  period : ConditionalTargets TransitionFinalIntegratedW11.PeriodPackage
  periodBlock : FixedBlockTargets TransitionFinalIntegratedW11.PeriodBlockPackage
  crossBlock : ConditionalTargets TransitionFinalIntegratedW11.CrossBlockPackage

/-- Checked transition projections, all conditional on a package value. -/
def transitionProjectionLedger : TransitionProjectionLedger where
  route := {
    exactTarget := TransitionRoleTargetFinalW11.exactTarget_of_transitionRoutePackage
    fixedTarget := TransitionRoleTargetFinalW11.fixedTarget_of_transitionRoutePackage
    eventualTarget := TransitionRoleTargetFinalW11.eventualTarget_of_transitionRoutePackage
    arbitraryTarget := TransitionRoleTargetFinalW11.arbitraryTarget_of_transitionRoutePackage }
  candidate := {
    exactTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_candidatePackage
    fixedTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_candidatePackage
    eventualTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_candidatePackage
    arbitraryTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_candidatePackage }
  roleHinge := {
    exactTarget := TransitionRoleTargetFinalW11.exactTarget_of_transitionRoleHingePackage
    fixedTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_roleHingePackage
    eventualTarget :=
      TransitionRoleHingeFinalW11.eventualTarget_of_transitionRoleHingePackage
    arbitraryTarget :=
      TransitionRoleTargetFinalW11.arbitraryTarget_of_transitionRoleHingePackage }
  period := {
    exactTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_periodPackage
    fixedTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodPackage
    eventualTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_periodPackage
    arbitraryTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage }
  periodBlock := {
    blockIndex := TransitionFinalIntegratedW11.PeriodBlockPackage.blockIndex
    fixedBlockTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodBlockPackage }
  crossBlock := {
    exactTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_crossBlockPackage
    fixedTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_crossBlockPackage
    eventualTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_crossBlockPackage
    arbitraryTarget :=
      TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockPackage }

/-! ## Role-hinge field projections -/

/-- Role-hinge target projections retained with their explicit field inputs. -/
structure RoleProjectionLedger where
  equation : RoleTargets RoleHingeTargetFinalW11.RoleEquationRouteFields
  ledgerCandidateAssembly :
    RoleTargets RoleHingeTargetFinalW11.RoleLedgerCandidateAssemblyFields
  exactLocalRoute : RoleTargets RoleHingeTargetFinalW11.ExactLocalRouteFields
  exactLocalReducedEquations :
    forall S : RoleHingeTargetFinalW11.ExactLocalSameOppositeEquationPackage,
      RoleTargets (RoleHingeTargetFinalW11.ExactLocalTransitionRemainingFields S)
  crossBlockLowerBoundClosure :
    forall F : RoleHingeTargetFinalW11.RoleHingePeriodFamily,
      RoleTargets (RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundClosure F)
  checkedCrossBlockLowerBoundFields :
    forall F : RoleHingeTargetFinalW11.RoleHingePeriodFamily,
      RoleTargets (RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundFields F)
  rawCrossBlockInequalityLedger :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      RoleTargets (RoleHingeTargetFinalW11.RawCrossBlockInequalityLedger F)
  numericLedgerClosure :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      RoleTargets (RoleHingeTargetFinalW11.NumericLedgerClosure F)
  crossBlockClosureLedger :
    forall F : RoleHingeTargetFinalW11.LedgerPeriodFamily,
      RoleTargets (RoleHingeTargetFinalW11.CrossBlockClosureLedger F)
  roleHingeInequalityPackage :
    forall F : RoleHingeTargetFinalW11.CrossBlockRoleHingeFamily,
      RoleTargets (RoleHingeTargetFinalW11.RoleHingeCrossBlockInequalityPackage F)

/-- Checked role-hinge projections, all conditional on field/package values. -/
def roleProjectionLedger : RoleProjectionLedger where
  equation := {
    exactTarget := RoleHingeTargetFinalW11.exactTarget_of_roleEquationRouteFields
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_roleEquationRouteFields
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_roleEquationRouteFields }
  ledgerCandidateAssembly := {
    exactTarget :=
      RoleHingeTargetFinalW11.exactTarget_of_roleLedgerCandidateAssemblyFields
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_roleLedgerCandidateAssemblyFields
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_roleLedgerCandidateAssemblyFields }
  exactLocalRoute := {
    exactTarget := RoleHingeTargetFinalW11.exactTarget_of_exactLocalRouteFields
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_exactLocalRouteFields
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_exactLocalRouteFields }
  exactLocalReducedEquations := fun S => {
    exactTarget := fun R =>
      RoleHingeTargetFinalW11.exactTarget_of_exactLocalReducedEquations S R
    eventualTarget := fun R =>
      RoleHingeTargetFinalW11.eventualTarget_of_exactLocalReducedEquations S R
    arbitraryTarget := fun R =>
      RoleHingeTargetFinalW11.arbitraryTarget_of_exactLocalReducedEquations S R }
  crossBlockLowerBoundClosure := fun _F => {
    exactTarget :=
      RoleHingeTargetFinalW11.exactTarget_of_crossBlockLowerBoundClosure
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_crossBlockLowerBoundClosure
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_crossBlockLowerBoundClosure }
  checkedCrossBlockLowerBoundFields := fun _F => {
    exactTarget :=
      RoleHingeTargetFinalW11.exactTarget_of_checkedCrossBlockLowerBoundFields
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_checkedCrossBlockLowerBoundFields
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_checkedCrossBlockLowerBoundFields }
  rawCrossBlockInequalityLedger := fun _F => {
    exactTarget :=
      RoleHingeTargetFinalW11.exactTarget_of_rawCrossBlockInequalityLedger
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_rawCrossBlockInequalityLedger
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_rawCrossBlockInequalityLedger }
  numericLedgerClosure := fun _F => {
    exactTarget := RoleHingeTargetFinalW11.exactTarget_of_numericLedgerClosure
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_numericLedgerClosure
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_numericLedgerClosure }
  crossBlockClosureLedger := fun _F => {
    exactTarget := RoleHingeTargetFinalW11.exactTarget_of_crossBlockClosureLedger
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_crossBlockClosureLedger
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_crossBlockClosureLedger }
  roleHingeInequalityPackage := fun _F => {
    exactTarget :=
      RoleHingeTargetFinalW11.exactTarget_of_roleHingeInequalityPackage
    eventualTarget :=
      RoleHingeTargetFinalW11.eventualTarget_of_roleHingeInequalityPackage
    arbitraryTarget :=
      RoleHingeTargetFinalW11.arbitraryTarget_of_roleHingeInequalityPackage }

/-! ## Aggregate projections -/

/-- Pach--Toth aggregate projections that remain conditional on route data. -/
structure AggregateProjectionLedger where
  transitionRoute : ArbitraryTargets TransitionFinalIntegratedW11.RoutePackage
  transitionCandidate :
    ArbitraryTargets TransitionFinalIntegratedW11.CandidatePackage
  transitionPeriod : ArbitraryTargets TransitionFinalIntegratedW11.PeriodPackage
  transitionCrossBlock :
    ArbitraryTargets TransitionFinalIntegratedW11.CrossBlockPackage
  transitionPeriodBlock :
    FixedBlockTargets TransitionFinalIntegratedW11.PeriodBlockPackage
  generatedPointLowerBound :
    forall F : GeneratedFinalIntegratedW11.GeneratedPointFamily,
      ArbitraryTargets (GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F)
  generatedCrossBlock :
    forall F : GeneratedFinalIntegratedW11.CrossBlockFamily,
      ArbitraryTargets (GeneratedFinalIntegratedW11.CrossBlockInequalityLedger F)
  arbitraryNExactClosedChains :
    ArbitraryTargets ArbitraryNFinalIntegratedW11.ExactClosedChainPackage
  smallLengthAggregate :
    ArbitraryTargets SmallLengthFinalIntegratedW11.AggregateFields

/-- Checked Pach--Toth aggregate projections, all conditional on packages. -/
def aggregateProjectionLedger : AggregateProjectionLedger where
  transitionRoute := {
    arbitraryTarget := PachTothW11FinalAggregate.arbitraryTarget_of_transitionRoutePackage }
  transitionCandidate := {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_transitionCandidatePackage }
  transitionPeriod := {
    arbitraryTarget := PachTothW11FinalAggregate.arbitraryTarget_of_transitionPeriodPackage }
  transitionCrossBlock := {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_transitionCrossBlockPackage }
  transitionPeriodBlock := {
    blockIndex := TransitionFinalIntegratedW11.PeriodBlockPackage.blockIndex
    fixedBlockTarget :=
      PachTothW11FinalAggregate.fixedTarget_of_transitionPeriodBlockPackage }
  generatedPointLowerBound := fun _F => {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_generatedPointLowerBoundFields }
  generatedCrossBlock := fun _F => {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_generatedCrossBlockInequalityLedger }
  arbitraryNExactClosedChains := {
    arbitraryTarget := PachTothW11FinalAggregate.arbitraryTarget_of_exactClosedChains }
  smallLengthAggregate := {
    arbitraryTarget :=
      PachTothW11FinalAggregate.arbitraryTarget_of_smallLengthAggregateFiniteCertificates }

/-! ## Blocker fields -/

/-- Blocker rows retained alongside the conditional projection ledgers. -/
structure BlockerFields where
  transitionRoleTarget : TransitionRoleTargetFinalW11.BlockerLedger
  transitionRoleHinge : TransitionRoleHingeFinalW11.BlockerFields
  roleHingeTarget : RoleHingeFinalIntegratedW11.BlockerFields
  transitionFinal : TransitionFinalIntegratedW11.BlockerProjections
  pachTothAggregate : PachTothW11FinalConsistency.FinalBlockerLedger
  routeClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  completedFilteredRoute :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  sameOppositeCandidateFields :
    Not TransitionConsistencyW11.ConcreteSameOppositeCandidateFields
  missingCandidateRows :
    forall C : ExactLocalClosureW11.CandidateRows,
      Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C)
  fullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap
  endpointShortcut :
    forall E : ExactLocalFinalIntegratedW11.EndpointShortcutRow,
      Not (ExactLocalFinalIntegratedW11.PossibleRow E.u E.v)
  aggregateRouteClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  aggregateCompletedFilteredRoute :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  aggregateFullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap

/-- Checked blocker fields. -/
def blockerFields : BlockerFields where
  transitionRoleTarget := TransitionRoleTargetFinalW11.blockerLedger
  transitionRoleHinge := TransitionRoleHingeFinalW11.blockerFields
  roleHingeTarget := RoleHingeTargetFinalW11.matrix.blockers
  transitionFinal := TransitionFinalIntegratedW11.blockerProjections
  pachTothAggregate := PachTothW11FinalAggregate.matrix.blockers
  routeClaim := TransitionRoleTargetFinalW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionRoleTargetFinalW11.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    TransitionRoleTargetFinalW11.concreteFourTargetSameOppositeCandidateFields_blocked
  missingCandidateRows :=
    TransitionRoleTargetFinalW11.concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    TransitionRoleTargetFinalW11.concreteFourTargetFullSameRestShortcut_blocked
  endpointShortcut := TransitionRoleTargetFinalW11.endpointShortcut_not_possible
  aggregateRouteClaim := PachTothW11FinalAggregate.transitionConcreteRouteClaim_blocked
  aggregateCompletedFilteredRoute :=
    PachTothW11FinalAggregate.transitionCompletedFilteredRoute_blocked
  aggregateFullSameRestShortcut :=
    PachTothW11FinalAggregate.transitionFullSameRestShortcut_blocked

/-! ## Final matrix -/

/-- Final W11 transition/role ledger. -/
structure Matrix where
  packages : ExplicitPackageLedger
  imported : ImportedMatrices
  transition : TransitionProjectionLedger
  role : RoleProjectionLedger
  aggregate : AggregateProjectionLedger
  blockers : BlockerFields

/-- Checked final W11 transition/role ledger. -/
def matrix : Matrix where
  packages := explicitPackageLedger
  imported := importedMatrices
  transition := transitionProjectionLedger
  role := roleProjectionLedger
  aggregate := aggregateProjectionLedger
  blockers := blockerFields

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public transition projections -/

theorem exactTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ExactTarget :=
  matrix.transition.route.exactTarget package

theorem fixedTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) (n : Nat) :
    FixedTarget n :=
  matrix.transition.route.fixedTarget package n

theorem eventualTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    EventualTarget :=
  matrix.transition.route.eventualTarget package

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.transition.route.arbitraryTarget package

theorem arbitraryTarget_of_transitionCandidatePackage
    (package : TransitionFinalIntegratedW11.CandidatePackage) :
    ArbitraryTarget :=
  matrix.transition.candidate.arbitraryTarget package

theorem exactTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ExactTarget :=
  matrix.transition.roleHinge.exactTarget package

theorem arbitraryTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ArbitraryTarget :=
  matrix.transition.roleHinge.arbitraryTarget package

theorem arbitraryTarget_of_transitionPeriodPackage
    (package : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.transition.period.arbitraryTarget package

theorem fixedTarget_of_transitionPeriodBlockPackage
    (package : TransitionFinalIntegratedW11.PeriodBlockPackage) :
    FixedTarget (16 * matrix.transition.periodBlock.blockIndex package) :=
  matrix.transition.periodBlock.fixedBlockTarget package

theorem arbitraryTarget_of_transitionCrossBlockPackage
    (package : TransitionFinalIntegratedW11.CrossBlockPackage) :
    ArbitraryTarget :=
  matrix.transition.crossBlock.arbitraryTarget package

/-! ## Public role-hinge projections -/

theorem exactTarget_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ExactTarget :=
  matrix.role.equation.exactTarget R

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.role.equation.arbitraryTarget R

theorem exactTarget_of_roleLedgerCandidateAssemblyFields
    (R : RoleHingeTargetFinalW11.RoleLedgerCandidateAssemblyFields) :
    ExactTarget :=
  matrix.role.ledgerCandidateAssembly.exactTarget R

theorem arbitraryTarget_of_exactLocalRouteFields
    (R : RoleHingeTargetFinalW11.ExactLocalRouteFields) :
    ArbitraryTarget :=
  matrix.role.exactLocalRoute.arbitraryTarget R

theorem arbitraryTarget_of_exactLocalReducedEquations
    (S : RoleHingeTargetFinalW11.ExactLocalSameOppositeEquationPackage)
    (R : RoleHingeTargetFinalW11.ExactLocalTransitionRemainingFields S) :
    ArbitraryTarget :=
  (matrix.role.exactLocalReducedEquations S).arbitraryTarget R

theorem arbitraryTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingeTargetFinalW11.RoleHingePeriodFamily}
    (R : RoleHingeTargetFinalW11.RoleCrossBlockLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.role.checkedCrossBlockLowerBoundFields F).arbitraryTarget R

theorem arbitraryTarget_of_crossBlockClosureLedger
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (R : RoleHingeTargetFinalW11.CrossBlockClosureLedger F) :
    ArbitraryTarget :=
  (matrix.role.crossBlockClosureLedger F).arbitraryTarget R

/-! ## Public aggregate projections -/

theorem arbitraryTarget_viaAggregate_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.aggregate.transitionRoute.arbitraryTarget package

theorem arbitraryTarget_viaAggregate_of_generatedPointLowerBoundFields
    {F : GeneratedFinalIntegratedW11.GeneratedPointFamily}
    (R : GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.aggregate.generatedPointLowerBound F).arbitraryTarget R

theorem arbitraryTarget_viaAggregate_of_generatedCrossBlockInequalityLedger
    {F : GeneratedFinalIntegratedW11.CrossBlockFamily}
    (R : GeneratedFinalIntegratedW11.CrossBlockInequalityLedger F) :
    ArbitraryTarget :=
  (matrix.aggregate.generatedCrossBlock F).arbitraryTarget R

theorem arbitraryTarget_viaAggregate_of_exactClosedChains
    (P : ArbitraryNFinalIntegratedW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.aggregate.arbitraryNExactClosedChains.arbitraryTarget P

theorem arbitraryTarget_viaAggregate_of_smallLengthAggregate
    (A : SmallLengthFinalIntegratedW11.AggregateFields) :
    ArbitraryTarget :=
  matrix.aggregate.smallLengthAggregate.arbitraryTarget A

/-! ## Public blocker projections -/

theorem periodFinalIntegratedW11_absent :
    matrix.packages.pachTothAvailability.periodFinal =
      PachTothW11FinalAggregate.LedgerAvailability.absent :=
  PachTothW11FinalAggregate.periodFinalIntegratedW11_absent

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not TransitionConsistencyW11.ConcreteSameOppositeCandidateFields :=
  matrix.blockers.sameOppositeCandidateFields

theorem concreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.blockers.missingCandidateRows C

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

theorem endpointShortcut_not_possible
    (E : ExactLocalFinalIntegratedW11.EndpointShortcutRow) :
    Not (ExactLocalFinalIntegratedW11.PossibleRow E.u E.v) :=
  matrix.blockers.endpointShortcut E

theorem aggregate_concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.blockers.aggregateRouteClaim

theorem aggregate_concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.blockers.aggregateCompletedFilteredRoute

theorem aggregate_concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.aggregateFullSameRestShortcut

end

end TransitionRoleLedgerFinalW11
end PachToth
end ErdosProblems1066
