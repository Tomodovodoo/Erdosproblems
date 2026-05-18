import ErdosProblems1066.PachToth.TransitionRoleHingeFinalW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeFinalIntegratedW11
import ErdosProblems1066.PachToth.ExactLocalFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalAggregate

set_option autoImplicit false

/-!
# W11 final transition, role, and exact-local target layer

This file is a final consistency facade over the transition, role-hinge,
exact-local, and Pach--Toth aggregate ledgers.  It records the checked source
matrices, the blocker rows, and the package-indexed target projections.

The target facts below always keep an explicit package or field input.
-/

namespace ErdosProblems1066
namespace PachToth
namespace TransitionRoleTargetFinalW11

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

/-! ## Shared package-indexed projection shapes -/

/-- Exact, fixed, eventual, and arbitrary target projections from one input
shape. -/
structure ConditionalTargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  fixedTarget : alpha -> forall n : Nat, FixedTarget n
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Arbitrary target projection from one input shape. -/
structure ConditionalArbitraryProjection (alpha : Sort u) :
    Sort (max 1 u) where
  arbitraryTarget : alpha -> ArbitraryTarget

/-- Fixed block projection whose block index is part of the input row. -/
structure ConditionalFixedBlockProjection (alpha : Sort u) :
    Sort (max 1 u) where
  blockIndex : alpha -> Nat
  fixedBlockTarget : forall a : alpha, FixedTarget (16 * blockIndex a)

def projectionOfTransitionRoleHinge
    {alpha : Sort u}
    (R : TransitionRoleHingeFinalW11.TargetProjection alpha) :
    ConditionalTargetProjection alpha where
  exactTarget := R.exactTarget
  fixedTarget := R.fixedTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

/-! ## Imported ledgers -/

/-- Checked final matrices used by this terminal layer. -/
structure ImportedFinalLedgers where
  transitionRoleHinge : TransitionRoleHingeFinalW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  roleHingeFinal : RoleHingeFinalIntegratedW11.Matrix
  exactLocalFinal : ExactLocalFinalIntegratedW11.Matrix
  pachTothAggregate : PachTothW11FinalAggregate.Matrix

def importedFinalLedgers : ImportedFinalLedgers where
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  roleHingeFinal := RoleHingeFinalIntegratedW11.matrix
  exactLocalFinal := ExactLocalFinalIntegratedW11.matrix
  pachTothAggregate := PachTothW11FinalAggregate.matrix

/-- Source and open-data ledgers retained as explicit fields. -/
structure SourceLedger where
  transitionPackages : TransitionFinalIntegratedW11.ExplicitPackageLedger
  roleHingeEquationFields : RoleHingeFinalIntegratedW11.EquationFieldLedger
  roleHingeExactLocalFields : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger
  exactLocalSources : ExactLocalFinalIntegratedW11.FinalSourceLedger
  pachTothOpenData : PachTothW11FinalAggregate.ExplicitOpenData
  pachTothAvailability : PachTothW11FinalAggregate.FinalLedgerAvailability

def sourceLedger : SourceLedger where
  transitionPackages := TransitionFinalIntegratedW11.explicitPackageLedger
  roleHingeEquationFields :=
    RoleHingeFinalIntegratedW11.equationFieldLedger
  roleHingeExactLocalFields :=
    RoleHingeFinalIntegratedW11.exactLocalFieldLedger
  exactLocalSources := ExactLocalFinalIntegratedW11.finalSourceLedger
  pachTothOpenData := PachTothW11FinalAggregate.explicitOpenData
  pachTothAvailability := PachTothW11FinalAggregate.finalLedgerAvailability

/-! ## Target consistency routes -/

/-- Transition, role-hinge, and exact-local projections that agree on the
same target predicates. -/
structure TransitionRoleExactProjections where
  transitionRoute :
    ConditionalTargetProjection TransitionFinalIntegratedW11.RoutePackage
  transitionRoleHinge :
    ConditionalTargetProjection TransitionFinalIntegratedW11.RoleHingePackage
  roleEquation :
    ConditionalTargetProjection RoleHingeFinalIntegratedW11.RoleEquationRouteFields
  roleLedgerCandidateAssembly :
    ConditionalTargetProjection
      RoleHingeFinalIntegratedW11.RoleLedgerCandidateAssemblyFields
  roleTransition :
    ConditionalTargetProjection RoleHingeFinalIntegratedW11.TransitionRouteFields
  exactLocal :
    ConditionalTargetProjection ExactLocalFinalIntegratedW11.FinalExactLocalPackage

def transitionRoleExactProjections : TransitionRoleExactProjections where
  transitionRoute :=
    projectionOfTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.transitionFinalRoute
  transitionRoleHinge :=
    projectionOfTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.transitionFinalRoleHinge
  roleEquation :=
    projectionOfTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.roleHingeEquationRoute
  roleLedgerCandidateAssembly :=
    projectionOfTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.roleHingeLedgerCandidateAssembly
  roleTransition :=
    projectionOfTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.roleHingeTransitionRoute
  exactLocal :=
    projectionOfTransitionRoleHinge
      TransitionRoleHingeFinalW11.matrix.projections.exactLocalFinalPackage

/-- Pach--Toth aggregate projections that remain conditional on explicit
route data. -/
structure PachTothAggregateProjections where
  transitionRoute :
    ConditionalArbitraryProjection TransitionFinalIntegratedW11.RoutePackage
  transitionCandidate :
    ConditionalArbitraryProjection TransitionFinalIntegratedW11.CandidatePackage
  transitionPeriod :
    ConditionalArbitraryProjection TransitionFinalIntegratedW11.PeriodPackage
  transitionCrossBlock :
    ConditionalArbitraryProjection TransitionFinalIntegratedW11.CrossBlockPackage
  transitionPeriodBlock :
    ConditionalFixedBlockProjection TransitionFinalIntegratedW11.PeriodBlockPackage
  generatedPointLowerBound :
    forall F : GeneratedFinalIntegratedW11.GeneratedPointFamily,
      ConditionalArbitraryProjection
        (GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F)
  generatedCrossBlock :
    forall F : GeneratedFinalIntegratedW11.CrossBlockFamily,
      ConditionalArbitraryProjection
        (GeneratedFinalIntegratedW11.CrossBlockInequalityLedger F)
  arbitraryNExactClosedChains :
    ConditionalArbitraryProjection
      ArbitraryNFinalIntegratedW11.ExactClosedChainPackage
  smallLengthAggregate :
    ConditionalArbitraryProjection SmallLengthFinalIntegratedW11.AggregateFields

def pachTothAggregateProjections : PachTothAggregateProjections where
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

/-! ## Cross-layer consistency witnesses -/

/-- Checked agreement witnesses retained from the imported consistency
matrices. -/
structure TargetConsistencyLedger where
  transitionRoute :
    forall R : TransitionConsistencyW11.TransitionRouteFields,
      TransitionConsistencyW11.TransitionRouteConsistency R
  roleEquation :
    forall R : TransitionConsistencyW11.RoleEquationRouteFields,
      TransitionConsistencyW11.RoleEquationRouteConsistency R
  exactLocal :
    forall P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage,
      PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
        P.equations P.remaining
  roleHingePeriod :
    forall R : RoleHingeClosureW11.EquationRouteFields,
      PachTothW11ConsistencyMatrix.RoleHingePeriodRouteConsistency R
  periodFinalStatus :
    PachTothW11FinalAggregate.finalLedgerAvailability.periodFinal =
      PachTothW11FinalAggregate.LedgerAvailability.absent

def targetConsistencyLedger : TargetConsistencyLedger where
  transitionRoute := TransitionRoleHingeFinalW11.matrix.consistency.transitionRoute
  roleEquation := TransitionRoleHingeFinalW11.matrix.consistency.roleEquationRoute
  exactLocal := TransitionRoleHingeFinalW11.matrix.consistency.exactLocalRoute
  roleHingePeriod :=
    TransitionRoleHingeFinalW11.matrix.consistency.roleHingePeriodRoute
  periodFinalStatus := PachTothW11FinalAggregate.periodFinalIntegratedW11_absent

/-! ## Blockers -/

/-- Blocker rows that keep shortcut routes separate from the conditional
target projections. -/
structure BlockerLedger where
  transitionRoleHinge : TransitionRoleHingeFinalW11.BlockerFields
  transitionFinal : TransitionFinalIntegratedW11.BlockerProjections
  roleHingeFinal : RoleHingeFinalIntegratedW11.BlockerFields
  exactLocalFinal : ExactLocalFinalIntegratedW11.FinalEndpointBlockerLedger
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
  aggregateTransitionRouteClaim :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False
  aggregateCompletedFilteredRoute :
    TransitionIntegratedW11.CompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False
  aggregateFullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap

def blockerLedger : BlockerLedger where
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix.blockers
  transitionFinal := TransitionFinalIntegratedW11.blockerProjections
  roleHingeFinal := RoleHingeFinalIntegratedW11.blockerFields
  exactLocalFinal := ExactLocalFinalIntegratedW11.finalEndpointBlockerLedger
  pachTothAggregate := PachTothW11FinalAggregate.matrix.blockers
  routeClaim := TransitionRoleHingeFinalW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionRoleHingeFinalW11.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    TransitionRoleHingeFinalW11.concreteFourTargetSameOppositeCandidateFields_blocked
  missingCandidateRows :=
    TransitionRoleHingeFinalW11.concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    TransitionRoleHingeFinalW11.concreteFourTargetFullSameRestShortcut_blocked
  endpointShortcut := TransitionRoleHingeFinalW11.endpointShortcut_not_possible
  aggregateTransitionRouteClaim :=
    PachTothW11FinalAggregate.transitionConcreteRouteClaim_blocked
  aggregateCompletedFilteredRoute :=
    PachTothW11FinalAggregate.transitionCompletedFilteredRoute_blocked
  aggregateFullSameRestShortcut :=
    PachTothW11FinalAggregate.transitionFullSameRestShortcut_blocked

/-! ## Final matrix -/

/-- Final W11 transition/role/exact-local target consistency layer. -/
structure Matrix where
  imported : ImportedFinalLedgers
  sources : SourceLedger
  transitionRoleExact : TransitionRoleExactProjections
  pachTothAggregate : PachTothAggregateProjections
  consistency : TargetConsistencyLedger
  blockers : BlockerLedger

def matrix : Matrix where
  imported := importedFinalLedgers
  sources := sourceLedger
  transitionRoleExact := transitionRoleExactProjections
  pachTothAggregate := pachTothAggregateProjections
  consistency := targetConsistencyLedger
  blockers := blockerLedger

/-! ## Public transition, role-hinge, and exact-local projections -/

theorem exactTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ExactTarget :=
  matrix.transitionRoleExact.transitionRoute.exactTarget package

theorem fixedTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) (n : Nat) :
    FixedTarget n :=
  matrix.transitionRoleExact.transitionRoute.fixedTarget package n

theorem eventualTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    EventualTarget :=
  matrix.transitionRoleExact.transitionRoute.eventualTarget package

theorem arbitraryTarget_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.transitionRoleExact.transitionRoute.arbitraryTarget package

theorem exactTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ExactTarget :=
  matrix.transitionRoleExact.transitionRoleHinge.exactTarget package

theorem arbitraryTarget_of_transitionRoleHingePackage
    (package : TransitionFinalIntegratedW11.RoleHingePackage) :
    ArbitraryTarget :=
  matrix.transitionRoleExact.transitionRoleHinge.arbitraryTarget package

theorem exactTarget_of_roleEquationRouteFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    ExactTarget :=
  matrix.transitionRoleExact.roleEquation.exactTarget R

theorem eventualTarget_of_roleEquationRouteFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    EventualTarget :=
  matrix.transitionRoleExact.roleEquation.eventualTarget R

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleHingeFinalIntegratedW11.RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.transitionRoleExact.roleEquation.arbitraryTarget R

theorem exactTarget_of_exactLocalFinalPackage
    (P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    ExactTarget :=
  matrix.transitionRoleExact.exactLocal.exactTarget P

theorem eventualTarget_of_exactLocalFinalPackage
    (P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    EventualTarget :=
  matrix.transitionRoleExact.exactLocal.eventualTarget P

theorem arbitraryTarget_of_exactLocalFinalPackage
    (P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.transitionRoleExact.exactLocal.arbitraryTarget P

/-! ## Public aggregate projections -/

theorem arbitraryTarget_viaAggregate_of_transitionRoutePackage
    (package : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.pachTothAggregate.transitionRoute.arbitraryTarget package

theorem arbitraryTarget_viaAggregate_of_transitionCandidatePackage
    (package : TransitionFinalIntegratedW11.CandidatePackage) :
    ArbitraryTarget :=
  matrix.pachTothAggregate.transitionCandidate.arbitraryTarget package

theorem fixedTarget_viaAggregate_of_transitionPeriodBlockPackage
    (package : TransitionFinalIntegratedW11.PeriodBlockPackage) :
    FixedTarget
      (16 * matrix.pachTothAggregate.transitionPeriodBlock.blockIndex package) :=
  matrix.pachTothAggregate.transitionPeriodBlock.fixedBlockTarget package

theorem arbitraryTarget_viaAggregate_of_generatedPointLowerBoundFields
    {F : GeneratedFinalIntegratedW11.GeneratedPointFamily}
    (C : GeneratedFinalIntegratedW11.GeneratedPointLowerBoundFields F) :
    ArbitraryTarget :=
  (matrix.pachTothAggregate.generatedPointLowerBound F).arbitraryTarget C

theorem arbitraryTarget_viaAggregate_of_arbitraryNExactClosedChains
    (P : ArbitraryNFinalIntegratedW11.ExactClosedChainPackage) :
    ArbitraryTarget :=
  matrix.pachTothAggregate.arbitraryNExactClosedChains.arbitraryTarget P

theorem arbitraryTarget_viaAggregate_of_smallLengthAggregate
    (A : SmallLengthFinalIntegratedW11.AggregateFields) :
    ArbitraryTarget :=
  matrix.pachTothAggregate.smallLengthAggregate.arbitraryTarget A

/-! ## Public consistency and blocker projections -/

def transitionRouteConsistency
    (R : TransitionConsistencyW11.TransitionRouteFields) :
    TransitionConsistencyW11.TransitionRouteConsistency R :=
  matrix.consistency.transitionRoute R

def roleEquationRouteConsistency
    (R : TransitionConsistencyW11.RoleEquationRouteFields) :
    TransitionConsistencyW11.RoleEquationRouteConsistency R :=
  matrix.consistency.roleEquation R

def exactLocalRouteConsistency
    (P : ExactLocalFinalIntegratedW11.FinalExactLocalPackage) :
    PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
      P.equations P.remaining :=
  matrix.consistency.exactLocal P

theorem periodFinalIntegratedW11_absent :
    matrix.sources.pachTothAvailability.periodFinal =
      PachTothW11FinalAggregate.LedgerAvailability.absent :=
  matrix.consistency.periodFinalStatus

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

end

end TransitionRoleTargetFinalW11
end PachToth
end ErdosProblems1066
