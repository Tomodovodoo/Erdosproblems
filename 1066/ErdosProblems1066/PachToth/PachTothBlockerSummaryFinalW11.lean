import ErdosProblems1066.PachToth.ExactLocalTargetFinalW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.TransitionRoleHingeFinalW11
import ErdosProblems1066.PachToth.RoleHingeTargetFinalW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final blocker summary

This file is the checked W11 ledger for the concrete shortcut blockers and
the exact-local, numeric, and period data still carried as explicit fields.
Target-facing entries below are projections from a supplied package or field
value.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothBlockerSummaryFinalW11

noncomputable section

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev FixedTarget (n : Nat) : Prop :=
  PachToth.targetUpperConstructionFiveSixteenAt n

/-! ## Imported checked ledgers -/

/-- Checked W11 ledgers used by the blocker summary. -/
structure ImportedLedgers where
  exactLocalTarget : ExactLocalTargetFinalW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  transitionRoleHinge : TransitionRoleHingeFinalW11.Matrix
  roleHingeTarget : RoleHingeTargetFinalW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

/-- Imported checked W11 ledgers. -/
def importedLedgers : ImportedLedgers where
  exactLocalTarget := ExactLocalTargetFinalW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  transitionRoleHinge := TransitionRoleHingeFinalW11.matrix
  roleHingeTarget := RoleHingeTargetFinalW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Concrete shortcut blockers -/

/-- Final checked facts blocking the concrete shortcut rows. -/
structure ConcreteShortcutBlockerLedger where
  transitionFinal : TransitionFinalIntegratedW11.BlockerProjections
  transitionRoleHinge : TransitionRoleHingeFinalW11.BlockerFields
  exactLocalEndpoint : ExactLocalTargetFinalW11.EndpointBlockerFields
  t11rNotPossible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r)
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
    forall E : ExactLocalTargetFinalW11.EndpointShortcutRow,
      Not (ExactLocalTargetFinalW11.PossibleRow E.u E.v)
  pUpperForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_1)
  pUpperReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.T2_2)
  pLowerForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_2)
  pLowerReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T1_2 FiniteGraph.LocalVertex.T2_2)
  qUpperForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_0)
  qUpperReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_0 FiniteGraph.LocalVertex.T4_0)
  qLowerForward :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_2)
  qLowerReverse :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_2 FiniteGraph.LocalVertex.T4_0)

/-- Checked concrete shortcut blockers. -/
def concreteShortcutBlockers : ConcreteShortcutBlockerLedger where
  transitionFinal := TransitionFinalIntegratedW11.blockerProjections
  transitionRoleHinge := TransitionRoleHingeFinalW11.blockerFields
  exactLocalEndpoint := ExactLocalTargetFinalW11.endpointBlockerFields
  t11rNotPossible :=
    RoleHingeTargetFinalW11.concreteFourTargetT11R_not_possible
  routeClaim :=
    TransitionRoleHingeFinalW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionRoleHingeFinalW11.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    TransitionRoleHingeFinalW11.concreteFourTargetSameOppositeCandidateFields_blocked
  missingCandidateRows :=
    TransitionRoleHingeFinalW11.concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    TransitionRoleHingeFinalW11.concreteFourTargetFullSameRestShortcut_blocked
  endpointShortcut :=
    ExactLocalTargetFinalW11.endpointShortcut_not_possible
  pUpperForward :=
    ExactLocalTargetFinalW11.pUpperForward_endpointShortcut_not_possible
  pUpperReverse :=
    ExactLocalTargetFinalW11.pUpperReverse_endpointShortcut_not_possible
  pLowerForward :=
    ExactLocalTargetFinalW11.pLowerForward_endpointShortcut_not_possible
  pLowerReverse :=
    ExactLocalTargetFinalW11.pLowerReverse_endpointShortcut_not_possible
  qUpperForward :=
    ExactLocalTargetFinalW11.qUpperForward_endpointShortcut_not_possible
  qUpperReverse :=
    ExactLocalTargetFinalW11.qUpperReverse_endpointShortcut_not_possible
  qLowerForward :=
    ExactLocalTargetFinalW11.qLowerForward_endpointShortcut_not_possible
  qLowerReverse :=
    ExactLocalTargetFinalW11.qLowerReverse_endpointShortcut_not_possible

/-! ## Missing-data ledgers -/

/-- Exact-local row data still represented by explicit fields. -/
structure ExactLocalMissingDataLedger where
  targetFields : ExactLocalTargetFinalW11.ExplicitFieldLedger
  roleHingeFields : RoleHingeFinalIntegratedW11.ExactLocalFieldLedger
  finalSources : ExactLocalFinalIntegratedW11.FinalSourceLedger
  missingRows : ExactLocalClosureW11.CandidateRows -> Prop
  missingRowsBlocked :
    forall C : ExactLocalClosureW11.CandidateRows,
      Not (missingRows C)
  targetMissingRowsBlocked :
    forall F : ExactLocalTargetFinalW11.CandidateRowSubsetFields,
      Not
        (ExactLocalTargetFinalW11.MissingViableCandidateRows
          F.rows.candidateRows)
  packageMissingRowsBlocked :
    forall P : ExactLocalTargetFinalW11.FinalExactLocalPackage,
      Not
        (ExactLocalTargetFinalW11.MissingViableCandidateRows
          P.subset.rows.candidateRows)

/-- Checked exact-local missing-data ledger. -/
def exactLocalMissingDataLedger : ExactLocalMissingDataLedger where
  targetFields := ExactLocalTargetFinalW11.explicitFieldLedger
  roleHingeFields := RoleHingeFinalIntegratedW11.exactLocalFieldLedger
  finalSources := ExactLocalFinalIntegratedW11.finalSourceLedger
  missingRows := ExactLocalClosureW11.ConcreteMissingCandidateRows
  missingRowsBlocked :=
    TransitionRoleHingeFinalW11.concreteMissingCandidateRows_blocked
  targetMissingRowsBlocked :=
    ExactLocalTargetFinalW11.missingViableCandidateRows_blocked
  packageMissingRowsBlocked :=
    ExactLocalTargetFinalW11.package_missingRowsBlocked

/-- Numeric lower-bound and cross-block data kept as explicit ledgers. -/
structure NumericMissingDataLedger where
  roleHingeCrossBlockFields :
    RoleHingeFinalIntegratedW11.CrossBlockLowerBoundFieldLedger
  generatedInputs : GeneratedTargetFinalW11.ExplicitInputLedgers
  generatedNumericCertificates :
    GeneratedTargetFinalW11.NumericCertificateLedger
  finalOpenInputs : PachTothW11FinalConsistency.OpenInputLedgers
  numericLedgerClosureArbitrary :
    forall {F : RoleHingeTargetFinalW11.LedgerPeriodFamily},
      RoleHingeTargetFinalW11.NumericLedgerClosure F ->
        ArbitraryTarget
  crossBlockClosureArbitrary :
    forall {F : RoleHingeTargetFinalW11.LedgerPeriodFamily},
      RoleHingeTargetFinalW11.CrossBlockClosureLedger F ->
        ArbitraryTarget
  generatedLowerBoundArbitrary :
    forall {F : GeneratedTargetIntegratedW11.RoleHingedPeriodSearchFamily},
      GeneratedTargetIntegratedW11.LowerBoundFields F ->
        ArbitraryTarget

/-- Checked numeric missing-data ledger. -/
def numericMissingDataLedger : NumericMissingDataLedger where
  roleHingeCrossBlockFields :=
    RoleHingeFinalIntegratedW11.crossBlockLowerBoundFieldLedger
  generatedInputs := GeneratedTargetFinalW11.explicitInputLedgers
  generatedNumericCertificates :=
    GeneratedTargetFinalW11.numericCertificateLedger
  finalOpenInputs := PachTothW11FinalConsistency.openInputLedgers
  numericLedgerClosureArbitrary := fun C =>
    RoleHingeTargetFinalW11.arbitraryTarget_of_numericLedgerClosure C
  crossBlockClosureArbitrary := fun C =>
    RoleHingeTargetFinalW11.arbitraryTarget_of_crossBlockClosureLedger C
  generatedLowerBoundArbitrary := fun C =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_generatedPointLowerBoundFields
      C

/-- Period data retained as candidate-indexed package fields. -/
structure PeriodMissingDataLedger where
  transitionPackages : Type
  transitionBlockPackages : Type
  periodPackages : PeriodIntegratedW11.SourcePackageLedger
  periodRoutes : PeriodIntegratedW11.Matrix
  periodExactCandidateConsistency :
    forall {T : PeriodEquationSearchW11.Candidate}
      (D : PeriodEquationSearchW11.ExactCandidatePeriodFields T),
      PachTothW11ConsistencyMatrix.PeriodExactCandidateConsistency T D
  roleHingePeriodRouteConsistency :
    forall R : RoleHingeClosureW11.EquationRouteFields,
      PachTothW11ConsistencyMatrix.RoleHingePeriodRouteConsistency R
  transitionPeriodArbitrary :
    TransitionFinalIntegratedW11.PeriodPackage -> ArbitraryTarget
  transitionPeriodBlockTarget :
    forall package : TransitionFinalIntegratedW11.PeriodBlockPackage,
      FixedTarget
        (16 *
          TransitionFinalIntegratedW11.matrix.periodBlockTargets.blockIndex
            package)
  periodExactCandidateArbitrary :
    forall {T : PeriodIntegratedW11.Candidate},
      PeriodIntegratedW11.ExactCandidatePeriodFields T ->
        ArbitraryTarget

/-- Checked period missing-data ledger. -/
def periodMissingDataLedger : PeriodMissingDataLedger where
  transitionPackages := TransitionFinalIntegratedW11.PeriodPackage
  transitionBlockPackages := TransitionFinalIntegratedW11.PeriodBlockPackage
  periodPackages := PeriodIntegratedW11.sourcePackageLedger
  periodRoutes := PeriodIntegratedW11.matrix
  periodExactCandidateConsistency := fun D =>
    PachTothW11FinalConsistency.matrix.consistency.periodExactCandidate D
  roleHingePeriodRouteConsistency :=
    PachTothW11FinalConsistency.matrix.consistency.roleHingePeriodRoute
  transitionPeriodArbitrary :=
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
  transitionPeriodBlockTarget :=
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenAt_of_periodBlockPackage
  periodExactCandidateArbitrary := fun D =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_periodExactCandidateFields
      D

/-! ## Conditional target projections -/

/-- Target-facing projections, each requiring an explicit source value. -/
structure ConditionalTargetProjectionLedger where
  exactLocalFinalPackageExact :
    ExactLocalTargetFinalW11.FinalExactLocalPackage -> ExactTarget
  exactLocalFinalPackageArbitrary :
    ExactLocalTargetFinalW11.FinalExactLocalPackage -> ArbitraryTarget
  transitionRoutePackageArbitrary :
    TransitionFinalIntegratedW11.RoutePackage -> ArbitraryTarget
  transitionPeriodPackageArbitrary :
    TransitionFinalIntegratedW11.PeriodPackage -> ArbitraryTarget
  roleEquationRouteFieldsArbitrary :
    RoleHingeTargetFinalW11.RoleEquationRouteFields -> ArbitraryTarget
  exactLocalRouteFieldsArbitrary :
    RoleHingeTargetFinalW11.ExactLocalRouteFields -> ArbitraryTarget
  numericLedgerClosureArbitrary :
    forall {F : RoleHingeTargetFinalW11.LedgerPeriodFamily},
      RoleHingeTargetFinalW11.NumericLedgerClosure F ->
        ArbitraryTarget
  periodExactCandidateArbitrary :
    forall {T : PeriodIntegratedW11.Candidate},
      PeriodIntegratedW11.ExactCandidatePeriodFields T ->
        ArbitraryTarget

/-- Checked conditional target projection ledger. -/
def conditionalTargetProjectionLedger :
    ConditionalTargetProjectionLedger where
  exactLocalFinalPackageExact :=
    ExactLocalTargetFinalW11.exactTarget_of_finalExactLocalPackage
  exactLocalFinalPackageArbitrary :=
    ExactLocalTargetFinalW11.arbitraryTarget_of_finalExactLocalPackage
  transitionRoutePackageArbitrary :=
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
  transitionPeriodPackageArbitrary :=
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_periodPackage
  roleEquationRouteFieldsArbitrary :=
    RoleHingeTargetFinalW11.arbitraryTarget_of_roleEquationRouteFields
  exactLocalRouteFieldsArbitrary :=
    RoleHingeTargetFinalW11.arbitraryTarget_of_exactLocalRouteFields
  numericLedgerClosureArbitrary := fun C =>
    RoleHingeTargetFinalW11.arbitraryTarget_of_numericLedgerClosure C
  periodExactCandidateArbitrary := fun D =>
    PachTothW11FinalConsistency.targetUpperConstructionFiveSixteenArbitrary_of_periodExactCandidateFields
      D

/-! ## Final matrix -/

/-- Final checked blocker-summary matrix. -/
structure Matrix where
  imports : ImportedLedgers
  shortcuts : ConcreteShortcutBlockerLedger
  exactLocal : ExactLocalMissingDataLedger
  numeric : NumericMissingDataLedger
  period : PeriodMissingDataLedger
  targets : ConditionalTargetProjectionLedger

/-- The final checked W11 blocker-summary ledger. -/
def matrix : Matrix where
  imports := importedLedgers
  shortcuts := concreteShortcutBlockers
  exactLocal := exactLocalMissingDataLedger
  numeric := numericMissingDataLedger
  period := periodMissingDataLedger
  targets := conditionalTargetProjectionLedger

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public blocker facts -/

theorem concreteFourTargetT11R_not_possible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r) :=
  matrix.shortcuts.t11rNotPossible

theorem concreteFourTargetRouteClaim_blocked :
    FlexibleTransitionSearchW11.ConcreteFourTargetRouteClaim -> False :=
  matrix.shortcuts.routeClaim

theorem concreteFourTargetCompletedFilteredRoute_blocked :
    TransitionFinalIntegratedW11.CheckedCompletedFilteredRouteFields
        FlexibleTransitionSearchW10.concreteFourTargetFilteredSameOpposite ->
      False :=
  matrix.shortcuts.completedFilteredRoute

theorem concreteFourTargetSameOppositeCandidateFields_blocked :
    Not TransitionConsistencyW11.ConcreteSameOppositeCandidateFields :=
  matrix.shortcuts.sameOppositeCandidateFields

theorem concreteMissingCandidateRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  matrix.shortcuts.missingCandidateRows C

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.shortcuts.fullSameRestShortcut

theorem endpointShortcut_not_possible
    (E : ExactLocalTargetFinalW11.EndpointShortcutRow) :
    Not (ExactLocalTargetFinalW11.PossibleRow E.u E.v) :=
  matrix.shortcuts.endpointShortcut E

theorem pUpperForward_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_1) :=
  matrix.shortcuts.pUpperForward

theorem pUpperReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.T2_2) :=
  matrix.shortcuts.pUpperReverse

theorem pLowerForward_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T2_2 FiniteGraph.LocalVertex.T1_2) :=
  matrix.shortcuts.pLowerForward

theorem pLowerReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T1_2 FiniteGraph.LocalVertex.T2_2) :=
  matrix.shortcuts.pLowerReverse

theorem qUpperForward_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_0) :=
  matrix.shortcuts.qUpperForward

theorem qUpperReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_0 FiniteGraph.LocalVertex.T4_0) :=
  matrix.shortcuts.qUpperReverse

theorem qLowerForward_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T4_0 FiniteGraph.LocalVertex.T0_2) :=
  matrix.shortcuts.qLowerForward

theorem qLowerReverse_endpointShortcut_not_possible :
    Not
      (ExactLocalTargetFinalW11.PossibleRow
        FiniteGraph.LocalVertex.T0_2 FiniteGraph.LocalVertex.T4_0) :=
  matrix.shortcuts.qLowerReverse

/-! ## Public missing-data and conditional target facts -/

theorem missingViableCandidateRows_blocked
    (F : ExactLocalTargetFinalW11.CandidateRowSubsetFields) :
    Not
      (ExactLocalTargetFinalW11.MissingViableCandidateRows
        F.rows.candidateRows) :=
  matrix.exactLocal.targetMissingRowsBlocked F

theorem package_missingRowsBlocked
    (P : ExactLocalTargetFinalW11.FinalExactLocalPackage) :
    Not
      (ExactLocalTargetFinalW11.MissingViableCandidateRows
        P.subset.rows.candidateRows) :=
  matrix.exactLocal.packageMissingRowsBlocked P

theorem exactTarget_of_finalExactLocalPackage
    (P : ExactLocalTargetFinalW11.FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.exactLocalFinalPackageExact P

theorem arbitraryTarget_of_finalExactLocalPackage
    (P : ExactLocalTargetFinalW11.FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.exactLocalFinalPackageArbitrary P

theorem arbitraryTarget_of_routePackage
    (P : TransitionFinalIntegratedW11.RoutePackage) :
    ArbitraryTarget :=
  matrix.targets.transitionRoutePackageArbitrary P

theorem arbitraryTarget_of_periodPackage
    (P : TransitionFinalIntegratedW11.PeriodPackage) :
    ArbitraryTarget :=
  matrix.targets.transitionPeriodPackageArbitrary P

theorem targetUpperConstructionFiveSixteenAt_of_periodBlockPackage
    (P : TransitionFinalIntegratedW11.PeriodBlockPackage) :
    FixedTarget
      (16 *
        TransitionFinalIntegratedW11.matrix.periodBlockTargets.blockIndex P) :=
  matrix.period.transitionPeriodBlockTarget P

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleHingeTargetFinalW11.RoleEquationRouteFields) :
    ArbitraryTarget :=
  matrix.targets.roleEquationRouteFieldsArbitrary R

theorem arbitraryTarget_of_exactLocalRouteFields
    (R : RoleHingeTargetFinalW11.ExactLocalRouteFields) :
    ArbitraryTarget :=
  matrix.targets.exactLocalRouteFieldsArbitrary R

theorem arbitraryTarget_of_numericLedgerClosure
    {F : RoleHingeTargetFinalW11.LedgerPeriodFamily}
    (C : RoleHingeTargetFinalW11.NumericLedgerClosure F) :
    ArbitraryTarget :=
  matrix.targets.numericLedgerClosureArbitrary C

theorem arbitraryTarget_of_periodExactCandidateFields
    {T : PeriodIntegratedW11.Candidate}
    (D : PeriodIntegratedW11.ExactCandidatePeriodFields T) :
    ArbitraryTarget :=
  matrix.targets.periodExactCandidateArbitrary D

end

end PachTothBlockerSummaryFinalW11
end PachToth
end ErdosProblems1066
