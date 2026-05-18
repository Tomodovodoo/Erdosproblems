import ErdosProblems1066.PachToth.RoleHingeIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.TransitionCheckedIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11ConsistencyMatrix
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 final role-hinge and transition aggregate

This module is the final W11 facade for the role-hinge, exact-local,
transition, and cross-block lower-bound ledgers.  It records the explicit
field packages and checked blocker rows, and exposes only package-dependent
exact, eventual, and arbitrary target projections.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeFinalIntegratedW11

noncomputable section

universe u

abbrev ConnectorEquationPackage :=
  RoleHingeIntegratedW11.ConnectorEquationPackage

abbrev ConnectorClosure :=
  RoleHingeIntegratedW11.ConnectorClosure

abbrev BranchEquationPackage :=
  RoleHingeIntegratedW11.ExactLocalEquationPackage

abbrev BranchEquationClosure :=
  RoleHingeIntegratedW11.BranchEquationClosure

abbrev SameOppositeEquationPackage :=
  RoleHingeIntegratedW11.SameOppositeExactLocalEquationPackage

abbrev SameOppositeEquationClosure :=
  RoleHingeIntegratedW11.SameOppositeEquationClosure

abbrev RoleEquationRouteFields :=
  RoleHingeIntegratedW11.EquationRouteFields

abbrev RoleLedgerCandidateAssemblyFields :=
  RoleHingeIntegratedW11.LedgerCandidateAssemblyFields

abbrev RoleHingePeriodFamily :=
  RoleHingeIntegratedW11.RoleHingedPeriodSearchFamily

abbrev RoleCrossBlockLowerBoundClosure
    (F : RoleHingePeriodFamily) :=
  RoleHingeIntegratedW11.CrossBlockLowerBoundClosure F

abbrev LedgerPeriodFamily :=
  RoleHingeIntegratedW11.LedgerRoleHingedPeriodSearchFamily

abbrev RawCrossBlockInequalityLedger
    (F : LedgerPeriodFamily) :=
  RoleHingeIntegratedW11.RawCrossBlockInequalityLedger F

abbrev NumericLedgerClosure
    (F : LedgerPeriodFamily) :=
  RoleHingeIntegratedW11.NumericLedgerClosure F

abbrev CrossBlockClosureLedger
    (F : LedgerPeriodFamily) :=
  RoleHingeIntegratedW11.CrossBlockClosureLedger F

abbrev TransitionRouteFields :=
  TransitionCheckedIntegratedW11.TransitionRouteFields

abbrev FilteredSameOpposite :=
  TransitionCheckedIntegratedW11.FilteredSameOpposite

abbrev CompletedFilteredRouteFields
    (F : FilteredSameOpposite) :=
  TransitionCheckedIntegratedW11.CompletedFilteredRouteFields F

abbrev TransitionCandidateAssemblyFields :=
  TransitionCheckedIntegratedW11.CandidateAssemblyFields

abbrev FinalConditionalFamily :=
  TransitionCheckedIntegratedW11.FinalConditionalFamily

abbrev ExactLocalRouteFields :=
  TransitionCheckedIntegratedW11.ExactLocalRouteFields

abbrev ExactLocalSameOppositeEquationPackage :=
  TransitionCheckedIntegratedW11.ExactLocalSameOppositeEquationPackage

abbrev ExactLocalTransitionRemainingFields
    (S : ExactLocalSameOppositeEquationPackage) :=
  TransitionCheckedIntegratedW11.ExactLocalTransitionRemainingFields S

abbrev RoleCrossBlockLowerBoundFields
    (F : RoleHingePeriodFamily) :=
  TransitionCheckedIntegratedW11.RoleCrossBlockLowerBoundFields F

/-! ## Shared package-dependent target rows -/

/-- Exact, eventual, and arbitrary target projections from one explicit
package shape. -/
structure TargetProjection (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

namespace TargetProjection

theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

def ofExactAndArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetProjection alpha where
  exactTarget := exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget

def ofRoleHingeRow
    {alpha : Sort u}
    (R : RoleHingeIntegratedW11.TargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofCheckedTransitionRow
    {alpha : Sort u}
    (R : TransitionCheckedIntegratedW11.CheckedTargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def ofIntegratedTransitionRow
    {alpha : Type}
    (R : TransitionIntegratedW11.ConditionalTargetRow alpha) :
    TargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end TargetProjection

/-! ## Explicit source fields -/

/-- Equation and transition package shapes used by the final aggregate. -/
structure EquationFieldLedger where
  connectorEquationPackage : Type
  connectorClosure : Type
  branchEquationPackage : Type
  branchEquationClosure : Type
  sameOppositeEquationPackage : Type
  sameOppositeEquationClosure : Type
  roleEquationRouteFields : Type
  roleLedgerCandidateAssemblyFields : Type
  transitionRouteFields : Type
  transitionCandidateAssemblyFields : Type
  finalConditionalFamily : Type

def equationFieldLedger : EquationFieldLedger where
  connectorEquationPackage := ConnectorEquationPackage
  connectorClosure := ConnectorClosure
  branchEquationPackage := BranchEquationPackage
  branchEquationClosure := BranchEquationClosure
  sameOppositeEquationPackage := SameOppositeEquationPackage
  sameOppositeEquationClosure := SameOppositeEquationClosure
  roleEquationRouteFields := RoleEquationRouteFields
  roleLedgerCandidateAssemblyFields := RoleLedgerCandidateAssemblyFields
  transitionRouteFields := TransitionRouteFields
  transitionCandidateAssemblyFields := TransitionCandidateAssemblyFields
  finalConditionalFamily := FinalConditionalFamily

/-- Exact-local package shapes and obstruction rows kept explicit. -/
structure ExactLocalFieldLedger where
  candidateRows : Type
  rowSubsetLedger : Type
  obstructionRows : ExactLocalClosureW11.ObstructionRowsLedger
  missingConcreteCandidateRows :
    ExactLocalClosureW11.CandidateRows -> Prop
  exactLocalRouteFields : Type
  reducedSameOppositeEquations : Type
  remainingFields :
    ExactLocalSameOppositeEquationPackage -> Type

def exactLocalFieldLedger : ExactLocalFieldLedger where
  candidateRows := ExactLocalClosureW11.CandidateRows
  rowSubsetLedger := ExactLocalClosureW11.CandidateRowSubsetLedger
  obstructionRows := ExactLocalClosureW11.matrix.obstructions
  missingConcreteCandidateRows :=
    ExactLocalClosureW11.ConcreteMissingCandidateRows
  exactLocalRouteFields := ExactLocalRouteFields
  reducedSameOppositeEquations := ExactLocalSameOppositeEquationPackage
  remainingFields := ExactLocalTransitionRemainingFields

/-- Cross-block lower-bound and ledger package shapes kept explicit. -/
structure CrossBlockLowerBoundFieldLedger where
  roleHingeFamilies : Type
  ledgerFamilies : Type
  lowerBoundClosures : RoleHingePeriodFamily -> Prop
  lowerBoundFields : RoleHingePeriodFamily -> Type
  rawInequalityLedgers : LedgerPeriodFamily -> Type
  numericLedgerClosures : LedgerPeriodFamily -> Type
  closureLedgers : LedgerPeriodFamily -> Type

def crossBlockLowerBoundFieldLedger :
    CrossBlockLowerBoundFieldLedger where
  roleHingeFamilies := RoleHingePeriodFamily
  ledgerFamilies := LedgerPeriodFamily
  lowerBoundClosures := RoleCrossBlockLowerBoundClosure
  lowerBoundFields := RoleCrossBlockLowerBoundFields
  rawInequalityLedgers := RawCrossBlockInequalityLedger
  numericLedgerClosures := NumericLedgerClosure
  closureLedgers := CrossBlockClosureLedger

/-! ## Imported matrices and blockers -/

/-- Checked W11 matrices imported by this final aggregate. -/
structure ImportedMatrices where
  roleHingeIntegrated : RoleHingeIntegratedW11.Matrix
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  transitionIntegrated : TransitionIntegratedW11.Matrix
  transitionChecked : TransitionCheckedIntegratedW11.Matrix
  consistency : PachTothW11ConsistencyMatrix.Matrix
  pachTothIntegrated : PachTothW11IntegratedMatrix.Matrix

def importedMatrices : ImportedMatrices where
  roleHingeIntegrated := RoleHingeIntegratedW11.matrix
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  transitionIntegrated := TransitionIntegratedW11.matrix
  transitionChecked := TransitionCheckedIntegratedW11.matrix
  consistency := PachTothW11ConsistencyMatrix.matrix
  pachTothIntegrated := PachTothW11IntegratedMatrix.matrix

/-- Named blockers carried by the transition and exact-local ledgers. -/
structure BlockerFields where
  checkedTransition : TransitionCheckedIntegratedW11.BlockerLedger
  integratedTransition : TransitionIntegratedW11.BlockerLedger
  exactLocalObstructions : ExactLocalClosureW11.ObstructionRowsLedger
  t11rNotPossible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r)
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
  fullSameRestShortcut :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap

def blockerFields : BlockerFields where
  checkedTransition := TransitionCheckedIntegratedW11.blockerLedger
  integratedTransition := TransitionIntegratedW11.blockerLedger
  exactLocalObstructions := ExactLocalClosureW11.matrix.obstructions
  t11rNotPossible :=
    TransitionCheckedIntegratedW11.concreteFourTargetT11R_not_possible
  routeClaim :=
    TransitionCheckedIntegratedW11.concreteFourTargetRouteClaim_blocked
  completedFilteredRoute :=
    TransitionCheckedIntegratedW11.concreteFourTargetCompletedFilteredRoute_blocked
  sameOppositeCandidateFields :=
    TransitionCheckedIntegratedW11.concreteFourTargetSameOppositeCandidateFields_blocked
  exactLocalMissingRows :=
    TransitionCheckedIntegratedW11.concreteMissingCandidateRows_blocked
  fullSameRestShortcut :=
    TransitionIntegratedW11.concreteFourTargetFullSameRestShortcut_blocked

/-! ## Final package-dependent routes -/

/-- Equation routes through the role-hinge and transition layers. -/
structure EquationRoutes where
  roleHingeIntegrated : TargetProjection RoleEquationRouteFields
  transitionChecked : TargetProjection RoleEquationRouteFields
  transitionIntegrated : TargetProjection RoleEquationRouteFields
  broadIntegrated : TargetProjection RoleEquationRouteFields
  ledgerCandidateAssembly :
    TargetProjection RoleLedgerCandidateAssemblyFields
  checkedLedgerCandidateAssembly :
    TargetProjection RoleLedgerCandidateAssemblyFields

def equationRoutes : EquationRoutes where
  roleHingeIntegrated :=
    TargetProjection.ofRoleHingeRow
      RoleHingeIntegratedW11.matrix.equationRouteTargets
  transitionChecked :=
    TargetProjection.ofCheckedTransitionRow
      TransitionCheckedIntegratedW11.matrix.roleEquationRouteFields
  transitionIntegrated :=
    TargetProjection.ofIntegratedTransitionRow
      TransitionIntegratedW11.matrix.roleEquationRouteFields
  broadIntegrated :=
    TargetProjection.ofExactAndArbitrary
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_roleHingeEquationRouteFields
      PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_roleHingeEquationRouteFields
  ledgerCandidateAssembly :=
    TargetProjection.ofRoleHingeRow
      RoleHingeIntegratedW11.matrix.ledgerCandidateAssemblyTargets
  checkedLedgerCandidateAssembly :=
    TargetProjection.ofCheckedTransitionRow
      TransitionCheckedIntegratedW11.matrix.roleLedgerCandidateAssemblyFields

/-- Transition routes that remain package-dependent. -/
structure TransitionRoutes where
  transitionRouteFields : TargetProjection TransitionRouteFields
  candidateAssemblyFields :
    TargetProjection TransitionCandidateAssemblyFields
  finalConditionalFamily : TargetProjection FinalConditionalFamily

def transitionRoutes : TransitionRoutes where
  transitionRouteFields :=
    TargetProjection.ofCheckedTransitionRow
      TransitionCheckedIntegratedW11.matrix.transitionRouteFields
  candidateAssemblyFields :=
    TargetProjection.ofCheckedTransitionRow
      TransitionCheckedIntegratedW11.matrix.candidateAssemblyFields
  finalConditionalFamily :=
    TargetProjection.ofCheckedTransitionRow
      TransitionCheckedIntegratedW11.matrix.finalConditionalFamily

/-- Exact-local routes from explicit reduced equations and remaining fields. -/
structure ExactLocalRoutes where
  checkedRouteFields : TargetProjection ExactLocalRouteFields
  reducedEquationRoutes :
    forall S : ExactLocalSameOppositeEquationPackage,
      TargetProjection (ExactLocalTransitionRemainingFields S)

def exactLocalReducedEquationRoutes
    (S : ExactLocalSameOppositeEquationPackage) :
    TargetProjection (ExactLocalTransitionRemainingFields S) :=
  TargetProjection.ofExactAndArbitrary
    (fun R =>
      RoleHingeIntegratedW11.targetUpperConstructionFiveSixteen_of_exactLocalEquationRoute
        S R)
    (fun R =>
      RoleHingeIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalEquationRoute
        S R)

def exactLocalRoutes : ExactLocalRoutes where
  checkedRouteFields :=
    TargetProjection.ofCheckedTransitionRow
      TransitionCheckedIntegratedW11.matrix.exactLocalRouteFields
  reducedEquationRoutes := exactLocalReducedEquationRoutes

/-- Cross-block lower-bound and ledger routes. -/
structure CrossBlockLowerBoundRoutes where
  lowerBoundClosure :
    forall F : RoleHingePeriodFamily,
      TargetProjection (RoleCrossBlockLowerBoundClosure F)
  checkedLowerBoundFields :
    forall F : RoleHingePeriodFamily,
      TargetProjection (RoleCrossBlockLowerBoundFields F)
  rawInequalityLedger :
    forall F : LedgerPeriodFamily,
      TargetProjection (RawCrossBlockInequalityLedger F)
  numericLedgerClosure :
    forall F : LedgerPeriodFamily,
      TargetProjection (NumericLedgerClosure F)
  closureLedger :
    forall F : LedgerPeriodFamily,
      TargetProjection (CrossBlockClosureLedger F)

def crossBlockLowerBoundRoutes : CrossBlockLowerBoundRoutes where
  lowerBoundClosure := fun F =>
    TargetProjection.ofRoleHingeRow
      (RoleHingeIntegratedW11.matrix.crossBlockLowerBoundTargets F)
  checkedLowerBoundFields := fun F =>
    TargetProjection.ofCheckedTransitionRow
      (TransitionCheckedIntegratedW11.matrix.roleCrossBlockLowerBoundFields F)
  rawInequalityLedger := fun F =>
    TargetProjection.ofRoleHingeRow
      (RoleHingeIntegratedW11.matrix.rawCrossBlockInequalityLedgerTargets F)
  numericLedgerClosure := fun F =>
    TargetProjection.ofRoleHingeRow
      (RoleHingeIntegratedW11.matrix.numericLedgerClosureTargets F)
  closureLedger := fun F =>
    TargetProjection.ofRoleHingeRow
      (RoleHingeIntegratedW11.matrix.crossBlockClosureLedgerTargets F)

/-! ## Final aggregate matrix -/

/-- Final W11 role-hinge/transition aggregate.

All target rows remain conditional on the explicit package fields listed in
the ledgers above. -/
structure Matrix where
  equationFields : EquationFieldLedger
  exactLocalFields : ExactLocalFieldLedger
  crossBlockLowerBoundFields : CrossBlockLowerBoundFieldLedger
  blockers : BlockerFields
  imported : ImportedMatrices
  equation : EquationRoutes
  transition : TransitionRoutes
  exactLocal : ExactLocalRoutes
  crossBlockLowerBound : CrossBlockLowerBoundRoutes

def matrix : Matrix where
  equationFields := equationFieldLedger
  exactLocalFields := exactLocalFieldLedger
  crossBlockLowerBoundFields := crossBlockLowerBoundFieldLedger
  blockers := blockerFields
  imported := importedMatrices
  equation := equationRoutes
  transition := transitionRoutes
  exactLocal := exactLocalRoutes
  crossBlockLowerBound := crossBlockLowerBoundRoutes

/-! ## Public equation projections -/

theorem exactTarget_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.equation.roleHingeIntegrated.exactTarget R

theorem eventualTarget_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.equation.roleHingeIntegrated.eventualTarget R

theorem arbitraryTarget_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.equation.roleHingeIntegrated.arbitraryTarget R

theorem exactTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.equation.transitionChecked.exactTarget R

theorem eventualTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.equation.transitionChecked.eventualTarget R

theorem arbitraryTarget_viaTransition_of_roleEquationRouteFields
    (R : RoleEquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.equation.transitionChecked.arbitraryTarget R

theorem exactTarget_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.equation.ledgerCandidateAssembly.exactTarget L

theorem eventualTarget_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.equation.ledgerCandidateAssembly.eventualTarget L

theorem arbitraryTarget_of_roleLedgerCandidateAssemblyFields
    (L : RoleLedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.equation.ledgerCandidateAssembly.arbitraryTarget L

/-! ## Public transition projections -/

theorem exactTarget_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transition.transitionRouteFields.exactTarget R

theorem eventualTarget_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transition.transitionRouteFields.eventualTarget R

theorem arbitraryTarget_of_transitionRouteFields
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transition.transitionRouteFields.arbitraryTarget R

/-! ## Public exact-local projections -/

theorem exactTarget_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.exactLocal.checkedRouteFields.exactTarget R

theorem eventualTarget_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.exactLocal.checkedRouteFields.eventualTarget R

theorem arbitraryTarget_of_exactLocalRouteFields
    (R : ExactLocalRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactLocal.checkedRouteFields.arbitraryTarget R

theorem exactTarget_of_exactLocalReducedEquations
    (S : ExactLocalSameOppositeEquationPackage)
    (R : ExactLocalTransitionRemainingFields S) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.exactLocal.reducedEquationRoutes S).exactTarget R

theorem eventualTarget_of_exactLocalReducedEquations
    (S : ExactLocalSameOppositeEquationPackage)
    (R : ExactLocalTransitionRemainingFields S) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.exactLocal.reducedEquationRoutes S).eventualTarget R

theorem arbitraryTarget_of_exactLocalReducedEquations
    (S : ExactLocalSameOppositeEquationPackage)
    (R : ExactLocalTransitionRemainingFields S) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.exactLocal.reducedEquationRoutes S).arbitraryTarget R

/-! ## Public cross-block lower-bound projections -/

theorem exactTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLowerBound.lowerBoundClosure F).exactTarget C

theorem eventualTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLowerBound.lowerBoundClosure F).eventualTarget C

theorem arbitraryTarget_of_crossBlockLowerBoundClosure
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLowerBound.lowerBoundClosure F).arbitraryTarget C

theorem exactTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLowerBound.checkedLowerBoundFields F).exactTarget C

theorem eventualTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLowerBound.checkedLowerBoundFields F).eventualTarget C

theorem arbitraryTarget_of_checkedCrossBlockLowerBoundFields
    {F : RoleHingePeriodFamily}
    (C : RoleCrossBlockLowerBoundFields F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLowerBound.checkedLowerBoundFields F).arbitraryTarget C

theorem exactTarget_of_rawCrossBlockInequalityLedger
    {F : LedgerPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLowerBound.rawInequalityLedger F).exactTarget L

theorem eventualTarget_of_rawCrossBlockInequalityLedger
    {F : LedgerPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLowerBound.rawInequalityLedger F).eventualTarget L

theorem arbitraryTarget_of_rawCrossBlockInequalityLedger
    {F : LedgerPeriodFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLowerBound.rawInequalityLedger F).arbitraryTarget L

/-! ## Public blocker projections -/

theorem concreteFourTargetT11R_not_possible :
    Not
      (ExactLocalBranchSolverSurface.PossibleRow
        FiniteGraph.LocalVertex.T1_1 FiniteGraph.LocalVertex.r) :=
  matrix.blockers.t11rNotPossible

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

theorem concreteFourTargetFullSameRestShortcut_blocked :
    Not PachTothRemainingObligationsW9.FullSameRestForConcreteFourTargetMap :=
  matrix.blockers.fullSameRestShortcut

end

end RoleHingeFinalIntegratedW11
end PachToth
end ErdosProblems1066
