import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.ExactLocalObstructionMatrixW11
import ErdosProblems1066.PachToth.FlexibleTransitionClosureW11
import ErdosProblems1066.PachToth.RoleHingeClosureW11

set_option autoImplicit false

/-!
# W11 exact-local integrated matrix

This module routes the W11 exact-local row ledger through the transition and
role-hinge target facades.  The route package keeps the candidate-row subset,
the obstruction ledger, endpoint shortcut blockers, and the missing concrete
candidate-row completion visible next to the reduced same/opposite equations.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalIntegratedW11

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

universe u

abbrev R2 := Prod Real Real

abbrev CandidateRows :=
  ExactLocalClosureW11.CandidateRows

abbrev CandidateRowSubsetLedger :=
  ExactLocalClosureW11.CandidateRowSubsetLedger

abbrev ObstructionRowsLedger :=
  ExactLocalClosureW11.ObstructionRowsLedger

abbrev ConcreteEndpointShortcutLedger :=
  ExactLocalClosureW11.ConcreteEndpointShortcutLedger

abbrev EndpointShortcutRow :=
  ExactLocalClosureW11.EndpointShortcutRow

abbrev ConcreteMissingCandidateRows :=
  ExactLocalClosureW11.ConcreteMissingCandidateRows

abbrev MissingViableCandidateRows :=
  ConcreteMissingCandidateRows

abbrev PossibleRow :=
  ExactLocalObstructionMatrixW11.PossibleRow

abbrev W10PossibleRow :=
  ExactLocalObstructionMatrixW11.W10PossibleRow

abbrev PreservesRows :=
  ExactLocalObstructionMatrixW11.PreservesRows

abbrev ExactLocalEquationPackage :=
  ExactLocalClosureW11.ExactLocalEquationPackage

abbrev SameOppositeExactLocalEquationPackage :=
  ExactLocalClosureW11.SameOppositeExactLocalEquationPackage

abbrev SameOppositeCandidate :=
  ExactLocalClosureW11.SameOppositeCandidate

abbrev TransitionRemainingFields
    (T : SameOppositeCandidate) :=
  ExactLocalClosureW11.TransitionRemainingFields T

abbrev TransitionRouteFields :=
  FlexibleTransitionClosureW11.TransitionRouteFields

abbrev RoleEquationRouteFields :=
  RoleHingeClosureW11.EquationRouteFields

/-- Missing concrete row completions remain an explicit blocked field. -/
structure MissingViableRowsLedger where
  missingRows : CandidateRows -> Prop
  blocked : forall C : CandidateRows, Not (missingRows C)

def missingViableRowsLedger : MissingViableRowsLedger where
  missingRows := MissingViableCandidateRows
  blocked := ExactLocalClosureW11.noConcreteMissingCandidateRows

/-! ## Exact-local subset route package -/

/-- A candidate-row subset routed through reduced same/opposite equations and
the W11 remaining transition fields. -/
structure CandidateSubsetRouteFields where
  rows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  endpointShortcuts : ConcreteEndpointShortcutLedger
  missingViableRowsBlocked :
    Not (MissingViableCandidateRows rows.candidateRows)
  equations : SameOppositeExactLocalEquationPackage
  remaining :
    TransitionRemainingFields equations.toSameOppositeCandidate

namespace CandidateSubsetRouteFields

def toCandidateRowsInW11Candidate
    (R : CandidateSubsetRouteFields) :
    ExactLocalClosureW11.CandidateRowsInW11Candidate
      R.rows.candidateRows :=
  ExactLocalClosureW11.CandidateRowsInW11Candidate.ofCandidate
    R.rows.candidateRows R.equations.toSameOppositeCandidate

theorem sameRows
    (R : CandidateSubsetRouteFields) :
    PreservesRows R.equations.same.placeNext
      R.rows.candidateRows.row := by
  intro source hsource u v _hrow
  exact R.equations.same.preservesExactLocalSqDistances source hsource u v

theorem oppositeRows
    (R : CandidateSubsetRouteFields) :
    PreservesRows R.equations.opposite.placeNext
      R.rows.candidateRows.row := by
  intro source hsource u v _hrow
  exact R.equations.opposite.preservesExactLocalSqDistances source hsource u v

theorem noBlockedEndpointRow
    (R : CandidateSubsetRouteFields)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (R.rows.candidateRows.row u v) :=
  R.rows.no_blocked_row hblocked

theorem missingRowsBlocked
    (R : CandidateSubsetRouteFields) :
    Not (MissingViableCandidateRows R.rows.candidateRows) :=
  R.missingViableRowsBlocked

def toTransitionRouteFields
    (R : CandidateSubsetRouteFields) :
    TransitionRouteFields where
  candidate := R.equations.toSameOppositeCandidate
  remaining := R.remaining

def toRoleEquationRouteFields
    (R : CandidateSubsetRouteFields) :
    RoleEquationRouteFields where
  equations := R.equations
  remaining := R.remaining

theorem generatedTransitionsPreserveExactLocalSqDistances
    (R : CandidateSubsetRouteFields) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      R.equations.toFigure2TransitionObligations :=
  R.equations.generatedTransitionsPreserveExactLocalSqDistances

end CandidateSubsetRouteFields

/-- Fill the ledger fields around a row subset and reduced equation route. -/
def candidateSubsetRouteFields
    (rows : CandidateRowSubsetLedger)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    CandidateSubsetRouteFields where
  rows := rows
  obstructions := ExactLocalClosureW11.obstructionRowsLedger
  endpointShortcuts := ExactLocalClosureW11.concreteEndpointShortcutLedger
  missingViableRowsBlocked :=
    ExactLocalClosureW11.noConcreteMissingCandidateRows rows.candidateRows
  equations := equations
  remaining := remaining

def possibleRowsRouteFields
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    CandidateSubsetRouteFields :=
  candidateSubsetRouteFields
    ExactLocalClosureW11.possibleRowsSubsetLedger equations remaining

/-! ## Explicit ledgers -/

/-- The exact-local source shapes exported by this integration layer. -/
structure PackageLedger where
  candidateRows : Type
  candidateRowSubsetLedger : Type
  obstructionRowsLedger : Type
  endpointShortcutLedger : Type
  missingViableCandidateRows : CandidateRows -> Prop
  exactLocalEquationPackage : Type
  sameOppositeEquationPackage : Type
  candidateSubsetRouteFields : Type
  transitionRouteFields : Type
  roleEquationRouteFields : Type

def packageLedger : PackageLedger where
  candidateRows := CandidateRows
  candidateRowSubsetLedger := CandidateRowSubsetLedger
  obstructionRowsLedger := ObstructionRowsLedger
  endpointShortcutLedger := ConcreteEndpointShortcutLedger
  missingViableCandidateRows := MissingViableCandidateRows
  exactLocalEquationPackage := ExactLocalEquationPackage
  sameOppositeEquationPackage := SameOppositeExactLocalEquationPackage
  candidateSubsetRouteFields := CandidateSubsetRouteFields
  transitionRouteFields := TransitionRouteFields
  roleEquationRouteFields := RoleEquationRouteFields

/-! ## Target facade rows -/

/-- Exact, eventual, and arbitrary W11 target projections from one package. -/
structure TargetFacadeRow (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

open FlexibleTransitionClosureW11 in
def transitionRouteExactTarget
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_transitionRouteFields R

open FlexibleTransitionClosureW11 in
def transitionRouteEventualTarget
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields R

open FlexibleTransitionClosureW11 in
def transitionRouteArbitraryTarget
    (R : TransitionRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields R

def candidateSubsetTransitionTargetRow :
    TargetFacadeRow CandidateSubsetRouteFields where
  exactTarget := fun R =>
    transitionRouteExactTarget R.toTransitionRouteFields
  eventualTarget := fun R =>
    transitionRouteEventualTarget R.toTransitionRouteFields
  arbitraryTarget := fun R =>
    transitionRouteArbitraryTarget R.toTransitionRouteFields

def candidateSubsetRoleHingeTargetRow :
    TargetFacadeRow CandidateSubsetRouteFields where
  exactTarget := fun R =>
    RoleHingeClosureW11.targetUpperConstructionFiveSixteen_of_equationRoute
      R.toRoleEquationRouteFields
  eventualTarget := fun R =>
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenEventually_of_equationRoute
      R.toRoleEquationRouteFields
  arbitraryTarget := fun R =>
    RoleHingeClosureW11.targetUpperConstructionFiveSixteenArbitrary_of_equationRoute
      R.toRoleEquationRouteFields

/-! ## Integrated matrix -/

/-- Integrated exact-local matrix for W11 row, obstruction, and target routes. -/
structure Matrix where
  packages : PackageLedger
  exactLocalClosure : ExactLocalClosureW11.Matrix
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  flexibleTransitionClosure : FlexibleTransitionClosureW11.Matrix
  possibleRows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  endpointShortcuts : ConcreteEndpointShortcutLedger
  missingViableRows : MissingViableRowsLedger
  transitionTargets : TargetFacadeRow CandidateSubsetRouteFields
  roleHingeTargets : TargetFacadeRow CandidateSubsetRouteFields

def matrix : Matrix where
  packages := packageLedger
  exactLocalClosure := ExactLocalClosureW11.matrix
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  flexibleTransitionClosure := FlexibleTransitionClosureW11.matrix
  possibleRows := ExactLocalClosureW11.possibleRowsSubsetLedger
  obstructions := ExactLocalClosureW11.obstructionRowsLedger
  endpointShortcuts := ExactLocalClosureW11.concreteEndpointShortcutLedger
  missingViableRows := missingViableRowsLedger
  transitionTargets := candidateSubsetTransitionTargetRow
  roleHingeTargets := candidateSubsetRoleHingeTargetRow

/-! ## Public row and obstruction projections -/

theorem possibleRowsSubset_card :
    ExactLocalObstructionMatrixW11.possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard :=
  matrix.obstructions.possibleRowCount

theorem impossibleRowsSubset_card :
    ExactLocalObstructionMatrixW11.impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard :=
  matrix.obstructions.impossibleRowCount

theorem candidateRows_project_to_w10
    (C : CandidateRows)
    {u v : LocalVertex}
    (hrow : C.row u v) :
    W10PossibleRow u v :=
  C.projects_to_w10 hrow

theorem candidateRows_project_to_w11
    (C : CandidateRows)
    {u v : LocalVertex}
    (hrow : C.row u v) :
    PossibleRow u v :=
  ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.possible C hrow

theorem candidateRows_exclude_blockedEndpoint
    (C : CandidateRows)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (C.row u v) :=
  matrix.obstructions.candidateExcludesBlocked C hblocked

theorem rootMovedTargetRow_not_possible
    {u v : LocalVertex}
    (hrow :
      ExactLocalObstructionMatrixW11.IsRootMovedTargetRow u v) :
    Not (PossibleRow u v) :=
  matrix.obstructions.rootMovedTarget hrow

theorem connectorEndpointRow_not_possible
    {u v : LocalVertex}
    (hrow :
      ExactLocalObstructionMatrixW11.IsConnectorEndpointRow u v) :
    Not (PossibleRow u v) :=
  matrix.obstructions.connectorEndpoint hrow

theorem blockedEndpointRow_not_possible
    {u v : LocalVertex}
    (hrow :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (PossibleRow u v) :=
  matrix.obstructions.blockedEndpoint hrow

theorem missingViableCandidateRows_blocked
    (C : CandidateRows) :
    Not (MissingViableCandidateRows C) :=
  matrix.missingViableRows.blocked C

/-! ## Public endpoint shortcut projections -/

theorem endpointShortcut_not_possible
    (E : EndpointShortcutRow) :
    Not (PossibleRow E.u E.v) :=
  E.notPossible

theorem endpointShortcut_sameRows_blocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  E.sameRowsBlocked hrow

theorem endpointShortcut_oppositeRows_blocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  E.oppositeRowsBlocked hrow

theorem pUpperForward_endpointShortcut_not_possible :
    Not (PossibleRow T2_2 T1_1) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.pUpperForward

theorem pUpperReverse_endpointShortcut_not_possible :
    Not (PossibleRow T1_1 T2_2) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.pUpperReverse

theorem pLowerForward_endpointShortcut_not_possible :
    Not (PossibleRow T2_2 T1_2) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.pLowerForward

theorem pLowerReverse_endpointShortcut_not_possible :
    Not (PossibleRow T1_2 T2_2) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.pLowerReverse

theorem qUpperForward_endpointShortcut_not_possible :
    Not (PossibleRow T4_0 T0_0) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.qUpperForward

theorem qUpperReverse_endpointShortcut_not_possible :
    Not (PossibleRow T0_0 T4_0) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.qUpperReverse

theorem qLowerForward_endpointShortcut_not_possible :
    Not (PossibleRow T4_0 T0_2) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.qLowerForward

theorem qLowerReverse_endpointShortcut_not_possible :
    Not (PossibleRow T0_2 T4_0) :=
  endpointShortcut_not_possible matrix.endpointShortcuts.qLowerReverse

/-! ## Public target routes -/

theorem targetUpperConstructionFiveSixteen_of_candidateSubsetTransitionRoute
    (R : CandidateSubsetRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transitionTargets.exactTarget R

theorem
    targetUpperConstructionFiveSixteenEventually_of_candidateSubsetTransitionRoute
    (R : CandidateSubsetRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transitionTargets.eventualTarget R

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_candidateSubsetTransitionRoute
    (R : CandidateSubsetRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionTargets.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_candidateSubsetRoleHingeRoute
    (R : CandidateSubsetRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleHingeTargets.exactTarget R

theorem
    targetUpperConstructionFiveSixteenEventually_of_candidateSubsetRoleHingeRoute
    (R : CandidateSubsetRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.roleHingeTargets.eventualTarget R

theorem
    targetUpperConstructionFiveSixteenArbitrary_of_candidateSubsetRoleHingeRoute
    (R : CandidateSubsetRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleHingeTargets.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_possibleRowsRoute
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_candidateSubsetTransitionRoute
    (possibleRowsRouteFields equations remaining)

theorem targetUpperConstructionFiveSixteenArbitrary_of_possibleRowsRoute
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_candidateSubsetTransitionRoute
    (possibleRowsRouteFields equations remaining)

end

end ExactLocalIntegratedW11
end PachToth
end ErdosProblems1066
