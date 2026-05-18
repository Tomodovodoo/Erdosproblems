import ErdosProblems1066.PachToth.ExactLocalIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeIntegratedW11
import ErdosProblems1066.PachToth.TransitionIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 exact-local target integration

This module is a target-facing adapter for the W11 exact-local route.  It keeps
candidate-row subsets, obstruction rows, endpoint blockers, and the remaining
role-hinge or transition data visible.  Target conclusions are exported only
from an explicit exact-local target field package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalTargetIntegratedW11

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

universe u v

abbrev R2 := Prod Real Real

abbrev CandidateRows :=
  ExactLocalIntegratedW11.CandidateRows

abbrev CandidateRowSubsetLedger :=
  ExactLocalIntegratedW11.CandidateRowSubsetLedger

abbrev ObstructionRowsLedger :=
  ExactLocalIntegratedW11.ObstructionRowsLedger

abbrev ConcreteEndpointShortcutLedger :=
  ExactLocalIntegratedW11.ConcreteEndpointShortcutLedger

abbrev EndpointShortcutRow :=
  ExactLocalIntegratedW11.EndpointShortcutRow

abbrev MissingViableCandidateRows :=
  ExactLocalIntegratedW11.MissingViableCandidateRows

abbrev MissingViableRowsLedger :=
  ExactLocalIntegratedW11.MissingViableRowsLedger

abbrev PossibleRow :=
  ExactLocalIntegratedW11.PossibleRow

abbrev W10PossibleRow :=
  ExactLocalIntegratedW11.W10PossibleRow

abbrev PreservesRows :=
  ExactLocalIntegratedW11.PreservesRows

abbrev SameOppositeCandidate :=
  ExactLocalIntegratedW11.SameOppositeCandidate

abbrev SameOppositeExactLocalEquationPackage :=
  ExactLocalIntegratedW11.SameOppositeExactLocalEquationPackage

abbrev TransitionRemainingFields
    (T : SameOppositeCandidate) :=
  ExactLocalIntegratedW11.TransitionRemainingFields T

abbrev CandidateSubsetRouteFields :=
  ExactLocalIntegratedW11.CandidateSubsetRouteFields

abbrev TransitionRouteFields :=
  TransitionIntegratedW11.TransitionRouteFields

abbrev RoleEquationRouteFields :=
  RoleHingeIntegratedW11.EquationRouteFields

abbrev TransitionExactLocalRouteFields :=
  TransitionIntegratedW11.ExactLocalRouteFields

/-! ## Candidate subset and blocker ledgers -/

/-- Endpoint shortcuts excluded by the exact-local row matrix. -/
structure EndpointBlockerLedger where
  endpointShortcuts : ConcreteEndpointShortcutLedger
  pUpperForward : Not (PossibleRow T2_2 T1_1)
  pUpperReverse : Not (PossibleRow T1_1 T2_2)
  pLowerForward : Not (PossibleRow T2_2 T1_2)
  pLowerReverse : Not (PossibleRow T1_2 T2_2)
  qUpperForward : Not (PossibleRow T4_0 T0_0)
  qUpperReverse : Not (PossibleRow T0_0 T4_0)
  qLowerForward : Not (PossibleRow T4_0 T0_2)
  qLowerReverse : Not (PossibleRow T0_2 T4_0)

def endpointBlockerLedger : EndpointBlockerLedger where
  endpointShortcuts := ExactLocalIntegratedW11.matrix.endpointShortcuts
  pUpperForward :=
    ExactLocalIntegratedW11.pUpperForward_endpointShortcut_not_possible
  pUpperReverse :=
    ExactLocalIntegratedW11.pUpperReverse_endpointShortcut_not_possible
  pLowerForward :=
    ExactLocalIntegratedW11.pLowerForward_endpointShortcut_not_possible
  pLowerReverse :=
    ExactLocalIntegratedW11.pLowerReverse_endpointShortcut_not_possible
  qUpperForward :=
    ExactLocalIntegratedW11.qUpperForward_endpointShortcut_not_possible
  qUpperReverse :=
    ExactLocalIntegratedW11.qUpperReverse_endpointShortcut_not_possible
  qLowerForward :=
    ExactLocalIntegratedW11.qLowerForward_endpointShortcut_not_possible
  qLowerReverse :=
    ExactLocalIntegratedW11.qLowerReverse_endpointShortcut_not_possible

/-- Source package shapes displayed by the target adapter. -/
structure SourceLedger where
  candidateRows : Type
  candidateRowSubsetLedger : Type
  possibleRows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  endpointBlockers : EndpointBlockerLedger
  missingViableCandidateRows : CandidateRows -> Prop
  missingViableRowsLedger : Type
  sameOppositeEquationPackage : Type
  candidateSubsetRouteFields : Type
  transitionRouteFields : Type
  roleEquationRouteFields : Type
  transitionExactLocalRouteFields : Type

def sourceLedger : SourceLedger where
  candidateRows := CandidateRows
  candidateRowSubsetLedger := CandidateRowSubsetLedger
  possibleRows := ExactLocalIntegratedW11.matrix.possibleRows
  obstructions := ExactLocalIntegratedW11.matrix.obstructions
  endpointBlockers := endpointBlockerLedger
  missingViableCandidateRows := MissingViableCandidateRows
  missingViableRowsLedger := MissingViableRowsLedger
  sameOppositeEquationPackage := SameOppositeExactLocalEquationPackage
  candidateSubsetRouteFields := CandidateSubsetRouteFields
  transitionRouteFields := TransitionRouteFields
  roleEquationRouteFields := RoleEquationRouteFields
  transitionExactLocalRouteFields := TransitionExactLocalRouteFields

/-! ## Explicit target-facing exact-local fields -/

/-- Exact-local target fields from a candidate-row subset and reduced
same/opposite equation package. -/
structure ExactLocalTargetFields where
  rows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  endpointShortcuts : ConcreteEndpointShortcutLedger
  missingViableRowsBlocked :
    Not (MissingViableCandidateRows rows.candidateRows)
  equations : SameOppositeExactLocalEquationPackage
  remaining : TransitionRemainingFields equations.toSameOppositeCandidate

namespace ExactLocalTargetFields

def toCandidateSubsetRouteFields
    (R : ExactLocalTargetFields) :
    CandidateSubsetRouteFields where
  rows := R.rows
  obstructions := R.obstructions
  endpointShortcuts := R.endpointShortcuts
  missingViableRowsBlocked := R.missingViableRowsBlocked
  equations := R.equations
  remaining := R.remaining

def toTransitionRouteFields
    (R : ExactLocalTargetFields) :
    TransitionRouteFields :=
  R.toCandidateSubsetRouteFields.toTransitionRouteFields

def toRoleEquationRouteFields
    (R : ExactLocalTargetFields) :
    RoleEquationRouteFields :=
  R.toCandidateSubsetRouteFields.toRoleEquationRouteFields

def toTransitionExactLocalRouteFields
    (R : ExactLocalTargetFields) :
    TransitionExactLocalRouteFields where
  equations := R.equations
  remaining := R.remaining

theorem sameRows
    (R : ExactLocalTargetFields) :
    PreservesRows R.equations.same.placeNext
      R.rows.candidateRows.row :=
  ExactLocalIntegratedW11.CandidateSubsetRouteFields.sameRows
    R.toCandidateSubsetRouteFields

theorem oppositeRows
    (R : ExactLocalTargetFields) :
    PreservesRows R.equations.opposite.placeNext
      R.rows.candidateRows.row :=
  ExactLocalIntegratedW11.CandidateSubsetRouteFields.oppositeRows
    R.toCandidateSubsetRouteFields

theorem noBlockedEndpointRow
    (R : ExactLocalTargetFields)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (R.rows.candidateRows.row u v) :=
  ExactLocalIntegratedW11.CandidateSubsetRouteFields.noBlockedEndpointRow
    R.toCandidateSubsetRouteFields hblocked

theorem missingRowsBlocked
    (R : ExactLocalTargetFields) :
    Not (MissingViableCandidateRows R.rows.candidateRows) :=
  R.missingViableRowsBlocked

theorem generatedTransitionsPreserveExactLocalSqDistances
    (R : ExactLocalTargetFields) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      R.equations.toFigure2TransitionObligations :=
  ExactLocalIntegratedW11.CandidateSubsetRouteFields.generatedTransitionsPreserveExactLocalSqDistances
    R.toCandidateSubsetRouteFields

end ExactLocalTargetFields

def exactLocalTargetFields
    (rows : CandidateRowSubsetLedger)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ExactLocalTargetFields where
  rows := rows
  obstructions := ExactLocalIntegratedW11.matrix.obstructions
  endpointShortcuts := ExactLocalIntegratedW11.matrix.endpointShortcuts
  missingViableRowsBlocked :=
    ExactLocalIntegratedW11.missingViableCandidateRows_blocked
      rows.candidateRows
  equations := equations
  remaining := remaining

def possibleRowsTargetFields
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ExactLocalTargetFields :=
  exactLocalTargetFields
    ExactLocalIntegratedW11.matrix.possibleRows equations remaining

/-! ## Target route rows -/

/-- Exact, eventual, and arbitrary target projections from one package. -/
structure TargetRoute (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

def pullbackTargetRoute
    {alpha : Sort u} {beta : Sort v}
    (R : TargetRoute beta) (f : alpha -> beta) :
    TargetRoute alpha where
  exactTarget := fun a => R.exactTarget (f a)
  eventualTarget := fun a => R.eventualTarget (f a)
  arbitraryTarget := fun a => R.arbitraryTarget (f a)

def targetRouteOfExactLocalFacade
    {alpha : Sort u}
    (R : ExactLocalIntegratedW11.TargetFacadeRow alpha) :
    TargetRoute alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

def exactLocalIntegratedTransitionRoute :
    TargetRoute ExactLocalTargetFields :=
  pullbackTargetRoute
    (targetRouteOfExactLocalFacade
      ExactLocalIntegratedW11.candidateSubsetTransitionTargetRow)
    ExactLocalTargetFields.toCandidateSubsetRouteFields

def exactLocalIntegratedRoleHingeRoute :
    TargetRoute ExactLocalTargetFields :=
  pullbackTargetRoute
    (targetRouteOfExactLocalFacade
      ExactLocalIntegratedW11.candidateSubsetRoleHingeTargetRow)
    ExactLocalTargetFields.toCandidateSubsetRouteFields

def transitionIntegratedRoute :
    TargetRoute ExactLocalTargetFields where
  exactTarget := fun R =>
    TransitionIntegratedW11.targetUpperConstructionFiveSixteen_of_transitionRouteFields
      R.toTransitionRouteFields
  eventualTarget := fun R =>
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
      R.toTransitionRouteFields
  arbitraryTarget := fun R =>
    TransitionIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
      R.toTransitionRouteFields

def roleHingeIntegratedRoute :
    TargetRoute ExactLocalTargetFields where
  exactTarget := fun R =>
    RoleHingeIntegratedW11.targetUpperConstructionFiveSixteen_of_equationRoute
      R.toRoleEquationRouteFields
  eventualTarget := fun R =>
    RoleHingeIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_equationRoute
      R.toRoleEquationRouteFields
  arbitraryTarget := fun R =>
    RoleHingeIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_equationRoute
      R.toRoleEquationRouteFields

def pachTothIntegratedTransitionRoute :
    TargetRoute ExactLocalTargetFields where
  exactTarget := fun R =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_transitionRouteFields
      R.toTransitionRouteFields
  eventualTarget := fun R =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
      R.toTransitionRouteFields
  arbitraryTarget := fun R =>
    PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
      R.toTransitionRouteFields

/-! ## Imported matrices and aggregate -/

/-- Checked ledgers imported by this target adapter. -/
structure ImportedLedgers where
  exactLocalClosure : ExactLocalClosureW11.Matrix
  exactLocalIntegrated : ExactLocalIntegratedW11.Matrix
  roleHingeIntegrated : RoleHingeIntegratedW11.Matrix
  transitionIntegrated : TransitionIntegratedW11.Matrix
  pachTothIntegrated : PachTothW11IntegratedMatrix.Matrix

def importedLedgers : ImportedLedgers where
  exactLocalClosure := ExactLocalClosureW11.matrix
  exactLocalIntegrated := ExactLocalIntegratedW11.matrix
  roleHingeIntegrated := RoleHingeIntegratedW11.matrix
  transitionIntegrated := TransitionIntegratedW11.matrix
  pachTothIntegrated := PachTothW11IntegratedMatrix.matrix

/-- Target-facing exact-local aggregate.  It stores route functions only. -/
structure Matrix where
  sources : SourceLedger
  imported : ImportedLedgers
  endpointBlockers : EndpointBlockerLedger
  exactLocalTransition :
    TargetRoute ExactLocalTargetFields
  exactLocalRoleHinge :
    TargetRoute ExactLocalTargetFields
  transitionFacade :
    TargetRoute ExactLocalTargetFields
  roleHingeFacade :
    TargetRoute ExactLocalTargetFields
  pachTothTransitionFacade :
    TargetRoute ExactLocalTargetFields

def matrix : Matrix where
  sources := sourceLedger
  imported := importedLedgers
  endpointBlockers := endpointBlockerLedger
  exactLocalTransition := exactLocalIntegratedTransitionRoute
  exactLocalRoleHinge := exactLocalIntegratedRoleHingeRoute
  transitionFacade := transitionIntegratedRoute
  roleHingeFacade := roleHingeIntegratedRoute
  pachTothTransitionFacade := pachTothIntegratedTransitionRoute

/-! ## Public candidate-row projections -/

theorem candidateRows_project_to_w10
    (R : ExactLocalTargetFields)
    {u v : LocalVertex}
    (hrow : R.rows.candidateRows.row u v) :
    W10PossibleRow u v :=
  R.rows.projectsToW10 hrow

theorem candidateRows_project_to_w11
    (R : ExactLocalTargetFields)
    {u v : LocalVertex}
    (hrow : R.rows.candidateRows.row u v) :
    PossibleRow u v :=
  R.rows.projectsToW11 hrow

theorem candidateRows_exclude_blockedEndpoint
    (R : ExactLocalTargetFields)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (R.rows.candidateRows.row u v) :=
  R.noBlockedEndpointRow hblocked

theorem missingViableCandidateRows_blocked
    (R : ExactLocalTargetFields) :
    Not (MissingViableCandidateRows R.rows.candidateRows) :=
  R.missingRowsBlocked

theorem endpointShortcut_not_possible
    (E : EndpointShortcutRow) :
    Not (PossibleRow E.u E.v) :=
  ExactLocalIntegratedW11.endpointShortcut_not_possible E

theorem endpointShortcut_sameRows_blocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  ExactLocalIntegratedW11.endpointShortcut_sameRows_blocked E hrow

theorem endpointShortcut_oppositeRows_blocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  ExactLocalIntegratedW11.endpointShortcut_oppositeRows_blocked E hrow

theorem pUpperForward_endpointShortcut_not_possible :
    Not (PossibleRow T2_2 T1_1) :=
  matrix.endpointBlockers.pUpperForward

theorem pUpperReverse_endpointShortcut_not_possible :
    Not (PossibleRow T1_1 T2_2) :=
  matrix.endpointBlockers.pUpperReverse

theorem pLowerForward_endpointShortcut_not_possible :
    Not (PossibleRow T2_2 T1_2) :=
  matrix.endpointBlockers.pLowerForward

theorem pLowerReverse_endpointShortcut_not_possible :
    Not (PossibleRow T1_2 T2_2) :=
  matrix.endpointBlockers.pLowerReverse

theorem qUpperForward_endpointShortcut_not_possible :
    Not (PossibleRow T4_0 T0_0) :=
  matrix.endpointBlockers.qUpperForward

theorem qUpperReverse_endpointShortcut_not_possible :
    Not (PossibleRow T0_0 T4_0) :=
  matrix.endpointBlockers.qUpperReverse

theorem qLowerForward_endpointShortcut_not_possible :
    Not (PossibleRow T4_0 T0_2) :=
  matrix.endpointBlockers.qLowerForward

theorem qLowerReverse_endpointShortcut_not_possible :
    Not (PossibleRow T0_2 T4_0) :=
  matrix.endpointBlockers.qLowerReverse

/-! ## Public target projections -/

theorem targetUpperConstructionFiveSixteen_of_exactLocalTransition
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.exactLocalTransition.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_exactLocalTransition
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.exactLocalTransition.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactLocalTransition
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactLocalTransition.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_exactLocalRoleHinge
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.exactLocalRoleHinge.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_exactLocalRoleHinge
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.exactLocalRoleHinge.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRoleHinge
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.exactLocalRoleHinge.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_transitionFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.transitionFacade.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_transitionFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.transitionFacade.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_transitionFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.transitionFacade.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_roleHingeFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.roleHingeFacade.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_roleHingeFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.roleHingeFacade.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_roleHingeFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.roleHingeFacade.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_pachTothTransitionFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.pachTothTransitionFacade.exactTarget R

theorem targetUpperConstructionFiveSixteenEventually_of_pachTothTransitionFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.pachTothTransitionFacade.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_pachTothTransitionFacade
    (R : ExactLocalTargetFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.pachTothTransitionFacade.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_possibleRowsTransitionFacade
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  targetUpperConstructionFiveSixteen_of_transitionFacade
    (possibleRowsTargetFields equations remaining)

theorem targetUpperConstructionFiveSixteenEventually_of_possibleRowsTransitionFacade
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  targetUpperConstructionFiveSixteenEventually_of_transitionFacade
    (possibleRowsTargetFields equations remaining)

theorem targetUpperConstructionFiveSixteenArbitrary_of_possibleRowsTransitionFacade
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  targetUpperConstructionFiveSixteenArbitrary_of_transitionFacade
    (possibleRowsTargetFields equations remaining)

end

end ExactLocalTargetIntegratedW11
end PachToth
end ErdosProblems1066
