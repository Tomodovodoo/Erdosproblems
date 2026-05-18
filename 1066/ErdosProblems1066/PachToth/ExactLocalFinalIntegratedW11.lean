import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.ExactLocalIntegratedW11
import ErdosProblems1066.PachToth.ExactLocalTargetIntegratedW11
import ErdosProblems1066.PachToth.TransitionTargetIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final exact-local aggregate

This module is the final exact-local W11 ledger.  It keeps candidate-row
subsets, endpoint shortcut blockers, exact-local target fields, transition
target packages, role-hinge final routes, and final consistency witnesses in
one package-dependent facade.

All target projections below take an explicit exact-local package value.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalFinalIntegratedW11

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

universe u

abbrev R2 := Prod Real Real

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev CandidateRows :=
  ExactLocalTargetIntegratedW11.CandidateRows

abbrev CandidateRowSubsetLedger :=
  ExactLocalTargetIntegratedW11.CandidateRowSubsetLedger

abbrev ObstructionRowsLedger :=
  ExactLocalTargetIntegratedW11.ObstructionRowsLedger

abbrev ConcreteEndpointShortcutLedger :=
  ExactLocalTargetIntegratedW11.ConcreteEndpointShortcutLedger

abbrev EndpointShortcutRow :=
  ExactLocalTargetIntegratedW11.EndpointShortcutRow

abbrev MissingViableCandidateRows :=
  ExactLocalTargetIntegratedW11.MissingViableCandidateRows

abbrev PossibleRow :=
  ExactLocalTargetIntegratedW11.PossibleRow

abbrev W10PossibleRow :=
  ExactLocalTargetIntegratedW11.W10PossibleRow

abbrev PreservesRows :=
  ExactLocalTargetIntegratedW11.PreservesRows

abbrev SameOppositeExactLocalEquationPackage :=
  ExactLocalTargetIntegratedW11.SameOppositeExactLocalEquationPackage

abbrev SameOppositeCandidate :=
  ExactLocalTargetIntegratedW11.SameOppositeCandidate

abbrev TransitionRemainingFields
    (T : SameOppositeCandidate) :=
  ExactLocalTargetIntegratedW11.TransitionRemainingFields T

abbrev CandidateSubsetRouteFields :=
  ExactLocalTargetIntegratedW11.CandidateSubsetRouteFields

abbrev ExactLocalTargetFields :=
  ExactLocalTargetIntegratedW11.ExactLocalTargetFields

abbrev TransitionRouteFields :=
  ExactLocalTargetIntegratedW11.TransitionRouteFields

abbrev RoleEquationRouteFields :=
  ExactLocalTargetIntegratedW11.RoleEquationRouteFields

abbrev TransitionExactLocalRouteFields :=
  ExactLocalTargetIntegratedW11.TransitionExactLocalRouteFields

/-! ## Source and endpoint ledgers -/

/-- Source shapes exposed by the final exact-local aggregate. -/
structure FinalSourceLedger where
  candidateRows : Type
  candidateRowSubsetLedger : Type
  candidateRowSubsetFields : Type
  endpointBlockerLedger : Type
  obstructionRows : Type
  endpointShortcutRows : Type
  missingViableCandidateRows : CandidateRows -> Prop
  exactLocalTargetFields : Type
  exactLocalFinalPackage : Type
  sameOppositeEquationPackage : Type
  remainingFields :
    forall _ : SameOppositeExactLocalEquationPackage,
      Type
  transitionRouteFields : Type
  roleEquationRouteFields : Type
  transitionExactLocalRouteFields : Type

/-- Endpoint shortcut blockers carried by the exact-local row matrix. -/
structure FinalEndpointBlockerLedger where
  targetLedger : ExactLocalTargetIntegratedW11.EndpointBlockerLedger
  endpointShortcuts : ConcreteEndpointShortcutLedger
  shortcutNotPossible :
    forall E : EndpointShortcutRow, Not (PossibleRow E.u E.v)
  shortcutSameRowsBlocked :
    forall E : EndpointShortcutRow,
      forall {row : LocalVertex -> LocalVertex -> Prop},
        row E.u E.v ->
          Not (PreservesRows RoleHingeConcreteSearch.samePlaceNext row)
  shortcutOppositeRowsBlocked :
    forall E : EndpointShortcutRow,
      forall {row : LocalVertex -> LocalVertex -> Prop},
        row E.u E.v ->
          Not (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row)
  pUpperForward : Not (PossibleRow T2_2 T1_1)
  pUpperReverse : Not (PossibleRow T1_1 T2_2)
  pLowerForward : Not (PossibleRow T2_2 T1_2)
  pLowerReverse : Not (PossibleRow T1_2 T2_2)
  qUpperForward : Not (PossibleRow T4_0 T0_0)
  qUpperReverse : Not (PossibleRow T0_0 T4_0)
  qLowerForward : Not (PossibleRow T4_0 T0_2)
  qLowerReverse : Not (PossibleRow T0_2 T4_0)

def finalEndpointBlockerLedger : FinalEndpointBlockerLedger where
  targetLedger := ExactLocalTargetIntegratedW11.endpointBlockerLedger
  endpointShortcuts := ExactLocalIntegratedW11.matrix.endpointShortcuts
  shortcutNotPossible :=
    ExactLocalTargetIntegratedW11.endpointShortcut_not_possible
  shortcutSameRowsBlocked :=
    ExactLocalTargetIntegratedW11.endpointShortcut_sameRows_blocked
  shortcutOppositeRowsBlocked :=
    ExactLocalTargetIntegratedW11.endpointShortcut_oppositeRows_blocked
  pUpperForward :=
    ExactLocalTargetIntegratedW11.pUpperForward_endpointShortcut_not_possible
  pUpperReverse :=
    ExactLocalTargetIntegratedW11.pUpperReverse_endpointShortcut_not_possible
  pLowerForward :=
    ExactLocalTargetIntegratedW11.pLowerForward_endpointShortcut_not_possible
  pLowerReverse :=
    ExactLocalTargetIntegratedW11.pLowerReverse_endpointShortcut_not_possible
  qUpperForward :=
    ExactLocalTargetIntegratedW11.qUpperForward_endpointShortcut_not_possible
  qUpperReverse :=
    ExactLocalTargetIntegratedW11.qUpperReverse_endpointShortcut_not_possible
  qLowerForward :=
    ExactLocalTargetIntegratedW11.qLowerForward_endpointShortcut_not_possible
  qLowerReverse :=
    ExactLocalTargetIntegratedW11.qLowerReverse_endpointShortcut_not_possible

/-! ## Candidate-row subset fields -/

/-- Candidate-row subset data before a reduced equation package is supplied. -/
structure CandidateRowSubsetFields where
  rows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  endpointShortcuts : ConcreteEndpointShortcutLedger
  endpointBlockers : FinalEndpointBlockerLedger
  missingViableRowsBlocked :
    Not (MissingViableCandidateRows rows.candidateRows)

namespace CandidateRowSubsetFields

def toCandidateSubsetRouteFields
    (F : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    CandidateSubsetRouteFields where
  rows := F.rows
  obstructions := F.obstructions
  endpointShortcuts := F.endpointShortcuts
  missingViableRowsBlocked := F.missingViableRowsBlocked
  equations := equations
  remaining := remaining

def toExactLocalTargetFields
    (F : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ExactLocalTargetFields where
  rows := F.rows
  obstructions := F.obstructions
  endpointShortcuts := F.endpointShortcuts
  missingViableRowsBlocked := F.missingViableRowsBlocked
  equations := equations
  remaining := remaining

theorem candidateRows_project_to_w10
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hrow : F.rows.candidateRows.row u v) :
    W10PossibleRow u v :=
  F.rows.projectsToW10 hrow

theorem candidateRows_project_to_w11
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hrow : F.rows.candidateRows.row u v) :
    PossibleRow u v :=
  F.rows.projectsToW11 hrow

theorem sameRows
    (F : CandidateRowSubsetFields) :
    PreservesRows RoleHingeConcreteSearch.samePlaceNext
      F.rows.candidateRows.row :=
  F.rows.samePreserves

theorem oppositeRows
    (F : CandidateRowSubsetFields) :
    PreservesRows RoleHingeConcreteSearch.oppositePlaceNext
      F.rows.candidateRows.row :=
  F.rows.oppositePreserves

theorem noBlockedEndpointRow
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (F.rows.candidateRows.row u v) :=
  F.rows.no_blocked_row hblocked

theorem missingRowsBlocked
    (F : CandidateRowSubsetFields) :
    Not (MissingViableCandidateRows F.rows.candidateRows) :=
  F.missingViableRowsBlocked

end CandidateRowSubsetFields

/-- Fill final subset fields around any checked row subset. -/
def candidateRowSubsetFields
    (rows : CandidateRowSubsetLedger) :
    CandidateRowSubsetFields where
  rows := rows
  obstructions := ExactLocalIntegratedW11.matrix.obstructions
  endpointShortcuts := ExactLocalIntegratedW11.matrix.endpointShortcuts
  endpointBlockers := finalEndpointBlockerLedger
  missingViableRowsBlocked :=
    ExactLocalIntegratedW11.missingViableCandidateRows_blocked
      rows.candidateRows

def possibleRowsCandidateRowSubsetFields : CandidateRowSubsetFields :=
  candidateRowSubsetFields ExactLocalIntegratedW11.matrix.possibleRows

/-! ## Final exact-local packages -/

/-- Final exact-local input package for all target projections in this file. -/
structure FinalExactLocalPackage where
  subset : CandidateRowSubsetFields
  equations : SameOppositeExactLocalEquationPackage
  remaining :
    TransitionRemainingFields equations.toSameOppositeCandidate

namespace FinalExactLocalPackage

def toCandidateSubsetRouteFields
    (P : FinalExactLocalPackage) :
    CandidateSubsetRouteFields :=
  P.subset.toCandidateSubsetRouteFields P.equations P.remaining

def toExactLocalTargetFields
    (P : FinalExactLocalPackage) :
    ExactLocalTargetFields :=
  P.subset.toExactLocalTargetFields P.equations P.remaining

def toTransitionRouteFields
    (P : FinalExactLocalPackage) :
    TransitionRouteFields :=
  P.toExactLocalTargetFields.toTransitionRouteFields

def toRoleEquationRouteFields
    (P : FinalExactLocalPackage) :
    RoleEquationRouteFields :=
  P.toExactLocalTargetFields.toRoleEquationRouteFields

def toTransitionExactLocalRouteFields
    (P : FinalExactLocalPackage) :
    TransitionExactLocalRouteFields :=
  P.toExactLocalTargetFields.toTransitionExactLocalRouteFields

def toTransitionTargetRoutePackage
    (P : FinalExactLocalPackage) :
    TransitionTargetIntegratedW11.RoutePackage :=
  TransitionTargetIntegratedW11.RoutePackage.exactLocal
    P.toTransitionExactLocalRouteFields

def toRoleHingeFinalExactLocalRouteFields
    (P : FinalExactLocalPackage) :
    RoleHingeFinalIntegratedW11.ExactLocalRouteFields where
  equations := P.equations
  remaining := P.remaining

theorem sameRows
    (P : FinalExactLocalPackage) :
    PreservesRows P.equations.same.placeNext
      P.subset.rows.candidateRows.row :=
  P.toExactLocalTargetFields.sameRows

theorem oppositeRows
    (P : FinalExactLocalPackage) :
    PreservesRows P.equations.opposite.placeNext
      P.subset.rows.candidateRows.row :=
  P.toExactLocalTargetFields.oppositeRows

theorem noBlockedEndpointRow
    (P : FinalExactLocalPackage)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (P.subset.rows.candidateRows.row u v) :=
  P.toExactLocalTargetFields.noBlockedEndpointRow hblocked

theorem missingRowsBlocked
    (P : FinalExactLocalPackage) :
    Not (MissingViableCandidateRows P.subset.rows.candidateRows) :=
  P.toExactLocalTargetFields.missingRowsBlocked

theorem generatedTransitionsPreserveExactLocalSqDistances
    (P : FinalExactLocalPackage) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      P.equations.toFigure2TransitionObligations :=
  P.toExactLocalTargetFields.generatedTransitionsPreserveExactLocalSqDistances

end FinalExactLocalPackage

def finalExactLocalPackage
    (subset : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    FinalExactLocalPackage where
  subset := subset
  equations := equations
  remaining := remaining

def possibleRowsFinalExactLocalPackage
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    FinalExactLocalPackage :=
  finalExactLocalPackage
    possibleRowsCandidateRowSubsetFields equations remaining

def finalSourceLedger : FinalSourceLedger where
  candidateRows := CandidateRows
  candidateRowSubsetLedger := CandidateRowSubsetLedger
  candidateRowSubsetFields := CandidateRowSubsetFields
  endpointBlockerLedger := FinalEndpointBlockerLedger
  obstructionRows := ObstructionRowsLedger
  endpointShortcutRows := EndpointShortcutRow
  missingViableCandidateRows := MissingViableCandidateRows
  exactLocalTargetFields := ExactLocalTargetFields
  exactLocalFinalPackage := FinalExactLocalPackage
  sameOppositeEquationPackage := SameOppositeExactLocalEquationPackage
  remainingFields := fun S =>
    TransitionRemainingFields S.toSameOppositeCandidate
  transitionRouteFields := TransitionRouteFields
  roleEquationRouteFields := RoleEquationRouteFields
  transitionExactLocalRouteFields := TransitionExactLocalRouteFields

/-! ## Imported final ledgers -/

/-- Checked W11 ledgers imported by the final exact-local aggregate. -/
structure ImportedFinalLedgers where
  exactLocalClosure : ExactLocalClosureW11.Matrix
  exactLocalIntegrated : ExactLocalIntegratedW11.Matrix
  exactLocalTarget : ExactLocalTargetIntegratedW11.Matrix
  transitionTarget : TransitionTargetIntegratedW11.Matrix
  roleHingeFinal : RoleHingeFinalIntegratedW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

def importedFinalLedgers : ImportedFinalLedgers where
  exactLocalClosure := ExactLocalClosureW11.matrix
  exactLocalIntegrated := ExactLocalIntegratedW11.matrix
  exactLocalTarget := ExactLocalTargetIntegratedW11.matrix
  transitionTarget := TransitionTargetIntegratedW11.matrix
  roleHingeFinal := RoleHingeFinalIntegratedW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-! ## Package-dependent target routes -/

/-- Exact, eventual, and arbitrary target projections from one explicit
package shape. -/
structure ConditionalTargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

def exactLocalTargetTransitionProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_exactLocalTransition
      P.toExactLocalTargetFields
  eventualTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactLocalTransition
      P.toExactLocalTargetFields
  arbitraryTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalTransition
      P.toExactLocalTargetFields

def exactLocalTargetRoleHingeProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_exactLocalRoleHinge
      P.toExactLocalTargetFields
  eventualTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_exactLocalRoleHinge
      P.toExactLocalTargetFields
  arbitraryTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_exactLocalRoleHinge
      P.toExactLocalTargetFields

def transitionTargetAggregateProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
      P.toTransitionTargetRoutePackage
  eventualTarget := fun P =>
    TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
      P.toTransitionTargetRoutePackage
  arbitraryTarget := fun P =>
    TransitionTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
      P.toTransitionTargetRoutePackage

def roleHingeFinalCheckedProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    RoleHingeFinalIntegratedW11.exactTarget_of_exactLocalRouteFields
      P.toRoleHingeFinalExactLocalRouteFields
  eventualTarget := fun P =>
    RoleHingeFinalIntegratedW11.eventualTarget_of_exactLocalRouteFields
      P.toRoleHingeFinalExactLocalRouteFields
  arbitraryTarget := fun P =>
    RoleHingeFinalIntegratedW11.arbitraryTarget_of_exactLocalRouteFields
      P.toRoleHingeFinalExactLocalRouteFields

def roleHingeFinalReducedProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    RoleHingeFinalIntegratedW11.exactTarget_of_exactLocalReducedEquations
      P.equations P.remaining
  eventualTarget := fun P =>
    RoleHingeFinalIntegratedW11.eventualTarget_of_exactLocalReducedEquations
      P.equations P.remaining
  arbitraryTarget := fun P =>
    RoleHingeFinalIntegratedW11.arbitraryTarget_of_exactLocalReducedEquations
      P.equations P.remaining

def pachTothIntegratedTransitionProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteen_of_pachTothTransitionFacade
      P.toExactLocalTargetFields
  eventualTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_pachTothTransitionFacade
      P.toExactLocalTargetFields
  arbitraryTarget := fun P =>
    ExactLocalTargetIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_pachTothTransitionFacade
      P.toExactLocalTargetFields

/-- All final exact-local route projections remain package-dependent. -/
structure FinalTargetRoutes where
  exactLocalTransition :
    ConditionalTargetProjection FinalExactLocalPackage
  exactLocalRoleHinge :
    ConditionalTargetProjection FinalExactLocalPackage
  transitionTargetAggregate :
    ConditionalTargetProjection FinalExactLocalPackage
  roleHingeFinalChecked :
    ConditionalTargetProjection FinalExactLocalPackage
  roleHingeFinalReduced :
    ConditionalTargetProjection FinalExactLocalPackage
  pachTothIntegratedTransition :
    ConditionalTargetProjection FinalExactLocalPackage

def finalTargetRoutes : FinalTargetRoutes where
  exactLocalTransition := exactLocalTargetTransitionProjection
  exactLocalRoleHinge := exactLocalTargetRoleHingeProjection
  transitionTargetAggregate := transitionTargetAggregateProjection
  roleHingeFinalChecked := roleHingeFinalCheckedProjection
  roleHingeFinalReduced := roleHingeFinalReducedProjection
  pachTothIntegratedTransition := pachTothIntegratedTransitionProjection

/-! ## Final consistency witnesses -/

/-- Exact-local consistency witness imported from the final W11 consistency
ledger. -/
structure FinalConsistencyLedger where
  exactLocalRoute :
    forall P : FinalExactLocalPackage,
      PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
        P.equations P.remaining

def finalConsistencyLedger : FinalConsistencyLedger where
  exactLocalRoute := fun P =>
    PachTothW11FinalConsistency.matrix.consistency.exactLocalRoute
      (S := P.equations) P.remaining

/-! ## Final matrix -/

/-- Final exact-local aggregate matrix for W11. -/
structure Matrix where
  sources : FinalSourceLedger
  imported : ImportedFinalLedgers
  endpointBlockers : FinalEndpointBlockerLedger
  candidateRowSubsetFields :
    CandidateRowSubsetLedger -> CandidateRowSubsetFields
  possibleRows : CandidateRowSubsetFields
  targets : FinalTargetRoutes
  consistency : FinalConsistencyLedger

def matrix : Matrix where
  sources := finalSourceLedger
  imported := importedFinalLedgers
  endpointBlockers := finalEndpointBlockerLedger
  candidateRowSubsetFields := candidateRowSubsetFields
  possibleRows := possibleRowsCandidateRowSubsetFields
  targets := finalTargetRoutes
  consistency := finalConsistencyLedger

/-! ## Public candidate-row and endpoint projections -/

theorem candidateRows_project_to_w10
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hrow : F.rows.candidateRows.row u v) :
    W10PossibleRow u v :=
  F.candidateRows_project_to_w10 hrow

theorem candidateRows_project_to_w11
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hrow : F.rows.candidateRows.row u v) :
    PossibleRow u v :=
  F.candidateRows_project_to_w11 hrow

theorem candidateRows_exclude_blockedEndpoint
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (F.rows.candidateRows.row u v) :=
  F.noBlockedEndpointRow hblocked

theorem missingViableCandidateRows_blocked
    (F : CandidateRowSubsetFields) :
    Not (MissingViableCandidateRows F.rows.candidateRows) :=
  F.missingRowsBlocked

theorem endpointShortcut_not_possible
    (E : EndpointShortcutRow) :
    Not (PossibleRow E.u E.v) :=
  matrix.endpointBlockers.shortcutNotPossible E

theorem endpointShortcut_sameRows_blocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  matrix.endpointBlockers.shortcutSameRowsBlocked E hrow

theorem endpointShortcut_oppositeRows_blocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  matrix.endpointBlockers.shortcutOppositeRowsBlocked E hrow

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

/-! ## Public package and consistency projections -/

theorem package_sameRows
    (P : FinalExactLocalPackage) :
    PreservesRows P.equations.same.placeNext
      P.subset.rows.candidateRows.row :=
  P.sameRows

theorem package_oppositeRows
    (P : FinalExactLocalPackage) :
    PreservesRows P.equations.opposite.placeNext
      P.subset.rows.candidateRows.row :=
  P.oppositeRows

theorem package_missingRowsBlocked
    (P : FinalExactLocalPackage) :
    Not (MissingViableCandidateRows P.subset.rows.candidateRows) :=
  P.missingRowsBlocked

def exactLocalRouteConsistency
    (P : FinalExactLocalPackage) :
    PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
      P.equations P.remaining :=
  matrix.consistency.exactLocalRoute P

/-! ## Public target projections -/

theorem exactTarget_of_finalExactLocalPackage
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.exactLocalTransition.exactTarget P

theorem eventualTarget_of_finalExactLocalPackage
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.exactLocalTransition.eventualTarget P

theorem arbitraryTarget_of_finalExactLocalPackage
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.exactLocalTransition.arbitraryTarget P

theorem exactTarget_via_exactLocalRoleHinge
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.exactLocalRoleHinge.exactTarget P

theorem eventualTarget_via_exactLocalRoleHinge
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.exactLocalRoleHinge.eventualTarget P

theorem arbitraryTarget_via_exactLocalRoleHinge
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.exactLocalRoleHinge.arbitraryTarget P

theorem exactTarget_via_transitionTargetAggregate
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.transitionTargetAggregate.exactTarget P

theorem eventualTarget_via_transitionTargetAggregate
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.transitionTargetAggregate.eventualTarget P

theorem arbitraryTarget_via_transitionTargetAggregate
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.transitionTargetAggregate.arbitraryTarget P

theorem exactTarget_via_roleHingeFinalChecked
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.roleHingeFinalChecked.exactTarget P

theorem eventualTarget_via_roleHingeFinalChecked
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.roleHingeFinalChecked.eventualTarget P

theorem arbitraryTarget_via_roleHingeFinalChecked
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.roleHingeFinalChecked.arbitraryTarget P

theorem exactTarget_via_roleHingeFinalReduced
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.roleHingeFinalReduced.exactTarget P

theorem eventualTarget_via_roleHingeFinalReduced
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.roleHingeFinalReduced.eventualTarget P

theorem arbitraryTarget_via_roleHingeFinalReduced
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.roleHingeFinalReduced.arbitraryTarget P

theorem exactTarget_via_pachTothIntegratedTransition
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.pachTothIntegratedTransition.exactTarget P

theorem eventualTarget_via_pachTothIntegratedTransition
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.pachTothIntegratedTransition.eventualTarget P

theorem arbitraryTarget_via_pachTothIntegratedTransition
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.pachTothIntegratedTransition.arbitraryTarget P

theorem exactTarget_of_possibleRowsFinalExactLocalPackage
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ExactTarget :=
  exactTarget_of_finalExactLocalPackage
    (possibleRowsFinalExactLocalPackage equations remaining)

theorem eventualTarget_of_possibleRowsFinalExactLocalPackage
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    EventualTarget :=
  eventualTarget_of_finalExactLocalPackage
    (possibleRowsFinalExactLocalPackage equations remaining)

theorem arbitraryTarget_of_possibleRowsFinalExactLocalPackage
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ArbitraryTarget :=
  arbitraryTarget_of_finalExactLocalPackage
    (possibleRowsFinalExactLocalPackage equations remaining)

end

end ExactLocalFinalIntegratedW11
end PachToth
end ErdosProblems1066
