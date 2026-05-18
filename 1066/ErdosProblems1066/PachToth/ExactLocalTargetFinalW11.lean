import ErdosProblems1066.PachToth.ExactLocalFinalIntegratedW11
import ErdosProblems1066.PachToth.ExactLocalTargetIntegratedW11
import ErdosProblems1066.PachToth.TransitionFinalIntegratedW11
import ErdosProblems1066.PachToth.RoleHingeFinalIntegratedW11
import ErdosProblems1066.PachToth.PachTothW11FinalConsistency

set_option autoImplicit false

/-!
# W11 final exact-local target consistency

This target-facing layer keeps the exact-local row fields, endpoint shortcut
blockers, final route packages, and W11 consistency witnesses in one record.
Every target projection below is a function of an explicit exact-local package.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalTargetFinalW11

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

universe u

abbrev ExactTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteen

abbrev EventualTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenEventually

abbrev ArbitraryTarget : Prop :=
  PachToth.targetUpperConstructionFiveSixteenArbitrary

abbrev CandidateRows :=
  ExactLocalFinalIntegratedW11.CandidateRows

abbrev CandidateRowSubsetLedger :=
  ExactLocalFinalIntegratedW11.CandidateRowSubsetLedger

abbrev ObstructionRowsLedger :=
  ExactLocalFinalIntegratedW11.ObstructionRowsLedger

abbrev ConcreteEndpointShortcutLedger :=
  ExactLocalFinalIntegratedW11.ConcreteEndpointShortcutLedger

abbrev EndpointShortcutRow :=
  ExactLocalFinalIntegratedW11.EndpointShortcutRow

abbrev MissingViableCandidateRows :=
  ExactLocalFinalIntegratedW11.MissingViableCandidateRows

abbrev PossibleRow :=
  ExactLocalFinalIntegratedW11.PossibleRow

abbrev W10PossibleRow :=
  ExactLocalFinalIntegratedW11.W10PossibleRow

abbrev PreservesRows :=
  ExactLocalFinalIntegratedW11.PreservesRows

abbrev SameOppositeExactLocalEquationPackage :=
  ExactLocalFinalIntegratedW11.SameOppositeExactLocalEquationPackage

abbrev SameOppositeCandidate :=
  ExactLocalFinalIntegratedW11.SameOppositeCandidate

abbrev TransitionRemainingFields
    (T : SameOppositeCandidate) :=
  ExactLocalFinalIntegratedW11.TransitionRemainingFields T

abbrev CandidateSubsetRouteFields :=
  ExactLocalFinalIntegratedW11.CandidateSubsetRouteFields

abbrev ExactLocalTargetFields :=
  ExactLocalFinalIntegratedW11.ExactLocalTargetFields

abbrev TransitionRouteFields :=
  ExactLocalFinalIntegratedW11.TransitionRouteFields

abbrev RoleEquationRouteFields :=
  ExactLocalFinalIntegratedW11.RoleEquationRouteFields

abbrev TransitionExactLocalRouteFields :=
  ExactLocalFinalIntegratedW11.TransitionExactLocalRouteFields

abbrev CandidateRowSubsetFields :=
  ExactLocalFinalIntegratedW11.CandidateRowSubsetFields

abbrev FinalEndpointBlockerLedger :=
  ExactLocalFinalIntegratedW11.FinalEndpointBlockerLedger

abbrev FinalExactLocalPackage :=
  ExactLocalFinalIntegratedW11.FinalExactLocalPackage

abbrev IsW11BlockedEndpointRow :=
  ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow

/-! ## Explicit row and endpoint fields -/

/-- Candidate-row data retained by the final target layer. -/
structure CandidateRowFields where
  rows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  endpointShortcuts : ConcreteEndpointShortcutLedger
  projectsToW10 :
    forall {u v : LocalVertex}, rows.candidateRows.row u v ->
      W10PossibleRow u v
  projectsToW11 :
    forall {u v : LocalVertex}, rows.candidateRows.row u v ->
      PossibleRow u v
  sameRows :
    PreservesRows RoleHingeConcreteSearch.samePlaceNext
      rows.candidateRows.row
  oppositeRows :
    PreservesRows RoleHingeConcreteSearch.oppositePlaceNext
      rows.candidateRows.row
  noBlockedEndpointRow :
    forall {u v : LocalVertex}, IsW11BlockedEndpointRow u v ->
      Not (rows.candidateRows.row u v)
  missingRowsBlocked :
    Not (MissingViableCandidateRows rows.candidateRows)

/-- Endpoint shortcut blockers retained by the final target layer. -/
structure EndpointBlockerFields where
  integratedLedger : ExactLocalTargetIntegratedW11.EndpointBlockerLedger
  finalLedger : FinalEndpointBlockerLedger
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

def candidateRowFields
    (F : CandidateRowSubsetFields) :
    CandidateRowFields where
  rows := F.rows
  obstructions := F.obstructions
  endpointShortcuts := F.endpointShortcuts
  projectsToW10 := fun hrow =>
    ExactLocalFinalIntegratedW11.candidateRows_project_to_w10 F hrow
  projectsToW11 := fun hrow =>
    ExactLocalFinalIntegratedW11.candidateRows_project_to_w11 F hrow
  sameRows := F.sameRows
  oppositeRows := F.oppositeRows
  noBlockedEndpointRow := fun hblocked =>
    F.noBlockedEndpointRow hblocked
  missingRowsBlocked := F.missingRowsBlocked

def possibleRowsCandidateRowFields : CandidateRowFields :=
  candidateRowFields ExactLocalFinalIntegratedW11.matrix.possibleRows

def endpointBlockerFields : EndpointBlockerFields where
  integratedLedger := ExactLocalTargetIntegratedW11.endpointBlockerLedger
  finalLedger := ExactLocalFinalIntegratedW11.finalEndpointBlockerLedger
  endpointShortcuts :=
    ExactLocalFinalIntegratedW11.finalEndpointBlockerLedger.endpointShortcuts
  shortcutNotPossible :=
    ExactLocalFinalIntegratedW11.endpointShortcut_not_possible
  shortcutSameRowsBlocked :=
    ExactLocalFinalIntegratedW11.endpointShortcut_sameRows_blocked
  shortcutOppositeRowsBlocked :=
    ExactLocalFinalIntegratedW11.endpointShortcut_oppositeRows_blocked
  pUpperForward :=
    ExactLocalFinalIntegratedW11.pUpperForward_endpointShortcut_not_possible
  pUpperReverse :=
    ExactLocalFinalIntegratedW11.pUpperReverse_endpointShortcut_not_possible
  pLowerForward :=
    ExactLocalFinalIntegratedW11.pLowerForward_endpointShortcut_not_possible
  pLowerReverse :=
    ExactLocalFinalIntegratedW11.pLowerReverse_endpointShortcut_not_possible
  qUpperForward :=
    ExactLocalFinalIntegratedW11.qUpperForward_endpointShortcut_not_possible
  qUpperReverse :=
    ExactLocalFinalIntegratedW11.qUpperReverse_endpointShortcut_not_possible
  qLowerForward :=
    ExactLocalFinalIntegratedW11.qLowerForward_endpointShortcut_not_possible
  qLowerReverse :=
    ExactLocalFinalIntegratedW11.qLowerReverse_endpointShortcut_not_possible

namespace FinalExactLocalPackage

def candidateRows
    (P : FinalExactLocalPackage) :
    CandidateRowFields :=
  candidateRowFields P.subset

def endpointBlockers
    (_P : FinalExactLocalPackage) :
    EndpointBlockerFields :=
  endpointBlockerFields

end FinalExactLocalPackage

/-! ## Explicit package builders -/

def finalExactLocalPackage
    (subset : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    FinalExactLocalPackage :=
  ExactLocalFinalIntegratedW11.finalExactLocalPackage
    subset equations remaining

def possibleRowsFinalExactLocalPackage
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    FinalExactLocalPackage :=
  ExactLocalFinalIntegratedW11.possibleRowsFinalExactLocalPackage
    equations remaining

def toTransitionFinalRoutePackage
    (P : FinalExactLocalPackage) :
    TransitionFinalIntegratedW11.RoutePackage :=
  TransitionFinalIntegratedW11.RoutePackage.exactLocalIntegratedTransition
    P.toExactLocalTargetFields

def toTransitionFinalFacadePackage
    (P : FinalExactLocalPackage) :
    TransitionFinalIntegratedW11.RoutePackage :=
  TransitionFinalIntegratedW11.RoutePackage.exactLocalTransitionFacade
    P.toExactLocalTargetFields

def toTransitionFinalPachTothPackage
    (P : FinalExactLocalPackage) :
    TransitionFinalIntegratedW11.RoutePackage :=
  TransitionFinalIntegratedW11.RoutePackage.exactLocalPachTothTransitionFacade
    P.toExactLocalTargetFields

def toRoleHingeFinalExactLocalRouteFields
    (P : FinalExactLocalPackage) :
    RoleHingeFinalIntegratedW11.ExactLocalRouteFields :=
  P.toRoleHingeFinalExactLocalRouteFields

/-! ## Conditional target projections -/

/-- Exact, eventual, and arbitrary target projections from one input package. -/
structure ConditionalTargetProjection (alpha : Sort u) : Sort (max 1 u) where
  exactTarget : alpha -> ExactTarget
  eventualTarget : alpha -> EventualTarget
  arbitraryTarget : alpha -> ArbitraryTarget

namespace ConditionalTargetProjection

def ofExactLocalFinal
    {alpha : Sort u}
    (R : ExactLocalFinalIntegratedW11.ConditionalTargetProjection alpha) :
    ConditionalTargetProjection alpha where
  exactTarget := R.exactTarget
  eventualTarget := R.eventualTarget
  arbitraryTarget := R.arbitraryTarget

end ConditionalTargetProjection

def exactLocalFinalTransitionProjection :
    ConditionalTargetProjection FinalExactLocalPackage :=
  ConditionalTargetProjection.ofExactLocalFinal
    ExactLocalFinalIntegratedW11.matrix.targets.exactLocalTransition

def exactLocalFinalRoleHingeProjection :
    ConditionalTargetProjection FinalExactLocalPackage :=
  ConditionalTargetProjection.ofExactLocalFinal
    ExactLocalFinalIntegratedW11.matrix.targets.exactLocalRoleHinge

def exactLocalFinalTransitionTargetProjection :
    ConditionalTargetProjection FinalExactLocalPackage :=
  ConditionalTargetProjection.ofExactLocalFinal
    ExactLocalFinalIntegratedW11.matrix.targets.transitionTargetAggregate

def roleHingeFinalCheckedProjection :
    ConditionalTargetProjection FinalExactLocalPackage :=
  ConditionalTargetProjection.ofExactLocalFinal
    ExactLocalFinalIntegratedW11.matrix.targets.roleHingeFinalChecked

def roleHingeFinalReducedProjection :
    ConditionalTargetProjection FinalExactLocalPackage :=
  ConditionalTargetProjection.ofExactLocalFinal
    ExactLocalFinalIntegratedW11.matrix.targets.roleHingeFinalReduced

def pachTothIntegratedTransitionProjection :
    ConditionalTargetProjection FinalExactLocalPackage :=
  ConditionalTargetProjection.ofExactLocalFinal
    ExactLocalFinalIntegratedW11.matrix.targets.pachTothIntegratedTransition

def transitionFinalRouteProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
      (toTransitionFinalRoutePackage P)
  eventualTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
      (toTransitionFinalRoutePackage P)
  arbitraryTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
      (toTransitionFinalRoutePackage P)

def transitionFinalFacadeProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
      (toTransitionFinalFacadePackage P)
  eventualTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
      (toTransitionFinalFacadePackage P)
  arbitraryTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
      (toTransitionFinalFacadePackage P)

def transitionFinalPachTothProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteen_of_routePackage
      (toTransitionFinalPachTothPackage P)
  eventualTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenEventually_of_routePackage
      (toTransitionFinalPachTothPackage P)
  arbitraryTarget := fun P =>
    TransitionFinalIntegratedW11.targetUpperConstructionFiveSixteenArbitrary_of_routePackage
      (toTransitionFinalPachTothPackage P)

def roleHingeFinalRouteFieldsProjection :
    ConditionalTargetProjection FinalExactLocalPackage where
  exactTarget := fun P =>
    RoleHingeFinalIntegratedW11.exactTarget_of_exactLocalRouteFields
      (toRoleHingeFinalExactLocalRouteFields P)
  eventualTarget := fun P =>
    RoleHingeFinalIntegratedW11.eventualTarget_of_exactLocalRouteFields
      (toRoleHingeFinalExactLocalRouteFields P)
  arbitraryTarget := fun P =>
    RoleHingeFinalIntegratedW11.arbitraryTarget_of_exactLocalRouteFields
      (toRoleHingeFinalExactLocalRouteFields P)

/-! ## Consistency witnesses -/

/-- W11 agreement witness for each exact-local package. -/
structure FinalConsistencyWitnesses where
  exactLocalRoute :
    forall P : FinalExactLocalPackage,
      PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
        P.equations P.remaining

def finalConsistencyWitnesses : FinalConsistencyWitnesses where
  exactLocalRoute := fun P =>
    PachTothW11FinalConsistency.matrix.consistency.exactLocalRoute
      (S := P.equations) P.remaining

/-! ## Final matrix -/

/-- Input and package shapes exposed by this final target layer. -/
structure ExplicitFieldLedger where
  candidateRows : Type
  candidateRowSubsets : Type
  candidateRowFields : Type
  endpointBlockerFields : Type
  exactLocalTargetFields : Type
  finalExactLocalPackages : Type
  sameOppositeEquationPackages : Type
  transitionRemainingFields :
    forall _ : SameOppositeExactLocalEquationPackage, Type
  transitionRouteFields : Type
  roleEquationRouteFields : Type
  transitionExactLocalRouteFields : Type

def explicitFieldLedger : ExplicitFieldLedger where
  candidateRows := CandidateRows
  candidateRowSubsets := CandidateRowSubsetLedger
  candidateRowFields := CandidateRowFields
  endpointBlockerFields := EndpointBlockerFields
  exactLocalTargetFields := ExactLocalTargetFields
  finalExactLocalPackages := FinalExactLocalPackage
  sameOppositeEquationPackages := SameOppositeExactLocalEquationPackage
  transitionRemainingFields := fun S =>
    TransitionRemainingFields S.toSameOppositeCandidate
  transitionRouteFields := TransitionRouteFields
  roleEquationRouteFields := RoleEquationRouteFields
  transitionExactLocalRouteFields := TransitionExactLocalRouteFields

/-- Checked ledgers imported by this final target layer. -/
structure ImportedLedgers where
  exactLocalFinal : ExactLocalFinalIntegratedW11.Matrix
  exactLocalTarget : ExactLocalTargetIntegratedW11.Matrix
  transitionFinal : TransitionFinalIntegratedW11.Matrix
  roleHingeFinal : RoleHingeFinalIntegratedW11.Matrix
  pachTothFinalConsistency : PachTothW11FinalConsistency.Matrix

def importedLedgers : ImportedLedgers where
  exactLocalFinal := ExactLocalFinalIntegratedW11.matrix
  exactLocalTarget := ExactLocalTargetIntegratedW11.matrix
  transitionFinal := TransitionFinalIntegratedW11.matrix
  roleHingeFinal := RoleHingeFinalIntegratedW11.matrix
  pachTothFinalConsistency := PachTothW11FinalConsistency.matrix

/-- Conditional target routes retained by the final exact-local target layer. -/
structure TargetProjectionLedger where
  exactLocalTransition :
    ConditionalTargetProjection FinalExactLocalPackage
  exactLocalRoleHinge :
    ConditionalTargetProjection FinalExactLocalPackage
  exactLocalTransitionTarget :
    ConditionalTargetProjection FinalExactLocalPackage
  transitionFinalRoute :
    ConditionalTargetProjection FinalExactLocalPackage
  transitionFinalFacade :
    ConditionalTargetProjection FinalExactLocalPackage
  transitionFinalPachToth :
    ConditionalTargetProjection FinalExactLocalPackage
  roleHingeFinalChecked :
    ConditionalTargetProjection FinalExactLocalPackage
  roleHingeFinalRouteFields :
    ConditionalTargetProjection FinalExactLocalPackage
  roleHingeFinalReduced :
    ConditionalTargetProjection FinalExactLocalPackage
  pachTothIntegratedTransition :
    ConditionalTargetProjection FinalExactLocalPackage

def targetProjectionLedger : TargetProjectionLedger where
  exactLocalTransition := exactLocalFinalTransitionProjection
  exactLocalRoleHinge := exactLocalFinalRoleHingeProjection
  exactLocalTransitionTarget := exactLocalFinalTransitionTargetProjection
  transitionFinalRoute := transitionFinalRouteProjection
  transitionFinalFacade := transitionFinalFacadeProjection
  transitionFinalPachToth := transitionFinalPachTothProjection
  roleHingeFinalChecked := roleHingeFinalCheckedProjection
  roleHingeFinalRouteFields := roleHingeFinalRouteFieldsProjection
  roleHingeFinalReduced := roleHingeFinalReducedProjection
  pachTothIntegratedTransition := pachTothIntegratedTransitionProjection

/-- Final exact-local target consistency matrix. -/
structure Matrix where
  fields : ExplicitFieldLedger
  imports : ImportedLedgers
  candidateRows :
    CandidateRowSubsetFields -> CandidateRowFields
  possibleRows : CandidateRowFields
  endpointBlockers : EndpointBlockerFields
  targets : TargetProjectionLedger
  consistency : FinalConsistencyWitnesses

def matrix : Matrix where
  fields := explicitFieldLedger
  imports := importedLedgers
  candidateRows := candidateRowFields
  possibleRows := possibleRowsCandidateRowFields
  endpointBlockers := endpointBlockerFields
  targets := targetProjectionLedger
  consistency := finalConsistencyWitnesses

theorem matrix_nonempty : Nonempty Matrix :=
  Nonempty.intro matrix

/-! ## Public row and endpoint projections -/

theorem candidateRows_project_to_w10
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hrow : F.rows.candidateRows.row u v) :
    W10PossibleRow u v :=
  (matrix.candidateRows F).projectsToW10 hrow

theorem candidateRows_project_to_w11
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hrow : F.rows.candidateRows.row u v) :
    PossibleRow u v :=
  (matrix.candidateRows F).projectsToW11 hrow

theorem candidateRows_exclude_blockedEndpoint
    (F : CandidateRowSubsetFields)
    {u v : LocalVertex}
    (hblocked : IsW11BlockedEndpointRow u v) :
    Not (F.rows.candidateRows.row u v) :=
  (matrix.candidateRows F).noBlockedEndpointRow hblocked

theorem missingViableCandidateRows_blocked
    (F : CandidateRowSubsetFields) :
    Not (MissingViableCandidateRows F.rows.candidateRows) :=
  (matrix.candidateRows F).missingRowsBlocked

theorem package_candidateRows_project_to_w11
    (P : FinalExactLocalPackage)
    {u v : LocalVertex}
    (hrow : P.subset.rows.candidateRows.row u v) :
    PossibleRow u v :=
  P.candidateRows.projectsToW11 hrow

theorem package_missingRowsBlocked
    (P : FinalExactLocalPackage) :
    Not (MissingViableCandidateRows P.subset.rows.candidateRows) :=
  P.candidateRows.missingRowsBlocked

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

/-! ## Public consistency and target projections -/

def exactLocalRouteConsistency
    (P : FinalExactLocalPackage) :
    PachTothW11ConsistencyMatrix.ExactLocalRouteConsistency
      P.equations P.remaining :=
  matrix.consistency.exactLocalRoute P

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

theorem exactTarget_via_transitionTarget
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.exactLocalTransitionTarget.exactTarget P

theorem eventualTarget_via_transitionTarget
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.exactLocalTransitionTarget.eventualTarget P

theorem arbitraryTarget_via_transitionTarget
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.exactLocalTransitionTarget.arbitraryTarget P

theorem exactTarget_via_transitionFinalRoute
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.transitionFinalRoute.exactTarget P

theorem eventualTarget_via_transitionFinalRoute
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.transitionFinalRoute.eventualTarget P

theorem arbitraryTarget_via_transitionFinalRoute
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.transitionFinalRoute.arbitraryTarget P

theorem exactTarget_via_transitionFinalFacade
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.transitionFinalFacade.exactTarget P

theorem eventualTarget_via_transitionFinalFacade
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.transitionFinalFacade.eventualTarget P

theorem arbitraryTarget_via_transitionFinalFacade
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.transitionFinalFacade.arbitraryTarget P

theorem exactTarget_via_transitionFinalPachToth
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.transitionFinalPachToth.exactTarget P

theorem eventualTarget_via_transitionFinalPachToth
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.transitionFinalPachToth.eventualTarget P

theorem arbitraryTarget_via_transitionFinalPachToth
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.transitionFinalPachToth.arbitraryTarget P

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

theorem exactTarget_via_roleHingeFinalRouteFields
    (P : FinalExactLocalPackage) :
    ExactTarget :=
  matrix.targets.roleHingeFinalRouteFields.exactTarget P

theorem eventualTarget_via_roleHingeFinalRouteFields
    (P : FinalExactLocalPackage) :
    EventualTarget :=
  matrix.targets.roleHingeFinalRouteFields.eventualTarget P

theorem arbitraryTarget_via_roleHingeFinalRouteFields
    (P : FinalExactLocalPackage) :
    ArbitraryTarget :=
  matrix.targets.roleHingeFinalRouteFields.arbitraryTarget P

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

theorem exactTarget_of_candidateRowSubsetFields
    (F : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ExactTarget :=
  exactTarget_of_finalExactLocalPackage
    (finalExactLocalPackage F equations remaining)

theorem eventualTarget_of_candidateRowSubsetFields
    (F : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    EventualTarget :=
  eventualTarget_of_finalExactLocalPackage
    (finalExactLocalPackage F equations remaining)

theorem arbitraryTarget_of_candidateRowSubsetFields
    (F : CandidateRowSubsetFields)
    (equations : SameOppositeExactLocalEquationPackage)
    (remaining :
      TransitionRemainingFields equations.toSameOppositeCandidate) :
    ArbitraryTarget :=
  arbitraryTarget_of_finalExactLocalPackage
    (finalExactLocalPackage F equations remaining)

end

end ExactLocalTargetFinalW11
end PachToth
end ErdosProblems1066
