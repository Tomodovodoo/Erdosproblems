import ErdosProblems1066.PachToth.ExactLocalObstructionMatrixW11
import ErdosProblems1066.PachToth.RoleHingePolynomialReductionW11
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.ExactLocalObstructionExpansionW10

set_option autoImplicit false

/-!
# W11 exact-local closure ledger

This module records how the checked exact-local row matrix feeds the W11
transition and candidate surfaces.

The file does not add an unconditional Pach--Toth construction.  Candidate row
subsets are kept as filtered row data, full W11 candidates still require an
explicit exact-local completion, and the concrete endpoint shortcuts blocked
by the current four-target maps are named one by one.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ExactLocalClosureW11

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real

abbrev PossibleRow :=
  ExactLocalObstructionMatrixW11.PossibleRow

abbrev W10PossibleRow :=
  ExactLocalObstructionExpansionW10.PossibleRow

abbrev CandidateRows :=
  ExactLocalObstructionMatrixW11.ExactLocalCandidateRows

abbrev PreservesRows :=
  ExactLocalObstructionMatrixW11.PreservesRows

abbrev ExactBaseRowContradiction :=
  ExactLocalObstructionMatrixW11.ExactBaseRowContradiction

abbrev BranchCandidate :=
  FlexibleTransitionSearchW11.BranchCandidate

abbrev SameOppositeCandidate :=
  FlexibleTransitionSearchW11.SameOppositeCandidate

abbrev TransitionRemainingFields
    (T : SameOppositeCandidate) :=
  FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields T

abbrev TransitionRouteFields :=
  FlexibleTransitionSearchW11.NonRigidRouteFields

abbrev ExactLocalEquationPackage :=
  RoleHingePolynomialReductionW11.ExactLocalEquationPackage

abbrev SameOppositeExactLocalEquationPackage :=
  RoleHingePolynomialReductionW11.SameOppositeExactLocalEquationPackage

/-! ## Candidate row subsets -/

/-- A ledger row for any requested subset of the checked exact-local matrix. -/
structure CandidateRowSubsetLedger where
  candidateRows : CandidateRows
  projectsToW10 :
    forall {u v : LocalVertex}, candidateRows.row u v ->
      W10PossibleRow u v
  projectsToW11 :
    forall {u v : LocalVertex}, candidateRows.row u v ->
      PossibleRow u v
  samePreserves :
    PreservesRows RoleHingeConcreteSearch.samePlaceNext
      candidateRows.row
  oppositePreserves :
    PreservesRows RoleHingeConcreteSearch.oppositePlaceNext
      candidateRows.row
  excludesBlocked :
    forall {u v : LocalVertex},
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v ->
        Not (candidateRows.row u v)

/-- Build the row-subset ledger from the W11 candidate-row interface. -/
def candidateRowSubsetLedger
    (C : CandidateRows) :
    CandidateRowSubsetLedger where
  candidateRows := C
  projectsToW10 := fun hrow => C.projects_to_w10 hrow
  projectsToW11 := fun hrow =>
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.possible C hrow
  samePreserves :=
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.samePlaceNext_preservesRows C
  oppositePreserves :=
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.oppositePlaceNext_preservesRows C
  excludesBlocked := fun hblocked =>
    ExactLocalObstructionMatrixW11.candidateRows_exclude_blockedEndpointRow
      C hblocked

/-- The maximal currently checked row subset: every W11 possible row. -/
def possibleRowsSubsetLedger : CandidateRowSubsetLedger :=
  candidateRowSubsetLedger
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.possibleRows

namespace CandidateRowSubsetLedger

theorem same_sqDist
    (L : CandidateRowSubsetLedger)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : L.candidateRows.row u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.samePlaceNext source u)
        (RoleHingeConcreteSearch.samePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  L.samePreserves source hsource u v hrow

theorem opposite_sqDist
    (L : CandidateRowSubsetLedger)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hrow : L.candidateRows.row u v) :
    RoleHingeSameBlockAlgebra.sqDist
        (RoleHingeConcreteSearch.oppositePlaceNext source u)
        (RoleHingeConcreteSearch.oppositePlaceNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  L.oppositePreserves source hsource u v hrow

theorem no_blocked_row
    (L : CandidateRowSubsetLedger)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (L.candidateRows.row u v) :=
  L.excludesBlocked hblocked

end CandidateRowSubsetLedger

/-! ## Explicit missing completion rows -/

/-- The rows still missing if one tries to upgrade a filtered concrete row
subset to full exact-local preservation for the current concrete maps. -/
structure ConcreteMissingCandidateRows
    (C : CandidateRows) where
  sameMissing :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (C.row u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.samePlaceNext source u)
                (RoleHingeConcreteSearch.samePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4
  oppositeMissing :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (C.row u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (RoleHingeConcreteSearch.oppositePlaceNext source u)
                (RoleHingeConcreteSearch.oppositePlaceNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

namespace ConcreteMissingCandidateRows

theorem sameFullExactLocal
    {C : CandidateRows}
    (M : ConcreteMissingCandidateRows C) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      RoleHingeConcreteSearch.samePlaceNext := by
  intro source hsource u v
  classical
  exact
    if hrow : C.row u v then
      ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.samePlaceNext_preservesRows
        C source hsource u v hrow
    else
      M.sameMissing source hsource u v hrow

theorem oppositeFullExactLocal
    {C : CandidateRows}
    (M : ConcreteMissingCandidateRows C) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      RoleHingeConcreteSearch.oppositePlaceNext := by
  intro source hsource u v
  classical
  exact
    if hrow : C.row u v then
      ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.oppositePlaceNext_preservesRows
        C source hsource u v hrow
    else
      M.oppositeMissing source hsource u v hrow

end ConcreteMissingCandidateRows

/-- The missing-row completion is visible and cannot be filled by the current
concrete four-target same map. -/
theorem noConcreteMissingCandidateRows
    (C : CandidateRows) :
    Not (ConcreteMissingCandidateRows C) := by
  intro M
  exact
    ExactLocalBranchSolverSurface.samePlaceNext_not_preservesExactLocalSqDistances
      M.sameFullExactLocal

/-! ## Full candidate interfaces -/

/-- A full W11 branch candidate preserves any checked row subset. -/
theorem branchCandidate_preservesCandidateRows
    (B : BranchCandidate)
    (C : CandidateRows) :
    PreservesRows B.placeNext C.row := by
  intro source hsource u v _hrow
  exact B.preserves_exactLocal_sqDistances source hsource u v

/-- A full W11 same/opposite candidate carries any checked row subset. -/
structure CandidateRowsInW11Candidate
    (C : CandidateRows) where
  candidate : SameOppositeCandidate
  sameRows : PreservesRows candidate.same.placeNext C.row
  oppositeRows : PreservesRows candidate.opposite.placeNext C.row

namespace CandidateRowsInW11Candidate

/-- Build the row ledger from an already completed W11 candidate. -/
def ofCandidate
    (C : CandidateRows)
    (T : SameOppositeCandidate) :
    CandidateRowsInW11Candidate C where
  candidate := T
  sameRows := branchCandidate_preservesCandidateRows T.same C
  oppositeRows := branchCandidate_preservesCandidateRows T.opposite C

end CandidateRowsInW11Candidate

/-- A reduced exact-local equation package produces a W11 branch candidate. -/
def exactLocalEquationPackage_toBranchCandidate
    (B : ExactLocalEquationPackage) :
    BranchCandidate :=
  B.toBranchCandidate

/-- Reduced branch equations preserve any checked row subset. -/
theorem exactLocalEquationPackage_preservesCandidateRows
    (B : ExactLocalEquationPackage)
    (C : CandidateRows) :
    PreservesRows B.placeNext C.row := by
  intro source hsource u v _hrow
  exact B.preservesExactLocalSqDistances source hsource u v

/-- A reduced same/opposite equation package produces a W11 candidate. -/
def sameOppositeEquationPackage_toCandidate
    (S : SameOppositeExactLocalEquationPackage) :
    SameOppositeCandidate :=
  S.toSameOppositeCandidate

/-- Row-subset ledger for a reduced same/opposite equation package. -/
def sameOppositeEquationPackage_rowsInCandidate
    (S : SameOppositeExactLocalEquationPackage)
    (C : CandidateRows) :
    CandidateRowsInW11Candidate C :=
  CandidateRowsInW11Candidate.ofCandidate C
    S.toSameOppositeCandidate

/-- Package a reduced same/opposite equation package with its still explicit
period and metric fields into the W11 route interface. -/
def sameOppositeEquationPackage_toRouteFields
    (S : SameOppositeExactLocalEquationPackage)
    (R : TransitionRemainingFields S.toSameOppositeCandidate) :
    TransitionRouteFields where
  candidate := S.toSameOppositeCandidate
  remaining := R

theorem targetUpperConstructionFiveSixteen_of_sameOppositeEquationPackage
    (S : SameOppositeExactLocalEquationPackage)
    (R : TransitionRemainingFields S.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (sameOppositeEquationPackage_toRouteFields S R).targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_sameOppositeEquationPackage
    (S : SameOppositeExactLocalEquationPackage)
    (R : TransitionRemainingFields S.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (sameOppositeEquationPackage_toRouteFields S R).targetUpperConstructionFiveSixteenArbitrary

/-! ## Concrete endpoint shortcut blockers -/

/-- One concrete endpoint shortcut that is both outside the checked row matrix
and inconsistent with the current same/opposite maps on the exact base. -/
structure EndpointShortcutRow where
  u : LocalVertex
  v : LocalVertex
  notPossible : Not (PossibleRow u v)
  sameExactBase :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.samePlaceNext u v
  oppositeExactBase :
    ExactBaseRowContradiction
      RoleHingeConcreteSearch.oppositePlaceNext u v

namespace EndpointShortcutRow

theorem sameRowsBlocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow E.sameExactBase

theorem oppositeRowsBlocked
    (E : EndpointShortcutRow)
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row E.u E.v) :
    Not
      (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  ExactLocalBranchSolverSurface.not_preservesRows_of_exactBaseRowContradiction
    hrow E.oppositeExactBase

end EndpointShortcutRow

def endpointShortcut_T2_2_T1_1 : EndpointShortcutRow where
  u := T2_2
  v := T1_1
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T2_2_T1_1
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T2_2_T1_1_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T2_2_T1_1_exactBaseContradiction

def endpointShortcut_T1_1_T2_2 : EndpointShortcutRow where
  u := T1_1
  v := T2_2
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T1_1_T2_2
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T1_1_T2_2_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T1_1_T2_2_exactBaseContradiction

def endpointShortcut_T2_2_T1_2 : EndpointShortcutRow where
  u := T2_2
  v := T1_2
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T2_2_T1_2
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T2_2_T1_2_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T2_2_T1_2_exactBaseContradiction

def endpointShortcut_T1_2_T2_2 : EndpointShortcutRow where
  u := T1_2
  v := T2_2
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T1_2_T2_2
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T1_2_T2_2_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T1_2_T2_2_exactBaseContradiction

def endpointShortcut_T4_0_T0_0 : EndpointShortcutRow where
  u := T4_0
  v := T0_0
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T4_0_T0_0
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T4_0_T0_0_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T4_0_T0_0_exactBaseContradiction

def endpointShortcut_T0_0_T4_0 : EndpointShortcutRow where
  u := T0_0
  v := T4_0
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T0_0_T4_0
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T0_0_T4_0_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T0_0_T4_0_exactBaseContradiction

def endpointShortcut_T4_0_T0_2 : EndpointShortcutRow where
  u := T4_0
  v := T0_2
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T4_0_T0_2
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T4_0_T0_2_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T4_0_T0_2_exactBaseContradiction

def endpointShortcut_T0_2_T4_0 : EndpointShortcutRow where
  u := T0_2
  v := T4_0
  notPossible :=
    ExactLocalObstructionMatrixW11.not_possible_T0_2_T4_0
  sameExactBase :=
    ExactLocalObstructionMatrixW11.samePlaceNext_T0_2_T4_0_exactBaseContradiction
  oppositeExactBase :=
    ExactLocalObstructionMatrixW11.oppositePlaceNext_T0_2_T4_0_exactBaseContradiction

/-- All concrete connector-endpoint shortcuts known to be impossible here. -/
structure ConcreteEndpointShortcutLedger where
  pUpperForward : EndpointShortcutRow
  pUpperReverse : EndpointShortcutRow
  pLowerForward : EndpointShortcutRow
  pLowerReverse : EndpointShortcutRow
  qUpperForward : EndpointShortcutRow
  qUpperReverse : EndpointShortcutRow
  qLowerForward : EndpointShortcutRow
  qLowerReverse : EndpointShortcutRow

def concreteEndpointShortcutLedger : ConcreteEndpointShortcutLedger where
  pUpperForward := endpointShortcut_T2_2_T1_1
  pUpperReverse := endpointShortcut_T1_1_T2_2
  pLowerForward := endpointShortcut_T2_2_T1_2
  pLowerReverse := endpointShortcut_T1_2_T2_2
  qUpperForward := endpointShortcut_T4_0_T0_0
  qUpperReverse := endpointShortcut_T0_0_T4_0
  qLowerForward := endpointShortcut_T4_0_T0_2
  qLowerReverse := endpointShortcut_T0_2_T4_0

/-! ## Obstruction and closure matrices -/

/-- W11 obstruction rows exported as one checked ledger. -/
structure ObstructionRowsLedger where
  possibleRowCount :
    ExactLocalObstructionMatrixW11.possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard
  impossibleRowCount :
    ExactLocalObstructionMatrixW11.impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard
  rootMovedTarget :
    forall {u v : LocalVertex},
      ExactLocalObstructionMatrixW11.IsRootMovedTargetRow u v ->
        Not (PossibleRow u v)
  connectorEndpoint :
    forall {u v : LocalVertex},
      ExactLocalObstructionMatrixW11.IsConnectorEndpointRow u v ->
        Not (PossibleRow u v)
  blockedEndpoint :
    forall {u v : LocalVertex},
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v ->
        Not (PossibleRow u v)
  candidateExcludesBlocked :
    forall (C : CandidateRows) {u v : LocalVertex},
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v ->
        Not (C.row u v)
  endpointShortcuts : ConcreteEndpointShortcutLedger

def obstructionRowsLedger : ObstructionRowsLedger where
  possibleRowCount :=
    ExactLocalObstructionMatrixW11.possibleRowEntries_card
  impossibleRowCount :=
    ExactLocalObstructionMatrixW11.impossibleRowEntries_card
  rootMovedTarget := fun hrow =>
    ExactLocalObstructionMatrixW11.rootMovedTargetRow_not_possible hrow
  connectorEndpoint := fun hrow =>
    ExactLocalObstructionMatrixW11.connectorEndpointRow_not_possible hrow
  blockedEndpoint := fun hrow =>
    ExactLocalObstructionMatrixW11.blockedEndpointRow_not_possible hrow
  candidateExcludesBlocked := by
    intro C u v hrow
    exact
      ExactLocalObstructionMatrixW11.candidateRows_exclude_blockedEndpointRow
        C hrow
  endpointShortcuts := concreteEndpointShortcutLedger

/-- The public W11 exact-local closure matrix. -/
structure Matrix where
  possibleRows : CandidateRowSubsetLedger
  obstructions : ObstructionRowsLedger
  missingConcreteCandidateRows : CandidateRows -> Prop
  concreteMissingRowsBlocked :
    forall C : CandidateRows, Not (ConcreteMissingCandidateRows C)
  branchCandidateFromReducedEquations :
    forall _B : ExactLocalEquationPackage, BranchCandidate
  sameOppositeCandidateFromReducedEquations :
    forall _S : SameOppositeExactLocalEquationPackage,
      SameOppositeCandidate
  routeFromReducedEquations :
    forall S : SameOppositeExactLocalEquationPackage,
      TransitionRemainingFields S.toSameOppositeCandidate ->
        TransitionRouteFields

def matrix : Matrix where
  possibleRows := possibleRowsSubsetLedger
  obstructions := obstructionRowsLedger
  missingConcreteCandidateRows := ConcreteMissingCandidateRows
  concreteMissingRowsBlocked := noConcreteMissingCandidateRows
  branchCandidateFromReducedEquations :=
    exactLocalEquationPackage_toBranchCandidate
  sameOppositeCandidateFromReducedEquations :=
    sameOppositeEquationPackage_toCandidate
  routeFromReducedEquations :=
    sameOppositeEquationPackage_toRouteFields

/-! ## Public projections -/

theorem possibleRowsSubset_card :
    ExactLocalObstructionMatrixW11.possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard :=
  matrix.obstructions.possibleRowCount

theorem impossibleRowsSubset_card :
    ExactLocalObstructionMatrixW11.impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard :=
  matrix.obstructions.impossibleRowCount

theorem candidateRows_exclude_blockedEndpoint
    (C : CandidateRows)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (C.row u v) :=
  matrix.obstructions.candidateExcludesBlocked C hblocked

theorem concreteMissingCandidateRows_blocked
    (C : CandidateRows) :
    Not (ConcreteMissingCandidateRows C) :=
  matrix.concreteMissingRowsBlocked C

theorem pUpperForward_sameEndpointShortcut_blocked
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T2_2 T1_1) :
    Not
      (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  matrix.obstructions.endpointShortcuts.pUpperForward.sameRowsBlocked hrow

theorem pUpperForward_oppositeEndpointShortcut_blocked
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T2_2 T1_1) :
    Not
      (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  matrix.obstructions.endpointShortcuts.pUpperForward.oppositeRowsBlocked hrow

theorem qUpperForward_sameEndpointShortcut_blocked
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T4_0 T0_0) :
    Not
      (PreservesRows RoleHingeConcreteSearch.samePlaceNext row) :=
  matrix.obstructions.endpointShortcuts.qUpperForward.sameRowsBlocked hrow

theorem qUpperForward_oppositeEndpointShortcut_blocked
    {row : LocalVertex -> LocalVertex -> Prop}
    (hrow : row T4_0 T0_0) :
    Not
      (PreservesRows RoleHingeConcreteSearch.oppositePlaceNext row) :=
  matrix.obstructions.endpointShortcuts.qUpperForward.oppositeRowsBlocked hrow

end ExactLocalClosureW11
end PachToth
end ErdosProblems1066

end
