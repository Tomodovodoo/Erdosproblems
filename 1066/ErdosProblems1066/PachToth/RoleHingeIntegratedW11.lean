import ErdosProblems1066.PachToth.RoleHingeClosureW11
import ErdosProblems1066.PachToth.ExactLocalClosureW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11
import ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11
import ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix

set_option autoImplicit false

/-!
# W11 integrated role-hinge matrix

This module routes the W11 role-hinge closure fields through the wider
Pach--Toth W11 target facades.  Connector and exact-local equation fields are
kept as interface projections until the remaining route data is supplied.
Cross-block and numeric rows remain explicit package arguments.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeIntegratedW11

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

universe u

abbrev R2 := Prod Real Real

abbrev ConnectorEquationPackage :=
  RoleHingePolynomialReductionW11.ConnectorEquationPackage

abbrev ExactLocalEquationPackage :=
  RoleHingePolynomialReductionW11.ExactLocalEquationPackage

abbrev SameOppositeExactLocalEquationPackage :=
  RoleHingePolynomialReductionW11.SameOppositeExactLocalEquationPackage

abbrev CrossBlockInequalityPackage :=
  RoleHingePolynomialReductionW11.CrossBlockInequalityPackage

abbrev ConnectorClosure :=
  RoleHingeClosureW11.ConnectorClosure

abbrev BranchEquationClosure :=
  RoleHingeClosureW11.BranchEquationClosure

abbrev SameOppositeEquationClosure :=
  RoleHingeClosureW11.SameOppositeEquationClosure

abbrev EquationRouteFields :=
  RoleHingeClosureW11.EquationRouteFields

abbrev LedgerCandidateAssemblyFields :=
  RoleHingeClosureW11.LedgerCandidateAssemblyFields

abbrev RoleHingedPeriodSearchFamily :=
  RoleHingeClosureW11.RoleHingedPeriodSearchFamily

abbrev LedgerRoleHingedPeriodSearchFamily :=
  RoleHingeClosureW11.LedgerRoleHingedPeriodSearchFamily

abbrev CrossBlockLowerBoundClosure :=
  RoleHingeClosureW11.CrossBlockLowerBoundClosure

abbrev NumericLedgerClosure :=
  RoleHingeClosureW11.NumericLedgerClosure

abbrev RawCrossBlockInequalityLedger :=
  _root_.ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger

abbrev CrossBlockClosureLedger :=
  _root_.ErdosProblems1066.PachToth.CrossBlockInequalityClosureW11.CrossBlockClosureLedger

/-- Exact, eventual, and arbitrary projections for one explicit package. -/
structure TargetRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  eventualTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenEventually
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

theorem eventualTargetOfArbitrary
    (H : PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact H n

/-! ## Source and numeric ledgers -/

/-- Explicit source package shapes used by the role-hinge integration layer. -/
structure SourceLedger where
  connectorEquations : Type
  connectorClosure : Type
  branchEquations : Type
  branchClosure : Type
  sameOppositeEquations : Type
  sameOppositeClosure : Type
  equationRouteFields : Type
  exactLocalCandidateRows :
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows
  exactLocalClosureMatrix : Type
  roleCrossBlockInequalities :
    RoleHingedPeriodSearchFamily -> Prop
  crossBlockLowerBoundClosure :
    RoleHingedPeriodSearchFamily -> Prop
  upperTrianglePolynomialRows :
    LedgerRoleHingedPeriodSearchFamily -> Prop
  upperTriangleValueRows :
    LedgerRoleHingedPeriodSearchFamily -> Type
  rawCrossBlockInequalityLedgers :
    LedgerRoleHingedPeriodSearchFamily -> Type
  numericLedgerClosures :
    LedgerRoleHingedPeriodSearchFamily -> Type
  crossBlockClosureLedgers :
    LedgerRoleHingedPeriodSearchFamily -> Type
  ledgerCandidateAssemblyFields : Type

/-- The checked source ledger assembled from the W11 role-hinge files. -/
def sourceLedger : SourceLedger where
  connectorEquations := ConnectorEquationPackage
  connectorClosure := ConnectorClosure
  branchEquations := ExactLocalEquationPackage
  branchClosure := BranchEquationClosure
  sameOppositeEquations := SameOppositeExactLocalEquationPackage
  sameOppositeClosure := SameOppositeEquationClosure
  equationRouteFields := EquationRouteFields
  exactLocalCandidateRows :=
    ExactLocalObstructionMatrixW11.ExactLocalCandidateRows.possibleRows
  exactLocalClosureMatrix := ExactLocalClosureW11.Matrix
  roleCrossBlockInequalities := CrossBlockInequalityPackage
  crossBlockLowerBoundClosure := CrossBlockLowerBoundClosure
  upperTrianglePolynomialRows :=
    _root_.ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointPolynomialRowFamilies
  upperTriangleValueRows :=
    _root_.ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointValueRowFamilies
  rawCrossBlockInequalityLedgers := RawCrossBlockInequalityLedger
  numericLedgerClosures := NumericLedgerClosure
  crossBlockClosureLedgers := CrossBlockClosureLedger
  ledgerCandidateAssemblyFields := LedgerCandidateAssemblyFields

/-! ## Connector and exact-local projections -/

def connectorClosureToConnectorUnitRoleData
    (C : ConnectorClosure) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData :=
  C.toConnectorUnitRoleData

def connectorClosureToTransitionFacts
    (C : ConnectorClosure) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  C.toConnectorTransitionFacts

theorem connectorClosure_unit_edges
    (C : ConnectorClosure) :
    HingedTransitionInterface.ConnectorUnitEdges
      C.package.placeNext :=
  C.connector_unit_edges

def branchClosureToBranchCandidate
    (B : BranchEquationClosure) :
    RoleHingeCandidateSearchSurface.BranchCandidate :=
  B.toBranchCandidate

theorem branchClosure_preservesExactLocalSqDistances
    (B : BranchEquationClosure) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      B.package.placeNext :=
  B.preservesExactLocalSqDistances

def sameOppositeClosureToCandidate
    (S : SameOppositeEquationClosure) :
    RoleHingeCandidateSearchSurface.SameOppositeCandidate :=
  S.toSameOppositeCandidate

def exactLocalRouteFromReducedEquations
    (S : SameOppositeExactLocalEquationPackage)
    (R :
      ExactLocalClosureW11.TransitionRemainingFields
        S.toSameOppositeCandidate) :
    ExactLocalClosureW11.TransitionRouteFields :=
  ExactLocalClosureW11.sameOppositeEquationPackage_toRouteFields S R

theorem exactLocalCandidateRows_exclude_blockedEndpoint
    (C : ExactLocalClosureW11.CandidateRows)
    {u v : LocalVertex}
    (hblocked :
      ExactLocalObstructionMatrixW11.IsW11BlockedEndpointRow u v) :
    Not (C.row u v) :=
  ExactLocalClosureW11.candidateRows_exclude_blockedEndpoint
    C hblocked

theorem exactLocalConcreteMissingRows_blocked
    (C : ExactLocalClosureW11.CandidateRows) :
    Not (ExactLocalClosureW11.ConcreteMissingCandidateRows C) :=
  ExactLocalClosureW11.concreteMissingCandidateRows_blocked C

/-! ## Broad target rows -/

def rowOfExactArbitrary
    {alpha : Sort u}
    (exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen)
    (arbitraryTarget :
      alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary) :
    TargetRow alpha where
  exactTarget := exactTarget
  eventualTarget := fun a => eventualTargetOfArbitrary (arbitraryTarget a)
  arbitraryTarget := arbitraryTarget

def equationRouteTargetRow : TargetRow EquationRouteFields where
  exactTarget := fun R =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_transitionRouteFields
      R.toNonRigidRouteFields
  eventualTarget := fun R =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenEventually_of_transitionRouteFields
      R.toNonRigidRouteFields
  arbitraryTarget := fun R =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
      R.toNonRigidRouteFields

def ledgerCandidateAssemblyTargetRow :
    TargetRow LedgerCandidateAssemblyFields where
  exactTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_flexibleCandidateFields
      L.toFlexibleCandidateAssemblyFields
  eventualTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenEventually_of_flexibleCandidateFields
      L.toFlexibleCandidateAssemblyFields
  arbitraryTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_flexibleCandidateFields
      L.toFlexibleCandidateAssemblyFields

def crossBlockLowerBoundTargetRow
    (F : RoleHingedPeriodSearchFamily) :
    TargetRow (CrossBlockLowerBoundClosure F) :=
  rowOfExactArbitrary
    (fun C =>
      _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_roleHingeCrossBlockInequalities
        C.inequalities)
    (fun C =>
      _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_roleHingeCrossBlockInequalities
        C.inequalities)

def toCrossBlockClosureLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : RawCrossBlockInequalityLedger F) :
    CrossBlockClosureLedger F where
  inequalityLedger := L

def numericLedgerClosureToCrossBlockClosureLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : NumericLedgerClosure F) :
    CrossBlockClosureLedger F :=
  toCrossBlockClosureLedger L.ledger

def rawCrossBlockInequalityLedgerTargetRow
    (F : LedgerRoleHingedPeriodSearchFamily) :
    TargetRow (RawCrossBlockInequalityLedger F) where
  exactTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
      (toCrossBlockClosureLedger L)
  eventualTarget := fun L =>
    eventualTargetOfArbitrary
      (_root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        (toCrossBlockClosureLedger L))
  arbitraryTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
      (toCrossBlockClosureLedger L)

def numericLedgerClosureTargetRow
    (F : LedgerRoleHingedPeriodSearchFamily) :
    TargetRow (NumericLedgerClosure F) where
  exactTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
      (numericLedgerClosureToCrossBlockClosureLedger L)
  eventualTarget := fun L =>
    eventualTargetOfArbitrary
      (_root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        (numericLedgerClosureToCrossBlockClosureLedger L))
  arbitraryTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
      (numericLedgerClosureToCrossBlockClosureLedger L)

def crossBlockClosureLedgerTargetRow
    (F : LedgerRoleHingedPeriodSearchFamily) :
    TargetRow (CrossBlockClosureLedger F) where
  exactTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger L
  eventualTarget := fun L =>
    eventualTargetOfArbitrary
      (_root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
        L)
  arbitraryTarget := fun L =>
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger L

/-! ## Integrated matrix -/

/-- Integrated role-hinge matrix with explicit source rows and target routes. -/
structure Matrix where
  sources : SourceLedger
  roleHingeClosure : RoleHingeClosureW11.ClosureMatrix
  exactLocalClosure : ExactLocalClosureW11.Matrix
  pachTothIntegrated :
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.Matrix
  equationRouteTargets : TargetRow EquationRouteFields
  ledgerCandidateAssemblyTargets :
    TargetRow LedgerCandidateAssemblyFields
  crossBlockLowerBoundTargets :
    forall F : RoleHingedPeriodSearchFamily,
      TargetRow (CrossBlockLowerBoundClosure F)
  rawCrossBlockInequalityLedgerTargets :
    forall F : LedgerRoleHingedPeriodSearchFamily,
      TargetRow (RawCrossBlockInequalityLedger F)
  numericLedgerClosureTargets :
    forall F : LedgerRoleHingedPeriodSearchFamily,
      TargetRow (NumericLedgerClosure F)
  crossBlockClosureLedgerTargets :
    forall F : LedgerRoleHingedPeriodSearchFamily,
      TargetRow (CrossBlockClosureLedger F)

/-- The public W11 role-hinge integration matrix. -/
def matrix : Matrix where
  sources := sourceLedger
  roleHingeClosure := RoleHingeClosureW11.closureMatrix
  exactLocalClosure := ExactLocalClosureW11.matrix
  pachTothIntegrated :=
    _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.matrix
  equationRouteTargets := equationRouteTargetRow
  ledgerCandidateAssemblyTargets := ledgerCandidateAssemblyTargetRow
  crossBlockLowerBoundTargets := crossBlockLowerBoundTargetRow
  rawCrossBlockInequalityLedgerTargets :=
    rawCrossBlockInequalityLedgerTargetRow
  numericLedgerClosureTargets := numericLedgerClosureTargetRow
  crossBlockClosureLedgerTargets := crossBlockClosureLedgerTargetRow

/-! ## Public target projections -/

theorem targetUpperConstructionFiveSixteen_of_equationRoute
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.equationRouteTargets.exactTarget R

theorem targetUpperConstructionFiveSixteenAt_of_equationRoute
    (R : EquationRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_transitionRouteFields
    R.toNonRigidRouteFields n

theorem targetUpperConstructionFiveSixteenEventually_of_equationRoute
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.equationRouteTargets.eventualTarget R

theorem targetUpperConstructionFiveSixteenArbitrary_of_equationRoute
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.equationRouteTargets.arbitraryTarget R

theorem targetUpperConstructionFiveSixteen_of_exactLocalEquationRoute
    (S : SameOppositeExactLocalEquationPackage)
    (R :
      ExactLocalClosureW11.TransitionRemainingFields
        S.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteen :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteen_of_transitionRouteFields
    (exactLocalRouteFromReducedEquations S R)

theorem targetUpperConstructionFiveSixteenArbitrary_of_exactLocalEquationRoute
    (S : SameOppositeExactLocalEquationPackage)
    (R :
      ExactLocalClosureW11.TransitionRemainingFields
        S.toSameOppositeCandidate) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenArbitrary_of_transitionRouteFields
    (exactLocalRouteFromReducedEquations S R)

theorem targetUpperConstructionFiveSixteen_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.ledgerCandidateAssemblyTargets.exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_flexibleCandidateFields
    L.toFlexibleCandidateAssemblyFields n

theorem targetUpperConstructionFiveSixteenEventually_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  matrix.ledgerCandidateAssemblyTargets.eventualTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.ledgerCandidateAssemblyTargets.arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_crossBlockLowerBoundClosure
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockLowerBoundTargets F).exactTarget C

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockLowerBoundClosure
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockLowerBoundTargets F).eventualTarget C

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBoundClosure
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockLowerBoundTargets F).arbitraryTarget C

theorem targetUpperConstructionFiveSixteen_of_rawCrossBlockInequalityLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.rawCrossBlockInequalityLedgerTargets F).exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_rawCrossBlockInequalityLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : RawCrossBlockInequalityLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    (toCrossBlockClosureLedger L) n

theorem targetUpperConstructionFiveSixteenEventually_of_rawCrossBlockInequalityLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.rawCrossBlockInequalityLedgerTargets F).eventualTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_rawCrossBlockInequalityLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : RawCrossBlockInequalityLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.rawCrossBlockInequalityLedgerTargets F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_numericLedgerClosure
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : NumericLedgerClosure F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.numericLedgerClosureTargets F).exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_numericLedgerClosure
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : NumericLedgerClosure F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    (numericLedgerClosureToCrossBlockClosureLedger L) n

theorem targetUpperConstructionFiveSixteenEventually_of_numericLedgerClosure
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : NumericLedgerClosure F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.numericLedgerClosureTargets F).eventualTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_numericLedgerClosure
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : NumericLedgerClosure F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.numericLedgerClosureTargets F).arbitraryTarget L

theorem targetUpperConstructionFiveSixteen_of_crossBlockClosureLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  (matrix.crossBlockClosureLedgerTargets F).exactTarget L

theorem targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : CrossBlockClosureLedger F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  _root_.ErdosProblems1066.PachToth.PachTothW11IntegratedMatrix.targetUpperConstructionFiveSixteenAt_of_crossBlockClosureLedger L n

theorem targetUpperConstructionFiveSixteenEventually_of_crossBlockClosureLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  (matrix.crossBlockClosureLedgerTargets F).eventualTarget L

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockClosureLedger
    {F : LedgerRoleHingedPeriodSearchFamily}
    (L : CrossBlockClosureLedger F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  (matrix.crossBlockClosureLedgerTargets F).arbitraryTarget L

end

end RoleHingeIntegratedW11
end PachToth
end ErdosProblems1066
