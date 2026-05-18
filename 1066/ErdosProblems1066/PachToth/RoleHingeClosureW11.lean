import ErdosProblems1066.PachToth.RoleHingePolynomialReductionW11
import ErdosProblems1066.PachToth.FlexibleTransitionSearchW11
import ErdosProblems1066.PachToth.FlexibleCandidateAssemblyW11
import ErdosProblems1066.PachToth.CrossBlockInequalityLedgerW11

set_option autoImplicit false

/-!
# W11 role-hinge closure layer

This module is a checked facade over the W11 role-hinge search surfaces.
It records only conditional routes:

* connector and reduced exact-local equation packages project to the candidate
  fields used by the non-rigid route;
* remaining period and metric fields then give the strongest target
  projections already available in W11;
* cross-block inequality packages project to lower-bound and separation
  interfaces; and
* row-grouped numeric ledgers remain explicit witnesses before they are
  repacked into the candidate assembly route.

No concrete numeric ledger is filled here.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeClosureW11

open FiniteGraph
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real

abbrev ConnectorEquationPackage :=
  RoleHingePolynomialReductionW11.ConnectorEquationPackage

abbrev ExactLocalEquationPackage :=
  RoleHingePolynomialReductionW11.ExactLocalEquationPackage

abbrev SameOppositeExactLocalEquationPackage :=
  RoleHingePolynomialReductionW11.SameOppositeExactLocalEquationPackage

abbrev CrossBlockInequalityPackage :=
  RoleHingePolynomialReductionW11.CrossBlockInequalityPackage

abbrev RoleHingedPeriodSearchFamily :=
  RoleHingePolynomialReductionW11.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  RoleHingePolynomialReductionW11.LocalVertexIndex

abbrev NonRigidCandidateRemainingFields :=
  FlexibleTransitionSearchW11.NonRigidCandidateRemainingFields

abbrev NonRigidRouteFields :=
  FlexibleTransitionSearchW11.NonRigidRouteFields

abbrev FlexibleCandidateAssemblyFields :=
  FlexibleCandidateAssemblyW11.FlexibleCandidateAssemblyFields

abbrev PackedCandidateInequalities :=
  FlexibleCandidateAssemblyW11.PackedCandidateInequalities

abbrev CrossBlockInequalityLedger :=
  CrossBlockInequalityLedgerW11.CrossBlockInequalityLedger

abbrev LedgerRoleHingedPeriodSearchFamily :=
  CrossBlockInequalityLedgerW11.RoleHingedPeriodSearchFamily

/-! ## Connector and exact-local equation packages -/

/-- Connector equations as the smallest role-hinge transition package. -/
structure ConnectorClosure where
  package : ConnectorEquationPackage

namespace ConnectorClosure

def toConnectorUnitRoleData
    (C : ConnectorClosure) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData :=
  C.package.toConnectorUnitRoleData

def toConnectorTransitionFacts
    (C : ConnectorClosure) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  C.package.toConnectorTransitionFacts

theorem connector_unit_edges
    (C : ConnectorClosure) :
    HingedTransitionInterface.ConnectorUnitEdges
      C.package.placeNext :=
  C.package.connector_unit_edges

theorem portPairUnitEdges
    (C : ConnectorClosure)
    (angle :
      RoleHingePolynomialSystemW10.PortPairEquationSystem
        C.package.roleAngle) :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (C.package.placeNext source T1_1)
          (C.package.placeNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (C.package.placeNext source T0_0)
          (C.package.placeNext source T0_2) = 1) :=
  C.package.portPairUnitEdges angle

end ConnectorClosure

/-- One reduced exact-local branch package, ready for candidate projection. -/
structure BranchEquationClosure where
  package : ExactLocalEquationPackage

namespace BranchEquationClosure

def toConnectorUnitRoleData
    (B : BranchEquationClosure) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData :=
  B.package.toConnectorUnitRoleData

def toBranchCoordinateData
    (B : BranchEquationClosure) :
    FlexibleBranchCoordinateSearch.BranchCoordinateData :=
  B.package.toBranchCoordinateData

def toFlexibleBranch
    (B : BranchEquationClosure) :
    FlexibleExactLocalTransition.Branch :=
  B.package.toFlexibleBranch

def toBranchCandidate
    (B : BranchEquationClosure) :
    RoleHingeCandidateSearchSurface.BranchCandidate :=
  B.package.toBranchCandidate

theorem connector_unit_edges
    (B : BranchEquationClosure) :
    HingedTransitionInterface.ConnectorUnitEdges
      B.package.placeNext :=
  B.package.connector_unit_edges

theorem preservesExactLocalSqDistances
    (B : BranchEquationClosure) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      B.package.placeNext :=
  B.package.preservesExactLocalSqDistances

theorem exactLocalRow
    (B : BranchEquationClosure)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.package.placeNext source u)
        (B.package.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  B.package.exactLocalRow hsource u v

end BranchEquationClosure

/-- Same/opposite reduced equations projected to all transition interfaces
used by the W11 non-rigid candidate route. -/
structure SameOppositeEquationClosure where
  equations : SameOppositeExactLocalEquationPackage

namespace SameOppositeEquationClosure

def toCoordinateData
    (S : SameOppositeEquationClosure) :
    FlexibleBranchCoordinateSearch.SameOppositeCoordinateData :=
  S.equations.toCoordinateData

def toConnectorTransitionFacts
    (S : SameOppositeEquationClosure) :
    RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts :=
  S.equations.toConnectorTransitionFacts

def toFigure2TransitionObligations
    (S : SameOppositeEquationClosure) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  S.equations.toFigure2TransitionObligations

def toFlexibleSameOpposite
    (S : SameOppositeEquationClosure) :
    FlexibleExactLocalTransition.SameOpposite :=
  S.equations.toFlexibleSameOpposite

def toSameOppositeCandidate
    (S : SameOppositeEquationClosure) :
    RoleHingeCandidateSearchSurface.SameOppositeCandidate :=
  S.equations.toSameOppositeCandidate

theorem generatedTransitionsPreserveExactLocalSqDistances
    (S : SameOppositeEquationClosure) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      S.toFigure2TransitionObligations :=
  S.equations.generatedTransitionsPreserveExactLocalSqDistances

theorem same_sqDist
    (S : SameOppositeEquationClosure)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (S.equations.same.placeNext source u)
        (S.equations.same.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  S.equations.same.exactLocalRow hsource u v

theorem opposite_sqDist
    (S : SameOppositeEquationClosure)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (S.equations.opposite.placeNext source u)
        (S.equations.opposite.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  S.equations.opposite.exactLocalRow hsource u v

end SameOppositeEquationClosure

/-! ## Equation packages plus remaining W11 route fields -/

/-- Reduced same/opposite equations plus the remaining period and metric
fields required by the W11 non-rigid route. -/
structure EquationRouteFields where
  equations : SameOppositeExactLocalEquationPackage
  remaining :
    NonRigidCandidateRemainingFields
      equations.toSameOppositeCandidate

namespace EquationRouteFields

def toSameOppositeEquationClosure
    (R : EquationRouteFields) :
    SameOppositeEquationClosure where
  equations := R.equations

def toNonRigidRouteFields
    (R : EquationRouteFields) :
    NonRigidRouteFields where
  candidate := R.equations.toSameOppositeCandidate
  remaining := R.remaining

def toFlexibleSameOpposite
    (R : EquationRouteFields) :
    FlexibleExactLocalTransition.SameOpposite :=
  R.toNonRigidRouteFields.toFlexibleSameOpposite

def toGeneratedChainFamily
    (R : EquationRouteFields) :
    GeneratedSeparationInterface.GeneratedChainFamily :=
  R.toNonRigidRouteFields.toGeneratedChainFamily

theorem periods
    (R : EquationRouteFields) :
    R.toGeneratedChainFamily.Periods :=
  R.toNonRigidRouteFields.periods

def toFamilyMetricHypotheses
    (R : EquationRouteFields) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      R.toGeneratedChainFamily :=
  R.toNonRigidRouteFields.toFamilyMetricHypotheses

theorem generatedTransitionsPreserveExactLocalSqDistances
    (R : EquationRouteFields) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      R.equations.toFigure2TransitionObligations :=
  R.equations.generatedTransitionsPreserveExactLocalSqDistances

theorem targetUpperConstructionFiveSixteen
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.toNonRigidRouteFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  R.toNonRigidRouteFields.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt
    (R : EquationRouteFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  R.targetUpperConstructionFiveSixteenArbitrary n

theorem targetUpperConstructionFiveSixteenEventually
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact R.targetUpperConstructionFiveSixteenAt n

end EquationRouteFields

/-! ## Cross-block lower-bound closures -/

/-- Cross-block inequality rows, after connector rows have been removed,
projected to lower-bound and target interfaces. -/
structure CrossBlockLowerBoundClosure
    (F : RoleHingedPeriodSearchFamily) where
  inequalities : CrossBlockInequalityPackage F

namespace CrossBlockLowerBoundClosure

variable {F : RoleHingedPeriodSearchFamily}

def toIndexedNonConnectorCrossBlockSqDistanceTableFamily
    (C : CrossBlockLowerBoundClosure F) :
    NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
      F :=
  C.inequalities.toIndexedNonConnectorCrossBlockSqDistanceTableFamily

def toCrossBlockLowerBounds
    (C : CrossBlockLowerBoundClosure F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.inequalities.toCrossBlockLowerBounds

theorem separated
    (C : CrossBlockLowerBoundClosure F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.inequalities.separated k hk

theorem sqDist_ge_one
    (C : CrossBlockLowerBoundClosure F)
    (k : Nat) (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex)
    (hij : Ne i j)
    (hnot :
      Not
        (NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair
          hk i u j v)) :
    1 <=
      CrossBlockDistanceSqReduction.indexedGeneratedSqDist
        F hk i u j v :=
  C.inequalities.sqDist_ge_one k hk i u j v hij hnot

theorem targetUpperConstructionFiveSixteen
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.inequalities.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.inequalities.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenAt
    (C : CrossBlockLowerBoundClosure F) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  C.targetUpperConstructionFiveSixteenArbitrary n

theorem targetUpperConstructionFiveSixteenEventually
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenEventually := by
  refine Exists.intro 0 ?_
  intro n _hn
  exact C.targetUpperConstructionFiveSixteenAt n

end CrossBlockLowerBoundClosure

/-! ## Explicit numeric ledgers and candidate assembly -/

/-- Row-grouped numeric witnesses remain explicit.  This closure only exposes
the already-checked projections from those rows. -/
structure NumericLedgerClosure
    (F : LedgerRoleHingedPeriodSearchFamily) where
  ledger : CrossBlockInequalityLedger F

namespace NumericLedgerClosure

variable {F : LedgerRoleHingedPeriodSearchFamily}

def toPolynomialRowFamilies
    (L : NumericLedgerClosure F) :
    CrossBlockInequalityLedgerW11.UpperTriangleGeneratedPointPolynomialRowFamilies
      F :=
  L.ledger.toPolynomialRowFamilies

def toNonConnectorValueMatrixFamily
    (L : NumericLedgerClosure F) :
    ConcreteNonConnectorValueMatrix.NonConnectorValueMatrixFamily F :=
  L.ledger.toNonConnectorValueMatrixFamily

def toNonConnectorLowerTableFamily
    (L : NumericLedgerClosure F) :
    ConcreteCrossBlockLowerTable.NonConnectorLowerTableFamily F :=
  L.ledger.toNonConnectorLowerTableFamily

theorem separated
    (L : NumericLedgerClosure F)
    (k : Nat) (hk : 0 < k) :
    CrossBlockInequalityLedgerW11.GeneratedGlobalSeparationAt F hk :=
  L.ledger.separated k hk

end NumericLedgerClosure

/-- A period-candidate family together with explicit row-grouped numeric
witnesses.  Repacking into the W11 candidate-assembly route is conditional on
these fields. -/
structure LedgerCandidateAssemblyFields where
  period : CrossBlockValueSearchW10.PeriodCandidateFamily
  ledger :
    CrossBlockInequalityLedger
      period.toRoleHingedPeriodSearchFamily

namespace LedgerCandidateAssemblyFields

def toNumericLedgerClosure
    (L : LedgerCandidateAssemblyFields) :
    NumericLedgerClosure L.period.toRoleHingedPeriodSearchFamily where
  ledger := L.ledger

def toPackedCandidateInequalities
    (L : LedgerCandidateAssemblyFields) :
    PackedCandidateInequalities where
  period := L.period
  certificates := L.ledger.toPolynomialRowFamilies.toPackedInequalityFamily

def toFlexibleCandidateAssemblyFields
    (L : LedgerCandidateAssemblyFields) :
    FlexibleCandidateAssemblyFields where
  packedInequalities := L.toPackedCandidateInequalities

def toCandidateValueMatrixFamily
    (L : LedgerCandidateAssemblyFields) :
    FlexibleCandidateAssemblyW11.CandidateValueMatrixFamily :=
  L.toFlexibleCandidateAssemblyFields.toCandidateValueMatrixFamily

def toRoleHingedPeriodSearchFamily
    (L : LedgerCandidateAssemblyFields) :
    FlexibleCandidateAssemblyW11.RoleHingedPeriodSearchFamily :=
  L.toFlexibleCandidateAssemblyFields.toRoleHingedPeriodSearchFamily

def toCrossBlockLowerBounds
    (L : LedgerCandidateAssemblyFields) :
    FlexibleCandidateAssemblyW11.CrossBlockLowerBounds
      L.toRoleHingedPeriodSearchFamily :=
  L.toFlexibleCandidateAssemblyFields.toCrossBlockLowerBounds

theorem separated
    (L : LedgerCandidateAssemblyFields)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      L.toRoleHingedPeriodSearchFamily.transitions.toFigure2TransitionObligations
      hk
      BaseTransitionRealization.exactBase
      (L.toRoleHingedPeriodSearchFamily.orientation k hk) :=
  L.toFlexibleCandidateAssemblyFields.separated k hk

theorem targetUpperConstructionFiveSixteen
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  L.toFlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenAt
    (L : LedgerCandidateAssemblyFields) (n : Nat) :
    PachToth.targetUpperConstructionFiveSixteenAt n :=
  L.toFlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenAt n

theorem targetUpperConstructionFiveSixteenEventually
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  L.toFlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteenArbitrary
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  L.toFlexibleCandidateAssemblyFields.targetUpperConstructionFiveSixteenArbitrary

end LedgerCandidateAssemblyFields

/-- A compact public matrix of the W11 closure entry points.  The fields are
types of required data, not filled concrete witnesses. -/
structure ClosureMatrix where
  connectorPackage : Type
  branchEquationPackage : Type
  sameOppositeEquationPackage : Type
  equationRoutePackage : Type
  candidateAssemblyPackage : Type
  numericLedgerPackage :
    LedgerRoleHingedPeriodSearchFamily -> Type
  lowerBoundPackage :
    RoleHingedPeriodSearchFamily -> Prop

def closureMatrix : ClosureMatrix where
  connectorPackage := ConnectorClosure
  branchEquationPackage := BranchEquationClosure
  sameOppositeEquationPackage := SameOppositeEquationClosure
  equationRoutePackage := EquationRouteFields
  candidateAssemblyPackage := LedgerCandidateAssemblyFields
  numericLedgerPackage := NumericLedgerClosure
  lowerBoundPackage := CrossBlockLowerBoundClosure

/-! ## Public target routes -/

theorem targetUpperConstructionFiveSixteen_of_equationRoute
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  R.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_equationRoute
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  R.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenEventually_of_equationRoute
    (R : EquationRouteFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  R.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteen_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteen :=
  L.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  L.targetUpperConstructionFiveSixteenArbitrary

theorem targetUpperConstructionFiveSixteenEventually_of_ledgerCandidateAssembly
    (L : LedgerCandidateAssemblyFields) :
    PachToth.targetUpperConstructionFiveSixteenEventually :=
  L.targetUpperConstructionFiveSixteenEventually

theorem targetUpperConstructionFiveSixteen_of_crossBlockLowerBoundClosure
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.targetUpperConstructionFiveSixteen

theorem targetUpperConstructionFiveSixteenArbitrary_of_crossBlockLowerBoundClosure
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockLowerBoundClosure F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.targetUpperConstructionFiveSixteenArbitrary

end

end RoleHingeClosureW11
end PachToth
end ErdosProblems1066
