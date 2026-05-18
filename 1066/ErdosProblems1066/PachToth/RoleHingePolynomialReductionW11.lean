import ErdosProblems1066.PachToth.RoleHingePolynomialSystemW10
import ErdosProblems1066.PachToth.ExactLocalObstructionExpansionW10

set_option autoImplicit false

/-!
# W11 reduced role-hinge polynomial obligations

This module separates the role-hinge search obligations into the pieces used
by downstream interfaces.

* Connector role equations alone give connector-unit facts.
* The two role-angle equations plus all non-angle exact-local row equations
  give full exact-local squared-distance preservation.
* Cross-block work is recorded as the remaining non-connector square-distance
  inequalities, after connector rows have been removed.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingePolynomialReductionW11

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev PossibleExactLocalRow :=
  RoleHingePolynomialSystemW10.PossibleExactLocalRow
abbrev DerivableExactLocalRow :=
  RoleHingePolynomialSystemW10.DerivableExactLocalRow
abbrev RoleHingedPeriodSearchFamily :=
  RoleHingePolynomialSystemW10.RoleHingedPeriodSearchFamily
abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

/-! ## Connector equations -/

/-- The connector-equation part of one branch.  No exact-local row facts are
stored here. -/
structure ConnectorEquationPackage where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  connector :
    RoleHingePolynomialSystemW10.ConnectorEquationSystem
      placeNext roleAngle

namespace ConnectorEquationPackage

/-- Projection to the flexible connector role-data interface. -/
def toConnectorUnitRoleData
    (C : ConnectorEquationPackage) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData where
  placeNext := C.placeNext
  roleAngle := C.roleAngle
  realizes_role := C.connector

@[simp]
theorem toConnectorUnitRoleData_placeNext
    (C : ConnectorEquationPackage) :
    C.toConnectorUnitRoleData.placeNext = C.placeNext :=
  rfl

@[simp]
theorem toConnectorUnitRoleData_roleAngle
    (C : ConnectorEquationPackage) :
    C.toConnectorUnitRoleData.roleAngle = C.roleAngle :=
  rfl

/-- Projection to the connector-only role-hinge transition facts. -/
def toConnectorTransitionFacts
    (C : ConnectorEquationPackage) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  C.toConnectorUnitRoleData.toConnectorTransitionFacts

@[simp]
theorem toConnectorTransitionFacts_placeNext
    (C : ConnectorEquationPackage) :
    C.toConnectorTransitionFacts.placeNext = C.placeNext :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_roleAngle
    (C : ConnectorEquationPackage) :
    C.toConnectorTransitionFacts.roleAngle = C.roleAngle :=
  rfl

/-- Connector-unit edges are a consequence of the role equations alone. -/
theorem connector_unit_edges
    (C : ConnectorEquationPackage) :
    HingedTransitionInterface.ConnectorUnitEdges C.placeNext :=
  C.toConnectorUnitRoleData.connector_unit_edges

/-- Same-source port-pair unit edges follow once the two angle equations are
added to the connector equations. -/
theorem portPairUnitEdges
    (C : ConnectorEquationPackage)
    (angle :
      RoleHingePolynomialSystemW10.PortPairEquationSystem C.roleAngle) :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (C.placeNext source T1_1) (C.placeNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (C.placeNext source T0_0) (C.placeNext source T0_2) = 1) :=
  RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
    C.placeNext C.roleAngle C.connector angle

end ConnectorEquationPackage

/-! ## Exact-local equation reduction -/

/-- The exact-local rows still requiring direct algebra after the two
role-angle port-pair rows are removed. -/
def NonAngleExactLocalEquationRows
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall source : LocalVertex -> R2,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
      forall u v : LocalVertex,
        Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (placeNext source u) (placeNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

/-- Connector equations, the two angle equations, and the non-angle
exact-local rows are sufficient for the full exact-local preservation
interface. -/
structure ExactLocalEquationPackage extends ConnectorEquationPackage where
  angle :
    RoleHingePolynomialSystemW10.PortPairEquationSystem roleAngle
  nonAngleRows : NonAngleExactLocalEquationRows placeNext

namespace ExactLocalEquationPackage

/-- Projection to connector role data. -/
def toConnectorUnitRoleData
    (B : ExactLocalEquationPackage) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector

@[simp]
theorem toConnectorUnitRoleData_placeNext
    (B : ExactLocalEquationPackage) :
    B.toConnectorUnitRoleData.placeNext = B.placeNext :=
  rfl

/-- Projection to the W9 coordinate-data surface. -/
def toBranchCoordinateData
    (B : ExactLocalEquationPackage) :
    FlexibleBranchCoordinateSearch.BranchCoordinateData where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector
  angleEquations := B.angle

@[simp]
theorem toBranchCoordinateData_placeNext
    (B : ExactLocalEquationPackage) :
    B.toBranchCoordinateData.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toBranchCoordinateData_roleAngle
    (B : ExactLocalEquationPackage) :
    B.toBranchCoordinateData.roleAngle = B.roleAngle :=
  rfl

/-- Connector-unit edges still use only the connector equation field. -/
theorem connector_unit_edges
    (B : ExactLocalEquationPackage) :
    HingedTransitionInterface.ConnectorUnitEdges B.placeNext :=
  B.toConnectorUnitRoleData.connector_unit_edges

/-- The reduced equation rows imply exact-local squared-distance
preservation. -/
theorem preservesExactLocalSqDistances
    (B : ExactLocalEquationPackage) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances B.placeNext :=
  RoleHingeAngleCertificates.preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
      B.placeNext B.roleAngle B.connector B.angle B.nonAngleRows

/-- Row-level exact-local preservation obtained from the reduced package. -/
theorem exactLocalRow
    (B : ExactLocalEquationPackage)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (B.placeNext source u) (B.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  B.preservesExactLocalSqDistances source hsource u v

/-- Projection to the flexible exact-local branch interface. -/
def toFlexibleBranch
    (B : ExactLocalEquationPackage) :
    FlexibleExactLocalTransition.Branch where
  connector := B.toConnectorUnitRoleData
  exactLocal :=
    { preserves_exact_local_sq_distances :=
        B.preservesExactLocalSqDistances }

@[simp]
theorem toFlexibleBranch_placeNext
    (B : ExactLocalEquationPackage) :
    B.toFlexibleBranch.placeNext = B.placeNext :=
  rfl

/-- Projection to the non-rigid branch-candidate interface. -/
def toBranchCandidate
    (B : ExactLocalEquationPackage) :
    RoleHingeCandidateSearchSurface.BranchCandidate where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  realizes_role := B.connector
  preserves_exactLocal_sqDistances := B.preservesExactLocalSqDistances

@[simp]
theorem toBranchCandidate_placeNext
    (B : ExactLocalEquationPackage) :
    B.toBranchCandidate.placeNext = B.placeNext :=
  rfl

/-- Projection to the W10 full branch polynomial system. -/
def toW10BranchPolynomialSystem
    (B : ExactLocalEquationPackage) :
    RoleHingePolynomialSystemW10.BranchPolynomialSystem where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  connector := B.connector
  portPair := B.angle
  exactLocal :=
    (RoleHingePolynomialSystemW10.fullExactLocalEquationSystem_iff_preservesExactLocalSqDistances
        B.placeNext).mpr B.preservesExactLocalSqDistances

@[simp]
theorem toW10BranchPolynomialSystem_placeNext
    (B : ExactLocalEquationPackage) :
    B.toW10BranchPolynomialSystem.placeNext = B.placeNext :=
  rfl

/-- Projection to the W10 filtered possible-row branch system. -/
def toW10FilteredBranchPolynomialSystem
    (B : ExactLocalEquationPackage) :
    RoleHingePolynomialSystemW10.FilteredBranchPolynomialSystem where
  placeNext := B.placeNext
  roleAngle := B.roleAngle
  connector := B.connector
  portPair := B.angle
  possibleRows := by
    intro source hsource u v _hrow
    exact B.preservesExactLocalSqDistances source hsource u v

/-- Projection to the W9 exact-local filtered branch surface. -/
def toFilteredBranch
    (B : ExactLocalEquationPackage) :
    ExactLocalBranchSolverSurface.FilteredBranch where
  connector := B.toConnectorUnitRoleData
  possibleRows :=
    ExactLocalBranchSolverSurface.preservesPossibleRows_of_preservesExactLocalSqDistances
        B.preservesExactLocalSqDistances

end ExactLocalEquationPackage

/-! ## Same/opposite reductions -/

/-- Reduced equation package for the same and opposite role-hinge branches. -/
structure SameOppositeExactLocalEquationPackage where
  same : ExactLocalEquationPackage
  opposite : ExactLocalEquationPackage

namespace SameOppositeExactLocalEquationPackage

/-- Projection to the W9 same/opposite coordinate-data surface. -/
def toCoordinateData
    (S : SameOppositeExactLocalEquationPackage) :
    FlexibleBranchCoordinateSearch.SameOppositeCoordinateData where
  same := S.same.toBranchCoordinateData
  opposite := S.opposite.toBranchCoordinateData

/-- Projection to connector-only same/opposite role-hinge transition facts. -/
def toConnectorTransitionFacts
    (S : SameOppositeExactLocalEquationPackage) :
    RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts where
  same := S.same.toConnectorUnitRoleData.toConnectorTransitionFacts
  opposite := S.opposite.toConnectorUnitRoleData.toConnectorTransitionFacts

/-- Projection to Figure 2 connector obligations. -/
def toFigure2TransitionObligations
    (S : SameOppositeExactLocalEquationPackage) :
    Figure2Certificate.SameOppositeTransitionObligations where
  samePlaceNext := S.same.placeNext
  oppositePlaceNext := S.opposite.placeNext
  same_connector_unit_edges := S.same.connector_unit_edges
  opposite_connector_unit_edges := S.opposite.connector_unit_edges

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (S : SameOppositeExactLocalEquationPackage) :
    S.toFigure2TransitionObligations.samePlaceNext =
      S.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (S : SameOppositeExactLocalEquationPackage) :
    S.toFigure2TransitionObligations.oppositePlaceNext =
      S.opposite.placeNext :=
  rfl

/-- Projection to the flexible same/opposite exact-local interface. -/
def toFlexibleSameOpposite
    (S : SameOppositeExactLocalEquationPackage) :
    FlexibleExactLocalTransition.SameOpposite where
  same := S.same.toFlexibleBranch
  opposite := S.opposite.toFlexibleBranch

/-- Projection to the non-rigid same/opposite candidate interface. -/
def toSameOppositeCandidate
    (S : SameOppositeExactLocalEquationPackage) :
    RoleHingeCandidateSearchSurface.SameOppositeCandidate where
  same := S.same.toBranchCandidate
  opposite := S.opposite.toBranchCandidate

/-- Projection to the W10 completed same/opposite polynomial system. -/
def toW10SameOppositePolynomialSystem
    (S : SameOppositeExactLocalEquationPackage) :
    RoleHingePolynomialSystemW10.SameOppositePolynomialSystem where
  same := S.same.toW10BranchPolynomialSystem
  opposite := S.opposite.toW10BranchPolynomialSystem

/-- Projection to the W10 filtered same/opposite polynomial system. -/
def toW10FilteredSameOppositePolynomialSystem
    (S : SameOppositeExactLocalEquationPackage) :
    RoleHingePolynomialSystemW10.FilteredSameOppositePolynomialSystem where
  same := S.same.toW10FilteredBranchPolynomialSystem
  opposite := S.opposite.toW10FilteredBranchPolynomialSystem

/-- Projection to the W9 filtered exact-local branch surface. -/
def toFilteredSameOpposite
    (S : SameOppositeExactLocalEquationPackage) :
    ExactLocalBranchSolverSurface.FilteredSameOpposite where
  same := S.same.toFilteredBranch
  opposite := S.opposite.toFilteredBranch

/-- The reduced branch equations imply the generated-transition exact-local
invariant. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (S : SameOppositeExactLocalEquationPackage) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      S.toFigure2TransitionObligations := by
  intro orientation source hsource
  cases orientation with
  | same =>
      exact S.same.preservesExactLocalSqDistances source hsource
  | opposite =>
      exact S.opposite.preservesExactLocalSqDistances source hsource

end SameOppositeExactLocalEquationPackage

/-! ## Concrete filtered row surface and blocked exact-local rows -/

/-- The concrete four-target system already inhabits the W10 filtered
possible-row surface. -/
def concreteFilteredSameOppositeSystem :
    RoleHingePolynomialSystemW10.FilteredSameOppositePolynomialSystem :=
  RoleHingePolynomialSystemW10.concreteFilteredSameOppositeSystem

/-- The W10 and W9 possible-row spellings are equivalent. -/
theorem possibleExactLocalRow_iff_derivableExactLocalRow
    (u v : LocalVertex) :
    PossibleExactLocalRow u v <-> DerivableExactLocalRow u v :=
  RoleHingePolynomialSystemW10.possibleExactLocalRow_iff_derivableExactLocalRow
    u v

/-- Count of exact-local rows still available to the concrete filtered
surface. -/
theorem possibleRowEntries_card :
    ExactLocalObstructionExpansionW10.possibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.possibleExactLocalRowExpectedCard :=
  ExactLocalObstructionExpansionW10.possibleRowEntries_card

/-- Count of exact-local rows excluded from the concrete filtered surface. -/
theorem blockedRowEntries_card :
    ExactLocalObstructionExpansionW10.impossibleRowEntries.card =
      ExactLocalTransitionObligationMatrix.impossibleExactLocalRowExpectedCard :=
  ExactLocalObstructionExpansionW10.impossibleRowEntries_card

/-- The concrete same branch cannot be promoted to all exact-local rows. -/
theorem sameConcrete_not_fullExactLocalEquationSystem :
    Not
      (RoleHingePolynomialSystemW10.FullExactLocalEquationSystem
        RoleHingeConcreteSearch.samePlaceNext) :=
  RoleHingePolynomialSystemW10.sameConcrete_not_fullExactLocalEquationSystem

/-- The concrete opposite branch cannot be promoted to all exact-local rows. -/
theorem oppositeConcrete_not_fullExactLocalEquationSystem :
    Not
      (RoleHingePolynomialSystemW10.FullExactLocalEquationSystem
        RoleHingeConcreteSearch.oppositePlaceNext) :=
  RoleHingePolynomialSystemW10.oppositeConcrete_not_fullExactLocalEquationSystem

/-- One named blocked row from the W10 matrix expansion. -/
theorem not_possible_T1_2_r :
    Not (PossibleExactLocalRow T1_2 LocalVertex.r) :=
  ExactLocalObstructionExpansionW10.not_possible_T1_2_r

/-! ## Cross-block lower-bound inequality rows -/

/-- The cross-block rows left after connector pairs have been removed. -/
def RemainingCrossBlockInequalityRow
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  Ne i j /\
    Not
      (NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair
        hk i u j v)

/-- The remaining cross-block work as square-distance lower-bound rows. -/
structure CrossBlockInequalityPackage
    (F : RoleHingedPeriodSearchFamily) where
  row_sqDist_ge_one :
    forall (k : Nat) (hk : 0 < k)
      (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        RemainingCrossBlockInequalityRow hk i u j v ->
          1 <=
            CrossBlockDistanceSqReduction.indexedGeneratedSqDist
              F hk i u j v

namespace CrossBlockInequalityPackage

/-- Row-level access in the native non-connector table spelling. -/
theorem sqDist_ge_one
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F)
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
  C.row_sqDist_ge_one k hk i u j v ⟨hij, hnot⟩

/-- One positive period length as the existing non-connector square-distance
table. -/
def toIndexedNonConnectorCrossBlockSqDistanceTable
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F)
    (k : Nat) (hk : 0 < k) :
    NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable
      F k hk where
  sqDist_ge_one := by
    intro i u j v hij hnot
    exact C.sqDist_ge_one k hk i u j v hij hnot

/-- Projection to the existing family of non-connector square-distance
tables. -/
def toIndexedNonConnectorCrossBlockSqDistanceTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F) :
    NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily
      F where
  table := fun k hk =>
    C.toIndexedNonConnectorCrossBlockSqDistanceTable k hk

/-- Projection to the existing cross-block lower-bound facade. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F) :
    CrossBlockLowerBoundsInterface.CrossBlockLowerBounds F :=
  C.toIndexedNonConnectorCrossBlockSqDistanceTableFamily.toCrossBlockLowerBounds

/-- The inequality rows give generated global separation for each positive
period length. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  C.toIndexedNonConnectorCrossBlockSqDistanceTableFamily.separated k hk

/-- Exact target projection from period data plus the remaining inequality
rows. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

/-- Arbitrary-target projection from period data plus the remaining
inequality rows. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    {F : RoleHingedPeriodSearchFamily}
    (C : CrossBlockInequalityPackage F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  C.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end CrossBlockInequalityPackage

end RoleHingePolynomialReductionW11
end PachToth
end ErdosProblems1066

end
