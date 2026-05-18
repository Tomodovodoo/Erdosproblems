import ErdosProblems1066.PachToth.RoleHingeConcreteSearch

set_option autoImplicit false

/-!
# Concrete connector-level role-hinge transitions

This module packages the existing concrete hinge-point maps with the concrete
same/opposite equilateral role angles as `RoleHingeConnectorTransitionFacts`.
It deliberately targets the connector-only package, not the obstructed
all-source same-block preservation interface.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeConnectorConcrete

open FiniteGraph
open FiniteGraph.LocalVertex
open Figure2EdgeTable

noncomputable section

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev RoleHingeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts
abbrev SameOppositeRoleHingeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts

/-- The existing concrete hinge-point formula, exposed under the connector
concrete namespace. -/
def concretePlaceNext (roleAngle : ConnectorRole -> Real) :
    (LocalVertex -> R2) -> LocalVertex -> R2 :=
  RoleHingeConcreteSearch.concreteRoleHingePlace roleAngle

/-- The concrete map realizes every named successor connector as its role
hinge endpoint. -/
theorem concretePlaceNext_realizes_role
    (roleAngle : ConnectorRole -> Real) :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      nextConnectorRole u v = some role ->
        concretePlaceNext roleAngle source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role) := by
  simpa [concretePlaceNext] using
    RoleHingeConcreteSearch.concreteRoleHingePlace_realizes_role roleAngle

/-- Same-branch connector map with the concrete equilateral role angles. -/
def samePlaceNext : (LocalVertex -> R2) -> LocalVertex -> R2 :=
  concretePlaceNext RoleHingeAngleCertificates.sameEquilateralRoleAngle

/-- Opposite-branch connector map with the mirrored equilateral role angles. -/
def oppositePlaceNext : (LocalVertex -> R2) -> LocalVertex -> R2 :=
  concretePlaceNext RoleHingeAngleCertificates.oppositeEquilateralRoleAngle

theorem samePlaceNext_realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      nextConnectorRole u v = some role ->
        samePlaceNext source v =
          UnitVectorGeometry.hingePoint
            (source u)
            (RoleHingeAngleCertificates.sameEquilateralRoleAngle role) :=
  concretePlaceNext_realizes_role
    RoleHingeAngleCertificates.sameEquilateralRoleAngle

theorem oppositePlaceNext_realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      nextConnectorRole u v = some role ->
        oppositePlaceNext source v =
          UnitVectorGeometry.hingePoint
            (source u)
            (RoleHingeAngleCertificates.oppositeEquilateralRoleAngle role) :=
  concretePlaceNext_realizes_role
    RoleHingeAngleCertificates.oppositeEquilateralRoleAngle

/-- Build one concrete connector-only transition fact package from a role-angle
assignment and the concrete hinge-point formulas. -/
def transitionFactsOfRoleAngle
    (roleAngle : ConnectorRole -> Real) :
    RoleHingeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.roleHingeConnectorTransitionFacts
    (concretePlaceNext roleAngle)
    roleAngle
    (concretePlaceNext_realizes_role roleAngle)

@[simp]
theorem transitionFactsOfRoleAngle_placeNext
    (roleAngle : ConnectorRole -> Real) :
    (transitionFactsOfRoleAngle roleAngle).placeNext =
      concretePlaceNext roleAngle :=
  rfl

@[simp]
theorem transitionFactsOfRoleAngle_roleAngle
    (roleAngle : ConnectorRole -> Real) :
    (transitionFactsOfRoleAngle roleAngle).roleAngle = roleAngle :=
  rfl

/-- Concrete same-branch connector-unit transition facts. -/
def sameTransitionFacts : RoleHingeConnectorTransitionFacts :=
  transitionFactsOfRoleAngle
    RoleHingeAngleCertificates.sameEquilateralRoleAngle

/-- Concrete opposite-branch connector-unit transition facts. -/
def oppositeTransitionFacts : RoleHingeConnectorTransitionFacts :=
  transitionFactsOfRoleAngle
    RoleHingeAngleCertificates.oppositeEquilateralRoleAngle

@[simp]
theorem sameTransitionFacts_placeNext :
    sameTransitionFacts.placeNext = samePlaceNext :=
  rfl

@[simp]
theorem oppositeTransitionFacts_placeNext :
    oppositeTransitionFacts.placeNext = oppositePlaceNext :=
  rfl

@[simp]
theorem sameTransitionFacts_roleAngle :
    sameTransitionFacts.roleAngle =
      RoleHingeAngleCertificates.sameEquilateralRoleAngle :=
  rfl

@[simp]
theorem oppositeTransitionFacts_roleAngle :
    oppositeTransitionFacts.roleAngle =
      RoleHingeAngleCertificates.oppositeEquilateralRoleAngle :=
  rfl

theorem same_angleEquations :
    RoleHingeAngleCertificates.RoleHingeAngleEquations
      sameTransitionFacts.roleAngle := by
  exact RoleHingeAngleCertificates.sameEquilateralRoleAngle_angleEquations

theorem opposite_angleEquations :
    RoleHingeAngleCertificates.RoleHingeAngleEquations
      oppositeTransitionFacts.roleAngle := by
  exact RoleHingeAngleCertificates.oppositeEquilateralRoleAngle_angleEquations

/-- The same-branch concrete transition has all successor connector unit
edges. -/
theorem same_connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges samePlaceNext :=
  sameTransitionFacts.connector_unit_edges

/-- The opposite-branch concrete transition has all successor connector unit
edges. -/
theorem opposite_connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges oppositePlaceNext :=
  oppositeTransitionFacts.connector_unit_edges

/-- Concrete same/opposite connector-unit transition facts. -/
def sameOppositeTransitionFacts :
    SameOppositeRoleHingeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.sameOppositeRoleHingeConnectorTransitionFacts
    sameTransitionFacts oppositeTransitionFacts

@[simp]
theorem sameOppositeTransitionFacts_same :
    sameOppositeTransitionFacts.same = sameTransitionFacts :=
  rfl

@[simp]
theorem sameOppositeTransitionFacts_opposite :
    sameOppositeTransitionFacts.opposite = oppositeTransitionFacts :=
  rfl

/-- Projection of the concrete connector facts to the Figure 2 transition
obligation package used by generated chains. -/
def figure2TransitionObligations :
    Figure2Certificate.SameOppositeTransitionObligations :=
  sameOppositeTransitionFacts.toFigure2TransitionObligations

@[simp]
theorem figure2TransitionObligations_samePlaceNext :
    figure2TransitionObligations.samePlaceNext = samePlaceNext :=
  rfl

@[simp]
theorem figure2TransitionObligations_oppositePlaceNext :
    figure2TransitionObligations.oppositePlaceNext = oppositePlaceNext :=
  rfl

theorem figure2TransitionObligations_same_connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges
      figure2TransitionObligations.samePlaceNext := by
  simpa using same_connector_unit_edges

theorem figure2TransitionObligations_opposite_connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges
      figure2TransitionObligations.oppositePlaceNext := by
  simpa using opposite_connector_unit_edges

/-- The concrete same-branch equilateral role angles make both same-source
connector-port pairs unit edges. -/
theorem same_port_pair_unit_edges :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (samePlaceNext source T1_1) (samePlaceNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (samePlaceNext source T0_0) (samePlaceNext source T0_2) = 1) := by
  exact
    RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
      samePlaceNext RoleHingeAngleCertificates.sameEquilateralRoleAngle
      samePlaceNext_realizes_role
      RoleHingeAngleCertificates.sameEquilateralRoleAngle_angleEquations

/-- The concrete opposite-branch equilateral role angles make both same-source
connector-port pairs unit edges. -/
theorem opposite_port_pair_unit_edges :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (oppositePlaceNext source T1_1)
          (oppositePlaceNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (oppositePlaceNext source T0_0)
          (oppositePlaceNext source T0_2) = 1) := by
  exact
    RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
      oppositePlaceNext RoleHingeAngleCertificates.oppositeEquilateralRoleAngle
      oppositePlaceNext_realizes_role
      RoleHingeAngleCertificates.oppositeEquilateralRoleAngle_angleEquations

/-- Same/opposite concrete connector maps have all four same-source port-pair
unit-edge facts. -/
theorem sameOpposite_port_pair_unit_edges :
    And
      (And
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (samePlaceNext source T1_1) (samePlaceNext source T1_2) = 1)
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (samePlaceNext source T0_0) (samePlaceNext source T0_2) = 1))
      (And
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (oppositePlaceNext source T1_1)
            (oppositePlaceNext source T1_2) = 1)
        (forall source : LocalVertex -> R2,
          _root_.eucDist
            (oppositePlaceNext source T0_0)
            (oppositePlaceNext source T0_2) = 1)) := by
  exact And.intro same_port_pair_unit_edges opposite_port_pair_unit_edges

end

end RoleHingeConnectorConcrete
end PachToth
end ErdosProblems1066
