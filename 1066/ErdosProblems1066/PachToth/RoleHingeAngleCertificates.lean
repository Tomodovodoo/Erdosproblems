import ErdosProblems1066.PachToth.RoleHingeConnectorAlgebra

set_option autoImplicit false

/-!
# Angle certificates for role-hinged connector ports

The role-hinge connector algebra reduces the two same-source port-pair unit
edges to two cosine equations.  This module packages exactly those equations
and proves that they imply the corresponding `p` and `q` port-pair unit edges.

The concrete `pi / 3` helpers below are deliberately small: they show that the
certificate fields are non-vacuous without committing the global construction
to one final set of transition angles.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeAngleCertificates

open FiniteGraph
open FiniteGraph.LocalVertex
open Figure2EdgeTable

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev RoleHingeTransition :=
  BaseTransitionRealization.RoleHingeTransition

/-- The minimal angle data needed to make both same-source connector-port
pairs equilateral. -/
structure RoleHingeAngleEquations (roleAngle : ConnectorRole -> Real) :
    Prop where
  p_cos_sub_eq_half :
    Real.cos
      (roleAngle NextConnectorRole.pToUpper -
        roleAngle NextConnectorRole.pToLower) = 1 / 2
  q_cos_sub_eq_half :
    Real.cos
      (roleAngle NextConnectorRole.qToUpper -
        roleAngle NextConnectorRole.qToLower) = 1 / 2

/-- Both same-source port pairs in one role-hinged transition are unit edges. -/
structure RoleHingePortPairUnitEdges (T : RoleHingeTransition) : Prop where
  p_ports_unit :
    forall source : LocalVertex -> R2,
      _root_.eucDist
        (T.placeNext source T1_1) (T.placeNext source T1_2) = 1
  q_ports_unit :
    forall source : LocalVertex -> R2,
      _root_.eucDist
        (T.placeNext source T0_0) (T.placeNext source T0_2) = 1

/-- The `p` angle equation gives the `p` port-pair unit edge. -/
theorem p_ports_unit_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle)
    (source : LocalVertex -> R2) :
    _root_.eucDist
      (T.placeNext source T1_1) (T.placeNext source T1_2) = 1 := by
  exact
    (RoleHingeConnectorAlgebra.p_ports_unit_iff_cos_sub_eq_half
      T source).mpr A.p_cos_sub_eq_half

/-- The `q` angle equation gives the `q` port-pair unit edge. -/
theorem q_ports_unit_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle)
    (source : LocalVertex -> R2) :
    _root_.eucDist
      (T.placeNext source T0_0) (T.placeNext source T0_2) = 1 := by
  exact
    (RoleHingeConnectorAlgebra.q_ports_unit_iff_cos_sub_eq_half
      T source).mpr A.q_cos_sub_eq_half

/-- The two angle equations give both same-source port-pair unit edges. -/
def portPairUnitEdges_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle) :
    RoleHingePortPairUnitEdges T where
  p_ports_unit := p_ports_unit_of_angleEquations T A
  q_ports_unit := q_ports_unit_of_angleEquations T A

/-- A signed `pi / 3` angle difference has the required equilateral cosine. -/
theorem cos_sub_eq_half_of_sub_eq_pi_div_three
    {theta phi : Real}
    (h : theta - phi = Real.pi / 3) :
    Real.cos (theta - phi) = 1 / 2 := by
  rw [h]
  exact Real.cos_pi_div_three

/-- A signed `-pi / 3` angle difference has the required equilateral cosine. -/
theorem cos_sub_eq_half_of_sub_eq_neg_pi_div_three
    {theta phi : Real}
    (h : theta - phi = -(Real.pi / 3)) :
    Real.cos (theta - phi) = 1 / 2 := by
  rw [h, Real.cos_neg]
  exact Real.cos_pi_div_three

/-- A compact constructor from explicit signed `pi / 3` difference equations. -/
def angleEquations_of_signed_pi_div_three
    (roleAngle : ConnectorRole -> Real)
    (hp :
      roleAngle NextConnectorRole.pToUpper -
        roleAngle NextConnectorRole.pToLower = Real.pi / 3 \/
      roleAngle NextConnectorRole.pToUpper -
        roleAngle NextConnectorRole.pToLower = -(Real.pi / 3))
    (hq :
      roleAngle NextConnectorRole.qToUpper -
        roleAngle NextConnectorRole.qToLower = Real.pi / 3 \/
      roleAngle NextConnectorRole.qToUpper -
        roleAngle NextConnectorRole.qToLower = -(Real.pi / 3)) :
    RoleHingeAngleEquations roleAngle where
  p_cos_sub_eq_half := by
    cases hp with
    | inl h => exact cos_sub_eq_half_of_sub_eq_pi_div_three h
    | inr h => exact cos_sub_eq_half_of_sub_eq_neg_pi_div_three h
  q_cos_sub_eq_half := by
    cases hq with
    | inl h => exact cos_sub_eq_half_of_sub_eq_pi_div_three h
    | inr h => exact cos_sub_eq_half_of_sub_eq_neg_pi_div_three h

/-- A concrete same-branch equilateral angle assignment for the four roles. -/
def sameEquilateralRoleAngle : ConnectorRole -> Real
  | .pToUpper => 0
  | .pToLower => Real.pi / 3
  | .qToUpper => 2 * Real.pi / 3
  | .qToLower => Real.pi

/-- A concrete opposite-branch equilateral angle assignment for the four roles. -/
def oppositeEquilateralRoleAngle : ConnectorRole -> Real
  | .pToUpper => 0
  | .pToLower => -Real.pi / 3
  | .qToUpper => -2 * Real.pi / 3
  | .qToLower => -Real.pi

/-- The same-branch concrete angles satisfy the two port-pair equations. -/
theorem sameEquilateralRoleAngle_angleEquations :
    RoleHingeAngleEquations sameEquilateralRoleAngle := by
  refine
    angleEquations_of_signed_pi_div_three sameEquilateralRoleAngle
      (Or.inr ?_) (Or.inr ?_)
  · dsimp [sameEquilateralRoleAngle]
    ring
  · dsimp [sameEquilateralRoleAngle]
    ring

/-- The opposite-branch concrete angles satisfy the two port-pair equations. -/
theorem oppositeEquilateralRoleAngle_angleEquations :
    RoleHingeAngleEquations oppositeEquilateralRoleAngle := by
  refine
    angleEquations_of_signed_pi_div_three oppositeEquilateralRoleAngle
      (Or.inl ?_) (Or.inl ?_)
  · dsimp [oppositeEquilateralRoleAngle]
    ring
  · dsimp [oppositeEquilateralRoleAngle]
    ring

end RoleHingeAngleCertificates
end PachToth
end ErdosProblems1066

end
