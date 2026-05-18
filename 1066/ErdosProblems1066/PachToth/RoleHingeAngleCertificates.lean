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

/-- The `p` angle equation gives the raw `p` port-pair unit edge. -/
theorem p_ports_unit_of_angleEquations_realizes
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (A : RoleHingeAngleEquations roleAngle)
    (source : LocalVertex -> R2) :
    _root_.eucDist
      (placeNext source T1_1) (placeNext source T1_2) = 1 := by
  rw [realizes_role source T2_2 T1_1 NextConnectorRole.pToUpper rfl]
  rw [realizes_role source T2_2 T1_2 NextConnectorRole.pToLower rfl]
  exact
    (RoleHingeConnectorAlgebra.hinge_ports_unit_iff_cos_sub_eq_half
      (source T2_2)
      (roleAngle NextConnectorRole.pToUpper)
      (roleAngle NextConnectorRole.pToLower)).mpr A.p_cos_sub_eq_half

/-- The `q` angle equation gives the raw `q` port-pair unit edge. -/
theorem q_ports_unit_of_angleEquations_realizes
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (A : RoleHingeAngleEquations roleAngle)
    (source : LocalVertex -> R2) :
    _root_.eucDist
      (placeNext source T0_0) (placeNext source T0_2) = 1 := by
  rw [realizes_role source T4_0 T0_0 NextConnectorRole.qToUpper rfl]
  rw [realizes_role source T4_0 T0_2 NextConnectorRole.qToLower rfl]
  exact
    (RoleHingeConnectorAlgebra.hinge_ports_unit_iff_cos_sub_eq_half
      (source T4_0)
      (roleAngle NextConnectorRole.qToUpper)
      (roleAngle NextConnectorRole.qToLower)).mpr A.q_cos_sub_eq_half

/-- The two raw role-realization equations and angle equations give both
same-source port-pair unit-edge facts. -/
theorem portPairUnitEdges_of_angleEquations_realizes
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (A : RoleHingeAngleEquations roleAngle) :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (placeNext source T1_1) (placeNext source T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (placeNext source T0_0) (placeNext source T0_2) = 1) := by
  exact
    And.intro
      (fun source =>
        p_ports_unit_of_angleEquations_realizes
          placeNext roleAngle realizes_role A source)
      (fun source =>
        q_ports_unit_of_angleEquations_realizes
          placeNext roleAngle realizes_role A source)

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

/-- The same-branch `p` roles differ by `-pi / 3`. -/
theorem sameEquilateralRoleAngle_p_sub_eq_neg_pi_div_three :
    sameEquilateralRoleAngle NextConnectorRole.pToUpper -
      sameEquilateralRoleAngle NextConnectorRole.pToLower =
        -(Real.pi / 3) := by
  dsimp [sameEquilateralRoleAngle]
  ring

/-- The same-branch `q` roles differ by `-pi / 3`. -/
theorem sameEquilateralRoleAngle_q_sub_eq_neg_pi_div_three :
    sameEquilateralRoleAngle NextConnectorRole.qToUpper -
      sameEquilateralRoleAngle NextConnectorRole.qToLower =
        -(Real.pi / 3) := by
  dsimp [sameEquilateralRoleAngle]
  ring

/-- The opposite-branch `p` roles differ by `pi / 3`. -/
theorem oppositeEquilateralRoleAngle_p_sub_eq_pi_div_three :
    oppositeEquilateralRoleAngle NextConnectorRole.pToUpper -
      oppositeEquilateralRoleAngle NextConnectorRole.pToLower =
        Real.pi / 3 := by
  dsimp [oppositeEquilateralRoleAngle]
  ring

/-- The opposite-branch `q` roles differ by `pi / 3`. -/
theorem oppositeEquilateralRoleAngle_q_sub_eq_pi_div_three :
    oppositeEquilateralRoleAngle NextConnectorRole.qToUpper -
      oppositeEquilateralRoleAngle NextConnectorRole.qToLower =
        Real.pi / 3 := by
  dsimp [oppositeEquilateralRoleAngle]
  ring

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

/-- Any role-angle assignment equal to the same-branch concrete angles
satisfies the two port-pair equations. -/
theorem angleEquations_of_eq_sameEquilateralRoleAngle
    {roleAngle : ConnectorRole -> Real}
    (h : roleAngle = sameEquilateralRoleAngle) :
    RoleHingeAngleEquations roleAngle := by
  rw [h]
  exact sameEquilateralRoleAngle_angleEquations

/-- Any role-angle assignment equal to the opposite-branch concrete angles
satisfies the two port-pair equations. -/
theorem angleEquations_of_eq_oppositeEquilateralRoleAngle
    {roleAngle : ConnectorRole -> Real}
    (h : roleAngle = oppositeEquilateralRoleAngle) :
    RoleHingeAngleEquations roleAngle := by
  rw [h]
  exact oppositeEquilateralRoleAngle_angleEquations

/-- Same/opposite concrete role angles satisfy the two port-pair equation
facts. -/
theorem sameOppositeEquilateralRoleAngle_angleEquations :
    And
      (RoleHingeAngleEquations sameEquilateralRoleAngle)
      (RoleHingeAngleEquations oppositeEquilateralRoleAngle) := by
  exact
    And.intro
      sameEquilateralRoleAngle_angleEquations
      oppositeEquilateralRoleAngle_angleEquations

/-- A transition whose role angles are the same-branch concrete angles has both
same-source port-pair unit edges. -/
theorem portPairUnitEdges_of_eq_sameEquilateralRoleAngle
    (T : RoleHingeTransition)
    (h : T.roleAngle = sameEquilateralRoleAngle) :
    RoleHingePortPairUnitEdges T :=
  portPairUnitEdges_of_angleEquations T
    (angleEquations_of_eq_sameEquilateralRoleAngle h)

/-- A transition whose role angles are the opposite-branch concrete angles has
both same-source port-pair unit edges. -/
theorem portPairUnitEdges_of_eq_oppositeEquilateralRoleAngle
    (T : RoleHingeTransition)
    (h : T.roleAngle = oppositeEquilateralRoleAngle) :
    RoleHingePortPairUnitEdges T :=
  portPairUnitEdges_of_angleEquations T
    (angleEquations_of_eq_oppositeEquilateralRoleAngle h)

/-- Raw same/opposite role-hinge maps using the concrete equilateral angles
have all four same-source port-pair unit-edge facts. -/
theorem sameOppositePortPairUnitEdges_of_equilateralRoleAngles
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (same_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          samePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (sameEquilateralRoleAngle role))
    (opposite_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          oppositePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (oppositeEquilateralRoleAngle role)) :
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
  exact
    And.intro
      (portPairUnitEdges_of_angleEquations_realizes
        samePlaceNext sameEquilateralRoleAngle same_realizes_role
        sameEquilateralRoleAngle_angleEquations)
      (portPairUnitEdges_of_angleEquations_realizes
        oppositePlaceNext oppositeEquilateralRoleAngle opposite_realizes_role
        oppositeEquilateralRoleAngle_angleEquations)

end RoleHingeAngleCertificates
end PachToth
end ErdosProblems1066

end
