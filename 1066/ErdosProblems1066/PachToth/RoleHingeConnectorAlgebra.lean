import ErdosProblems1066.PachToth.HingeAlgebra
import ErdosProblems1066.PachToth.BaseTransitionRealization

set_option autoImplicit false

/-!
# Connector-port algebra for role-hinged transitions

This module exposes the connector facts that are automatic for a non-rigid
role-hinged transition. Once a connector target is realized as a unit hinge
point from its named source, the corresponding connector edge has length one.

For the two pairs of connector ports sharing a source, the remaining
equilateral condition is exactly the cosine-half equation for the two hinge
angles.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeConnectorAlgebra

open FiniteGraph
open FiniteGraph.LocalVertex
open Figure2EdgeTable

abbrev R2 := Prod Real Real

/-- A single role-realization equation gives the corresponding unit connector
edge by the unit-vector hinge lemma. -/
theorem role_port_unit_of_realizes
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : NextConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : NextConnectorRole),
        nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (source : LocalVertex -> R2) (u v : LocalVertex)
    (role : NextConnectorRole)
    (hrole : nextConnectorRole u v = some role) :
    _root_.eucDist (source u) (placeNext source v) = 1 := by
  rw [realizes_role source u v role hrole]
  exact HingeAlgebra.root_eucDist_center_hingePoint
    (source u) (roleAngle role)

/-- The `p` upper connector port is a unit edge. -/
theorem pToUpper_port_unit
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T2_2) (T.placeNext source T1_1) = 1 :=
  role_port_unit_of_realizes T.placeNext T.roleAngle T.realizes_role
    source T2_2 T1_1 NextConnectorRole.pToUpper rfl

/-- The `p` lower connector port is a unit edge. -/
theorem pToLower_port_unit
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T2_2) (T.placeNext source T1_2) = 1 :=
  role_port_unit_of_realizes T.placeNext T.roleAngle T.realizes_role
    source T2_2 T1_2 NextConnectorRole.pToLower rfl

/-- The `q` upper connector port is a unit edge. -/
theorem qToUpper_port_unit
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T4_0) (T.placeNext source T0_0) = 1 :=
  role_port_unit_of_realizes T.placeNext T.roleAngle T.realizes_role
    source T4_0 T0_0 NextConnectorRole.qToUpper rfl

/-- The `q` lower connector port is a unit edge. -/
theorem qToLower_port_unit
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2) :
    _root_.eucDist (source T4_0) (T.placeNext source T0_2) = 1 :=
  role_port_unit_of_realizes T.placeNext T.roleAngle T.realizes_role
    source T4_0 T0_2 NextConnectorRole.qToLower rfl

/-- The two hinge ports over one center form a unit chord exactly when their
angle difference has cosine `1 / 2`. -/
theorem hinge_ports_unit_iff_cos_sub_eq_half
    (center : R2) (theta phi : Real) :
    _root_.eucDist
        (UnitVectorGeometry.hingePoint center theta)
        (UnitVectorGeometry.hingePoint center phi) = 1 <->
      Real.cos (theta - phi) = 1 / 2 := by
  rw [HingeAlgebra.root_eucDist_hingePoint_hingePoint_eq_one_iff]
  constructor <;> intro h <;> nlinarith

/-- The two `p` connector ports are a unit edge exactly when the two `p`
role angles satisfy the equilateral cosine equation. -/
theorem p_ports_unit_iff_cos_sub_eq_half
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2) :
    _root_.eucDist (T.placeNext source T1_1) (T.placeNext source T1_2) = 1 <->
      Real.cos
        (T.roleAngle NextConnectorRole.pToUpper -
          T.roleAngle NextConnectorRole.pToLower) = 1 / 2 := by
  rw [T.realizes_role source T2_2 T1_1 NextConnectorRole.pToUpper rfl]
  rw [T.realizes_role source T2_2 T1_2 NextConnectorRole.pToLower rfl]
  exact hinge_ports_unit_iff_cos_sub_eq_half
    (source T2_2)
    (T.roleAngle NextConnectorRole.pToUpper)
    (T.roleAngle NextConnectorRole.pToLower)

/-- The two `q` connector ports are a unit edge exactly when the two `q`
role angles satisfy the equilateral cosine equation. -/
theorem q_ports_unit_iff_cos_sub_eq_half
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2) :
    _root_.eucDist (T.placeNext source T0_0) (T.placeNext source T0_2) = 1 <->
      Real.cos
        (T.roleAngle NextConnectorRole.qToUpper -
          T.roleAngle NextConnectorRole.qToLower) = 1 / 2 := by
  rw [T.realizes_role source T4_0 T0_0 NextConnectorRole.qToUpper rfl]
  rw [T.realizes_role source T4_0 T0_2 NextConnectorRole.qToLower rfl]
  exact hinge_ports_unit_iff_cos_sub_eq_half
    (source T4_0)
    (T.roleAngle NextConnectorRole.qToUpper)
    (T.roleAngle NextConnectorRole.qToLower)

/-- Connector-unit obligations for one role-hinged transition, restated from
the four named connector ports. -/
theorem connector_unit_edges
    (T : BaseTransitionRealization.RoleHingeTransition) :
    HingedTransitionInterface.ConnectorUnitEdges T.placeNext := by
  intro source u v hconn
  match HingeAlgebra.nextConnector_cases hconn with
  | Or.inl h =>
      rw [h.left, h.right]
      exact pToUpper_port_unit T source
  | Or.inr (Or.inl h) =>
      rw [h.left, h.right]
      exact pToLower_port_unit T source
  | Or.inr (Or.inr (Or.inl h)) =>
      rw [h.left, h.right]
      exact qToUpper_port_unit T source
  | Or.inr (Or.inr (Or.inr h)) =>
      rw [h.left, h.right]
      exact qToLower_port_unit T source

end RoleHingeConnectorAlgebra
end PachToth
end ErdosProblems1066

end
