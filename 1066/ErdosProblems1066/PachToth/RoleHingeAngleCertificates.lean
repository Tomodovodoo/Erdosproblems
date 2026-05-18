import ErdosProblems1066.PachToth.RoleHingeConnectorAlgebra
import ErdosProblems1066.PachToth.RoleHingeSameBlockAlgebra

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

/-- The two same-source port pairs whose exact local squared distances are
controlled directly by the role-angle equations. -/
def IsRoleAnglePortPair (u v : LocalVertex) : Prop :=
  (u = T1_1 /\ v = T1_2) \/
    (u = T1_2 /\ v = T1_1) \/
    (u = T0_0 /\ v = T0_2) \/
    (u = T0_2 /\ v = T0_0)

theorem roleAnglePortPair_symm
    {u v : LocalVertex}
    (h : IsRoleAnglePortPair u v) :
    IsRoleAnglePortPair v u := by
  match h with
  | Or.inl h => exact Or.inr (Or.inl (And.intro h.right h.left))
  | Or.inr (Or.inl h) => exact Or.inl (And.intro h.right h.left)
  | Or.inr (Or.inr (Or.inl h)) =>
      exact Or.inr (Or.inr (Or.inr (And.intro h.right h.left)))
  | Or.inr (Or.inr (Or.inr h)) =>
      exact Or.inr (Or.inr (Or.inl (And.intro h.right h.left)))

theorem sqDist_comm (p q : R2) :
    RoleHingeSameBlockAlgebra.sqDist p q =
      RoleHingeSameBlockAlgebra.sqDist q p := by
  simp [RoleHingeSameBlockAlgebra.sqDist]
  ring

theorem sqDist_eq_one_of_eucDist_eq_one
    {p q : R2}
    (h : _root_.eucDist p q = 1) :
    RoleHingeSameBlockAlgebra.sqDist p q = 1 := by
  have hsq : _root_.eucDist p q ^ 2 = (1 : Real) := by
    rw [h]
    norm_num
  rw [_root_.eucDist_sq] at hsq
  simpa [RoleHingeSameBlockAlgebra.sqDist] using hsq

theorem exactLocalNorm4_p_ports :
    (((ExactLocalGeometry.localNorm4 T1_1 T1_2 : Int) : Real) / 4) = 1 := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T1_1, T1_2]

theorem exactLocalNorm4_p_ports_symm :
    (((ExactLocalGeometry.localNorm4 T1_2 T1_1 : Int) : Real) / 4) = 1 := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T1_1, T1_2]

theorem exactLocalNorm4_q_ports :
    (((ExactLocalGeometry.localNorm4 T0_0 T0_2 : Int) : Real) / 4) = 1 := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T0_0, T0_2]

theorem exactLocalNorm4_q_ports_symm :
    (((ExactLocalGeometry.localNorm4 T0_2 T0_0 : Int) : Real) / 4) = 1 := by
  norm_num [ExactLocalGeometry.localNorm4, ExactLocalGeometry.localGrid,
    ExactLocalGeometry.GridPoint.norm4, T, T0_0, T0_2]

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

/-- The `p` angle equation gives the exact local squared-distance entry for
the `p` same-source port pair. -/
theorem p_ports_exactLocalSqDist_of_angleEquations_realizes
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
    RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T1_1) (placeNext source T1_2) =
      ((ExactLocalGeometry.localNorm4 T1_1 T1_2 : Int) : Real) / 4 := by
  have hunit :=
    p_ports_unit_of_angleEquations_realizes
      placeNext roleAngle realizes_role A source
  exact
    (sqDist_eq_one_of_eucDist_eq_one hunit).trans
      exactLocalNorm4_p_ports.symm

/-- The `p` angle equation also gives the reversed exact local squared-distance
entry for the same port pair. -/
theorem p_ports_exactLocalSqDist_symm_of_angleEquations_realizes
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
    RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T1_2) (placeNext source T1_1) =
      ((ExactLocalGeometry.localNorm4 T1_2 T1_1 : Int) : Real) / 4 := by
  have h :=
    p_ports_exactLocalSqDist_of_angleEquations_realizes
      placeNext roleAngle realizes_role A source
  calc
    RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T1_2) (placeNext source T1_1) =
      RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T1_1) (placeNext source T1_2) := by
        exact sqDist_comm _ _
    _ = ((ExactLocalGeometry.localNorm4 T1_1 T1_2 : Int) : Real) / 4 := h
    _ = ((ExactLocalGeometry.localNorm4 T1_2 T1_1 : Int) : Real) / 4 := by
        rw [exactLocalNorm4_p_ports, exactLocalNorm4_p_ports_symm]

/-- The `q` angle equation gives the exact local squared-distance entry for
the `q` same-source port pair. -/
theorem q_ports_exactLocalSqDist_of_angleEquations_realizes
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
    RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T0_0) (placeNext source T0_2) =
      ((ExactLocalGeometry.localNorm4 T0_0 T0_2 : Int) : Real) / 4 := by
  have hunit :=
    q_ports_unit_of_angleEquations_realizes
      placeNext roleAngle realizes_role A source
  exact
    (sqDist_eq_one_of_eucDist_eq_one hunit).trans
      exactLocalNorm4_q_ports.symm

/-- The `q` angle equation also gives the reversed exact local squared-distance
entry for the same port pair. -/
theorem q_ports_exactLocalSqDist_symm_of_angleEquations_realizes
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
    RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T0_2) (placeNext source T0_0) =
      ((ExactLocalGeometry.localNorm4 T0_2 T0_0 : Int) : Real) / 4 := by
  have h :=
    q_ports_exactLocalSqDist_of_angleEquations_realizes
      placeNext roleAngle realizes_role A source
  calc
    RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T0_2) (placeNext source T0_0) =
      RoleHingeSameBlockAlgebra.sqDist
        (placeNext source T0_0) (placeNext source T0_2) := by
        exact sqDist_comm _ _
    _ = ((ExactLocalGeometry.localNorm4 T0_0 T0_2 : Int) : Real) / 4 := h
    _ = ((ExactLocalGeometry.localNorm4 T0_2 T0_0 : Int) : Real) / 4 := by
        rw [exactLocalNorm4_q_ports, exactLocalNorm4_q_ports_symm]

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

/-- The `p` angle equation gives the exact local squared-distance entry for a
bundled role-hinge transition. -/
theorem p_ports_exactLocalSqDist_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle)
    (source : LocalVertex -> R2) :
    RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T1_1) (T.placeNext source T1_2) =
      ((ExactLocalGeometry.localNorm4 T1_1 T1_2 : Int) : Real) / 4 := by
  have hunit := p_ports_unit_of_angleEquations T A source
  exact
    (sqDist_eq_one_of_eucDist_eq_one hunit).trans
      exactLocalNorm4_p_ports.symm

/-- The reversed `p` port-pair exact local squared-distance entry for a
bundled role-hinge transition. -/
theorem p_ports_exactLocalSqDist_symm_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle)
    (source : LocalVertex -> R2) :
    RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T1_2) (T.placeNext source T1_1) =
      ((ExactLocalGeometry.localNorm4 T1_2 T1_1 : Int) : Real) / 4 := by
  have h := p_ports_exactLocalSqDist_of_angleEquations T A source
  calc
    RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T1_2) (T.placeNext source T1_1) =
      RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T1_1) (T.placeNext source T1_2) := by
        exact sqDist_comm _ _
    _ = ((ExactLocalGeometry.localNorm4 T1_1 T1_2 : Int) : Real) / 4 := h
    _ = ((ExactLocalGeometry.localNorm4 T1_2 T1_1 : Int) : Real) / 4 := by
        rw [exactLocalNorm4_p_ports, exactLocalNorm4_p_ports_symm]

/-- The `q` angle equation gives the exact local squared-distance entry for a
bundled role-hinge transition. -/
theorem q_ports_exactLocalSqDist_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle)
    (source : LocalVertex -> R2) :
    RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T0_0) (T.placeNext source T0_2) =
      ((ExactLocalGeometry.localNorm4 T0_0 T0_2 : Int) : Real) / 4 := by
  have hunit := q_ports_unit_of_angleEquations T A source
  exact
    (sqDist_eq_one_of_eucDist_eq_one hunit).trans
      exactLocalNorm4_q_ports.symm

/-- The reversed `q` port-pair exact local squared-distance entry for a
bundled role-hinge transition. -/
theorem q_ports_exactLocalSqDist_symm_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle)
    (source : LocalVertex -> R2) :
    RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T0_2) (T.placeNext source T0_0) =
      ((ExactLocalGeometry.localNorm4 T0_2 T0_0 : Int) : Real) / 4 := by
  have h := q_ports_exactLocalSqDist_of_angleEquations T A source
  calc
    RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T0_2) (T.placeNext source T0_0) =
      RoleHingeSameBlockAlgebra.sqDist
        (T.placeNext source T0_0) (T.placeNext source T0_2) := by
        exact sqDist_comm _ _
    _ = ((ExactLocalGeometry.localNorm4 T0_0 T0_2 : Int) : Real) / 4 := h
    _ = ((ExactLocalGeometry.localNorm4 T0_2 T0_0 : Int) : Real) / 4 := by
        rw [exactLocalNorm4_q_ports, exactLocalNorm4_q_ports_symm]

/-- The two angle equations give both same-source port-pair unit edges. -/
def portPairUnitEdges_of_angleEquations
    (T : RoleHingeTransition)
    (A : RoleHingeAngleEquations T.roleAngle) :
    RoleHingePortPairUnitEdges T where
  p_ports_unit := p_ports_unit_of_angleEquations T A
  q_ports_unit := q_ports_unit_of_angleEquations T A

/-- Angle equations discharge the two same-source port-pair rows of the exact
local squared-distance table; all other rows can be supplied by a finite
certificate or direct computation. -/
theorem matchesExactLocalSqDistances_of_angleEquations_realizes_and_rest
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (A : RoleHingeAngleEquations roleAngle)
    (source : LocalVertex -> R2)
    (hrest :
      forall u v : LocalVertex,
        Not (IsRoleAnglePortPair u v) ->
          RoleHingeSameBlockAlgebra.sqDist
              (placeNext source u) (placeNext source v) =
            ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
      (placeNext source) := by
  intro u v
  by_cases hpair : IsRoleAnglePortPair u v
  case pos =>
    match hpair with
    | Or.inl h =>
        cases h.left
        cases h.right
        exact
          p_ports_exactLocalSqDist_of_angleEquations_realizes
            placeNext roleAngle realizes_role A source
    | Or.inr (Or.inl h) =>
        cases h.left
        cases h.right
        exact
          p_ports_exactLocalSqDist_symm_of_angleEquations_realizes
            placeNext roleAngle realizes_role A source
    | Or.inr (Or.inr (Or.inl h)) =>
        cases h.left
        cases h.right
        exact
          q_ports_exactLocalSqDist_of_angleEquations_realizes
            placeNext roleAngle realizes_role A source
    | Or.inr (Or.inr (Or.inr h)) =>
        cases h.left
        cases h.right
        exact
          q_ports_exactLocalSqDist_symm_of_angleEquations_realizes
            placeNext roleAngle realizes_role A source
  case neg => exact hrest u v hpair

/-- Branch-level exact-local squared-distance preservation, with the two
angle-controlled port pairs removed from the remaining finite obligation. -/
theorem preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (A : RoleHingeAngleEquations roleAngle)
    (hrest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (placeNext source u) (placeNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      placeNext := by
  intro source hsource
  exact
    matchesExactLocalSqDistances_of_angleEquations_realizes_and_rest
      placeNext roleAngle realizes_role A source
      (hrest source hsource)

/-- Role-realization data alone supplies the existing connector-only Figure 2
same/opposite transition obligations. -/
def sameOppositeTransitionObligations_of_realizes
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (sameRoleAngle oppositeRoleAngle : ConnectorRole -> Real)
    (same_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          samePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (sameRoleAngle role))
    (opposite_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          oppositePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (oppositeRoleAngle role)) :
    Figure2Certificate.SameOppositeTransitionObligations where
  samePlaceNext := samePlaceNext
  oppositePlaceNext := oppositePlaceNext
  same_connector_unit_edges := by
    intro source u v hconn
    exact
      Exists.elim (Figure2EdgeTable.nextConnector_has_role u v hconn)
        (fun role hrole =>
          RoleHingeConnectorAlgebra.role_port_unit_of_realizes
            samePlaceNext sameRoleAngle same_realizes_role
            source u v role hrole)
  opposite_connector_unit_edges := by
    intro source u v hconn
    exact
      Exists.elim (Figure2EdgeTable.nextConnector_has_role u v hconn)
        (fun role hrole =>
          RoleHingeConnectorAlgebra.role_port_unit_of_realizes
            oppositePlaceNext oppositeRoleAngle opposite_realizes_role
            source u v role hrole)

@[simp]
theorem sameOppositeTransitionObligations_of_realizes_samePlaceNext
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (sameRoleAngle oppositeRoleAngle : ConnectorRole -> Real)
    (same_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          samePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (sameRoleAngle role))
    (opposite_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          oppositePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (oppositeRoleAngle role)) :
    (sameOppositeTransitionObligations_of_realizes
      samePlaceNext oppositePlaceNext sameRoleAngle oppositeRoleAngle
      same_realizes_role opposite_realizes_role).samePlaceNext =
        samePlaceNext := by
  rfl

@[simp]
theorem sameOppositeTransitionObligations_of_realizes_oppositePlaceNext
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (sameRoleAngle oppositeRoleAngle : ConnectorRole -> Real)
    (same_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          samePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (sameRoleAngle role))
    (opposite_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          oppositePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (oppositeRoleAngle role)) :
    (sameOppositeTransitionObligations_of_realizes
      samePlaceNext oppositePlaceNext sameRoleAngle oppositeRoleAngle
      same_realizes_role opposite_realizes_role).oppositePlaceNext =
        oppositePlaceNext := by
  rfl

/-- Same/opposite generated transitions preserve the exact local squared table
once each branch supplies the non-angle-controlled entries. -/
theorem sameOppositeGeneratedTransitionsPreserveExactLocalSqDistances
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (sameRoleAngle oppositeRoleAngle : ConnectorRole -> Real)
    (same_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          samePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (sameRoleAngle role))
    (opposite_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          oppositePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (oppositeRoleAngle role))
    (sameA : RoleHingeAngleEquations sameRoleAngle)
    (oppositeA : RoleHingeAngleEquations oppositeRoleAngle)
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (samePlaceNext source u) (samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (oppositePlaceNext source u) (oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      (sameOppositeTransitionObligations_of_realizes
        samePlaceNext oppositePlaceNext sameRoleAngle oppositeRoleAngle
        same_realizes_role opposite_realizes_role) := by
  intro orientation source hsource
  cases orientation with
  | same =>
      exact
        preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
          samePlaceNext sameRoleAngle same_realizes_role sameA same_rest
          source hsource
  | opposite =>
      exact
        preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
          oppositePlaceNext oppositeRoleAngle opposite_realizes_role
          oppositeA opposite_rest source hsource

/-- Same/opposite generated transitions preserve the exact local squared table
for any existing transition-obligation record whose selected maps are the
role-angle maps. -/
theorem sameOppositeGeneratedTransitionsPreserveExactLocalSqDistances_of_obligations_eq
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (sameRoleAngle oppositeRoleAngle : ConnectorRole -> Real)
    (hsamePlace : O.samePlaceNext = samePlaceNext)
    (hoppositePlace : O.oppositePlaceNext = oppositePlaceNext)
    (same_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          samePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (sameRoleAngle role))
    (opposite_realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        nextConnectorRole u v = some role ->
          oppositePlaceNext source v =
            UnitVectorGeometry.hingePoint
              (source u) (oppositeRoleAngle role))
    (sameA : RoleHingeAngleEquations sameRoleAngle)
    (oppositeA : RoleHingeAngleEquations oppositeRoleAngle)
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (samePlaceNext source u) (samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (oppositePlaceNext source u) (oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      O := by
  intro orientation source hsource
  cases orientation with
  | same =>
      have hpres :=
        preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
          samePlaceNext sameRoleAngle same_realizes_role sameA same_rest
      have hmatch := hpres source hsource
      simpa [Figure2Certificate.SameOppositeTransitionObligations.transitionFor,
        Figure2Certificate.SameOppositeTransitionObligations.same,
        Figure2Certificate.sameTransition, hsamePlace] using hmatch
  | opposite =>
      have hpres :=
        preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
          oppositePlaceNext oppositeRoleAngle opposite_realizes_role
          oppositeA opposite_rest
      have hmatch := hpres source hsource
      simpa [Figure2Certificate.SameOppositeTransitionObligations.transitionFor,
        Figure2Certificate.SameOppositeTransitionObligations.opposite,
        Figure2Certificate.oppositeTransition, hoppositePlace] using hmatch

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

/-- Same/opposite concrete equilateral role-angle data supplies the existing
connector-only Figure 2 transition obligations. -/
def sameOppositeTransitionObligations_of_equilateralRoleAngles
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
    Figure2Certificate.SameOppositeTransitionObligations :=
  sameOppositeTransitionObligations_of_realizes
    samePlaceNext oppositePlaceNext
    sameEquilateralRoleAngle oppositeEquilateralRoleAngle
    same_realizes_role opposite_realizes_role

/-- Same/opposite concrete equilateral role-angle data preserves the exact
local squared-distance table once the non-angle-controlled entries are
certified. -/
theorem sameOppositeGeneratedTransitionsPreserveExactLocalSqDistances_of_equilateralRoleAngles
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
              (source u) (oppositeEquilateralRoleAngle role))
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (samePlaceNext source u) (samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (oppositePlaceNext source u) (oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      (sameOppositeTransitionObligations_of_equilateralRoleAngles
        samePlaceNext oppositePlaceNext
        same_realizes_role opposite_realizes_role) := by
  exact
    sameOppositeGeneratedTransitionsPreserveExactLocalSqDistances
      samePlaceNext oppositePlaceNext
      sameEquilateralRoleAngle oppositeEquilateralRoleAngle
      same_realizes_role opposite_realizes_role
      sameEquilateralRoleAngle_angleEquations
      oppositeEquilateralRoleAngle_angleEquations
      same_rest opposite_rest

/-- Same/opposite concrete equilateral role-angle data gives the exact-local
generated-transition obligation for any already-built Figure 2 transition
obligation record using those same maps. -/
theorem sameOppositeExactLocal_of_equilateralRoleAngles_obligations_eq
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    (samePlaceNext oppositePlaceNext :
      (LocalVertex -> R2) -> LocalVertex -> R2)
    (hsamePlace : O.samePlaceNext = samePlaceNext)
    (hoppositePlace : O.oppositePlaceNext = oppositePlaceNext)
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
              (source u) (oppositeEquilateralRoleAngle role))
    (same_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (samePlaceNext source u) (samePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4)
    (opposite_rest :
      forall source : LocalVertex -> R2,
        RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
          forall u v : LocalVertex,
            Not (IsRoleAnglePortPair u v) ->
              RoleHingeSameBlockAlgebra.sqDist
                  (oppositePlaceNext source u) (oppositePlaceNext source v) =
                ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      O := by
  exact
    sameOppositeGeneratedTransitionsPreserveExactLocalSqDistances_of_obligations_eq
      O samePlaceNext oppositePlaceNext
      sameEquilateralRoleAngle oppositeEquilateralRoleAngle
      hsamePlace hoppositePlace
      same_realizes_role opposite_realizes_role
      sameEquilateralRoleAngle_angleEquations
      oppositeEquilateralRoleAngle_angleEquations
      same_rest opposite_rest

end RoleHingeAngleCertificates
end PachToth
end ErdosProblems1066

end
