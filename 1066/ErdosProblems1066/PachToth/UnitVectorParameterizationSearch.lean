import ErdosProblems1066.PachToth.UnitVectorGeometry
import ErdosProblems1066.PachToth.RoleHingeAngleCertificates
import ErdosProblems1066.PachToth.FlexibleExactLocalTransition

set_option autoImplicit false

/-!
# Unit-vector parameterization search surface

This module is a small search-facing wrapper around the flexible exact-local
transition interface.  A branch is parameterized by role angles and explicit
unit-vector coordinate equations.  The connector-unit equations then follow
from `UnitVectorGeometry`, while exact-local preservation is reduced to:

* the two angle-controlled port-pair equations, and
* explicit algebraic row equations for every other ordered local row.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace UnitVectorParameterizationSearch

open FiniteGraph

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

/-- One flexible branch written with unit-vector/angle variables.

The field `unit_vector_formula` is the coordinate parameterization needed by
search output: every named connector target is the source connector vertex plus
the unit vector at its role angle.
-/
structure UnitVectorBranchParameters where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  unit_vector_formula :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.add
            (source u) (UnitVectorGeometry.unitVec (roleAngle role))

namespace UnitVectorBranchParameters

/-- The unit-vector coordinate formula is exactly the role-hinge realization
equation used by the existing connector interfaces. -/
theorem realizes_role
    (P : UnitVectorBranchParameters) :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        P.placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (P.roleAngle role) := by
  intro source u v role hrole
  simpa [UnitVectorGeometry.hingePoint] using
    P.unit_vector_formula source u v role hrole

/-- Forget the parameterization to the flexible connector-unit branch data. -/
def toConnectorUnitRoleData
    (P : UnitVectorBranchParameters) :
    FlexibleExactLocalTransition.ConnectorUnitRoleData where
  placeNext := P.placeNext
  roleAngle := P.roleAngle
  realizes_role := P.realizes_role

@[simp]
theorem toConnectorUnitRoleData_placeNext
    (P : UnitVectorBranchParameters) :
    P.toConnectorUnitRoleData.placeNext = P.placeNext :=
  rfl

@[simp]
theorem toConnectorUnitRoleData_roleAngle
    (P : UnitVectorBranchParameters) :
    P.toConnectorUnitRoleData.roleAngle = P.roleAngle :=
  rfl

/-- The raw connector-unit equation for one named role edge. -/
theorem connector_unit_equation
    (P : UnitVectorBranchParameters)
    (source : LocalVertex -> R2) (u v : LocalVertex)
    (role : ConnectorRole)
    (hrole : Figure2EdgeTable.nextConnectorRole u v = some role) :
    _root_.eucDist (source u) (P.placeNext source v) = 1 := by
  rw [P.realizes_role source u v role hrole]
  exact UnitVectorGeometry.eucDist_center_hingePoint
    (source u) (P.roleAngle role)

/-- The parameterized branch realizes every directed connector as a unit edge. -/
theorem connector_unit_edges
    (P : UnitVectorBranchParameters) :
    HingedTransitionInterface.ConnectorUnitEdges P.placeNext := by
  exact P.toConnectorUnitRoleData.connector_unit_edges

/-- Angle equations give the two same-source port-pair unit equations. -/
theorem portPairUnitEdges_of_angleEquations
    (P : UnitVectorBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle) :
    And
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (P.placeNext source FiniteGraph.LocalVertex.T1_1)
          (P.placeNext source FiniteGraph.LocalVertex.T1_2) = 1)
      (forall source : LocalVertex -> R2,
        _root_.eucDist
          (P.placeNext source FiniteGraph.LocalVertex.T0_0)
          (P.placeNext source FiniteGraph.LocalVertex.T0_2) = 1) := by
  exact
    RoleHingeAngleCertificates.portPairUnitEdges_of_angleEquations_realizes
      P.placeNext P.roleAngle P.realizes_role A

/-- Explicit algebraic hypotheses for every exact-local row not already
controlled by the two role-angle port-pair equations. -/
structure NonAngleExactLocalRowHypotheses
    (P : UnitVectorBranchParameters) : Prop where
  row_sqDist :
    forall source : LocalVertex -> R2,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source ->
        forall u v : LocalVertex,
          Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v) ->
            RoleHingeSameBlockAlgebra.sqDist
                (P.placeNext source u) (P.placeNext source v) =
              ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4

namespace NonAngleExactLocalRowHypotheses

/-- Row-level access to the explicit non-angle algebraic hypotheses. -/
theorem sqDist
    {P : UnitVectorBranchParameters}
    (H : NonAngleExactLocalRowHypotheses P)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    {u v : LocalVertex}
    (hnot :
      Not (RoleHingeAngleCertificates.IsRoleAnglePortPair u v)) :
    RoleHingeSameBlockAlgebra.sqDist
        (P.placeNext source u) (P.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  H.row_sqDist source hsource u v hnot

end NonAngleExactLocalRowHypotheses

/-- Angle equations plus explicit non-angle row equations preserve the whole
exact-local squared-distance table. -/
theorem preservesExactLocalSqDistances_of_angleEquations_and_nonAngleRows
    (P : UnitVectorBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle)
    (H : NonAngleExactLocalRowHypotheses P) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances
      P.placeNext := by
  exact
    RoleHingeAngleCertificates.preservesExactLocalSqDistances_of_angleEquations_realizes_and_rest
      P.placeNext P.roleAngle P.realizes_role A
      (fun source hsource u v hnot =>
        H.row_sqDist source hsource u v hnot)

/-- Pointwise exact-local row preservation under explicit algebraic
hypotheses. -/
theorem exactLocal_row_sqDist_of_angleEquations_and_nonAngleRows
    (P : UnitVectorBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle)
    (H : NonAngleExactLocalRowHypotheses P)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (P.placeNext source u) (P.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  preservesExactLocalSqDistances_of_angleEquations_and_nonAngleRows
    P A H source hsource u v

/-- Package the exact-local conclusion as flexible branch data. -/
def exactLocalSameBlockData_of_angleEquations_and_nonAngleRows
    (P : UnitVectorBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle)
    (H : NonAngleExactLocalRowHypotheses P) :
    FlexibleExactLocalTransition.ExactLocalSameBlockData
      P.toConnectorUnitRoleData where
  preserves_exact_local_sq_distances :=
    preservesExactLocalSqDistances_of_angleEquations_and_nonAngleRows P A H

/-- Build one flexible exact-local branch from unit-vector coordinates, the
two angle equations, and explicit non-angle row equations. -/
def toFlexibleBranch
    (P : UnitVectorBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle)
    (H : NonAngleExactLocalRowHypotheses P) :
    FlexibleExactLocalTransition.Branch where
  connector := P.toConnectorUnitRoleData
  exactLocal :=
    P.exactLocalSameBlockData_of_angleEquations_and_nonAngleRows A H

@[simp]
theorem toFlexibleBranch_placeNext
    (P : UnitVectorBranchParameters)
    (A : RoleHingeAngleCertificates.RoleHingeAngleEquations P.roleAngle)
    (H : NonAngleExactLocalRowHypotheses P) :
    (P.toFlexibleBranch A H).placeNext = P.placeNext :=
  rfl

/-- Same/opposite unit-vector branch parameters. -/
structure SameOppositeParameters where
  same : UnitVectorBranchParameters
  opposite : UnitVectorBranchParameters

/-- Same/opposite algebraic hypotheses for building flexible branches. -/
structure SameOppositeAlgebraicHypotheses
    (P : SameOppositeParameters) : Prop where
  same_angle :
    RoleHingeAngleCertificates.RoleHingeAngleEquations P.same.roleAngle
  opposite_angle :
    RoleHingeAngleCertificates.RoleHingeAngleEquations P.opposite.roleAngle
  same_rows : NonAngleExactLocalRowHypotheses P.same
  opposite_rows : NonAngleExactLocalRowHypotheses P.opposite

namespace SameOppositeParameters

/-- Project same/opposite unit-vector parameters to the flexible transition
package under the explicit algebraic hypotheses. -/
def toFlexibleSameOpposite
    (P : SameOppositeParameters)
    (H : SameOppositeAlgebraicHypotheses P) :
    FlexibleExactLocalTransition.SameOpposite where
  same := P.same.toFlexibleBranch H.same_angle H.same_rows
  opposite := P.opposite.toFlexibleBranch H.opposite_angle H.opposite_rows

@[simp]
theorem toFlexibleSameOpposite_same_placeNext
    (P : SameOppositeParameters)
    (H : SameOppositeAlgebraicHypotheses P) :
    (P.toFlexibleSameOpposite H).same.placeNext =
      P.same.placeNext :=
  rfl

@[simp]
theorem toFlexibleSameOpposite_opposite_placeNext
    (P : SameOppositeParameters)
    (H : SameOppositeAlgebraicHypotheses P) :
    (P.toFlexibleSameOpposite H).opposite.placeNext =
      P.opposite.placeNext :=
  rfl

/-- Same-branch connector-unit equations from the unit-vector parameterization. -/
theorem same_connector_unit_edges
    (P : SameOppositeParameters) :
    HingedTransitionInterface.ConnectorUnitEdges P.same.placeNext :=
  P.same.connector_unit_edges

/-- Opposite-branch connector-unit equations from the unit-vector
parameterization. -/
theorem opposite_connector_unit_edges
    (P : SameOppositeParameters) :
    HingedTransitionInterface.ConnectorUnitEdges P.opposite.placeNext :=
  P.opposite.connector_unit_edges

/-- Same/opposite exact-local generated-transition preservation follows from
the explicit angle and row hypotheses. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (P : SameOppositeParameters)
    (H : SameOppositeAlgebraicHypotheses P) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      (P.toFlexibleSameOpposite H).toFigure2TransitionObligations :=
  (P.toFlexibleSameOpposite H).generatedTransitionsPreserveExactLocalSqDistances

end SameOppositeParameters

end UnitVectorBranchParameters
end UnitVectorParameterizationSearch
end PachToth
end ErdosProblems1066

end
