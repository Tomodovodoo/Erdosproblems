import ErdosProblems1066.PachToth.Figure2EdgeTable
import ErdosProblems1066.PachToth.HingedTransitionInterface
import ErdosProblems1066.PachToth.ExactLocalGeometry
import ErdosProblems1066.PachToth.UnitVectorGeometry

set_option autoImplicit false

/-!
# Base hinged transition realization

This module turns named Figure 2 successor-connector role data into the
connector fields required by the same/opposite transition interfaces.  The
metric facts that are not forced by the role table and the unit-vector hinge
lemma remain explicit fields.
-/

namespace ErdosProblems1066
namespace PachToth
namespace BaseTransitionRealization

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The checked exact one-block placement used as the generated-chain base. -/
def exactBase : LocalVertex -> R2 :=
  ExactLocalGeometry.localPoint

/-- The exact base block has the checked one-block metric. -/
theorem exactBase_same_block_isometry :
    HingedTransitionInterface.BaseSameBlockIsometry exactBase := by
  intro u v
  simp [HingedTransitionInterface.referenceDistance, exactBase,
    OneBlockSoundness.oneBlockCertificate, OneBlockSoundness.oneBlockConfig,
    OneBlockSoundness.oneBlockPoint]

/-- Data for one transition whose proof-used connector targets are placed as
unit hinge points from their named connector sources. -/
structure RoleHingeTransition where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : Figure2EdgeTable.NextConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : Figure2EdgeTable.NextConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)
  preserves_same_block_distances :
    HingedTransitionInterface.PreservesSameBlockDistances placeNext

namespace RoleHingeTransition

/-- A named connector role is realized as a unit edge by the hinge lemma. -/
theorem role_connector_unit_edges
    (T : RoleHingeTransition)
    (source : LocalVertex -> R2) (u v : LocalVertex)
    (role : Figure2EdgeTable.NextConnectorRole)
    (hrole : Figure2EdgeTable.nextConnectorRole u v = some role) :
    _root_.eucDist (source u) (T.placeNext source v) = 1 := by
  rw [T.realizes_role source u v role hrole]
  exact UnitVectorGeometry.eucDist_center_hingePoint
    (source u) (T.roleAngle role)

/-- The finite role table covers the proof-used successor-connector relation,
so the role-level unit facts project to the interface connector obligation. -/
theorem connector_unit_edges
    (T : RoleHingeTransition) :
    HingedTransitionInterface.ConnectorUnitEdges T.placeNext := by
  intro source u v hconn
  exact Exists.elim (Figure2EdgeTable.nextConnector_has_role u v hconn)
    (fun role hrole => T.role_connector_unit_edges source u v role hrole)

/-- Package one role-hinged transition as the metric transition interface. -/
def toTransitionMetricObligations
    (T : RoleHingeTransition) :
    HingedTransitionInterface.TransitionMetricObligations where
  placeNext := T.placeNext
  preserves_same_block_distances := T.preserves_same_block_distances
  connector_unit_edges := T.connector_unit_edges

@[simp]
theorem toTransitionMetricObligations_placeNext
    (T : RoleHingeTransition) :
    T.toTransitionMetricObligations.placeNext = T.placeNext :=
  rfl

@[simp]
theorem toTransitionMetricObligations_preserves_same_block_distances
    (T : RoleHingeTransition) :
    T.toTransitionMetricObligations.preserves_same_block_distances =
      T.preserves_same_block_distances :=
  rfl

@[simp]
theorem toTransitionMetricObligations_connector_unit_edges
    (T : RoleHingeTransition) :
    T.toTransitionMetricObligations.connector_unit_edges =
      T.connector_unit_edges :=
  rfl

end RoleHingeTransition

/-- Same/opposite role-hinged transitions based at the exact local block. -/
structure BaseSameOppositeTransitionRealization where
  same : RoleHingeTransition
  opposite : RoleHingeTransition

namespace BaseSameOppositeTransitionRealization

/-- Project the role-hinged data to the same/opposite metric obligation
interface used by generated chains. -/
def toMetricObligations
    (T : BaseSameOppositeTransitionRealization) :
    HingedTransitionInterface.SameOppositeTransitionMetricObligations where
  base := exactBase
  base_same_block_isometry := exactBase_same_block_isometry
  same := T.same.toTransitionMetricObligations
  opposite := T.opposite.toTransitionMetricObligations

@[simp]
theorem toMetricObligations_base
    (T : BaseSameOppositeTransitionRealization) :
    T.toMetricObligations.base = exactBase :=
  rfl

@[simp]
theorem toMetricObligations_same
    (T : BaseSameOppositeTransitionRealization) :
    T.toMetricObligations.same =
      T.same.toTransitionMetricObligations :=
  rfl

@[simp]
theorem toMetricObligations_opposite
    (T : BaseSameOppositeTransitionRealization) :
    T.toMetricObligations.opposite =
      T.opposite.toTransitionMetricObligations :=
  rfl

@[simp]
theorem toMetricObligations_samePlaceNext
    (T : BaseSameOppositeTransitionRealization) :
    T.toMetricObligations.toFigure2TransitionObligations.samePlaceNext =
      T.same.placeNext :=
  rfl

@[simp]
theorem toMetricObligations_oppositePlaceNext
    (T : BaseSameOppositeTransitionRealization) :
    T.toMetricObligations.toFigure2TransitionObligations.oppositePlaceNext =
      T.opposite.placeNext :=
  rfl

/-- Same-transition connector obligations are obtained from the role table and
unit-vector hinge geometry. -/
theorem same_connector_unit_edges
    (T : BaseSameOppositeTransitionRealization) :
    HingedTransitionInterface.ConnectorUnitEdges T.same.placeNext :=
  T.same.connector_unit_edges

/-- Opposite-transition connector obligations are obtained from the role table
and unit-vector hinge geometry. -/
theorem opposite_connector_unit_edges
    (T : BaseSameOppositeTransitionRealization) :
    HingedTransitionInterface.ConnectorUnitEdges T.opposite.placeNext :=
  T.opposite.connector_unit_edges

/-- The same/opposite metric data forgets to the connector-only Figure 2
transition obligations. -/
def toFigure2TransitionObligations
    (T : BaseSameOppositeTransitionRealization) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  T.toMetricObligations.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (T : BaseSameOppositeTransitionRealization) :
    T.toFigure2TransitionObligations.samePlaceNext = T.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (T : BaseSameOppositeTransitionRealization) :
    T.toFigure2TransitionObligations.oppositePlaceNext =
      T.opposite.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_same
    (T : BaseSameOppositeTransitionRealization) :
    T.toFigure2TransitionObligations.same =
      T.toMetricObligations.sameTransition :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_opposite
    (T : BaseSameOppositeTransitionRealization) :
    T.toFigure2TransitionObligations.opposite =
      T.toMetricObligations.oppositeTransition :=
  rfl

end BaseSameOppositeTransitionRealization

end

end BaseTransitionRealization
end PachToth
end ErdosProblems1066
