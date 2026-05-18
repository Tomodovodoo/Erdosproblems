import ErdosProblems1066.PachToth.GeneratedClosedChain

set_option autoImplicit false

/-!
# Hinged transition metric interface

This file records the metric obligations for proposed same/opposite hinged
transition maps.  The existing `Figure2Certificate` transition certificate is
connector-only; the structures below keep the additional geometry explicit:

* every transition preserves all same-block distances,
* every transition realizes the directed connector edges as unit edges, and
* the chosen base block is isometric to the checked one-block certificate.
-/

namespace ErdosProblems1066
namespace PachToth
namespace HingedTransitionInterface

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The reference same-block distance in the checked one-block certificate. -/
def referenceDistance (u v : LocalVertex) : Real :=
  _root_.eucDist
    (OneBlockSoundness.oneBlockCertificate.config.pts
      (BlockPartition.localVertexEquivFin16 u))
    (OneBlockSoundness.oneBlockCertificate.config.pts
      (BlockPartition.localVertexEquivFin16 v))

/-- A placed base block is isometric to the checked one-block certificate. -/
def BaseSameBlockIsometry (base : LocalVertex -> R2) : Prop :=
  forall u v : LocalVertex,
    _root_.eucDist (base u) (base v) = referenceDistance u v

/-- A transition preserves all distances inside the block it produces. -/
def PreservesSameBlockDistances
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall (source : LocalVertex -> R2) (u v : LocalVertex),
    _root_.eucDist (placeNext source u) (placeNext source v) =
      _root_.eucDist (source u) (source v)

/-- A transition realizes every directed next-block connector as a unit edge. -/
def ConnectorUnitEdges
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2) : Prop :=
  forall (source : LocalVertex -> R2) (u v : LocalVertex),
    CrossBlock.NextConnector u v ->
      _root_.eucDist (source u) (placeNext source v) = 1

/-- Metric obligations for one proposed next-block transition map. -/
structure TransitionMetricObligations where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  preserves_same_block_distances : PreservesSameBlockDistances placeNext
  connector_unit_edges : ConnectorUnitEdges placeNext

namespace TransitionMetricObligations

/-- Forget the metric fields and keep only the transition map with its
orientation label. -/
def toOrientedTransition
    (T : TransitionMetricObligations)
    (orientation : OrientationData.BlockOrientation) :
    OrientationData.OrientedTransition where
  orientation := orientation
  placeNext := T.placeNext

@[simp]
theorem toOrientedTransition_orientation
    (T : TransitionMetricObligations)
    (orientation : OrientationData.BlockOrientation) :
    (T.toOrientedTransition orientation).orientation = orientation :=
  rfl

@[simp]
theorem toOrientedTransition_placeNext
    (T : TransitionMetricObligations)
    (orientation : OrientationData.BlockOrientation) :
    (T.toOrientedTransition orientation).placeNext = T.placeNext :=
  rfl

end TransitionMetricObligations

/-- Same/opposite transition obligations, together with the base block needed
to turn distance-preservation into same-block isometry along a generated
orbit. -/
structure SameOppositeTransitionMetricObligations where
  base : LocalVertex -> R2
  base_same_block_isometry : BaseSameBlockIsometry base
  same : TransitionMetricObligations
  opposite : TransitionMetricObligations

namespace SameOppositeTransitionMetricObligations

/-- Select the metric transition data for an orientation label. -/
def transitionMetricFor
    (O : SameOppositeTransitionMetricObligations) :
    OrientationData.BlockOrientation -> TransitionMetricObligations
  | OrientationData.BlockOrientation.same => O.same
  | OrientationData.BlockOrientation.opposite => O.opposite

@[simp]
theorem transitionMetricFor_same
    (O : SameOppositeTransitionMetricObligations) :
    O.transitionMetricFor OrientationData.BlockOrientation.same = O.same :=
  rfl

@[simp]
theorem transitionMetricFor_opposite
    (O : SameOppositeTransitionMetricObligations) :
    O.transitionMetricFor OrientationData.BlockOrientation.opposite =
      O.opposite :=
  rfl

/-- The same-orientation transition map, retaining only data. -/
def sameTransition
    (O : SameOppositeTransitionMetricObligations) :
    OrientationData.OrientedTransition :=
  O.same.toOrientedTransition OrientationData.BlockOrientation.same

/-- The opposite-orientation transition map, retaining only data. -/
def oppositeTransition
    (O : SameOppositeTransitionMetricObligations) :
    OrientationData.OrientedTransition :=
  O.opposite.toOrientedTransition OrientationData.BlockOrientation.opposite

@[simp]
theorem sameTransition_orientation
    (O : SameOppositeTransitionMetricObligations) :
    O.sameTransition.orientation = OrientationData.BlockOrientation.same :=
  rfl

@[simp]
theorem oppositeTransition_orientation
    (O : SameOppositeTransitionMetricObligations) :
    O.oppositeTransition.orientation =
      OrientationData.BlockOrientation.opposite :=
  rfl

/-- A forgetful conversion to the existing connector-only same/opposite
certificate.  This does not construct geometry: it merely projects out the
connector-unit fields from the richer metric obligations. -/
def toFigure2TransitionObligations
    (O : SameOppositeTransitionMetricObligations) :
    Figure2Certificate.SameOppositeTransitionObligations where
  samePlaceNext := O.same.placeNext
  oppositePlaceNext := O.opposite.placeNext
  same_connector_unit_edges := O.same.connector_unit_edges
  opposite_connector_unit_edges := O.opposite.connector_unit_edges

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (O : SameOppositeTransitionMetricObligations) :
    O.toFigure2TransitionObligations.samePlaceNext = O.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (O : SameOppositeTransitionMetricObligations) :
    O.toFigure2TransitionObligations.oppositePlaceNext =
      O.opposite.placeNext :=
  rfl

/-- The converted same transition is the same metric transition map. -/
@[simp]
theorem toFigure2TransitionObligations_same
    (O : SameOppositeTransitionMetricObligations) :
    O.toFigure2TransitionObligations.same = O.sameTransition :=
  rfl

/-- The converted opposite transition is the opposite metric transition map. -/
@[simp]
theorem toFigure2TransitionObligations_opposite
    (O : SameOppositeTransitionMetricObligations) :
    O.toFigure2TransitionObligations.opposite = O.oppositeTransition :=
  rfl

/-- The converted transition selected by an orientation preserves same-block
distances. -/
theorem transitionFor_preserves_same_block_distances
    (O : SameOppositeTransitionMetricObligations)
    (orientation : OrientationData.BlockOrientation)
    (source : LocalVertex -> R2) (u v : LocalVertex) :
    _root_.eucDist
        ((O.toFigure2TransitionObligations.transitionFor orientation).placeNext
          source u)
        ((O.toFigure2TransitionObligations.transitionFor orientation).placeNext
          source v) =
      _root_.eucDist (source u) (source v) := by
  cases orientation
  · exact O.same.preserves_same_block_distances source u v
  · exact O.opposite.preserves_same_block_distances source u v

/-- The converted transition selected by an orientation realizes the connector
unit edges. -/
theorem transitionFor_connector_unit_edges
    (O : SameOppositeTransitionMetricObligations)
    (orientation : OrientationData.BlockOrientation)
    (source : LocalVertex -> R2) (u v : LocalVertex)
    (hconn : CrossBlock.NextConnector u v) :
    _root_.eucDist (source u)
        ((O.toFigure2TransitionObligations.transitionFor orientation).placeNext
          source v) = 1 := by
  cases orientation
  · exact O.same.connector_unit_edges source u v hconn
  · exact O.opposite.connector_unit_edges source u v hconn

/-- Along a generated orbit, the explicit base isometry and transition
distance-preservation obligations supply same-block isometry for every block. -/
theorem generatedPoint_same_block_isometry
    (O : SameOppositeTransitionMetricObligations)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    forall (i : Fin k) (u v : LocalVertex),
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint
          O.toFigure2TransitionObligations hk O.base orientation i u)
        (GeneratedClosedChain.generatedPoint
          O.toFigure2TransitionObligations hk O.base orientation i v) =
        referenceDistance u v := by
  exact
    GeneratedClosedChain.generatedPoint_same_block_isometry
      O.toFigure2TransitionObligations hk O.base orientation
      O.base_same_block_isometry
      (O.transitionFor_preserves_same_block_distances)

end SameOppositeTransitionMetricObligations

end

end HingedTransitionInterface
end PachToth
end ErdosProblems1066
