import ErdosProblems1066.PachToth.HingeAlgebra
import ErdosProblems1066.PachToth.BaseTransitionRealization

set_option autoImplicit false

/-!
# Connector equation closure

This module closes the proof-used connector unit obligations from explicit
real connector equations.  It does not solve those equations and it does not
infer same-block metric preservation; both remain supplied data.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace ConnectorEquationClosure

open FiniteGraph
open FiniteGraph.LocalVertex

abbrev R2 := Prod Real Real

/-- Move the displacement from `baseCenter` to `target` so that it starts at
the currently placed source center. -/
def carryDisplacement (baseCenter sourceCenter target : R2) : R2 :=
  (sourceCenter.1 + (target.1 - baseCenter.1),
    sourceCenter.2 + (target.2 - baseCenter.2))

theorem root_eucDist_carryDisplacement
    (baseCenter sourceCenter target : R2) :
    _root_.eucDist sourceCenter
        (carryDisplacement baseCenter sourceCenter target) =
      _root_.eucDist baseCenter target := by
  unfold _root_.eucDist carryDisplacement
  congr 1
  ring

/-- The connector target `v`, read from connector source `u`, with its
explicit translated-base displacement carried to the current source block. -/
def carriedConnectorTarget
    (offset : R2) (source : LocalVertex -> R2)
    (u v : LocalVertex) : R2 :=
  carryDisplacement (BaseTransitionRealization.exactBase u) (source u)
    (AffineLocalGeometry.translatedLocalPoint offset v)

/-- A transition map that realizes the four proof-used connector targets from
the algebraic offset equations.  Values away from those four targets are left
as the source placement, since this file only closes connector obligations. -/
def equationPlaceNext
    (offset : R2) (source : LocalVertex -> R2) :
    LocalVertex -> R2
  | .tri 1 1 => carriedConnectorTarget offset source T2_2 T1_1
  | .tri 1 2 => carriedConnectorTarget offset source T2_2 T1_2
  | .tri 0 0 => carriedConnectorTarget offset source T4_0 T0_0
  | .tri 0 2 => carriedConnectorTarget offset source T4_0 T0_2
  | v => source v

theorem translated_T2_2_T1_1_unit_of_eq211
    (offset : R2)
    (h211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_1) = 1 := by
  simpa [BaseTransitionRealization.exactBase] using
    (HingeAlgebra.translated_T2_2_T1_1_unit_iff_eq211 offset).2 h211

theorem translated_T2_2_T1_2_unit_of_eq212
    (offset : R2)
    (h212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (BaseTransitionRealization.exactBase T2_2)
        (AffineLocalGeometry.translatedLocalPoint offset T1_2) = 1 := by
  simpa [BaseTransitionRealization.exactBase] using
    (HingeAlgebra.translated_T2_2_T1_2_unit_iff_eq212 offset).2 h212

theorem translated_T4_0_T0_0_unit_of_eq400
    (offset : R2)
    (h400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (BaseTransitionRealization.exactBase T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_0) = 1 := by
  simpa [BaseTransitionRealization.exactBase] using
    (HingeAlgebra.translated_T4_0_T0_0_unit_iff_eq400 offset).2 h400

theorem translated_T4_0_T0_2_unit_of_eq402
    (offset : R2)
    (h402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (BaseTransitionRealization.exactBase T4_0)
        (AffineLocalGeometry.translatedLocalPoint offset T0_2) = 1 := by
  simpa [BaseTransitionRealization.exactBase] using
    (HingeAlgebra.translated_T4_0_T0_2_unit_iff_eq402 offset).2 h402

theorem carried_T2_2_T1_1_unit_of_eq211
    (offset : R2) (source : LocalVertex -> R2)
    (h211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (source T2_2)
        (carriedConnectorTarget offset source T2_2 T1_1) = 1 := by
  rw [carriedConnectorTarget, root_eucDist_carryDisplacement]
  exact translated_T2_2_T1_1_unit_of_eq211 offset h211

theorem carried_T2_2_T1_2_unit_of_eq212
    (offset : R2) (source : LocalVertex -> R2)
    (h212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (source T2_2)
        (carriedConnectorTarget offset source T2_2 T1_2) = 1 := by
  rw [carriedConnectorTarget, root_eucDist_carryDisplacement]
  exact translated_T2_2_T1_2_unit_of_eq212 offset h212

theorem carried_T4_0_T0_0_unit_of_eq400
    (offset : R2) (source : LocalVertex -> R2)
    (h400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (source T4_0)
        (carriedConnectorTarget offset source T4_0 T0_0) = 1 := by
  rw [carriedConnectorTarget, root_eucDist_carryDisplacement]
  exact translated_T4_0_T0_0_unit_of_eq400 offset h400

theorem carried_T4_0_T0_2_unit_of_eq402
    (offset : R2) (source : LocalVertex -> R2)
    (h402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h) :
    _root_.eucDist (source T4_0)
        (carriedConnectorTarget offset source T4_0 T0_2) = 1 := by
  rw [carriedConnectorTarget, root_eucDist_carryDisplacement]
  exact translated_T4_0_T0_2_unit_of_eq402 offset h402

/-- Explicit connector equations close all connector unit obligations for the
equation-carried transition map. -/
theorem equationPlaceNext_connector_unit_edges_of_equations
    (offset : R2)
    (h211 :
      ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h)
    (h212 :
      ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h)
    (h400 :
      ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h)
    (h402 :
      ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h) :
    HingedTransitionInterface.ConnectorUnitEdges
      (equationPlaceNext offset) := by
  intro source u v hconn
  rcases HingeAlgebra.nextConnector_cases hconn with h211case |
      h212case | h400case | h402case
  · rw [h211case.1, h211case.2]
    exact carried_T2_2_T1_1_unit_of_eq211 offset source h211
  · rw [h212case.1, h212case.2]
    exact carried_T2_2_T1_2_unit_of_eq212 offset source h212
  · rw [h400case.1, h400case.2]
    exact carried_T4_0_T0_0_unit_of_eq400 offset source h400
  · rw [h402case.1, h402case.2]
    exact carried_T4_0_T0_2_unit_of_eq402 offset source h402

/-- One transition whose connector targets are closed by explicit algebraic
connector equations.  Same-block preservation is deliberately a field. -/
structure EquationTransition where
  offset : R2
  eq211 :
    ConnectorEquationFacts.eq211 offset.1 offset.2 ExactLocalGeometry.h
  eq212 :
    ConnectorEquationFacts.eq212 offset.1 offset.2 ExactLocalGeometry.h
  eq400 :
    ConnectorEquationFacts.eq400 offset.1 offset.2 ExactLocalGeometry.h
  eq402 :
    ConnectorEquationFacts.eq402 offset.1 offset.2 ExactLocalGeometry.h
  preserves_same_block_distances :
    HingedTransitionInterface.PreservesSameBlockDistances
      (equationPlaceNext offset)

namespace EquationTransition

/-- The transition map attached to an equation transition. -/
def placeNext (T : EquationTransition) :
    (LocalVertex -> R2) -> LocalVertex -> R2 :=
  equationPlaceNext T.offset

theorem connector_unit_edges
    (T : EquationTransition) :
    HingedTransitionInterface.ConnectorUnitEdges T.placeNext :=
  equationPlaceNext_connector_unit_edges_of_equations
    T.offset T.eq211 T.eq212 T.eq400 T.eq402

/-- Package one equation transition as metric transition data. -/
def toTransitionMetricObligations
    (T : EquationTransition) :
    HingedTransitionInterface.TransitionMetricObligations where
  placeNext := T.placeNext
  preserves_same_block_distances := T.preserves_same_block_distances
  connector_unit_edges := T.connector_unit_edges

@[simp]
theorem toTransitionMetricObligations_placeNext
    (T : EquationTransition) :
    T.toTransitionMetricObligations.placeNext = T.placeNext :=
  rfl

@[simp]
theorem toTransitionMetricObligations_connector_unit_edges
    (T : EquationTransition) :
    T.toTransitionMetricObligations.connector_unit_edges =
      T.connector_unit_edges :=
  rfl

end EquationTransition

/-- Same/opposite equation-carried transitions based at the exact local block. -/
structure SameOppositeEquationTransition where
  same : EquationTransition
  opposite : EquationTransition

namespace SameOppositeEquationTransition

/-- Project same/opposite equation data to the generated-chain metric
obligation interface. -/
def toMetricObligations
    (T : SameOppositeEquationTransition) :
    HingedTransitionInterface.SameOppositeTransitionMetricObligations where
  base := BaseTransitionRealization.exactBase
  base_same_block_isometry :=
    BaseTransitionRealization.exactBase_same_block_isometry
  same := T.same.toTransitionMetricObligations
  opposite := T.opposite.toTransitionMetricObligations

@[simp]
theorem toMetricObligations_base
    (T : SameOppositeEquationTransition) :
    T.toMetricObligations.base = BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toMetricObligations_same
    (T : SameOppositeEquationTransition) :
    T.toMetricObligations.same =
      T.same.toTransitionMetricObligations :=
  rfl

@[simp]
theorem toMetricObligations_opposite
    (T : SameOppositeEquationTransition) :
    T.toMetricObligations.opposite =
      T.opposite.toTransitionMetricObligations :=
  rfl

theorem same_connector_unit_edges
    (T : SameOppositeEquationTransition) :
    HingedTransitionInterface.ConnectorUnitEdges T.same.placeNext :=
  T.same.connector_unit_edges

theorem opposite_connector_unit_edges
    (T : SameOppositeEquationTransition) :
    HingedTransitionInterface.ConnectorUnitEdges T.opposite.placeNext :=
  T.opposite.connector_unit_edges

/-- The same/opposite metric data forgets to the connector-only Figure 2
transition obligations. -/
def toFigure2TransitionObligations
    (T : SameOppositeEquationTransition) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  T.toMetricObligations.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (T : SameOppositeEquationTransition) :
    T.toFigure2TransitionObligations.samePlaceNext =
      T.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (T : SameOppositeEquationTransition) :
    T.toFigure2TransitionObligations.oppositePlaceNext =
      T.opposite.placeNext :=
  rfl

end SameOppositeEquationTransition

end ConnectorEquationClosure
end PachToth
end ErdosProblems1066

end
