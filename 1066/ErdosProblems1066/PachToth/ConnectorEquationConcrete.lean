import ErdosProblems1066.PachToth.EquationTransitionClosure

set_option autoImplicit false

/-!
# Concrete connector-equation transition inputs

This module is a narrow audited facade over `ConnectorEquationClosure` and
`EquationTransitionClosure`.  A single translated exact block cannot satisfy
the four connector equations, so no concrete offset is constructed here.
Instead, the raw real equation facts are kept as explicit fields and projected
through the existing transition-closure interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace ConnectorEquationConcrete

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- The explicit real data needed to feed one equation-carried transition into
`EquationTransitionClosure`.  The four equation fields are intentionally raw:
the exact-block obstruction below shows they are not currently constructible
from a real offset. -/
structure ConnectorEquationTransitionFacts where
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
      (ConnectorEquationClosure.equationPlaceNext offset)

namespace ConnectorEquationTransitionFacts

/-- Project raw equation facts to the existing one-transition closure package. -/
def toEquationTransitionData
    (F : ConnectorEquationTransitionFacts) :
    EquationTransitionClosure.EquationTransitionData :=
  EquationTransitionClosure.equationTransitionOfEquations F.offset
    F.eq211 F.eq212 F.eq400 F.eq402
    F.preserves_same_block_distances

@[simp]
theorem toEquationTransitionData_offset
    (F : ConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.offset = F.offset :=
  rfl

@[simp]
theorem toEquationTransitionData_eq211
    (F : ConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.eq211 = F.eq211 :=
  rfl

@[simp]
theorem toEquationTransitionData_eq212
    (F : ConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.eq212 = F.eq212 :=
  rfl

@[simp]
theorem toEquationTransitionData_eq400
    (F : ConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.eq400 = F.eq400 :=
  rfl

@[simp]
theorem toEquationTransitionData_eq402
    (F : ConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.eq402 = F.eq402 :=
  rfl

@[simp]
theorem toEquationTransitionData_preservesSameBlock
    (F : ConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.preserves_same_block_distances =
      F.preserves_same_block_distances :=
  rfl

/-- Project raw equation facts directly to the transition metric interface. -/
def toTransitionMetricObligations
    (F : ConnectorEquationTransitionFacts) :
    HingedTransitionInterface.TransitionMetricObligations :=
  EquationTransitionClosure.transitionMetricObligationsOfEquations F.offset
    F.eq211 F.eq212 F.eq400 F.eq402
    F.preserves_same_block_distances

@[simp]
theorem toTransitionMetricObligations_placeNext
    (F : ConnectorEquationTransitionFacts) :
    F.toTransitionMetricObligations.placeNext =
      ConnectorEquationClosure.equationPlaceNext F.offset :=
  rfl

@[simp]
theorem toTransitionMetricObligations_preservesSameBlock
    (F : ConnectorEquationTransitionFacts) :
    F.toTransitionMetricObligations.preserves_same_block_distances =
      F.preserves_same_block_distances :=
  rfl

theorem connector_unit_edges
    (F : ConnectorEquationTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges
      (ConnectorEquationClosure.equationPlaceNext F.offset) := by
  exact F.toEquationTransitionData.connector_unit_edges

/-- Full four-equation translated exact-block data is contradictory. -/
theorem false_of_connector_equation_transition_facts
    (F : ConnectorEquationTransitionFacts) :
    False := by
  exact
    ConnectorEquationFacts.not_all_four_connector_equations
      F.offset.1 F.offset.2 ExactLocalGeometry.h
      ExactLocalGeometry.GridPoint.h_sq
      (And.intro F.eq211
        (And.intro F.eq212
          (And.intro F.eq400 F.eq402)))

end ConnectorEquationTransitionFacts

/-- Same/opposite equation-transition facts, kept at the smallest raw-field
level needed to invoke `EquationTransitionClosure`. -/
structure SameOppositeConnectorEquationTransitionFacts where
  same : ConnectorEquationTransitionFacts
  opposite : ConnectorEquationTransitionFacts

namespace SameOppositeConnectorEquationTransitionFacts

/-- Project same/opposite raw facts to the existing same/opposite equation
transition closure package. -/
def toEquationTransitionData
    (F : SameOppositeConnectorEquationTransitionFacts) :
    EquationTransitionClosure.SameOppositeEquationTransitionData :=
  EquationTransitionClosure.sameOppositeEquationTransitionOfEquations
    F.same.offset F.opposite.offset
    F.same.eq211 F.same.eq212 F.same.eq400 F.same.eq402
    F.same.preserves_same_block_distances
    F.opposite.eq211 F.opposite.eq212 F.opposite.eq400 F.opposite.eq402
    F.opposite.preserves_same_block_distances

@[simp]
theorem toEquationTransitionData_same_offset
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.same.offset = F.same.offset :=
  rfl

@[simp]
theorem toEquationTransitionData_opposite_offset
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.opposite.offset = F.opposite.offset :=
  rfl

@[simp]
theorem toEquationTransitionData_same_eq211
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.same.eq211 = F.same.eq211 :=
  rfl

@[simp]
theorem toEquationTransitionData_same_eq212
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.same.eq212 = F.same.eq212 :=
  rfl

@[simp]
theorem toEquationTransitionData_same_eq400
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.same.eq400 = F.same.eq400 :=
  rfl

@[simp]
theorem toEquationTransitionData_same_eq402
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.same.eq402 = F.same.eq402 :=
  rfl

@[simp]
theorem toEquationTransitionData_opposite_eq211
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.opposite.eq211 = F.opposite.eq211 :=
  rfl

@[simp]
theorem toEquationTransitionData_opposite_eq212
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.opposite.eq212 = F.opposite.eq212 :=
  rfl

@[simp]
theorem toEquationTransitionData_opposite_eq400
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.opposite.eq400 = F.opposite.eq400 :=
  rfl

@[simp]
theorem toEquationTransitionData_opposite_eq402
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toEquationTransitionData.opposite.eq402 = F.opposite.eq402 :=
  rfl

/-- Project same/opposite raw facts to the generated-chain metric interface. -/
def toMetricObligations
    (F : SameOppositeConnectorEquationTransitionFacts) :
    HingedTransitionInterface.SameOppositeTransitionMetricObligations :=
  EquationTransitionClosure.sameOppositeTransitionMetricObligationsOfEquations
    F.same.offset F.opposite.offset
    F.same.eq211 F.same.eq212 F.same.eq400 F.same.eq402
    F.same.preserves_same_block_distances
    F.opposite.eq211 F.opposite.eq212 F.opposite.eq400 F.opposite.eq402
    F.opposite.preserves_same_block_distances

@[simp]
theorem toMetricObligations_base
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toMetricObligations.base = BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toMetricObligations_same_placeNext
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toMetricObligations.same.placeNext =
      ConnectorEquationClosure.equationPlaceNext F.same.offset :=
  rfl

@[simp]
theorem toMetricObligations_opposite_placeNext
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toMetricObligations.opposite.placeNext =
      ConnectorEquationClosure.equationPlaceNext F.opposite.offset :=
  rfl

theorem same_connector_unit_edges
    (F : SameOppositeConnectorEquationTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges
      (ConnectorEquationClosure.equationPlaceNext F.same.offset) := by
  exact F.same.connector_unit_edges

theorem opposite_connector_unit_edges
    (F : SameOppositeConnectorEquationTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges
      (ConnectorEquationClosure.equationPlaceNext F.opposite.offset) := by
  exact F.opposite.connector_unit_edges

/-- Forget the metric fields to the connector-only Figure 2 transition
interface used by generated chains. -/
def toFigure2TransitionObligations
    (F : SameOppositeConnectorEquationTransitionFacts) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  F.toMetricObligations.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toFigure2TransitionObligations.samePlaceNext =
      ConnectorEquationClosure.equationPlaceNext F.same.offset :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (F : SameOppositeConnectorEquationTransitionFacts) :
    F.toFigure2TransitionObligations.oppositePlaceNext =
      ConnectorEquationClosure.equationPlaceNext F.opposite.offset :=
  rfl

/-- Same/opposite full translated equation data is contradictory already in
the same branch. -/
theorem false_of_sameOpposite_connector_equation_transition_facts
    (F : SameOppositeConnectorEquationTransitionFacts) :
    False :=
  F.same.false_of_connector_equation_transition_facts

end SameOppositeConnectorEquationTransitionFacts

/-- Existing one-transition equation-closure data is uninhabited for the exact
height because its four real connector equations are inconsistent. -/
theorem false_of_equationTransitionData
    (T : EquationTransitionClosure.EquationTransitionData) :
    False := by
  exact
    ConnectorEquationFacts.not_all_four_connector_equations
      T.offset.1 T.offset.2 ExactLocalGeometry.h
      ExactLocalGeometry.GridPoint.h_sq
      (And.intro T.eq211
        (And.intro T.eq212
          (And.intro T.eq400 T.eq402)))

/-- Existing same/opposite equation-closure data is also uninhabited, since
its same branch already contains one full four-equation translate package. -/
theorem false_of_sameOppositeEquationTransitionData
    (T : EquationTransitionClosure.SameOppositeEquationTransitionData) :
    False :=
  false_of_equationTransitionData T.same

end

end ConnectorEquationConcrete
end PachToth
end ErdosProblems1066
