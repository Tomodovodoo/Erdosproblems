import ErdosProblems1066.PachToth.GeneratedMetricClosure

set_option autoImplicit false

/-!
# Search-facing role-hinged transition data

This module gives a direct input shape for role-hinged transition searches.
The real-valued angle assignments, role-realization equalities, same-block
metric preservation, generated closure equations, and separation facts are all
kept as explicit fields.  The constructors below only project those fields to
the existing role-hinge and generated-metric interfaces.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeTransitionSearch

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev RoleHingeTransition :=
  BaseTransitionRealization.RoleHingeTransition
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions

/-- Raw facts for one role-hinged transition map. -/
structure RoleHingeTransitionFacts where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)
  preserves_same_block_distances :
    HingedTransitionInterface.PreservesSameBlockDistances placeNext

/-- Constructor spelling for search output with all numeric facts explicit. -/
def roleHingeTransitionFacts
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        Figure2EdgeTable.nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role))
    (preserves_same_block_distances :
      HingedTransitionInterface.PreservesSameBlockDistances placeNext) :
    RoleHingeTransitionFacts where
  placeNext := placeNext
  roleAngle := roleAngle
  realizes_role := realizes_role
  preserves_same_block_distances := preserves_same_block_distances

namespace RoleHingeTransitionFacts

/-- Project raw search facts to the existing one-transition role-hinge
interface. -/
def toRoleHingeTransition
    (F : RoleHingeTransitionFacts) :
    RoleHingeTransition where
  placeNext := F.placeNext
  roleAngle := F.roleAngle
  realizes_role := F.realizes_role
  preserves_same_block_distances := F.preserves_same_block_distances

@[simp]
theorem toRoleHingeTransition_placeNext
    (F : RoleHingeTransitionFacts) :
    F.toRoleHingeTransition.placeNext = F.placeNext :=
  rfl

@[simp]
theorem toRoleHingeTransition_roleAngle
    (F : RoleHingeTransitionFacts) :
    F.toRoleHingeTransition.roleAngle = F.roleAngle :=
  rfl

@[simp]
theorem toRoleHingeTransition_realizes_role
    (F : RoleHingeTransitionFacts) :
    F.toRoleHingeTransition.realizes_role = F.realizes_role :=
  rfl

@[simp]
theorem toRoleHingeTransition_preserves_same_block_distances
    (F : RoleHingeTransitionFacts) :
    F.toRoleHingeTransition.preserves_same_block_distances =
      F.preserves_same_block_distances :=
  rfl

/-- The role table and hinge lemma turn the explicit role facts into the
connector-unit obligation. -/
theorem connector_unit_edges
    (F : RoleHingeTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges F.placeNext := by
  exact F.toRoleHingeTransition.connector_unit_edges

/-- Project raw search facts to the one-transition metric interface. -/
def toTransitionMetricObligations
    (F : RoleHingeTransitionFacts) :
    HingedTransitionInterface.TransitionMetricObligations :=
  F.toRoleHingeTransition.toTransitionMetricObligations

@[simp]
theorem toTransitionMetricObligations_placeNext
    (F : RoleHingeTransitionFacts) :
    F.toTransitionMetricObligations.placeNext = F.placeNext :=
  rfl

@[simp]
theorem toTransitionMetricObligations_preserves_same_block_distances
    (F : RoleHingeTransitionFacts) :
    F.toTransitionMetricObligations.preserves_same_block_distances =
      F.preserves_same_block_distances :=
  rfl

@[simp]
theorem toTransitionMetricObligations_connector_unit_edges
    (F : RoleHingeTransitionFacts) :
    F.toTransitionMetricObligations.connector_unit_edges =
      F.connector_unit_edges :=
  rfl

end RoleHingeTransitionFacts

/-- Raw same/opposite role-hinged transition facts. -/
structure SameOppositeRoleHingeTransitionFacts where
  same : RoleHingeTransitionFacts
  opposite : RoleHingeTransitionFacts

/-- Constructor spelling for search output containing both orientations. -/
def sameOppositeRoleHingeTransitionFacts
    (same opposite : RoleHingeTransitionFacts) :
    SameOppositeRoleHingeTransitionFacts where
  same := same
  opposite := opposite

namespace SameOppositeRoleHingeTransitionFacts

/-- Project raw same/opposite search facts to the generated-metric transition
package. -/
def toRoleHingeTransitions
    (F : SameOppositeRoleHingeTransitionFacts) :
    RoleHingeTransitions where
  same := F.same.toRoleHingeTransition
  opposite := F.opposite.toRoleHingeTransition

@[simp]
theorem toRoleHingeTransitions_same
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toRoleHingeTransitions.same = F.same.toRoleHingeTransition :=
  rfl

@[simp]
theorem toRoleHingeTransitions_opposite
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toRoleHingeTransitions.opposite =
      F.opposite.toRoleHingeTransition :=
  rfl

/-- Project raw same/opposite search facts to the strongest metric interface. -/
def toMetricObligations
    (F : SameOppositeRoleHingeTransitionFacts) :
    HingedTransitionInterface.SameOppositeTransitionMetricObligations :=
  F.toRoleHingeTransitions.toMetricObligations

@[simp]
theorem toMetricObligations_base
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toMetricObligations.base = BaseTransitionRealization.exactBase :=
  rfl

@[simp]
theorem toMetricObligations_same
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toMetricObligations.same =
      F.same.toTransitionMetricObligations :=
  rfl

@[simp]
theorem toMetricObligations_opposite
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toMetricObligations.opposite =
      F.opposite.toTransitionMetricObligations :=
  rfl

/-- Project raw same/opposite search facts to the Figure 2 transition
obligations used by generated chains. -/
def toFigure2TransitionObligations
    (F : SameOppositeRoleHingeTransitionFacts) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  F.toRoleHingeTransitions.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toFigure2TransitionObligations.samePlaceNext =
      F.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toFigure2TransitionObligations.oppositePlaceNext =
      F.opposite.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_same
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toFigure2TransitionObligations.same =
      F.toMetricObligations.sameTransition :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_opposite
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toFigure2TransitionObligations.opposite =
      F.toMetricObligations.oppositeTransition :=
  rfl

/-- Same-branch connector obligations obtained from the role facts. -/
theorem same_connector_unit_edges
    (F : SameOppositeRoleHingeTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges F.same.placeNext :=
  F.same.connector_unit_edges

/-- Opposite-branch connector obligations obtained from the role facts. -/
theorem opposite_connector_unit_edges
    (F : SameOppositeRoleHingeTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges F.opposite.placeNext :=
  F.opposite.connector_unit_edges

/-- The projected generated-chain transition package preserves same-block
distances. -/
theorem preservesSameBlockDistances
    (F : SameOppositeRoleHingeTransitionFacts) :
    GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
      F.toFigure2TransitionObligations := by
  exact
    GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
      F.toRoleHingeTransitions

end SameOppositeRoleHingeTransitionFacts

/-- One generated-closure search certificate using direct role-hinged
transition facts. -/
structure GeneratedClosureSearchData (k : Nat) (hk : 0 < k) where
  transitions : SameOppositeRoleHingeTransitionFacts
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  separated :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace GeneratedClosureSearchData

/-- Project one search certificate to the generated-metric closure data. -/
def toRoleHingedGeneratedClosureData
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureData k hk where
  transitions := G.transitions.toRoleHingeTransitions
  orientation := G.orientation
  closure := G.closure
  separated := G.separated

@[simp]
theorem toRoleHingedGeneratedClosureData_transitions
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    G.toRoleHingedGeneratedClosureData.transitions =
      G.transitions.toRoleHingeTransitions :=
  rfl

@[simp]
theorem toRoleHingedGeneratedClosureData_orientation
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    G.toRoleHingedGeneratedClosureData.orientation = G.orientation :=
  rfl

/-- Project one search certificate to reduced generated metric hypotheses. -/
def toGeneratedReducedMetricHypotheses
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation :=
  GeneratedMetricClosure.generatedReducedMetricHypotheses
    G.transitions.toRoleHingeTransitions hk G.orientation G.separated

@[simp]
theorem toGeneratedReducedMetricHypotheses_separated
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    G.toGeneratedReducedMetricHypotheses.separated = G.separated :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_baseSameBlock
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    G.toGeneratedReducedMetricHypotheses.base_same_block_isometry =
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry :=
  rfl

@[simp]
theorem toGeneratedReducedMetricHypotheses_transitionPreserves
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    G.toGeneratedReducedMetricHypotheses.transition_preserves_same_block_distances =
      G.transitions.preservesSameBlockDistances :=
  rfl

/-- The explicit closed-placement certificate projected from one search
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate k hk :=
  G.toRoleHingedGeneratedClosureData.toExplicitTransitionClosedPlacementCertificate

/-- The closed placement projected from one search certificate. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  G.toRoleHingedGeneratedClosureData.toClosedPlacement

/-- The exact-block target projected from one search certificate. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureSearchData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) :=
  G.toRoleHingedGeneratedClosureData.targetUpperConstructionFiveSixteenAt_exactBlock

end GeneratedClosureSearchData

/-- Family of generated-closure search certificates with all closure and
separation facts explicit for every positive length. -/
structure GeneratedClosureSearchFamily where
  transitions : SameOppositeRoleHingeTransitionFacts
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

namespace GeneratedClosureSearchFamily

/-- Project a search family to the generated-metric closure family. -/
def toRoleHingedGeneratedClosureFamily
    (F : GeneratedClosureSearchFamily) :
    GeneratedMetricClosure.RoleHingedGeneratedClosureFamily where
  transitions := F.transitions.toRoleHingeTransitions
  orientation := F.orientation
  closure := F.closure
  separated := F.separated

@[simp]
theorem toRoleHingedGeneratedClosureFamily_transitions
    (F : GeneratedClosureSearchFamily) :
    F.toRoleHingedGeneratedClosureFamily.transitions =
      F.transitions.toRoleHingeTransitions :=
  rfl

@[simp]
theorem toRoleHingedGeneratedClosureFamily_orientation
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    F.toRoleHingedGeneratedClosureFamily.orientation k hk =
      F.orientation k hk :=
  rfl

/-- One member of the family as bundled generated-closure search data. -/
def data
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedClosureSearchData k hk where
  transitions := F.transitions
  orientation := F.orientation k hk
  closure := F.closure k hk
  separated := F.separated k hk

@[simp]
theorem data_transitions
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (F.data k hk).transitions = F.transitions :=
  rfl

@[simp]
theorem data_orientation
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (F.data k hk).orientation = F.orientation k hk :=
  rfl

/-- Reduced metric hypotheses for one member of the family. -/
def reducedMetricHypotheses
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (F.data k hk).toGeneratedReducedMetricHypotheses

@[simp]
theorem reducedMetricHypotheses_separated
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (F.reducedMetricHypotheses k hk).separated = F.separated k hk :=
  rfl

@[simp]
theorem reducedMetricHypotheses_transitionPreserves
    (F : GeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    (F.reducedMetricHypotheses k hk).transition_preserves_same_block_distances =
      F.transitions.preservesSameBlockDistances :=
  rfl

/-- Closed placements for every positive length in a search family. -/
def closedPlacementFamily
    (F : GeneratedClosureSearchFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  F.toRoleHingedGeneratedClosureFamily.closedPlacementFamily

/-- Exact-multiple target theorem obtained from the direct role-hinged search
family. -/
theorem targetUpperConstructionFiveSixteen
    (F : GeneratedClosureSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen :=
  F.toRoleHingedGeneratedClosureFamily.targetUpperConstructionFiveSixteen

end GeneratedClosureSearchFamily

end

end RoleHingeTransitionSearch
end PachToth
end ErdosProblems1066
