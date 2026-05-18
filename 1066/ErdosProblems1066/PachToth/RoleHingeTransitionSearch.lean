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
open FiniteGraph.LocalVertex

noncomputable section

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole
abbrev RoleHingeTransition :=
  BaseTransitionRealization.RoleHingeTransition
abbrev RoleHingeTransitions :=
  GeneratedMetricClosure.RoleHingeTransitions

/-- Role-realization equations alone imply every successor connector has
unit length; no same-block preservation is used. -/
theorem connector_unit_edges_of_realizes
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        Figure2EdgeTable.nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role)) :
    HingedTransitionInterface.ConnectorUnitEdges placeNext := by
  intro source u v hconn
  exact Exists.elim (Figure2EdgeTable.nextConnector_has_role u v hconn)
    (fun role hrole => by
      rw [realizes_role source u v role hrole]
      exact UnitVectorGeometry.eucDist_center_hingePoint
        (source u) (roleAngle role))

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

/-- Weaker raw facts for one role-hinged transition map.  This keeps the
role-angle data and the connector-unit consequences, but omits the impossible
arbitrary-source same-block preservation field. -/
structure RoleHingeConnectorTransitionFacts where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)
  connector_unit_edges :
    HingedTransitionInterface.ConnectorUnitEdges placeNext

/-- Constructor spelling for the weaker connector-level transition facts.
The connector-unit field is derived from the role table and hinge geometry. -/
def roleHingeConnectorTransitionFacts
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        Figure2EdgeTable.nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role)) :
    RoleHingeConnectorTransitionFacts where
  placeNext := placeNext
  roleAngle := roleAngle
  realizes_role := realizes_role
  connector_unit_edges :=
    connector_unit_edges_of_realizes placeNext roleAngle realizes_role

namespace RoleHingeConnectorTransitionFacts

@[simp]
theorem mk_connector_unit_edges
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (roleAngle : ConnectorRole -> Real)
    (realizes_role :
      forall (source : LocalVertex -> R2) (u v : LocalVertex)
        (role : ConnectorRole),
        Figure2EdgeTable.nextConnectorRole u v = some role ->
          placeNext source v =
            UnitVectorGeometry.hingePoint (source u) (roleAngle role)) :
    (roleHingeConnectorTransitionFacts placeNext roleAngle
      realizes_role).connector_unit_edges =
      connector_unit_edges_of_realizes placeNext roleAngle realizes_role :=
  rfl

/-- The two `p`-connector targets in the produced block are always the two
hinge endpoints from the source `T2_2`; this uses only role realization. -/
theorem pPort_pair_distance_eq_hinge_distance
    (F : RoleHingeConnectorTransitionFacts)
    (source : LocalVertex -> R2) :
    _root_.eucDist (F.placeNext source T1_1) (F.placeNext source T1_2) =
      _root_.eucDist
        (UnitVectorGeometry.hingePoint (source T2_2)
          (F.roleAngle (.pToUpper : ConnectorRole)))
        (UnitVectorGeometry.hingePoint (source T2_2)
          (F.roleAngle (.pToLower : ConnectorRole))) := by
  rw [F.realizes_role source T2_2 T1_1
    (.pToUpper : ConnectorRole) rfl]
  rw [F.realizes_role source T2_2 T1_2
    (.pToLower : ConnectorRole) rfl]

/-- The two `q`-connector targets in the produced block are always the two
hinge endpoints from the source `T4_0`; this uses only role realization. -/
theorem qPort_pair_distance_eq_hinge_distance
    (F : RoleHingeConnectorTransitionFacts)
    (source : LocalVertex -> R2) :
    _root_.eucDist (F.placeNext source T0_0) (F.placeNext source T0_2) =
      _root_.eucDist
        (UnitVectorGeometry.hingePoint (source T4_0)
          (F.roleAngle (.qToUpper : ConnectorRole)))
        (UnitVectorGeometry.hingePoint (source T4_0)
          (F.roleAngle (.qToLower : ConnectorRole))) := by
  rw [F.realizes_role source T4_0 T0_0
    (.qToUpper : ConnectorRole) rfl]
  rw [F.realizes_role source T4_0 T0_2
    (.qToLower : ConnectorRole) rfl]

end RoleHingeConnectorTransitionFacts

namespace RoleHingeTransitionFacts

/-- Forget the impossible all-source same-block field and retain the
connector-level role-hinge facts. -/
def toConnectorTransitionFacts
    (F : RoleHingeTransitionFacts) :
    RoleHingeConnectorTransitionFacts where
  placeNext := F.placeNext
  roleAngle := F.roleAngle
  realizes_role := F.realizes_role
  connector_unit_edges := F.connector_unit_edges

@[simp]
theorem toConnectorTransitionFacts_placeNext
    (F : RoleHingeTransitionFacts) :
    F.toConnectorTransitionFacts.placeNext = F.placeNext :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_roleAngle
    (F : RoleHingeTransitionFacts) :
    F.toConnectorTransitionFacts.roleAngle = F.roleAngle :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_realizes_role
    (F : RoleHingeTransitionFacts) :
    F.toConnectorTransitionFacts.realizes_role = F.realizes_role :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_connector_unit_edges
    (F : RoleHingeTransitionFacts) :
    F.toConnectorTransitionFacts.connector_unit_edges =
      F.connector_unit_edges :=
  rfl

end RoleHingeTransitionFacts

/-- Weaker same/opposite role-hinged transition facts.  This is the
search-facing connector-level package that can feed generated-chain
obligations without the old all-pairs same-block field. -/
structure SameOppositeRoleHingeConnectorTransitionFacts where
  same : RoleHingeConnectorTransitionFacts
  opposite : RoleHingeConnectorTransitionFacts

/-- Constructor spelling for the weaker same/opposite connector-level
transition package. -/
def sameOppositeRoleHingeConnectorTransitionFacts
    (same opposite : RoleHingeConnectorTransitionFacts) :
    SameOppositeRoleHingeConnectorTransitionFacts where
  same := same
  opposite := opposite

namespace SameOppositeRoleHingeConnectorTransitionFacts

/-- Forget the role-angle data to the Figure 2 connector-only transition
obligations used by generated chains. -/
def toFigure2TransitionObligations
    (F : SameOppositeRoleHingeConnectorTransitionFacts) :
    Figure2Certificate.SameOppositeTransitionObligations where
  samePlaceNext := F.same.placeNext
  oppositePlaceNext := F.opposite.placeNext
  same_connector_unit_edges := F.same.connector_unit_edges
  opposite_connector_unit_edges := F.opposite.connector_unit_edges

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (F : SameOppositeRoleHingeConnectorTransitionFacts) :
    F.toFigure2TransitionObligations.samePlaceNext =
      F.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (F : SameOppositeRoleHingeConnectorTransitionFacts) :
    F.toFigure2TransitionObligations.oppositePlaceNext =
      F.opposite.placeNext :=
  rfl

/-- Same-branch connector obligations obtained from the role facts. -/
theorem same_connector_unit_edges
    (F : SameOppositeRoleHingeConnectorTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges F.same.placeNext :=
  F.same.connector_unit_edges

/-- Opposite-branch connector obligations obtained from the role facts. -/
theorem opposite_connector_unit_edges
    (F : SameOppositeRoleHingeConnectorTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges F.opposite.placeNext :=
  F.opposite.connector_unit_edges

end SameOppositeRoleHingeConnectorTransitionFacts

/-- One generated-closure search certificate using connector-level
role-hinged transition facts.  Same-block control is supplied directly as a
generated-chain metric hypothesis, avoiding the old all-source transition
preservation field. -/
structure ConnectorGeneratedClosureSearchData (k : Nat) (hk : 0 < k) where
  transitions : SameOppositeRoleHingeConnectorTransitionFacts
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  metric :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace ConnectorGeneratedClosureSearchData

/-- Project connector-level generated closure data to the explicit
closed-placement certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (G : ConnectorGeneratedClosureSearchData k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase G.orientation G.closure G.metric

/-- The closed placement projected from connector-level generated closure
data. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (G : ConnectorGeneratedClosureSearchData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacement_of_generatedClosure
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase G.orientation G.closure G.metric

/-- Exact-block target bridge for connector-level role-hinged generated
closure data. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (G : ConnectorGeneratedClosureSearchData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation G.closure G.metric

end ConnectorGeneratedClosureSearchData

/-- Family of generated-closure search certificates using connector-level
role-hinged transition facts and full generated-chain metric hypotheses. -/
structure ConnectorGeneratedClosureSearchFamily where
  transitions : SameOppositeRoleHingeConnectorTransitionFacts
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  closure :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedClosureEquation
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)
  metric :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedMetricHypotheses
        transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (orientation k hk)

namespace ConnectorGeneratedClosureSearchFamily

/-- Forget connector-level role-hinge data to the generated-chain family
interface. -/
def toGeneratedChainFamily
    (F : ConnectorGeneratedClosureSearchFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

/-- Closure equations for the generated-chain family projected from a
connector-level search family. -/
def toGeneratedChainFamilyClosures
    (F : ConnectorGeneratedClosureSearchFamily) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      F.toGeneratedChainFamily :=
  fun k hk => F.closure k hk

/-- Full generated metric hypotheses projected from a connector-level search
family. -/
def toMetricHypotheses
    (F : ConnectorGeneratedClosureSearchFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      F.toGeneratedChainFamily where
  metric := fun k hk => F.metric k hk

/-- One member of a connector-level search family as bundled data. -/
def data
    (F : ConnectorGeneratedClosureSearchFamily)
    (k : Nat) (hk : 0 < k) :
    ConnectorGeneratedClosureSearchData k hk where
  transitions := F.transitions
  orientation := F.orientation k hk
  closure := F.closure k hk
  metric := F.metric k hk

/-- Closed placements for every positive length in a connector-level search
family. -/
def closedPlacementFamily
    (F : ConnectorGeneratedClosureSearchFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacementFamily_of_generatedClosure
    F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
    F.toMetricHypotheses

/-- Exact-multiple target theorem obtained from a connector-level role-hinge
search family. -/
theorem targetUpperConstructionFiveSixteen
    (F : ConnectorGeneratedClosureSearchFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family
      F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
      F.toMetricHypotheses

end ConnectorGeneratedClosureSearchFamily

/-- A source in which the `p`-port target pair is collapsed. -/
def collapsedPPortSource : LocalVertex -> R2 :=
  fun _ => (0, 0)

/-- A source in which the `p`-port target pair is separated by distance `2`,
while the common hinge center remains fixed. -/
def separatedPPortSource : LocalVertex -> R2
  | .tri 1 2 => (2, 0)
  | _ => (0, 0)

theorem eucDist_origin_two_zero :
    _root_.eucDist ((0, 0) : R2) ((2, 0) : R2) = 2 := by
  norm_num [_root_.eucDist]

/-- Same-block preservation restricted to the `p`-port target pair at a
single source. -/
def PreservesPPortPairAtSource
    (placeNext : (LocalVertex -> R2) -> LocalVertex -> R2)
    (source : LocalVertex -> R2) : Prop :=
  _root_.eucDist (placeNext source T1_1) (placeNext source T1_2) =
    _root_.eucDist (source T1_1) (source T1_2)

theorem preservesPPortPairAtSource_of_preservesSameBlockDistances
    {placeNext : (LocalVertex -> R2) -> LocalVertex -> R2}
    (hpreserve :
      HingedTransitionInterface.PreservesSameBlockDistances placeNext)
    (source : LocalVertex -> R2) :
    PreservesPPortPairAtSource placeNext source :=
  hpreserve source T1_1 T1_2

/-- The contradiction needs exactly these two same-block preservation
instances for the same `p`-port pair. -/
theorem false_of_pPortPair_preservation
    (F : RoleHingeConnectorTransitionFacts)
    (hcollapsed :
      PreservesPPortPairAtSource F.placeNext collapsedPPortSource)
    (hseparated :
      PreservesPPortPairAtSource F.placeNext separatedPPortSource) :
    False := by
  let produced : R2 :=
    UnitVectorGeometry.hingePoint ((0, 0) : R2)
      (F.roleAngle (.pToUpper : ConnectorRole))
  let produced' : R2 :=
    UnitVectorGeometry.hingePoint ((0, 0) : R2)
      (F.roleAngle (.pToLower : ConnectorRole))
  have hcollapsed_produced :
      _root_.eucDist
          (F.placeNext collapsedPPortSource T1_1)
          (F.placeNext collapsedPPortSource T1_2) =
        _root_.eucDist produced produced' := by
    simpa [produced, produced', collapsedPPortSource, T, T2_2] using
      F.pPort_pair_distance_eq_hinge_distance collapsedPPortSource
  have hseparated_produced :
      _root_.eucDist
          (F.placeNext separatedPPortSource T1_1)
          (F.placeNext separatedPPortSource T1_2) =
        _root_.eucDist produced produced' := by
    simpa [produced, produced', separatedPPortSource, T, T2_2] using
      F.pPort_pair_distance_eq_hinge_distance separatedPPortSource
  have hzero : _root_.eucDist produced produced' = 0 := by
    rw [← hcollapsed_produced]
    simpa [PreservesPPortPairAtSource, collapsedPPortSource] using hcollapsed
  have htwo : _root_.eucDist produced produced' = 2 := by
    rw [← hseparated_produced]
    simpa [PreservesPPortPairAtSource, separatedPPortSource, T, T1_1, T1_2,
      eucDist_origin_two_zero] using hseparated
  linarith

/-- Any role-realizing transition with the old all-source same-block
preservation field is inconsistent. -/
theorem false_of_preservesSameBlockDistances_and_realizes_role
    (F : RoleHingeConnectorTransitionFacts)
    (hpreserve :
      HingedTransitionInterface.PreservesSameBlockDistances F.placeNext) :
    False :=
  false_of_pPortPair_preservation F
    (preservesPPortPairAtSource_of_preservesSameBlockDistances
      hpreserve collapsedPPortSource)
    (preservesPPortPairAtSource_of_preservesSameBlockDistances
      hpreserve separatedPPortSource)

/-- No role-hinged transition can satisfy the current strong arbitrary-source
same-block preservation interface.

Both `T1_1` and `T1_2` are required by the role table to be hinge endpoints
from the same source vertex `T2_2`.  The produced distance between them is
therefore fixed by the source's `T2_2` value and the two role angles.  But the
same-block preservation field quantifies over arbitrary source placements, so
the same produced distance would have to equal both `0` and `2`. -/
theorem false_of_roleHingeTransitionFacts
    (F : RoleHingeTransitionFacts) :
    False := by
  exact
    false_of_preservesSameBlockDistances_and_realizes_role
      F.toConnectorTransitionFacts F.preserves_same_block_distances

theorem no_roleHingeTransitionFacts :
    RoleHingeTransitionFacts -> False := by
  intro F
  exact false_of_roleHingeTransitionFacts F

theorem not_nonempty_roleHingeTransitionFacts :
    Not (Nonempty RoleHingeTransitionFacts) := by
  rintro ⟨F⟩
  exact false_of_roleHingeTransitionFacts F

instance roleHingeTransitionFacts_isEmpty :
    IsEmpty RoleHingeTransitionFacts :=
  ⟨false_of_roleHingeTransitionFacts⟩

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

/-- Forget the impossible all-source same-block fields and retain the
connector-level same/opposite role-hinge facts. -/
def toConnectorTransitionFacts
    (F : SameOppositeRoleHingeTransitionFacts) :
    SameOppositeRoleHingeConnectorTransitionFacts where
  same := F.same.toConnectorTransitionFacts
  opposite := F.opposite.toConnectorTransitionFacts

@[simp]
theorem toConnectorTransitionFacts_same
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toConnectorTransitionFacts.same =
      F.same.toConnectorTransitionFacts :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_opposite
    (F : SameOppositeRoleHingeTransitionFacts) :
    F.toConnectorTransitionFacts.opposite =
      F.opposite.toConnectorTransitionFacts :=
  rfl

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

/-- The same/opposite strong role-hinge package is already inconsistent in
its same branch. -/
theorem false_of_sameOppositeRoleHingeTransitionFacts
    (F : SameOppositeRoleHingeTransitionFacts) :
    False :=
  false_of_roleHingeTransitionFacts F.same

theorem no_sameOppositeRoleHingeTransitionFacts :
    SameOppositeRoleHingeTransitionFacts -> False := by
  intro F
  exact false_of_sameOppositeRoleHingeTransitionFacts F

theorem not_nonempty_sameOppositeRoleHingeTransitionFacts :
    Not (Nonempty SameOppositeRoleHingeTransitionFacts) := by
  rintro ⟨F⟩
  exact false_of_sameOppositeRoleHingeTransitionFacts F

instance sameOppositeRoleHingeTransitionFacts_isEmpty :
    IsEmpty SameOppositeRoleHingeTransitionFacts :=
  ⟨false_of_sameOppositeRoleHingeTransitionFacts⟩

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
