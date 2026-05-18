import ErdosProblems1066.PachToth.RoleHingeExactLocalFinite
import ErdosProblems1066.PachToth.RoleHingeSameBlockAlgebra
import ErdosProblems1066.PachToth.RoleHingeAngleCertificates
import ErdosProblems1066.PachToth.RoleHingeTransitionSearch

set_option autoImplicit false

/-!
# Flexible exact-local role-hinge transitions

The four-target concrete role-hinge route cannot discharge the old
`not IsRoleAnglePortPair` remainder: `RoleHingeExactLocalFinite` records the
specific obstruction.  This file replaces that route with an honest flexible
interface.

Connector-unit role data is kept separate from the exact-local same-block
invariant.  A construction that can provide both may still feed the generated
closed-chain metric interface, but the exact-local preservation field is now
explicit data rather than a hidden non-port-pair theorem.
-/

noncomputable section

namespace ErdosProblems1066
namespace PachToth
namespace FlexibleExactLocalTransition

open FiniteGraph

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

/-- Role-realization data for one transition branch.

This is the connector-unit part only: it records the map, its role-angle
assignment, and the table equation saying each connector target is the
corresponding unit hinge point.  It deliberately carries no same-block metric
claim. -/
structure ConnectorUnitRoleData where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)

namespace ConnectorUnitRoleData

/-- Connector-unit role data projects to the existing connector-level
role-hinge facts. -/
def toConnectorTransitionFacts
    (C : ConnectorUnitRoleData) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  RoleHingeTransitionSearch.roleHingeConnectorTransitionFacts
    C.placeNext C.roleAngle C.realizes_role

@[simp]
theorem toConnectorTransitionFacts_placeNext
    (C : ConnectorUnitRoleData) :
    C.toConnectorTransitionFacts.placeNext = C.placeNext :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_roleAngle
    (C : ConnectorUnitRoleData) :
    C.toConnectorTransitionFacts.roleAngle = C.roleAngle :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_realizes_role
    (C : ConnectorUnitRoleData) :
    C.toConnectorTransitionFacts.realizes_role = C.realizes_role :=
  rfl

/-- The connector-unit obligation is derived from the role table and the hinge
geometry, without using same-block preservation. -/
theorem connector_unit_edges
    (C : ConnectorUnitRoleData) :
    HingedTransitionInterface.ConnectorUnitEdges C.placeNext := by
  exact
    RoleHingeTransitionSearch.connector_unit_edges_of_realizes
      C.placeNext C.roleAngle C.realizes_role

end ConnectorUnitRoleData

/-- Exact-local same-block data for one branch.

This is the flexible replacement for the blocked non-port-pair remainder:
the construction must provide preservation of the exact local squared-distance
table on exact-local sources directly. -/
structure ExactLocalSameBlockData
    (C : ConnectorUnitRoleData) : Prop where
  preserves_exact_local_sq_distances :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances C.placeNext

namespace ExactLocalSameBlockData

/-- Pointwise exact-local preservation for a source block. -/
theorem matchesExactLocalSqDistances
    {C : ConnectorUnitRoleData}
    (E : ExactLocalSameBlockData C)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source) :
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
      (C.placeNext source) :=
  E.preserves_exact_local_sq_distances source hsource

/-- Row-level form of the exact-local preservation field. -/
theorem sqDist
    {C : ConnectorUnitRoleData}
    (E : ExactLocalSameBlockData C)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source)
    (u v : LocalVertex) :
    RoleHingeSameBlockAlgebra.sqDist
        (C.placeNext source u) (C.placeNext source v) =
      ((ExactLocalGeometry.localNorm4 u v : Int) : Real) / 4 :=
  E.matchesExactLocalSqDistances hsource u v

/-- Exact-local preservation also gives the Euclidean same-block table on the
produced exact-local block. -/
theorem matchesExactLocalDistances
    {C : ConnectorUnitRoleData}
    (E : ExactLocalSameBlockData C)
    {source : LocalVertex -> R2}
    (hsource :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances source) :
    RoleHingeSameBlockAlgebra.MatchesExactLocalDistances
      (C.placeNext source) :=
  RoleHingeSameBlockAlgebra.matchesExactLocalDistances_of_sqDistances
    (E.matchesExactLocalSqDistances hsource)

end ExactLocalSameBlockData

/-- One flexible role-hinge branch: connector-unit role data plus direct
exact-local same-block preservation. -/
structure Branch where
  connector : ConnectorUnitRoleData
  exactLocal : ExactLocalSameBlockData connector

namespace Branch

def placeNext
    (B : Branch) :
    (LocalVertex -> R2) -> LocalVertex -> R2 :=
  B.connector.placeNext

def roleAngle
    (B : Branch) :
    ConnectorRole -> Real :=
  B.connector.roleAngle

@[simp]
theorem placeNext_eq
    (B : Branch) :
    B.placeNext = B.connector.placeNext :=
  rfl

@[simp]
theorem roleAngle_eq
    (B : Branch) :
    B.roleAngle = B.connector.roleAngle :=
  rfl

/-- Forget the exact-local field and retain connector-level role-hinge facts. -/
def toConnectorTransitionFacts
    (B : Branch) :
    RoleHingeTransitionSearch.RoleHingeConnectorTransitionFacts :=
  B.connector.toConnectorTransitionFacts

@[simp]
theorem toConnectorTransitionFacts_placeNext
    (B : Branch) :
    B.toConnectorTransitionFacts.placeNext = B.placeNext :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_roleAngle
    (B : Branch) :
    B.toConnectorTransitionFacts.roleAngle = B.roleAngle :=
  rfl

/-- Connector-unit edges for the branch, derived only from role realization. -/
theorem connector_unit_edges
    (B : Branch) :
    HingedTransitionInterface.ConnectorUnitEdges B.placeNext :=
  B.connector.connector_unit_edges

/-- Exact-local squared-distance preservation for the branch. -/
theorem preserves_exact_local_sq_distances
    (B : Branch) :
    RoleHingeSameBlockAlgebra.PreservesExactLocalSqDistances B.placeNext :=
  B.exactLocal.preserves_exact_local_sq_distances

end Branch

/-- Same/opposite flexible role-hinge transition data. -/
structure SameOpposite where
  same : Branch
  opposite : Branch

namespace SameOpposite

/-- Forget exact-local data to the connector-level role-hinge transition
package. -/
def toConnectorTransitionFacts
    (F : SameOpposite) :
    RoleHingeTransitionSearch.SameOppositeRoleHingeConnectorTransitionFacts where
  same := F.same.toConnectorTransitionFacts
  opposite := F.opposite.toConnectorTransitionFacts

@[simp]
theorem toConnectorTransitionFacts_same
    (F : SameOpposite) :
    F.toConnectorTransitionFacts.same = F.same.toConnectorTransitionFacts :=
  rfl

@[simp]
theorem toConnectorTransitionFacts_opposite
    (F : SameOpposite) :
    F.toConnectorTransitionFacts.opposite =
      F.opposite.toConnectorTransitionFacts :=
  rfl

/-- The generated-chain connector-only transition obligations associated to
the flexible same/opposite package. -/
def toFigure2TransitionObligations
    (F : SameOpposite) :
    Figure2Certificate.SameOppositeTransitionObligations :=
  F.toConnectorTransitionFacts.toFigure2TransitionObligations

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (F : SameOpposite) :
    F.toFigure2TransitionObligations.samePlaceNext =
      F.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (F : SameOpposite) :
    F.toFigure2TransitionObligations.oppositePlaceNext =
      F.opposite.placeNext :=
  rfl

/-- Same-branch connector-unit edges are obtained from role data only. -/
theorem same_connector_unit_edges
    (F : SameOpposite) :
    HingedTransitionInterface.ConnectorUnitEdges F.same.placeNext :=
  F.same.connector_unit_edges

/-- Opposite-branch connector-unit edges are obtained from role data only. -/
theorem opposite_connector_unit_edges
    (F : SameOpposite) :
    HingedTransitionInterface.ConnectorUnitEdges F.opposite.placeNext :=
  F.opposite.connector_unit_edges

/-- The flexible exact-local fields imply the selected generated-transition
exact-local invariant. -/
theorem generatedTransitionsPreserveExactLocalSqDistances
    (F : SameOpposite) :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      F.toFigure2TransitionObligations := by
  intro orientation source hsource
  cases orientation with
  | same =>
      exact F.same.preserves_exact_local_sq_distances source hsource
  | opposite =>
      exact F.opposite.preserves_exact_local_sq_distances source hsource

/-- Exact-local squared-distance tables propagate along every generated
orbit from the exact base. -/
theorem generatedOrbit_exactBase_matchesExactLocalSqDistances
    (F : SameOpposite)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    forall i : Fin k,
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
        (GeneratedClosedChain.generatedPoint F.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase orientation i) :=
  RoleHingeSameBlockAlgebra.generatedOrbit_exactBase_matchesExactLocalSqDistances
    F.toFigure2TransitionObligations hk orientation
    F.generatedTransitionsPreserveExactLocalSqDistances

/-- The flexible exact-local fields give the generated same-block isometry
needed by closed-chain metric hypotheses. -/
theorem generatedSameBlockIsometry
    (F : SameOpposite)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      F.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation := by
  exact
    RoleHingeSameBlockAlgebra.generatedSameBlockIsometry_of_exactLocalSqDistances
      F.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
      (by
        simpa [BaseTransitionRealization.exactBase] using
          RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances)
      F.generatedTransitionsPreserveExactLocalSqDistances

/-- Package global separation with the flexible exact-local transition fields
into full generated metric hypotheses. -/
def generatedMetricHypotheses
    (F : SameOpposite)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        F.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      F.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation where
  separated := separated
  same_block_isometry := F.generatedSameBlockIsometry hk orientation

end SameOpposite

/-- One generated-closure certificate using flexible exact-local role-hinge
transitions.

The remaining data are exactly the generated closure equation and global
separation; same-block preservation is supplied by the branch-local
exact-local fields instead of by an all-source non-port-pair theorem. -/
structure GeneratedClosureData (k : Nat) (hk : 0 < k) where
  transitions : SameOpposite
  orientation : Fin k -> OrientationData.BlockOrientation
  closure :
    PeriodInterface.GeneratedClosureEquation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation
  separated :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation

namespace GeneratedClosureData

/-- Full metric hypotheses obtained from flexible exact-local transition data. -/
def metricHypotheses
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureData k hk) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation :=
  G.transitions.generatedMetricHypotheses hk G.orientation G.separated

@[simp]
theorem metricHypotheses_separated
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureData k hk) :
    G.metricHypotheses.separated = G.separated :=
  rfl

/-- Project flexible generated closure data to an explicit closed-placement
certificate. -/
def toExplicitTransitionClosedPlacementCertificate
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureData k hk) :
    ClosedPlacementInterface.ExplicitTransitionClosedPlacementCertificate
      k hk :=
  ClosedPlacementClosure.explicitTransitionClosedPlacementCertificate_of_generatedClosure
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase G.orientation
    G.closure G.metricHypotheses

/-- The closed placement projected from flexible generated closure data. -/
def toClosedPlacement
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureData k hk) :
    DeformedPlacement.ClosedPlacement k hk :=
  ClosedPlacementClosure.closedPlacement_of_generatedClosure
    G.transitions.toFigure2TransitionObligations hk
    BaseTransitionRealization.exactBase G.orientation
    G.closure G.metricHypotheses

/-- Exact-block target bridge for one flexible generated closure certificate. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    {k : Nat} {hk : 0 < k}
    (G : GeneratedClosureData k hk) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure
      G.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase G.orientation
      G.closure G.metricHypotheses

end GeneratedClosureData

/-- A family of flexible generated-closure certificates. -/
structure GeneratedClosureFamily where
  transitions : SameOpposite
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

namespace GeneratedClosureFamily

/-- Forget flexible role-hinge data to the generated-chain family interface. -/
def toGeneratedChainFamily
    (F : GeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _ _ => F.transitions.toFigure2TransitionObligations
  base := fun _ _ => BaseTransitionRealization.exactBase
  orientation := F.orientation

/-- Closure equations for the generated-chain family projected from a
flexible exact-local family. -/
def toGeneratedChainFamilyClosures
    (F : GeneratedClosureFamily) :
    ClosedPlacementClosure.GeneratedChainFamilyClosures
      F.toGeneratedChainFamily :=
  fun k hk => F.closure k hk

/-- Full generated metric hypotheses projected from a flexible exact-local
family. -/
def toMetricHypotheses
    (F : GeneratedClosureFamily) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses
      F.toGeneratedChainFamily where
  metric := fun k hk =>
    F.transitions.generatedMetricHypotheses
      hk (F.orientation k hk) (F.separated k hk)

/-- One member of a flexible generated-closure family. -/
def data
    (F : GeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    GeneratedClosureData k hk where
  transitions := F.transitions
  orientation := F.orientation k hk
  closure := F.closure k hk
  separated := F.separated k hk

@[simp]
theorem data_transitions
    (F : GeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    (F.data k hk).transitions = F.transitions :=
  rfl

@[simp]
theorem data_orientation
    (F : GeneratedClosureFamily)
    (k : Nat) (hk : 0 < k) :
    (F.data k hk).orientation = F.orientation k hk :=
  rfl

/-- Closed placements for every positive length in a flexible family. -/
def closedPlacementFamily
    (F : GeneratedClosureFamily) :
    forall (k : Nat) (hk : 0 < k),
      DeformedPlacement.ClosedPlacement k hk :=
  fun k hk => (F.data k hk).toClosedPlacement

/-- Exact-multiple target theorem obtained from a flexible exact-local
role-hinge search family. -/
theorem targetUpperConstructionFiveSixteen
    (F : GeneratedClosureFamily) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family
      F.toGeneratedChainFamily F.toGeneratedChainFamilyClosures
      F.toMetricHypotheses

end GeneratedClosureFamily

end FlexibleExactLocalTransition
end PachToth
end ErdosProblems1066

end
