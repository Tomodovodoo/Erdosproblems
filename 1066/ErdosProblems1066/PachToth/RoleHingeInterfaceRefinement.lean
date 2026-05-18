import ErdosProblems1066.PachToth.ClosedPlacementClosure
import ErdosProblems1066.PachToth.RoleHingeConcreteSearch
import ErdosProblems1066.PachToth.RoleHingeConnectorAlgebra
import ErdosProblems1066.PachToth.RoleHingeSameBlockAlgebra

set_option autoImplicit false

/-!
# Role-hinge interface refinement

The current role-hinge transition interface asks a next-block map to preserve
all same-block distances for every possible source placement.  That is stronger
than the generated-chain reduction needs: along a closed-chain construction it
is enough to know that each block on the generated orbit has the exact local
same-block metric.

This file records that weaker orbit-level interface and bridges it to the
existing generated-chain and closed-placement target wrappers.  It also names
the concrete obstruction already exposed by `RoleHingeConcreteSearch`: the
four-target role-hinge override cannot satisfy the arbitrary-source
preservation field.
-/

namespace ErdosProblems1066
namespace PachToth
namespace RoleHingeInterfaceRefinement

open FiniteGraph
open GeneratedSeparationInterface

noncomputable section

abbrev R2 := Prod Real Real
abbrev ConnectorRole := Figure2EdgeTable.NextConnectorRole

/-- Orbit-level same-block invariant: every generated block realizes the exact
local squared-distance table. -/
def GeneratedOrbitMatchesExactLocalSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) : Prop :=
  forall i : Fin k,
    RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances
      (GeneratedClosedChain.generatedPoint O hk base orientation i)

/-- The orbit-level squared-distance invariant supplies the same-block
isometry required by generated closed chains. -/
theorem generatedSameBlockIsometry_of_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances O hk base orientation) :
    GeneratedSeparationInterface.GeneratedSameBlockIsometry
      O hk base orientation := by
  intro i u v
  have hdist :=
    RoleHingeSameBlockAlgebra.matchesExactLocalDistances_of_sqDistances
      (horbit i) u v
  calc
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation i v) =
      _root_.eucDist
        (ExactLocalGeometry.localPoint u)
        (ExactLocalGeometry.localPoint v) := hdist
    _ =
      _root_.eucDist
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 u))
        (OneBlockSoundness.oneBlockCertificate.config.pts
          (BlockPartition.localVertexEquivFin16 v)) := by
        exact
          RoleHingeSameBlockAlgebra.exactLocal_generatedBaseSameBlockIsometry
            u v

/-- Full metric hypotheses obtained from global separation plus the weaker
orbit-level same-block invariant. -/
def generatedMetricHypotheses_of_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances O hk base orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated := separated
  same_block_isometry :=
    generatedSameBlockIsometry_of_orbitSqDistances
      O hk base orientation horbit

/-- Exact-block target bridge using algebraic closure and the orbit-level
same-block invariant. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances O hk base orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedClosure
      O hk base orientation closure
      (generatedMetricHypotheses_of_orbitSqDistances
        O hk base orientation separated horbit)

/-- Closed-placement existence bridge using algebraic closure and the
orbit-level same-block invariant. -/
theorem exists_closedPlacement_of_orbitSqDistances
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation O hk base orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        O hk base orientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances O hk base orientation) :
    exists P : DeformedPlacement.ClosedPlacement k hk,
      P.point = GeneratedClosedChain.generatedPoint O hk base orientation := by
  exact
    ClosedPlacementClosure.exists_closedPlacement_of_generatedClosure
      O hk base orientation closure
      (generatedMetricHypotheses_of_orbitSqDistances
        O hk base orientation separated horbit)

/-- Family-level orbit metric hypotheses. -/
structure GeneratedChainFamilyOrbitSqDistanceHypotheses
    (F : GeneratedSeparationInterface.GeneratedChainFamily) where
  separated :
    forall (k : Nat) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)
  orbit_sq_distances :
    forall (k : Nat) (hk : 0 < k),
      GeneratedOrbitMatchesExactLocalSqDistances
        (F.O k hk) hk (F.base k hk) (F.orientation k hk)

namespace GeneratedChainFamilyOrbitSqDistanceHypotheses

/-- Convert family-level orbit metric hypotheses to the existing full metric
hypotheses interface. -/
def toMetricHypotheses
    {F : GeneratedSeparationInterface.GeneratedChainFamily}
    (H : GeneratedChainFamilyOrbitSqDistanceHypotheses F) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F where
  metric := fun k hk =>
    generatedMetricHypotheses_of_orbitSqDistances
      (F.O k hk) hk (F.base k hk) (F.orientation k hk)
      (H.separated k hk) (H.orbit_sq_distances k hk)

end GeneratedChainFamilyOrbitSqDistanceHypotheses

/-- Generated closure and orbit-level same-block hypotheses imply the
finite-family Pach--Toth target. -/
theorem targetUpperConstructionFiveSixteen_of_generatedClosure_family_orbitSqDistances
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (closure : ClosedPlacementClosure.GeneratedChainFamilyClosures F)
    (H : GeneratedChainFamilyOrbitSqDistanceHypotheses F) :
    targetUpperConstructionFiveSixteen := by
  exact
    ClosedPlacementClosure.targetUpperConstructionFiveSixteen_of_generatedClosure_family
      F closure H.toMetricHypotheses

/-- Eventual-family orbit metric hypotheses. -/
structure EventualGeneratedChainFamilyOrbitSqDistanceHypotheses
    {K0 : Nat}
    (F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0) where
  separated :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        (F.O k hK hk) hk (F.base k hK hk) (F.orientation k hK hk)
  orbit_sq_distances :
    forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
      GeneratedOrbitMatchesExactLocalSqDistances
        (F.O k hK hk) hk (F.base k hK hk) (F.orientation k hK hk)

namespace EventualGeneratedChainFamilyOrbitSqDistanceHypotheses

/-- Convert eventual-family orbit metric hypotheses to the existing full
metric hypotheses interface. -/
def toMetricHypotheses
    {K0 : Nat}
    {F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0}
    (H : EventualGeneratedChainFamilyOrbitSqDistanceHypotheses F) :
    GeneratedSeparationInterface.EventualGeneratedChainFamily.MetricHypotheses
      F where
  metric := fun k hK hk =>
    generatedMetricHypotheses_of_orbitSqDistances
      (F.O k hK hk) hk (F.base k hK hk) (F.orientation k hK hk)
      (H.separated k hK hk) (H.orbit_sq_distances k hK hk)

end EventualGeneratedChainFamilyOrbitSqDistanceHypotheses

/-- Eventual generated closure data and small cases imply the arbitrary target
when same-block control is supplied only on the generated orbit. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_orbitSqDistances
    {K0 : Nat}
    (F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0)
    (period : F.Periods)
    (H : EventualGeneratedChainFamilyOrbitSqDistanceHypotheses F)
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F period H.toMetricHypotheses Hsmall

/-- Raw facts for one role-hinged transition with no arbitrary-source
same-block preservation field. -/
structure RoleHingeOrbitTransitionFacts where
  placeNext : (LocalVertex -> R2) -> LocalVertex -> R2
  roleAngle : ConnectorRole -> Real
  realizes_role :
    forall (source : LocalVertex -> R2) (u v : LocalVertex)
      (role : ConnectorRole),
      Figure2EdgeTable.nextConnectorRole u v = some role ->
        placeNext source v =
          UnitVectorGeometry.hingePoint (source u) (roleAngle role)

namespace RoleHingeOrbitTransitionFacts

/-- The role table and hinge lemma still give all connector-unit obligations;
the strong same-block field is not used. -/
theorem connector_unit_edges
    (T : RoleHingeOrbitTransitionFacts) :
    HingedTransitionInterface.ConnectorUnitEdges T.placeNext := by
  intro source u v hconn
  exact Exists.elim (Figure2EdgeTable.nextConnector_has_role u v hconn)
    (fun role hrole =>
      RoleHingeConnectorAlgebra.role_port_unit_of_realizes
        T.placeNext T.roleAngle T.realizes_role source u v role hrole)

end RoleHingeOrbitTransitionFacts

/-- Same/opposite role-hinged transitions at the refined, connector-only
level. -/
structure SameOppositeRoleHingeOrbitTransitionFacts where
  same : RoleHingeOrbitTransitionFacts
  opposite : RoleHingeOrbitTransitionFacts

namespace SameOppositeRoleHingeOrbitTransitionFacts

/-- Forget the role-hinge data to the Figure 2 connector transition
obligations used by generated chains. -/
def toFigure2TransitionObligations
    (T : SameOppositeRoleHingeOrbitTransitionFacts) :
    Figure2Certificate.SameOppositeTransitionObligations where
  samePlaceNext := T.same.placeNext
  oppositePlaceNext := T.opposite.placeNext
  same_connector_unit_edges := T.same.connector_unit_edges
  opposite_connector_unit_edges := T.opposite.connector_unit_edges

@[simp]
theorem toFigure2TransitionObligations_samePlaceNext
    (T : SameOppositeRoleHingeOrbitTransitionFacts) :
    T.toFigure2TransitionObligations.samePlaceNext = T.same.placeNext :=
  rfl

@[simp]
theorem toFigure2TransitionObligations_oppositePlaceNext
    (T : SameOppositeRoleHingeOrbitTransitionFacts) :
    T.toFigure2TransitionObligations.oppositePlaceNext =
      T.opposite.placeNext :=
  rfl

/-- The stronger old search-facing transition facts project to the refined
connector-only role-hinge interface. -/
def ofStrong
    (F : RoleHingeTransitionSearch.SameOppositeRoleHingeTransitionFacts) :
    SameOppositeRoleHingeOrbitTransitionFacts where
  same :=
    { placeNext := F.same.placeNext
      roleAngle := F.same.roleAngle
      realizes_role := F.same.realizes_role }
  opposite :=
    { placeNext := F.opposite.placeNext
      roleAngle := F.opposite.roleAngle
      realizes_role := F.opposite.realizes_role }

end SameOppositeRoleHingeOrbitTransitionFacts

/-- If a refined same/opposite package preserves exact-local squared
distances under selected transitions, then every block on a generated orbit
has the exact local same-block metric. -/
theorem generatedOrbitSqDistances_of_transitionExactLocalSqDistances
    (T : SameOppositeRoleHingeOrbitTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (hbase :
      RoleHingeSameBlockAlgebra.MatchesExactLocalSqDistances base)
    (htransition :
      RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    GeneratedOrbitMatchesExactLocalSqDistances
      T.toFigure2TransitionObligations hk base orientation := by
  intro i
  simpa [GeneratedOrbitMatchesExactLocalSqDistances,
    GeneratedClosedChain.generatedPoint] using
    RoleHingeSameBlockAlgebra.generatedBlock_matchesExactLocalSqDistances
      T.toFigure2TransitionObligations hk base orientation hbase htransition
      i.val

/-- Exact-base specialization of the previous orbit invariant. -/
theorem generatedOrbitSqDistances_exactBase_of_transitionExactLocalSqDistances
    (T : SameOppositeRoleHingeOrbitTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (htransition :
      RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    GeneratedOrbitMatchesExactLocalSqDistances
      T.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase orientation := by
  simpa [BaseTransitionRealization.exactBase] using
    generatedOrbitSqDistances_of_transitionExactLocalSqDistances
      T hk ExactLocalGeometry.localPoint orientation
      RoleHingeSameBlockAlgebra.exactLocal_matchesExactLocalSqDistances
      htransition

/-- Exact-block target bridge for refined role-hinge transitions whose
same-block metric is certified only by exact-local orbit preservation. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_roleHingeOrbitSqDistances
    (T : SameOppositeRoleHingeOrbitTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (horbit :
      GeneratedOrbitMatchesExactLocalSqDistances
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_orbitSqDistances
      T.toFigure2TransitionObligations hk BaseTransitionRealization.exactBase
      orientation closure separated horbit

/-- Exact-block target bridge when the orbit invariant is obtained by
propagating exact-local squared distances. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_roleHingeTransitionExactLocalSqDistances
    (T : SameOppositeRoleHingeOrbitTransitionFacts)
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (closure :
      PeriodInterface.GeneratedClosureEquation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (separated :
      GeneratedSeparationInterface.GeneratedGlobalSeparation
        T.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase orientation)
    (htransition :
      RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
        T.toFigure2TransitionObligations) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_roleHingeOrbitSqDistances
      T hk orientation closure separated
      (generatedOrbitSqDistances_exactBase_of_transitionExactLocalSqDistances
        T hk orientation htransition)

/-- Named obstruction: the concrete fixed-angle role-hinge override cannot
satisfy the old arbitrary-source same-block preservation interface. -/
theorem current_forallSource_preservation_obstructs_concreteRoleHingePlace
    (angle : ConnectorRole -> Real) :
    Not
      (HingedTransitionInterface.PreservesSameBlockDistances
        (RoleHingeConcreteSearch.concreteRoleHingePlace angle)) :=
  RoleHingeConcreteSearch.not_preservesSameBlockDistances_concreteRoleHingePlace
    angle

/-- Consequently, the concrete same/opposite remaining-equation package built
for the old strong interface is inconsistent. -/
theorem no_concreteSameOppositeRemainingEquations_for_strong_interface :
    Not RoleHingeConcreteSearch.ConcreteSameOppositeRemainingEquations :=
  RoleHingeConcreteSearch.no_concreteSameOppositeRemainingEquations

end

end RoleHingeInterfaceRefinement
end PachToth
end ErdosProblems1066
