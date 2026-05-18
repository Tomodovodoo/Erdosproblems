import ErdosProblems1066.PachToth.CrossBlockDistanceSqReduction
import ErdosProblems1066.PachToth.RoleHingeConnectorAlgebra

set_option autoImplicit false

/-!
# Non-rigid connector separation facts

This module isolates the separation facts for successor connector pairs in a
generated non-rigid chain.  Same-block pairs are already handled by the
checked one-block separation/isometry route, and the remaining cross-block
pairs are intended for finite lower tables.  The connector pairs themselves
come from the transition connector-unit fields, so finite metric tables only
need to cover non-connector cross-block pairs.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonRigidConnectorSeparationFacts

open Arithmetic
open CrossBlockDistanceSqReduction
open CrossBlockLowerBoundsInterface
open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

/-- A directed successor connector pair from block `i` to block `j`. -/
def SuccessorConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Prop :=
  j = cyclicSucc hk i ∧ CrossBlock.NextConnector u v

/-- A connector pair, allowing either order of the two endpoints. -/
def CyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Prop :=
  SuccessorConnectorPair hk i u j v ∨
    SuccessorConnectorPair hk j v i u

/-- Finite-index spelling of `CyclicConnectorPair`. -/
def IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  CyclicConnectorPair hk i (localVertexOfIndex u) j (localVertexOfIndex v)

/-- A role-hinge transition separates every directed connector edge. -/
theorem roleHinge_connector_separated
    (T : BaseTransitionRealization.RoleHingeTransition)
    (source : LocalVertex -> R2)
    (u v : LocalVertex)
    (hconn : CrossBlock.NextConnector u v) :
    1 <= _root_.eucDist (source u) (T.placeNext source v) := by
  rw [RoleHingeConnectorAlgebra.connector_unit_edges T source u v hconn]

/-- A closed generated chain has distance exactly one on every cyclic
successor connector pair. -/
theorem successorConnectorPair_distance_eq_one
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : SuccessorConnectorPair hk i u j v) :
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) = 1 := by
  rcases hpair with ⟨hj, hconn⟩
  subst j
  rw [GeneratedClosedChain.generatedPoint_successor_compatible
    O hk base orientation period i v]
  exact
    Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
      O (orientation i) (GeneratedClosedChain.generatedPoint O hk base orientation i)
      u v hconn

/-- A closed generated chain has distance exactly one on every connector pair,
in either endpoint order. -/
theorem cyclicConnectorPair_distance_eq_one
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : CyclicConnectorPair hk i u j v) :
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) = 1 := by
  rcases hpair with hforward | hreverse
  · exact
      successorConnectorPair_distance_eq_one
        O hk base orientation period i u j v hforward
  · rw [_root_.eucDist_comm]
    exact
      successorConnectorPair_distance_eq_one
        O hk base orientation period j v i u hreverse

/-- Connector pairs supply their own separation lower bound. -/
theorem cyclicConnectorPair_separated
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : CyclicConnectorPair hk i u j v) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  rw [cyclicConnectorPair_distance_eq_one
    O hk base orientation period i u j v hpair]

/-- Lower-bound table predicate for cross-block pairs that are not cyclic
successor connector pairs. -/
def GeneratedNonConnectorCrossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j ->
      Not (CyclicConnectorPair hk i u j v) ->
        lower i u j v <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- The same non-connector table must be at least one. -/
def GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j -> Not (CyclicConnectorPair hk i u j v) ->
      1 <= lower i u j v

/-- Same-block separation, connector-unit facts, and finite non-connector
cross-block lower bounds imply global generated separation. -/
theorem generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower)
    (hlower :
      GeneratedNonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  by_cases hij : i = j
  · subst j
    have huv : Ne u v := by
      intro huv
      exact hne (Prod.ext rfl huv)
    exact
      GeneratedSeparationFarApart.generatedSameBlockSeparation_of_sameBlockIsometry
        O hk base orientation same_block_isometry i u v huv
  · by_cases hconn : CyclicConnectorPair hk i u j v
    · exact cyclicConnectorPair_separated
        O hk base orientation period i u j v hconn
    · exact le_trans (hge_one i u j v hij hconn)
        (hlower i u j v hij hconn)

/-- Reduced same-block hypotheses plus connector and non-connector lower
bounds imply global generated separation. -/
theorem generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower)
    (hlower :
      GeneratedNonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
      O hk base orientation period
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      lower hge_one hlower

/-- A finite-index square-distance table for all remaining cross-block pairs
after removing successor connector pairs. -/
structure IndexedNonConnectorCrossBlockSqDistanceTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  sqDist_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (IndexedCyclicConnectorPair hk i u j v) ->
            1 <= indexedGeneratedSqDist F hk i u j v

namespace IndexedNonConnectorCrossBlockSqDistanceTable

/-- The generated period equation stored in the period-search family. -/
def periodEquation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (_T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    PeriodInterface.GeneratedPeriodEquation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) := by
  simpa [ExactFamilyClosure.finiteOrientationWord] using
    (F.period k hk).toGeneratedPeriodEquation

/-- The uniform lower table `1` is enough for the non-connector pairs covered
by the finite square-distance table. -/
theorem lower_bound_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedNonConnectorCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (fun _i _u _j _v => 1) := by
  intro i u j v hij hnot
  have hnot_index :
      Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
        j (localVertexIndex v)) := by
    intro hidx
    exact hnot (by
      simpa [IndexedCyclicConnectorPair] using hidx)
  simpa [indexedGeneratedPoint] using
    (one_le_indexedGenerated_eucDist_iff_sqDist F hk
      i (localVertexIndex u) j (localVertexIndex v)).2
      (T.sqDist_ge_one i (localVertexIndex u)
        j (localVertexIndex v) hij hnot_index)

/-- Finite non-connector square-distance tables, together with the connector
unit facts and reduced same-block facts, give generated global separation. -/
theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) := by
  exact
    generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds_reduced
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      T.periodEquation
      GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry
      (GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
        F.transitions)
      (fun _i _u _j _v => 1)
      (fun _i _u _j _v _hij _hnot => by norm_num)
      T.lower_bound_one

end IndexedNonConnectorCrossBlockSqDistanceTable

/-- A family of finite non-connector square-distance tables. -/
structure IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      IndexedNonConnectorCrossBlockSqDistanceTable F k hk

namespace IndexedNonConnectorCrossBlockSqDistanceTableFamily

/-- The table family supplies generated global separation at every positive
block count. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  (T.table k hk).generatedGlobalSeparation

/-- Exact Pach-Toth target from period-search data and finite non-connector
cross-block square-distance tables. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      (fun _k _hk => F.transitions.toFigure2TransitionObligations)
      (fun _k _hk => BaseTransitionRealization.exactBase)
      F.orientation
      (fun k hk => (T.table k hk).periodEquation)
      (fun k hk => T.separated k hk)
      (fun _k _hk =>
        GeneratedMetricClosure.exactBase_generatedBaseSameBlockIsometry)
      (fun _k _hk =>
        GeneratedMetricClosure.roleHingeTransitions_preserveSameBlockDistances
          F.transitions)

end IndexedNonConnectorCrossBlockSqDistanceTableFamily

end

end NonRigidConnectorSeparationFacts
end PachToth
end ErdosProblems1066
