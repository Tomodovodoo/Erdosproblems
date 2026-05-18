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

/-- The everywhere-one lower table satisfies the non-connector `>= 1`
obligation. -/
theorem generatedNonConnectorCrossBlockLowerBoundsAtLeastOne_one
    {k : Nat} (hk : 0 < k) :
    GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk
      (fun _i _u _j _v => (1 : Real)) := by
  intro _i _u _j _v _hij _hnot
  norm_num

/-- The full cross-block lower table obtained from a non-connector table by
filling cyclic connector entries with the connector-unit value `1`. -/
noncomputable def connectorSeparatedLower
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real := by
  classical
  exact fun i u j v =>
    if CyclicConnectorPair hk i u j v then (1 : Real) else lower i u j v

/-- The connector-completed lower table is at least one on every cross-block
pair: connector slots are filled by `1`, and all other slots use the supplied
non-connector lower-table fact. -/
theorem connectorSeparatedLower_ge_one
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      (connectorSeparatedLower hk lower) := by
  intro i u j v hij
  by_cases hconn : CyclicConnectorPair hk i u j v
  case pos =>
    simp [connectorSeparatedLower, hconn]
  case neg =>
    simpa [connectorSeparatedLower, hconn] using
      hge_one i u j v hij hconn

/-- The connector-completed lower table is bounded by generated distances.
Connector slots use the role-hinge connector-unit facts; non-connector slots
use the finite lower-bound table. -/
theorem connectorSeparatedLower_bound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hlower :
      GeneratedNonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      O hk base orientation (connectorSeparatedLower hk lower) := by
  intro i u j v hij
  by_cases hconn : CyclicConnectorPair hk i u j v
  case pos =>
    simpa [connectorSeparatedLower, hconn] using
      cyclicConnectorPair_separated
        O hk base orientation period i u j v hconn
  case neg =>
    simpa [connectorSeparatedLower, hconn] using
      hlower i u j v hij hconn

/-- On distinct blocks, connector pairs are separated by the transition
connector-unit facts, while non-connector pairs are separated by the supplied
finite lower table. -/
theorem generatedCrossBlockSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower)
    (hlower :
      GeneratedNonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation lower)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hij : Ne i j) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  by_cases hconn : CyclicConnectorPair hk i u j v
  · exact cyclicConnectorPair_separated
      O hk base orientation period i u j v hconn
  · exact le_trans (hge_one i u j v hij hconn)
      (hlower i u j v hij hconn)

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
  exact
    GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation same_block_isometry
      (connectorSeparatedLower hk lower)
      (connectorSeparatedLower_ge_one hk lower hge_one)
      (connectorSeparatedLower_bound
        O hk base orientation period lower hlower)

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
    GeneratedSeparationFarApart.generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
      O hk base orientation
      base_same_block_isometry transition_preserves_same_block_distances
      (connectorSeparatedLower hk lower)
      (connectorSeparatedLower_ge_one hk lower hge_one)
      (connectorSeparatedLower_bound
        O hk base orientation period lower hlower)

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

/-- The local-vertex lower table induced by a finite non-connector
square-distance table.  Connector pairs are handled separately, so the table
uses the fixed value `1` only on non-connector cross-block obligations. -/
def lower
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (_T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun _i _u _j _v => 1

@[simp]
theorem lower_apply
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    T.lower i u j v = 1 :=
  rfl

/-- Passing from local vertices to their finite indices preserves the
non-connector side condition. -/
theorem not_indexedCyclicConnectorPair_of_not_cyclicConnectorPair
    {k : Nat} {hk : 0 < k}
    {i : Fin k} {u : LocalVertex}
    {j : Fin k} {v : LocalVertex}
    (hnot : Not (CyclicConnectorPair hk i u j v)) :
    Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
      j (localVertexIndex v)) := by
  intro hidx
  exact hnot (by
    simpa [IndexedCyclicConnectorPair] using hidx)

/-- The induced everywhere-one lower table satisfies the non-connector `>= 1`
obligation. -/
theorem lower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk T.lower := by
  intro _i _u _j _v _hij _hnot
  norm_num [lower]

/-- A finite non-connector square-distance table gives the metric lower-bound
predicate for the induced local lower table. -/
theorem lower_bound
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedNonConnectorCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      T.lower := by
  intro i u j v hij hnot
  have hnot_index :
      Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
        j (localVertexIndex v)) :=
    not_indexedCyclicConnectorPair_of_not_cyclicConnectorPair hnot
  simpa [lower, indexedGeneratedPoint] using
    (one_le_indexedGenerated_eucDist_iff_sqDist F hk
      i (localVertexIndex u) j (localVertexIndex v)).2
      (T.sqDist_ge_one i (localVertexIndex u)
        j (localVertexIndex v) hij hnot_index)

/-- Compatibility spelling for callers that want the uniform lower table
written directly as `fun _ _ _ _ => 1`. -/
theorem lower_bound_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedNonConnectorCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      (fun _i _u _j _v => 1) := by
  simpa [lower] using T.lower_bound

/-- The induced everywhere-one lower table is at least one on all cross-block
pairs, including connector slots. -/
theorem crossBlock_lower_ge_one
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockLowerBoundsAtLeastOne
      T.lower := by
  intro _i _u _j _v _hij
  norm_num [lower]

/-- Connector slots and finite non-connector square-distance entries together
bound the everywhere-one cross-block lower table. -/
theorem crossBlock_lower_bound
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedSeparationFarApart.GeneratedCrossBlockDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      T.lower := by
  intro i u j v hij
  by_cases hconn : CyclicConnectorPair hk i u j v
  case pos =>
    simpa [lower] using
      cyclicConnectorPair_separated
        F.transitions.toFigure2TransitionObligations hk
        BaseTransitionRealization.exactBase (F.orientation k hk)
        T.periodEquation i u j v hconn
  case neg =>
    exact T.lower_bound i u j v hij hconn

/-- Expand finite non-connector square-distance data to the existing indexed
cross-block lower-table facade by filling connector slots with `1`. -/
def toCrossBlockLowerTable
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    IndexedCrossBlockLowerTable F k hk where
  lower := fun _i _u _j _v => 1
  lower_ge_one := by
    intro _i _u _j _v _hij
    norm_num
  lower_bound := by
    intro i u j v hij
    by_cases hconn : IndexedCyclicConnectorPair hk i u j v
    case pos =>
      have hpair :
          CyclicConnectorPair hk i (localVertexOfIndex u)
            j (localVertexOfIndex v) := by
        simpa [IndexedCyclicConnectorPair] using hconn
      simpa [indexedGeneratedPoint] using
        cyclicConnectorPair_separated
          F.transitions.toFigure2TransitionObligations hk
          BaseTransitionRealization.exactBase (F.orientation k hk)
          T.periodEquation i (localVertexOfIndex u)
          j (localVertexOfIndex v) hpair
    case neg =>
      simpa using
        one_le_indexedGenerated_eucDist_of_one_le_sqDist
          F hk i u j v (T.sqDist_ge_one i u j v hij hconn)

@[simp]
theorem toCrossBlockLowerTable_lower
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    T.toCrossBlockLowerTable.lower i u j v = 1 :=
  rfl

/-- Finite non-connector square-distance tables, together with the connector
unit facts and reduced same-block facts, give generated global separation. -/
theorem generatedGlobalSeparation
    {F : RoleHingedPeriodSearchFamily}
    {k : Nat} {hk : 0 < k}
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) := by
  exact T.toCrossBlockLowerTable.generatedGlobalSeparation

end IndexedNonConnectorCrossBlockSqDistanceTable

/-- A family of finite non-connector square-distance tables. -/
structure IndexedNonConnectorCrossBlockSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      IndexedNonConnectorCrossBlockSqDistanceTable F k hk

namespace IndexedNonConnectorCrossBlockSqDistanceTableFamily

/-- Expand a family of non-connector square-distance tables to the existing
finite-index cross-block lower-table family. -/
def toCrossBlockLowerTableFamily
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    IndexedCrossBlockLowerTableFamily F where
  table := fun k hk => (T.table k hk).toCrossBlockLowerTable

/-- The connector-separated finite data as the standard cross-block lower
bound facade. -/
def toCrossBlockLowerBounds
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    CrossBlockLowerBounds F :=
  CrossBlockLowerBounds.ofIndexedTables T.toCrossBlockLowerTableFamily

/-- The table family supplies generated global separation at every positive
block count. -/
theorem separated
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toCrossBlockLowerBounds.separated k hk

/-- Exact Pach-Toth target from period-search data and finite non-connector
cross-block square-distance tables. -/
theorem targetUpperConstructionFiveSixteen
    {F : RoleHingedPeriodSearchFamily}
    (T : IndexedNonConnectorCrossBlockSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteen

end IndexedNonConnectorCrossBlockSqDistanceTableFamily

end

end NonRigidConnectorSeparationFacts
end PachToth
end ErdosProblems1066
