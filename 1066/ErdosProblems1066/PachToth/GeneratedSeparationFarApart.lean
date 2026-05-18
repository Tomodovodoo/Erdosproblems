import ErdosProblems1066.PachToth.GeneratedPeriodClosure
import ErdosProblems1066.PachToth.UnitVectorGeometry

set_option autoImplicit false

/-!
# Generated far-apart separation wrappers

This module turns quantitative lower-bound checks for generated point pairs
into the named `GeneratedGlobalSeparation` hypothesis, then routes those
checks through the exact-block and arbitrary-`n` generated-chain closures.

The cross-block wrappers discharge same-block separation from the checked
one-block certificate and a supplied same-block isometry, so only genuinely
cross-block distance lower bounds remain.
-/

namespace ErdosProblems1066
namespace PachToth
namespace GeneratedSeparationFarApart

open FiniteGraph
open GeneratedPeriodClosure
open GeneratedSeparationInterface
open Arithmetic

noncomputable section

abbrev R2 := Prod Real Real

/-- A per-pair quantitative lower bound for distinct generated vertices. -/
def GeneratedPairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) ->
      lower i u j v <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A per-pair lower-bound table is strong enough for separation. -/
def GeneratedPairLowerBoundsAtLeastOne
    {k : Nat}
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) -> 1 <= lower i u j v

/-- A cross-block-only quantitative lower bound.  Same-block pairs can often
be discharged from the finite one-block data instead. -/
def GeneratedCrossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j ->
      lower i u j v <=
        _root_.eucDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A cross-block lower-bound table is strong enough for separation on every
cross-block pair. -/
def GeneratedCrossBlockLowerBoundsAtLeastOne
    {k : Nat}
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j -> 1 <= lower i u j v

/-- A per-pair quantitative squared-distance lower bound for distinct
generated vertices. -/
def GeneratedPairSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne (i, u) (j, v) ->
      lower i u j v <=
        UnitVectorGeometry.sqDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A cross-block-only quantitative squared-distance lower bound. -/
def GeneratedCrossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j ->
      lower i u j v <=
        UnitVectorGeometry.sqDist
          (GeneratedClosedChain.generatedPoint O hk base orientation i u)
          (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A directed successor connector pair from generated block `i` to generated
block `j`. -/
def GeneratedSuccessorConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Prop :=
  j = cyclicSucc hk i /\ CrossBlock.NextConnector u v

/-- A cyclic connector pair, allowing either endpoint order. -/
def GeneratedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Prop :=
  GeneratedSuccessorConnectorPair hk i u j v \/
    GeneratedSuccessorConnectorPair hk j v i u

/-- A non-connector cross-block quantitative distance lower bound.
Connector pairs are handled by the transition connector-unit equations, so
finite distance tables only need to cover the remaining cross-block pairs. -/
def GeneratedNonConnectorCrossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j ->
      Not (GeneratedCyclicConnectorPair hk i u j v) ->
        lower i u j v <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A non-connector cross-block quantitative squared-distance lower bound.
Connector pairs are handled by the transition connector-unit equations, so
finite square-distance tables only need to cover the remaining cross-block
pairs. -/
def GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j ->
      Not (GeneratedCyclicConnectorPair hk i u j v) ->
        lower i u j v <=
          UnitVectorGeometry.sqDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v)

/-- A non-connector cross-block lower-bound table is at least one on every
remaining cross-block pair. -/
def GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) : Prop :=
  forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
    Ne i j -> Not (GeneratedCyclicConnectorPair hk i u j v) ->
      1 <= lower i u j v

/-- A table entry bounded below by `1` and above by squared distance gives the
root-distance separation used by generated chains. -/
theorem one_le_eucDist_of_sqDistanceLowerBound {p q : R2} {lower : Real}
    (hge_one : 1 <= lower)
    (hlower : lower <= UnitVectorGeometry.sqDist p q) :
    1 <= _root_.eucDist p q := by
  rw [_root_.eucDist_ge_one_iff]
  exact le_trans hge_one (by
    simpa [UnitVectorGeometry.sqDist, UnitVectorGeometry.sqNorm,
      UnitVectorGeometry.sub] using hlower)

/-- Quantitative pairwise lower bounds imply generated global separation. -/
theorem generatedGlobalSeparation_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  exact le_trans (hge_one i u j v hne) (hlower i u j v hne)

/-- Pairwise squared-distance lower bounds imply generated global
separation. -/
theorem generatedGlobalSeparation_of_pairSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  exact
    one_le_eucDist_of_sqDistanceLowerBound
      (hge_one i u j v hne) (hlower i u j v hne)

/-- Uniform quantitative lower bounds imply generated global separation. -/
theorem generatedGlobalSeparation_of_uniformDistanceLowerBound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    {delta : Real}
    (hdelta : 1 <= delta)
    (hlower :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne (i, u) (j, v) ->
          delta <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  exact le_trans hdelta (hlower i u j v hne)

/-- Same-block generated separation follows from the checked one-block finite
separation data and a same-block isometry. -/
theorem generatedSameBlockSeparation_of_sameBlockIsometry
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation) :
    forall (i : Fin k) (u v : LocalVertex),
      Ne u v ->
        1 <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation i v) := by
  intro i u v huv
  have hfin :
      Ne (BlockPartition.localVertexEquivFin16 u)
        (BlockPartition.localVertexEquivFin16 v) := by
    intro h
    exact huv (BlockPartition.localVertexEquivFin16.injective h)
  have hsep :=
    OneBlockSoundness.oneBlockCertificate.separated
      (BlockPartition.localVertexEquivFin16 u)
      (BlockPartition.localVertexEquivFin16 v) hfin
  rw [same_block_isometry i u v]
  exact hsep

/-- Cross-block quantitative lower bounds, plus finite same-block separation,
imply generated global separation. -/
theorem generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  by_cases hij : i = j
  case pos =>
    subst j
    have huv : Ne u v := by
      intro huv
      exact hne (Prod.ext rfl huv)
    exact
      generatedSameBlockSeparation_of_sameBlockIsometry
        O hk base orientation same_block_isometry i u v huv
  case neg =>
    exact le_trans (hge_one i u j v hij) (hlower i u j v hij)

/-- A generated period has distance exactly one on every directed successor
connector pair. -/
theorem generatedSuccessorConnectorPair_distance_eq_one
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : GeneratedSuccessorConnectorPair hk i u j v) :
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) = 1 := by
  have hj : j = cyclicSucc hk i := hpair.1
  have hconn : CrossBlock.NextConnector u v := hpair.2
  subst j
  rw [GeneratedClosedChain.generatedPoint_successor_compatible
    O hk base orientation period i v]
  exact
    Figure2Certificate.SameOppositeTransitionObligations.transitionFor_connector_unit_edges
      O (orientation i) (GeneratedClosedChain.generatedPoint O hk base orientation i)
      u v hconn

/-- A generated period has distance exactly one on cyclic connector pairs in
either endpoint order. -/
theorem generatedCyclicConnectorPair_distance_eq_one
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : GeneratedCyclicConnectorPair hk i u j v) :
    _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) = 1 := by
  cases hpair with
  | inl hforward =>
    exact
      generatedSuccessorConnectorPair_distance_eq_one
        O hk base orientation period i u j v hforward
  | inr hreverse =>
    rw [_root_.eucDist_comm]
    exact
      generatedSuccessorConnectorPair_distance_eq_one
        O hk base orientation period j v i u hreverse

/-- Connector pairs supply their own generated separation lower bound. -/
theorem generatedCyclicConnectorPair_separated
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : GeneratedCyclicConnectorPair hk i u j v) :
    1 <=
      _root_.eucDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  rw [generatedCyclicConnectorPair_distance_eq_one
    O hk base orientation period i u j v hpair]

/-- Complete a non-connector distance lower table by filling connector pairs
with the exact connector value `1`. -/
noncomputable def generatedConnectorSeparatedLower
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real := by
  classical
  exact fun i u j v =>
    if GeneratedCyclicConnectorPair hk i u j v then (1 : Real)
    else lower i u j v

/-- The connector-filled distance lower table is at least one on every
cross-block pair. -/
theorem generatedConnectorSeparatedLower_ge_one
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower) :
    GeneratedCrossBlockLowerBoundsAtLeastOne
      (generatedConnectorSeparatedLower hk lower) := by
  intro i u j v hij
  by_cases hconn : GeneratedCyclicConnectorPair hk i u j v
  case pos =>
    simp [generatedConnectorSeparatedLower, hconn]
  case neg =>
    simpa [generatedConnectorSeparatedLower, hconn] using
      hge_one i u j v hij hconn

/-- Connector exact values and finite non-connector distance facts give a
genuine all-cross-block distance lower table. -/
theorem generatedConnectorSeparatedLower_bound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hlower :
      GeneratedNonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedCrossBlockDistanceLowerBounds
      O hk base orientation (generatedConnectorSeparatedLower hk lower) := by
  intro i u j v hij
  by_cases hconn : GeneratedCyclicConnectorPair hk i u j v
  case pos =>
    simpa [generatedConnectorSeparatedLower, hconn] using
      generatedCyclicConnectorPair_separated
        O hk base orientation period i u j v hconn
  case neg =>
    simpa [generatedConnectorSeparatedLower, hconn] using
      hlower i u j v hij hconn

/-- Non-connector distance facts plus connector-unit facts separate every
cross-block pair. -/
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
        O hk base orientation lower) :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne i j ->
        1 <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  intro i u j v hij
  by_cases hconn : GeneratedCyclicConnectorPair hk i u j v
  case pos =>
    exact generatedCyclicConnectorPair_separated
      O hk base orientation period i u j v hconn
  case neg =>
    exact le_trans (hge_one i u j v hij hconn)
      (hlower i u j v hij hconn)

/-- Same-block separation, connector-unit facts, and non-connector distance
lower bounds imply global generated separation. -/
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
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation same_block_isometry
      (generatedConnectorSeparatedLower hk lower)
      (generatedConnectorSeparatedLower_ge_one hk lower hge_one)
      (generatedConnectorSeparatedLower_bound
        O hk base orientation period lower hlower)

/-- Non-connector distance lower bounds with reduced same-block hypotheses. -/
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

/-- Connector pairs also have squared distance exactly one. -/
theorem generatedCyclicConnectorPair_sqDist_eq_one
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hpair : GeneratedCyclicConnectorPair hk i u j v) :
    UnitVectorGeometry.sqDist
        (GeneratedClosedChain.generatedPoint O hk base orientation i u)
        (GeneratedClosedChain.generatedPoint O hk base orientation j v) = 1 := by
  exact
    (UnitVectorGeometry.eucDist_eq_one_iff_sqDist_eq_one
      (GeneratedClosedChain.generatedPoint O hk base orientation i u)
      (GeneratedClosedChain.generatedPoint O hk base orientation j v)).mp
      (generatedCyclicConnectorPair_distance_eq_one
        O hk base orientation period i u j v hpair)

/-- Complete a non-connector square-distance lower table by filling connector
pairs with the exact square value `1`. -/
noncomputable def generatedConnectorSeparatedSqLower
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real := by
  classical
  exact fun i u j v =>
    if GeneratedCyclicConnectorPair hk i u j v then (1 : Real)
    else lower i u j v

/-- The connector-filled square lower table is at least one on every
cross-block pair. -/
theorem generatedConnectorSeparatedSqLower_ge_one
    {k : Nat} (hk : 0 < k)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower) :
    GeneratedCrossBlockLowerBoundsAtLeastOne
      (generatedConnectorSeparatedSqLower hk lower) := by
  intro i u j v hij
  by_cases hconn : GeneratedCyclicConnectorPair hk i u j v
  case pos =>
    simp [generatedConnectorSeparatedSqLower, hconn]
  case neg =>
    simpa [generatedConnectorSeparatedSqLower, hconn] using
      hge_one i u j v hij hconn

/-- Connector exact square values and finite non-connector square-distance
facts give a genuine all-cross-block squared-distance lower table. -/
theorem generatedConnectorSeparatedSqLower_bound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hlower :
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedCrossBlockSqDistanceLowerBounds
      O hk base orientation (generatedConnectorSeparatedSqLower hk lower) := by
  intro i u j v hij
  by_cases hconn : GeneratedCyclicConnectorPair hk i u j v
  case pos =>
    have hsq :
        UnitVectorGeometry.sqDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v) =
          1 :=
      generatedCyclicConnectorPair_sqDist_eq_one
        O hk base orientation period i u j v hconn
    simpa [generatedConnectorSeparatedSqLower, hconn] using
      (show (1 : Real) <=
          UnitVectorGeometry.sqDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v) by
        rw [hsq])
  case neg =>
    simpa [generatedConnectorSeparatedSqLower, hconn] using
      hlower i u j v hij hconn

/-- Non-connector squared-distance facts plus connector-unit facts separate
every cross-block pair. -/
theorem generatedCrossBlockSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk lower)
    (hlower :
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne i j ->
        1 <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  intro i u j v hij
  by_cases hconn : GeneratedCyclicConnectorPair hk i u j v
  case pos =>
    exact generatedCyclicConnectorPair_separated
      O hk base orientation period i u j v hconn
  case neg =>
    exact
      one_le_eucDist_of_sqDistanceLowerBound
        (hge_one i u j v hij hconn)
        (hlower i u j v hij hconn)

/-- Same-block separation, connector-unit facts, and non-connector
squared-distance lower bounds imply global generated separation. -/
theorem generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
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
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  by_cases hij : i = j
  case pos =>
    subst j
    have huv : Ne u v := by
      intro huv
      exact hne (Prod.ext rfl huv)
    exact
      generatedSameBlockSeparation_of_sameBlockIsometry
        O hk base orientation same_block_isometry i u v huv
  case neg =>
    exact
      generatedCrossBlockSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation period lower hge_one hlower i u j v hij

/-- Non-connector squared-distance lower bounds with reduced same-block
hypotheses. -/
theorem generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds_reduced
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
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
      O hk base orientation period
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      lower hge_one hlower

/-- Cross-block squared-distance lower bounds imply separation for every
cross-block pair. -/
theorem generatedCrossBlockSeparation_of_crossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
      Ne i j ->
        1 <=
          _root_.eucDist
            (GeneratedClosedChain.generatedPoint O hk base orientation i u)
            (GeneratedClosedChain.generatedPoint O hk base orientation j v) := by
  intro i u j v hij
  exact
    one_le_eucDist_of_sqDistanceLowerBound
      (hge_one i u j v hij) (hlower i u j v hij)

/-- Cross-block squared-distance lower bounds, plus finite same-block
separation, imply generated global separation. -/
theorem generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  intro i u j v hne
  by_cases hij : i = j
  case pos =>
    subst j
    have huv : Ne u v := by
      intro huv
      exact hne (Prod.ext rfl huv)
    exact
      generatedSameBlockSeparation_of_sameBlockIsometry
        O hk base orientation same_block_isometry i u v huv
  case neg =>
    exact
      generatedCrossBlockSeparation_of_crossBlockSqDistanceLowerBounds
        O hk base orientation lower hge_one hlower i u j v hij

/-- Uniform cross-block lower bounds, plus finite same-block separation, imply
generated global separation. -/
theorem generatedGlobalSeparation_of_uniformCrossBlockDistanceLowerBound
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    {delta : Real}
    (hdelta : 1 <= delta)
    (hlower :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          delta <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation same_block_isometry
      (fun _i _u _j _v => delta)
      (fun i u j v hij => hdelta)
      (fun i u j v hij => hlower i u j v hij)

/-- Cross-block lower bounds with reduced same-block hypotheses. -/
theorem generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      lower hge_one hlower

/-- Cross-block squared-distance lower bounds with reduced same-block
hypotheses. -/
theorem generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds
      O hk base orientation
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      lower hge_one hlower

/-- Uniform cross-block lower bounds with reduced same-block hypotheses. -/
theorem generatedGlobalSeparation_of_uniformCrossBlockDistanceLowerBound_reduced
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    {delta : Real}
    (hdelta : 1 <= delta)
    (hlower :
      forall (i : Fin k) (u : LocalVertex) (j : Fin k) (v : LocalVertex),
        Ne i j ->
          delta <=
            _root_.eucDist
              (GeneratedClosedChain.generatedPoint O hk base orientation i u)
              (GeneratedClosedChain.generatedPoint O hk base orientation j v)) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      O hk base orientation := by
  exact
    generatedGlobalSeparation_of_uniformCrossBlockDistanceLowerBound
      O hk base orientation
      (GeneratedClosedChain.generatedPoint_same_block_isometry
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances)
      hdelta hlower

/-- Reduced generated metric hypotheses can be promoted to the full metric
facade by deriving same-block isometry along the generated orbit. -/
def generatedMetricHypotheses_of_reducedMetricHypotheses
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (H :
      GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated := H.separated
  same_block_isometry :=
    GeneratedSeparationInterface.same_block_isometry_of_reduced
      O hk base orientation H

/-- Fieldwise characterization of the full generated metric facade. -/
theorem generatedMetricHypotheses_iff_fields
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
        O hk base orientation <->
      GeneratedSeparationInterface.GeneratedGlobalSeparation
          O hk base orientation /\
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          O hk base orientation := by
  constructor
  · intro H
    exact ⟨H.separated, H.same_block_isometry⟩
  · intro H
    exact
      { separated := H.1
        same_block_isometry := H.2 }

/-- Fieldwise characterization of the reduced generated metric facade. -/
theorem generatedReducedMetricHypotheses_iff_fields
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation <->
      GeneratedSeparationInterface.GeneratedGlobalSeparation
          O hk base orientation /\
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base /\
          GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
            O := by
  constructor
  · intro H
    exact
      ⟨H.separated, H.base_same_block_isometry,
        H.transition_preserves_same_block_distances⟩
  · intro H
    exact
      { separated := H.1
        base_same_block_isometry := H.2.1
        transition_preserves_same_block_distances := H.2.2 }

/-- Reduced metric data is equivalent to full metric data plus the two
reduced same-block fields.  The full facade is obtained by deriving the
generated same-block isometry from those reduced fields. -/
theorem generatedReducedMetricHypotheses_iff_fullMetricHypotheses_and_fields
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
        O hk base orientation <->
      GeneratedSeparationInterface.GeneratedMetricHypotheses
          O hk base orientation /\
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base /\
          GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
            O := by
  constructor
  · intro H
    exact
      ⟨generatedMetricHypotheses_of_reducedMetricHypotheses
          O hk base orientation H,
        H.base_same_block_isometry,
        H.transition_preserves_same_block_distances⟩
  · intro H
    exact
      { separated := H.1.separated
        base_same_block_isometry := H.2.1
        transition_preserves_same_block_distances := H.2.2 }

/-- Promote reduced metric hypotheses for a generated-chain family to the
full metric facade. -/
def generatedChainFamilyMetricHypotheses_of_reducedMetricHypotheses
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    GeneratedSeparationInterface.GeneratedChainFamily.MetricHypotheses F where
  metric := fun k hk =>
    generatedMetricHypotheses_of_reducedMetricHypotheses
      (F.O k hk) hk (F.base k hk) (F.orientation k hk) (H.metric k hk)

/-- Promote reduced metric hypotheses for an eventual generated-chain family
to the full metric facade. -/
def eventualGeneratedChainFamilyMetricHypotheses_of_reducedMetricHypotheses
    {K0 : Nat}
    (F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0)
    (H :
      GeneratedSeparationInterface.EventualGeneratedChainFamily.ReducedMetricHypotheses
        F) :
    GeneratedSeparationInterface.EventualGeneratedChainFamily.MetricHypotheses
      F where
  metric := fun k hK hk =>
    generatedMetricHypotheses_of_reducedMetricHypotheses
      (F.O k hK hk) hk (F.base k hK hk) (F.orientation k hK hk)
      (H.metric k hK hk)

/-- Exact target from reduced family metrics, routed through the full metric
facade. -/
theorem targetUpperConstructionFiveSixteen_of_family_reduced_via_full
    (F : GeneratedSeparationInterface.GeneratedChainFamily)
    (period : F.Periods)
    (H :
      GeneratedSeparationInterface.GeneratedChainFamily.ReducedMetricHypotheses
        F) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family
      F period
      (generatedChainFamilyMetricHypotheses_of_reducedMetricHypotheses F H)

/-- Arbitrary target from reduced eventual-family metrics, routed through the
full metric facade. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced_via_full
    {K0 : Nat}
    (F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0)
    (period : F.Periods)
    (H :
      GeneratedSeparationInterface.EventualGeneratedChainFamily.ReducedMetricHypotheses
        F)
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F period
      (eventualGeneratedChainFamilyMetricHypotheses_of_reducedMetricHypotheses
        F H)
      Hsmall

/-- Package full generated metric hypotheses from per-pair lower bounds. -/
def generatedMetricHypotheses_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_pairDistanceLowerBounds
      O hk base orientation lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package full generated metric hypotheses from per-pair squared-distance
lower bounds. -/
def generatedMetricHypotheses_of_pairSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_pairSqDistanceLowerBounds
      O hk base orientation lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package reduced generated metric hypotheses from per-pair lower bounds. -/
def generatedReducedMetricHypotheses_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_pairDistanceLowerBounds
      O hk base orientation lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Package reduced generated metric hypotheses from per-pair squared-distance
lower bounds. -/
def generatedReducedMetricHypotheses_of_pairSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_pairSqDistanceLowerBounds
      O hk base orientation lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Package full generated metric hypotheses from cross-block lower bounds,
using finite same-block separation for pairs in the same block. -/
def generatedMetricHypotheses_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
      O hk base orientation same_block_isometry lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package full generated metric hypotheses from cross-block squared-distance
lower bounds, using finite same-block separation for pairs in the same block. -/
def generatedMetricHypotheses_of_crossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds
      O hk base orientation same_block_isometry lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package reduced generated metric hypotheses from cross-block lower bounds,
using finite same-block separation for pairs in the same block. -/
def generatedReducedMetricHypotheses_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
      O hk base orientation base_same_block_isometry
      transition_preserves_same_block_distances lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Package reduced generated metric hypotheses from cross-block
squared-distance lower bounds, using finite same-block separation for pairs in
the same block. -/
def generatedReducedMetricHypotheses_of_crossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (base_same_block_isometry :
      GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry base)
    (transition_preserves_same_block_distances :
      GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
        O)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds_reduced
      O hk base orientation base_same_block_isometry
      transition_preserves_same_block_distances lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Package full generated metric hypotheses from generated connector facts
and non-connector cross-block distance lower bounds. -/
def generatedMetricHypotheses_of_nonConnectorCrossBlockDistanceLowerBounds
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
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
      O hk base orientation period same_block_isometry lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package reduced generated metric hypotheses from generated connector facts
and non-connector cross-block distance lower bounds. -/
def generatedReducedMetricHypotheses_of_nonConnectorCrossBlockDistanceLowerBounds
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
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds_reduced
      O hk base orientation period base_same_block_isometry
      transition_preserves_same_block_distances lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Package full generated metric hypotheses from generated connector facts
and non-connector cross-block squared-distance lower bounds. -/
def generatedMetricHypotheses_of_nonConnectorCrossBlockSqDistanceLowerBounds
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
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
      O hk base orientation period same_block_isometry lower hge_one hlower
  same_block_isometry := same_block_isometry

/-- Package reduced generated metric hypotheses from generated connector facts
and non-connector cross-block squared-distance lower bounds. -/
def generatedReducedMetricHypotheses_of_nonConnectorCrossBlockSqDistanceLowerBounds
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
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    GeneratedSeparationInterface.GeneratedReducedMetricHypotheses
      O hk base orientation where
  separated :=
    generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds_reduced
      O hk base orientation period base_same_block_isometry
      transition_preserves_same_block_distances lower hge_one hlower
  base_same_block_isometry := base_same_block_isometry
  transition_preserves_same_block_distances :=
    transition_preserves_same_block_distances

/-- Exact-block target from one period equation, same-block isometry, and
per-pair lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_pairDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_pairDistanceLowerBounds
        O hk base orientation same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data, and
per-pair lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_pairDistanceLowerBounds_reduced
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
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_pairDistanceLowerBounds
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact-block target from one period equation, same-block isometry, and
per-pair squared-distance lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_pairSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairSqDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_pairSqDistanceLowerBounds
        O hk base orientation same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data, and
per-pair squared-distance lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_pairSqDistanceLowerBounds_reduced
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
    (hge_one : GeneratedPairLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedPairSqDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_pairSqDistanceLowerBounds
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact-block target from one period equation and cross-block lower bounds.
Same-block separation is obtained from the checked finite block. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_crossBlockDistanceLowerBounds
        O hk base orientation same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data, and
cross-block lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockDistanceLowerBounds_reduced
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
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_crossBlockDistanceLowerBounds
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact-block target from one period equation and cross-block
squared-distance lower bounds.  Same-block separation is obtained from the
checked finite block. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockSqDistanceLowerBounds
    (O : Figure2Certificate.SameOppositeTransitionObligations)
    {k : Nat} (hk : 0 < k)
    (base : LocalVertex -> R2)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (period : PeriodInterface.GeneratedPeriodEquation O hk base orientation)
    (same_block_isometry :
      GeneratedSeparationInterface.GeneratedSameBlockIsometry
        O hk base orientation)
    (lower : Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_crossBlockSqDistanceLowerBounds
        O hk base orientation same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data, and
cross-block squared-distance lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_crossBlockSqDistanceLowerBounds_reduced
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
    (hge_one : GeneratedCrossBlockLowerBoundsAtLeastOne lower)
    (hlower :
      GeneratedCrossBlockSqDistanceLowerBounds O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_crossBlockSqDistanceLowerBounds
        O hk base orientation base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact-block target from one period equation, same-block isometry,
connector-unit facts, and non-connector cross-block distance lower bounds. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock_of_nonConnectorCrossBlockDistanceLowerBounds
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
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_nonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation period same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data,
connector-unit facts, and non-connector cross-block distance lower bounds. -/
theorem targetAt_of_nonConnectorDistanceLowerBounds_reduced
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
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_nonConnectorCrossBlockDistanceLowerBounds
        O hk base orientation period base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact-block target from one period equation, same-block isometry,
connector-unit facts, and non-connector cross-block squared-distance lower
bounds. -/
theorem targetAt_of_nonConnectorSqDistanceLowerBounds
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
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation
      O hk base orientation period
      (generatedMetricHypotheses_of_nonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation period same_block_isometry lower hge_one hlower)

/-- Exact-block target from one period equation, reduced same-block data,
connector-unit facts, and non-connector cross-block squared-distance lower
bounds. -/
theorem targetAt_of_nonConnectorSqDistanceLowerBounds_reduced
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
      GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation lower) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_generatedPeriodEquation_reduced
      O hk base orientation period
      (generatedReducedMetricHypotheses_of_nonConnectorCrossBlockSqDistanceLowerBounds
        O hk base orientation period base_same_block_isometry
        transition_preserves_same_block_distances lower hge_one hlower)

/-- Exact Pach--Toth target from generated period equations and per-pair lower
bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_pairDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_pairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, and per-pair lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_pairDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_pairDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Exact Pach--Toth target from generated period equations and per-pair
squared-distance lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_pairSqDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_pairSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, and per-pair squared-distance lower bounds for every positive
block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_pairSqDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedPairSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_pairSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Exact Pach--Toth target from generated period equations and cross-block
lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_crossBlockDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk)
          (same_block_isometry k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, and cross-block lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_crossBlockDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
          (O k hk) hk (base k hk) (orientation k hk)
          (base_same_block_isometry k hk)
          (transition_preserves_same_block_distances k hk)
          (lower k hk) (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Exact Pach--Toth target from generated period equations and cross-block
squared-distance lower bounds for every positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_crossBlockSqDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk)
          (same_block_isometry k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, and cross-block squared-distance lower bounds for every
positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_crossBlockSqDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedCrossBlockSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds_reduced
          (O k hk) hk (base k hk) (orientation k hk)
          (base_same_block_isometry k hk)
          (transition_preserves_same_block_distances k hk)
          (lower k hk) (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Exact Pach--Toth target from generated period equations, connector-unit
facts, and non-connector cross-block distance lower bounds for every positive
block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_nonConnectorCrossBlockDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk)
          (period k hk) (same_block_isometry k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, connector-unit facts, and non-connector cross-block distance
lower bounds for every positive block count. -/
theorem target_of_period_nonConnectorDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds_reduced
          (O k hk) hk (base k hk) (orientation k hk) (period k hk)
          (base_same_block_isometry k hk)
          (transition_preserves_same_block_distances k hk)
          (lower k hk) (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Exact Pach--Toth target from generated period equations, connector-unit
facts, and non-connector cross-block squared-distance lower bounds for every
positive block count. -/
theorem targetUpperConstructionFiveSixteen_of_period_nonConnectorCrossBlockSqDistanceLowerBounds
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hk) hk (base k hk) (orientation k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_sameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk)
          (period k hk) (same_block_isometry k hk) (lower k hk)
          (hge_one k hk) (hlower k hk))
      same_block_isometry

/-- Exact Pach--Toth target from generated period equations, reduced
same-block data, connector-unit facts, and non-connector cross-block
squared-distance lower bounds for every positive block count. -/
theorem target_of_period_nonConnectorSqDistanceLowerBounds_reduced
    (O :
      forall (k : Nat), 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base : forall (k : Nat), 0 < k -> LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hk) hk (base k hk) (orientation k hk))
    (base_same_block_isometry :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hk))
    (lower :
      forall (k : Nat) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk (lower k hk))
    (hlower :
      forall (k : Nat) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
          (O k hk) hk (base k hk) (orientation k hk) (lower k hk)) :
    targetUpperConstructionFiveSixteen := by
  exact
    GeneratedPeriodClosure.targetUpperConstructionFiveSixteen_of_period_separation_reducedSameBlock
      O base orientation period
      (fun k hk =>
        generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds_reduced
          (O k hk) hk (base k hk) (orientation k hk) (period k hk)
          (base_same_block_isometry k hk)
          (transition_preserves_same_block_distances k hk)
          (lower k hk) (hge_one k hk) (hlower k hk))
      base_same_block_isometry
      transition_preserves_same_block_distances

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, per-pair lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_pairDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_pairDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, per-pair lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_pairDistanceLowerBounds_and_small_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_pairDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, per-pair squared-distance lower bounds, and the supplied
small cases. -/
theorem targetArbitrary_of_eventual_period_pairSqDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairSqDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_pairSqDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, per-pair squared-distance lower bounds, and the
supplied small cases. -/
theorem targetArbitrary_of_eventual_period_pairSqDistanceLowerBounds_and_small_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedPairSqDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_pairSqDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, cross-block lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_crossBlockDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_crossBlockDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (same_block_isometry k hK hk) (lower k hK hk)
                (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, cross-block lower bounds, and the supplied small
cases. -/
theorem targetArbitrary_of_eventual_period_crossBlockDistanceLowerBounds_and_small_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_crossBlockDistanceLowerBounds_reduced
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (base_same_block_isometry k hK hk)
                (transition_preserves_same_block_distances k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, cross-block squared-distance lower bounds, and the
supplied small cases. -/
theorem targetArbitrary_of_eventual_period_crossBlockSqDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockSqDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (same_block_isometry k hK hk) (lower k hK hk)
                (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, cross-block squared-distance lower bounds, and the
supplied small cases. -/
theorem targetArbitrary_of_eventual_period_crossBlockSqDistanceLowerBounds_and_small_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockLowerBoundsAtLeastOne (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedCrossBlockSqDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_crossBlockSqDistanceLowerBounds_reduced
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (base_same_block_isometry k hK hk)
                (transition_preserves_same_block_distances k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, connector-unit facts, non-connector cross-block distance
lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_nonConnectorCrossBlockDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk
          (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (period k hK hk) (same_block_isometry k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, connector-unit facts, non-connector cross-block
distance lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_nonConnectorDistanceLowerBounds_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk
          (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds_reduced
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (period k hK hk) (base_same_block_isometry k hK hk)
                (transition_preserves_same_block_distances k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
same-block isometry, connector-unit facts, non-connector cross-block
squared-distance lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_period_nonConnectorCrossBlockSqDistanceLowerBounds_and_small
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedSameBlockIsometry
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk
          (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (period k hK hk) (same_block_isometry k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            same_block_isometry := same_block_isometry k hK hk } }
      Hsmall

/-- Arbitrary-`n` Pach--Toth target from eventual generated period equations,
reduced same-block data, connector-unit facts, non-connector cross-block
squared-distance lower bounds, and the supplied small cases. -/
theorem targetArbitrary_of_eventual_nonConnectorSqDistanceLowerBounds_reduced
    (K0 : Nat)
    (O :
      forall (k : Nat), K0 <= k -> 0 < k ->
        Figure2Certificate.SameOppositeTransitionObligations)
    (base :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        LocalVertex -> R2)
    (orientation :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> OrientationData.BlockOrientation)
    (period :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        PeriodInterface.GeneratedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk))
    (base_same_block_isometry :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedBaseSameBlockIsometry
          (base k hK hk))
    (transition_preserves_same_block_distances :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedSeparationInterface.GeneratedTransitionsPreserveSameBlockDistances
          (O k hK hk))
    (lower :
      forall (k : Nat) (_hK : K0 <= k) (_hk : 0 < k),
        Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real)
    (hge_one :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne hk
          (lower k hK hk))
    (hlower :
      forall (k : Nat) (hK : K0 <= k) (hk : 0 < k),
        GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (lower k hK hk))
    (Hsmall :
      forall N0 : Nat,
        (forall n : Nat, N0 <= n -> targetUpperConstructionFiveSixteenAt n) ->
          targetUpperConstructionFiveSixteenSmallUpTo N0) :
    targetUpperConstructionFiveSixteenArbitrary := by
  let F : GeneratedSeparationInterface.EventualGeneratedChainFamily K0 :=
    { O := O
      base := base
      orientation := orientation }
  exact
    targetUpperConstructionFiveSixteenArbitrary_of_eventual_family_and_small_reduced
      F
      (fun k hK hk =>
        GeneratedPeriodClosure.generatedPeriod_of_generatedPeriodEquation
          (O k hK hk) hk (base k hK hk) (orientation k hK hk)
          (period k hK hk))
      { metric := fun k hK hk =>
          { separated :=
              generatedGlobalSeparation_of_nonConnectorCrossBlockSqDistanceLowerBounds_reduced
                (O k hK hk) hk (base k hK hk) (orientation k hK hk)
                (period k hK hk) (base_same_block_isometry k hK hk)
                (transition_preserves_same_block_distances k hK hk)
                (lower k hK hk) (hge_one k hK hk) (hlower k hK hk)
            base_same_block_isometry := base_same_block_isometry k hK hk
            transition_preserves_same_block_distances :=
              transition_preserves_same_block_distances k hK hk } }
      Hsmall

end

end GeneratedSeparationFarApart
end PachToth
end ErdosProblems1066
