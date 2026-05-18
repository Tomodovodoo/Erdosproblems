import ErdosProblems1066.PachToth.ExactFamilyClosure
import ErdosProblems1066.PachToth.NonRigidConnectorSeparationFacts
import ErdosProblems1066.PachToth.RoleHingeInterfaceRefinement

set_option autoImplicit false

/-!
# Pach--Toth remaining-data matrix

This module records the honest remaining data needed by the concrete
role-hinge route.  The connector maps are the checked concrete
connector-only transitions from `RoleHingeConcreteSearch`; the period and
metric facts remain explicit fields.

No field below claims that the missing period equations, exact-local
same-block preservation, or non-connector lower tables have been solved.
Instead, the matrix proves that once those concrete obligations are supplied,
they produce the public exact and arbitrary Pach--Toth targets.
-/

namespace ErdosProblems1066
namespace PachToth
namespace PachTothRemainingMatrix

open FiniteGraph
open NonRigidConnectorSeparationFacts
open RoleHingeInterfaceRefinement

noncomputable section

abbrev R2 := Prod Real Real

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

/-- The concrete same/opposite connector-only transition obligations. -/
abbrev concreteConnectorTransitions :
    Figure2Certificate.SameOppositeTransitionObligations :=
  RoleHingeConcreteSearch.concreteSameOppositeTransitionObligations

/-- Decode a finite local index for the concrete generated-chain route. -/
def localVertexOfIndex (u : LocalVertexIndex) : LocalVertex :=
  CrossBlockLowerBoundsInterface.localVertexOfIndex u

/-- Encode a local vertex for the concrete generated-chain route. -/
def localVertexIndex (u : LocalVertex) : LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.localVertexIndex u

@[simp]
theorem localVertexOfIndex_localVertexIndex (u : LocalVertex) :
    localVertexOfIndex (localVertexIndex u) = u := by
  exact CrossBlockLowerBoundsInterface.localVertexOfIndex_localVertexIndex u

@[simp]
theorem localVertexIndex_localVertexOfIndex (u : LocalVertexIndex) :
    localVertexIndex (localVertexOfIndex u) = u := by
  exact CrossBlockLowerBoundsInterface.localVertexIndex_localVertexOfIndex u

/-- The concrete generated point addressed by finite local indices. -/
def concreteIndexedGeneratedPoint
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertexIndex) : R2 :=
  GeneratedClosedChain.generatedPoint
    concreteConnectorTransitions hk
    BaseTransitionRealization.exactBase orientation i
    (localVertexOfIndex u)

/-- Squared coordinate distance between concrete generated indexed points. -/
def concreteIndexedGeneratedSqDist
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Real :=
  CrossBlockDistanceSqReduction.sqDist
    (concreteIndexedGeneratedPoint hk orientation i u)
    (concreteIndexedGeneratedPoint hk orientation j v)

@[simp]
theorem concreteIndexedGeneratedSqDist_eq_coordinate
    {k : Nat} (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    concreteIndexedGeneratedSqDist hk orientation i u j v =
      ((concreteIndexedGeneratedPoint hk orientation i u).1 -
          (concreteIndexedGeneratedPoint hk orientation j v).1) ^ 2 +
        ((concreteIndexedGeneratedPoint hk orientation i u).2 -
          (concreteIndexedGeneratedPoint hk orientation j v).2) ^ 2 := by
  rfl

/-- Finite non-connector square-distance table for the concrete connector
transition route at one positive block count.  Cyclic connector slots are
handled separately by the checked connector-unit facts, so this field names
only the remaining finite inequalities. -/
structure ConcreteNonConnectorSqDistanceTable
    (k : Nat) (hk : 0 < k)
    (orientation : Fin k -> OrientationData.BlockOrientation) where
  sqDist_ge_one :
    forall (i : Fin k) (u : LocalVertexIndex)
      (j : Fin k) (v : LocalVertexIndex),
        Ne i j ->
          Not (NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair
            hk i u j v) ->
            1 <= concreteIndexedGeneratedSqDist hk orientation i u j v

namespace ConcreteNonConnectorSqDistanceTable

/-- The fixed lower table used after cyclic connector slots are removed. -/
def lower
    {k : Nat} {hk : 0 < k}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    (_T : ConcreteNonConnectorSqDistanceTable k hk orientation) :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun _i _u _j _v => 1

@[simp]
theorem lower_apply
    {k : Nat} {hk : 0 < k}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    (T : ConcreteNonConnectorSqDistanceTable k hk orientation)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    T.lower i u j v = 1 := by
  rfl

/-- The fixed lower table is at least one on every remaining non-connector
cross-block pair. -/
theorem lower_ge_one
    {k : Nat} {hk : 0 < k}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    (T : ConcreteNonConnectorSqDistanceTable k hk orientation) :
    NonRigidConnectorSeparationFacts.GeneratedNonConnectorCrossBlockLowerBoundsAtLeastOne
      hk T.lower := by
  intro _i _u _j _v _hij _hnot
  norm_num [lower]

/-- A finite-index non-connector square-distance entry gives the Euclidean
lower bound for the corresponding local-vertex pair. -/
theorem lower_bound
    {k : Nat} {hk : 0 < k}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    (T : ConcreteNonConnectorSqDistanceTable k hk orientation) :
    NonRigidConnectorSeparationFacts.GeneratedNonConnectorCrossBlockDistanceLowerBounds
      concreteConnectorTransitions hk
      BaseTransitionRealization.exactBase orientation T.lower := by
  intro i u j v hij hnot
  have hnot_index :
      Not (NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair
        hk i (localVertexIndex u) j (localVertexIndex v)) := by
    intro hidx
    exact hnot (by
      simpa [NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair,
        localVertexIndex, localVertexOfIndex] using hidx)
  have hsq :
      1 <= concreteIndexedGeneratedSqDist
        hk orientation i (localVertexIndex u) j (localVertexIndex v) :=
    T.sqDist_ge_one i (localVertexIndex u) j (localVertexIndex v)
      hij hnot_index
  simpa [lower, concreteIndexedGeneratedPoint,
    concreteIndexedGeneratedSqDist, localVertexIndex, localVertexOfIndex]
    using CrossBlockDistanceSqReduction.one_le_root_eucDist_of_one_le_sqDist
      hsq

/-- Connector-unit facts, the supplied period equation, and the finite
non-connector table give global separation once the generated blocks have the
exact local same-block metric. -/
theorem separated
    {k : Nat} {hk : 0 < k}
    {orientation : Fin k -> OrientationData.BlockOrientation}
    (T : ConcreteNonConnectorSqDistanceTable k hk orientation)
    (period :
      PeriodInterface.GeneratedPeriodEquation
        concreteConnectorTransitions hk
        BaseTransitionRealization.exactBase orientation)
    (orbitSqDistances :
      RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
        concreteConnectorTransitions hk
        BaseTransitionRealization.exactBase orientation) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      concreteConnectorTransitions hk
      BaseTransitionRealization.exactBase orientation := by
  exact
    generatedGlobalSeparation_of_nonConnectorCrossBlockDistanceLowerBounds
      concreteConnectorTransitions hk BaseTransitionRealization.exactBase
      orientation period
      (generatedSameBlockIsometry_of_orbitSqDistances
        concreteConnectorTransitions hk BaseTransitionRealization.exactBase
        orientation orbitSqDistances)
      T.lower T.lower_ge_one T.lower_bound

end ConcreteNonConnectorSqDistanceTable

/-- The complete remaining concrete data matrix for the non-vacuous
connector-separated route.

The concrete connector transitions are fixed.  The fields below are exactly
the remaining proof obligations: period closure for each positive block
count, exact-local preservation along generated concrete transitions, and
finite non-connector square-distance tables. -/
structure ConcreteRemainingData where
  orientation :
    forall (k : Nat), 0 < k -> Fin k -> OrientationData.BlockOrientation
  period :
    forall (k : Nat) (hk : 0 < k),
      PeriodInterface.GeneratedPeriodEquation
        concreteConnectorTransitions hk
        BaseTransitionRealization.exactBase (orientation k hk)
  transition_exact_local :
    RoleHingeSameBlockAlgebra.GeneratedTransitionsPreserveExactLocalSqDistances
      concreteConnectorTransitions
  nonConnector :
    forall (k : Nat) (hk : 0 < k),
      ConcreteNonConnectorSqDistanceTable k hk (orientation k hk)

namespace ConcreteRemainingData

/-- The generated-chain family determined by concrete connector transitions
and the supplied period words. -/
def toGeneratedChainFamily (D : ConcreteRemainingData) :
    GeneratedSeparationInterface.GeneratedChainFamily where
  O := fun _k _hk => concreteConnectorTransitions
  base := fun _k _hk => BaseTransitionRealization.exactBase
  orientation := D.orientation

/-- Period hypotheses for the generated-chain family. -/
def periods (D : ConcreteRemainingData) :
    D.toGeneratedChainFamily.Periods := by
  intro k hk
  simpa [toGeneratedChainFamily, GeneratedSeparationInterface.GeneratedPeriod,
    PeriodInterface.GeneratedPeriodEquation] using D.period k hk

/-- The algebraic closure equation obtained from the supplied generated
period equation. -/
def closure
    (D : ConcreteRemainingData)
    (k : Nat) (hk : 0 < k) :
    PeriodInterface.GeneratedClosureEquation
      concreteConnectorTransitions hk
      BaseTransitionRealization.exactBase (D.orientation k hk) :=
  PeriodInterface.generatedClosureEquation_of_generatedPeriodEquation
    concreteConnectorTransitions hk BaseTransitionRealization.exactBase
    (D.orientation k hk) (D.period k hk)

/-- Exact-local same-block metric on every generated block. -/
def orbitSqDistances
    (D : ConcreteRemainingData)
    (k : Nat) (hk : 0 < k) :
    RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances
      concreteConnectorTransitions hk
      BaseTransitionRealization.exactBase (D.orientation k hk) := by
  simpa [RoleHingeInterfaceRefinement.GeneratedOrbitMatchesExactLocalSqDistances]
    using
      RoleHingeSameBlockAlgebra.generatedOrbit_exactBase_matchesExactLocalSqDistances
        concreteConnectorTransitions hk (D.orientation k hk)
        D.transition_exact_local

/-- Global generated separation from connector facts and non-connector
finite square-distance tables. -/
def separated
    (D : ConcreteRemainingData)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      concreteConnectorTransitions hk
      BaseTransitionRealization.exactBase (D.orientation k hk) :=
  (D.nonConnector k hk).separated
    (D.period k hk) (D.orbitSqDistances k hk)

/-- Full generated metric hypotheses for one block count. -/
def metricHypothesis
    (D : ConcreteRemainingData)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedMetricHypotheses
      concreteConnectorTransitions hk
      BaseTransitionRealization.exactBase (D.orientation k hk) where
  separated := D.separated k hk
  same_block_isometry :=
    RoleHingeInterfaceRefinement.generatedSameBlockIsometry_of_orbitSqDistances
      concreteConnectorTransitions hk BaseTransitionRealization.exactBase
      (D.orientation k hk) (D.orbitSqDistances k hk)

/-- Full metric hypotheses for the generated-chain family. -/
def metricHypotheses (D : ConcreteRemainingData) :
    D.toGeneratedChainFamily.MetricHypotheses where
  metric := D.metricHypothesis

/-- Exact-block target at one positive block count, routed through period
closure, connector facts, and the non-connector table. -/
theorem targetUpperConstructionFiveSixteenAt_exactBlock
    (D : ConcreteRemainingData)
    (k : Nat) (hk : 0 < k) :
    targetUpperConstructionFiveSixteenAt (16 * k) := by
  exact
    targetUpperConstructionFiveSixteenAt_exactBlock_of_orbitSqDistances
      concreteConnectorTransitions hk BaseTransitionRealization.exactBase
      (D.orientation k hk) (D.closure k hk) (D.separated k hk)
      (D.orbitSqDistances k hk)

/-- Public exact Pach--Toth target from the concrete remaining data matrix. -/
theorem targetUpperConstructionFiveSixteen
    (D : ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteen := by
  exact
    GeneratedSeparationInterface.targetUpperConstructionFiveSixteen_of_family
      D.toGeneratedChainFamily D.periods D.metricHypotheses

/-- Public arbitrary-`n` Pach--Toth target from the concrete remaining data
matrix and the checked exact-to-arbitrary bridge. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (D : ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary := by
  exact
    ExactFamilyClosure.targetUpperConstructionFiveSixteenArbitrary_of_exactTarget
      D.targetUpperConstructionFiveSixteen

end ConcreteRemainingData

universe u

/-- A proof-producing public-target row for one remaining data shape. -/
structure RouteRow (alpha : Sort u) where
  exactTarget : alpha -> PachToth.targetUpperConstructionFiveSixteen
  arbitraryTarget :
    alpha -> PachToth.targetUpperConstructionFiveSixteenArbitrary

/-- The Lean-side remaining-data matrix for the concrete Pach--Toth route. -/
structure Matrix where
  concreteConnectorTransitions :
    Figure2Certificate.SameOppositeTransitionObligations
  concreteConnectorTransitions_eq :
    concreteConnectorTransitions =
      PachTothRemainingMatrix.concreteConnectorTransitions
  concretePeriodNonConnector : RouteRow ConcreteRemainingData

/-- The checked matrix: concrete connector transitions plus explicit
remaining period/exact-local/non-connector obligations route to both public
targets. -/
def matrix : Matrix where
  concreteConnectorTransitions :=
    PachTothRemainingMatrix.concreteConnectorTransitions
  concreteConnectorTransitions_eq := rfl
  concretePeriodNonConnector :=
    { exactTarget := ConcreteRemainingData.targetUpperConstructionFiveSixteen
      arbitraryTarget :=
        ConcreteRemainingData.targetUpperConstructionFiveSixteenArbitrary }

/-- Exact target exposed from the remaining-data matrix. -/
theorem targetUpperConstructionFiveSixteen_of_concreteRemainingData
    (D : ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteen :=
  matrix.concretePeriodNonConnector.exactTarget D

/-- Arbitrary target exposed from the remaining-data matrix. -/
theorem targetUpperConstructionFiveSixteenArbitrary_of_concreteRemainingData
    (D : ConcreteRemainingData) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  matrix.concretePeriodNonConnector.arbitraryTarget D

end

end PachTothRemainingMatrix
end PachToth
end ErdosProblems1066
