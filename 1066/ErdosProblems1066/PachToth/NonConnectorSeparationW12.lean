import ErdosProblems1066.PachToth.ConcreteCrossBlockLowerTable
import ErdosProblems1066.PachToth.GeneratedPointDistanceFacts

set_option autoImplicit false

/-!
# W12 non-connector separation bridge

This module packages the reduced non-connector squared-distance route in the
generated-chain spelling.  A worker can prove the remaining cross-block
non-connector inequalities directly for generated local vertices, with the
fixed lower value `1`; the adapters below turn those facts into the existing
finite-index non-connector square-distance table, and conversely expose an
existing finite-index table as generated local-vertex squared-distance facts.
-/

namespace ErdosProblems1066
namespace PachToth
namespace NonConnectorSeparationW12

open FiniteGraph

noncomputable section

abbrev R2 := Prod Real Real

abbrev RoleHingedPeriodSearchFamily :=
  CrossBlockLowerBoundsInterface.RoleHingedPeriodSearchFamily

abbrev LocalVertexIndex :=
  CrossBlockLowerBoundsInterface.LocalVertexIndex

abbrev localVertexIndex :=
  CrossBlockLowerBoundsInterface.localVertexIndex

abbrev localVertexOfIndex :=
  CrossBlockLowerBoundsInterface.localVertexOfIndex

abbrev indexedGeneratedPoint :=
  CrossBlockLowerBoundsInterface.indexedGeneratedPoint

abbrev GeneratedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) : Prop :=
  GeneratedSeparationFarApart.GeneratedCyclicConnectorPair hk i u j v

abbrev IndexedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) : Prop :=
  NonRigidConnectorSeparationFacts.IndexedCyclicConnectorPair hk i u j v

abbrev IndexedNonConnectorCrossBlockSqDistanceTable :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTable

abbrev IndexedNonConnectorCrossBlockSqDistanceTableFamily :=
  NonRigidConnectorSeparationFacts.IndexedNonConnectorCrossBlockSqDistanceTableFamily

abbrev CrossBlockLowerBounds :=
  CrossBlockLowerBoundsInterface.CrossBlockLowerBounds

/-- The reduced non-connector table uses the fixed lower value `1`. -/
def oneLower {k : Nat} :
    Fin k -> LocalVertex -> Fin k -> LocalVertex -> Real :=
  fun _i _u _j _v => 1

@[simp]
theorem oneLower_apply
    {k : Nat}
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    oneLower i u j v = 1 :=
  rfl

/-- The generated-chain and non-rigid connector predicates have the same
local-vertex content. -/
theorem generatedCyclicConnectorPair_iff_cyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    GeneratedCyclicConnectorPair hk i u j v <->
      NonRigidConnectorSeparationFacts.CyclicConnectorPair hk i u j v := by
  rfl

/-- Finite-index connector pairs are the generated-chain connector pairs
after decoding the local vertex indices. -/
theorem indexedCyclicConnectorPair_iff_generatedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertexIndex)
    (j : Fin k) (v : LocalVertexIndex) :
    IndexedCyclicConnectorPair hk i u j v <->
      GeneratedCyclicConnectorPair hk i (localVertexOfIndex u)
        j (localVertexOfIndex v) := by
  rfl

/-- Local-vertex connector pairs and indexed connector pairs agree after
encoding the local vertices. -/
theorem indexedCyclicConnectorPair_of_local_iff_generatedCyclicConnectorPair
    {k : Nat} (hk : 0 < k)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex) :
    IndexedCyclicConnectorPair hk i (localVertexIndex u)
        j (localVertexIndex v) <->
      GeneratedCyclicConnectorPair hk i u j v := by
  simpa [localVertexIndex, localVertexOfIndex] using
    indexedCyclicConnectorPair_iff_generatedCyclicConnectorPair
      hk i (localVertexIndex u) j (localVertexIndex v)

/-- A generated local-vertex non-connector squared-distance table for one
positive block count. -/
structure GeneratedNonConnectorSqDistanceTable
    (F : RoleHingedPeriodSearchFamily)
    (k : Nat) (hk : 0 < k) where
  oneLower_bound :
    GeneratedSeparationFarApart.GeneratedNonConnectorCrossBlockSqDistanceLowerBounds
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk)
      oneLower

namespace GeneratedNonConnectorSqDistanceTable

variable {F : RoleHingedPeriodSearchFamily}
variable {k : Nat} {hk : 0 < k}

/-- Build the generated table from direct `1 <= sqDist` facts. -/
def ofSqDistGeOne
    (h :
      forall (i : Fin k) (u : LocalVertex)
        (j : Fin k) (v : LocalVertex),
          Ne i j ->
            Not (GeneratedCyclicConnectorPair hk i u j v) ->
              1 <=
                UnitVectorGeometry.sqDist
                  (GeneratedClosedChain.generatedPoint
                    F.transitions.toFigure2TransitionObligations
                    hk BaseTransitionRealization.exactBase
                    (F.orientation k hk) i u)
                  (GeneratedClosedChain.generatedPoint
                    F.transitions.toFigure2TransitionObligations
                    hk BaseTransitionRealization.exactBase
                    (F.orientation k hk) j v)) :
    GeneratedNonConnectorSqDistanceTable F k hk where
  oneLower_bound := by
    intro i u j v hij hnot_connector
    simpa [oneLower] using h i u j v hij hnot_connector

/-- Pointwise generated-chain squared-distance separation from the packaged
fixed-one lower table. -/
theorem sqDist_ge_one
    (T : GeneratedNonConnectorSqDistanceTable F k hk)
    (i : Fin k) (u : LocalVertex)
    (j : Fin k) (v : LocalVertex)
    (hij : Ne i j)
    (hnot_connector : Not (GeneratedCyclicConnectorPair hk i u j v)) :
    1 <=
      UnitVectorGeometry.sqDist
        (GeneratedClosedChain.generatedPoint
          F.transitions.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase
          (F.orientation k hk) i u)
        (GeneratedClosedChain.generatedPoint
          F.transitions.toFigure2TransitionObligations
          hk BaseTransitionRealization.exactBase
          (F.orientation k hk) j v) := by
  simpa [oneLower] using
    T.oneLower_bound i u j v hij hnot_connector

/-- Convert generated local-vertex squared-distance facts into the native
finite-index non-connector square-distance table. -/
def toIndexedNonConnectorCrossBlockSqDistanceTable
    (T : GeneratedNonConnectorSqDistanceTable F k hk) :
    IndexedNonConnectorCrossBlockSqDistanceTable F k hk where
  sqDist_ge_one := by
    intro i u j v hij hnot_connector
    have hnot_generated :
        Not (GeneratedCyclicConnectorPair hk i (localVertexOfIndex u)
          j (localVertexOfIndex v)) := by
      intro hconn
      exact hnot_connector
        ((indexedCyclicConnectorPair_iff_generatedCyclicConnectorPair
          hk i u j v).2 hconn)
    have hunit :
        1 <=
          UnitVectorGeometry.sqDist
            (indexedGeneratedPoint F hk i u)
            (indexedGeneratedPoint F hk j v) := by
      simpa [CrossBlockLowerBoundsInterface.indexedGeneratedPoint] using
        T.sqDist_ge_one i (localVertexOfIndex u) j (localVertexOfIndex v)
          hij hnot_generated
    simpa [GeneratedPointDistanceFacts.indexedGeneratedSqDist_eq_unitVectorSqDist]
      using hunit

/-- Generated local-vertex squared-distance facts give generated global
separation for this period length. -/
theorem generatedGlobalSeparation
    (T : GeneratedNonConnectorSqDistanceTable F k hk) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toIndexedNonConnectorCrossBlockSqDistanceTable.generatedGlobalSeparation

/-- Expose an existing finite-index non-connector square-distance table as
generated local-vertex squared-distance lower bounds. -/
def ofIndexedNonConnectorCrossBlockSqDistanceTable
    (T : IndexedNonConnectorCrossBlockSqDistanceTable F k hk) :
    GeneratedNonConnectorSqDistanceTable F k hk where
  oneLower_bound := by
    intro i u j v hij hnot_connector
    have hnot_indexed :
        Not (IndexedCyclicConnectorPair hk i (localVertexIndex u)
          j (localVertexIndex v)) := by
      intro hconn
      exact hnot_connector
        ((indexedCyclicConnectorPair_of_local_iff_generatedCyclicConnectorPair
          hk i u j v).1 hconn)
    have hunit :
        1 <=
          UnitVectorGeometry.sqDist
            (indexedGeneratedPoint F hk i (localVertexIndex u))
            (indexedGeneratedPoint F hk j (localVertexIndex v)) := by
      simpa [GeneratedPointDistanceFacts.indexedGeneratedSqDist_eq_unitVectorSqDist]
        using T.sqDist_ge_one i (localVertexIndex u)
          j (localVertexIndex v) hij hnot_indexed
    simpa [oneLower, CrossBlockLowerBoundsInterface.indexedGeneratedPoint]
      using hunit

end GeneratedNonConnectorSqDistanceTable

/-- Generated local-vertex non-connector squared-distance tables for every
positive block count. -/
structure GeneratedNonConnectorSqDistanceTableFamily
    (F : RoleHingedPeriodSearchFamily) where
  table :
    forall (k : Nat) (hk : 0 < k),
      GeneratedNonConnectorSqDistanceTable F k hk

namespace GeneratedNonConnectorSqDistanceTableFamily

variable {F : RoleHingedPeriodSearchFamily}

/-- Build the family from raw generated local-vertex `1 <= sqDist` facts. -/
def ofSqDistGeOne
    (h :
      forall (k : Nat) (hk : 0 < k)
        (i : Fin k) (u : LocalVertex)
        (j : Fin k) (v : LocalVertex),
          Ne i j ->
            Not (GeneratedCyclicConnectorPair hk i u j v) ->
              1 <=
                UnitVectorGeometry.sqDist
                  (GeneratedClosedChain.generatedPoint
                    F.transitions.toFigure2TransitionObligations
                    hk BaseTransitionRealization.exactBase
                    (F.orientation k hk) i u)
                  (GeneratedClosedChain.generatedPoint
                    F.transitions.toFigure2TransitionObligations
                    hk BaseTransitionRealization.exactBase
                    (F.orientation k hk) j v)) :
    GeneratedNonConnectorSqDistanceTableFamily F where
  table := fun k hk =>
    GeneratedNonConnectorSqDistanceTable.ofSqDistGeOne
      (F := F) (k := k) (hk := hk) (h k hk)

/-- Project the generated local-vertex family to the native finite-index
non-connector square-distance table family. -/
def toIndexedNonConnectorCrossBlockSqDistanceTableFamily
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    IndexedNonConnectorCrossBlockSqDistanceTableFamily F where
  table := fun k hk =>
    (T.table k hk).toIndexedNonConnectorCrossBlockSqDistanceTable

/-- The generated local-vertex family gives the standard lower-bound
facade. -/
def toCrossBlockLowerBounds
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    CrossBlockLowerBounds F :=
  T.toIndexedNonConnectorCrossBlockSqDistanceTableFamily.toCrossBlockLowerBounds

/-- Generated separation at every positive block count. -/
theorem separated
    (T : GeneratedNonConnectorSqDistanceTableFamily F)
    (k : Nat) (hk : 0 < k) :
    GeneratedSeparationInterface.GeneratedGlobalSeparation
      F.transitions.toFigure2TransitionObligations hk
      BaseTransitionRealization.exactBase (F.orientation k hk) :=
  T.toIndexedNonConnectorCrossBlockSqDistanceTableFamily.separated k hk

/-- Exact Pach--Toth target from a full generated local-vertex
non-connector squared-distance family. -/
theorem targetUpperConstructionFiveSixteen
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteen :=
  T.toIndexedNonConnectorCrossBlockSqDistanceTableFamily
    |>.targetUpperConstructionFiveSixteen

/-- Arbitrary-`n` target from the same generated local-vertex
non-connector squared-distance family. -/
theorem targetUpperConstructionFiveSixteenArbitrary
    (T : GeneratedNonConnectorSqDistanceTableFamily F) :
    PachToth.targetUpperConstructionFiveSixteenArbitrary :=
  T.toCrossBlockLowerBounds.targetUpperConstructionFiveSixteenArbitrary

end GeneratedNonConnectorSqDistanceTableFamily

end

end NonConnectorSeparationW12
end PachToth
end ErdosProblems1066
