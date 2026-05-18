import ErdosProblems1066.Swanepoel.BoundaryFaceCountingToM8
import ErdosProblems1066.Swanepoel.BoundarySpineFiniteCertificate
import ErdosProblems1066.Swanepoel.BrokenLatticeClosure
import ErdosProblems1066.Swanepoel.JordanTopologyFactsConcrete
import ErdosProblems1066.Swanepoel.Lemma8ExistenceConcrete
import ErdosProblems1066.Swanepoel.MinimalFailureComponentPackage
import ErdosProblems1066.Swanepoel.MinimalGraphClosure
import ErdosProblems1066.Swanepoel.NoEarlyTripleObstructionConcrete
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false

/-!
# Swanepoel remaining-obligations matrix

This file records the post-sixth-wave Swanepoel `8 / 31` route as checked
conditional data.  It is a matrix of remaining obligations, not a proof that
the obligations have been constructed.

For one fixed minimal cleared failure, the route is:

* topology/core data, tied to the planar boundary carried by the long-arc
  package;
* boundary count data available from that same planar boundary;
* the boundary-attached long-arc turn budget;
* the finite boundary spine and Lemma 8 existence data that produce local
  labels;
* the `K_{2,3}`/no-early route plus window containment;
* the broken-lattice construction data and contradiction;
* the minimal-graph closure from a uniform family to
  `targetLowerBoundEightThirtyOne`.

Every theorem below has an explicit hypothesis carrying the remaining data.
There is intentionally no unconditional Swanepoel lower-bound theorem here.
-/

namespace ErdosProblems1066
namespace Swanepoel
namespace SwanepoelRemainingMatrix

open Lemma10Inequalities
open MinimalGraphFacts

universe u

noncomputable section

variable {n : Nat}

/-- The canonical straight-line unit-distance graph attached to a
configuration. -/
abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  BoundaryFaceCountingToM8.CanonicalUDGraph C

/-! ## Topology, boundary counts, and long arc -/

/-- Topology/core data tied to the same planar-boundary package that carries
the long nonconcave-arc budget.

The equality field is the honest compatibility obligation between the
topology construction and the boundary/counting/long-arc construction. -/
structure TopologyBoundaryLongArc
    (C : _root_.UDConfig n) where
  topology : JordanTopologyFactsConcrete.TopologyFacts C
  arcBoundaryBudget :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (CanonicalGraph C)
  topologyCore_eq :
    arcBoundaryBudget.planarBoundary.core = topology.toCore

namespace TopologyBoundaryLongArc

variable {C : _root_.UDConfig n}

/-- The full planar-boundary package used by the boundary-count and long-arc
rows. -/
def planarBoundary
    (T : TopologyBoundaryLongArc.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  T.arcBoundaryBudget.planarBoundary

/-- The topology core agrees with the planar-boundary core used downstream. -/
theorem planarBoundary_core_eq_topology
    (T : TopologyBoundaryLongArc.{u} C) :
    T.planarBoundary.core = T.topology.toCore :=
  T.topologyCore_eq

/-- The reusable concrete/proposition-valued boundary count row attached to
the long-arc planar boundary. -/
def boundaryAngleCountFields
    (T : TopologyBoundaryLongArc.{u} C) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.BoundaryAngleCountFields
      T.arcBoundaryBudget :=
  T.arcBoundaryBudget.boundaryAngleCountFields

/-- The proposition-valued E12/E13 boundary count theorems attached to the
same planar-boundary package. -/
theorem faceCountingTheorems
    (T : TopologyBoundaryLongArc.{u} C) :
    PlanarBoundaryClosure.PlanarBoundaryData.FaceCountingTheorems
      T.planarBoundary :=
  T.arcBoundaryBudget.faceCountingTheorems

/-- The concrete face-counting data exposed by `PlanarBoundaryFinal`. -/
def concreteFaceCountingData
    (T : TopologyBoundaryLongArc.{u} C) :
    PlanarBoundaryFinal.PlanarBoundaryData.ConcreteFaceCountingData
      T.planarBoundary :=
  T.arcBoundaryBudget.concreteFaceCountingData

/-- The nonconcave long-arc turn data selected by the boundary budget. -/
def longArc
    (T : TopologyBoundaryLongArc.{u} C) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  T.arcBoundaryBudget.toNonconcaveArcTurnData

/-- The M8 construction-level turn bounds supplied by the selected long arc. -/
def turnBounds
    (T : TopologyBoundaryLongArc.{u} C) :
    M8ConstructionInterface.M8TurnBounds :=
  T.longArc.toM8TurnBounds

/-- The long-arc turn function is pointwise nonnegative. -/
theorem turn_nonnegative
    (T : TopologyBoundaryLongArc.{u} C) (k : Nat) :
    0 <= T.turnBounds.turn k := by
  simpa [turnBounds] using T.longArc.turn_nonnegative k

/-- The long-arc total turn is strictly below `pi / 3`. -/
theorem total_turn_lt_pi_div_three
    (T : TopologyBoundaryLongArc.{u} C) :
    totalTurn T.turnBounds.turn < Real.pi / 3 := by
  simpa [turnBounds] using T.longArc.totalTurn_turn_lt_pi_div_three

end TopologyBoundaryLongArc

/-! ## Boundary labels and Lemma 8 -/

/-- The boundary-label obligations after topology/counts/long-arc data have
been fixed.

The finite spine certificate and Lemma 8 existence data are still explicit
inputs.  Their checked consumers produce the local M8 labels. -/
structure BoundaryLemma8Matrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  positiveCard : 0 < n
  remainingNoCutSlack : CutVertexFinal.RemainingNoCutSlackFact C
  topologyLongArc : TopologyBoundaryLongArc.{u} C
  spineCertificate :
    BoundarySpineFiniteCertificate.M8FinitePQSpineCertificate
      topologyLongArc.planarBoundary
  lemma8Existence :
    Lemma8ExistenceConcrete.M8Lemma8MissingExistenceConditions
      (spineCertificate.toM8BoundarySpine
        ({ positiveCard := positiveCard
           remainingSlack := remainingNoCutSlack } :
          MinimalFailureComponentPackage.MinimalFailureCutVertexFacts
            C hmin).preconnectedNoCut hmin)

namespace BoundaryLemma8Matrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The cut/no-cut facts consumed by the boundary-label context. -/
def cutVertex
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    MinimalFailureComponentPackage.MinimalFailureCutVertexFacts C hmin where
  positiveCard := B.positiveCard
  remainingSlack := B.remainingNoCutSlack

/-- The planar-boundary package used by both count and label rows. -/
def planarBoundary
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  B.topologyLongArc.planarBoundary

/-- Boundary spine obtained from the finite `p/q` spine certificate. -/
def spine
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    M8LabelsFromBoundaryInterface.M8BoundarySpine
      (BoundaryFaceCountingToM8.boundaryCutDegreeContextOfPlanarBoundary
        B.planarBoundary B.cutVertex.preconnectedNoCut hmin) :=
  B.spineCertificate.toM8BoundarySpine
    B.cutVertex.preconnectedNoCut hmin

/-- Lemma 8 combinatorics obtained from the remaining finite existence row. -/
def lemma8
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    M8LabelsFromBoundaryInterface.M8Lemma8Combinatorics B.spine :=
  B.lemma8Existence.toLemma8Combinatorics

/-- Boundary/counting route data, now equipped with the explicit spine and
Lemma 8 rows. -/
def boundaryRouteData
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    BoundaryFaceCountingToM8.M8BoundaryRouteData.{u} C hmin where
  planarBoundary := B.planarBoundary
  connectedNoCut := B.cutVertex.preconnectedNoCut
  spine := B.spine
  lemma8 := B.lemma8

/-- The face-counting row consumed by the M8 boundary route. -/
def faceCounting
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    BoundaryFaceCountingToM8.PlanarBoundaryFaceCountingFields
      B.planarBoundary B.boundaryRouteData.context :=
  B.boundaryRouteData.faceCounting

/-- The local labels produced from topology/core, boundary counts, spine, and
Lemma 8. -/
def localLabels
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    M8ConstructionInterface.M8LocalLabels C :=
  B.boundaryRouteData.toM8LocalLabels

/-- The selected long arc in the label-indexed route. -/
def longArc
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    M8TurnBoundsFromArc.NonconcaveArcTurnData :=
  B.topologyLongArc.longArc

/-- The turn bounds selected by the long-arc row. -/
def turnBounds
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    M8ConstructionInterface.M8TurnBounds :=
  B.longArc.toM8TurnBounds

@[simp]
theorem turnBounds_eq_topologyLongArc_turnBounds
    (B : BoundaryLemma8Matrix.{u} C hmin) :
    B.turnBounds = B.topologyLongArc.turnBounds :=
  rfl

end BoundaryLemma8Matrix

/-! ## K23/no-early and broken-lattice closure -/

/-- The final fixed-row package before contradiction.

The `k23Obstruction` and `windowContainment` fields are the remaining
K23/no-early and Lemma 10 window inputs for the local labels produced by the
topology/count/Lemma 8 rows. -/
structure FixedRemainingMatrix
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  boundary : BoundaryLemma8Matrix.{u} C hmin
  k23Obstruction :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23ObstructionInputs
      boundary.localLabels.predicates.data
  windowContainment :
    M8WindowGeometryFromContainment.M8WindowContainment
      boundary.localLabels boundary.turnBounds

namespace FixedRemainingMatrix

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

/-- The unit-distance `K_{2,3}` cap available for the local graph. -/
theorem noK23
    (_M : FixedRemainingMatrix.{u} C hmin) :
    Not (LocalConfigurations.HasK23 (GraphBridge.unitDistanceLocalGraph C)) :=
  CommonNeighborGeometry.not_hasK23_unitDistanceLocalGraph C

/-- Package the K23/no-early route together with the long-arc turn data and
window containment. -/
def k23TurnWindowObstructionData
    (M : FixedRemainingMatrix.{u} C hmin) :
    NoEarlyTripleObstructionConcrete.M8ConcreteK23TurnWindowObstructionData
      C hmin :=
  NoEarlyTripleObstructionConcrete.k23TurnWindowObstructionData_of_unitDistanceConfig
    (C := C) (hmin := hmin) (localLabels := M.boundary.localLabels)
    M.boundary.longArc M.k23Obstruction M.windowContainment

/-- The K23 route supplies concrete no-early triple exclusions. -/
def noEarlyTriples
    (M : FixedRemainingMatrix.{u} C hmin) :
    NoEarlyTripleConcrete.M8ConcreteNoEarlyTripleEquality
      M.boundary.localLabels.predicates.data :=
  M.k23TurnWindowObstructionData.noEarlyTriples

/-- The no-early exclusions supply the construction-level late-triples field.
-/
def lateTriples
    (M : FixedRemainingMatrix.{u} C hmin) :
    M8ConstructionInterface.M8LateTriples M.boundary.localLabels :=
  M.k23TurnWindowObstructionData.lateTriples

/-- The window-containment row supplies construction-level window geometry. -/
def windowGeometry
    (M : FixedRemainingMatrix.{u} C hmin) :
    M8ConstructionInterface.M8WindowGeometry
      M.boundary.localLabels M.boundary.turnBounds :=
  M.windowContainment.toM8WindowGeometry

/-- Clean construction-interface data assembled from the matrix rows. -/
def constructionData
    (M : FixedRemainingMatrix.{u} C hmin) :
    M8ConstructionInterface.M8ConstructionData C hmin :=
  M.k23TurnWindowObstructionData.toM8ConstructionData

/-- The separated construction fields consumed by `M8PipelineClosure`. -/
def separatedConstructionFields
    (M : FixedRemainingMatrix.{u} C hmin) :
    M8PipelineClosure.M8SeparatedConstructionFields C hmin :=
  M.k23TurnWindowObstructionData.toM8SeparatedConstructionFields

/-- The broken-lattice minimal-failure construction data assembled from the
matrix rows. -/
def brokenLatticeData
    (M : FixedRemainingMatrix.{u} C hmin) :
    BrokenLatticeMinimalFailure.M8ConstructionData C hmin :=
  M.constructionData.toBrokenLatticeMinimalFailure

/-- A fixed minimal cleared failure satisfying the full remaining matrix is
contradictory. -/
theorem contradiction
    (M : FixedRemainingMatrix.{u} C hmin) :
    False :=
  M.brokenLatticeData.contradiction

end FixedRemainingMatrix

/-! ## Uniform family and target closure -/

/-- Uniform remaining-obligations matrix for every minimal cleared failure.

This is the exact post-sixth-wave conditional input used by this file.  It is
not constructed here. -/
structure UniformRemainingMatrix where
  facts :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        FixedRemainingMatrix.{u} C hmin

namespace UniformRemainingMatrix

/-- The uniform K23/no-early eliminator obtained by forgetting each fixed row
to its K23 turn/window package. -/
def toK23TurnWindowEliminator
    (U : UniformRemainingMatrix.{u}) :
    NoEarlyTripleObstructionConcrete.MinimalFailureM8K23TurnWindowEliminator :=
  fun C hmin =>
    Nonempty.intro (U.facts C hmin).k23TurnWindowObstructionData

/-- The uniform separated-field eliminator consumed by the M8 pipeline. -/
def toSeparatedConstructionEliminator
    (U : UniformRemainingMatrix.{u}) :
    M8PipelineClosure.MinimalFailureM8SeparatedConstructionEliminator :=
  NoEarlyTripleObstructionConcrete.separatedConstructionEliminator_of_K23TurnWindowEliminator
    U.toK23TurnWindowEliminator

/-- The same uniform row in the concrete-data form expected by
`MinimalGraphClosure`. -/
def toMinimalGraphM8SeparatedConstructionData
    (U : UniformRemainingMatrix.{u}) :
    MinimalGraphClosure.M8SeparatedConstructionData where
  constructionFields := fun C hmin =>
    (U.facts C hmin).separatedConstructionFields

/-- The uniform remaining matrix rules out all minimal cleared failures. -/
theorem no_minimalClearedFailure
    (U : UniformRemainingMatrix.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  MinimalGraphClosure.M8SeparatedConstructionData.no_minimalClearedFailure
    U.toMinimalGraphM8SeparatedConstructionData

/-- Pipeline-cleared form of the uniform remaining matrix. -/
theorem pipelineCleared
    (U : UniformRemainingMatrix.{u}) :
    forall (n : Nat) (C : _root_.UDConfig n),
      CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphClosure.M8SeparatedConstructionData.pipelineCleared
    U.toMinimalGraphM8SeparatedConstructionData

/-- Conditional final target: supplying the uniform remaining matrix reaches
the Swanepoel `8 / 31` target through the checked minimal-graph closure. -/
theorem targetLowerBoundEightThirtyOne
    (U : UniformRemainingMatrix.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  MinimalGraphClosure.M8SeparatedConstructionData.targetLowerBoundEightThirtyOne
    U.toMinimalGraphM8SeparatedConstructionData

end UniformRemainingMatrix

end

end SwanepoelRemainingMatrix
end Swanepoel
end ErdosProblems1066
