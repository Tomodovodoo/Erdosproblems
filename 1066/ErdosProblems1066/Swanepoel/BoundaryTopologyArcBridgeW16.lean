import ErdosProblems1066.Swanepoel.TopologyToBoundaryArcW14
import ErdosProblems1066.Swanepoel.BoundaryArcToRemainingInputsW14
import ErdosProblems1066.Swanepoel.BoundaryArcExtractionProofW15
import ErdosProblems1066.Swanepoel.ExactOuterBoundaryTopologyW13

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace BoundaryTopologyArcBridgeW16

open BoundaryArcExtractionProofW15
open BoundaryArcInstantiationW13
open BoundaryArcToRemainingInputsW14
open CutVertexInterface
open ExactOuterBoundaryTopologyW13
open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open M8WindowGeometryFromContainment
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open TopologyToBoundaryArcW14

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  ExactOuterBoundaryTopologyW13.CanonicalGraph C

abbrev ActualTopologyArcInputs (C : _root_.UDConfig n) :=
  TopologyBoundaryArcFields.{u} C

abbrev MinimalExactTopologyInputs (C : _root_.UDConfig n) :=
  ExactOuterBoundaryTopologyW13.MinimalExactFields C

def topologyArcInputsOfFiniteWalkData
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData))
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :
    ActualTopologyArcInputs.{u} C where
  topology := T
  outerAngleBounds := outerAngleBounds
  Subpolygon := Subpolygon
  subpolygonData := subpolygonData
  longArc := longArc
  arcExtraction := finiteWalk.toBoundaryArcExtractionFields

@[simp]
theorem topologyArcInputsOfFiniteWalkData_boundaryArc
    {C : _root_.UDConfig n}
    (T : TopologyFacts C)
    (outerAngleBounds :
      OuterBoundaryAngleClosure.BoundaryBookkeepingAngleBounds.{u})
    (Subpolygon : Type u)
    (subpolygonData :
      Subpolygon ->
        SubpolygonAssembly.SubpolygonCycleCountAngleData (CanonicalGraph C))
    (longArc :
      LongArcExistenceConcrete.BoundaryLongArcExistenceFields
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData))
    (finiteWalk :
      BoundaryArcFiniteWalkData
        (T.toPlanarBoundaryData outerAngleBounds Subpolygon
          subpolygonData)) :
    (topologyArcInputsOfFiniteWalkData
      T outerAngleBounds Subpolygon subpolygonData longArc
      finiteWalk).boundaryArc =
        finiteWalk.toBoundaryArcCertificate :=
  rfl

structure TopologyArcRemainingInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  topologyArc : ActualTopologyArcInputs.{u} C
  noCutVertex : NoCutVertex C
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin noCutVertex
        topologyArc.arcBoundaryBudget topologyArc.boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        topologyArc.arcBoundaryBudget topologyArc.boundaryArc
        lemma8Existence).predicates.data
  figure8EuclideanFacts :
    HonestFigure8ExplicitEuclideanFacts
      (localLabelsOfBoundaryArc hmin noCutVertex
        topologyArc.arcBoundaryBudget topologyArc.boundaryArc
        lemma8Existence).predicates
      topologyArc.arcBoundaryBudget.toM8TurnBounds.turn
  figure9EuclideanFacts :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      (localLabelsOfBoundaryArc hmin noCutVertex
        topologyArc.arcBoundaryBudget topologyArc.boundaryArc
        lemma8Existence).predicates
      topologyArc.arcBoundaryBudget.toM8TurnBounds.turn
  windowContainment :
    M8WindowContainment
      (localLabelsOfBoundaryArc hmin noCutVertex
        topologyArc.arcBoundaryBudget topologyArc.boundaryArc
        lemma8Existence)
      (topologyArc.arcBoundaryBudget
        |>.toNonconcaveArcTurnData
        |>.toM8TurnBounds)

namespace TopologyArcRemainingInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def planarBoundary (P : TopologyArcRemainingInputs.{u} C hmin) :
    PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C) :=
  P.topologyArc.planarBoundary

def exactTopology (P : TopologyArcRemainingInputs.{u} C hmin) :
    MinimalExactTopologyInputs C :=
  P.topologyArc.minimalExactFields

def arcBoundaryBudget (P : TopologyArcRemainingInputs.{u} C hmin) :
    NonconcaveArcBudgetFromBoundary.NonconcaveArcBoundaryBudgetData.{u}
      (CanonicalGraph C) :=
  P.topologyArc.arcBoundaryBudget

def boundaryArc (P : TopologyArcRemainingInputs.{u} C hmin) :
    BoundaryArcW12.M8BoundaryArcCertificate
      P.arcBoundaryBudget.planarBoundary :=
  P.topologyArc.boundaryArc

def boundaryArcInstantiation
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    BoundaryArcInstantiation P.planarBoundary :=
  P.topologyArc.toBoundaryArcInstantiation

def toBoundaryArcRemainingFactInputs
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    BoundaryArcRemainingFactInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  planarBoundary := P.planarBoundary
  boundaryArcInstantiation := P.boundaryArcInstantiation
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := P.lemma9FiveStartLateFacts
  figure8EuclideanFacts := P.figure8EuclideanFacts
  figure9EuclideanFacts := P.figure9EuclideanFacts
  windowContainment := P.windowContainment

def toPointwiseRemainingInputs
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    PointwiseRemainingInputs.{u} C hmin :=
  P.toBoundaryArcRemainingFactInputs.toPointwiseRemainingInputs

@[simp]
theorem toBoundaryArcRemainingFactInputs_arcBoundaryBudget
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    P.toBoundaryArcRemainingFactInputs.arcBoundaryBudget =
      P.arcBoundaryBudget :=
  rfl

@[simp]
theorem toBoundaryArcRemainingFactInputs_boundaryArc
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    P.toBoundaryArcRemainingFactInputs.boundaryArc =
      P.boundaryArc :=
  rfl

@[simp]
theorem toBoundaryArcRemainingFactInputs_localLabels
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    P.toBoundaryArcRemainingFactInputs.localLabels =
      localLabelsOfBoundaryArc hmin P.noCutVertex P.arcBoundaryBudget
        P.boundaryArc P.lemma8Existence :=
  rfl

theorem contradiction
    (P : TopologyArcRemainingInputs.{u} C hmin) :
    False :=
  P.toBoundaryArcRemainingFactInputs.pointwiseContradiction

end TopologyArcRemainingInputs

structure TopologyArcRemainingInputFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        TopologyArcRemainingInputs.{u} C hmin

namespace TopologyArcRemainingInputFamily

def toRemainingInputFamily
    (H : TopologyArcRemainingInputFamily.{0}) :
    MinimalFailureClosureW13.RemainingInputFamily.{0} where
  inputs := fun C hmin =>
    (H.inputs C hmin).toPointwiseRemainingInputs

theorem no_minimalClearedFailure
    (H : TopologyArcRemainingInputFamily.{0}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toRemainingInputFamily.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (H : TopologyArcRemainingInputFamily.{0}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toRemainingInputFamily.targetLowerBoundEightThirtyOne

end TopologyArcRemainingInputFamily

structure FiniteWalkTopologyArcRemainingInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  remaining : TopologyArcRemainingInputs.{u} C hmin
  finiteWalk :
    BoundaryArcFiniteWalkData remaining.topologyArc.planarBoundary
  boundaryArc_eq :
    remaining.boundaryArc = finiteWalk.toBoundaryArcCertificate

namespace FiniteWalkTopologyArcRemainingInputs

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def toTopologyArcRemainingInputs
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    TopologyArcRemainingInputs.{u} C hmin :=
  P.remaining

def toBoundaryArcRemainingFactInputs
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    BoundaryArcRemainingFactInputs.{u} C hmin :=
  P.remaining.toBoundaryArcRemainingFactInputs

def toPointwiseRemainingInputs
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    PointwiseRemainingInputs.{u} C hmin :=
  P.remaining.toPointwiseRemainingInputs

@[simp]
theorem toBoundaryArcRemainingFactInputs_arcBoundaryBudget
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    P.toBoundaryArcRemainingFactInputs.arcBoundaryBudget =
      P.remaining.arcBoundaryBudget :=
  rfl

@[simp]
theorem toBoundaryArcRemainingFactInputs_boundaryArc
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    P.toBoundaryArcRemainingFactInputs.boundaryArc =
      P.remaining.boundaryArc :=
  rfl

theorem boundaryArc_from_finiteWalk
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    P.toBoundaryArcRemainingFactInputs.boundaryArc =
      P.finiteWalk.toBoundaryArcCertificate := by
  rw [toBoundaryArcRemainingFactInputs_boundaryArc, P.boundaryArc_eq]

theorem contradiction
    (P : FiniteWalkTopologyArcRemainingInputs.{u} C hmin) :
    False :=
  P.remaining.contradiction

end FiniteWalkTopologyArcRemainingInputs

end

end BoundaryTopologyArcBridgeW16
end Swanepoel
end ErdosProblems1066
