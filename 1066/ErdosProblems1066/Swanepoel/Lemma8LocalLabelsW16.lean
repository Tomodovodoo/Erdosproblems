import ErdosProblems1066.Swanepoel.BoundaryArcExtractionProofW15
import ErdosProblems1066.Swanepoel.Lemma8Lemma9AssemblyW13
import ErdosProblems1066.Swanepoel.Lemma89WindowContainmentProofW15

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace Lemma8LocalLabelsW16

open BoundaryArcExtractionProofW15
open BoundaryArcW12
open BoundaryFaceCountingToM8
open CutVertexInterface
open Lemma8ExistenceConcrete
open Lemma8Lemma9AssemblyW13
open Lemma8NeighborExtractionConcrete
open Lemma8WitnessW12
open Lemma89WindowContainmentProofW15
open Lemma10AnalyticBridge
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalFailureClosureW13
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

structure PointwiseLemma8LocalLabelInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  boundaryArc :
    M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget boundaryArc) i = 6
  neighborFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget boundaryArc) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix neighborFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix neighborFrame).r i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget boundaryArc).prevQ i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget boundaryArc).leftP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget boundaryArc).rightP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget boundaryArc).nextQ i)

namespace PointwiseLemma8LocalLabelInputs

variable (P : PointwiseLemma8LocalLabelInputs.{u} C hmin)

def cutVertex :
    MinimalFailureComponentPackage.MinimalFailureCutVertexFacts C hmin :=
  MinimalFailureClosureW13.cutVertexOfNoCut hmin P.noCutVertex

def spine :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        P.arcBoundaryBudget.planarBoundary.core
        P.cutVertex.preconnectedNoCut hmin) :=
  MinimalFailureClosureW13.spineOfBoundaryArc hmin P.noCutVertex
    P.arcBoundaryBudget P.boundaryArc

def witnessData :
    Lemma8Lemma9AssemblyW13.M8ArcLemma8WitnessData
      P.arcBoundaryBudget.planarBoundary P.cutVertex.preconnectedNoCut hmin
    where
  arc := P.boundaryArc
  centerDegreeSix := P.centerDegreeSix
  forbiddenFrame := P.neighborFrame
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def lemma8Existence :
    M8Lemma8MissingExistenceConditions P.spine where
  centerDegreeSix := P.centerDegreeSix
  forbiddenFrame := P.neighborFrame
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def lemma8 :
    M8Lemma8Combinatorics P.spine :=
  P.lemma8Existence.toLemma8Combinatorics

def boundaryLabelPackage : M8BoundaryLabelPackage C :=
  MinimalFailureClosureW13.boundaryLabelsOfBoundaryArc
    hmin P.noCutVertex P.arcBoundaryBudget P.boundaryArc
    P.lemma8Existence

def localLabels : M8ConstructionInterface.M8LocalLabels C :=
  P.boundaryLabelPackage.toM8LocalLabels

@[simp]
theorem localLabels_eq_minimalFailureClosure :
    P.localLabels =
      MinimalFailureClosureW13.localLabelsOfBoundaryArc hmin P.noCutVertex
        P.arcBoundaryBudget P.boundaryArc P.lemma8Existence :=
  rfl

@[simp]
theorem lemma8_r (i : M8ExtraIndex) :
    P.lemma8.r i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.neighborFrame).r i :=
  rfl

@[simp]
theorem lemma8_s (i : M8ExtraIndex) :
    P.lemma8.s i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.neighborFrame).s i :=
  rfl

@[simp]
theorem localLabels_r (i : M8ExtraIndex) :
    P.localLabels.labels.r i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.neighborFrame).r i :=
  rfl

@[simp]
theorem localLabels_s (i : M8ExtraIndex) :
    P.localLabels.labels.s i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.neighborFrame).s i :=
  rfl

theorem localLabels_extraNeighborWitness (i : M8ExtraIndex) :
    P.localLabels.predicates.data.extraNeighborWitness i :=
  P.boundaryLabelPackage.extraNeighborWitness i

theorem witnessData_localLabels_eq :
    P.witnessData.localLabels = P.localLabels :=
  rfl

theorem witnessData_lemma8_eq :
    P.witnessData.toLemma8Combinatorics = P.lemma8 :=
  rfl

def toPointwiseLemma89Base
    (lemma9FiveStartLateFacts :
      M8Lemma9FiveStartLateFacts P.localLabels.predicates.data) :
    Lemma89WindowContainmentProofW15.PointwiseLemma89Base.{u} C hmin
    where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.boundaryArc
  lemma8Existence := P.lemma8Existence
  lemma9FiveStartLateFacts := lemma9FiveStartLateFacts

@[simp]
theorem toPointwiseLemma89Base_localLabels
    (lemma9FiveStartLateFacts :
      M8Lemma9FiveStartLateFacts P.localLabels.predicates.data) :
    (P.toPointwiseLemma89Base lemma9FiveStartLateFacts).localLabels =
      P.localLabels :=
  rfl

@[simp]
theorem toPointwiseLemma89Base_turnBounds
    (lemma9FiveStartLateFacts :
      M8Lemma9FiveStartLateFacts P.localLabels.predicates.data) :
    (P.toPointwiseLemma89Base lemma9FiveStartLateFacts).turnBounds =
      P.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds :=
  rfl

end PointwiseLemma8LocalLabelInputs

structure PointwiseFiniteWalkLemma8LocalLabelInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u}
      (MinimalFailureClosureW13.CanonicalGraph C)
  finiteWalk :
    BoundaryArcFiniteWalkData arcBoundaryBudget.planarBoundary
  centerDegreeSix :
    forall i : M8ExtraIndex,
      centerDegree
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate) i = 6
  neighborFrame :
    forall i : M8ExtraIndex,
      FourForbiddenNeighborFrame
        (MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate) i
  positiveCyclicOrderAt :
    M8ExtraIndex -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n -> Fin n ->
      Prop
  positiveCyclicOrder :
    forall i : M8ExtraIndex,
      positiveCyclicOrderAt i
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix neighborFrame).s i)
        ((M8ExtraNeighborData.ofDegreeSixForbiddenFrame
          centerDegreeSix neighborFrame).r i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).prevQ i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).leftP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).rightP i)
        ((MinimalFailureClosureW13.spineOfBoundaryArc hmin noCutVertex
          arcBoundaryBudget finiteWalk.toBoundaryArcCertificate).nextQ i)

namespace PointwiseFiniteWalkLemma8LocalLabelInputs

variable (P : PointwiseFiniteWalkLemma8LocalLabelInputs.{u} C hmin)

def toLocalLabelInputs :
    PointwiseLemma8LocalLabelInputs.{u} C hmin where
  noCutVertex := P.noCutVertex
  arcBoundaryBudget := P.arcBoundaryBudget
  boundaryArc := P.finiteWalk.toBoundaryArcCertificate
  centerDegreeSix := P.centerDegreeSix
  neighborFrame := P.neighborFrame
  positiveCyclicOrderAt := P.positiveCyclicOrderAt
  positiveCyclicOrder := P.positiveCyclicOrder

def localLabels : M8ConstructionInterface.M8LocalLabels C :=
  P.toLocalLabelInputs.localLabels

def lemma8Existence :
    M8Lemma8MissingExistenceConditions P.toLocalLabelInputs.spine :=
  P.toLocalLabelInputs.lemma8Existence

@[simp]
theorem boundaryArc_eq_finiteWalk :
    P.toLocalLabelInputs.boundaryArc =
      P.finiteWalk.toBoundaryArcCertificate :=
  rfl

@[simp]
theorem localLabels_r (i : M8ExtraIndex) :
    P.localLabels.labels.r i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.neighborFrame).r i :=
  rfl

@[simp]
theorem localLabels_s (i : M8ExtraIndex) :
    P.localLabels.labels.s i =
      (M8ExtraNeighborData.ofDegreeSixForbiddenFrame
        P.centerDegreeSix P.neighborFrame).s i :=
  rfl

def toPointwiseLemma89Base
    (lemma9FiveStartLateFacts :
      M8Lemma9FiveStartLateFacts P.localLabels.predicates.data) :
    Lemma89WindowContainmentProofW15.PointwiseLemma89Base.{u} C hmin :=
  P.toLocalLabelInputs.toPointwiseLemma89Base lemma9FiveStartLateFacts

end PointwiseFiniteWalkLemma8LocalLabelInputs

structure PointwiseLemma8Lemma9LocalWindowInputs
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  labels : PointwiseLemma8LocalLabelInputs.{u} C hmin
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts labels.localLabels.predicates.data
  windowFields :
    PointwiseMissingWindowContainmentFields
      (labels.toPointwiseLemma89Base lemma9FiveStartLateFacts)

namespace PointwiseLemma8Lemma9LocalWindowInputs

variable (P : PointwiseLemma8Lemma9LocalWindowInputs.{u} C hmin)

def base :
    Lemma89WindowContainmentProofW15.PointwiseLemma89Base.{u} C hmin :=
  P.labels.toPointwiseLemma89Base P.lemma9FiveStartLateFacts

def localLabels : M8ConstructionInterface.M8LocalLabels C :=
  P.labels.localLabels

def toPointwiseLemma89WindowContainmentFields :
    Lemma89WindowContainmentProofW15.PointwiseLemma89WindowContainmentFields.{u}
      C hmin where
  base := P.base
  windowFields := P.windowFields

def toPointwiseLemma89LocalWindowInputs :
    Lemma89ToRemainingInputsW14.PointwiseLemma89LocalWindowInputs.{u}
      C hmin :=
  P.toPointwiseLemma89WindowContainmentFields
    |>.toPointwiseLemma89LocalWindowInputs

def toPointwiseRemainingInputs :
    MinimalFailureClosureW13.PointwiseRemainingInputs.{u} C hmin :=
  P.toPointwiseLemma89WindowContainmentFields.toPointwiseRemainingInputs

@[simp]
theorem base_localLabels :
    P.base.localLabels = P.localLabels :=
  rfl

@[simp]
theorem toPointwiseRemainingInputs_localLabels :
    P.toPointwiseRemainingInputs.localLabels = P.localLabels :=
  rfl

theorem E22_E23 :
    HonestFigure8SeparatedWindowLowerE22
        P.localLabels.predicates
        P.labels.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds.turn /\
      HonestFigure9AdjacentWindowLowerE23
        P.localLabels.predicates
        P.labels.arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds.turn :=
  P.toPointwiseLemma89WindowContainmentFields.E22_E23

theorem contradiction
    (P : PointwiseLemma8Lemma9LocalWindowInputs.{u} C hmin) :
    False :=
  Lemma89WindowContainmentProofW15.PointwiseLemma89WindowContainmentFields.contradiction
    (toPointwiseLemma89WindowContainmentFields P)

end PointwiseLemma8Lemma9LocalWindowInputs

structure Lemma8Lemma9LocalWindowInputFamily : Type (u + 1) where
  row :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseLemma8Lemma9LocalWindowInputs.{u} C hmin

namespace Lemma8Lemma9LocalWindowInputFamily

def toWindowContainmentFieldFamily
    (F : Lemma8Lemma9LocalWindowInputFamily.{u}) :
    Lemma89WindowContainmentProofW15.Lemma89WindowContainmentFieldFamily.{u}
    where
  row := fun C hmin =>
    (F.row C hmin).toPointwiseLemma89WindowContainmentFields

def toRemainingInputFamily
    (F : Lemma8Lemma9LocalWindowInputFamily.{u}) :
    MinimalFailureClosureW13.RemainingInputFamily.{u} :=
  F.toWindowContainmentFieldFamily.toRemainingInputFamily

theorem no_minimalClearedFailure
    (F : Lemma8Lemma9LocalWindowInputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  F.toRemainingInputFamily.no_minimalClearedFailure

end Lemma8Lemma9LocalWindowInputFamily

end

end Lemma8LocalLabelsW16
end Swanepoel
end ErdosProblems1066
