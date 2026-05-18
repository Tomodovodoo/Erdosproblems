import ErdosProblems1066.Swanepoel.BoundaryArcW12
import ErdosProblems1066.Swanepoel.CutVertexSlackW12
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.M8TurnWindowNoEarlyFinal
import ErdosProblems1066.Swanepoel.MinimalFailureConcreteDataMatrix
import ErdosProblems1066.Swanepoel.TargetReduction

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace MinimalFailureClosureW13

open BoundaryArcW12
open CutVertexInterface
open Lemma8ExistenceConcrete
open M8BoundaryLabelsConcrete
open M8LabelsFromBoundaryInterface
open M8TurnWindowNoEarlyFinal
open M8WindowGeometryFromContainment
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleConcrete
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

abbrev CanonicalGraph {n : Nat} (C : _root_.UDConfig n) :=
  MinimalFailureConcreteDataMatrix.CanonicalGraph C

def remainingSlackOfNoCut {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C) :
    CutVertexFinal.RemainingNoCutSlackFact C :=
  CutVertexSlackW12.remainingNoCutSlackFact_of_minimalFailure_of_noCutVertex
    hmin hno

def cutVertexOfNoCut {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard :=
    MinimalFailureConcreteDataMatrix.positiveCard_of_minimalClearedFailure
      hmin
  remainingSlack := remainingSlackOfNoCut hmin hno

def spineOfBoundaryArc {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary) :
    M8BoundarySpine
      (M8BoundaryCutDegreeContext.of_minimalClearedFailure
        arcBoundaryBudget.planarBoundary.core
        (cutVertexOfNoCut hmin hno).preconnectedNoCut hmin) :=
  boundaryArc.toFinitePQSpineCertificate.toM8BoundarySpine
    (cutVertexOfNoCut hmin hno).preconnectedNoCut hmin

def lemma8OfBoundaryArc {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary)
    (lemma8Existence :
      M8Lemma8MissingExistenceConditions
        (spineOfBoundaryArc hmin hno arcBoundaryBudget boundaryArc)) :
    M8Lemma8Combinatorics
      (spineOfBoundaryArc hmin hno arcBoundaryBudget boundaryArc) :=
  lemma8Existence.toLemma8Combinatorics

def boundaryLabelsOfBoundaryArc {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary)
    (lemma8Existence :
      M8Lemma8MissingExistenceConditions
        (spineOfBoundaryArc hmin hno arcBoundaryBudget boundaryArc)) :
    M8BoundaryLabelPackage C :=
  M8BoundaryLabelPackage.ofMinimalClearedFailure
    arcBoundaryBudget.planarBoundary.core
    (cutVertexOfNoCut hmin hno).preconnectedNoCut hmin
    (spineOfBoundaryArc hmin hno arcBoundaryBudget boundaryArc)
    (lemma8OfBoundaryArc hmin hno arcBoundaryBudget boundaryArc
      lemma8Existence)

def localLabelsOfBoundaryArc {n : Nat} {C : _root_.UDConfig n}
    (hmin : IsMinimalClearedFailure C) (hno : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (boundaryArc :
      M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary)
    (lemma8Existence :
      M8Lemma8MissingExistenceConditions
        (spineOfBoundaryArc hmin hno arcBoundaryBudget boundaryArc)) :
    M8ConstructionInterface.M8LocalLabels C :=
  (boundaryLabelsOfBoundaryArc hmin hno arcBoundaryBudget boundaryArc
    lemma8Existence).toM8LocalLabels

structure PointwiseRemainingInputs {n : Nat}
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)
  boundaryArc :
    M8BoundaryArcCertificate arcBoundaryBudget.planarBoundary
  lemma8Existence :
    M8Lemma8MissingExistenceConditions
      (spineOfBoundaryArc hmin noCutVertex arcBoundaryBudget boundaryArc)
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabelsOfBoundaryArc hmin noCutVertex arcBoundaryBudget
        boundaryArc lemma8Existence).predicates.data
  windowContainment :
    M8WindowContainment
      (localLabelsOfBoundaryArc hmin noCutVertex arcBoundaryBudget
        boundaryArc lemma8Existence)
      arcBoundaryBudget.toNonconcaveArcTurnData.toM8TurnBounds

namespace PointwiseRemainingInputs

variable {n : Nat} {C : _root_.UDConfig n}
variable {hmin : IsMinimalClearedFailure C}

def localLabels (P : PointwiseRemainingInputs.{u} C hmin) :
    M8ConstructionInterface.M8LocalLabels C :=
  localLabelsOfBoundaryArc hmin P.noCutVertex P.arcBoundaryBudget
    P.boundaryArc P.lemma8Existence

def noEarlyTripleEquality (P : PointwiseRemainingInputs.{u} C hmin) :
    M8ConcreteNoEarlyTripleEquality P.localLabels.predicates.data :=
  P.lemma9FiveStartLateFacts.toConcreteNoEarlyTripleEquality

def toTurnWindowNoEarlyPackage
    (P : PointwiseRemainingInputs.{u} C hmin) :
    M8TurnWindowNoEarlyPackage C hmin where
  localLabels := P.localLabels
  arc := P.arcBoundaryBudget.toNonconcaveArcTurnData
  noEarlyTriples := P.noEarlyTripleEquality
  windowContainment := P.windowContainment

def toConstructionDataFromContainment
    (P : PointwiseRemainingInputs.{u} C hmin) :
    M8ConstructionDataFromContainment C hmin :=
  P.toTurnWindowNoEarlyPackage.toM8ConstructionDataFromContainment

theorem contradiction (P : PointwiseRemainingInputs.{u} C hmin) :
    False :=
  E22E23BridgeW12.contradiction_of_constructionDataFromContainment
    P.toConstructionDataFromContainment

end PointwiseRemainingInputs

structure RemainingInputFamily : Type (u + 1) where
  inputs :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        PointwiseRemainingInputs.{u} C hmin

namespace RemainingInputFamily

theorem no_minimalClearedFailure (H : RemainingInputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) := by
  intro n C hmin
  exact (H.inputs C hmin).contradiction

theorem hasCleared (H : RemainingInputFamily.{u}) :
    forall (n : Nat) (C : _root_.UDConfig n),
      CounterexamplePipeline.HasClearedEightThirtyOneIndependentSet C :=
  MinimalGraphFacts.hasCleared_of_no_minimalClearedFailure
    H.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (H : RemainingInputFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  targetLowerBoundEightThirtyOne_of_pipelineCleared H.hasCleared

end RemainingInputFamily

theorem no_minimalClearedFailure_of_remainingInputFamily
    (H : RemainingInputFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne_of_remainingInputFamily
    (H : RemainingInputFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.targetLowerBoundEightThirtyOne

theorem no_minimalClearedFailure_of_concreteObligationFamily
    (H :
      MinimalFailureConcreteDataMatrix.MinimalFailureConcreteObligationFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.no_minimalClearedFailure

end

end MinimalFailureClosureW13
end Swanepoel
end ErdosProblems1066
