import ErdosProblems1066.Swanepoel.CutVertexSlackW12
import ErdosProblems1066.Swanepoel.E22E23BridgeW12
import ErdosProblems1066.Swanepoel.Lemma8WitnessW12
import ErdosProblems1066.Swanepoel.Lemma9NoStartConcrete
import ErdosProblems1066.Swanepoel.M8PaperFactsAssemblyRefined
import ErdosProblems1066.Swanepoel.M8TurnPackageW12
import ErdosProblems1066.Swanepoel.MinimalConnectednessClosure
import ErdosProblems1066.Swanepoel.NonconcaveArcBudgetFromBoundary

set_option autoImplicit false

namespace ErdosProblems1066
namespace Swanepoel
namespace RefinedPaperFactsAssemblyW13

open BoundarySpineFiniteCertificate
open CutVertexFinal
open CutVertexInterface
open Figure8EuclideanFactsConcrete
open Figure9EuclideanFactsConcrete
open Lemma8ExistenceConcrete
open Lemma8WitnessW12
open M8BoundaryLabelsConcrete
open M8ConstructionInterface
open M8LabelsFromBoundaryInterface
open MinimalFailureComponentPackage
open MinimalGraphFacts
open NoEarlyTripleFromLemma9
open NonconcaveArcBudgetFromBoundary

universe u

noncomputable section

variable {n : Nat}

abbrev CanonicalGraph (C : _root_.UDConfig n) :
    FaceReduction.CanonicalStraightLineUnitDistanceGraph n :=
  M8PaperFactsAssemblyRefined.CanonicalGraph C

theorem positiveCard_of_minimalClearedFailure
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C) :
    0 < n := by
  cases n with
  | zero =>
      have hfin : Nonempty (Fin 0) :=
        MinimalConnectednessClosure.fin_nonempty_of_minimalClearedFailure
          (C := C) hmin
      cases hfin with
      | intro i => exact Fin.elim0 i
  | succ n =>
      exact Nat.succ_pos n

def remainingNoCutSlack_of_noCutVertex
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    RemainingNoCutSlackFact C :=
  CutVertexSlackW12.remainingNoCutSlackFact_of_minimalFailure_of_noCutVertex
    hmin hno

def cutVertexFacts_of_noCutVertex
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    MinimalFailureCutVertexFacts C hmin where
  positiveCard := positiveCard_of_minimalClearedFailure hmin
  remainingSlack := remainingNoCutSlack_of_noCutVertex hmin hno

abbrev PreconnectedNoCut_of_noCutVertex
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (hno : NoCutVertex C) :
    CutVertexClosure.PreconnectedNoCutVertexCertificate C :=
  (cutVertexFacts_of_noCutVertex hmin hno).preconnectedNoCut

def lemma8Existence_of_finiteWitness
    {C : _root_.UDConfig n}
    {Dplanar :
      PlanarBoundaryClosure.PlanarBoundaryData.{u} (CanonicalGraph C)}
    {connectedNoCut : CutVertexClosure.PreconnectedNoCutVertexCertificate C}
    {hmin : IsMinimalClearedFailure C}
    (W :
      M8FiniteBoundaryLemma8WitnessData
        Dplanar connectedNoCut hmin) :
    M8Lemma8MissingExistenceConditions
      (W.finiteLabels.toM8BoundarySpine connectedNoCut hmin) where
  centerDegreeSix := W.centerDegreeSix
  forbiddenFrame := W.forbiddenFrame
  positiveCyclicOrderAt := W.positiveCyclicOrderAt
  positiveCyclicOrder := W.positiveCyclicOrder

def localLabels_of_finiteWitness
    {C : _root_.UDConfig n} (hmin : IsMinimalClearedFailure C)
    (hno : NoCutVertex C)
    (arcBoundaryBudget :
      NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C))
    (lemma8Witness :
      M8FiniteBoundaryLemma8WitnessData
        arcBoundaryBudget.planarBoundary
        (PreconnectedNoCut_of_noCutVertex hmin hno) hmin) :
    M8LocalLabels C :=
  (M8BoundaryLabelPackage.ofMinimalClearedFailure
    arcBoundaryBudget.planarBoundary.core
    (PreconnectedNoCut_of_noCutVertex hmin hno) hmin
    (lemma8Witness.finiteLabels.toM8BoundarySpine
      (PreconnectedNoCut_of_noCutVertex hmin hno) hmin)
    (lemma8Existence_of_finiteWitness
      lemma8Witness).toLemma8Combinatorics).toM8LocalLabels

structure ExplicitW12RefinedPaperFactRecords
    (C : _root_.UDConfig n) (hmin : IsMinimalClearedFailure C) where
  noCutVertex : NoCutVertex C
  arcBoundaryBudget :
    NonconcaveArcBoundaryBudgetData.{u} (CanonicalGraph C)
  lemma8Witness :
    M8FiniteBoundaryLemma8WitnessData
      arcBoundaryBudget.planarBoundary
      (PreconnectedNoCut_of_noCutVertex hmin noCutVertex) hmin
  lemma9FiveStartLateFacts :
    M8Lemma9FiveStartLateFacts
      (localLabels_of_finiteWitness hmin noCutVertex arcBoundaryBudget
        lemma8Witness).predicates.data
  figure8EuclideanFacts :
    HonestFigure8ExplicitEuclideanFacts
      (localLabels_of_finiteWitness hmin noCutVertex arcBoundaryBudget
        lemma8Witness).predicates
      arcBoundaryBudget.toM8TurnBounds.turn
  figure9EuclideanFacts :
    HonestFigure9AdjacentLeftEuclideanFactWitnesses
      (localLabels_of_finiteWitness hmin noCutVertex arcBoundaryBudget
        lemma8Witness).predicates
      arcBoundaryBudget.toM8TurnBounds.turn

namespace ExplicitW12RefinedPaperFactRecords

variable {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}

def positiveCard
    (_R : ExplicitW12RefinedPaperFactRecords C hmin) :
    0 < n :=
  positiveCard_of_minimalClearedFailure hmin

def remainingNoCutSlack
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    RemainingNoCutSlackFact C :=
  remainingNoCutSlack_of_noCutVertex hmin R.noCutVertex

def cutVertex
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    MinimalFailureCutVertexFacts C hmin :=
  cutVertexFacts_of_noCutVertex hmin R.noCutVertex

def spineCertificate
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    M8FinitePQSpineCertificate R.arcBoundaryBudget.planarBoundary :=
  R.lemma8Witness.finiteLabels

def lemma8Existence
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    M8Lemma8MissingExistenceConditions
      (R.spineCertificate.toM8BoundarySpine
        R.cutVertex.preconnectedNoCut hmin) :=
  lemma8Existence_of_finiteWitness R.lemma8Witness

def localLabels
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    M8LocalLabels C :=
  localLabels_of_finiteWitness hmin R.noCutVertex
    R.arcBoundaryBudget R.lemma8Witness

def toMinimalFailureM8RefinedPaperFacts
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts
      C hmin where
  positiveCard := R.positiveCard
  remainingNoCutSlack := R.remainingNoCutSlack
  arcBoundaryBudget := R.arcBoundaryBudget
  spineCertificate := R.spineCertificate
  lemma8Existence := R.lemma8Existence
  lemma9FiveStartLateFacts := R.lemma9FiveStartLateFacts
  figure8EuclideanFacts := R.figure8EuclideanFacts
  figure9EuclideanFacts := R.figure9EuclideanFacts

theorem contradiction
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    False :=
  R.toMinimalFailureM8RefinedPaperFacts.contradiction

end ExplicitW12RefinedPaperFactRecords

def minimalFailureM8RefinedPaperFacts_of_explicitW12Records
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFacts
      C hmin :=
  R.toMinimalFailureM8RefinedPaperFacts

theorem contradiction_of_explicitW12Records
    {C : _root_.UDConfig n} {hmin : IsMinimalClearedFailure C}
    (R : ExplicitW12RefinedPaperFactRecords C hmin) :
    False :=
  R.contradiction

structure ExplicitW12RefinedPaperFactRecordsFamily where
  records :
    forall {n : Nat} (C : _root_.UDConfig n)
      (hmin : IsMinimalClearedFailure C),
        ExplicitW12RefinedPaperFactRecords.{u} C hmin

namespace ExplicitW12RefinedPaperFactRecordsFamily

def toMinimalFailureM8RefinedPaperFactsFamily
    (H : ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    M8PaperFactsAssemblyRefined.MinimalFailureM8RefinedPaperFactsFamily where
  facts := fun C hmin =>
    (H.records C hmin).toMinimalFailureM8RefinedPaperFacts

theorem no_minimalClearedFailure
    (H : ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    forall {n : Nat} (C : _root_.UDConfig n),
      Not (IsMinimalClearedFailure C) :=
  H.toMinimalFailureM8RefinedPaperFactsFamily.no_minimalClearedFailure

theorem targetLowerBoundEightThirtyOne
    (H : ExplicitW12RefinedPaperFactRecordsFamily.{u}) :
    _root_.ErdosProblems1066.Swanepoel.targetLowerBoundEightThirtyOne :=
  H.toMinimalFailureM8RefinedPaperFactsFamily.targetLowerBoundEightThirtyOne

end ExplicitW12RefinedPaperFactRecordsFamily

end

end RefinedPaperFactsAssemblyW13
end Swanepoel
end ErdosProblems1066
